namespace nml.Parser

open System.IO
open nml
open nml.Contexts
open nml.Helper
open nml.Typer
open nml.Ast
open With

exception ParserFailed of msg:string with
  override x.Message = x.msg
exception ParserFailedWithPos of msg:string * loc:Source with
  override x.Message = sprintf "%s: %s" (to_s x.loc) x.msg

[<AutoOpen>]
module ParsedAst =
  type ParsedType =
    | PTyVar of qualified_name
    | PTyApp of qualified_name * ParsedType list
    | PTyFun of ParsedType * ParsedType
    | PTyTuple of ParsedType * ParsedType
    | PTyExplicit of ParsedType

  type ParsedTermWithSource = WithSource<ParsedTerm>
  and ParsedTerm =
    | PTmVar of qualified_name
    | PTmLiteral of Literal
    | PTmTuple of ParsedTermWithSource list
    | PTmList of ParsedTermWithSource list
    
    | PTmFun of string  * ParsedTermWithSource
    | PTmFunUnit of ParsedTermWithSource
    | PTmApply of ParsedTermWithSource * ParsedTermWithSource
    | PTmOp2 of ParsedTermWithSource * string * ParsedTermWithSource
    
    | PTmLet of string * ParsedTermWithSource * ParsedTermWithSource
    | PTmDefer of ParsedTermWithSource
    | PTmDeferInf of ParsedTermWithSource
    | PTmLetDefer of TemporalTime * string * ParsedTermWithSource * ParsedTermWithSource
    
    | PTmIf of ParsedTermWithSource * ParsedTermWithSource * ParsedTermWithSource
    | PTmMatch of ParsedTermWithSource * (ParsedTermWithSource * ParsedTermWithSource) list
    | PTmFunction of (ParsedTermWithSource * ParsedTermWithSource) list
    | PTmFixpoint of string * (ParsedTermWithSource * ParsedTermWithSource) list
  
  type ParsedTopLevelWithSource = WithSource<ParsedTopLevel>
  and ParsedTopLevel =
    | PTopImport of filename:string
    | PTopOpen of qualified_name
    | PTopModule of string * ParsedTopLevelWithSource list
    | PTopTermDef of string * string list * ParsedTermWithSource
    | PTopDataTypeDef of kind: TyDataTypeKind * name:string * tyParams:string list * cstrs: (string * ParsedType option) list
    | PTopDo of ParsedTermWithSource

module ParserUtils =
  let checkRecursiveDataType (name: qualified_name) (cstrs: (string * ParsedType option) list) =
    let rec dig = function
      | PTyVar x -> x = name
      | PTyApp (x, ts) -> x = name || ts |> List.exists dig
      | PTyExplicit x -> dig x
      | PTyFun (a, b) ->
        if (dig a) then
          ParserFailed "negative types are not allowed" |> raise
        else 
          dig b
      | PTyTuple (a, b) -> dig a || dig b
    let cases =
      List.map (snd >> function Some x -> dig x | None -> false) cstrs
    match (cases |> List.exists id, cases |> List.forall id) with
      | false, false -> DTVariant
      | true, false -> DTInductive
      | true, true -> DTCoinductive
      | false, true -> failwith "impossible"

  let makeList t = 
    let rec m = function
      | [ { item = PTmOp2 (l, ";", r) }] -> l :: m [r]
      | x -> x
    in m t |> PTmList
  
  let makeFun (args, body) =
    match args with
      | ["()"] -> PTmFunUnit body
      | _ -> body |> List.foldBack (fun x t -> PTmFun(x, t) |> sameInfoOf body) args |> itemof
  
  let makeLet (vars, value, expr) =
    assert (vars <> []);
    let h, t = List.head vars, List.tail vars
    if List.isEmpty t then
      PTmLet (h, value, expr)
    else
      PTmLet (h, makeFun (t, value) |> sameInfoOf value, expr)

  let rec toKnownType ctx : ParsedType -> TemporalType =
    function
      | PTyVar ["Unit"] -> TyUnit |> NotTemporal
      | PTyVar ["Bool"] -> TyBool |> NotTemporal
      | PTyVar x ->
        match ctx |> Context.findType x |> Option.map deschemePrettified with
          | Some (NotTemporal (TyDataType (_, [], _) & vt))
          | Some (NotTemporal (TyDataTypeSelf (_, []) & vt)) -> NotTemporal vt
          | Some (NotTemporal (TyDataType _))
          | Some (NotTemporal (TyDataTypeSelf _)) ->
            sprintf "Insufficient type argument(s) for type constructor '%s'" (sprint_qualified x) 
            |> tee |> ParserFailed |> raise
          | Some t -> t
          | None ->
            match x with
              | [v] -> NTTyVar v
              | _ ->
                sprintf "Unknown type '%s'" (sprint_qualified x)
                |> tee |> ParserFailed |> raise
      | PTyFun (a, b) -> TyFun (toKnownType ctx a, toKnownType ctx b) |> NotTemporal
      | PTyTuple (l, r) ->
        NotTemporal <|
          match (r, toKnownType ctx r) with
            | PTyTuple _, NotTemporal (TyTuple ts) ->
              TyTuple (toKnownType ctx l :: ts)
            | _, x -> TyTuple [toKnownType ctx l; x]
      | PTyApp (["Next"], [x]) -> toKnownType ctx x |> delayTypeBy (TimeN 1u)
      | PTyApp (["Finally"], [x]) -> toKnownType ctx x |> delayTypeBy TimeInf
      | PTyApp (name, ts) ->
        NotTemporal <|
          match ctx |> Context.findType name
                    |> Option.map deschemePrettified
                    |> Option.bind (function NotTemporal t -> Some t | _ -> None) with
            | Some (TyDataType (n, vts, { cstrs = cts } & prop)) ->
              if (List.length ts <> List.length vts) then
                sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name)
                |> tee |> ParserFailed |> raise
              
              let ts = ts |> List.map (toKnownType ctx)
              let asgn = 
                vts |> List.map2 (fun x -> function | NTTyVar y -> (y, x) |> Some | _ -> None) ts
                    |> List.choose id
                    |> Map.ofList
                    |> Assign in
              let cts' = cts |> List.map (argsmap (substAll asgn)) in
              TyDataType (n, ts, { prop with cstrs = cts' })
            | Some (TyDataTypeSelf (n, vts)) ->
              if List.length ts = List.length vts then
                TyDataTypeSelf (n, ts |> List.map (toKnownType ctx))
              else
                sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name)
                |> tee |> ParserFailed |> raise 
            | _ ->
              sprintf "Unknown datatype: '%s'" (sprint_qualified name)
              |> tee |> ParserFailed |> raise
      | PTyExplicit x -> toKnownType ctx x
  
  let toUntypedTerm ctx (pt: ParsedTermWithSource) : UntypedTerm =
    let isValidCstr name args =
      ctx |> Context.findConstructor name (Some args) |> Option.isSome

    let rec getVariablePatterns =
      function
        | Item (TmFreeVar [x]) when x <> "_" -> [x]
        | Item (TmTuple xs) 
        | Item (TmConstruct (_, xs))
        | Item (TmApply (_, xs)) ->
          List.collect getVariablePatterns xs 
        | _ -> []

    let rec totc stack (pt, bd) =
      let fv = pt |> tot [] |> getVariablePatterns in
      (pt |> top (List.append fv stack), bd |> tot (List.append fv stack))

    and top stack ptm : MatchPattern =
      match ptm.item with
        | PTmVar ["_"] -> MtWildcard
        | PTmVar [x] when stack |> List.contains x ->
          stack |> List.findIndex ((=) x) |> MtBoundVar
        | PTmVar name when isValidCstr name [] ->
          MtConstruct (name, [])
        | PTmLiteral l -> MtLiteral l
        | PTmApply (Item (PTmVar name), Item (PTmTuple xs))
          when isValidCstr name xs ->
          MtConstruct (name, xs |> List.map (top stack))
        | PTmApply (Item (PTmVar name), y)
          when isValidCstr name [y] ->
          MtConstruct (name, [y |> top stack])
        | PTmList [] -> MtNil
        | PTmList (h::t) -> MtCons (top stack h, top stack (PTmList t |> noinfo))
        | PTmOp2 (l, name, r)
          when isValidCstr [name] [l;r] ->
          MtConstruct ([name], [l;r] |> List.map (top stack))
        | PTmTuple xs -> MtTuple (xs |> List.map (top stack))
        | _ ->
          printfn "%A" ptm.item
          ParserFailedWithPos ("Invalid pattern", ptm.info) |> raise

    and tot stack ptm : UntypedTerm =
      sameInfoOf ptm <| 
        match ptm.item with
          | PTmVar x ->
            // constructor without arguments
            if (ctx |> Context.findConstructor x (Some []) |> Option.isSome) then
              TmConstruct (x, [])
            else
              let p x = ctx |> Context.findConstructor x None
              match x with
                | Choose p (ty, targs) ->
                  let frees =
                    [0..targs.Length-1] |> List.map (fun i -> MtBoundVar i, TmBoundVar i |> sameInfoOf ptm)
                  TmFunction (FunNormal, [ MtTuple (frees |> List.map fst), TmConstruct (x, frees |> List.map snd) |> sameInfoOf ptm ])
                | [v] ->
                  match (stack |> List.tryFindIndex ((=) v)) with
                    | Some i -> TmBoundVar i
                    | None ->   TmFreeVar x
                | _ -> TmFreeVar x
          | PTmLiteral l -> TmLiteral l
          | PTmTuple xs -> TmTuple (xs |> List.map (tot stack))
          | PTmList [] -> TmNil
          | PTmList (h::t) ->
            TmCons (tot stack h, tot stack (PTmList t |> sameInfoOf ptm))
          | PTmFun (arg, body) -> TmFun (body |> tot (arg :: stack))
          | PTmFunUnit body -> TmFun (body |> tot ("" :: stack))
          // immediate constructor handling
          | PTmApply ({ item = PTmVar x }, { item = PTmTuple xs })
            when (ctx |> Context.findConstructor x (Some xs) |> Option.isSome) ->
            TmConstruct (x, xs |> List.map (tot stack))
          // immediate constructor handling
          | PTmApply ({ item = PTmVar x }, y)
            when (ctx |> Context.findConstructor x (Some [y]) |> Option.isSome)  ->
            TmConstruct (x, [y |> tot stack])
          | PTmApply (l, r) ->
            match (l |> tot stack) with
              | Item (TmApply (l', r')) -> TmApply (l', List.append r' [tot stack r])
              | x -> TmApply (x, [tot stack r])
          | PTmDefer x ->
            match tot stack x with
              | Item (TmDefer (time, x')) ->
                TmDefer (time + TimeN 1u, x')
              | x' -> TmDefer (TimeN 1u, NotTemporalTerm x')
          | PTmDeferInf x -> TmDefer (TimeInf, tot stack x |> NotTemporalTerm)
          | PTmLet (x, r, b) ->
            TmLet (x, r |> tot stack, b |> tot stack)
          | PTmLetDefer (time, x, r, b) ->
            TmDefer (time,
              TmLetRun (x, time, r |> tot stack, b |> tot stack) |> sameInfoOf ptm
            )
          | PTmOp2 (l, op, r) when ctx |> Context.findConstructor [op] (Some [l; r]) |> Option.isSome ->
            TmConstruct ([op], [l; r] |> List.map (tot stack))
          | PTmOp2 (l, op, r) ->
            PTmApply (PTmApply (PTmVar [op] |> sameInfoOf ptm, l) |> sameInfoOf ptm , r)
              |> sameInfoOf ptm
              |> tot stack
              |> itemof
          | PTmIf (x, t, e) ->
            PTmMatch (x, [(PTmLiteral (LBool true) |> sameInfoOf ptm , t); (PTmLiteral (LBool false) |> sameInfoOf ptm , e) ])
              |> sameInfoOf ptm
              |> tot stack
              |> itemof
          | PTmMatch (x, cs) ->
            TmApply (TmFunction (FunNormal, cs |> List.map (totc stack)) |> sameInfoOf ptm, [x |> tot stack])
          | PTmFunction cs ->
            TmFunction (FunNormal, cs |> List.map (totc stack))
          | PTmFixpoint (n, cs) ->
            TmFunction (FunFixpoint, cs |> List.map (totc (n :: stack)))
    in tot [] pt

  let rec toToplevelBase (ctx: Context<'Term>)
                         (parser: string -> string -> ParsedTopLevelWithSource list)
                         (converter: Context<'Term> -> UntypedTerm -> 'Term)
                         (defaultCtx: Context<'Term>)
                         (moduleName: qualified_name)
                         (ptop: ParsedTopLevelWithSource list)
                         : TopLevel<'Term> list * Context<'Term> =
    let inline (+>>) x (xs, ctx) = (x :: xs, ctx)
    let inline (@>>) xs1 (xs2, ctx) = (xs1 @ xs2, ctx)
    let inline orEmpty x = x |> Option.defaultValue (TyTuple [] |> NotTemporal)
    let rec tot ctx moduleName ptops =
      match (ptops |> List.map itemof, ptops) with
        | toplevel :: _, toplevel_WithSource :: remaining ->
          let info = toplevel_WithSource.info
          match toplevel with
            | PTopImport filename ->
              let sourceDir =
                match info with
                  | SourceFile i when File.Exists i.fileName -> Path.GetDirectoryName i.fileName
                  | _ -> Directory.GetCurrentDirectory()
              let destPath = Path.Combine(sourceDir, filename) |> Path.GetFullPath
              if File.Exists destPath |> not then
                sprintf "Import: file '%s' not found" destPath |> ParserFailed |> raise
              let (extTop, extCtx) =
                parser destPath (File.ReadAllText destPath)
                  |> tot defaultCtx [destPath |> Path.GetFileName]
              extTop @>> tot (extCtx @ ctx) moduleName remaining
            | PTopOpen qn ->
              TopOpen (qn, info) +>> tot (ctx |> Context.openModule qn) moduleName remaining
            | PTopModule (name, toplevels) ->
              let top = TopModule (name, toplevels |> tot ctx (moduleName @ [name]) |> fst, info)
              top +>> tot (ctx |> Context.addToplevels [top] (fun _ -> id)) moduleName remaining
            | PTopTermDef (name, args, pt) ->
              let tm =
                makeFun (args, pt)
                   |> sameInfoOf pt
                   |> toUntypedTerm ctx
                   |> converter ctx
              TopTermDef (name, tm, info)
              +>> tot (ctx |> Context.addTerm name tm) moduleName remaining
            | PTopDo pt ->
              let tm = toUntypedTerm ctx pt |> converter ctx
              TopDo (tm, info) +>> tot ctx moduleName remaining
            | PTopDataTypeDef (kind, name, typrms, cstrs) ->
              let qualifiedName = moduleName @ [name]
              let kind' =
                match kind, checkRecursiveDataType qualifiedName cstrs with
                  | x, y when x = y -> x
                  | DTInductive, DTCoinductive ->
                    ParserFailedWithPos ("this is not an inductive definition", toplevel_WithSource.info) |> raise
                  | DTVariant, _ ->
                    ParserFailedWithPos ("this is not a variant definition", toplevel_WithSource.info) |> raise
                  | x, _ -> x
              let ctx' =
                match kind' with
                  | DTVariant -> ctx
                  | DTInductive ->
                    ctx |> Context.addType name 
                           (TyScheme (
                              set typrms, 
                              TyDataTypeSelf (qualifiedName, typrms |> List.map NTTyVar) |> NotTemporal))
                  | _ -> ParserFailed "coinductive datatypes are not supported" |> raise
              let cstrs' =
                cstrs |> List.map (
                     (fun (n, pt) -> (n, pt |> Option.map (toKnownType ctx') |> orEmpty)) 
                  >> (fun (n, ty) ->
                          match ty with
                            | NotTemporal (TyTuple ts) ->
                              { name = n; args = ts }
                            | _ ->
                              { name = n; args = [ty] })
                )
              let printer : EqualityNull<string * Printf.StringFormat<string -> string>> =
                if is_op name then EValue (sprintf " %s " name, "%s") else ENull
              let ty = 
                TyDataType (
                  qualifiedName, 
                  typrms |> List.map NTTyVar, 
                  { cstrs = cstrs'; kind = kind'; printer = printer; source = info })
                |> NotTemporal
                |> generalizeAllFV
              TopTypeDef (name, ty, info) +>> tot (ctx |> Context.addType name ty) moduleName remaining
        | [], _
        | _, [] -> ([], ctx)
    tot ctx moduleName ptop
