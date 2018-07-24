namespace nml.Parser

open System
open System.IO
open nml
open nml.Contexts
open nml.Helper
open nml.Typer
open nml.Ast

exception ParserFailed of string
exception ParserFailedAtEof

[<AutoOpen>]
module ParsedAst =
  type ParsedType =
    | PTyVar of qualified_name
    | PTyApp of qualified_name * ParsedType list
    | PTyFun of ParsedType * ParsedType
    | PTyTuple of ParsedType * ParsedType
    | PTyDefer of ParsedType
    | PTyExplicit of ParsedType

  type ParsedTermWithInfo = WithInfo<ParsedTerm>
  and ParsedTerm =
    | PTmVar of qualified_name
    | PTmLiteral of Literal
    | PTmTuple of ParsedTermWithInfo list
    | PTmList of ParsedTermWithInfo list
    | PTmFun of string  * ParsedTermWithInfo
    | PTmFunUnit of ParsedTermWithInfo
    | PTmApply of ParsedTermWithInfo * ParsedTermWithInfo
    | PTmIf of ParsedTermWithInfo * ParsedTermWithInfo * ParsedTermWithInfo
    | PTmLet of string * ParsedTermWithInfo * ParsedTermWithInfo
    | PTmFixMatch of string * (ParsedTermWithInfo * ParsedTermWithInfo) list
    | PTmDefer of ParsedTermWithInfo
    | PTmRun of ParsedTermWithInfo
    | PTmLetDefer of string * ParsedTermWithInfo * ParsedTermWithInfo
    | PTmOp2 of ParsedTermWithInfo * string * ParsedTermWithInfo
    | PTmMatch of ParsedTermWithInfo * (ParsedTermWithInfo * ParsedTermWithInfo) list
  
  type PTTypeKind = PTTKVariant | PTTKInductive | PTTKCoinductive

  type ParsedTopLevelWithInfo = WithInfo<ParsedTopLevel>
  and ParsedTopLevel =
    | PTopImport of filename:string
    | PTopOpen of qualified_name
    | PTopModule of string * ParsedTopLevelWithInfo list
    | PTopTermDef of string * string list * ParsedTermWithInfo
    | PTopTypeDef of kind: PTTypeKind * name:string * tyParams:string list * cstrs: (string * ParsedType option) list
    | PTopDo of ParsedTermWithInfo

module ParserUtils =

  let checkRecursiveDataType (name: qualified_name) (cstrs: (string * ParsedType option) list) =
    let rec dig = function
      | PTyVar x -> x = name
      | PTyApp (x, ts) -> x = name || ts |> List.exists dig
      | PTyExplicit x
      | PTyDefer x -> dig x
      | PTyFun (a, b)
      | PTyTuple (a, b) -> dig a || dig b
    let cases =
      cstrs |> List.map snd
            |> List.map (function Some x -> dig x | None -> false)
    match (cases |> List.exists id, cases |> List.forall id) with
      | false, false -> PTTKVariant
      | true, false -> PTTKInductive
      | true, true -> PTTKCoinductive
      | false, true -> failwith "impossible"

  let makeList t = 
    let rec m = function
      | [ { item = PTmOp2 (l, ";", r) }] -> l :: m [r]
      | x -> x
    in m t |> PTmList
  
  let makeFun (args, body) =
    match args with
      | "()" :: [] -> PTmFunUnit body
      | _ -> body |> List.foldBack (fun x t -> PTmFun(x, t) |> sameInfoOf body) args |> itemof
  
  let makeLet (vars, value, expr) =
    assert (vars <> []);
    let (h :: t) = vars in
    if (List.length t = 0) then
      PTmLet (h, value, expr)
    else
      PTmLet (h, makeFun (t, value) |> sameInfoOf value, expr)

  let toDefer x =
    match x.item with
      | PTmLet(n, r, b) -> PTmLetDefer(n, r, b) |> sameInfoOf x
      | _ -> PTmDefer x |> sameInfoOf x

  let rec toKnownType ctx =
    function
      | PTyVar ["Unit"] -> TyUnit
      | PTyVar ["Bool"] -> TyBool
      | PTyVar x ->
        match (ctx |> Context.findType x) with
          | Some (TyDataType (n, [], cts, p, info)) ->
            TyDataType (n, [], cts, p, info)
          | Some (TyDataTypeSelf (n, [])) ->
            TyDataTypeSelf (n, [])
          | Some (TyDataType _)
          | Some (TyDataTypeSelf _) ->
            sprintf "Insufficient type argument(s) for type constructor '%s'" (sprint_qualified x) |> ParserFailed |> raise
          | Some t -> t
          | None ->
            match x with
              | [v] -> TyVar v
              | _ -> sprintf "Unknown type '%s'" (sprint_qualified x) |> ParserFailed |> raise
      | PTyDefer x -> TyDeferred (toKnownType ctx x)
      | PTyFun (a, b) -> TyFun (toKnownType ctx a, toKnownType ctx b)
      | PTyTuple (l, r) ->
        match (r, toKnownType ctx r) with
          | PTyTuple _, TyTuple ts ->
            TyTuple (toKnownType ctx l :: ts)
          | _, x -> TyTuple [toKnownType ctx l; x]
      | PTyApp (name, ts) ->
        match (ctx |> Context.findType name) with
          | Some (TyDataType (n, vts, cts, p, info)) ->
            if (List.length ts <> List.length vts) then
              sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name) |> ParserFailed |> raise
            
            let ts = ts |> List.map (toKnownType ctx)
            let asgn = 
              vts |> List.map2 (fun x -> function | TyVar y -> (y, x) |> Some | _ -> None) ts
                  |> List.choose id
                  |> Map.ofList
                  |> Assign in
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            TyDataType (n, ts, cts', p, info)
          | Some (TyDataTypeSelf (n, vts)) ->
            if List.length ts = List.length vts then
              TyDataTypeSelf (n, ts |> List.map (toKnownType ctx))
            else
              sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name) |> ParserFailed |> raise 
          | _ ->
            sprintf "Unknown datatype: '%s'" (sprint_qualified name) |> ParserFailed |> raise
      | PTyExplicit x -> toKnownType ctx x
  
  let toUntypedTerm ctx pt =
    let rec getVariablePatterns =
      function
        | UTmFreeVar [x] when x <> "_" -> [x]
        | UTmTuple xs 
        | UTmConstruct (_, xs) 
        | UTmApply (UTmFreeVar ["::"], xs) -> xs |> List.map getVariablePatterns |> List.concat 
        | _ -> []

    let rec totc stack (pt, bd) =
      let fv = pt |> tot [] |> getVariablePatterns in
      (pt |> tot (List.append fv stack), bd |> tot (List.append fv stack))
    
    and tot stack ptm =
      match (ptm.item) with
      | PTmVar x ->
        // constructor without arguments
        if (ctx |> Context.findConstructor x (Some []) |> Option.isSome) then
          UTmConstruct (x, [])
        else
          match x with
            | [v] ->
              match (stack |> List.tryFindIndex ((=) v)) with
                | Some i -> UTmBoundVar i
                | None -> UTmFreeVar x
            | _ -> UTmFreeVar x
      | PTmLiteral l -> UTmLiteral l
      | PTmTuple xs -> UTmTuple (xs |> List.map (tot stack))
      | PTmList [] -> UTmConstruct (["Nil"], [])
      | PTmList xs -> xs |> List.rev |> List.fold (fun l x -> UTmConstruct (["Cons"], [tot stack x; l])) (UTmConstruct (["Nil"], []))
      | PTmFun (arg, body) -> UTmFun (body |> tot (arg :: stack))
      | PTmFunUnit body -> UTmFun (body |> tot ("" :: stack))
      // immediate constructor handling
      | PTmApply ({ item = PTmVar x }, { item = PTmTuple xs })
        when (ctx |> Context.findConstructor x (Some xs) |> Option.isSome) ->
        UTmConstruct (x, xs |> List.map (tot stack))
      // immediate constructor handling
      | PTmApply ({ item = PTmVar x }, y)
        when (ctx |> Context.findConstructor x (Some [y]) |> Option.isSome)  ->
        UTmConstruct (x, [y |> tot stack])
      | PTmApply (l, r) ->
        match (l |> tot stack) with
          | UTmApply (l', r') -> UTmApply (l', List.append r' [tot stack r])
          | x -> UTmApply (x, [tot stack r])
      | PTmDefer x -> UTmDefer (tot stack x)
      | PTmRun x -> UTmRun (tot stack x)
      | PTmLet (x, r, b) ->
        UTmLet (x, r |> tot stack, b |> tot stack)
      | PTmLetDefer (x, r, b) ->
        UTmLetDefer (x, r |> tot stack, b |> tot stack)
        // UTmDefer (PTmLet (x, PTmRun r, b) |> tot stack)
      | PTmOp2 (l, op, r) ->
        PTmApply (PTmApply (PTmVar [op] |> sameInfoOf ptm , l) |> sameInfoOf ptm , r) |> sameInfoOf ptm |> tot stack
      | PTmIf (x, t, e) ->
        PTmMatch (x, [ (PTmLiteral (LBool true) |> sameInfoOf ptm , t); (PTmLiteral (LBool false) |> sameInfoOf ptm , e) ]) |> sameInfoOf ptm |> tot stack
      | PTmMatch (x, cs) ->
        UTmMatch (x |> tot stack, cs |> List.map (totc stack))
      | PTmFixMatch (n, cs) ->
        UTmFixMatch (cs |> List.map (totc (n :: stack)))
      | x ->
        NotImplementedException(sprintf "%A is not yet supported" (x.GetType().Name)) |> raise
    in tot [] pt

  let rec internal toToplevelBase ctx parser defaultCtx (moduleName: qualified_name) =
    let inline (+>>) x (xs, ctx) = (x :: xs, ctx)
    let inline (@>>) xs1 (xs2, ctx) = (xs1 @ xs2, ctx)
    let inline orEmpty x = x |> Option.defaultValue (TyTuple [])
    let rec tot ctx moduleName ptops =
      match (ptops |> List.map itemof, ptops) with
        | toplevel :: _, toplevel_withinfo :: remaining ->
          let info = toplevel_withinfo.info
          match toplevel with
            | PTopImport filename ->
              let sourceDir =
                match info with
                  | Some i when File.Exists i.fileName -> Path.GetDirectoryName i.fileName
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
              let top = TopModule(name, toplevels |> tot ctx (moduleName @ [name]) |> fst, info)
              top +>> tot (ctx |> Context.addToplevels [top] (fun _ -> id)) moduleName remaining
            | PTopTermDef (name, args, pt) ->
              let tm =
                makeFun (args, pt)
                   |> sameInfoOf pt
                   |> toUntypedTerm ctx
              let (tm, ty) = Typer.inferWithContext (ctx |> Context.termMap fst) tm
              TopTermDef (name, (ty, tm), info) +>> tot (ctx |> Context.addTerm name (ty, tm)) moduleName remaining
            | PTopDo pt ->
              let tm = toUntypedTerm ctx pt
              let (tm, ty) = Typer.inferWithContext (ctx |> Context.termMap fst) tm
              TopDo ((ty, tm), info) +>> tot ctx moduleName remaining
            | PTopTypeDef (kind, name, typrms, cstrs) ->
              let qualifiedName = moduleName @ [name]
              let ctx' =
                match kind with
                  | PTTKVariant -> ctx
                  | PTTKInductive -> ctx |> Context.addType name (TyDataTypeSelf(qualifiedName, typrms |> List.map TyVar))
                  | _ -> ParserFailed "coinductive datatypes are not supported" |> raise
              let cstrs' =
                cstrs |> List.map (fun (n, pt) -> (n, pt |> Option.map (toKnownType ctx') |> orEmpty))
                      |> List.map (fun (n, ty) ->
                          match ty with
                            | TyTuple ts ->
                              { name = n; args = ts; isRecursive = ts |> List.exists (containsSelf qualifiedName) }
                            | _ ->
                              { name = n; args = [ty]; isRecursive = containsSelf qualifiedName ty }
                         )
              let printer : EqualityNull<string * Printf.StringFormat<string -> string>> =
                if is_op name then EValue (sprintf " %s " name, "%s") else ENull
              let ty = TyDataType(qualifiedName, typrms |> List.map TyVar, cstrs', printer, info)
              TopTypeDef(name, ty, info) +>> tot (ctx |> Context.addType name ty) moduleName remaining
        | [], _
        | _, [] -> ([], ctx)
    tot ctx moduleName
