module nml.Ast

open System
open FSharp.Collections

type qualified_name = string list

[<Struct>]
type SourceLocation = 
  {
    fileName: string
    startPos: FParsec.Position
    endPos:   FParsec.Position
  }
  override this.ToString() =
    sprintf "%s, Ln %i/Col %i"
            this.fileName
            this.startPos.Line
            this.startPos.Column

// Some: user defined / None: builtin
type Source = SourceFile of SourceLocation | Builtin 
  with
    override this.ToString() = match this with SourceFile x -> to_s x | _ -> "builtin"
    member x.IsFile = match x with SourceFile _ -> true | _ -> false
    member x.Location = match x with SourceFile l -> l | _ -> undefined "not a location!"
    static member map2 f x y =
      match x, y with
        | SourceFile x, SourceFile y -> f x y |> SourceFile
        | _ -> Builtin

type WithSource<'T> = With<'T, Source>

[<Struct>]
type TyDataTypeKind =
  | DTVariant
  | DTInductive
  | DTCoinductive
  override x.ToString() =
    match x with
      | DTVariant -> "variant"
      | DTInductive -> "inductive"
      | DTCoinductive -> "coinductive"

#nowarn "0342" // disable warning about not overloading Object.Equals()
[<Struct; CustomComparison; StructuralEquality>]
type TemporalTime =
  | TimeN of nat
  | TimeInf
  with
    override x.ToString() =
      match x with
        | TimeN i -> string i
        | TimeInf -> "inf"
    static member (+) (a: TemporalTime, b: TemporalTime) =
      match a, b with
        | TimeN i, TimeN j -> TimeN (i+j)
        | TimeInf, _
        | _, TimeInf -> TimeInf
    static member (-) (a: TemporalTime, b: TemporalTime) =
      match a, b with
        | TimeInf, TimeInf -> TimeN Z
        | TimeInf, TimeN _ -> TimeInf
        | TimeN i, TimeN j when i>=j -> TimeN (i-j)
        | _ -> TimeN Z
    interface System.IComparable with
      member x.CompareTo yo =
        match yo with
          | :? TemporalTime as y ->
            match x, y with
              | TimeN i, TimeN j -> compare i j
              | TimeInf, TimeInf -> 0
              | TimeInf, TimeN _ -> 1
              | TimeN _, TimeInf -> -1
          | _ -> invalidArg "yo" "Not a TemporalTime"

type TemporalType = TyTemporal of TemporalTime * Type with
  member inline x.time =
    match x with TyTemporal (ti, _) -> ti
  override x.ToString() =
    let rec to_sc = function
        | TyVar s -> s
        | TyDataType (n, [], _) 
        | TyDataTypeSelf (n, []) -> sprint_qualified n
        | c -> sprintf "(%s)" (to_st c)
    and to_sc_tmp = function
        | TyTemporal (TimeN Z, t) -> to_sc t
        | x -> sprintf "(%s)" (to_s x)
    and to_st = function
        | TyVar s -> s
        | TyDataType (n, [], _) -> sprint_qualified n
        | TyDataType (_, ts, { printer = EValue (c, f)}) -> 
          sprintf f (ts |> List.map to_sc_tmp |> String.concat c)
        | TyDataTypeSelf (n, []) -> sprint_qualified n
        | TyDataType (n, ts, _)
        | TyDataTypeSelf (n, ts) ->
          sprintf "%s %s" (sprint_qualified n) (ts |> List.map to_sc_tmp |> String.concat " ")
    match x with
      | TyTemporal (TimeN Z, t) -> to_st t
      | TyTemporal (TimeN n, t) ->
        sprintf "Next[%i] %s" n (to_sc t)
      | TyTemporal (TimeInf, t) ->
        sprintf "Finally %s" (to_sc t)

and PolyType = TyScheme of Set<string> * TemporalType with
  override x.ToString() =
    match x with
      | TyScheme (When Set.isEmpty, tt) -> to_s tt
      | TyScheme (xs, tt) -> sprintf "forall %s. %s" (xs |> String.concat " ") (to_s tt) 

and Type =
  | TyVar of string
  | TyDataType of qualified_name * TemporalType list * TyDataTypeProp
  | TyDataTypeSelf of qualified_name * TemporalType list
  override x.ToString() = TyTemporal (TimeN Z, x) |> to_s

and TyDataTypeProp = {
  kind: TyDataTypeKind
  cstrs: Constructor list
  printer: EqualityNull<string * Printf.StringFormat<string -> string>>
  source: Source
}

and Constructor = {
  name: string
  args: TemporalType list
}

type TemporalType with
  member x.fv() = 
    let rec fvOf (TyTemporal (_, ty)) =
      match ty with
        | TyVar n -> set [n]
        | TyDataType (_, vs, { cstrs = ts }) -> 
          ts |> List.collect (fun c -> c.args |> List.map fvOf)
             |> List.fold Set.union (set [])
             |> Set.union (vs |> List.map fvOf |> Set.unionMany)
        | TyDataTypeSelf (_, vs) ->
          vs |> List.map fvOf |> Set.unionMany
    fvOf x

type PolyType with
  member inline x.fv() =
    let (TyScheme (tvs, tty)) = x
    Set.difference tvs (tty.fv())

type Type with
  member inline x.fv() =
    TyTemporal(TimeN Z, x).fv() 

[<AutoOpen>]
module TypeHelper =
  let inline Constructor (name, args) = { name = name; args = args }
  let inline MonoType ty = TyScheme (set [], ty)
  let inline NotTemporal t = TyTemporal (TimeN Z, t)
  let (|NotTemporal|_|) = function
    | TyTemporal (TimeN Z, t) -> Some t
    | _ -> None
  let (|TySchemeNotTemporal|_|) = function
    | TyScheme (vs, NotTemporal t) -> Some (vs, t)
    | _ -> None

[<AutoOpen>]
module PrimitiveTypes =
  let inline private PrimType (name, kind, ts, cstrs, po) =
    TyDataType ([name],
                ts,
                {
                  kind = kind;
                  cstrs = cstrs |> List.map Constructor;
                  printer = po;
                  source = Builtin 
                })
  let inline private genPattern ty f =
    match ty with
      | TyDataType ([name], _, { kind = kind; cstrs = cstrs; source = Builtin }) ->
        function
          | TyDataType ([name'], ts', { kind = kind'; cstrs = cstrs'; source = Builtin })
            when name = name' && kind = kind' && cstrs = cstrs' -> f ts'
          | _ -> None
      | _ -> fun _ -> None
  let dummy = TyVar "dummy" |> NotTemporal

  let inline TyFun (a, b) = PrimType ("->", DTVariant, [a;b], [], EValue (" -> ", "%s"))
  let private tfd = TyFun (dummy, dummy)
  let (|TyFun|_|) = genPattern tfd (function [a;b] -> Some (a, b) | _ -> None)

  let inline TyTuple ts = PrimType ("*", DTVariant, ts, [], EValue (" * ", "%s"))
  let private ttd = TyTuple []
  let (|TyTuple|_|) = genPattern ttd Some

  let TyBool = PrimType ("Bool", DTVariant, [], [("true", []); ("false", [])], ENull)
  let private tbd = TyBool
  let (|TyBool|_|) = genPattern tbd (fun _ -> Some TyBool)

  let TyNat = PrimType ("Nat", DTInductive, [], [("S", [TyDataTypeSelf(["Nat"], []) |> NotTemporal]); ("0", [])], ENull)
  let private tnd = TyNat
  let (|TyNat|_|) = genPattern tnd (fun _ -> Some TyNat)

  let TyUnit = PrimType ("Unit", DTVariant, [], [], ENull)
  let private tud = TyUnit
  let (|TyUnit|_|) = genPattern tud (fun _ -> Some TyUnit)

  let TyList a =
    PrimType ("List", DTInductive, [a],
      [
        ("::", [a; TyDataTypeSelf(["List"],[a]) |> NotTemporal]);
        ("[]", [])
      ], ENull)
  let private tul = TyList dummy
  let (|TyList|_|) = genPattern tul (function [t] -> Some t | _ -> None)

  let TyOption a =
    PrimType ("Option", DTVariant, [a],
      [
        ("Some", [a]);
        ("None", [])
      ], ENull)
  let private tod = TyOption dummy
  let (|TyOption|_|) = genPattern tod (function [t] -> Some t | _ -> None)

type Literal =
  | LNat of nat
  | LBool of bool
  | LUnit
  override x.ToString() =
    match x with
      | LNat i -> i.ToString()
      | LBool b -> if b then "true" else "false"
      | LUnit -> "()"

type FunctionType =
  | FunNormal
  | FunFixpoint
//  | FunCofixpoint

type TermWithInfo<'Info> = With<Term<'Info>, 'Info>
and  TemporalTermWithInfo<'Info> = With<TemporalTerm<'Info>, 'Info>

and MatchPattern =
  | MtLiteral of Literal
  | MtBoundVar of int
  | MtWildcard
  | MtTuple of MatchPattern list
  | MtConstruct of qualified_name * MatchPattern list
  with
    member x.asTerm() =
      let rec ast x =
        With.noinfo <|
          match x with
            | MtLiteral l -> TmLiteral l
            | MtBoundVar i -> TmBoundVar i
            | MtWildcard -> TmFreeVar ["_"]
            | MtTuple xs -> TmTuple (xs |> List.map ast)
            | MtConstruct (n, xs) -> TmConstruct (n, xs |> List.map ast)
      in ast x

and TemporalTerm<'Info> =
  | TmRun    of TemporalTime * TermWithInfo<'Info>
  | TmLetRun of string * TemporalTime * TermWithInfo<'Info> * TermWithInfo<'Info>
  with
    static member tos stack uniq = function
      | TmRun (TimeN Z, tm) -> Term<'Info>.tos stack uniq tm
      | TmRun (TimeN n, tm) ->
        sprintf "(run[%i] %s)" n (Term<'Info>.tos stack uniq tm)
      | TmRun (TimeInf, tm) ->
        sprintf "(run[inf] %s)" (Term<'Info>.tos stack uniq tm)
      | TmLetRun (s, TimeN Z, t, u) ->
        sprintf "let %s = %s in %s" s (Term<'Info>.tos stack uniq t) (Term<'Info>.tos stack uniq u)
      | TmLetRun (s, TimeN n, t, u) ->
        sprintf "let-run[%i] %s = %s in %s" n s (Term<'Info>.tos stack uniq t) (Term<'Info>.tos stack uniq u)
      | TmLetRun (s, TimeInf, t, u) ->
        sprintf "let-run[inf] %s = %s in %s" s (Term<'Info>.tos stack uniq t) (Term<'Info>.tos stack uniq u)
    override x.ToString() = TemporalTerm<'Info>.tos [] 0 x

and Term<'Info> =
  | TmLiteral of Literal
  | TmBoundVar of int
  | TmFreeVar of qualified_name
  | TmLet of string * TermWithInfo<'Info> * TermWithInfo<'Info> 
  | TmTuple of TermWithInfo<'Info> list
  | TmConstruct of qualified_name * TermWithInfo<'Info> list
  | TmApply of TermWithInfo<'Info> * TermWithInfo<'Info> list
  | TmFunction of FunctionType * (MatchPattern * TermWithInfo<'Info>) list
  | TmDefer  of TemporalTime * TemporalTermWithInfo<'Info> 
  | TmBuiltin of string * PolyType * EqualityNull<IBuiltinFunc>
  | TmRunnableBuiltin of string * PolyType * EqualityNull<IRunnableBuiltinFunc>
  with
    static member tos stack uniq (x: TermWithInfo<'Info>) =
      let inline tos x = Term<'Info>.tos x
      let rec tosc stack uniq (pt, bd) =
        let rec countFvOfPattern = function 
          | MtBoundVar _ -> 1
          | MtConstruct (_, xs) ->
            xs |> List.map countFvOfPattern |> List.sum
          | _ -> 0
        let (nvs, uniq) = genUniqs uniq (countFvOfPattern pt)
        let stack = List.append nvs stack
        sprintf "%s -> %s" (tos stack uniq (pt.asTerm())) (tos stack uniq bd) 
      match With.itemof x with
        | TmLiteral l -> to_s l
        | TmBoundVar i -> stack |> List.tryItem i ?| sprintf "{%i}" i
        | TmFunction (FunNormal, [MtBoundVar 0, b]) ->
          let (nv, uniq) = genUniq uniq in
          sprintf "(fun %s -> %s)" nv (b |> tos (nv :: stack) uniq)
        | TmFreeVar n -> sprint_qualified n
        | TmLet (x, v, b) -> sprintf "let %s = %s in %s" (handle_op x) (v |> tos stack uniq) (b |> tos stack uniq)
        | TmTuple xs -> sprintf "(%s)" (xs |> List.map (tos stack uniq) |> String.concat ", ")
        | TmConstruct (n, []) -> sprint_qualified n
        | TmConstruct (n, [x]) -> sprintf "(%s %s)" (sprint_qualified n) (x |> tos stack uniq)
        | TmConstruct (n, xs) ->
          sprintf "(%s (%s))" (sprint_qualified n) (xs |> List.map (tos stack uniq) |> String.concat ", ")
        | TmApply (Item (TmFreeVar [x]), [l; r]) when (is_op x) ->
          sprintf "(%s %s %s)" (l |> tos stack uniq) x (r |> tos stack uniq)
        | TmApply (Item (TmFunction (FunNormal, cs)), [x]) ->
          sprintf "(match %s with %s)" (x |> tos stack uniq) (cs |> List.map (tosc stack uniq) |> String.concat " | ")
        | TmApply (x, ys) ->
          sprintf "(%s %s)" (x |> tos stack uniq) (ys |> List.map (tos stack uniq) |> String.concat " ")
        | TmFunction (ft, cs) -> 
          match ft with
            | FunNormal ->
              sprintf "(function %s)" (cs |> List.map (tosc stack uniq) |> String.concat " | ")
            | FunFixpoint ->
              let (nv, uniq) = genUniq uniq in
              sprintf "(fixpoint %s of %s)" nv (cs |> List.map (tosc (nv :: stack) uniq) |> String.concat " | ")
        | TmDefer (TimeN Z, Item x) -> TemporalTerm<'Info>.tos stack uniq x
        | TmDefer (TimeN (S n), x) ->
          sprintf "(@ %s @)" ((TmDefer (TimeN n, x)) |> With.noinfo |> tos stack uniq)
        | TmDefer (TimeInf, Item x) ->
          sprintf "<@ %s @>" (TemporalTerm<'Info>.tos stack uniq x)
        | TmBuiltin (s, _, _)
        | TmRunnableBuiltin (s, _, _) -> s
    override x.ToString() = Term<'Info>.tos [] 0 (With.noinfo x)

and IBuiltinFunc =
  abstract member Eval: TermWithInfo<unit> list -> TermWithInfo<unit> option
and IRunnableBuiltinFunc =
  abstract member Eval: (TemporalTime * TermWithInfo<unit> list) -> TermWithInfo<unit> option

[<AutoOpen>]
module TermHelper =
  type BuiltinFunc =
    | BuiltinFunc of (TermWithInfo<unit> list -> TermWithInfo<unit> option) with
    interface IBuiltinFunc with
      member this.Eval(tm) = let (BuiltinFunc f) = this in f tm
  let inline BuiltinFunc f = BuiltinFunc f :> IBuiltinFunc

  type RunnableBuiltinFunc =
    | RunnableBuiltinFunc of ((TemporalTime * TermWithInfo<unit> list) -> TermWithInfo<unit> option) with
    interface IRunnableBuiltinFunc with
      member this.Eval(tm) = let (RunnableBuiltinFunc f) = this in f tm
  let inline RunnableBuiltinFunc f = RunnableBuiltinFunc f :> IRunnableBuiltinFunc

  let inline NotTemporalTerm t = TmRun (TimeN Z, t) |> With.sameInfoOf t
  let (|NotTemporalTerm|_|) = function
    | Item (TmRun (TimeN Z, t)) -> Some t
    | _ -> None

type UntypedTerm = TermWithInfo<Source>
type UntypedTemporalTerm = TemporalTermWithInfo<Source>
type EracedTerm = TermWithInfo<unit>
type EracedTemporalTerm = TemporalTermWithInfo<unit>

[<Struct>]
type TypedTermProp = { ty: TemporalType; source: Source }
type TypedTerm = TermWithInfo<TypedTermProp>
type TypedTemporalTerm = TemporalTermWithInfo<TypedTermProp>

type Term<'Info> with
  member x.fv() =
    let inline fv (x: TermWithInfo<'Info>) = x.item.fv()
    match x with
      | TmFreeVar [x] when x <> "_" -> set [x]
      | TmApply (l, rs) ->
        l :: rs |> List.collect (fv>> Set.toList) |> Set.ofList
      | TmTuple xs
      | TmConstruct (_, xs) ->
        xs |> List.collect (fv >> Set.toList) |> Set.ofList
      | TmFunction (_, cs) ->
        cs |> List.collect (fun (pt, bd) -> Set.difference (fv (pt.asTerm())) (fv bd) |> Set.toList)
           |> Set.ofList
      | TmLet (x, v, b) ->
        Set.union (fv v) (fv b) |> Set.difference (set [x])
      | TmFreeVar _
      | TmLiteral _
      | TmBoundVar _
      | TmBuiltin _
      | TmRunnableBuiltin _ -> set []
      | TmDefer (_, Item x) -> x.fv()
  static member mapInfo (f: 'Info -> 'NewInfo, x: TermWithInfo<'Info>) =
    let inline mapInfo f x = Term<'Info>.mapInfo(f, x)
    With.info (f x.info) <|
      match x.item with
        | TmLiteral l -> TmLiteral l
        | TmBoundVar i -> TmBoundVar i
        | TmFreeVar v -> TmFreeVar v
        | TmFunction (ft, cases) -> TmFunction (ft, cases |> List.map (Tuple.map2 id (mapInfo f)))
        | TmLet (x, v, b) -> TmLet (x, mapInfo f v, mapInfo f b)
        | TmTuple xs -> TmTuple (xs |> List.map (mapInfo f))
        | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (mapInfo f))
        | TmApply (x, ys) -> TmApply (mapInfo f x, ys |> List.map (mapInfo f))
        | TmDefer (time, x) -> TmDefer (time, TemporalTerm<_>.mapInfo(f, x))
        | TmBuiltin (x, t, b) -> TmBuiltin (x, t, b)
        | TmRunnableBuiltin (x, t, b) -> TmRunnableBuiltin (x, t, b)

and TemporalTerm<'Info> with
  member x.fv() =
    match x with
      | TmRun   (_, Item x) -> x.fv()
      | TmLetRun (x, _, ta, tb) ->
        Set.union (ta.item.fv()) (tb.item.fv()) |> Set.difference (set [x])
  static member mapInfo (f: 'Info -> 'NewInfo, x: TemporalTermWithInfo<'Info>) =
    With.info (f x.info) <|
      match x.item with
        | TmRun (time, x) -> TmRun (time, Term<_>.mapInfo(f, x))
        | TmLetRun (time, s, x, y) -> TmLetRun (time, s, Term<_>.mapInfo(f, x), Term<_>.mapInfo(f, y))

module Term =
  let inline getType (Info { ty = ty }) = ty
  let rec isStructural = function 
    | TmLiteral _ -> true
    | TmTuple xs
    | TmConstruct (_, xs) -> xs |> List.forall (With.itemof >> isStructural)
    | _ -> false

  let inline mapInfo (f: 'a -> 'b) (x: With< ^T, 'a >) : With< ^U, 'b > =
    (^T: (static member mapInfo: _ * _ -> _) f,x) 
  let inline addType orig ty x =
    x |> With.sameInfoOf orig |> With.mapInfo (fun src -> { ty = ty; source = src })
  let inline eraseType x =
    x |> mapInfo (fun _ -> ())

[<AutoOpen>]
module TmExtensions =
  let inline TmFun x = TmFunction (FunNormal, [MtBoundVar 0, x])
  let (|TmFun|_|) = function
    | TmFunction (FunNormal, [MtBoundVar 0, x]) -> Some x
    | _ -> None
  
  let inline TmCons (x, xs) = TmConstruct (["::"], [x; xs])
  let TmNil = TmConstruct (["[]"], [])
  let (|TmCons|_|) = function
    | TmConstruct (["::"], [x; xs]) -> Some (x, xs)
    | _ -> None
  let (|TmNil|_|) = function
    | TmConstruct (["[]"], []) -> Some TmNil
    | _ -> None

  let inline MtCons (x, xs) = MtConstruct (["::"], [x; xs])
  let MtNil = MtConstruct (["[]"], [])
  let (|MtCons|_|) = function
    | MtConstruct (["::"], [x; xs]) -> Some (x, xs)
    | _ -> None
  let (|MtNil|_|) = function
    | MtConstruct (["[]"], []) -> Some TmNil
    | _ -> None

type TopLevel<'Term> =
  | TopOpen of moduleName:qualified_name * info:Source
  | TopTermDef of name:string * tm:'Term * info:Source
  | TopDo of tm:'Term * info:Source
  | TopModule of name:string * stmts:TopLevel<'Term> list * info:Source
  | TopTypeDef of name:string * ty:PolyType * info:Source
  with
    member x.info =
      match x with
        | TopOpen (_, i)
        | TopTermDef (_, _, i)
        | TopDo (_, i)
        | TopModule (_, _, i)
        | TopTypeDef (_, _, i) -> i
    
    static member print toplevels =
      let rec p idt cs = [
        for c in cs do
          yield!
            match c with
              | TopTypeDef (_, TyScheme (_, NotTemporal (TyDataType (name, tyargs, { kind = kind; cstrs = cstrs }))), _) ->
                [
                  yield
                    if List.isEmpty tyargs then
                      sprintf "%s %s =" (to_s kind) (sprint_qualified name)
                    else
                      sprintf "%s %s %s ="
                        (to_s kind)
                        (sprint_qualified name)
                        (tyargs |> List.choose (function NotTemporal (TyVar x) -> Some x | _ -> None) |> String.concat " ")
                  for cstr in cstrs do
                    if cstr.args |> List.isEmpty then
                      yield sprintf "  | %s" (cstr.name |> handle_op)
                    else
                      yield sprintf "  | %s of %s"
                                    (cstr.name |> handle_op)
                                    (cstr.args |> List.map to_s |> String.concat " * ")
                ] |> List.map (indent idt)
              | TopTypeDef (name, ty, _) ->
                [ sprintf "newtype %s = %s" (handle_op name) (to_s ty)]
                |> List.map (indent idt)
              | TopTermDef (name, (ty, _), _) ->
                [ sprintf "def %s : %s"  (handle_op name) (to_s ty)]
                |> List.map (indent idt)
              | TopDo ((_, tm), _) ->
                [ "do"; sprintf "  %s" (to_s tm)]
                |> List.map (indent idt)
              | TopModule (name, cs', _) ->
                [
                  yield sprintf "module %s = begin" name
                  yield! p 2 cs'
                  yield "end"
                ] |> List.map (indent idt)
              | TopOpen (name, _) ->
                [ sprintf "open %s ;;" (sprint_qualified name)]
                |> List.map (indent idt)
      ]
      p 0 toplevels |> String.concat Environment.NewLine
