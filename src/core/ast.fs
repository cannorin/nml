module nml.Ast

open System

type qualified_name = string list

[<Struct>]
type source_info = 
  {
    fileName: string
    startPos: FParsec.Position
    endPos:   FParsec.Position
  }
  with
    override this.ToString() =
      sprintf "%s, Ln %i/Col %i"
              this.fileName
              this.startPos.Line
              this.startPos.Column

// Some: user defined / None: builtin
type source = source_info option

[<Struct>]
type WithInfo<'T> =
  {
    item: 'T
    info: source
  }

let inline itemof x = x.item
let inline infoof x = x.info
let inline itemMap f x = { item = f x.item; info = x.info }
let inline noinfo x = { item = x; info = None }
let inline sameInfoOf orig x = { item = x; info = orig.info }
let inline withinfo i x = { item = x; info = Some i }
let inline withinfof f (x, i) = { item = f x; info = Some i }

type Type =
  | TyVar of string
  | TyBool | TyUnit
  | TyFun of Type * Type
  | TyDeferred of Type
  | TyDataType of qualified_name * Type list * Constructor list * EqualityNull<string * Printf.StringFormat<string -> string>> * defined_location: source
  | TyDataTypeSelf of qualified_name * Type list
  | TyScheme of Set<string> * Type
  override x.ToString() =
    let inline to_sc dtOk x =
      match x with
        | TyVar _ | TyBool | TyUnit | TyDeferred _ -> to_s x
        | TyDataType (n, [], _, _, _) 
        | TyDataTypeSelf (n, []) -> sprint_qualified n
        | TyDataType _ | TyDataTypeSelf _ when dtOk -> to_s x
        | c -> "(" + (to_s c) + ")"
    in
    match x with
      | TyVar s -> s
      | TyBool -> "Bool"
      | TyUnit -> "Unit"
      | TyFun (a, b) -> sprintf "%s -> %s" (to_sc true a) (to_s b)
      | TyDeferred t -> sprintf "<%s>" (to_s t)
      | TyDataType (n, [], _, _, _) -> sprint_qualified n
      | TyDataType (n, ts, _, EValue (c, f), _) -> sprintf f (ts |> List.map (to_sc false) |> String.concat c)
      | TyDataTypeSelf (n, []) -> sprint_qualified n
      | TyDataType (n, ts, _, _, _)
      | TyDataTypeSelf (n, ts) -> sprintf "%s %s" (sprint_qualified n) (ts |> List.map (to_sc false) |> String.concat " ")
      | TyScheme (ts, t) -> sprintf "forall %s. %s" (ts |> String.concat " ") (to_s t)
and Constructor =
  { name: string; args: Type list; isRecursive: bool; }
  
let NewConst (n, a) =
  { name = n; args = a; isRecursive = false }

let NewRecConst (n, a) =
  { name = n; args = a; isRecursive = true }

let TypeOp (name, ts, po) =
  TyDataType (name, ts, [], po, None)

let Variant (name, ts, cs) =
  TyDataType (name, ts, cs, ENull, None)

let InductiveVariant (n, ts, f) =
  TyDataType (n, ts, TyDataTypeSelf (n, ts) |> f, ENull, None)

//let TChar = TypeOp ("Char", [], None)

let TyTuple ts =
  TypeOp (["*"], ts, EValue (" * ", "%s"))

let (|TyTuple|_|) = function | TyDataType (["*"], ts, [], _, _) -> Some ts | _ -> None

let TyList a =
  InductiveVariant (["List"], [a], (fun self -> [ NewConst ("Nil", []); NewRecConst ("Cons", [a; self]) ]))

let TyOption a =
  Variant (["Option"], [a], [ NewConst ("Some", [a]); NewConst ("None", []) ]);

let TyNat = 
  InductiveVariant (["Nat"], [], (fun self -> [ NewRecConst ("Succ", [self]); NewConst ("0", []) ]))

type Literal =
  | LNat of uint32
  | LBool of bool
  | LUnit
  override x.ToString() =
    match x with
      | LNat i -> i.ToString()
      | LBool b -> if b then "true" else "false"
      | LUnit -> "()"

type UntypedTerm =
  | UTmLiteral of Literal
  | UTmBoundVar of int
  | UTmFun of UntypedTerm
  | UTmFreeVar of qualified_name
  | UTmLet of string * UntypedTerm * UntypedTerm
  | UTmLetDefer of string * UntypedTerm * UntypedTerm
  | UTmConstruct of qualified_name * UntypedTerm list
  | UTmTuple of UntypedTerm list
  | UTmApply of UntypedTerm * UntypedTerm list
  | UTmMatch of UntypedTerm * (UntypedTerm * UntypedTerm) list
  | UTmFixMatch of (UntypedTerm * UntypedTerm) list
  | UTmExternal of NameCompared<UntypedTerm list -> UntypedTerm> * Type
  | UTmDefer of UntypedTerm
  | UTmRun of UntypedTerm
  override x.ToString() =
   let rec tosc stack uniq (pt, bd) =
      let rec countFvOfPattern = function 
        | UTmBoundVar _ -> 1
        | UTmTuple xs
        | UTmConstruct (_, xs) ->
          xs |> List.map countFvOfPattern |> List.sum
        | _ -> 0
      in
      let (nvs, uniq) = genUniqs uniq (countFvOfPattern pt) in
      let stack = List.append nvs stack in
      sprintf "%s -> %s" (tos stack uniq pt) (tos stack uniq bd)
    and tos stack uniq = function
      | UTmLiteral l -> to_s l
      | UTmBoundVar i -> stack |> List.tryItem i ?| sprintf "{%i}" i
      | UTmFun b ->
        let (nv, uniq) = genUniq uniq in
        sprintf "(fun %s -> %s)" nv (b |> tos (nv :: stack) uniq)
      | UTmFreeVar n -> sprint_qualified n
      | UTmLet (x, v, b) -> sprintf "let %s = %s in %s" (handle_op x) (v |> tos stack uniq) (b |> tos stack uniq)
      | UTmLetDefer (x, v, b) -> sprintf "let! %s = %s in %s" (handle_op x) (v |> tos stack uniq) (b |> tos stack uniq)
      | UTmConstruct (n, []) -> sprint_qualified n
      | UTmConstruct (n, [x]) -> sprintf "(%s %s)" (sprint_qualified n) (x |> tos stack uniq)
      | UTmConstruct (n, xs) -> sprintf "(%s (%s))" (sprint_qualified n) (xs |> List.map (tos stack uniq) |> String.concat ", ")
      | UTmTuple xs -> sprintf "(%s)" (xs |> List.map (tos stack uniq) |> String.concat ", ")
      | UTmApply (UTmFreeVar [x], [l; r]) when (is_op x) ->
        sprintf "(%s %s %s)" (l |> tos stack uniq) x (r |> tos stack uniq)
      | UTmApply (UTmExternal (f, _), [l; r]) when (is_op f.name) ->
        sprintf "(%s %s %s)" (l |> tos stack uniq) f.name (r |> tos stack uniq)
      | UTmApply (x, ys) -> sprintf "(%s %s)" (x |> tos stack uniq) (ys |> List.map (tos stack uniq) |> String.concat " ")
      | UTmMatch (x, cs) -> 
        sprintf "(match %s with %s)" (x |> tos stack uniq) (cs |> List.map (tosc stack uniq) |> String.concat " | ")
      | UTmFixMatch cs -> 
        let (nv, uniq) = genUniq uniq in
        sprintf "(fixpoint %s of %s)" nv (cs |> List.map (tosc (nv :: stack) uniq) |> String.concat " | ")
      | UTmExternal (f, _) -> handle_op f.name
      | UTmDefer x -> sprintf "<( %s )>" (x |> tos stack uniq)
      | UTmRun x -> sprintf "(run %s)" (x |> tos stack uniq)
    in tos [] 0 x

let ExternalFun nm typ f =
  UTmExternal({ name = nm; value = f }, typ)

type TopLevel<'Term> =
  | TopOpen of moduleName:qualified_name * info:source
  | TopTermDef of name:string * tm:'Term * info:source
  | TopDo of tm:'Term * info:source
  | TopModule of name:string * stmts:TopLevel<'Term> list * info:source
  | TopTypeDef of name:string * ty:Type * info:source
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
              | TopTypeDef (_, TyDataType (name, tyargs, cstrs, ENull, _), _) ->
                [
                  yield
                    if List.isEmpty tyargs then
                      sprintf "type %s =" <| sprint_qualified name
                    else
                      sprint_qualified name |> sprintf "type %s %s =" <| (tyargs |> List.choose (function TyVar x -> Some x | _ -> None) |> String.concat " ")
                  for cstr in cstrs do
                    if cstr.args |> List.isEmpty then
                      yield sprintf "  | %s" cstr.name
                    else
                      yield sprintf "  | %s of %s" cstr.name (cstr.args |> List.map to_s |> String.concat " * ")
                ] |> List.map (indent idt)
              | TopTypeDef (name, ty, _) ->
                [ sprintf "type %s = %s" (handle_op name) (to_s ty)]
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

type TopLevel_InferredUTm = TopLevel<Type * UntypedTerm>