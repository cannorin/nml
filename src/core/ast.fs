module nml.Ast
 
type Type =
  | TypeVar of string
  | Bool | Unit
  | Fun of Type * Type
  | Deferred of Type
  | DataType of string * Type list * Constructor list * EqualityNull<string * Printf.StringFormat<string -> string>>
  | DataTypeSelf of string * Type list
  | Scheme of Set<string> * Type
  override x.ToString() =
    let inline to_sc x =
      match x with
        | TypeVar _ | Bool | Unit | Deferred _ -> to_s x
        | DataType (n, [], _, _) -> n
        | c -> "(" + (to_s c) + ")"
    in
    match x with
      | TypeVar s -> s
      | Bool -> "Bool"
      | Unit -> "Unit"
      | Fun (a, b) -> sprintf "%s -> %s" (to_sc a) (to_s b)
      | Deferred t -> sprintf "<%s>" (to_s t)
      | DataType (n, [], _, _) -> n
      | DataType (n, ts, _, EValue (c, f)) -> sprintf f (ts |> List.map to_sc |> String.concat c)
      | DataType (n, ts, _, _)
      | DataTypeSelf (n, ts) -> sprintf "%s %s" n (ts |> List.map to_sc |> String.concat " ")
      | Scheme (ts, t) -> sprintf "∀%s. (%s)" (ts |> String.concat ", ") (to_s t)
and Constructor =
  { name: string; args: Type list; isRecursive: bool; }
  

let NewConst (n, a) =
  { name = n; args = a; isRecursive = false }

let NewRecConst (n, a) =
  { name = n; args = a; isRecursive = true }

let TypeOp (name, ts, po) =
  DataType (name, ts, [], po)

let Variant (name, ts, cs) =
  DataType (name, ts, cs, ENull)

let InductiveVariant (n, ts, f) =
  DataType (n, ts, DataTypeSelf (n, ts) |> f, ENull)

//let TChar = TypeOp ("Char", [], None)

let TTuple ts =
  TypeOp ("*", ts, EValue (" * ", "%s"))

let TList a =
  InductiveVariant ("List", [a], (fun self -> [ NewConst ("Nil", []); NewRecConst ("Cons", [a; self]) ]))

let TOption a =
  Variant ("Option", [a], [ NewConst ("Some", [a]); NewConst ("None", []) ]);

let Nat = 
  InductiveVariant ("Nat", [], (fun self -> [ NewRecConst ("Succ", [self]); NewConst ("0", []) ]))

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
  | UTmFreeVar of string
  | UTmLet of string * UntypedTerm * UntypedTerm
  | UTmLetDefer of string * UntypedTerm * UntypedTerm
  | UTmConstruct of string * UntypedTerm list
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
      | UTmFreeVar n -> handle_op n
      | UTmLet (x, v, b) -> sprintf "let %s = %s in %s" (handle_op x) (v |> tos stack uniq) (b |> tos stack uniq)
      | UTmLetDefer (x, v, b) -> sprintf "let! %s = %s in %s" (handle_op x) (v |> tos stack uniq) (b |> tos stack uniq)
      | UTmConstruct (n, []) -> n
      | UTmConstruct (n, [x]) -> sprintf "%s %s" n (x |> tos stack uniq)
      | UTmConstruct (n, xs) -> sprintf "%s (%s)" n (xs |> List.map (tos stack uniq) |> String.concat ", ")
      | UTmTuple xs -> sprintf "(%s)" (xs |> List.map (tos stack uniq) |> String.concat ", ")
      | UTmApply (UTmFreeVar x, [l; r]) when (is_op x) ->
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
  | TopOpen of moduleName:string
  | TopLet of name:string * tm:'Term
  | TopDo of tm:'Term
  | TopModule of name:string * stmts:TopLevel<'Term> list
  | TopTypeDef of name:string * ty:Type

type TopLevel_InferredUTm = TopLevel<Type * UntypedTerm>