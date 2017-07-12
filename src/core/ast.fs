module nml.Ast

let inline to_s x = x.ToString()
  
[<CustomEquality; NoComparison>]
type EqualityNull<'T> = 
  | Value of 'T
  override x.Equals(yobj) =
    match yobj with
      | :? EqualityNull<'T> as y -> true
      | _ -> false
  override x.GetHashCode() = 0

[<CustomEquality; NoComparison>]
type NameCompared<'T> = 
  { value: 'T; name: string }
  override x.Equals(yobj) =
    match yobj with
      | :? NameCompared<'T> as y -> x.name = y.name
      | _ -> false
  override x.GetHashCode() = 0


type Type =
  | TypeVar of string
  | Bool | Unit
  | Fun of Type * Type
  | Deferred of Type
  | TypeOp of string * Type list * EqualityNull<(string * Printf.StringFormat<string -> string>) option>
  | Variant of string * Type list * (string * Type list) list
  | Scheme of Set<string> * Type
  override x.ToString() =
    let inline to_sc x =
      match x with
        | TypeVar _ | Bool | Unit | Deferred _ -> to_s x
        | TypeOp (n, [], _)
        | Variant (n, [], _) -> n
        | c -> "(" + (to_s c) + ")"
    in
    match x with
      | TypeVar s -> s
      | Bool -> "Bool"
      | Unit -> "Unit"
      | Fun (a, b) -> sprintf "%s -> %s" (to_sc a) (to_s b)
      | Deferred t -> sprintf "<%s>" (to_s t)
      | TypeOp (n, [], _) -> n
      | TypeOp (n, ts, Value (Some (c, f))) -> sprintf f (ts |> List.map to_sc |> String.concat c)
      | TypeOp (n, ts, Value None) -> sprintf "%s %s" (ts |> List.map to_sc |> String.concat " ") n
      | Variant (n, [], _) -> n
      | Variant (n, ts, _) -> sprintf "%s %s" (ts |> List.map to_sc |> String.concat " ") n 
      | Scheme (ts, t) -> sprintf "∀%s. (%s)" (ts |> String.concat ", ") (to_s t)

//let TChar = TypeOp ("Char", [], None)

let NewTypeOp (tn, ts, o) =
  TypeOp (tn, ts, Value o)

let TTuple ts =
  NewTypeOp ("*", ts, Some(" * ", "%s"))

let InductiveVariant (n, ts, f) =
  Variant (n, ts, TypeOp (n, ts, Value None) |> f)

let TList a =
  InductiveVariant ("List", [a], (fun self -> [ ("Nil", []); ("Cons", [a; self]) ]))

let TOption a =
  Variant ("Option", [a], [ ("Some", [a]); ("None", []) ]);

let Nat = 
  InductiveVariant ("Nat", [], (fun self -> [ ("Succ", [self]); ("0", []) ]))

type Literal =
  | LNat of uint32
  | LBool of bool
  | LUnit
  override x.ToString() =
    match x with
      | LNat i -> i.ToString()
      | LBool b -> if b then "true" else "false"
      | LUnit -> "()"

let inline handle_op s =
  if (s |> String.forall (fun c -> System.Char.IsLetterOrDigit c || c = '_')) then
    s
  else
    "(" + s + ")"

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
  | UTmFixMatch of string * (UntypedTerm * UntypedTerm) list
  | UTmExternal of NameCompared<UntypedTerm list -> UntypedTerm> * Type
  | UTmDefer of UntypedTerm
  | UTmRun of UntypedTerm
  override x.ToString() =
    let rec tos stack uniq = function
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
      | UTmApply (x, ys) -> sprintf "(%s %s)" (x |> tos stack uniq) (ys |> List.map (tos stack uniq) |> String.concat " ")
      | UTmMatch (x, cs) -> sprintf "(match %s with %s)" (x |> tos stack uniq) (cs |> List.map (fun (pt, bd) -> sprintf "%s -> %s" (pt |> tos stack uniq) (bd |> tos stack uniq)) |> String.concat " | ")
      | UTmFixMatch (self, cs) -> sprintf "(fixpoint %s of %s)" self (cs |> List.map (fun (pt, bd) -> sprintf "%s -> %s" (pt |> tos stack uniq) (bd |> tos stack uniq)) |> String.concat " | ")
      | UTmExternal (f, _) -> handle_op f.name
      | UTmDefer x -> sprintf "<( %s )>" (x |> tos stack uniq)
      | UTmRun x -> sprintf "(run %s)" (x |> tos stack uniq)
    in tos [] 0 x

let ExternalFun nm typ f =
  UTmExternal({ name = nm; value = f }, typ)


(*
type TopLevel =
  | Open of string
  | Module of string * TopLevel list
  | TopLet of string * Type * ParsedTerm
  | TypeDef of string * Type
  | EntryPoint of ParsedTerm
*)

