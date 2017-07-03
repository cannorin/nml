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
  | UVar of string
  | ULiteral of Literal
  | UTuple of UntypedTerm list
  | UList of UntypedTerm list
  | UFun of string  * UntypedTerm
  | UFunUnit of UntypedTerm
  | UApply of UntypedTerm * UntypedTerm
  | UConstruct of string * UntypedTerm list
  | UIf of UntypedTerm * UntypedTerm * UntypedTerm
  | ULet of string * UntypedTerm * UntypedTerm
  //| ULetRec of string * UntypedTerm * UntypedTerm
  | UDefer of UntypedTerm
  | ULetDefer of string * UntypedTerm * UntypedTerm
  // | UModuleVal of string * string
  | UExternal of NameCompared<UntypedTerm list -> UntypedTerm> * Type
  | UOp2 of UntypedTerm * string * UntypedTerm
  | UMatch of UntypedTerm * (UntypedTerm * UntypedTerm) list
  | URun of UntypedTerm
  override x.ToString() =
    match x with
      | UVar name -> handle_op name
      | ULiteral l -> l.ToString()
      | UTuple ts -> sprintf "(%s)" (ts |> List.map to_s |> String.concat ", ")
      | UList ts -> sprintf "[%s]" (ts |> List.map to_s |> String.concat "; ")
      | UFun (arg, body) -> sprintf "(fun %s -> %s)" (to_s arg) (to_s body)
      | UFunUnit body -> sprintf "(fun () -> %s)" (to_s body)
      | UApply (l, r) -> sprintf "(%s %s)" (to_s l) (to_s r)
      | UConstruct (n, []) -> n
      | UConstruct (n, [t]) -> sprintf "%s %s" n (to_s t)
      | UConstruct (n, ts) -> sprintf "%s (%s)" n (ts |> List.map to_s |> String.concat ", ")
      | UIf (b, t, e) -> sprintf "if %s then %s else %s" (to_s b) (to_s t) (to_s e)
      | ULet (name, value, body) ->
        sprintf "let %s = %s in %s" (handle_op name) (to_s value) (to_s body)
      // | ULetRec (name, value, body) ->
      //   sprintf "let rec %s = %s in %s" name (to_s value) (to_s body)
      | UDefer x -> sprintf "<( %s )>" (to_s x)
      | ULetDefer (name, value, body) ->
        sprintf "let! %s = %s in %s" (handle_op name) (to_s value) (to_s body)
      // | UModuleVal (m, f) -> sprintf "%s.%s" m f
      | UExternal (f, _) -> f.name
      | UOp2 (x, op, y) -> sprintf "(%s %s %s)" (to_s x) op (to_s y)
      | UMatch (v, cs) -> sprintf "match %s with %s" (to_s v) (cs |> List.map (fun (l, r) -> sprintf "%s -> %s" (to_s l) (to_s r)) |> String.concat " | ")
      | URun x -> sprintf "(run %s)" (to_s x)

let ExternalFun nm typ f =
  UExternal({ name = nm; value = f }, typ)


(*
type TopLevel =
  | Open of string
  | Module of string * TopLevel list
  | TopLet of string * Type * UntypedTerm
  | TypeDef of string * Type
  | EntryPoint of UntypedTerm
*)

