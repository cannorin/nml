module nml.Ast
open nml.Sizes

type Type =
  | TypeVar of string
  | Bool | Unit
  | Fun of Type * Type
  | Deferred of Type
  | DataType of string 
              * Type list 
              * Constructor list
              * Size option
              * EqualityNull<string * Printf.StringFormat<string -> string>>
  | InductiveSelf of string
  | Scheme of Set<string> * Map<string, Size> * Type
  override x.ToString() =
    let rec tos = function
      | TypeVar n 
      | InductiveSelf n -> n
      | Bool -> "Bool" | Unit -> "Unit"
      | Fun (Fun(a, b), c) -> sprintf "(%s) -> %s" (Fun (a, b) |> tos) (tos c)
      | Fun (a, b) -> sprintf "%s -> %s" (tos a) (tos b)
      | Deferred t -> sprintf "<%s>" (tos t)
      | DataType (name, ts, _, None, Value (s, fmt)) ->
        sprintf fmt (ts |> List.map tos |> String.concat s)
      | DataType (name, [], _, Some s, _) ->
        sprintf "%s[%s]" name (to_s s)
      | DataType (name, [], _, _, _) -> name
      | DataType (name, ts, _, None, _) ->
        sprintf "(%s %s)" (ts |> List.map tos |> String.concat " ") name
      | DataType (name, ts, _, Some s, _) ->
        sprintf "(%s %s[%s])" (ts |> List.map tos |> String.concat " ") name (to_s s)
      | Scheme (ts, ss, t) when (Map.isEmpty ss) ->
        sprintf "∀%s. (%s)" (ts |> String.concat ", ") (tos t)
      | Scheme (ts, ss, t) when (Set.isEmpty ts) ->
        sprintf "∀[%s]. (%s)" (ss |> Map.toList |> List.map (fun (x, y) -> x + " <= " + to_s y) |> String.concat ", ") (to_s t)
      | Scheme (ts, ss, t) -> 
        sprintf "∀%s, [%s]. (%s)" 
                (ts |> String.concat ", ") 
                (ss |> Map.toList |> List.map (fun (x, y) -> x + " <= " + to_s y) |> String.concat ", ")
                (tos t)
    in tos x
        
and Constructor =
  { name: string; args: Type list; isRecursive: bool; }
  

let NewConst (n, a) =
  { name = n; args = a; isRecursive = false }

let NewRecConst (n, a) =
  { name = n; args = a; isRecursive = true }

let TypeOp (name, ts, po) =
  DataType (name, ts, [], None, po)

let Variant (name, ts, cs) =
  DataType (name, ts, cs, None, Null)

let InductiveVariant (n, ts, f, size) =
  DataType (n, ts, (InductiveSelf n) |> f, Some size, Null)

type Literal =
  | LNat of nat
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


(*
type TopLevel =
  | Open of string
  | Module of string * TopLevel list
  | TopLet of string * Type * ParsedTerm
  | TypeDef of string * Type
  | EntryPoint of ParsedTerm
*)

