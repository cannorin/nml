module nml.Helper

open nml.Ast
open nml.Stages

//let TChar = TypeOp ("Char", [], None)

let TTuple ts =
  TypeOp ("*", ts, Value(" * ", "%s"))

let TList a =
  InductiveVariant ("List", [a], (fun self -> [ ("Nil", []); ("Cons", [a; self]) ]), SVar "b")

let TOption a =
  Variant ("Option", [a], [ ("Some", [a]); ("None", []) ]);

let NatS s =
  InductiveVariant ("Nat", [], (fun self -> [ ("Succ", [self]); ("0", []) ]), s)

let Nat = NatS (SVar "b")


let matchPattern pat t =
  let rec mt pat t =
    match (pat, t) with
      | (UTmConstruct ("Succ", [pred]), UTmLiteral (LNat n)) when n > 0u ->
        mt pred (UTmLiteral (LNat (n - 1u)))
      | (UTmConstruct ("0", []), UTmLiteral (LNat 0u)) ->
        []
      | (UTmTuple xs, UTmTuple ys) ->
        ys |> List.map2 mt xs |> List.concat
      | (UTmConstruct (n, xs), UTmConstruct (m, ys)) when (n = m && List.length xs = List.length ys) ->
        ys |> List.map2 mt xs |> List.concat
      | (UTmLiteral x, UTmLiteral y) when x = y ->
        []
      | (UTmFreeVar "_", y) -> []
      | (UTmBoundVar x, y) -> [(x, y)]
      | _ -> failwith "matchfailed"
  in 
  try
    mt pat t |> List.map snd |> Some
  with
    | _ -> None

// (((f a) b) c) --> (f, [a; b; c])
let rec expandApply = function
  | UTmApply (UTmApply (a, b), r) ->
    let (loot, args) = UTmApply (a, b) |> expandApply in
    (loot, List.concat [args; [r];])
  | UTmApply (f, x) -> (f, [x])
  | x -> (x, [])

// [a; b; c] f --> (((f a) b) c)
let rec foldApply args f =
  match args with
    | x :: rest ->
      UTmApply(f, x) |> foldApply rest
    | [] -> f

// [("a", A); ("b", B)] body --> let a = A in let b = B in body
let rec foldLet body binds =
  match binds with
    | (name, value) :: rest ->
      UTmLet (name, value, foldLet body rest)
    | [] -> body

// a -> b -> c -> d --> ([a; b; c], d)
let rec expandFun = function
  | Scheme (_, _, t) -> expandFun t
  | Fun (a, Fun (b, c)) ->
    let (args, ret) = Fun (b, c) |> expandFun in
    (a :: args, ret)
  | Fun (a, b) ->
    ([a], b)
  | x -> ([], x)

// [a; b; c] d --> a -> b -> c -> d
let rec foldFun args ret =
  match args with
    | [] -> ret
    | a :: rest ->
      Fun(a, ret |> foldFun rest)

let rec fvOf = function
  | TypeVar n -> set [n]
  | Fun (a, b) -> Set.union (fvOf a) (fvOf b)
  | Deferred t -> fvOf t
  | DataType (_, vs, ts, _, _) -> 
    ts |> List.map (snd >> (List.map fvOf)) 
       |> List.concat
       |> List.fold Set.union (set [])
       |> Set.union (Set.ofList (vs |> List.choose (function | TypeVar x -> Some x | _ -> None )))
  | Scheme (vs, _, t) -> Set.difference (fvOf t) vs
  | _ -> set []

let rec fsvOf = function
  | Fun (a, b) -> Set.union (fsvOf a) (fsvOf b)
  | Deferred t -> fsvOf t
  | DataType (_, _, ts, s, _) ->
    let fsv = s |> Option.map (StageOp.fvOf) ?| (set []) in
    ts |> List.map (snd >> (List.map fsvOf))
       |> List.concat
       |> List.fold Set.union fsv
  | Scheme (_, ss, t) -> Set.difference (fsvOf t) (Map.keys ss)
  | _ -> set []

let getTimeOfType ty =
  let rec dig i = function
    | Deferred x -> x |> dig (i + 1)
    | x -> (x, i)
  in dig 0 ty

let rec delayTypeBy i ty =
  if (i > 0) then
    Deferred ty |> delayTypeBy (i - 1)
  else
    ty

let hasTyVar vname t =
  fvOf t |> Set.contains vname

let rec hasSelf name args = function
  | DataType (n, ts, _, _, _) when (n = name && ts = args) -> true
  | DataType (_, ts, _, _, _) -> 
    ts |> List.exists (fun t -> hasSelf name args t)
  | Fun (a, b) -> hasSelf name args a || hasSelf name args b
  | Scheme (_, _, t)
  | Deferred t -> hasSelf name args t
  | _ -> false

let rec isInductive vt =
  match vt with
    | DataType (vname, vtargs, cts, _, _) ->
      let hasRec = cts |> List.exists (snd >> List.exists (hasSelf vname vtargs)) in
      let hasBottom = cts |> List.exists (snd >> List.forall (hasSelf vname vtargs >> not)) in
      if (hasRec && hasBottom) then
        Some true
      else if hasRec then
        None
      else
        Some false
    | _ -> Some false

let rec countFvOfPattern = function 
  | UTmBoundVar _ -> 1
  | UTmTuple xs
  | UTmConstruct (_, xs) ->
    xs |> List.map countFvOfPattern |> List.sum
  | _ -> 0

let rec addRun i t =
  if (i > 0) then
    let t' = 
      match t with
        | UTmDefer x -> x
        | x -> UTmRun x
    in addRun (i - 1) t'
  else
    t

let rec delayTermBy i t =
  if (i > 0) then
    UTmDefer t |> delayTermBy (i - 1)
  else
    t


