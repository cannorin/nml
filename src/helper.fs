module nml.Helper

open nml.Ast

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
      | (UTmFreeVar x, y) -> [(x, y)]
      | _ -> failwith "matchfailed"
  in 
  try
    mt pat t |> Some
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
  | Scheme (_, t) -> expandFun t
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
  | Variant (_, vs, ts) -> 
    ts |> List.map (snd >> (List.map fvOf)) 
       |> List.concat
       |> List.fold Set.union (set [])
       |> Set.difference (Set.ofList (vs |> List.choose (function | TypeVar x -> Some x | _ -> None )))
  | TypeOp (_, ts, _) -> ts |> List.map fvOf |> List.fold Set.union (set [])
  | Scheme (vs, t) -> Set.difference (fvOf t) vs
  | _ -> set []

let getTimeOfType ty =
  let rec dig i = function
    | Deferred x -> x |> dig (i + 1)
    | x -> (x, i)
  in dig 0 ty

let rec hasSelf name args = function
  | Variant (n, ts, _)
  | TypeOp (n, ts, _) when (n = name && ts = args) -> true
  | Fun (a, b) -> hasSelf name args a || hasSelf name args b
  | Scheme (_, t)
  | Deferred t -> hasSelf name args t
  | TypeOp (_, ts, _) -> ts |> List.exists (fun t -> hasSelf name args t)
  | _ -> false

let rec isInductive vt =
  match vt with
    | Variant (vname, vtargs, cts) ->
      let hasRec = cts |> List.exists (snd >> List.forall (hasSelf vname vtargs)) in
      let hasBottom = cts |> List.exists (snd >> List.forall (hasSelf vname vtargs >> not)) in
      if (hasRec && hasBottom) then
        Some true
      else if hasRec then
        None
      else
        Some false
    | _ -> Some false

let rec fvOfTerm = function
  | UTmFreeVar x -> set [x]
  | UTmApply (l, rs) ->
    l :: rs |> List.map (fvOfTerm >> Set.toList) |> List.concat |> Set.ofList
  | UTmTuple xs
  | UTmConstruct (_, xs) ->
    xs |> List.map (fvOfTerm >> Set.toList) |> List.concat |> Set.ofList
  | UTmFun x
  | UTmDefer x
  | UTmRun x -> fvOfTerm x
  | UTmLet (x, v, b) -> Set.union (fvOfTerm v) (fvOfTerm b) |> Set.difference (set [x])
  | UTmMatch (x, cs) ->
    cs |> List.map (fun (pt, bd) -> Set.difference (fvOfTerm pt) (fvOfTerm bd) |> Set.toList)
       |> List.concat
       |> Set.ofList
       |> Set.union (fvOfTerm x)
  | UTmFixMatch (n, cs) ->
    UTmMatch (UTmLiteral LUnit, cs) |> fvOfTerm |> Set.difference (set [n])
  | _ -> set []

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


