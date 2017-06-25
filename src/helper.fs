module nml.Helper

open nml.Ast

let inline (?|) x y = defaultArg x y

let rec isValue = function
  | UApply (_, _)
  | URun _
  | ULet (_, _, _)
  | ULetDefer (_, _, _) -> false
  | UTuple (l, r) -> isValue l && isValue r
  | UDefer x
  | UFun (_, x) -> isValue x
  | UExternal _
  | _ -> true

let genUniq ng =
  let a = ng % 26 in
  let p = ng / 26 in
  (new string [| for i in 0..p do yield [|'a'..'z'|].[a] |], ng + 1)

// (((f a) b) c) --> (f, [a; b; c])
let rec expandApply = function
  | UApply (UApply (a, b), r) ->
    let (loot, args) = UApply (a, b) |> expandApply in
    (loot, List.concat [args; [r];])
  | UApply (f, x) -> (f, [x])
  | x -> (x, [])

// [a; b; c] f --> (((f a) b) c)
let rec foldApply args f =
  match args with
    | x :: rest ->
      UApply(f, x) |> foldApply rest
    | [] -> f


// a -> b -> c -> d --> ([a; b; c], d)
let rec expandFun = function
  | Forall (_, t) -> expandFun t
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
  | TypeOp (_, ts, _) -> ts |> List.map fvOf |> List.fold Set.union (set [])
  | Forall (vs, t)
  | Scheme (vs, t) -> Set.difference (fvOf t) vs
  | _ -> set []

let getTimeOfType ty =
  let rec dig i = function
    | Deferred x -> x |> dig (i + 1)
    | x -> (x, i)
  in dig 0 ty


