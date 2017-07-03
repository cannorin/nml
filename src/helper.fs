module nml.Helper

open nml.Ast
open Mono.Terminal

let inline (?|) x y = defaultArg x y
let inline cprintfn color p x =
  System.Console.ForegroundColor <- color;
  printfn p x;
  System.Console.ResetColor ()

let editor = new LineEditor ("nml", 300)
let inline scan prompt = editor.Edit(prompt, "")

let matchPattern pat t =
  let rec mt pat t =
    match (pat, t) with
      | (UApply (UVar "Succ", pred), ULiteral (LNat n))
      | (UConstruct ("Succ", [pred]), ULiteral (LNat n)) when n > 0u ->
        mt pred (ULiteral (LNat (n - 1u)))
      | (UConstruct ("0", []), ULiteral (LNat 0u)) ->
        []
      | (UConstruct (n, xs), UConstruct (m, ys))
      | (UApply (UVar n, UTuple xs), UConstruct (m, ys)) when (n = m && List.length xs = List.length ys) ->
        ys |> List.map2 mt xs |> List.concat
      | (UApply (UVar n, x), UConstruct (m, _)) when n = m ->
        mt (UApply (UVar n, UTuple [x])) t
      | (UTuple xs, UTuple ys) when (List.length xs = List.length ys) ->
        ys |> List.map2 mt xs |> List.concat
      | (ULiteral x, ULiteral y) when x = y ->
        []
      | (UVar x, y) -> [(x, y)]
      | _ -> failwith "matchfailed"
  in 
  try
    mt pat t |> Some
  with
    | _ -> None

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

// [("a", A); ("b", B)] body --> let a = A in let b = B in body
let rec foldLet body binds =
  match binds with
    | (name, value) :: rest ->
      ULet (name, value, foldLet body rest)
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

