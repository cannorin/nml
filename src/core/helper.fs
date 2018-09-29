module nml.Helper

open nml.Ast

let argsmap f c =
  { c with args = c.args |> List.map f }

let matchPattern pat t =
  let rec mt pat t =
    match pat, t.item with
      | MtConstruct (["S"], [pred]), TmLiteral (LNat (S n)) ->
        mt pred (TmLiteral (LNat n) |> With.sameInfoOf t)
      | MtConstruct (["0"], []), TmLiteral (LNat Z)
      | MtLiteral (LNat Z), TmConstruct (["0"], []) ->
        []
      | MtConstruct (n, xs), TmConstruct (m, ys)
        when (List.tryLast n = List.tryLast m && List.length xs = List.length ys) ->
        ys |> List.map2 mt xs |> List.concat
      | MtLiteral x, TmLiteral y when x = y ->
        []
      | MtTuple xs, TmTuple ys ->
        ys |> List.map2 mt xs |> List.concat
      | MtWildcard, _ -> []
      | MtBoundVar x, _ -> [ x, t ]
      | _ -> 
        failwith "matchfailed"
  in 
  try
    mt pat t |> List.map snd |> Some
  with
    | _ -> None

// [a; b; c] d --> a -> b -> c -> d
let rec foldFun builder args ret =
  match args with
    | [] -> ret
    | a :: rest ->
      builder (a, ret |> foldFun builder rest)

let inline fvOf (ty: ^T) = (^T: (member fv: unit -> Set<string>) ty)

let inline getTimeOfType (TyTemporal (ti, _)) = ti

let inline delayTypeBy i (TyTemporal (ti, ty)) = TyTemporal (i + ti, ty)

let inline runTypeBy   i (TyTemporal (ti, ty)) = TyTemporal (ti - i, ty)

let inline hasTyVar vname t =
  fvOf t |> Set.contains vname

let inline fvOfTerm (Item tm : With< ^T, _ >) = (^T: (member fv: unit -> Set<string>) tm)

let inline countFvOfPattern (x: MatchPattern) = x.countFv()