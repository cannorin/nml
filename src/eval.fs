module nml.Evaluation

open nml.Ast
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections

let (<+>) l r = List.append l r

let toEvalTerm t =
  let rec tot stack = function
    | UVar x ->
      match (stack |> List.tryFindIndex ((=) x)) with
        | Some i -> EBound i
        | None -> EFree x
    | ULiteral l -> ELit l
    | UTuple xs -> ECons ("*", xs)
    | UList [] -> ECons ("Nil", [])
    | UList xs -> xs |> List.rev |> List.fold (fun l x -> ECons ("Cons", [x; l])) (ECons ("Nil", []))
    | UFun (arg, body) -> EAbs (body |> tot (arg :: stack), Some arg)
    | UFunUnit body -> EAbs (body |> tot ("" :: stack), Some "()")
    | UApply (l, r) ->
      match (l |> tot stack) with
        | EApp (l', r') -> EApp (l', r' <+> [tot stack r])
        | x -> EApp (x, [tot stack r])
    | UConstruct (n, xs) -> ECons (n, xs |> List.map (tot stack))
    | UFixMatch (n, cs) ->
      let m = UFun ("x", UMatch (UVar "x", cs)) in
      EFix (m |> tot (n :: stack), Some n)
    | UDefer x
    | URun x -> tot stack x
    | ULet (x, r, b)
    | ULetDefer (x, r, b) ->
      UApply (UFun (x, b), r) |> tot stack
    | UOp2 (l, op, r) ->
      UApply (UApply (UVar op, l), r) |> tot stack
    | UIf (x, t, e) ->
      UMatch (x, [ (ULiteral true, t); (ULiteral false, e) ]) |> tot stack
    | UMatch (x, cs) ->
      EMatch (x |> tot stack, cs |> List.map (fun (p, b) -> (tot [] p, tot (stack |> List.map (fun n -> if (fvOfTerm p |> List.contains) then "" else n)) b)))
    | UExternal (f, t) ->
      EExt (f, t |> expandFun |> fst |> List.length, [])

let matchPattern pat t =
  let rec mt pat t =
    match (pat, t) with
      | (ECons ("Succ", [pred]), ELit (LNat n)) when n > 0u ->
        mt pred (ELit (LNat (n - 1u)))
      | (ECons ("0", []), ELit (LNat 0u)) ->
        []
      | (ECons (n, xs), ECons (m, ys)) when (n = m && List.length xs = List.length ys) ->
        ys |> List.map2 mt xs |> List.concat
      | (ELit x, ELit y) when x = y ->
        []
      | (EFree x, y) -> [(x, y)]
      | _ -> failwith "matchfailed"
  in 
  try
    mt pat t |> Some
  with
    | _ -> None


let evalWithContext map t =
  let rec e map stack = function
    | EFree n -> map |> Map.find n
    | EBound i -> stack.[i]
    | EConst xs -> EConst (xs |> List.map (e map stack))
    | EApp (EAbs (body, _), r) ->
      let r' = r |> List.map (e map stack) in
      body |> e ctx (r' <+> stack)
    | EApp (EFix (body, h), r) ->
      let r' = r |> List.map (e map stack) in
      body |> e ctx (EFix (body, h) :: r' <+> stack)
    | EApp (EExtApp (f, i, args), r) ->
      let r' = r |> List.map (e map stack) |> List.append args in
      EExtApp (fun xs -> f (r' <+> xs), i - List.length r', r')
    | EApp (l, r) ->
      EApp (l |> e map stack, r |> List.map (e map stack))
    | EExtApp (f, 0, args) when (args |> List.forall isValue) ->
      f.value args
    | EExtApp (f, n, args) -> EExtApp (f, n, args |> List.map (e map stack))
    | EMatch (x, cs) ->
      let x = x |> e map stack in
      if isValue x then
        match (cs |> List.choose (fun (p, b) -> matchPattern p x |> Option.map (fun mp -> (mp, b))) |> List.tryHead) with
          | Some (binds, body) -> body |> e (Map.ofList (binds <+> Map.toList map)) stack
          | None -> failwith "match failed"
      else EMatch (x, cs |> List.map (fun (p, b) -> (p, b |> e map stack)))
    | x -> x
  in
  e map [] t

let eval t = evalWithContext Map.empty t

