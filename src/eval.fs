module nml.Evaluation

open nml.Ast
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections

let rec fvOfTerm = function
  | UApply (l, r) -> 
    Set.union (fvOfTerm l) (fvOfTerm r)
  | UDefer x -> fvOfTerm x
  | UFun (a, b) ->
    Set.difference (fvOfTerm b) (set [a])
  | UIf (b, t, e) -> 
    fvOfTerm b |> Set.union (fvOfTerm t) |> Set.union (fvOfTerm e)
  | ULet (x, r, b)
  | ULetDefer (x, r, b) ->
    Set.union (fvOfTerm r) (fvOfTerm b |> Set.difference (set [x]))
  | UTuple xs
  | UConstruct (_, xs) -> 
    xs |> List.map (Set.toList << fvOfTerm) |> List.concat |> Set.ofList
  | UVar x when x <> "_" -> set [x]
  | UMatch (v, cs) ->
    cs 
      |> List.map (fun (x, y) -> Set.difference (fvOfTerm x) (fvOfTerm y) |> Set.toList)
      |> List.concat
      |> Set.ofList
      |> Set.union (fvOfTerm v)
  | _ -> set []

let rec hasVar vn = function
  | UVar n when (n = vn) -> true
  | UFun (a, b) when (a <> vn) -> hasVar vn b
  | UApply (l, r) -> (hasVar vn l) || (hasVar vn r)
  | UIf (b, t, e) -> (hasVar vn b) || (hasVar vn t) || (hasVar vn e)
  | ULet (x, r, b)
  | ULetDefer (x, r, b) -> (hasVar vn r) || (x <> vn && hasVar vn b)
  | UTuple xs
  | UConstruct (_, xs) ->
    xs |> List.exists (hasVar vn)
  | UMatch (v, cs) ->
    (hasVar vn v) || cs |> List.exists (fun (x, y) -> (hasVar vn x) || (hasVar vn y))
  | URun x
  | UDefer x -> hasVar vn x
  | _ -> false

let rec replace vn value = function
  | UVar n when (n = vn) -> value
  | UFun (a, b) when (a <> vn) -> UFun (a, b |> replace vn value) 
  | UApply (l, r) -> UApply (l |> replace vn value, r |> replace vn value)
  | UTuple xs ->
    UTuple (xs |> List.map (replace vn value))
  | UConstruct (n, xs) ->
    UConstruct (n, xs |> List.map (replace vn value))
  | UIf (b, t, e) -> UIf (b |> replace vn value, t |> replace vn value, e |> replace vn value)
  | ULet (x, r, b) -> ULet (x, r |> replace vn value, if (x <> vn) then b |> replace vn value else b)
  | ULetDefer (x, r, b) -> ULetDefer (x, r |> replace vn value, if (x <> vn) then b |> replace vn value else b)
  | URun x -> URun (x |> replace vn value)
  | UMatch (v, cs) ->
    UMatch (v |> replace vn value, cs |> List.map (fun (x, y) -> if (x |> hasVar vn) then (x, y) else (x, y |> replace vn value)))
  | UDefer x -> UDefer (x |> replace vn value)
  | x -> x

let replaceAll ctx t =
  ctx |> Map.fold (fun x' k v -> x' |> replace k v) t

let getTimeOfTerm t =
  let rec g = function
    | UDefer x -> 1 + (g x)
    | ULetDefer (x, r, b) -> (g r) + (g b)
    | UApply (_, _) as x ->
      let (loot, args) = expandApply x in
      match loot with
        | UExternal (ef, t) ->
          let (targs, tret) = expandFun t in
          if (List.length args = List.length targs && args |> List.forall (fvOfTerm >> Set.isEmpty)) then
            getTimeOfType tret |> snd
          else 0
        | _ -> 0
    | UIf (_, t, e) -> max (g t) (g e)
    | UMatch (_, cs) ->
      cs |> List.map (snd >> g) |> List.max
    | _ -> 0
  in g t

let rec addRun i t =
  if (i > 0) then
    let t' = 
      match t with
        | UDefer x -> x
        | x -> URun x
    in addRun (i - 1) t'
  else
    t

let rec delayTermBy i t =
  if (i > 0) then
    UDefer t |> delayTermBy (i - 1)
  else
    t

let evalWithContext term ctx =
  let uniq = ref 0 in
  let rec aconvert = function
    | UFun (arg, body) ->
      let (na, newuniq) = genUniq !uniq in
      uniq := newuniq;
      if (ctx |> Map.tryFind na |> Option.isNone && body |> hasVar na |> not) then
        UFun (na, body |> replace arg (UVar na))
      else UFun (arg, body) |> aconvert
    | x -> x
  in
  let rec e ctx = function
    | UVar n ->
      ctx |> Map.tryFind n |> Option.map (e ctx) ?| UVar n
    | UTuple xs -> UTuple (xs |> List.map (e ctx))
    | UConstruct (n, xs) -> UConstruct (n, xs |> List.map (e ctx))
    | UFun (arg, body) -> UFun (arg, body |> e (ctx |> Map.remove arg)) |> aconvert
    | UFunUnit body -> UFunUnit (body |> e ctx)
    | UApply (f, x) ->
      match (f |> e ctx) with
        | UFun (arg, body) ->
          body |> e (ctx |> Map.add arg x) |> e ctx
        | UFunUnit body ->
          body |> e ctx
        | f ->
          let (loot, args) = expandApply (UApply (f, x)) in
          match loot with
            | UExternal (ef, t) ->
              let (targs, tret) = expandFun t in
              let args' = args |> List.map (e ctx) in
              if (List.length args = List.length targs && args' |> List.forall (fvOfTerm >> Set.isEmpty)) then
                let (tret', time) = getTimeOfType tret in
                if (time > 0) then
                  let ef' = UExternal ({ name = ef.name; value = (ef.value >> addRun time) }, foldFun targs tret') in
                  ef' |> foldApply args' |> addRun time |> delayTermBy time
                else
                  let r = args' |> ef.value in
                  r |> e ctx
              else UApply (f, x |> e ctx)
            | _ -> UApply (f, x |> e ctx)
    | UIf (b, t, l) ->
      match (b |> e ctx) with
        | ULiteral (LBool true) -> t |> e ctx
        | ULiteral (LBool false) -> l |> e ctx
        | _ -> UIf (b, t, l)
    | ULet (x, r, b) ->
      b |> e (ctx |> Map.add x (r |> e ctx))
    | ULetDefer (x, r, b) ->
      let r' = r |> replaceAll ctx in
      let time = getTimeOfTerm r' in
      let b' =
        let b = b |> replaceAll ctx in
        if (getTimeOfTerm b > 0) then
          b
        else
          b |> e ctx
      in
      if (time = 0) then
        ULet (x, r, b) |> e ctx
      else
        ULet (x, r' |> addRun time, b') |> delayTermBy time
    | UDefer x ->
      x |> replaceAll ctx |> UDefer
    | UMatch (v, pts) ->
      let v' = v |> e ctx in
        if (fvOfTerm v' |> Set.isEmpty) then
          match (pts |> List.choose (fun (p, b) -> matchPattern p v' |> Option.map (fun x -> (b, x))) |> List.tryHead) with
            | Some (body, bindings) -> foldLet body bindings |> e ctx
            | None -> failwith "match failed"
        else
          UMatch (v |> e ctx, pts)
    | URun x ->
      match (x |> e ctx) with
        | UDefer x' -> x' |> e ctx
        | r -> r
    | x -> x
  in
  let term' = e ctx term in
  let time = term' |> getTimeOfTerm in
  let rec addRun i t =
    if (i > 0) then
      let t' = 
        match t with
          | x -> URun x
      in addRun (i - 1) t'
    else
      t
  in term' |> addRun time

let eval term = evalWithContext term Map.empty

