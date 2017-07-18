module nml.Evaluation

open nml.Ast
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections

let isValue t =
  let rec isValue i = function
    | UTmLiteral _ -> true
    | UTmTuple xs
    | UTmConstruct (_, xs) -> xs |> List.forall (isValue i)
    | UTmFun x -> x |> isValue (i + 1)
    | UTmBoundVar j -> j < i
    | UTmDefer _
    | UTmExternal _ -> true
    | _ -> false
  in isValue 0 t

let rec shift c d = function
  | UTmBoundVar i when i >= c -> UTmBoundVar (i + d)
  | UTmFun b -> UTmFun (b |> shift (c + 1) d)
  | UTmApply (l, rs) -> UTmApply (l |> shift c d, rs |> List.map (shift c d))
  | UTmLet (n, v, b) -> UTmLet (n, v |> shift c d, b |> shift c d)
  | UTmTuple xs -> UTmTuple (xs |> List.map (shift c d))
  | UTmConstruct (n, xs) -> UTmConstruct (n, xs |> List.map (shift c d))
  | UTmMatch (x, cs) -> UTmMatch (x |> shift c d, cs |> List.map (fun (p, b) -> (p, b |> shift (c + countFvOfPattern p) d)))
  | UTmFixMatch cs -> UTmFixMatch (cs |> List.map (fun (p, b) -> (p, b |> shift (c + 1 + countFvOfPattern p) d)))
  | UTmDefer x -> UTmDefer (x |> shift c d)
  | UTmRun x -> UTmRun (x |> shift c d)
  | x -> x


type EvalMode = Reduce | Replace | Run
let inline isReplace x = match x with | Replace -> true | _ -> false

let inline (<+>) l r = List.append l r

let rec e ctx stack mode = function
  | UTmFreeVar name ->
    ctx |> Map.tryFind name ?| UTmFreeVar name
  | UTmBoundVar i when (i < List.length stack) ->
    stack.[i] ?| UTmBoundVar i
  
  | UTmFun x ->
    x |> e ctx (None :: stack |> List.map (Option.map (shift 0 1))) mode |> UTmFun
  
  | UTmLet (name, value, body) ->
    if (mode |> isReplace) then
      UTmLet (name, value |> e ctx stack mode, body |> e (ctx |> Map.remove name) stack mode)
    else
      body |> e (ctx |> Map.add name (value |> e ctx stack mode)) stack mode
  | UTmLetDefer _ ->
    failwith "impossible_e"

  | UTmTuple xs ->
    xs |> List.map (e ctx stack mode) |> UTmTuple
  | UTmConstruct ("Succ", [UTmLiteral (LNat x)]) -> UTmLiteral (LNat (x + 1u))
  | UTmConstruct ("Succ", [x]) ->
    UTmApply (UTmFreeVar "+", [UTmLiteral (LNat 1u); x |> e ctx stack mode]) |> e ctx stack mode
  | UTmConstruct (name, xs) ->
    UTmConstruct (name, xs |> List.map (e ctx stack mode))
  
  | UTmApply (l, []) -> l |> e ctx stack mode
  | UTmApply (UTmApply (l, rs1), rs2) ->
    UTmApply (l, List.append rs1 rs2) |> e ctx stack mode
  | UTmApply (UTmFreeVar n, rs) ->
    match (ctx |> Map.tryFind n) with
      | Some l -> UTmApply (l, rs) |> e ctx stack mode
      | None -> UTmApply (UTmFreeVar n, rs |> List.map (e ctx stack mode))
  | UTmApply (UTmBoundVar i, rs) when (i < List.length stack) ->
    match (stack |> List.item i) with
      | Some l -> UTmApply (l, rs) |> e ctx stack mode
      | None -> UTmApply (UTmBoundVar i, rs |> List.map (e ctx stack mode))
  | UTmApply (l, rs) when (mode |> isReplace) ->
    UTmApply (l |> e ctx stack Replace, rs |> List.map (e ctx stack Replace))
  | UTmApply (UTmFun body, r :: rest) ->
    UTmApply (body |> e ctx ((Some r :: stack) |> List.map (Option.map (shift 0 1))) Replace |> shift 0 -1, rest) |> e ctx stack mode
  | UTmApply (UTmFixMatch cases, r :: rest) ->
    match (r |> e ctx stack mode) with
      | x when (isValue x) ->
        match (cases |> List.choose (fun (pt, bd) -> matchPattern pt x |> Option.map (fun bind -> (bind, bd))) |> List.tryHead) with
          | Some (bind, body) ->
            let s = List.length bind + 1 in
            let ufm = UTmFixMatch cases |> shift 0 s |> e ctx stack mode in
            let bind' = bind |> List.map (shift 0 s >> Some) in
            let stack' = stack |> List.map (Option.map (shift 0 s)) in
            let mt = body |> e ctx (bind' <+> [Some ufm] <+> stack') Replace |> shift 0 -s in
            UTmApply(mt, rest) |> e ctx stack mode
          | None ->
            printfn "%s" (UTmApply (UTmFixMatch cases, x :: rest) |> to_s);
            failwith "match failed"
      | x -> UTmApply (UTmFixMatch cases |> e ctx stack mode, x :: (rest |> List.map (e ctx stack mode)))
  | UTmApply (UTmExternal (f, t), rs) ->
    let (targs, _) = t |> expandFun in
    if (List.length rs = List.length targs) then
      if (rs |> List.forall isValue) then
        f.value rs |> e ctx stack mode
      else
        match (rs |> List.map (e ctx stack mode)) with
          | xs when (xs |> List.forall isValue) ->
            f.value xs |> e ctx stack mode
          | xs -> UTmApply (UTmExternal (f, t), xs)
    else if (List.length rs > List.length targs) then
      let (args, rest) = rs |> List.splitAt (List.length targs) in
      UTmApply (UTmApply (UTmExternal (f, t), args) |> e ctx stack mode, rest)
    else
      UTmApply (UTmExternal (f, t), rs)
  
  | UTmMatch (x, cs) ->
    match (x |> e ctx stack mode) with
      | x when (x |> isValue && mode |> isReplace |> not) ->
        match (cs |> List.choose (fun (pt, bd) -> matchPattern pt x |> Option.map (fun bind -> (bind, bd))) |> List.tryHead) with
          | Some (bind, body) ->
            let bind = bind |> List.map Some in
            body |> e ctx (bind <+> stack) mode
          | None ->
            printfn "%s" (to_s (UTmMatch (x, cs)));
            failwith "match failed"
      | x ->
        UTmMatch (x, cs |> List.map (fun (pt, bd) -> (pt, bd |> e ctx (List.init (countFvOfPattern pt) (fun _ -> None) <+> stack |> List.map (Option.map (shift 0 (countFvOfPattern pt)))) mode)))
  
  | UTmFixMatch cs ->
    UTmFixMatch (cs |> List.map (fun (pt, bd) -> (pt, bd |> e ctx (List.init (1 + countFvOfPattern pt) (fun _ -> None) <+> stack |> List.map (Option.map (shift 0 (1 + countFvOfPattern pt)))) mode)))
 
  | UTmDefer x ->
    match mode with
      | Run -> x |> e ctx stack Reduce |> UTmDefer
      | _ -> x |> e ctx stack Replace |> UTmDefer
 
  | UTmRun x ->
    let m = if (mode |> isReplace) then mode else Run in
    match (x |> e ctx stack m) with
      | UTmDefer x -> x |> e ctx stack mode
      | x -> 
        if (x |> isValue) then
          x
        else
          UTmRun (x |> e ctx stack mode)
    
  | x -> x

let eval ctx t =
  t |> e ctx [] Reduce

type NextResult = Reducible of UntypedTerm | Halted

let next ctx t =
  match t with
    | UTmDefer x -> Reducible x
    | _ -> Halted

