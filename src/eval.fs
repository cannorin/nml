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
  | UTmMatch (x, cs) -> UTmMatch (x |> shift c d, cs |> List.map (fun (p, b) -> (p, b |> shift c d)))
  | UTmFixMatch (s, cs) -> UTmFixMatch (s, cs |> List.map (fun (p, b) -> (p, b |> shift c d)))
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
    stack |> List.item i ?| UTmBoundVar i
  
  | UTmFun x ->
    x |> e ctx (None :: stack) Replace |> UTmFun
  
  | UTmLet (name, value, body) ->
    if (mode |> isReplace) then
      UTmLet (name, value |> e ctx stack mode, body |> e ctx stack mode)
    else
      body |> e (ctx |> Map.add name (value |> e ctx stack mode)) stack mode
  | UTmLetDefer _ ->
    failwith "impossible_e"

  | UTmTuple xs ->
    xs |> List.map (e ctx stack mode) |> UTmTuple
  | UTmConstruct ("Succ", [x]) ->
    UTmApply (UTmFreeVar "+", [x; UTmLiteral (LNat 1u)]) |> e ctx stack mode
  | UTmConstruct (name, xs) ->
    UTmConstruct (name, xs |> List.map (e ctx stack mode))
  
  | UTmApply (l, []) -> l |> e ctx stack mode
  | UTmApply (UTmApply (l, rs1), rs2) ->
    UTmApply (l, List.append rs1 rs2) |> e ctx stack mode
  | UTmApply (UTmFreeVar n, rs) when (ctx |> Map.containsKey n) ->
    UTmApply (ctx |> Map.find n, rs) |> e ctx stack mode
  | UTmApply (UTmBoundVar i, rs) when (i < List.length stack) ->
    match (stack |> List.item i) with
      | Some l -> UTmApply (l, rs) |> e ctx stack mode
      | None -> UTmApply (UTmBoundVar i, rs |> List.map (e ctx stack mode))
  | UTmApply (l, rs) when (mode |> isReplace) ->
    UTmApply (l, rs |> List.map (e ctx stack Replace))
  | UTmApply (UTmFun body, r :: rest) ->
    UTmApply (body |> e ctx (Some (r |> shift 0 1) :: stack) Replace |> shift 0 -1, rest) |> e ctx stack mode
  | UTmApply (UTmFixMatch (self, cases), r :: rest) ->
    match (r |> e ctx stack mode) with
      | x when isValue x ->
        let m = UTmMatch (x, cases) in 
        UTmApply (m |> e (ctx |> Map.add self (UTmFixMatch (self, cases))) stack mode, rest) |> e ctx stack mode
      | x -> UTmApply (UTmFixMatch (self, cases) |>  e ctx stack mode, x :: (rest |> List.map (e ctx stack mode)))
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
            foldLet body bind |> e ctx stack mode
          | None ->
            printfn "%A" x;
            failwith "match failed"
      | x ->
        let ctxOf pt = ctx |> Map.filter (fun k _ -> fvOfTerm pt |> Set.contains k |> not) in
        UTmMatch (x, cs |> List.map (fun (pt, bd) -> (pt, bd |> e (ctxOf pt) stack Replace)))
  
  | UTmFixMatch (self, cs) ->
    let ctxOf pt = ctx |> Map.filter (fun k _ -> k <> self && fvOfTerm pt |> Set.contains k |> not) in
    UTmFixMatch (self, cs |> List.map (fun (pt, bd) -> (pt, bd |> e (ctxOf pt) stack mode)))    
 
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

