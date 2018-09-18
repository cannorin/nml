module nml.Evaluation

open nml.Ast
open nml.Helper
open nml.Contexts
open Microsoft.FSharp.Collections
open With

let rec replace  (ctx: Context<EracedTerm>) stack (Item tm) =
  noinfo <|
    match tm with
      | TmFreeVar vname ->
        match ctx |> Context.findTerm vname with
          | Some value -> replace ctx stack value |> itemof
          | None -> tm
      | TmBoundVar i when (i < List.length stack) ->
        (stack.[i] ?| noinfo (TmBoundVar i)).item
      | TmLet (vn, tv, tb) ->
        let ctx' = ctx |> Context.removeTerm vn
        TmLet (vn, tv |> replace ctx stack, tb |> replace ctx' stack)
      | TmTuple xs -> TmTuple (xs |> List.map (replace ctx stack))
      | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (replace ctx stack))
      | TmApply (l, rs) -> TmApply (replace ctx stack l, rs |> List.map (replace ctx stack))
      | TmDefer (t, x) -> TmDefer (t, replace' ctx stack x)
      | TmFunction (ft, cs) ->
        let dc = match ft with FunNormal -> 0 | _ -> 1
        TmFunction (
          ft,
          cs |> List.map (fun (pt, bd) ->
            pt,
            bd |> replace ctx ((None |> List.replicate (dc + countFvOfPattern pt)) @ stack)
          )
        )
      | TmBoundVar _ | TmLiteral _ | TmBuiltin _ | TmRunnableBuiltin _ -> tm

and     replace' (ctx: Context<EracedTerm>) stack (Item tm) =
  noinfo <|
    match tm with
      | TmRun (ti, tm) -> TmRun (ti, tm |> replace ctx stack)
      | TmLetRun (vn, ti, tv, tb) ->
        let ctx' = ctx |> Context.removeTerm vn
        TmLetRun (vn, ti, tv |> replace ctx stack, tb |> replace ctx' stack)

let rec shift c d (tm: EracedTerm) =
  noinfo <|
    match tm.item with
      | TmBoundVar i when i >= c -> TmBoundVar (i + d)
      | TmFun b -> TmFun (b |> shift (c + 1) d)
      | TmApply (l, rs) -> TmApply (l |> shift c d, rs |> List.map (shift c d))
      | TmLet (n, v, b) -> TmLet (n, v |> shift c d, b |> shift c d)
      | TmTuple xs -> TmTuple (xs |> List.map (shift c d))
      | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (shift c d))
      | TmFunction (ft, cs) ->
        let dc = match ft with FunNormal -> 0 | _ -> 1
        TmFunction (ft,
          cs |> List.map (fun (p, b) -> (p, b |> shift (c + dc + countFvOfPattern p) d)))
      | TmDefer (t, x) -> TmDefer (t, x |> shift' c d)
      | TmLiteral _ | TmBoundVar _ | TmFreeVar _ | TmBuiltin _ | TmRunnableBuiltin _ -> tm.item
and shift' c d (tm: EracedTemporalTerm) =
  noinfo <|
    match tm.item with
      | TmRun (t, x) -> TmRun (t, x |> shift c d)
      | TmLetRun (n, t, v, b) -> TmLetRun (n, t, v |> shift c d, b |> shift c d)

let rec e' (ctx: Context<EracedTerm>) stack (tm: EracedTemporalTerm) : EracedTerm =
  match tm.item with
    | TmRun (ti, tm) ->
      match ti, tm |> e ctx stack with
        | ti, Item (TmApply (Item (TmRunnableBuiltin (_, _, EValue f)), args)) ->
          match f.Eval (ti, args |> List.map (e ctx stack)) with
            | Some tm' -> tm' |> e ctx stack
            | None     -> undefined ()

        | TimeInf, Item (TmDefer (_, tm)) ->
          TmRun (TimeInf, tm |> e' ctx stack) |> noinfo |> e' ctx stack
        | TimeInf, tm -> tm
        
        | TimeN _,     Item (TmDefer (TimeInf, tm)) ->
          TmDefer (TimeInf, tm) |> noinfo
        | TimeN (S n), Item (TmDefer (TimeN (S m), tm)) ->
          TmRun (TimeN n, noinfo <| TmDefer (TimeN m, tm))
          |> noinfo |> e' ctx stack
        | TimeN _, tm -> tm
    
    | TmLetRun (vname, time, tmvalue, tmbody) ->
      let tmvalue' = TmRun (time, tmvalue) |> noinfo |> e' ctx stack
      tmbody |> e (ctx |> Context.addTerm vname tmvalue') stack

and     e  (ctx: Context<EracedTerm>) stack (tm: EracedTerm) : EracedTerm =
  match tm.item with
    | TmLiteral l -> TmLiteral l |> noinfo

    | TmFreeVar vname ->
      match ctx |> Context.findTerm vname with
        | Some value -> e ctx stack value
        | None -> tm
    | TmBoundVar i when (i < List.length stack) ->
      stack.[i] ?| noinfo (TmBoundVar i)
    | TmBoundVar _ -> tm
    
    | TmLet (vname, tmvalue, tmbody) ->
      let tmvalue' = tmvalue |> e ctx stack
      tmbody |> e (ctx |> Context.addTerm vname tmvalue') stack

    | TmTuple xs -> TmTuple (xs |> List.map (e ctx stack)) |> noinfo
    | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (e ctx stack)) |> noinfo

    | TmApply (tm, []) -> e ctx stack tm
    | TmApply (Item (TmApply (l, rs1)), rs2) ->
      TmApply (l, rs1 @ rs2) |> noinfo |> e ctx stack
    | TmApply (Item (TmFreeVar var), args)
      when ctx |> Context.findTerm var |> Option.isSome ->
        TmApply (ctx |> Context.findTerm var |> Option.get, args)
        |> noinfo |> e ctx stack
    | TmApply (Item (TmBoundVar i), args) 
      when List.length stack > i && stack.[i].IsSome ->
        TmApply (stack.[i].Value, args) |> noinfo |> e ctx stack
    | TmApply (Item (TmBuiltin (_, _, EValue f)), args) ->
      match f.Eval (args |> List.map (e ctx stack)) with
        | Some tm' -> tm' |> e ctx stack
        | None     -> undefined ()

    | TmApply (Item (TmFunction (ft, cs)), arg :: rest) ->
      let arg = arg |> e ctx stack
      match cs |> List.choose (fun (pt, bd) -> 
                    matchPattern pt arg
                    |> Option.map (fun bind -> (bind, bd))
                  )
               |> List.tryHead with
        | Some (bind, body) ->
          let s = List.length bind + match ft with FunNormal -> 0 | _ -> 1
          let f = TmFunction (ft, cs) |> noinfo |> shift 0 s |> e ctx stack
          let stack = 
               (bind |> List.map (shift 0 s >> Some))
             @ (match ft with FunNormal -> [] | _ -> [Some f])
             @ stack |> List.map (Option.map (shift 0 s))
          let mt = body |> e ctx stack |> shift 0 -s
          TmApply (mt, rest) |> noinfo |> e ctx stack
        | None ->
          TmApply (
            TmFunction (ft, cs) |> noinfo |> e ctx stack,
            arg :: (rest |> List.map (e ctx stack))
          ) |> noinfo
    | TmApply _ -> tm

    | TmFunction (ft, cs) ->
      let c = match ft with FunNormal -> 0 | _ -> 1
      TmFunction (
        ft,
        cs |> List.map (fun (pt, bd) ->
                  pt,
                  let fvc = countFvOfPattern pt + c in
                  e ctx
                    (List.init fvc (fun _ -> None) @ stack
                     |> List.map (Option.map (shift 0 fvc)))
                    bd
              )
      ) |> noinfo
    
    | TmDefer (ti, tm) -> TmDefer (ti, tm |> replace' ctx stack) |> noinfo

    | TmBuiltin _ | TmRunnableBuiltin _ -> tm
    
let inline eval ctx tm = e ctx [] tm
let inline eval' ctx tm = e' ctx [] tm
