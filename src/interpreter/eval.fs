module nml.Evaluation

open nml.Ast
open nml.Helper
open nml.Contexts
open Microsoft.FSharp.Collections
open With

let rec shift c d (tm: EracedTerm) =
  noinfo <|
    match tm.item with
      | TmBoundVar i when i >= c -> TmBoundVar (i + d)
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

let rec replace  (ctx: Context<EracedTerm>)
                 (bindings: Map<qualified_name, EracedTerm>)
                 (stack: EracedTerm option list)
                 (Item tm) =
  noinfo <|
    match tm with
      | TmConstruct (["S"], [n]) ->
        match n |> replace ctx bindings stack with  
          | Item (TmLiteral (LNat n)) ->
            TmLiteral (LNat (S n))
          | n' -> TmConstruct (["S"], [n'])
      | TmFreeVar vname ->
        match bindings |> Map.tryFind vname, ctx |> Context.findTerm vname with
          | Some value, _
          | None, Some value -> replace ctx bindings stack value |> itemof
          | _ -> tm
      | TmBoundVar i when (i < List.length stack) ->
        (stack.[i] |> Option.map (replace ctx bindings stack) ?| noinfo (TmBoundVar i)).item
      | TmLet (vn, tv, tb) ->
        let ctx', bindings' = ctx |> Context.removeTerm vn, bindings |> Map.remove [vn]
        TmLet (vn, tv |> replace ctx bindings stack, tb |> replace ctx' bindings' stack)
      | TmTuple xs -> TmTuple (xs |> List.map (replace ctx bindings stack))
      | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (replace ctx bindings stack))
      | TmApply (tm, []) -> replace ctx bindings stack tm |> itemof
      | TmApply (Item (TmApply (l, rs1)), rs2) ->
        TmApply (l, rs1 @ rs2) |> noinfo |> replace ctx bindings stack |> itemof
      | TmApply (l, rs) -> TmApply (replace ctx bindings stack l, rs |> List.map (replace ctx bindings stack))
      | TmDefer (t, x) -> TmDefer (t, replace' ctx bindings stack x)
      | TmFunction (ft, cs) ->
        let dc = match ft with FunNormal -> 0 | _ -> 1
        TmFunction (
          ft,
          cs |> List.map (fun (pt, bd) ->
            let fvc = dc + countFvOfPattern pt
            pt,
            bd |> replace ctx bindings (
              List.replicate fvc None @ stack |> List.map (Option.map (shift 0 fvc))
            )
          )
        )
      | TmBoundVar _ | TmLiteral _ | TmBuiltin _ | TmRunnableBuiltin _ -> tm

and     replace' ctx bindings stack (Item tm) =
  noinfo <|
    match tm with
      | TmRun (ti, tm) -> TmRun (ti, tm |> replace ctx bindings stack)
      | TmLetRun (vn, ti, tv, tb) ->
        let ctx', bindings' = ctx |> Context.removeTerm vn, bindings |> Map.remove [vn]
        TmLetRun (vn, ti, tv |> replace ctx bindings stack, tb |> replace ctx' bindings' stack)

let rec e' (ctx: Context<EracedTerm>)
           (bindings: Map<qualified_name, EracedTerm>)
           (stack: EracedTerm option list)
           (tm: EracedTemporalTerm) : EracedTerm =
  match tm.item with
    | TmRun (ti, tm) ->
      match ti, tm |> e ctx bindings stack with
        | ti, Item (TmApply (Item (TmRunnableBuiltin (_, _, EValue f)), args)) ->
          match f.Eval (ti, args |> List.map (e ctx bindings stack)) with
            | Some tm' -> tm' |> e ctx bindings stack
            | None     -> undefined ()

        | ti, Item (TmDefer (TimeN Z, tm)) ->
          match tm.item with
            | TmRun (ti', tm') ->
              TmRun (ti + ti', tm') |> noinfo |> e' ctx bindings stack
            | TmLetRun (vn, ti', tmv, tmb) ->
              TmLetRun (vn, ti + ti', tmv, tmb) |> noinfo |> e' ctx bindings stack

        | TimeInf, Item (TmDefer (_, tm)) ->
          TmRun (TimeInf, tm |> e' ctx bindings stack) |> noinfo |> e' ctx bindings stack
        | TimeInf, tm -> tm |> e ctx bindings stack
        
        | TimeN _,     Item (TmDefer (TimeInf, tm)) ->
          TmDefer (TimeInf, tm) |> noinfo
        | TimeN (S n), Item (TmDefer (TimeN (S m), tm)) ->
          TmRun (TimeN n, noinfo <| TmDefer (TimeN m, tm))
          |> noinfo |> e' ctx bindings stack
        | TimeN _, tm -> tm |> e ctx bindings stack
    
    | TmLetRun (vname, time, tmvalue, tmbody) ->
      let tmvalue' =
        TmRun (time, tmvalue) 
        |> noinfo 
        |> e' (ctx |> Context.removeTerm vname) 
              (bindings |> Map.remove [vname])
              stack
      tmbody |> e ctx (bindings |> Map.add [vname] tmvalue') stack

and     e  (ctx: Context<EracedTerm>) 
           (bindings: Map<qualified_name, EracedTerm>)
           (stack: EracedTerm option list)
           (tm: EracedTerm) : EracedTerm =
  match tm.item with
    | TmLiteral l -> TmLiteral l |> noinfo
    | TmConstruct (["S"], [n]) ->
      match n |> e ctx bindings stack with  
        | Item (TmLiteral (LNat n)) ->
          TmLiteral (LNat (S n)) |> noinfo
        | n' -> TmConstruct (["S"], [n']) |> noinfo

    | TmFreeVar vname ->
      match bindings |> Map.tryFind vname, ctx |> Context.findTerm vname with
        | Some value, _
        | None, Some value -> e ctx bindings stack value
        | _ -> tm
    | TmBoundVar i when (i < List.length stack) ->
      stack.[i] |> Option.map (e ctx bindings stack) ?| tm
    | TmBoundVar _ -> tm
    
    | TmLet (vname, tmvalue, tmbody) ->
      tmbody |> e ctx (bindings |> Map.add [vname] tmvalue) stack

    | TmTuple xs -> TmTuple (xs |> List.map (e ctx bindings stack)) |> noinfo
    | TmConstruct (n, xs) -> TmConstruct (n, xs |> List.map (e ctx bindings stack)) |> noinfo

    | TmApply (tm, []) -> e ctx bindings stack tm
    | TmApply (Item (TmApply (l, rs1)), rs2) ->
      TmApply (l, rs1 @ rs2) |> noinfo |> e ctx bindings stack
    
    | TmApply (Item (TmBuiltin (_, _, EValue f)) & bf, args) ->
      let args = args |> List.map (e ctx bindings stack)
      match f.Eval args with
        | Some tm' -> tm' |> e ctx bindings stack
        | None     -> TmApply (bf, args) |> noinfo
    
    | TmApply (Item (TmFun body), arg :: rest) ->
      let stack' = (Some arg :: stack) |> List.map (Option.map (shift 0 1))
      TmApply (
        body |> replace ctx bindings stack' |> shift 0 -1,
        rest) |> noinfo |> e ctx bindings stack

    | TmApply (Item (TmFunction (ft, cs)), arg :: rest) ->
      let arg = arg |> e ctx bindings stack
      match cs |> List.choose (fun (pt, bd) -> 
                    matchPattern pt arg
                    |> Option.map (fun bind -> (bind, bd))
                  )
               |> List.tryHead with
        | Some (bind, body) when List.length cs = 1 || (Term.isVariable arg |> not) ->
          let stack' =
            let bind = bind |> List.map Some
            match ft with
              | FunNormal -> bind @ stack
              | _ ->
                let s = List.length bind + 1
                let f = TmFunction (ft, cs)
                        |> noinfo
                        |> shift 0 s
                        |> replace ctx bindings stack
                        |> shift 0 -s
                bind @ [Some f] @ stack
          let mt = body |> replace ctx bindings stack'
          TmApply (mt, rest) |> noinfo |> e ctx bindings stack
        | _ ->
          TmApply (
            TmFunction (ft, cs) |> noinfo |> e ctx bindings stack,
            arg :: (rest |> List.map (e ctx bindings stack))
          ) |> noinfo
    | TmApply (f, args) ->
      let f' = f |> e ctx bindings stack
      if f = f' then
        TmApply (f', args |> List.map (e ctx bindings stack)) |> noinfo
      else
        TmApply (f', args) |> noinfo |> e ctx bindings stack

    | TmFunction (ft, cs) ->
      let c = match ft with FunNormal -> 0 | _ -> 1
      TmFunction (
        ft,
        cs |> List.map (fun (pt, bd) ->
                  pt,
                  let fvc = countFvOfPattern pt + c
                  e ctx bindings
                    (List.replicate fvc None @ stack
                     |> List.map (Option.map (shift 0 fvc)))
                    bd
              )
      ) |> noinfo
    
    | TmDefer (ti, tm) -> TmDefer (ti, tm |> replace' ctx bindings stack) |> noinfo

    | TmBuiltin _ | TmRunnableBuiltin _ -> tm
    
let inline eval ctx tm = e ctx Map.empty [] tm
let inline eval' ctx tm = e' ctx Map.empty [] tm
