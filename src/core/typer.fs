module nml.Typer

open nml.Ast
open nml.Helper
open nml.Contexts
open Microsoft.FSharp.Collections
open nml.Prelude

type Constraint = Constraint of TemporalType * TemporalType * TypedTemporalTerm with
  override x.ToString() =
    let (Constraint (l, r, tm)) = x
    sprintf "Constraint ( %s = %s ) at %s" (to_s l) (to_s r) (to_s tm.info.source)

let (|Constraint|) = function Constraint (a,b,c) -> (a,b,c)

type Assign = Assign of Map<string, TemporalType>

let inline NTTyVar nm = NotTemporal (TyVar nm)
let (|NTTyVar|_|) = function NotTemporal (TyVar name) -> Some name | _ -> None

let cstrToAsgn xs =
  xs |> List.choose (function | Constraint (NTTyVar name, t, _) -> Some (name, t) | _ -> None )
     |> Map.ofList
     |> Assign

// t |> subst "x" tx
// --> t [x <- tx]
let rec subst vname tvl = function
  | TyVar nm -> if nm = vname then tvl else TyVar nm |> NotTemporal
  | TyDataType (n, ts, prop) ->
    NotTemporal <| 
      TyDataType (
        n,
        ts |> List.map (substTemporal vname tvl),
        { prop with cstrs = prop.cstrs |> List.map (argsmap (substTemporal vname tvl)) })
  | TyDataTypeSelf (n, ts) ->
    NotTemporal <| TyDataTypeSelf (n, ts |> List.map (substTemporal vname tvl))
and substTemporal vname tvl (TyTemporal (ti, ty)) =
  let (TyTemporal (ti', ty')) = subst vname tvl ty
  TyTemporal (ti + ti', ty')

// Assign -> Type -> Type
let substAll (Assign ss) tsbj =
  ss |> Map.fold (fun ts name tnsbj -> ts |> substTemporal name tnsbj) tsbj 

// TyId -> Type -> Constraint list -> Constraint list
let substInConstraints vname tvl cs =
  cs |> List.map (fun (Constraint (ta, tb, u)) ->
    Constraint (ta |> substTemporal vname tvl, tb |> substTemporal vname tvl, u))

let substAllInConstraints (Assign asgn) cs =
  asgn |> Map.fold (fun c name t -> c |> substInConstraints name t) cs

let rename u vs f t =
  let (nvs, u') = vs |> List.length |> genUniqs u
  let qvs = vs |> List.map ((+) "_rename")
  let genasgn xs ys =
    List.map2 (fun x y -> (x, NTTyVar y)) xs ys |> Map.ofList |> Assign
  (t |> f (substAll (genasgn vs qvs)) |> f (substAll (genasgn qvs nvs)), u')

let inline prettify t =
  t |> rename 0 (fvOf t |> Set.toList) id |> fst

let inline prettify' t = NotTemporal t |> prettify

let generalize (ctx: Context<PolyType>) ty =
  let fvs = 
    List.collect (fun (_, t) -> fvOf t |> Set.toList) (ctx |> Context.toTyperMap)
  let tvars = 
    ty |> fvOf
       |> Set.filter (fun y -> fvs |> List.contains y |> not)
  TyScheme (tvars, ty)

let generalizeAllFV ty = TyScheme (fvOf ty, ty)

let inline descheme u (TyScheme (tvs, t)) =
  t |> rename u (Set.toList tvs) id

let inline deschemePrettified t = descheme 0 t |> fst

type FailureReason =
  | UnifyFailed of string option * TemporalType * TemporalType
  | UnknownVar of qualified_name
  | UnknownConst of qualified_name * int
  | NotMatchable of TemporalType
  | TermWithMessage of Printf.StringFormat<string -> string> * obj
  | NotRunnable of TemporalType
  | NotInductive of TemporalType
  override this.ToString() =
    match this with
      | UnifyFailed (None, a, b) ->
        sprintf "'%s' and '%s' are incompatible types." (to_s a) (to_s b)
      | UnifyFailed (Some msg, a, b) ->
        sprintf "'%s' and '%s' are incompatible types. %s"
                (to_s a) (to_s b) msg
      | UnknownVar n ->
        sprintf "'%s' is not defined (unknown variable)." (sprint_qualified n)
      | UnknownConst (n, ac) ->
        sprintf "constructor '%s' that has %i arguments does not exist." (sprint_qualified n) ac
      | NotMatchable t ->
        sprintf "invalid match pattern for type '%s'." (to_s t)
      | NotRunnable t ->
        sprintf "type '%s' is not runnable" (to_s t)
      | TermWithMessage (f, t) ->
        sprintf f (to_s t) |> sprintf "%s"
      | NotInductive t ->
        sprintf "type '%s' is not inductive" (to_s t)

type TyperFailure = {
  reason: FailureReason
  source: Source
} with
  override this.ToString() =
    [
      sprintf "TYPER FAILED: %s" <| to_s this.reason
      sprintf "at %s" <| to_s this.source
    ] |> String.concat System.Environment.NewLine

exception TyperFailed of fail:TyperFailure with
  override this.Message = sprintf "%s" (to_s this.fail)

let inline failat source reason = 
  TyperFailed { reason = reason; source = source } |> raise

// Constraint list -> Constraint list
let unify cs =
  let inline cstrmap f xs =
    xs |> List.map Constraint |> f |> List.map (function Constraint x -> x)
  let rec u cs' =
    match cs' with
      | (s, t, _) :: rest when (s = t) -> u rest
      | (TyTemporal (ti1, TyVar tn), TyTemporal (ti2, s), x) :: _
      | (TyTemporal (ti2, s), TyTemporal (ti1, TyVar tn), x) :: _
        when NotTemporal s |> hasTyVar tn |> not && ti1 <= ti2 ->
        let s' = TyTemporal (ti2 - ti1, s)
        List.append (cs' |> cstrmap (substInConstraints tn s') |> u)
                    [ (NTTyVar tn, s', x) ]
      | (TyTemporal (ti1, ty1), TyTemporal (ti2, ty2), tm) :: rest when ti1 = ti2 ->
        match ty1, ty2 with
          | TyDataType (n, lts, { kind = kind }) & dt, TyDataTypeSelf (m, rts)
          | TyDataTypeSelf (m, rts), TyDataType (n, lts, { kind = kind }) & dt
            when (n = m && List.length lts = List.length rts) ->
            match kind with
              | DTInductive ->
                rest |> List.append (List.map2 (fun x y -> (x, y, tm)) lts rts) |> u
              | DTVariant ->
                UnifyFailed (None, prettify' ty1, prettify' ty2) |> failat tm.info.source
              | _ ->
                NotTemporal dt |> prettify |> NotInductive |> failat tm.info.source
          | TyDataType (lname, lts, { source = lloc }), TyDataType (rname, rts, { source = rloc })
            when (lname = rname && List.length lts = List.length rts && lloc = rloc) ->
            rest |> List.append (List.map2 (fun x y -> (x, y, tm)) lts rts) |> u
          | TyDataType (lname, _, { source = lloc }), 
            TyDataType (rname, _, { source = rloc })
            when List.last lname = List.last rname && lloc.IsFile && rloc.IsFile ->
            let msg =
              sprintf "from different locations:\n  %s\nand\n  %s" (to_s lloc.Location) (to_s rloc.Location)
            UnifyFailed (Some msg, prettify' ty1, prettify' ty2) |> failat tm.info.source
          | TyDataTypeSelf (n, lts), TyDataTypeSelf (m, rts) when n = m ->
            rest |> List.append (List.map2 (fun x y -> (x, y, tm)) lts rts) |> u
          | s, t ->
            printfn "%A, %A" s t
            UnifyFailed (None, prettify' s, prettify' t) |> failat tm.info.source
      | (s, t, u) :: _ ->
        UnifyFailed (None, prettify s, prettify t) |> failat u.info.source
      | [] -> []
  u (cs |> List.map (function Constraint x -> x)) |> List.map Constraint

let inline findDataType ctx uniq n args =
  ctx |> Context.findConstructor n args
      |> Option.map (Tuple.map2 (descheme uniq) id)
      |> Option.bind (function
        | (NotTemporal (TyDataType (_, _, prop) & t), uniq), name ->
          let cstr = prop.cstrs |> List.find (fun c -> c.name = name)
          Some (t, uniq, cstr.args)
        | _ -> None
      ) 

let rec reconTemporal (ctx: Context<PolyType>)
                      (stack: TemporalType list)
                      uniq
                      (term: UntypedTemporalTerm) 
                      : (TypedTemporalTerm * TemporalType * int * Constraint list) =
  let inline addTy t x = Term.addType term t x
  match term.item with
    | TmRun (ti, tm) ->
      let (tm', ty, uniq, cstr) = recon ctx stack uniq tm
      let ty' = ty |> runTypeBy ti
      let term' = TmRun (ti, tm') |> addTy ty'
      (term', ty', uniq, cstr)
    
    | TmLetRun (vname, ti, tmv, tmb) ->
      let (tmv', tyv, uniq, cstrv) = recon ctx stack uniq tmv
      let tyv' =
        cstrv
        |> unify
        |> cstrToAsgn
        |> substAll <| tyv
        |> runTypeBy ti
      let ctx' = ctx |> Context.addTerm vname (tyv' |> generalize ctx)
      let (tmb', tyb, uniq, cstrb) = recon ctx' stack uniq tmb
      let (nb, uniq) = genUniq uniq
      let term' = TmLetRun (vname, ti, tmv', tmb') |> addTy (NTTyVar nb)
      (term', NTTyVar nb, uniq, 
       cstrb @ [Constraint (NTTyVar nb, tyb, term')])

and recon (ctx: Context<PolyType>)
          (stack: TemporalType list)
          uniq
          (term: UntypedTerm) 
          : (TypedTerm * TemporalType * int * Constraint list) =
  let inline addTy t x = Term.addType term t x
  
  let multiRecon uq terms =
    let inline folder (xs, ts, u, cs) x =
      let (x', t', u', cs') = recon ctx stack u x
      (x' :: xs, t' :: ts, u', List.append cs' cs)
    let (terms', types', uniq', cstrs') = terms |> List.fold folder ([], [], uq, [])
    (terms' |> List.rev, types' |> List.rev, uniq', cstrs' |> List.rev)

  match term.item with
    | TmFreeVar vn ->
      let term' t = TmFreeVar vn |> addTy t
      match ctx |> Context.findTerm vn with
        | Some pt ->
          let t', uniq = pt |> descheme uniq
          (term' t', t', uniq, [])
        | None -> 
          UnknownVar vn |> failat term.info
    
    | TmBoundVar i ->
      if (List.length stack > i) then
        let t = stack |> List.item i
        (TmBoundVar i |> addTy t, t, uniq, [])
      else
        failwith "impossible_UBoundVar"
    
    | TmTuple [x] ->
      recon ctx stack uniq x
    
    | TmTuple xs ->
      let (xs', txs, uniq, cstrs) = multiRecon uniq xs
      let t = TyTuple txs
      (TmTuple xs' |> addTy t, t, uniq, cstrs) 
    
    | TmConstruct (n, args) ->
      match findDataType ctx uniq n (Some args) with
        | Some (TyDataType (name, vtargs, { cstrs = cts } & prop), uniq, _) ->
          let ctargs =
            (cts |> List.find (fun c -> c.name = List.last n)).args
          let (args', targs, uniq, cstrs) = multiRecon uniq args
          let vcstrs =
            targs
              |> List.map2 (fun x y -> (x, y)) ctargs
              |> List.map2 (fun x (y, z) -> Constraint (y, z, NotTemporalTerm x)) args'
          let (u, uniq) = genUniq uniq
          let newTerm = TmConstruct (n, args') |> addTy (NTTyVar u)
          let ty' = TyDataType (name, vtargs, { prop with cstrs = cts }) |> NotTemporal
          (newTerm,
           NTTyVar u, uniq,
           vcstrs @ cstrs @ [Constraint (NTTyVar u, ty', NotTemporalTerm newTerm)])
        | _
        | None -> UnknownConst (n, List.length args) |> failat term.info

    | TmApply (l, rs) ->
      let (l', tl, uniq, cstr1) = recon ctx stack uniq l
      let (rs', trs, uniq, cstr2) = multiRecon uniq rs
      let (nv, uniq) = genUniq uniq
      let newTerm = TmApply (l', rs') |> addTy (NTTyVar nv)
      (newTerm,
       NTTyVar nv, uniq,
       cstr2 @ cstr1 @ 
        [Constraint (tl, foldFun (TyFun) trs (NTTyVar nv), NotTemporalTerm newTerm)])

    | TmLiteral l -> 
      match l with
        | LNat _ ->  TmLiteral l |> addTy TyNat,  TyNat, uniq, []
        | LBool _ -> TmLiteral l |> addTy TyBool, TyBool, uniq, []
        | LUnit ->   TmLiteral l |> addTy TyUnit, TyUnit, uniq, []
   
    | TmLet (x, value, body) ->
      let (value', tvalue, uniq, cstr1) = recon ctx stack uniq value
      let cstr1' = unify cstr1
      let tvalue' = tvalue |> substAll (cstrToAsgn cstr1')
      let tx = generalize ctx tvalue'
      let ctx' = ctx |> Context.addTerm x tx
      let (body', tbody, uniq, cstr2) = recon ctx' stack uniq body

      let (r, uniq) = genUniq uniq
      let newTerm = TmLet (x, value', body') |> addTy (NTTyVar r)
      (newTerm, 
       NTTyVar r, uniq, 
       cstr1 @ cstr2 @ [Constraint (NTTyVar r, tbody, NotTemporalTerm newTerm)])
   
    | TmDefer (time, x) ->
      let (x', tx, uniq, cstr) = reconTemporal ctx stack uniq x
      let ty = tx |> delayTypeBy time
      let newx = TmDefer (time, x') |> addTy ty
      (newx, ty, uniq, cstr)
    
    | TmBuiltin (n, t, b)         -> 
      let t', uniq = descheme uniq t
      TmBuiltin (n, t, b) |> addTy t', t', uniq, []
    | TmRunnableBuiltin (n, t, b) ->
      let t', uniq = descheme uniq t
      TmRunnableBuiltin (n, t, b) |> addTy t', t', uniq, []

    | TmFunction (funtype, cases) ->
      let (argTy, uniq) = reconFromPatterns term.info cases ctx uniq
      let (retTy, uniq) = genUniq uniq |> Tuple.map2 NTTyVar id
      let (ty, uniq) = genUniq uniq |> Tuple.map2 NTTyVar id
      let stack =
        match funtype with
          | FunNormal -> stack
          | _         -> ty :: stack
      let (bs', tbs, uniq, css) =
        let f = 
          cases 
            |> List.map (fun (pat, body) ->
                match (ctx |> bindPattern pat argTy) with
                  | Some stack' -> 
                    (List.append stack' stack, body)
                  | None ->
                    NotMatchable argTy |> failat term.info
              )
            |> List.foldBack (fun (st, b) (bs', tbs, u, css) ->
                let (b', tb, u', cs) = recon ctx st u b in
                (b' :: bs', tb :: tbs, u', List.append cs css)
              )
        in f ([], [], uniq, [])
      let cases' = cases |> List.map2 (fun nb (pat, _) -> (pat, nb)) bs'
      let bcstr =
        tbs |> List.map2 (fun x t -> Constraint (retTy, t, NotTemporalTerm x)) bs'
      let newfun = TmFunction (funtype, cases') |> addTy ty
      let cstrs = css @ bcstr @ [Constraint (ty, TyFun (argTy, retTy), NotTemporalTerm newfun)]
      match funtype with
        | FunNormal -> ()
        | FunFixpoint -> verifyTermination term.info cases' |> ignore
      (newfun, ty, uniq, cstrs)

and verifyTermination source cases =
  let fvc p b = List.init (countFvOfPattern p) (fun _ -> b)

  let rec verifyTemporal dom codom = function
    | TmRun (_, Item tm) -> verify dom codom tm
    | TmLetRun (_, _, Item tmv, Item tmb) -> verify dom codom tmv && verify dom codom tmb
  and verify dom codom t =
    let self = dom |> List.length in
    let res = 
      match t with
        | TmApply (Item (TmBoundVar f), (Item (TmBoundVar x)) :: _) when (f = self) ->
          codom |> List.tryItem x ?| false
        | TmApply (Item (TmBoundVar f), _) when (f = self) -> false
        | TmApply (Item (TmFunction (_, cs)), Item (TmBoundVar x) :: _)
          when (dom |> List.tryItem x ?| false) ->
          cs |> List.forall (fun (pat, Item bdy) ->
            bdy |> verify (dom |> List.append (fvc pat true))
                          (codom |> List.append (fvc pat true)))
        | TmTuple xs
        | TmConstruct (_, xs) ->
          xs |> List.map With.itemof |> List.forall (verify dom codom)
        | TmLet (_, Item l, Item r) ->
          [l; r] |> List.forall (verify dom codom)
        | TmApply (Item l, rs) ->
          l :: (rs |> List.map With.itemof) |> List.forall (verify dom codom)
        | TmBoundVar x -> self <> x
        | TmFreeVar _
        | TmLiteral _
        | TmBuiltin _
        | TmRunnableBuiltin _ -> true
        | TmDefer (_, Item x) ->
          verifyTemporal dom codom x
        | TmFunction(FunNormal, cs) ->
          cs |> List.forall (fun (pat, bdy) ->
            bdy.item |> verify (dom |> List.append (fvc pat false))
                               (dom |> List.append (fvc pat false)))
        | TmFunction(FunFixpoint, cs) ->
          cs |> List.forall (fun (pat, bdy) ->
            bdy.item |> verify ((false :: dom) |> List.append (fvc pat false))
                               ((false :: codom) |> List.append (fvc pat false)))
    if res then
      res
    else
      TermWithMessage ("Recursion is not well-founded. Bad expression: '%s'", t) |> failat source
  in
  cases |> List.forall (fun (ptn, bdy) ->
      match ptn with
        | MtConstruct _ -> verify (fvc ptn true) (fvc ptn true) bdy.item
        | _ -> verify (fvc ptn true) [] bdy.item
    )

and reconFromPatterns source pats ctx uniq =
  let (a, uniq) = genUniq uniq
  let rec gh uniq pat =
    match pat with
      | MtTuple xs ->
        let (nq, ts) =
          xs |> List.fold (fun (u, ts) x ->
            let (nu, nt) = gh u x in (nu, nt :: ts)) (uniq, [])
        (nq, TyTuple (ts |> List.rev))
      | MtConstruct (x, ys) ->
        let (name, targs, ctargs, prop, nq) =
          match findDataType ctx uniq x (Some ys) with
            | Some (TyDataType (name, targs, { cstrs = cts } & prop), uniq, ctargs) ->
              (name, targs, ctargs, { prop with cstrs = cts }, uniq)
            | _ -> UnknownVar x |> failat source
        let (fnq, pts) =
          ys |> List.fold (fun (u, ts) y ->
            let (nu, nt) = gh u y in (nu, nt :: ts)) (nq, [])
        let asgn = 
          ctargs |> List.rev
                 |> List.map2 (fun y -> (function | NTTyVar x -> Some (x, y) | _ -> None)) pts 
                 |> List.choose id |> Map.ofList |> Assign 
        let vt = TyDataType (name, targs, prop) |> NotTemporal |> substAll asgn
        (fnq, vt)
      | MtLiteral LUnit -> (uniq, TyUnit)
      | MtLiteral (LNat _) -> (uniq, TyNat)
      | MtLiteral (LBool _) -> (uniq, TyBool)
      | MtWildcard
      | MtBoundVar _ ->
        let (tn, nq) = genUniq uniq
        (nq, NTTyVar tn)
  let (uniq, args) =
    pats |> List.map fst
         |> List.fold (fun (u, ts) p ->
            let (nu, t) = gh u p in (nu, (t, p) :: ts)) (uniq, [])
  let cstr =
    args |> List.map (fun (t, p) -> Constraint (NTTyVar a, t, p.asTerm() |> NotTemporalTerm))
  let rt = NTTyVar a |> substAll (unify cstr |> cstrToAsgn)
  exhaustiveCheck source (pats |> List.map fst) rt ctx;
  (rt, uniq)

and bindPattern pat t ctx =
  let rec bt pat t =
    match (pat, t) with
      | MtTuple xs, TyTuple ts when (List.length xs = List.length ts) ->
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat 
      | MtConstruct (n, xs), NotTemporal (TyDataTypeSelf (name, ts)) ->
        match ctx |> Context.findType name |> Option.map deschemePrettified with
          | Some (NotTemporal (TyDataType (name, vts, { cstrs = cts } & prop))) ->
            let asgn =
              List.map2 (fun x -> 
                function NTTyVar y -> (y, x) |> Some | _ -> None
              ) ts vts
              |> List.choose id |> Map.ofList |> Assign
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            bt (MtConstruct (n, xs)) (TyDataType (name, ts, { prop with cstrs = cts' }) |> NotTemporal)
          | _ ->
            failwith "impossible_bindPattern"
      | MtConstruct (n, xs), NotTemporal (TyDataType (_, _, { cstrs = cts }))
        when (cts |> List.exists (fun c -> c.name = List.last n && List.length xs = List.length (c.args))) ->
        let ts = (cts |> List.find (fun c -> c.name = List.last n)).args in
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | MtWildcard, _
      | MtLiteral LUnit, TyUnit
      | MtLiteral (LNat _), TyNat
      | MtLiteral (LBool _), TyBool -> []
      | MtBoundVar x, t -> [ (x, t) ]
      | _ ->
        failwith "bindfailed"
  try
    bt pat t |> List.map snd |> Some
  with
    | _ -> None

and getInductionDepth ptns ctx =
  let (<+>) (x, i) ys =
    match (ys |> Map.tryFind x) with
      | Some i' -> ys |> Map.add x (i + i')
      | None -> ys |> Map.add x i
  let concat ms =
    ms |> List.fold (fun mp xs -> xs |> Map.toList |> List.fold (fun m x -> x <+> m) mp) Map.empty
  let rec gett = function
    | MtTuple xs ->
      xs |> List.map gett |> concat
    | MtConstruct (x, ys) ->
      match findDataType ctx 0 x (Some ys) with
        | Some (TyDataType (name, _, _), _, _) -> (name, 1) <+> (ys |> List.map gett |> concat)
        | _ -> Map.empty
    | MtWildcard
    | MtBoundVar _ -> Map.empty
    | _ -> Map.empty
  ptns |> List.map gett |> concat

and exhaustiveCheck source ptns t ctx =
  let dmp = getInductionDepth ptns ctx
  let rec cartProd lol =
    let f n = function
      | [] -> [[n]]
      | xss -> xss |> List.map (fun xs -> n :: xs)
    match lol with
      | [] -> []
      | h :: t -> h |> List.collect (fun n -> f n (cartProd t))
  let next name mp =
    match mp |> Map.tryFind name with
      | Some 0
      | Some 1 -> mp |> Map.remove name
      | Some i -> mp |> Map.add name (i - 1)
      | None -> mp
  let rec genReq mp = function
    | TyTuple ts ->
      ts |> List.map (genReq mp) |> cartProd |> List.map (TmTuple >> With.noinfo)
    | TyUnit -> [ TmLiteral LUnit |> With.noinfo ]
    | TyBool -> [ TmLiteral (LBool true); TmLiteral (LBool false)] |> List.map With.noinfo
    | NotTemporal t ->
      match t with
        | TyDataType (vname, _, { cstrs = cts }) ->
          let ns = namespaceof vname
          List.collect (fun c ->
            c.args |> List.map (genReq (mp |> next vname))
                   |> cartProd
                   |> (function 
                        | [] -> [ TmConstruct (ns @ [c.name], []) ]
                        | x -> x |> List.map (fun xs -> TmConstruct (ns @ [c.name], xs))
                      )) cts
          |> List.map With.noinfo
        | TyDataTypeSelf (name, ts) ->
          match ctx |> Context.findType name|> Option.map deschemePrettified with
            | Some (NotTemporal (TyDataType (name, vts, { cstrs = cts } & prop))) ->
              if (mp |> Map.containsKey name) then
                let asgn =
                  vts |> List.map2 (fun x ->
                           function | NTTyVar y -> (y, x) |> Some | _ -> None
                         ) ts 
                      |> List.choose id |> Map.ofList |> Assign in
                let cts' = cts |> List.map (argsmap (substAll asgn)) in
                genReq mp (TyDataType (name, vts, { prop with cstrs = cts' }) |> NotTemporal)
              else
                [ TmFreeVar ["_"] |> With.noinfo ]
            | _ -> 
              printfn "%A" name;
              failwith "impossible_exhaustivenessCheck"
        | _ -> [ TmFreeVar ["_"] |> With.noinfo ] // only matched with variable patterns
      | _ -> [ TmFreeVar ["_"] |> With.noinfo ] // only matched with variable patterns
  let possiblePatterns = genReq dmp t
  let unmatched =
    ptns |> List.fold (fun xs ptn ->
        let xs' = xs |> List.filter (matchPattern ptn >> Option.isNone) in
        xs'
      ) possiblePatterns
  if not (List.isEmpty unmatched) then
    TermWithMessage ("The pattern match is not exhaustive.\nFor example, the value '%s' will fail.", unmatched |> List.head) |> failat source
  else
    ()

let inline private inferWithContextBase (ctx: TypeContext) term reconImpl =
  let (term', _, _, cstr) = reconImpl ctx [] 0 term
  let cstr' = unify cstr |> cstrToAsgn
  let tterm = term' |> Term.mapInfo (fun i -> { i with ty = i.ty |> substAll cstr' })
  tterm

let inline inferWithContext ctx term         : TypedTerm =
  inferWithContextBase ctx term recon
let inline inferWithContextTemporal ctx term : TypedTemporalTerm =
  inferWithContextBase ctx term reconTemporal

let inline infer term =         inferWithContext [] term
let inline interTemporal term = inferWithContextTemporal [] term

let inline printTypeError e = to_s e |> printfn "%s"