module nml.Typer

open nml.Ast
open nml.Helper
open nml.Contexts
open Microsoft.FSharp.Collections

type Constraint = Constraint of Type * Type * UntypedTerm
let cstr_Extract = function
  | Constraint (s, t, u) -> (s, t, u)

type Assign = Assign of Map<string, Type>
let asgn_Extract = function
  | Assign x -> x

let cstr_toAsgn cstr =
  match cstr with
    | xs -> xs |> List.choose (function | Constraint (TyVar name, t, _) -> Some (name, t) | _ -> None ) |> Map.ofList |> Assign

// tx |> substIn "x" t
// --> t [x <- tx]
let substIn vname tsbj tvl =
  let rec sub = function
    | TyFun (a, b) -> TyFun (sub a, sub b)
    | TyVar nm when (nm = vname) -> tvl
    | TyDeferred t -> TyDeferred (sub t)
    | TyDataType (n, ts, cts, p, info) ->
      TyDataType (n, ts |> List.map sub, cts |> List.map (argsmap sub), p, info)
    | TyDataTypeSelf (n, ts) -> TyDataTypeSelf (n, ts |> List.map sub)
    | TyScheme (tvs, t) -> TyScheme (tvs, sub t)
    | x -> x
  in sub tsbj

// Assign -> Type -> Type
let substAll ss tsbj =
  ss
    |> asgn_Extract
    |> Map.fold (fun ts name tnsbj -> tnsbj |> substIn name ts) tsbj 

// TyId -> Type -> Constraint list -> Constraint list
let substInConstraints vname tvl cs =
  cs |> List.map (fun (Constraint (ta, tb, u)) -> Constraint (tvl |> substIn vname ta, tvl |> substIn vname tb, u))

let substAllInConstraints asgn cs =
  asgn
    |> asgn_Extract
    |> Map.fold (fun c name t -> c |> substInConstraints name t) cs

let rec removeForall = function
  | TyScheme (_, t) -> removeForall t
  | t -> t

let prettify uniq ts =
  let rec getTyNames = function
    | TyVar n -> set [n]
    | TyFun (a, b) -> Set.union (getTyNames a) (getTyNames b)
    | TyDeferred t -> getTyNames t
    | TyDataType (_, ts, _, _, _)
    | TyDataTypeSelf (_, ts) -> ts |> List.map getTyNames |> List.fold Set.union (set [])
    | TyScheme (vs, t) -> getTyNames t |> Set.union vs
    | _ -> set []
  in
  let (fvs, ts) =
    let f t =
      let fv = getTyNames t in
      let t =
        if (Set.count fv > 0) then
          TyScheme (fv, t)
        else
          t
      in (fv, t)
    in
    ts |> List.map f
       |> List.fold (fun (fvs, ts) (fv, t) -> (Set.union fvs fv, t :: ts)) (Set.empty, [])
       |> (fun (x, y) -> (x, List.rev y))
  in
  let rec rename m = function
    | TyScheme (vs, t) ->
      TyScheme (vs |> Set.map (fun x -> m |> Map.tryFind x ?| x), rename m t) 
    | x -> x |> substAll (m |> Map.map (fun _ v -> TyVar v) |> Assign)
  let ftmap = fvs |> Set.map (fun x -> (x, x + "+")) |> Set.toList |> Map.ofList in
  let ts' = ts |> List.map (rename ftmap) in
  let (us, uniq) = fvs |> Set.count |> genUniqs uniq in
  let newmap = fvs |> Set.toList |> List.map2 (fun y x -> (x + "+", y)) us |> Map.ofList in
  (ts' |> List.map (rename newmap), uniq)


let prettify1 a =
  match (prettify 0 [a]) with
    | ([a'], _) -> a'
    | _ -> failwith "impossible_prettify1"

let prettify2 (a, b) =
  match (prettify 0 [a; b]) with
    | ([a'; b'], _) -> (a', b')
    | _ -> failwith "impossible_prettify2"

let rename u vs f t =
  let (nvs, u') = vs |> List.length |> genUniqs u in
  let qvs = vs |> List.map ((+) "_rename") in
  let genasgn xs ys =
    List.map2 (fun x y -> (x, TyVar y)) xs ys |> Map.ofList |> Assign
  in
  (t |> f (substAll (genasgn vs qvs)) |> f (substAll (genasgn qvs nvs)), u')


type FailureReason =
  | UnifyFailed of Type * Type * UntypedTerm
  | UnifyFailedWithMessage of string * Type * Type * UntypedTerm
  | UnknownVar of qualified_name * Context<Type>
  | UnknownConst of qualified_name * UntypedTerm list * Context<Type>
  | NotMatchable of UntypedTerm * Type * UntypedTerm
  | TermWithMessage of Printf.StringFormat<string -> string> * UntypedTerm
  | NotRunnable of Type
  | NotInductive of Type

exception TyperFailed of FailureReason

// Constraint list -> Constraint list
let unify cs =
  let cstrmap f xs =
    xs |> List.map Constraint |> f |> List.map cstr_Extract
  in
  let rec u cs' = 
    match cs' with
      | (s, t, _) :: rest when (s = t) -> u rest
      | (s, TyVar tn, x) :: rest
      | (TyVar tn, s, x) :: rest when (s |> hasTyVar tn |> not) ->
        List.append (cs' |> cstrmap (substInConstraints tn s) |> u) [ (TyVar tn, s, x) ]
      | ((TyDataType (n, lts, lcts, _, _), TyDataTypeSelf (m, rts), _) :: _ & (dt, dts, t) :: rest) 
      | ((TyDataTypeSelf (m, rts), TyDataType (n, lts, lcts, _, _), _) :: _ & (dts, dt, t) :: rest) when (n = m && List.length lts = List.length rts) ->
        match (dt |> isInductive) with
          | Some true -> rest |> List.append (List.map2 (fun x y -> (x, y, t)) lts rts) |> u
          | Some false ->
            let (l, r) = prettify2 (dt, dts) in
            UnifyFailed (l, r, t) |> TyperFailed |> raise
          | None -> dt |> prettify1 |> NotInductive |> TyperFailed |> raise
      | (TyFun (a1, b1), TyFun (a2, b2), f) :: rest ->
        u ((a1, a2, f) :: (b1, b2, f) :: rest)
      | (TyDeferred a, TyDeferred b, d) :: rest ->
        u ((a, b, d) :: rest)
      | (TyDataType (lname, lts, _, _, lloc), TyDataType (rname, rts, _, _, rloc), t) :: rest
        when (lname = rname && List.length lts = List.length rts && lloc = rloc) ->
        rest |> List.append (List.map2 (fun x y -> (x, y, t)) lts rts) |> u
      | (TyScheme (svar, sb), TyScheme (tvar, tb), _) :: _ & (s, t, x) :: rest when fvOf s = fvOf t ->
        let fvs = fvOf s
        let uniqVar =
          let rec f uniq =
            let (v, uniq) = genUniq uniq
            if fvs |> Set.contains v then
              f uniq
            else
              TyVar v
          f 0
        let sb' = svar |> Seq.map (fun x -> (x, uniqVar)) |> Map.ofSeq |> Assign |> substAll <| sb 
        let tb' = tvar |> Seq.map (fun x -> (x, uniqVar)) |> Map.ofSeq |> Assign |> substAll <| tb
        if sb' = tb' then
          u rest
        else
          UnifyFailed (s, t, x) |> TyperFailed |> raise
      | (s, t, u) :: _ & (TyDataType (_, _, _, _, lloc), TyDataType (_, _, _, _, rloc), _) :: _ 
        when lloc.IsSome && rloc.IsSome ->
        let (s', t') = prettify2 (s, t) in
        let msg =
          sprintf "from different locations: '%s' and '%s'" (to_s lloc.Value) (to_s rloc.Value)
        UnifyFailedWithMessage (msg, removeForall s', removeForall t', u) |> TyperFailed |> raise
      | (s, t, u) :: rest ->
        let (s', t') = prettify2 (s, t) in
        UnifyFailed (removeForall s', removeForall t', u) |> TyperFailed |> raise
      | [] -> []
  in u (cs |> List.map cstr_Extract) |> List.map Constraint

// Context -> Type list -> UniqId -> Term -> (Term * Type * UniqId * Constraint list)
let rec recon ctx stack uniq term =
  let multiRecon uq terms =
    let folder (xs, ts, u, cs) x =
      let (x', t', u', cs') = recon ctx stack u x in
      (x' :: xs, t' :: ts, u', List.append cs' cs)
    in
    let (terms', types', uniq', cstrs') = terms |> List.fold folder ([], [], uq, []) in
    (terms' |> List.rev, types' |> List.rev, uniq', cstrs' |> List.rev)
  in
  match term with
    | UTmFreeVar vn ->
      match (ctx |> Context.findTerm vn) with
        | Some (TyScheme (vs, t)) ->
          let (t',uniq) = t |> rename uniq (vs |> Set.toList) id in
          (term, t', uniq, [])
        | Some t -> (term, t, uniq, [])
        | None -> 
          match (ctx |> Context.findConstructor vn None) with
            // constructor as a function
            | Some (TyDataType (name, targs, cts, p, info), ctargs) ->
              let tprms = targs |> List.choose (function | TyVar x -> Some x | _ -> None) in
              let ((targs', cts', ctargs'), uniq) = (targs, cts, ctargs) |> rename uniq tprms (fun f (x, y, z) -> (x |> List.map f, y |> List.map (argsmap f), z |> List.map f)) in
              let (argt, isone) = 
                if (ctargs' |> List.length = 1) then
                  (ctargs'.[0], true)
                else
                  (TyTuple ctargs', false)
              in
              let typ = (TyFun (argt, TyDataType (name, targs', cts', p, info))) in
              let con = ExternalFun (sprint_qualified vn) typ (function
                  | x :: _ when isone -> UTmConstruct (vn, [x])
                  | UTmConstruct (["*"], xs) :: _ -> UTmConstruct (vn, xs)
                  | _ -> failwith "impossible_recon_UVar_variantfun"
                )
              in
              (con, typ, uniq, [])
            | Some _
            | None -> UnknownVar (vn, ctx) |> TyperFailed |> raise
    
    | UTmBoundVar i ->
      if (List.length stack > i) then
        (UTmBoundVar i, stack |> List.item i, uniq, [])
      else
        failwith "impossible_UBoundVar"

    | UTmFun body ->
      let (u, uniq) = genUniq uniq in
      let (body', t, uniq, cstr) = recon ctx ((TyVar u) :: stack) uniq body in
      let (v, uniq) = genUniq uniq in
      (UTmFun body', TyVar v, uniq, cstr @ Constraint (TyVar v, TyFun (TyVar u, t), UTmFun body') :: [])

    | UTmConstruct (n, args) ->
      match (ctx |> Context.findConstructor n (Some args)) with
        | Some (TyDataType (name, vtargs, cts, p, info), _) ->
          let vtprms = vtargs |> List.choose (function | TyVar x -> Some x | _ -> None) in
          let ((vtargs', cts'), uniq) = (vtargs, cts) |> rename uniq vtprms (fun f (x, y) -> (x |> List.map f, y |> List.map (argsmap f))) in
          let ctargs =
            (cts' |> List.find (fun c -> c.name = List.last n)).args
          in
          let (args', targs, uniq, cstrs) = multiRecon uniq args in
          let vcstrs =
            targs
              |> List.map2 (fun x y -> (x, y)) ctargs
              |> List.map2 (fun x (y, z) -> Constraint (y, z, x)) args'
          in
          let (u, uniq) = genUniq uniq in
          (UTmConstruct (n, args'), TyVar u, uniq, vcstrs @ cstrs @ Constraint (TyVar u, TyDataType (name, vtargs', cts', p, info), UTmConstruct (n, args')) :: [])
        | _
        | None -> UnknownConst (n, args, ctx) |> TyperFailed |> raise
    
    | UTmTuple [x] ->
      recon ctx stack uniq x
    
    | UTmTuple xs ->
      let (xs', txs, uniq, cstrs) = multiRecon uniq xs in
      (UTmTuple xs', TyTuple txs, uniq, cstrs) 

    | UTmApply (l, rs) ->
      let (l', tl, uniq, cstr1) = recon ctx stack uniq l in
      let (rs', trs, uniq, cstr2) = multiRecon uniq rs in
      let (nv, uniq) = genUniq uniq in
      (UTmApply (l', rs'), TyVar nv, uniq, cstr2 @ cstr1 @ Constraint (tl, foldFun TyFun trs (TyVar nv), UTmApply (l', rs')) :: [])

    | UTmLiteral l -> 
      match l with
        | LNat _ -> (term, TyNat, uniq, [])
        | LBool _ -> (term, TyBool, uniq, [])
        | LUnit -> (term, TyUnit, uniq, [])
   
    | UTmLet (x, value, body) ->
      let (value', tvalue, uniq, cstr1) = recon ctx stack uniq value in
      let cstr1' = unify cstr1 in
      let tvalue' = tvalue |> substAll (cstr_toAsgn cstr1') in
      let fvs = 
        ctx |> Context.toTyperMap
            |> List.map (fun (_, t) -> fvOf t |> Set.toList)
            |> List.concat
      in
      let tvars = 
        tvalue' |> fvOf
                |> Set.toList
                |> List.filter (fun y -> fvs |> List.contains y |> not)
      in
      let tx = if (List.length tvars > 0) then TyScheme (tvars |> Set.ofList, tvalue') else tvalue' in
      let ctx' = ctx |> Context.addTerm x tx in
      let (body', tbody, uniq, cstr2) = recon ctx' stack uniq body in

      let tbody' = tbody |> substAll (cstr1 @ cstr2 |> unify |> cstr_toAsgn) in

      let (r, uniq) = genUniq uniq in
      (UTmLet (x, value', body'), TyVar r, uniq, cstr1 @ cstr2 @ Constraint (TyVar r, tbody, UTmLet (x, value', body')) :: [])
   
    | UTmLetDefer (x, value, body) ->
      let (nv, uniq) = genUniq uniq in
      let (value', tvalue, uniq, cstr) = recon ctx stack uniq value in
      let (mv, uniq) = genUniq uniq in
      let cstr' = cstr @ Constraint (TyDeferred (TyVar nv), tvalue, value') :: Constraint (TyVar mv, TyDeferred (TyVar nv), value') :: [] in
      let (lv, uniq) = genUniq uniq in
      let (body', tbody, uniq, cstr2) = recon (ctx |> Context.addTerm x (TyVar lv)) stack uniq body in
      let cstr2' = cstr2 @ cstr' in
      let (tvalue', timevalue) = (TyVar mv) |> substAll (cstr2' |> unify |> cstr_toAsgn) |> getTimeOfType  in
      UTmLet (x, value' |> times timevalue UTmRun, body) |> times timevalue UTmDefer |> recon ctx stack uniq

    | UTmDefer x ->
      let (nv, uniq) = genUniq uniq in
      let dt = TyDeferred (TyVar nv) in
      let (x', tx, uniq, cstr) = recon ctx stack uniq x in
      let (mv, uniq) = genUniq uniq in
      (UTmDefer x', TyVar mv, uniq, cstr @ Constraint (TyVar nv, tx, UTmDefer x') :: Constraint (TyVar mv, dt, UTmDefer x') :: [])
    
    | UTmRun x ->
      let (nv, uniq) = genUniq uniq in
      let dt = TyDeferred (TyVar nv) in
      let (x', tx, uniq, cstr) = x |> recon ctx stack uniq in
      let (mv, uniq) = genUniq uniq in
      (UTmRun x', TyVar mv, uniq, cstr @ Constraint (dt, tx, UTmRun x) :: Constraint (TyVar mv, TyVar nv, UTmRun x') :: [])

    | UTmExternal (_, t) ->
      (term, t, uniq, [])

    | UTmMatch (v, cases) ->
      let (v', tv, uniq, cstr) = recon ctx stack uniq v in
      let rec expandCases = function
        | UTmApply (UTmFreeVar ["::"], [l; r]) -> UTmConstruct (["Cons"], [expandCases l; expandCases r])
        | UTmLiteral (LNat 0u) -> UTmConstruct (["0"], [])
        | UTmTuple xs -> UTmTuple (xs |> List.map expandCases)
        | x -> x
      in
      let cases = cases |> List.map (fun (ptn, body) -> (expandCases ptn, body)) in
      let (a, uniq) = reconFromPatterns (UTmMatch (v, cases)) ctx uniq in
      if ((getTimeOfType tv |> snd) > 0) then
        TermWithMessage ("the term '%s' is not pure and cannot be matched.", v') |> TyperFailed |> raise
      let (bs', tbs, uniq, css) = 
        let f = 
          cases 
            |> List.map (fun (pat, body) ->
                if (isValidAsPattern pat |> not) then
                  TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
                else
                  match (ctx |> bindPattern pat a) with
                    | Some stack' -> 
                      (List.append stack' stack, body)
                    | None -> NotMatchable (pat, a, body) |> TyperFailed |> raise
              )
            |> List.foldBack (fun (st, b) (bs', tbs, u, css) ->
                let (b', tb, u', cs) = recon ctx st u b in
                (b' :: bs', tb :: tbs, u', List.append cs css)
              )
        in f ([], [], uniq, [])
      in
      let term' = UTmMatch (v', cases |> List.map2 (fun nb (pat, b) -> (pat, nb)) bs') in
      let (b, uniq) = genUniq uniq in
      let b = TyVar b in
      let bcstr =
        tbs |> List.map2 (fun x t -> Constraint (b, t, x)) bs'
      in
      let cstrs = cstr @ css @ bcstr @ Constraint (tv, a, v') :: [] in
      (term', b, uniq, cstrs)
    
    | UTmFixMatch cases ->
      let (uvs, uniq) = genUniqs uniq 3 in
      let (targ, targ', tret) =
        match uvs with
          | [a; b; c] -> (TyVar a, TyVar b, TyVar c)
          | _ -> failwith "impossible_UFixMatch"
      in
      let tthis = TyFun (targ, tret) in

      let ctx' = ctx |> Context.addTerm "x" targ' in
      let (mth, tmth, uniq, cstr1) = recon ctx' (tthis :: stack) uniq (UTmMatch (UTmFreeVar ["x"], cases)) in

      let (ret, uniq) = genUniq uniq in
      match mth with
        | UTmMatch (_, cases) ->
          verifyTermination cases |> ignore;
          (UTmFixMatch cases, TyVar ret, uniq, cstr1 @ Constraint (tthis, TyFun (targ', tmth), UTmFixMatch cases) :: Constraint (TyVar ret, TyFun (targ', tmth), UTmFixMatch cases) :: [])
        | _ ->
          failwith "impossible_UFixMatch"

and verifyTermination cases =
  let fvc p b = List.init (countFvOfPattern p) (fun _ -> b) in
  let rec verify dom codom t =
    let self = dom |> List.length in
    let res = 
      match t with
        | UTmApply (UTmBoundVar f, UTmBoundVar x :: _) when (f = self) ->
          codom |> List.tryItem x ?| false
        | UTmApply (UTmBoundVar f, _) when (f = self) -> false
        | UTmMatch (UTmBoundVar x, cs) when (dom |> List.tryItem x ?| false) ->
          cs |> List.forall (fun (pat, bdy) -> bdy |> verify (dom |> List.append (fvc pat true)) (codom |> List.append (fvc pat true)))
        | UTmMatch (x, cs) ->
          verify dom codom x && cs |> List.forall (fun (pat, bdy) -> bdy |> verify (dom |> List.append (fvc pat false)) (codom |> List.append (fvc pat false)))
        | UTmConstruct (_, xs) -> xs |> List.forall (verify dom codom)
        | UTmFun b ->
          b |> verify (false :: dom) (false :: codom)
        | UTmLet (x, l, r) 
        | UTmLetDefer (x, l, r) ->
          [l; r] |> List.forall (verify dom codom)
        | UTmApply (l, rs) -> l :: rs |> List.forall (verify dom codom)
        | UTmBoundVar x -> self <> x
        | UTmTuple xs -> xs |> List.forall (verify dom codom)
        | UTmFreeVar _
        | UTmLiteral _
        | UTmExternal _ -> true
        | UTmDefer x
        | UTmRun x ->
          verify dom codom x
        | UTmFixMatch cs ->
          cs |> List.forall (fun (pat, bdy) -> bdy |> verify ((false :: dom) |> List.append (fvc pat false)) ((false :: codom) |> List.append (fvc pat false)))
    in
    if res then
      res
    else
      TermWithMessage ("Recursion is not well-founded. Bad expression: '%s'", t) |> TyperFailed |> raise
  in cases |> List.forall (fun (ptn, bdy) ->
      match ptn with
        | UTmConstruct _ -> verify (fvc ptn true) (fvc ptn true) bdy
        | _ -> verify (fvc ptn true) [] bdy
    )

and reconFromPatterns mth ctx uniq =
  let pats =
    match mth with
      | (UTmMatch (_, x)) -> x
      | _ -> failwith "impossible_reconFromPatterns"
  in
  let (a, uniq) = genUniq uniq in
  let rec gh uq pat =
    match pat with
      | UTmConstruct (x, ys) ->
        let (name, targs, cts, ctargs, nq, info) =
          match (ctx |> Context.findConstructor x (Some ys)) with
            | Some (TyDataType (name, targs, cts, _, info), ctargs) ->
              let tprms = targs |> List.choose (function | TyVar x -> Some x | _ -> None) in
              let ((targs', cts', ctargs'), uniq) = 
                (targs, cts, ctargs) |> rename uq tprms (fun f (x, y, z) -> 
                    (
                      x |> List.map f,
                      y |> List.map (argsmap f),
                      z |> List.map f
                    )
                  )
              in
              (name, targs', cts', ctargs', uniq, info)
            | _
            | None -> UnknownVar (x, ctx) |> TyperFailed |> raise
        in
        let (fnq, pts) = ys |> List.fold (fun (u, ts) y -> let (nu, nt) = gh u y in (nu, nt :: ts)) (nq, []) in
        let asgn = 
          ctargs |> List.rev
                 |> List.map2 (fun y -> (function | TyVar x -> Some (x, y) | _ -> None)) pts 
                 |> List.choose id |> Map.ofList |> Assign 
        in
        let vt = TyDataType (name, targs, cts, ENull, info) |> substAll asgn in
        (fnq, vt)
      | UTmTuple xs ->
        let (nq, ts) = xs |> List.fold (fun (u, ts) x -> let (nu, nt) = gh u x in (nu, nt :: ts)) (uq, []) in
        (nq, TyTuple (ts |> List.rev))
      | UTmLiteral LUnit -> (uq, TyUnit)
      | UTmLiteral (LNat _) -> (uq, TyNat)
      | UTmLiteral (LBool _) -> (uq, TyBool)
      | UTmFreeVar ["_"]
      | UTmBoundVar _ ->
        let (tn, nq) = genUniq uq in
        (nq, TyVar tn)
      | _ -> TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
  in
  let (uniq, ts) = pats |> List.map fst |> List.fold (fun (u, ts) p -> let (nu, t) = gh u p in (nu, t :: ts)) (uniq, []) in
  let cstr =
    ts |> List.map (fun t -> Constraint (TyVar a, t, mth))
  in 
  let rt = TyVar a |> substAll (unify cstr |> cstr_toAsgn) in
  exhaustiveCheck (pats |> List.map fst) rt ctx;
  (rt, uniq)


and isValidAsPattern = function
  | UTmLiteral _
  | UTmConstruct (_, [])
  | UTmFreeVar _ 
  | UTmBoundVar _ -> true
  | UTmConstruct (_, xs)
  | UTmTuple xs -> xs |> List.forall isValidAsPattern
  | _ -> false

and bindPattern pat t ctx =
  let rec bt pat t =
    match (pat, t) with
      | (UTmConstruct (n, xs), TyDataTypeSelf (name, ts)) ->
        match (ctx |> Context.findType name) with
          | Some (TyDataType (name, vts, cts, p, info)) ->
            let asgn = vts |> List.map2 (fun x -> function | TyVar y -> (y, x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList |> Assign in
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            bt (UTmConstruct (n, xs)) (TyDataType (name, ts, cts', p, info))
          | _ -> failwith "impossible_bindPattern"
      | (UTmConstruct (n, xs), TyDataType (_, _, cts, _, _)) when (cts |> List.exists (fun c -> c.name = List.last n && List.length xs = List.length (c.args))) ->
        let ts = (cts |> List.find (fun c -> c.name = List.last n)).args in
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UTmTuple xs, TyDataType(["*"], ts, _, _, _)) when (List.length xs = List.length ts) ->
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UTmFreeVar ["_"], _)
      | (UTmLiteral LUnit, TyUnit)
      | (UTmLiteral (LNat _), TyDataType (["Nat"], _, _, _, _))
      | (UTmLiteral (LBool _), TyBool) -> []
      | (UTmBoundVar x, t) -> [ (x, t) ]
      | _ -> failwith "bindfailed"
  in
  try
    bt pat t |> List.map snd |> Some
  with
    | _ -> None


and getInductionDepth ptns ctx =
  let (<+>) (x, i) ys =
    match (ys |> Map.tryFind x) with
      | Some i' -> ys |> Map.add x (i + i')
      | None -> ys |> Map.add x i
  in
  let concat ms =
    ms |> List.fold (fun mp xs -> xs |> Map.toList |> List.fold (fun m x -> x <+> m) mp) Map.empty
  in
  let rec gett = function
    | UTmConstruct (x, ys) ->
      match (ctx |> Context.findConstructor x (Some ys)) with
        | Some (TyDataType (name, _, _, _, _), _) -> (name, 1) <+> (ys |> List.map gett |> concat)
        | _ -> Map.empty
    | UTmFreeVar ["_"]
    | UTmBoundVar _ -> Map.empty
    | UTmTuple xs ->
      xs |> List.map gett |> concat
    | _ -> Map.empty
  in ptns |> List.map gett |> concat

and exhaustiveCheck ptns t ctx =
  let dmp = getInductionDepth ptns ctx in
  let rec cartProd lol =
    let f n = function
      | [] -> [[n]]
      | xss -> xss |> List.map (fun xs -> n :: xs)
    in
    match lol with
      | [] -> []
      | h :: t -> h |> List.collect (fun n -> f n (cartProd t))
  in
  let next name mp =
    match (mp |> Map.tryFind name) with
      | Some 0
      | Some 1 -> mp |> Map.remove name
      | Some i -> mp |> Map.add name (i - 1)
      | None -> mp
  in
  let rec genReq mp = function
    | TyDataType (["*"], ts, _, _, _) ->
      ts |> List.map (genReq mp) |> cartProd |> List.map UTmTuple
    | TyDataType (vname, _, cts, _, _) ->
      let ns = namespaceof vname
      cts |> List.map (fun c ->
              c.args |> List.map (genReq (mp |> next vname))
                     |> cartProd
                     |> (function 
                          | [] -> [ UTmConstruct (ns @ [c.name], []) ]
                          | x -> x |> List.map (fun xs -> UTmConstruct (ns @ [c.name], xs))
                        )
             ) 
          |> List.concat
    | TyUnit -> [ UTmLiteral LUnit ]
    | TyBool -> [ UTmLiteral (LBool true); UTmLiteral (LBool false)]
    | TyDataTypeSelf (name, ts) ->
      match (ctx |> Context.findType name) with
        | Some (TyDataType (name, vts, cts, p, info)) ->
          if (mp |> Map.containsKey name) then
            let asgn = vts |> List.map2 (fun x -> function | TyVar y -> (y, x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList |> Assign in
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            genReq mp (TyDataType (name, vts, cts', p, info))
          else
            [ UTmFreeVar ["_"] ]
        | _ -> failwith "impossible_exhaustivenessCheck"
    | TyVar _ -> [ UTmFreeVar ["_"] ] // only matched with variable patterns
    | _ -> []
  in
  let possiblePatterns = genReq dmp t in
  let unmatched =
    ptns |> List.fold (fun xs ptn ->
        let xs' = xs |> List.filter (matchPattern ptn >> Option.isNone) in
        xs'
      ) possiblePatterns
  in
  if (List.length unmatched > 0) then
    TermWithMessage ("The pattern match is not exhaustive.\nFor example, the value '%s' will fail.", unmatched |> List.head) |> TyperFailed |> raise
  else
    ()
  
let solve t cstr =
  let cstr' = unify cstr in
  t |> substAll (cstr_toAsgn cstr')

let inferWithContext ctx term =
  let (term', t, _, cstr) = recon ctx [] 0 term in
  (term', solve t cstr |> prettify1)

let inferWithAnnotation ctx term typ =
  let (term', t, _, cstr) = recon ctx [] 0 term in
  (term', solve t (Constraint (t, typ, term') :: cstr) |> prettify1)

let infer term =
  inferWithContext [] term


let printTypeError = function
  | UnifyFailed (a, b, ut) ->
    printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
  | UnifyFailedWithMessage (msg, a, b, ut) ->
    printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n              %s\n------------> %s" (to_s a) (to_s b) msg (to_s ut)
  | UnknownVar (n, ctx) ->
    printfn "TYPER FAILED: '%s' is not defined (unknown variable)" (sprint_qualified n)
  | UnknownConst (n, ts, ctx) ->
    let ac = ts |> List.length in
    printfn "TYPER FAILED: a constructor '%s' that has %i arguments does not exist." (sprint_qualified n) ac
  | NotMatchable (l, t, r) ->
    printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r)
  | NotRunnable t ->
    printfn "TYPER FAILED: '%s' is not runnable" (to_s t)
  | TermWithMessage (f, t) ->
    sprintf f (to_s t) |> printfn "TYPER FAILED: %s"
  | NotInductive t ->
    printfn "TYPER FAILED: '%s' is not inductive" (to_s t)

()
