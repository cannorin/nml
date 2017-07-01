module nml.Typer

open nml.Ast
open nml.Evaluation
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections

type Constraint = | Constraint of Type * Type * UntypedTerm
let cstr_Extract = function
  | Constraint (s, t, u) -> (s, t, u)

type Assign = | Assign of Map<string, Type>
let asgn_Extract = function
  | Assign x -> x

let cstr_toAsgn cstr =
  match cstr with
    | xs -> xs |> List.choose (function | Constraint (TypeVar name, t, _) -> Some (name, t) | _ -> None ) |> Map.ofList |> Assign


let rec getTyVars = function
  | TypeVar n -> set [n]
  | Fun (a, b) -> Set.union (getTyVars a) (getTyVars b)
  | Deferred t -> getTyVars t
  | Variant (_, ts, _)
  | TypeOp (_, ts, _) -> ts |> List.map getTyVars |> List.fold Set.union (set [])
  | Scheme (vs, t) -> getTyVars t |> Set.union vs
  | _ -> set []

let hasTyVar vname t =
  fvOf t |> Set.contains vname

let rec delayTypeBy i ty =
  if (i > 0) then
    Deferred ty |> delayTypeBy (i - 1)
  else
    ty

// tx |> substIn "x" t
// --> t [x <- tx]
let substIn vname tsbj tvl =
  let rec sub = function
    | Fun (a, b) -> Fun (sub a, sub b)
    | TypeVar nm when (nm = vname) -> tvl
    | Deferred t -> Deferred (sub t)
    | TypeOp (n, ts, p) -> TypeOp (n, ts |> List.map sub, p)
    | Variant (n, ts, cts) -> Variant (n, ts |> List.map sub, cts |> List.map (fun (n, targs) ->  (n, targs |> List.map sub)))
    | Scheme (tvs, t) -> Scheme (tvs, sub t)
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

type FailureReason =
  | UnifyFailed of Type * Type * UntypedTerm
  | UnknownVar of string * Context
  | UnknownConst of string * UntypedTerm list * Context
  | NotMatchable of UntypedTerm * Type * UntypedTerm
  | TermWithMessage of Printf.StringFormat<string -> string> * UntypedTerm
  | NotRunnable of Type

exception TyperFailed of FailureReason

// Constraint list -> Constraint list
let unify cs =
  let cstrmap f xs =
    xs |> List.map Constraint |> f |> List.map cstr_Extract
  in
  let rec u cs' = 
    match cs' with
      | (s, t, _) :: rest when (s = t) -> u rest
      | (s, TypeVar tn, x) :: rest
      | (TypeVar tn, s, x) :: rest when (s |> hasTyVar tn |> not) ->
        List.append (cs' |> cstrmap (substInConstraints tn s) |> u) [ (TypeVar tn, s, x) ]
      | (Fun (a1, b1), Fun (a2, b2), f) :: rest ->
        u ((a1, a2, f) :: (b1, b2, f) :: rest)
      | (Deferred a, Deferred b, d) :: rest ->
        u ((a, b, d) :: rest)
      | (Variant (lname, lts, _), Variant (rname, rts, _), t) :: rest
      | (TypeOp (lname, lts, _), TypeOp (rname, rts, _), t) :: rest when (lname = rname && List.length lts = List.length rts) ->
        rest |> List.append (List.map2 (fun x y -> (x, y, t)) lts rts) |> u
      | (s, t, u) :: rest ->
        UnifyFailed (s, t, u) |> TyperFailed |> raise
      | [] -> []
  in u (cs |> List.map cstr_Extract) |> List.map Constraint

let rec genUniqs uniq i =
  if i > 0 then
    let (x, nu) = genUniq uniq in
    let (rest, fu) = genUniqs nu (i - 1) in
    (x :: rest, fu)
  else
    ([], uniq)

let rename u vs f t =
  let (nvs, u') = vs |> List.length |> genUniqs u in
  let qvs = vs |> List.map ((+) "_rename") in
  let genasgn xs ys =
    List.map2 (fun x y -> (x, TypeVar y)) xs ys |> Map.ofList |> Assign
  in
  (t |> f (substAll (genasgn vs qvs)) |> f (substAll (genasgn qvs nvs)), u')


// Context -> UniqId -> (Type * UniqId * Constraint list)
let rec recon ctx uniq term =
  let multiRecon uq terms =
    let folder (xs, ts, u, cs) x =
      let (x', t', u', cs') = recon ctx u x in
      (x' :: xs, t' :: ts, u', List.append cs' cs)
    in
    let (terms', types', uniq', cstrs') = terms |> List.fold folder ([], [], uq, []) in
    (terms' |> List.rev, types' |> List.rev, uniq', cstrs' |> List.rev)
  in
  match term with
    | UVar vn ->
      match (ctx |> typerFind vn) with
        | Some (Scheme (vs, t)) ->
          let (t', newUniq) = t |> rename uniq (vs |> Set.toList) id in
          (term, t', newUniq, [])
        | Some t -> (term, t, uniq, [])
        | None -> 
          match (ctx |> findVariant vn None) with
            // arg-less constructor as a value
            | Some (Variant (name, targs, cts), []) ->
              let tprms = targs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
              let ((targs', cts'), newUniq) = (targs, cts) |> rename uniq tprms (fun f (x, y) -> (x |> List.map f, y |> List.map (fun (n, t) -> (n, t |> List.map f)))) in
              (UConstruct (vn, []), Variant (name, targs', cts'), newUniq, [])
            // constructor as a function
            | Some (Variant (name, targs, cts), ctargs) ->
              let tprms = targs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
              let ((targs', cts', ctargs'), newUniq) = (targs, cts, ctargs) |> rename uniq tprms (fun f (x, y, z) -> (x |> List.map f, y |> List.map (fun (n, t) -> (n, t |> List.map f)), z |> List.map f)) in
              let (argt, isone) = 
                if (ctargs' |> List.length = 1) then
                  (ctargs'.[0], true)
                else
                  (TTuple ctargs', false)
              in
              let typ = (Fun (argt, Variant (name, targs', cts'))) in
              let con = ExternalFun vn typ (function
                  | x :: _ when isone -> UConstruct (vn, [x])
                  | UTuple xs :: _ -> UConstruct (vn, xs)
                  | _ -> failwith "impossible_recon_UVar_variantfun"
                )
              in
              (con, typ, uniq, [])
            | Some _
            | None -> UnknownVar (vn, ctx) |> TyperFailed |> raise
    
    | UFun (an, body) ->
      let (u, newUniq) = genUniq uniq in
      let ctx' = ctx |> typerAdd an (TypeVar u) in
      let (body', t, newUniq', cstr) = recon ctx' newUniq body in
      (UFun (an, body'), Fun (TypeVar u, t), newUniq', cstr)
    
    | UFunUnit x ->
      let (x', tx, newUniq, cstr) = recon ctx uniq x in
      (UFunUnit x', Fun(Unit, tx), newUniq, cstr)

    // immediate constructor handling
    | UApply (UVar n, UTuple args) when (ctx |> findVariant n (Some args) |> Option.isSome) ->
      UConstruct (n, args) |> recon ctx uniq

    // immediate constructor handling
    | UApply (UVar n, x) when (ctx |> findVariant n (Some [x]) |> Option.isSome) ->
      UConstruct (n, [x]) |> recon ctx uniq
    
    | UConstruct (n, args) ->
      match (ctx |> findVariant n (Some args)) with
        | Some (Variant (name, vtargs, cts), _) ->
          let vtprms = vtargs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
          let ((vtargs', cts'), newUniq) = (vtargs, cts) |> rename uniq vtprms (fun f (x, y) -> (x |> List.map f, y |> List.map (fun (n, t) -> (n, t |> List.map f)))) in
          let ctargs =
            cts' |> List.find (fun (nm, _) -> nm = n) |> snd
          in
          let (args', targs, newUniq2, cstrs) = multiRecon newUniq args in
          let vcstrs =
            targs
              |> List.map2 (fun x y -> (x, y)) ctargs
              |> List.map2 (fun x (y, z) -> Constraint (y, z, x)) args'
          in
          let tvar = Variant (name, vtargs', cts') |> substAll (cstr_toAsgn vcstrs) in
          let vcstrs' = vcstrs |> List.filter (function | Constraint (TypeVar x, _, _) -> ctargs |> List.contains (TypeVar x) |> not | _ -> true) in
          (UConstruct (n, args'), tvar, newUniq2, List.concat [ vcstrs'; cstrs ])
        | _
        | None -> UnknownConst (n, args, ctx) |> TyperFailed |> raise

    | UOp2 (l, op, r) ->
      UApply (UApply (UVar op, l), r) |> recon ctx uniq

    | UApply (l, r) ->
      let (l', tl, newUniq1, cstr1) = recon ctx uniq l in
      let (r', tr, newUniq2, cstr2) = recon ctx newUniq1 r in
      let (nv, newUniq3) = genUniq newUniq2 in
      (UApply (l', r'), TypeVar nv, newUniq3, List.concat [ cstr2; cstr1; [ Constraint (tl, Fun (tr, TypeVar nv), UApply (l', r')) ] ])
    
    | UIf (b, t, e) ->
      let (b', tb, nu1, cs1) = recon ctx uniq b in
      let (t', tt, nu2, cs2) = recon ctx nu1 t in
      let (e', te, nu3, cs3) = recon ctx nu2 e in
      (UIf (b', t', e'), te, nu3, List.concat [ [ Constraint (tb, Bool, b); Constraint (tt, te, UIf (b, t, e)); ]; cs3; cs2; cs1 ]);
    
    | UTuple [x] ->
      recon ctx uniq x
    
    | UTuple xs ->
      let (xs', txs, newUniq, cstrs) = multiRecon uniq xs in
      (UTuple xs', TTuple txs, newUniq, cstrs) 
    
    | ULiteral l -> 
      match l with
        | LNat _ -> (term, Nat, uniq, [])
        | LBool _ -> (term, Bool, uniq, [])
        | LUnit -> (term, Unit, uniq, [])
   
    | ULet (x, value, body) ->
      let (value', tvalue, newUniq, cstr1) = recon ctx uniq value in
      let cstr1' = unify cstr1 in
      let tvalue' = tvalue |> substAll (cstr_toAsgn cstr1') in
      let fvs = 
        ctx |> toTyperMap
            |> List.map (fun (_, t) -> fvOf t |> Set.toList)
            |> List.concat
      in
      let tvars = 
        tvalue' |> fvOf
                |> Set.toList
                |> List.filter (fun y -> fvs |> List.contains y |> not)
      in
      let ctx' = ctx |> typerAdd x (Scheme (tvars |> Set.ofList, tvalue')) in
      let (body', tbody, newUniq2, cstr2) = recon ctx' newUniq body in
      (ULet (x, value', body'), tbody, newUniq2, cstr2)
    
    | UDefer x ->
      let (x', tx, newUniq, cstr) = recon ctx uniq x in
      (UDefer x', Deferred tx, newUniq, cstr)
   
    | ULetDefer (x, value, body) ->
      let (value', tvalue, newUniq, cstr1) = recon ctx uniq value in
      let cstr1' = unify cstr1 in
      let (tvalue', timevalue) = tvalue |> substAll (cstr_toAsgn cstr1') |> getTimeOfType in
      let fvs = 
        ctx |> toTyperMap
            |> List.map (fun (_, t) -> fvOf t |> Set.toList)
            |> List.concat
      in
      let tvars = 
        tvalue' |> fvOf
                |> Set.toList
                |> List.filter (fun y -> fvs |> List.contains y |> not)
      in
      let ctx' = ctx |> typerAdd x (Scheme (tvars |> Set.ofList, tvalue')) in
      let (body', tbody, newUniq2, cstr2) = recon ctx' newUniq body in
      (ULetDefer (x, value', body'), tbody |> delayTypeBy timevalue, newUniq2, cstr2)
    
    | UExternal (_, t) ->
      (term, t, uniq, [])

    | UMatch (v, cases) ->
      let (v', tv, newUniq, cstr) = recon ctx uniq v in
      let (a, newUniq) = reconFromPatterns (UMatch (v, cases)) ctx uniq in
      if ((getTimeOfType tv |> snd) > 0) then
        TermWithMessage ("the term '%s' is not pure and cannot be matched.", v') |> TyperFailed |> raise
      let (bs', tbs, u', css) = 
        let f = 
          cases 
            |> List.map (fun (pat, body) ->
                if (isValidAsPattern ctx pat |> not) then
                  TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
                else
                  match (bindPattern pat a) with
                    | Some ctx' -> (List.append ctx' ctx, body)
                    | None -> NotMatchable (pat, a, body) |> TyperFailed |> raise
              )
            |> List.foldBack (fun (cx, b) (bs', tbs, u, css) ->
                let (b', tb, u', cs) = recon cx u b in
                (b' :: bs', tb :: tbs, u', List.append cs css)
              )
        in f ([], [], newUniq, [])
      in
      let term' = UMatch (v', cases |> List.map2 (fun nb (pat, b) -> (pat, nb)) bs') in
      let (b, u') = genUniq u' in
      let b = TypeVar b in
      let bcstr =
        tbs |> List.map (fun t -> Constraint (b, t, term'))
      in
      (term', b, u', List.concat [ [ Constraint (tv, a, v') ]; css; cstr; bcstr ])

    | URun x ->
      let (x', tx, newUniq, cstr) = recon ctx uniq x in
      let (tx', ttime) = getTimeOfType tx in
      if (ttime > 0) then
        (URun x', tx' |> delayTypeBy (ttime - 1), newUniq, cstr)
      else
        NotRunnable tx |> TyperFailed |> raise

and reconFromPatterns mth ctx uniq =
  let pats =
    match mth with
      | (UMatch (_, x)) -> x
      | _ -> failwith "impossible_reconFromPatterns"
  in
  let (a, uniq) = genUniq uniq in
  let rec gh uq pat =
    match pat with
      | (UVar x) when (ctx |> findVariant x None |> Option.isSome) ->
        gh uq (UApply (UVar x, UTuple []))
      | (UApply (UVar x, UTuple ys)) when (ctx |> findVariant x (Some ys) |> Option.isSome) ->
        let (name, targs, cts, ctargs, nq) =
          match (ctx |> findVariant x (Some ys)) with
            | Some (Variant (name, targs, cts), ctargs) ->
              let tprms = targs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
              let ((targs', cts', ctargs'), newUniq) = 
                (targs, cts, ctargs) |> rename uq tprms (fun f (x, y, z) -> 
                    (
                      x |> List.map f,
                      y |> List.map (fun (n, t) -> (n, t |> List.map f)),
                      z |> List.map f
                    )
                  )
              in
              (name, targs', cts', ctargs', newUniq)
            | _
            | None -> UnknownVar (x, ctx) |> TyperFailed |> raise
        in
        let (fnq, pts) = ys |> List.fold (fun (u, ts) y -> let (nu, nt) = gh u y in (nu, nt :: ts)) (nq, []) in
        let asgn = 
          ctargs |> List.rev
                 |> List.map2 (fun y -> (function | TypeVar x -> Some (x, y) | _ -> None)) pts 
                 |> List.choose id |> Map.ofList |> Assign 
        in
        let vt = Variant (name, targs, cts) |> substAll asgn in
        (fnq, vt)
      | (UApply (UVar x, y)) -> gh uq (UApply (UVar x, UTuple [y]))
      | UTuple xs ->
        let (nq, ts) = xs |> List.fold (fun (u, ts) x -> let (nu, nt) = gh u x in (nu, nt :: ts)) (uq, []) in
        (nq, TTuple (ts |> List.rev))
      | ULiteral LUnit -> (uq, Unit)
      | ULiteral (LNat _) -> (uq, Nat)
      | ULiteral (LBool _) -> (uq, Bool)
      | UVar x ->
        let (tn, nq) = genUniq uq in
        (nq, TypeVar tn)
      | _ -> TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
  in
  let (newUniq, ts) = pats |> List.map fst |> List.fold (fun (u, ts) p -> let (nu, t) = gh u p in (nu, t :: ts)) (uniq, []) in
  let cstr =
    ts |> List.map (fun t -> Constraint (TypeVar a, t, mth))
  in 
  let rt = TypeVar a |> substAll (unify cstr |> cstr_toAsgn) in
  exhaustiveCheck (pats |> List.map fst) rt;
  (rt, newUniq)

and isValidAsPattern ctx = function
  | ULiteral _
  | UVar _ -> true
  | UConstruct (_, xs)
  | UTuple xs -> xs |> List.forall (isValidAsPattern ctx)
  | UApply (UVar x, _) -> ctx |> findVariant x None |> Option.isSome
  | _ -> false

and bindPattern pat t =
  let rec bt pat t =
    match (pat, t) with
      | (UApply (UVar n, UTuple xs), Variant (_, _, cts))
      | (UConstruct (n, xs), Variant (_, _, cts)) when (cts |> List.exists (fun (m, ts) -> m = n && List.length xs = List.length ts)) ->
        let ts = cts |> List.find (fst >> ((=) n)) |> snd in
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UVar n, Variant (_, _, cts)) when (cts |> List.exists (fst >> ((=) n))) -> []
      | (UApply (UVar n, x), Variant (_, _, _)) ->
        bt (UApply (UVar n, UTuple [x])) t
      | (UTuple xs, TypeOp("*", ts, _)) when (List.length xs = List.length ts) ->
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UVar "_", _)
      | (ULiteral LUnit, Unit)
      | (ULiteral (LBool _), Bool)
      | (ULiteral (LNat _), Nat) -> []
      | (UVar x, t) -> [ TermContext (x, t, UVar x) ]
      | _ -> failwith "bindfailed"
  in
  try
    bt pat t |> Some
  with
    | _ -> None

and exhaustiveCheck ptns t =
  let rec cartProd lol =
    let f n = function
      | [] -> [[n]]
      | xss -> xss |> List.map (fun xs -> n :: xs)
    in
    match lol with
      | [] -> []
      | h :: t -> h |> List.collect (fun n -> f n (cartProd t))
  in
  let rec genReq = function
    | Variant (_, _, cts) ->
      cts |> List.map (fun (name, args) ->
              args |> List.map genReq 
                   |> cartProd
                   |> (function 
                        | [] -> [ UConstruct (name, []) ]
                        | x -> x |> List.map (fun xs -> UConstruct (name, xs))
                      )
             ) 
          |> List.concat
    | TypeOp("*", ts, _) ->
      ts |> List.map genReq |> cartProd |> List.map UTuple
    | Unit -> [ ULiteral LUnit ]
    | Nat -> [ UVar "{random Nat value}" ] // only matched with variable patterns
    | Bool -> [ ULiteral (LBool true); ULiteral (LBool false)]
    | TypeVar _ -> [ UVar "_" ] // only matched with variable patterns
    | _ -> failwith "impossible_exhaustivenessCheck"
  in
  let possiblePatterns = genReq t in
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

let pretify uniq t =
  let fv = getTyVars t in
  let t =
    if (Set.count fv > 0) then
      Scheme (fv, t)
    else
      t
  in
  let rec rename m = function
    | Scheme (vs, t) ->
      Scheme (vs |> Set.map (fun x -> m |> Map.tryFind x ?| x), rename m t) 
    | x -> x |> substAll (m |> Map.map (fun _ v -> TypeVar v) |> Assign)
  let ftmap = fv |> Set.map (fun x -> (x, x + "+")) |> Set.toList |> Map.ofList in
  let t' = t |> rename ftmap in
  let (us, newUniq) = fv |> Set.count |> genUniqs uniq in
  let newmap = fv |> Set.toList |> List.map2 (fun y x -> (x + "+", y)) us |> Map.ofList in
  (t' |> rename newmap, newUniq)
  
let solve t cstr =
  let cstr' = unify cstr in
  t |> substAll (cstr_toAsgn cstr')

let inferWithContext ctx term =
  let (term', t, _, cstr) = recon ctx 0 term in
  (term', solve t cstr |> pretify 0 |> fst)

let infer term =
  inferWithContext [] term

()
