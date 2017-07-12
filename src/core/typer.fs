module nml.Typer

open nml.Ast
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections


let inline (<+>) l r = List.append l r

type Constraint = | Constraint of Type * Type * UntypedTerm
let cstr_Extract = function
  | Constraint (s, t, u) -> (s, t, u)

type Assign = | Assign of Map<string, Type>
let asgn_Extract = function
  | Assign x -> x

let cstr_toAsgn cstr =
  match cstr with
    | xs -> xs |> List.choose (function | Constraint (TypeVar name, t, _) -> Some (name, t) | _ -> None ) |> Map.ofList |> Assign


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
      | (s, TypeVar tn, x) :: rest
      | (TypeVar tn, s, x) :: rest when (s |> hasTyVar tn |> not) ->
        List.append (cs' |> cstrmap (substInConstraints tn s) |> u) [ (TypeVar tn, s, x) ]
      | (Variant (n, lts, lcts), TypeOp (m, rts, _), t) :: rest
      | (TypeOp (m, rts, _), Variant (n, lts, lcts), t) :: rest when (n = m && List.length lts = List.length rts) ->
        match (Variant (n, lts, lcts) |> isInductive) with
          | Some true -> rest |> List.append (List.map2 (fun x y -> (x, y, t)) lts rts) |> u
          | Some false -> UnifyFailed (Variant (n, lts, lcts), TypeOp (m, rts, Value None), t) |> TyperFailed |> raise
          | None -> Variant (n, lts, lcts) |> NotInductive |> TyperFailed |> raise
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
      match (ctx |> typerFind vn) with
        | Some (Scheme (vs, t)) ->
          let (t', newUniq) = t |> rename uniq (vs |> Set.toList) id in
          (term, t', newUniq, [])
        | Some t -> (term, t, uniq, [])
        | None -> 
          match (ctx |> findConstructor vn None) with
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
                  | x :: _ when isone -> UTmConstruct (vn, [x])
                  | UTmConstruct ("*", xs) :: _ -> UTmConstruct (vn, xs)
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
      let (u, newUniq) = genUniq uniq in
      let (body', t, newUniq', cstr) = recon ctx ((TypeVar u) :: stack) newUniq body in
      (UTmFun body', Fun (TypeVar u, t), newUniq', cstr)

    | UTmConstruct (n, args) ->
      match (ctx |> findConstructor n (Some args)) with
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
          let (u, newUniq3) = genUniq newUniq2 in
          (UTmConstruct (n, args'), TypeVar u, newUniq3, List.concat [ vcstrs; cstrs; [ Constraint (TypeVar u, Variant (name, vtargs', cts'), UTmConstruct (n, args')) ]; ])
        | _
        | None -> UnknownConst (n, args, ctx) |> TyperFailed |> raise
    
    | UTmTuple [x] ->
      recon ctx stack uniq x
    
    | UTmTuple xs ->
      let (xs', txs, newUniq, cstrs) = multiRecon uniq xs in
      (UTmTuple xs', TTuple txs, newUniq, cstrs) 

    | UTmApply (l, rs) ->
      let (l', tl, uniq, cstr1) = recon ctx stack uniq l in
      let (rs', trs, uniq, cstr2) = multiRecon uniq rs in
      let (nv, uniq) = genUniq uniq in
      (UTmApply (l', rs'), TypeVar nv, uniq, cstr2 <+> cstr1 <+> [ Constraint (tl, foldFun trs (TypeVar nv), UTmApply (l', rs')) ])

    | UTmLiteral l -> 
      match l with
        | LNat _ -> (term, Nat, uniq, [])
        | LBool _ -> (term, Bool, uniq, [])
        | LUnit -> (term, Unit, uniq, [])
   
    | UTmLet (x, value, body) ->
      let (value', tvalue, newUniq, cstr1) = recon ctx stack uniq value in
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
      let (body', tbody, newUniq2, cstr2) = recon ctx' stack newUniq body in
      (UTmLet (x, value', body'), tbody, newUniq2, cstr2)
   
    | UTmLetDefer (x, value, body) ->
      let (nv, uniq) = genUniq uniq in
      let (value', tvalue, uniq, cstr) = recon ctx stack uniq value in
      let (mv, uniq) = genUniq uniq in
      let cstr' = cstr <+> Constraint (Deferred (TypeVar nv), tvalue, value') :: Constraint (TypeVar mv, Deferred (TypeVar nv), value') :: [] in
      let (lv, uniq) = genUniq uniq in
      let (body', tbody, uniq, cstr2) = recon (ctx |> typerAdd x (TypeVar lv)) stack uniq body in
      let cstr2' = cstr2 <+> cstr' in
      let (tvalue', timevalue) = (TypeVar mv) |> substAll (cstr2' |> unify |> cstr_toAsgn) |> getTimeOfType  in
      UTmLet (x, value' |> times timevalue UTmRun, body) |> times timevalue UTmDefer |> recon ctx stack uniq

    | UTmDefer x ->
      let (nv, uniq) = genUniq uniq in
      let dt = Deferred (TypeVar nv) in
      let (x', tx, uniq, cstr) = recon ctx stack uniq x in
      let (mv, uniq) = genUniq uniq in
      (UTmDefer x', TypeVar mv, uniq, cstr <+> Constraint (TypeVar nv, tx, UTmDefer x') :: Constraint (TypeVar mv, dt, UTmDefer x') :: [])
    
    | UTmRun x ->
      let (nv, uniq) = genUniq uniq in
      let dt = Deferred (TypeVar nv) in
      let (x', tx, uniq, cstr) = x |> recon ctx stack uniq in
      let (mv, uniq) = genUniq uniq in
      (UTmRun x', TypeVar mv, uniq, cstr <+> Constraint (dt, tx, UTmRun x) :: Constraint (TypeVar mv, TypeVar nv, UTmRun x') :: [])

    | UTmExternal (_, t) ->
      (term, t, uniq, [])

    | UTmMatch (v, cases) ->
      let (v', tv, newUniq, cstr) = recon ctx stack uniq v in
      let rec expandCases = function
        | UTmApply (UTmFreeVar "::", [l; r]) -> UTmConstruct ("Cons", [expandCases l; expandCases r])
        | UTmLiteral (LNat 0u) -> UTmConstruct ("0", [])
        | UTmTuple xs -> UTmTuple (xs |> List.map expandCases)
        | x -> x
      in
      let cases = cases |> List.map (fun (ptn, body) -> (expandCases ptn, body)) in
      let (a, newUniq) = reconFromPatterns (UTmMatch (v, cases)) ctx newUniq in
      if ((getTimeOfType tv |> snd) > 0) then
        TermWithMessage ("the term '%s' is not pure and cannot be matched.", v') |> TyperFailed |> raise
      let (bs', tbs, u', css) = 
        let f = 
          cases 
            |> List.map (fun (pat, body) ->
                if (isValidAsPattern pat |> not) then
                  TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
                else
                  match (ctx |> bindPattern pat a) with
                    | Some ctx' -> 
                      (List.append ctx' ctx, body)
                    | None -> NotMatchable (pat, a, body) |> TyperFailed |> raise
              )
            |> List.foldBack (fun (cx, b) (bs', tbs, u, css) ->
                let (b', tb, u', cs) = recon cx stack u b in
                (b' :: bs', tb :: tbs, u', List.append cs css)
              )
        in f ([], [], newUniq, [])
      in
      let term' = UTmMatch (v', cases |> List.map2 (fun nb (pat, b) -> (pat, nb)) bs') in
      let (b, u') = genUniq u' in
      let b = TypeVar b in
      let bcstr =
        tbs |> List.map (fun t -> Constraint (b, t, term'))
      in
      let cstrs = List.concat [ [ Constraint (tv, a, v') ]; css; cstr; bcstr ] in
      (term', b, u', cstrs)
    
    | UTmFixMatch (self, cases) ->
      let (uvs, uniq) = genUniqs uniq 2 in
      let (targ, tret) =
        match uvs with
          | [a; b] -> (TypeVar a, TypeVar b)
          | _ -> failwith "impossible_UFixMatch"
      in
      let tthis = Fun (targ, tret) in

      let ctx' = ctx |> typerAdd self tthis 
                     |> typerAdd "x" targ
      in
      let (mth, tmth, uniq, cstr1) = recon ctx' stack uniq (UTmMatch (UTmFreeVar "x", cases)) in
      match mth with
        | UTmMatch (_, cases) ->
          verifyTermination self cases |> ignore;
          (UTmFixMatch (self, cases), Fun (targ, tret), uniq, Constraint (tret, tmth, UTmFixMatch (self, cases)) :: cstr1)
        | _ ->
          failwith "impossible_UFixMatch"

and verifyTermination self cases =
  let rec verify dom codom t =
    let res = 
      match t with
        | UTmApply (UTmFreeVar f, UTmFreeVar x :: _) when (f = self) ->
          codom |> Set.contains x
        | UTmApply (UTmFreeVar f, _) when (f = self) -> false
        | UTmMatch (UTmFreeVar x, cs) when (dom |> Set.contains x) ->
          cs |> List.forall (fun (pat, bdy) -> bdy |> verify (fvOfTerm pat |> Set.union dom) (fvOfTerm pat |> Set.union codom))
        | UTmMatch (x, cs) ->
          verify dom codom x && cs |> List.forall (snd >> verify dom codom)
        | UTmConstruct (_, xs) -> xs |> List.forall (verify dom codom)
        | UTmFun b ->
          b |> verify dom codom
        | UTmLet (x, l, r) 
        | UTmLetDefer (x, l, r) ->
          [l; r] |> List.forall (verify (dom |> Set.remove x) (codom |> Set.remove x))
        | UTmApply (l, rs) -> l :: rs |> List.forall (verify dom codom)
        | UTmFreeVar x -> self <> x
        | UTmTuple xs -> xs |> List.forall (verify dom codom)
        | UTmBoundVar _
        | UTmLiteral _
        | UTmExternal _ -> true
        | UTmDefer x
        | UTmRun x ->
          verify dom codom x
        | UTmFixMatch (f, cs) ->
          cs |> List.forall (snd >> verify (dom |> Set.remove f) (codom |> Set.remove f))
    in
    if res then
      res
    else
      TermWithMessage ("Recursion is not well-founded. Bad expression: '%s'", t) |> TyperFailed |> raise
  in cases |> List.forall (fun (ptn, bdy) ->
      match ptn with
        | UTmConstruct _ -> verify (fvOfTerm ptn) (fvOfTerm ptn) bdy
        | _ -> verify Set.empty Set.empty bdy
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
        let (name, targs, cts, ctargs, nq) =
          match (ctx |> findConstructor x (Some ys)) with
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
      | UTmTuple xs ->
        let (nq, ts) = xs |> List.fold (fun (u, ts) x -> let (nu, nt) = gh u x in (nu, nt :: ts)) (uq, []) in
        (nq, TTuple (ts |> List.rev))
      | UTmLiteral LUnit -> (uq, Unit)
      | UTmLiteral (LNat _) -> (uq, Nat)
      | UTmLiteral (LBool _) -> (uq, Bool)
      | UTmFreeVar x ->
        let (tn, nq) = genUniq uq in
        (nq, TypeVar tn)
      | _ -> TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
  in
  let (newUniq, ts) = pats |> List.map fst |> List.fold (fun (u, ts) p -> let (nu, t) = gh u p in (nu, t :: ts)) (uniq, []) in
  let cstr =
    ts |> List.map (fun t -> Constraint (TypeVar a, t, mth))
  in 
  let rt = TypeVar a |> substAll (unify cstr |> cstr_toAsgn) in
  exhaustiveCheck (pats |> List.map fst) rt ctx;
  (rt, newUniq)


and isValidAsPattern = function
  | UTmLiteral _
  | UTmConstruct (_, [])
  | UTmFreeVar _ -> true
  | UTmConstruct (_, xs)
  | UTmTuple xs -> xs |> List.forall isValidAsPattern
  | _ -> false

and bindPattern pat t ctx =
  let rec bt pat t =
    match (pat, t) with
      | (UTmConstruct (n, xs), TypeOp (name, ts, _)) ->
        match (ctx |> findType name) with
          | Some (Variant (name, vts, cts)) ->
            let asgn = vts |> List.map2 (fun x -> function | TypeVar y -> (y, x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList |> Assign in
            let cts' = cts |> List.map (fun (cn, ct) -> (cn, ct |> List.map (substAll asgn))) in
            bt (UTmConstruct (n, xs)) (Variant (name, vts, cts'))
          | _ -> failwith "impossible_bindPattern"
      | (UTmConstruct (n, xs), Variant (_, _, cts)) when (cts |> List.exists (fun (m, ts) -> m = n && List.length xs = List.length ts)) ->
        let ts = cts |> List.find (fst >> ((=) n)) |> snd in
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UTmTuple xs, TypeOp("*", ts, _)) when (List.length xs = List.length ts) ->
        xs |> List.map2 (fun x y -> bt y x) ts |> List.concat
      | (UTmFreeVar "_", _)
      | (UTmLiteral LUnit, Unit)
      | (UTmLiteral (LNat _), Variant ("Nat", _, _))
      | (UTmLiteral (LBool _), Bool) -> []
      | (UTmFreeVar x, t) -> [ TermContext (x, t, UTmFreeVar x) ]
      | _ -> failwith "bindfailed"
  in
  try
    bt pat t |> Some
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
      match (ctx |> findConstructor x (Some ys)) with
        | Some (Variant (name, _, _), _) -> (name, 1) <+> (ys |> List.map gett |> concat)
        | _ -> Map.empty
    | UTmFreeVar x ->
      match (ctx |> findConstructor x (Some [])) with
        | Some (Variant (name, _, _), _) -> [(name, 1)] |> Map.ofList
        | _ -> Map.empty
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
    | Variant (vname, _, cts) ->
      cts |> List.map (fun (name, args) ->
              args |> List.map (genReq (mp |> next vname))
                   |> cartProd
                   |> (function 
                        | [] -> [ UTmConstruct (name, []) ]
                        | x -> x |> List.map (fun xs -> UTmConstruct (name, xs))
                      )
             ) 
          |> List.concat
    | TypeOp ("*", ts, _) ->
      ts |> List.map (genReq mp) |> cartProd |> List.map UTmTuple
    | Unit -> [ UTmLiteral LUnit ]
    | Bool -> [ UTmLiteral (LBool true); UTmLiteral (LBool false)]
    | TypeOp (name, ts, _) ->
      match (ctx |> findType name) with
        | Some (Variant (name, vts, cts)) ->
          if (mp |> Map.containsKey name) then
            let asgn = vts |> List.map2 (fun x -> function | TypeVar y -> (y, x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList |> Assign in
            let cts' = cts |> List.map (fun (cn, ct) -> (cn, ct |> List.map (substAll asgn))) in
            genReq mp (Variant (name, vts, cts'))
          else
            [ UTmFreeVar "_" ]
        | _ -> failwith "impossible_exhaustivenessCheck"
    | TypeVar _ -> [ UTmFreeVar "_" ] // only matched with variable patterns
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

let prettify uniq t =
  let rec getTyNames = function
    | TypeVar n -> set [n]
    | Fun (a, b) -> Set.union (getTyNames a) (getTyNames b)
    | Deferred t -> getTyNames t
    | Variant (_, ts, _)
    | TypeOp (_, ts, _) -> ts |> List.map getTyNames |> List.fold Set.union (set [])
    | Scheme (vs, t) -> getTyNames t |> Set.union vs
    | _ -> set []
  in
  let fv = getTyNames t in
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
  let (term', t, _, cstr) = recon ctx [] 0 term in
  (term', solve t cstr |> prettify 0 |> fst)

let inferWithAnnotation ctx term typ =
  let (term', t, _, cstr) = recon ctx [] 0 term in
  (term', solve t (Constraint (t, typ, term') :: cstr) |> prettify 0 |> fst)

let infer term =
  inferWithContext [] term

()
