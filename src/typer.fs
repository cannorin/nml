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
          UnknownVar (vn, ctx) |> TyperFailed |> raise
    
    | UFun (an, body) ->
      let (u, newUniq) = genUniq uniq in
      let ctx' = ctx |> typerAdd an (TypeVar u) in
      let (body', t, newUniq', cstr) = recon ctx' newUniq body in
      (UFun (an, body'), Fun (TypeVar u, t), newUniq', cstr)
    
    | UFunUnit x ->
      let (x', tx, newUniq, cstr) = recon ctx uniq x in
      (UFunUnit x', Fun(Unit, tx), newUniq, cstr)

    | UApply (l, r) ->
      let (l', tl, newUniq1, cstr1) = recon ctx uniq l in
      let (r', tr, newUniq2, cstr2) = recon ctx newUniq1 r in
      let (nv, newUniq3) = genUniq newUniq2 in
      (UApply (l', r'), TypeVar nv, newUniq3, List.concat [ [ Constraint (tl, Fun (tr, TypeVar nv), UApply (l, r)) ]; cstr1; cstr2])
    
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

    | URun x ->
      let (x', tx, newUniq, cstr) = recon ctx uniq x in
      let (tx', ttime) = getTimeOfType tx in
      if (ttime > 0) then
        (URun x', tx' |> delayTypeBy (ttime - 1), newUniq, cstr)
      else
        NotRunnable tx |> TyperFailed |> raise

let prettify uniq t =
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
  (term', solve t cstr |> prettify 0 |> fst)

let infer term =
  inferWithContext [] term

()
