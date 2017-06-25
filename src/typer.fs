module nml.Typer

open nml.Ast
open nml.Evaluation
open nml.Helper
open Microsoft.FSharp.Collections

type Constraint = | Constraint of Type * Type * UntypedTerm
let cstr_Extract = function
  | Constraint (s, t, u) -> (s, t, u)

type Assign = | Assign of Map<string, Type>
let asgn_Extract = function
  | Assign x -> x

type Context = | Context of Map<string, Type>
let ctx_Extract = function
  | Context x -> x
let ctx_Init ts =
  ts |> List.fold (fun m (n, t) -> Map.add n t m) Map.empty |> Context

let cstr_toAsgn cstr =
  match cstr with
    | xs -> xs |> List.choose (function | Constraint (TypeVar name, t, _) -> Some (name, t) | _ -> None ) |> Map.ofList |> Assign


let rec getTyVars = function
  | TypeVar n -> set [n]
  | Fun (a, b) -> Set.union (getTyVars a) (getTyVars b)
  | Deferred t -> getTyVars t
  | TypeOp (_, ts, _) -> ts |> List.map getTyVars |> List.fold Set.union (set [])
  | Forall (vs, t)
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
    | Forall (tvs, t) -> Forall (tvs, sub t)
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
  | UnsupportedExpression of UntypedTerm
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
      | (s, TypeVar tn, x) :: rest when (s |> hasTyVar tn |> not) ->
        List.append (cs' |> cstrmap (substInConstraints tn s) |> u) [ (TypeVar tn, s, x) ]
      | (TypeVar tn, s, x) :: rest when (s |> hasTyVar tn |> not) ->
        List.append (cs' |> cstrmap (substInConstraints tn s) |> u) [ (TypeVar tn, s, x) ]
      | (Fun (a1, b1), Fun (a2, b2), f) :: rest ->
        u ((a1, a2, f) :: (b1, b2, f) :: rest)
      | (Deferred a, Deferred b, d) :: rest ->
        u ((a, b, d) :: rest)
      | (TypeOp (lname, lts, _), TypeOp (rname, rts, _), t) :: rest when (lname = rname && List.length lts = List.length rts) ->
        rest |> List.append (List.map2 (fun x y -> (x, y, t)) lts rts) |> u
      | (Forall (vs, a), b, t) :: rest
      | (b, Forall (vs, a), t) :: rest ->
        u ((a, b, t) :: rest)
      | (s, t, u) :: rest ->
        UnifyFailed (s, t, u) |> TyperFailed |> raise
      | [] -> []
  in u (cs |> List.map cstr_Extract) |> List.map Constraint

let renameType uniq t =
  let rec rename m = function
    | Scheme (vs, t) ->
      Scheme (vs |> Set.map (fun x -> m |> Map.tryFind x ?| x), rename m t) 
    | Forall (vs, t) ->
      Forall (vs |> Set.map (fun x -> m |> Map.tryFind x ?| x), rename m t) 
    | x -> x |> substAll (m |> Map.map (fun _ v -> TypeVar v) |> Assign)
  let ftmap = getTyVars t |> Set.map (fun x -> (x, x + "+")) |> Set.toList |> Map.ofList in
  let t' = t |> rename ftmap in
  let runiq = ref uniq in
  let rec newUniq () =
    let (u, nuniq) = genUniq !runiq in
    runiq := nuniq;
    u
  in
  let newmap = getTyVars t' |> Set.map (fun x -> (x, newUniq())) |> Set.toList |> Map.ofList in
  (t' |> rename newmap, !runiq)

// Context -> UniqId -> (Type * UniqId * Constraint list)
let rec recon ctx uniq t =
  let ectx = ctx_Extract ctx in
  match t with
    | UVar vn ->
      match (ectx |> Map.tryFind vn) with
        | Some (Scheme (vs, t)) ->
          let (t', newUniq) = renameType uniq t in
          (t', newUniq, [])
        | Some (Forall (vs, t)) ->
          let (t', newUniq) = Forall (vs, t) |> renameType uniq in
          (t', newUniq, [])
        | Some t -> (t, uniq, [])
        | None -> UnknownVar (vn, ctx) |> TyperFailed |> raise
    
    | UFun (an, body) ->
      let (u, newUniq) = genUniq uniq in
      let ctx' = ectx |> Map.add an (TypeVar u) |> Context in
      let (t, newUniq', cstr) = recon ctx' newUniq body in
      (Fun (TypeVar u, t), newUniq', cstr)
    
    | UFunUnit x ->
      let (tx, newUniq, cstr) = recon ctx uniq x in
      (Fun(Unit, tx), newUniq, cstr)
 
    | UApply (l, r) ->
      let (tl, newUniq1, cstr1) = recon ctx uniq l in
      let (tr, newUniq2, cstr2) = recon ctx newUniq1 r in
      let (tl', cstr1', newUniq2') = 
        match tl with
          | Forall (ts, t) ->
            let runiq = ref newUniq2 in
            let newUniq () =
              let (u, nuniq) = genUniq !runiq in
              runiq := nuniq;
              u
            in
            let asgn = ts |> Set.fold (fun pas v -> pas |> Map.add v (TypeVar (newUniq ()))) Map.empty |> Assign in
            (t |> substAll asgn, cstr1 |> substAllInConstraints asgn, !runiq) 
          | _ -> (tl, cstr1, newUniq2)
      in
      let (nv, newUniq3) = genUniq newUniq2' in
      (TypeVar nv, newUniq3, List.concat [ cstr1'; cstr2; [ Constraint (tl', Fun (tr, TypeVar nv), UApply (l, r)) ] ])
    
    | UIf (b, t, e) ->
      let (tb, nu1, cs1) = recon ctx uniq b in
      let (tt, nu2, cs2) = recon ctx nu1 t in
      let (te, nu3, cs3) = recon ctx nu2 e in
      (te, nu3, List.concat [ [ Constraint (tb, Bool, b); Constraint (tt, te, UIf (b, t, e)); ]; cs3; cs2; cs1 ]);
    
    | UTuple (a, b) ->
      let (ta, newUniq1, cstr1) = recon ctx uniq a in
      let (tb, newUniq2, cstr2) = recon ctx newUniq1 b in
      (TTuple (ta, tb), newUniq2, List.concat [ cstr1; cstr2 ])
    
    | ULiteral l -> 
      match l with
        | LNat _ -> (Nat, uniq, [])
        | LBool _ -> (Bool, uniq, [])
        | LUnit -> (Unit, uniq, [])
   
    | ULet (x, value, body) ->
      let (tvalue, newUniq, cstr1) = recon ctx uniq value in
      let cstr1' = unify cstr1 in
      let tvalue' = tvalue |> substAll (cstr_toAsgn cstr1') in
      let fvs = 
        ectx |> Map.toList
             |> List.map (fun (_, t) -> fvOf t |> Set.toList)
             |> List.concat
      in
      let tvars = 
        tvalue' |> fvOf
                |> Set.toList
                |> List.filter (fun y -> fvs |> List.contains y |> not)
      in
      let tx =
        if (List.length tvars = 0) then
          tvalue'
        else if (isValue value && body |> hasVar x) then
          Forall (tvars |> Set.ofList, tvalue')
        else
          Scheme (tvars |> Set.ofList, tvalue')
      in
      let ctx' = ectx |> Map.add x tx |> Context in
      recon ctx' newUniq body
    
    | UDefer x ->
      let (tx, newUniq, cstr) = recon ctx uniq x in
      (Deferred tx, newUniq, cstr)
   
    | ULetDefer (x, value, body) ->
      let (tvalue, newUniq, cstr1) = recon ctx uniq value in
      let cstr1' = unify cstr1 in
      let (tvalue', timevalue) = tvalue |> substAll (cstr_toAsgn cstr1') |> getTimeOfType in
      let fvs = 
        ectx |> Map.toList
             |> List.map (fun (_, t) -> fvOf t |> Set.toList)
             |> List.concat
      in
      let tvars = 
        tvalue' |> fvOf
                |> Set.toList
                |> List.filter (fun y -> fvs |> List.contains y |> not)
      in
      let tx =
        if (List.length tvars = 0) then
          tvalue'
        else if (isValue value && body |> hasVar x) then
          Forall (tvars |> Set.ofList, tvalue')
        else
          Scheme (tvars |> Set.ofList, tvalue')
      in
      let ctx' = ectx |> Map.add x tx |> Context in
      let (tbody, newUniq2, cstr2) = recon ctx' newUniq body in
      (tbody |> delayTypeBy timevalue, newUniq2, cstr2)
    
    | UExternal (_, t) ->
      (t, uniq, [])
    
    | URun x ->
      let (tx, newUniq, cstr) = recon ctx uniq x in
      let (tx', ttime) = getTimeOfType tx in
      if (ttime > 0) then
        (tx' |> delayTypeBy (ttime - 1), newUniq, cstr)
      else
        NotRunnable tx |> TyperFailed |> raise

let solve t cstr =
  let cstr' = unify cstr in
  t |> substAll (cstr_toAsgn cstr')

let inferWithContext ctx term =
  let ctx' = ctx_Init ctx in
  let (t, _, cstr) = recon ctx' 0 term in
  solve t cstr |> renameType 0 |> fst

let infer term =
  inferWithContext [] term

()
