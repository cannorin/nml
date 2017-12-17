module nml.Typer

open nml.Ast
open nml.Sizes
open nml.Helper
open nml.UniversalContext
open Microsoft.FSharp.Collections

let inline (<+>) l r = List.append l r

type Constraint = 
  | CTypeEq of Type * Type * UntypedTerm
  | CSizeLte of SizeInequality * Type * Type * UntypedTerm
  override this.ToString() =
    match this with
      | CTypeEq (t1, t2, _) ->
        sprintf "%s == %s" (to_s t1) (to_s t2)
      | CSizeLte (si, _, _, _) ->
        to_s si

type Assign =
  | AType of Type
  | ASize of Size * SizeAssignType
and SizeAssignType = SALeft | SARight

let cstr_toAsgn xs =
  let f = function
    | CTypeEq (TypeVar x, ty, _) -> (x, AType ty) |> Some
    | CSizeLte (SizeInequality (SVar x, sy), _, _, _) -> (x, ASize (sy, SARight)) |> Some
    | CSizeLte (SizeInequality (sx, SVar y), _, _, _) -> (y, ASize (sx, SALeft)) |> Some
    | _ -> None
  in
  xs |> List.choose f |> Map.ofList 

let argsmap f c =
  { c with args = c.args |> List.map f }

// t |> replaceType "x" tx
// --> t [x <- tx]
let replaceType vname tvl tsbj =
  let rec sub = function
    | Fun (a, b) -> Fun (sub a, sub b)
    | TypeVar nm when (nm = vname) -> tvl
    | Deferred t -> Deferred (sub t)
    | DataType (n, ts, cts, s, h) -> 
      DataType (n, ts |> List.map sub, cts |> List.map (argsmap sub), s, h)
    | Scheme (tvs, sbs, t) -> Scheme (tvs, sbs, sub t)
    | x -> x
  in sub tsbj

// t {i} |> replaceSize "i" s
// --> t {j}
let replaceSize vname size isRight t =
  let rec sub = function
    | Fun (a, b) -> Fun (sub a, sub b)
    | Deferred t -> Deferred (sub t)
    | DataType (n, ts, cts, s, h) ->
      DataType (n, 
                ts |> List.map sub,
                cts |> List.map (argsmap sub),
                (if true then s |> Option.map (SizeOp.substIn vname size) else s),
                h)
    | x -> x
  in sub t

let substIn name assign tsbj =
  match assign with
    | AType t -> tsbj |> replaceType name t
    | ASize (s, SARight) -> tsbj |> replaceSize name s true
    | ASize (s, SALeft) -> tsbj |> replaceSize name s false

let substAll asins t =
  asins |> Map.fold (fun tsbj n a -> tsbj |> substIn n a) t

let substInConstraints name assign cs =
  let f = function
    | CTypeEq (ta, tb, u) -> CTypeEq (ta |> substIn name assign, tb |> substIn name assign, u)
    | CSizeLte (SizeInequality (s, t), u, v, w) ->
      let u = u |> substIn name assign in
      let v = v |> substIn name assign in
      match assign with
        | ASize (a, SALeft)  -> CSizeLte (SizeInequality (s |> SizeOp.substIn name a, t), u, v, w)
        | ASize (a, SARight) -> CSizeLte (SizeInequality (s, t |> SizeOp.substIn name a), u, v, w)
        | _ -> CSizeLte (SizeInequality (s, t), u, v, w)
  in cs |> List.map f

let substAllInConstraints asins cs =
  asins |> Map.fold (fun c n a -> c |> substInConstraints n a) cs

let addForall ctx cstr t =
  let btvs = 
    ctx |> toTyperMap
        |> List.map (snd >> fvOf)
        |> List.fold Set.union (set [])
  in
  let bsvs =
    ctx |> toTyperMap
        |> List.map (snd >> fsvOf)
        |> List.fold Set.union (set [])
  in
  let tvars = 
    t |> fvOf
      |> Set.filter (fun y -> btvs |> Set.contains y |> not)
  in
  let svars =
    t |> fsvOf
      |> Set.filter (fun y -> bsvs |> Set.contains y |> not)
      |> Set.toList
      |> List.map (fun x ->
                     let f = function
                       | CSizeLte (SizeInequality (SVar x', sy), _, _, _) when x = x' -> Some (x, sy)
                       | _ -> None
                     in
                     match (cstr |> List.choose f) with
                       | [] -> [(x, SInf)]
                       | bs -> bs
                  )
      |> List.concat
      |> Map.ofList
  in
  //printsn (tvars, svars, t);
  if (Set.isEmpty tvars && Map.isEmpty svars) then 
    t
  else
    Scheme (tvars, svars, t)

let rec removeForall = function
  | Scheme (_, _, t) -> removeForall t
  | t -> t

let getNames t = 
  let rec gt = function
    | TypeVar n -> set [n]
    | Fun (a, b) -> Set.union (gt a) (gt b)
    | Deferred t -> gt t
    | DataType (_, ts, cts, _, _) ->
      cts |> List.map (fun c -> c.args) |> List.concat |> List.append ts 
          |> List.map gt |> List.fold Set.union (set [])
    | Scheme (vs, _, t) -> gt t |> Set.union vs
    | _ -> set []
  in
  let rec gs = function
    | Scheme (_, ss, t) -> gs t |> Set.union (ss |> Map.keys)
    | DataType (_, ts, cts, s, _) ->
      cts |> List.map (fun c -> c.args) |> List.concat |> List.append ts
          |> List.map gs |> List.fold Set.union (s |> Option.map SizeOp.fvOf ?| set [])
    | Fun (a, b) -> Set.union (gs a) (gs b)
    | Deferred t -> gt t
    | _ -> set []
  in
  (gt t, gs t)

let prettify uniq ts =
  let (ftvs, fsvs, ts) =
    let f t =
      let (ftv, fsv) = getNames t in
      (*
      let t =
        if (Set.isEmpty ftv && Set.isEmpty fsv) then
          t
        else
          Scheme (ftv, fsv, t)
      in *)
      (ftv, fsv, t)
    in
    ts |> List.map f
       |> List.fold (fun (ftvs, fsvs, ts) (ftv, fsv, t) -> (Set.union ftvs ftv, Set.union fsvs fsv, t :: ts)) (Set.empty, Set.empty, [])
       |> (fun (x, y, z) -> (x, y, List.rev z))
  in
  let rec rename mt ms = function
    | Scheme (vs, ss, t) ->
      Scheme (vs |> Set.map (fun x -> mt |> Map.tryFind x ?| x),
              ss |> Map.map2 (fun (k, v) -> (ms |> Map.tryFind k ?| k, 
                                             ms |> Map.fold (fun s k v -> s |> SizeOp.substIn k (SVar v)) v)),
              rename mt ms t)
    | x -> x |> substAll (mt |> Map.map (fun _ v -> TypeVar v |> AType)) 
             |> substAll (ms |> Map.map (fun _ v -> ASize (SVar v, SARight)))
  let ftmap = ftvs |> Set.map (fun x -> (x, x + "+")) |> Set.toList |> Map.ofList in
  let fsmap = fsvs |> Set.map (fun x -> (x, x + "+")) |> Set.toList |> Map.ofList in
  let ts' = ts |> List.map (rename ftmap fsmap) in
  let (us, uniq) = ftvs |> Set.count |> genUniqs uniq in
  let (vs, uniq) = fsvs |> Set.count |> genUniqs uniq in
  let newtmap = ftvs |> Set.toList |> List.map2 (fun y x -> (x + "+", y)) us |> Map.ofList in
  let newsmap = fsvs |> Set.toList |> List.map2 (fun y x -> (x + "+", y)) vs |> Map.ofList in
  (ts' |> List.map (rename newtmap newsmap), uniq)

let prettify1 a =
  match (prettify 0 [a]) with
    | ([a'], _) -> a'
    | _ -> failwith "impossible_prettify1"

let prettify2 (a, b) =
  match (prettify 0 [a; b]) with
    | ([a'; b'], _) -> (a', b')
    | _ -> failwith "impossible_prettify2"


let rename u vs ss f t =
  let (nvs, u) = vs |> List.length |> genUniqs u in
  let (nus, u) = ss |> List.length |> genUniqs u in
  let qvs = vs |> List.map ((+) "_rename") in
  let qus = ss |> List.map ((+) "_rename") in
  let genasgn xs ys xs' ys' =
    let mt = List.map2 (fun x y -> (x, AType (TypeVar y))) xs ys in
    let ms = List.map2 (fun x y -> (x, ASize (SVar y, SARight))) xs' ys' in
    List.append mt ms |> Map.ofList
  in
  let genst xs ys s =
    List.map2 (fun x y -> SizeOp.substIn x (SVar y)) xs ys |> List.fold (fun x f -> f x) s
  in
  let geng xs ys xs' ys' s =
    let c = List.zip xs ys <+> List.zip xs' ys' in
    c |> Map.ofList |> Map.tryFind s ?| s
  in
  (t |> f (substAll (genasgn vs qvs ss qus), genst ss qus, geng vs qvs ss qus) 
     |> f (substAll (genasgn qvs nvs qus nus), genst qus nus, geng qvs nvs qus nus), u)


type FailureReason =
  | UnifyFailed of Type * Type * UntypedTerm
  | SizeInconsistent of SizeInequality * Type * Type * UntypedTerm
  | UnknownVar of string * Context
  | UnknownConst of string * UntypedTerm list * Context
  | NotMatchable of UntypedTerm * Type * UntypedTerm
  | TermWithMessage of Printf.StringFormat<string -> string> * UntypedTerm
  | NotInductive of Type

exception TyperFailed of FailureReason

// Constraint list -> Constraint list
let unify cs =
  let diverge = function
    | DataType (n, ags, cs, Some _, h) -> DataType (n, ags, cs, Some SInf, h)
    | x -> x
  in
  let rec u = function
    | CTypeEq (s, t, _) :: rest when (s = t) -> u rest
    | CTypeEq (s, TypeVar tn, x) :: rest
    | CTypeEq (TypeVar tn, s, x) :: rest when (s |> hasTyVar tn |> not) ->
      List.append (rest |> substInConstraints tn (AType s) |> u) [ CTypeEq (TypeVar tn, s, x) ]
    | (CTypeEq (DataType (n, _, _, _, _), InductiveSelf m, _) :: _ & CTypeEq (t, _, _) :: rest)
    | (CTypeEq (InductiveSelf m, DataType (n, _, _, _, _), _) :: _ & CTypeEq (_, t, _) :: rest) when (n = m && isInductive t ?| false) ->
      u rest
    | (CTypeEq (DataType (m, rts, _, sm, _), DataType (n, lts, _, sn, _), t) :: rest & CTypeEq (tl, tr, _) :: _) when (n = m && List.length lts = List.length rts) ->
      let ams = sm |> Option.map2 (fun m n -> [ CSizeLte (SizeInequality (m, n), tl, tr, t); CSizeLte (SizeInequality (n, m), tr, tl, t) ]) sn ?| [] in
      ams <+> rest |> List.append (List.map2 (fun x y -> CTypeEq (x, y, t)) lts rts) |> u
    | CTypeEq (Fun (a1, b1), Fun (a2, b2), f) :: rest ->
      u (CTypeEq (a1, a2, f) :: CTypeEq (b1, b2, f) :: rest)
    | CTypeEq (Deferred a, Deferred b, d) :: rest ->
      u (CTypeEq (a, b, d) :: rest)
    | CTypeEq (s, t, u) :: _ ->
      let (s', t') = prettify2 (s, t) in
      UnifyFailed (removeForall s', removeForall t', u) |> TyperFailed |> raise
    | CSizeLte (SizeInequality (sl, sr), tl, tr, tm) :: rest ->
      let si = SizeInequality (sl, sr) in
      let csli l r = CSizeLte (SizeInequality (l, r), tl, tr, tm) in
      let csl si = CSizeLte (si, tl, tr, tm) in
      match (sl, sr) with
        | (sx, sy) when sx = sy -> rest |> u
        | (SSucc sx, SSucc sy) ->  csli sx sy :: rest |> u
        | (SVar x, sy) when (SizeOp.fvOf sy |> Set.contains x |> not) ->
          match (SizeOp.check si) with
            | Some xs ->
              let f s =
                let cs = List.append (xs |> List.map csl) rest |> substInConstraints x (ASize (s, SARight)) in
                [si |> SizeOp.bimap SizeOp.prettify |> csl] |> List.append (cs |> u)
              in
              try
                f sy
              with
                | _ -> f SInf
            | None -> SizeInconsistent (si, tl, tr, tm) |> TyperFailed |> raise
        | (sx, SVar y) when (SizeOp.fvOf sx |> Set.contains y |> not) ->
          match (SizeOp.check si) with
            | Some xs ->
              let cs = List.append (xs |> List.map csl) rest |> substInConstraints y (ASize (sx, SALeft)) in
              [si |> SizeOp.bimap SizeOp.prettify |> csl] |> List.append (cs |> u)
            | None -> SizeInconsistent (si, tl, tr, tm) |> TyperFailed |> raise
        | (SVar _, _) -> (si |> SizeOp.bimap SizeOp.prettify |> csl) :: (rest |> u)
        | (_, SVar _) -> SizeInconsistent (si, tl, tr, tm) |> TyperFailed |> raise
        | (_, _) ->
          match (SizeOp.check si) with
            | Some xs ->
              let cs = List.append (xs |> List.map csl) rest in
              [si |> SizeOp.bimap SizeOp.prettify |> csl] |> List.append (cs |> u) 
            | None -> SizeInconsistent (si, tl, tr, tm) |> TyperFailed |> raise
    | [] -> []
  in u cs

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
        | Some (Scheme (vs, ss, t)) ->
          //printsn (Scheme (vs, ss, t));
          let f (ft, fs, fg) (ty, ss) =
            (ft ty, ss |> Map.map2 (fun (k, v) -> (fg k, fs v)))
          in
          let ((t, ss), uniq) = (t, ss) |> rename uniq (vs |> Set.toList) (ss |> Map.keys |> Set.toList) f in
          //let cstr = ss |> Map.toList |> List.map (fun (k, v) -> CSizeLte (SizeInequality (SVar k, v), t, t, term)) in
          //printsn t;
          (term, t, uniq, [])
        | Some t -> (term, t, uniq, [])
        | None -> 
          match (ctx |> findConstructor vn None) with
            // constructor as a function
            | Some (DataType (name, targs, cts, s, h), c) & Some (t, _) ->
              let tprms = targs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
              let sprms = s |> Option.map (SizeOp.fvOf >> Set.toList) ?| [] in
              let (vt, uniq) = DataType (name, targs, cts, s, h) |> rename uniq tprms sprms fstOf3 in
              let (vt, c, cstr, uniq) = 
                match vt with
                  | DataType (_, ts, cs, _, _) when (c.isRecursive |> not) ->
                    let s = if (vt |> isInductive ?| false) then Some SZero else None in
                    let vt = DataType (name, ts, cs, s, h) in
                    let c = cs |> List.find (fun c -> c.name = vn) in
                    (vt, c, [], uniq)
                  | DataType (_, ts, cs, s, _) -> 
                    let (cs, cstr, uniq) = unfoldInductive uniq (name, ts, cs, s, h) (UTmFreeVar vn, vt) in 
                    let vt = DataType (name, ts, cs, s, h) in
                    let c = cs |> List.find (fun c -> c.name = vn) in
                    (vt, c, cstr, uniq)
                  | _ -> failwith "impossible_UTmFreeVar"
              in
              let (argt, isone) = 
                if (c.args |> List.length = 1) then
                  (c.args.[0], true)
                else
                  (TTuple (c.args), false)
              in
              let typ = (Fun (argt, vt)) in
              let con = ExternalFun vn typ (function
                  | x :: _ when isone -> UTmConstruct (vn, [x])
                  | UTmConstruct ("*", xs) :: _ -> UTmConstruct (vn, xs)
                  | _ -> failwith "impossible_recon_UVar_variantfun"
                )
              in
              (con, typ, uniq, cstr)
            | Some _
            | None -> UnknownVar (vn, ctx) |> TyperFailed |> raise
    
    | UTmBoundVar i ->
      if (List.length stack > i) then
        (UTmBoundVar i, stack |> List.item i, uniq, [])
      else
        failwith "impossible_UBoundVar"

    | UTmFun body ->
      let (u, uniq) = genUniq uniq in
      let (body', t, uniq, cstr) = recon ctx ((TypeVar u) :: stack) uniq body in
      let (v, uniq) = genUniq uniq in
      (UTmFun body', TypeVar v, uniq, cstr <+> CTypeEq (TypeVar v, Fun (TypeVar u, t), UTmFun body') :: [])

    | UTmConstruct (n, args) ->
      match (ctx |> findConstructor n (Some args)) with
        | Some (DataType (name, vtargs, cts, s, h), ctor) & Some (vt, _) ->
          printfn "%A" s;
          let vtprms = vtargs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
          let vsprms = s |> Option.map (SizeOp.fvOf >> Set.toList) ?| [] in
          let f (ft, fs, _) (vas, cts, st) =
            (vas |> List.map ft,
             cts |> List.map (argsmap ft),
             st |> Option.map fs
            )
          in
          let ((vtargs', cts', s'), uniq) = (vtargs, cts, s) |> rename uniq vtprms vsprms f in
          printfn "%A" s';
          let (cts', cstr, uniq) = 
            if ctor.isRecursive then
              unfoldInductive uniq (name, vtargs', cts', s', h) (UTmConstruct (n, args), vt)
            else
              (cts', [], uniq)
          in
          let ctargs =
            (cts' |> List.find (fun c -> c.name = n)).args
          in
          let (args', targs, uniq, cstrs) = multiRecon uniq args in
          let vcstrs =
            targs
              |> List.map2 (fun x y -> (x, y)) ctargs
              |> List.map2 (fun x (y, z) -> CTypeEq (y, z, x)) args'
          in

          let vt = 
            let s = 
              if ctor.isRecursive then s'
              else if (vt |> isInductive ?| false) then Some SZero 
              else None 
            in
            DataType (name, vtargs', cts', s, h)
          in
          let (u, uniq) = genUniq uniq in
          (UTmConstruct (n, args'), TypeVar u, uniq, cstr <+> vcstrs <+> cstrs <+> CTypeEq (TypeVar u, vt, UTmConstruct (n, args')) :: [])
        | _
        | None -> UnknownConst (n, args, ctx) |> TyperFailed |> raise
    
    | UTmTuple [x] ->
      recon ctx stack uniq x
    
    | UTmTuple xs ->
      let (xs', txs, uniq, cstrs) = multiRecon uniq xs in
      (UTmTuple xs', TTuple txs, uniq, cstrs) 

    | UTmApply (l, rs) ->
      let (l', tl, uniq, cstr1) = recon ctx stack uniq l in
      let (rs', trs, uniq, cstr2) = multiRecon uniq rs in
      let (nv, uniq) = genUniq uniq in
      (UTmApply (l', rs'), TypeVar nv, uniq, cstr2 <+> cstr1 <+> CTypeEq (tl, foldFun trs (TypeVar nv), UTmApply (l', rs')) :: [])

    | UTmLiteral l -> 
      match l with
        | LNat 0u ->
          (term, NatS (SZero), uniq, [])
        | LNat n ->
          let (nv, uniq) = genUniq uniq in
          (term, NatS (SVar nv), uniq, [ CSizeLte (SVar nv <=^ SNat n, NatS (SVar nv), NatS (SNat n), LNat n |> UTmLiteral) ])
        | LBool _ -> (term, Bool, uniq, [])
        | LUnit -> (term, Unit, uniq, [])
   
    | UTmLet (x, value, body) ->
      let (value', tvalue, uniq, cstr1) = recon ctx stack uniq value in
      let cstr1' = unify cstr1 in
      let tvalue' = tvalue |> substAll (cstr_toAsgn cstr1') in
      let tx = tvalue' |> addForall ctx cstr1' in
      let ctx' = ctx |> typerAdd x tx in
      let (body', tbody, uniq, cstr2) = recon ctx' stack uniq body in
      let tbody' = tbody |> substAll (cstr1 <+> cstr2 |> unify |> cstr_toAsgn) in
      let (r, uniq) = genUniq uniq in
      (UTmLet (x, value', body'), TypeVar r, uniq, cstr1 <+> cstr2 <+> CTypeEq (TypeVar r, tbody, UTmLet (x, value', body')) :: [])
   
    | UTmLetDefer (x, value, body) ->
      let (nv, uniq) = genUniq uniq in
      let (value', tvalue, uniq, cstr) = recon ctx stack uniq value in
      let (mv, uniq) = genUniq uniq in
      let cstr' = cstr <+> CTypeEq (Deferred (TypeVar nv), tvalue, value') :: CTypeEq (TypeVar mv, Deferred (TypeVar nv), value') :: [] in
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
      (UTmDefer x', TypeVar mv, uniq, cstr <+> CTypeEq (TypeVar nv, tx, UTmDefer x') :: CTypeEq (TypeVar mv, dt, UTmDefer x') :: [])
    
    | UTmRun x ->
      let (nv, uniq) = genUniq uniq in
      let dt = Deferred (TypeVar nv) in
      let (x', tx, uniq, cstr) = x |> recon ctx stack uniq in
      let (mv, uniq) = genUniq uniq in
      (UTmRun x', TypeVar mv, uniq, cstr <+> CTypeEq (dt, tx, UTmRun x) :: CTypeEq (TypeVar mv, TypeVar nv, UTmRun x') :: [])

    | UTmExternal (_, t) ->
      (term, t, uniq, [])

    | UTmMatch (v, cases) ->
      let (v', tv, uniq, cstr) = recon ctx stack uniq v in
      let cases = cases |> List.map (fun (ptn, body) -> (expandCases ptn, body)) in
      let (a, uniq) = reconFromPatterns cases (UTmMatch (v, cases)) ctx uniq in
      if ((getTimeOfType tv |> snd) > 0) then
        TermWithMessage ("the term '%s' is not pure and cannot be matched.", v') |> TyperFailed |> raise
      let (bs', tbs, uniq, css) = 
        let f = 
          cases 
            |> List.foldBack (fun (pat, body) (bs', tbs, u, css) ->
                if (isValidAsPattern pat |> not) then
                  TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
                else
                  match (bindPattern pat a ctx u) with
                    | Some (stack', cstr, uniq) -> 
                      let stack = List.append stack' stack in
                      let (body', tbody, uniq, bcstr) = recon ctx stack uniq body in
                      (body' :: bs', tbody :: tbs, uniq, bcstr <+> cstr <+> css)
                    | None -> NotMatchable (pat, a, body) |> TyperFailed |> raise
              )
        in f ([], [], uniq, [])
      in
      let term' = UTmMatch (v', cases |> List.map2 (fun nb (pat, b) -> (pat, nb)) bs') in
      let (b, uniq) = genUniq uniq in
      let b = TypeVar b in
      let bcstr =
        tbs |> List.map2 (fun x t -> CTypeEq (b, t, x)) bs'
      in
      let cstrs = cstr <+> css <+> bcstr <+> CTypeEq (tv, a, v') :: [] in
      (term', b, uniq, cstrs)
    
    | UTmFixMatch cases ->
      let (uvs, uniq) = genUniqs uniq 3 in
      let (targ, targ', tret) =
        match uvs with
          | [a; b; c] -> (TypeVar a, TypeVar b, TypeVar c)
          | _ -> failwith "impossible_UFixMatch"
      in
      let tthis = Fun (targ, tret) in
      let ctx' = ctx |> typerAdd "x" targ' in
      
      (*
      let cases = cases |> List.map (fun (ptn, body) -> (expandCases ptn, body)) in
      
      let (a, uniq) = reconFromPatterns cases (UTmFixMatch cases) ctx uniq in
      let (bs', tbs, uniq, css) = 
        let f = 
          cases 
            |> List.foldBack (fun (pat, body) (bs', tbs, u, css) ->
                if (isValidAsPattern pat |> not) then
                  TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
                else
                  match (bindPattern pat a ctx u) with
                    | Some (stack', cstr, uniq) -> 
                      let (n, uniq) = genUniq uniq in
                      let selfType = Fun (TypeVar n, a) in
                      let stack = selfType :: stack in 
                      let stack = List.append stack' stack in
                      let (n, uniq) = genUniq uniq in
                      let (body', tbody, uniq, bcstr) = recon ctx stack uniq body in
                      match (a, tbody |> substAll (unify bcstr |> cstr_toAsgn)) with
                        | (DataType (_, _, _, Some s, _), DataType (_, _, _, Some t, _)) ->
                          let d = SizeOp.tryGetDiff s t |> Option.map ((|>) SZero >> to_s) ?| (sprintf "%s, %s" (to_s a) (to_s tbody)) in
                          printsn d
                        | (a, tbody) -> printfn "%s, %s" (to_s a) (to_s tbody)
                      (body' :: bs', tbody :: tbs, uniq, bcstr <+> cstr <+> css)
                    | None -> NotMatchable (pat, a, body) |> TyperFailed |> raise
              )
        in f ([], [], uniq, [])
      in
      *)
      //let checkDiff (pat, bdy) =
      
      let (mth, tmth, uniq, cstr1) = recon ctx' (tthis :: stack) uniq (UTmMatch (UTmFreeVar "x", cases)) in

      let (ret, uniq) = genUniq uniq in
      match mth with
        | UTmMatch (_, cases) ->
          verifyTermination cases |> ignore;
          (UTmFixMatch cases, TypeVar ret, uniq, cstr1 <+> CTypeEq (tthis, Fun (targ', tmth), UTmFixMatch cases) :: CTypeEq (TypeVar ret, Fun (targ', tmth), UTmFixMatch cases) :: [])
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
        | _ -> verify [] [] bdy
    )

and reconFromPatterns pats tm ctx uniq =
  let (a, uniq) = genUniq uniq in
  let rec gh uq pat =
    match pat with
      | UTmConstruct (x, ys) ->
        let (name, targs, cts, ctargs, nq, s, h) =
          match (ctx |> findConstructor x (Some ys)) with
            | Some (DataType (name, targs, cts, s, h), c) ->
              let tprms = targs |> List.choose (function | TypeVar x -> Some x | _ -> None) in
              let sprms = s |> Option.map (SizeOp.fvOf >> Set.toList) ?| [] in
              let ((targs', cts', c', s'), uniq) = 
                (targs, cts, c, s) |> rename uq tprms sprms (fun (ft, fs, _) (x, y, z, s) -> 
                    (
                      x |> List.map ft,
                      y |> List.map (argsmap ft),
                      z |> argsmap ft,
                      s |> Option.map fs
                    )
                  )
              in
              (name, targs', cts', c'.args, uniq, s', h)
            | _
            | None -> UnknownVar (x, ctx) |> TyperFailed |> raise
        in
        let (fnq, pts) = ys |> List.fold (fun (u, ts) y -> let (nu, nt) = gh u y in (nu, nt :: ts)) (nq, []) in
        let asgn = 
          ctargs |> List.rev
                 |> List.map2 (fun y -> (function | TypeVar x -> Some (x, AType y) | _ -> None)) pts 
                 |> List.choose id |> Map.ofList 
        in
        let vt = DataType (name, targs, cts, s, h) |> substAll asgn in
        (fnq, vt)
      | UTmTuple xs ->
        let (nq, ts) = xs |> List.fold (fun (u, ts) x -> let (nu, nt) = gh u x in (nu, nt :: ts)) (uq, []) in
        (nq, TTuple (ts |> List.rev))
      | UTmLiteral LUnit -> (uq, Unit)
      | UTmLiteral (LNat _) -> 
        let (v, uq) = genUniq uq in
        (uq, NatS (SVar v))
      | UTmLiteral (LBool _) -> (uq, Bool)
      | UTmFreeVar "_"
      | UTmBoundVar _ ->
        let (tn, nq) = genUniq uq in
        (nq, TypeVar tn)
      | _ -> TermWithMessage ("the term '%s' cannot be used as a pattern.", pat) |> TyperFailed |> raise
  in
  let (uniq, ts) = pats |> List.map fst |> List.fold (fun (u, ts) p -> let (nu, t) = gh u p in (nu, t :: ts)) (uniq, []) in
  let cstr =
    ts |> List.map (fun t -> CTypeEq (TypeVar a, t, tm))
  in 
  let rt = TypeVar a |> substAll (unify cstr |> cstr_toAsgn) in
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

and unfoldInductive uniq (name, ts, cs, so, h) (pat, t) =
  let genNewSelf sv = DataType (name, ts, cs, Some sv, h) in
  let insertNone _ = DataType (name, ts, cs, None, h) in
  let unfoldCases psize genSelfMode =
    let nsvs = ref [] in
    let cuniq = ref uniq in
    let genUniqD () =
      let (nv, nuniq) = genUniq !cuniq in
      cuniq := nuniq;
      nsvs := nv :: (!nsvs);
      nv
    in
    let rec sub = function
      | Fun (a, b) -> Fun (sub a, sub b)
      | InductiveSelf nm when (nm = name) -> genUniqD () |> SVar |> genSelfMode
      | Deferred t -> Deferred (sub t)
      | DataType (n, ts, cts, s, h) ->
        DataType (n, ts |> List.map sub, cts |> List.map (argsmap sub), s, h)
      | Scheme (tvs, svs, t) -> Scheme (tvs, svs, sub t)
      | x -> x
    in
    let cs' = cs |> List.map (argsmap sub) in
    let cstr =
      let rec f = function
        | [] -> SZero
        | a :: [] -> SVar a
        | a :: rest -> SAdd (SVar a, f rest)
      in
      let sum = !nsvs |> List.rev |> f in
      [CSizeLte (SSucc sum <=^ psize, t, t, pat); CSizeLte (psize <=^ SSucc sum, t, t, pat)]
    in
    (cs', cstr, !cuniq)
  in
  match so with
    | Some s -> unfoldCases s genNewSelf
    | None when (isInductive t ?| false) ->
      let (cs, _, nuniq) = unfoldCases SZero genNewSelf in
      (cs, [], nuniq)
    | None ->
      let (cs, _, nuniq) = unfoldCases SZero insertNone in
      (cs, [], nuniq)

and bindPattern pat t ctx uniq =
  let rec bt pat t uniq =
    match (pat, t) with
      | (UTmConstruct (n, xs), DataType (name, ts, _, so, h)) ->
        match (ctx |> findType name) with
          | Some (DataType (_, vts, cts, _, _)) ->
            let (cts, cstr, uniq) = unfoldInductive uniq (name, vts, cts, so, h) (pat, t) in
            let asgn = vts |> List.map2 (fun x -> function | TypeVar y -> (y, AType x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList in
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            let ts = (cts' |> List.find (fun c -> c.name = n)).args in
            ts |> List.zip xs
               |> List.fold (fun (bs, cs, u) (pt, ty) ->
                               let (b', c', u) = bt pt ty u in
                               (bs <+> b', cs <+> c', u)
                            ) ([], cstr, uniq)
          | _ -> failwith "impossible_bindPattern"
      | (UTmTuple xs, DataType ("*", ts, _, _, _)) when (List.length xs = List.length ts) ->
        ts |> List.zip xs
           |> List.fold (fun (bs, cs, u) (pt, ty) ->
                           let (b', c', u)  = bt pt ty u in
                           (bs <+> b', cs <+> c', u)
                        ) ([], [], uniq)
      | (UTmFreeVar "_", _)
      | (UTmLiteral LUnit, Unit)
      | (UTmLiteral (LNat _), DataType ("Nat", _, _, _, _))
      | (UTmLiteral (LBool _), Bool) -> ([], [], uniq)
      | (UTmBoundVar x, t) -> ([(x, t)], [], uniq)
      | _ -> failwith "bindfailed"
  in
  try
    let (bs, cstr, uniq) = bt pat t uniq in 
    Some (bs |> List.sortBy fst |> List.map snd, cstr, uniq)
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
        | Some (DataType (name, _, _, _, _), _) -> (name, 1) <+> (ys |> List.map gett |> concat)
        | _ -> Map.empty
    | UTmFreeVar "_"
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
    | DataType ("*", ts, _, _, _) ->
      ts |> List.map (genReq mp) |> cartProd |> List.map UTmTuple
    | DataType (name, ts, _, _, _) ->
      match (ctx |> findType name) with
        | Some (DataType (vname, vts, cts, _ ,_)) ->
          if (mp |> Map.containsKey vname) then
            let (cts, _, _) = unfoldInductive 0 (name, vts, cts, None, Null) (UTmLiteral LUnit, Unit) in
            let asgn = vts |> List.map2 (fun x -> function | TypeVar y -> (y, AType x) |> Some | _ -> None) ts |> List.choose id |> Map.ofList in
            let cts = cts |> List.map (argsmap (substAll asgn)) in
            cts |> List.map (fun c ->
                     c.args |> List.map (genReq (mp |> next vname))
                            |> cartProd
                            |> (function 
                                 | [] -> [ UTmConstruct (c.name, []) ]
                                 | x -> x |> List.map (fun xs -> UTmConstruct (c.name, xs))
                               )
                   ) 
                |> List.concat
          else
            [ UTmFreeVar "_" ]
        | _ -> failwith "impossible_exhaustivenessCheck"
    | Unit -> [ UTmLiteral LUnit ]
    | Bool -> [ UTmLiteral (LBool true); UTmLiteral (LBool false)]
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

let inferWithContext_dbg ctx term debug =
  let (term', t, _, cstr) = recon ctx [] 0 term in
  let cstr' = unify cstr |> unify in
  let t' = t |> substAll (cstr_toAsgn cstr') |> prettify1 |> addForall ctx cstr' in
  if debug then
    cstr |> List.iter printsn;
    printfn "-------"; 
    cstr' |> List.iter printsn
  (term', t')
 
let inferWithContext ctx term =
  inferWithContext_dbg ctx term false

let infer term =
  inferWithContext [] term

let printTyperErr = function
  | UnifyFailed (a, b, ut) ->
    //printfn "%A" b;
    printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
  | SizeInconsistent (ti, a, b, ut) ->
    printfn "TYPER FAILED: '%s' and '%s' require an inconsistent size condition '%s'.\n------------> %s" (to_s a) (to_s b) (to_s ti) (to_s ut)
  | UnknownVar (n, ctx) ->
    printfn "TYPER FAILED: '%s' is not defined (unknown variable)" n
  | UnknownConst (n, ts, ctx) ->
    let ac = ts |> List.length in
    printfn "TYPER FAILED: a constructor '%s' that has %i arguments does not exist." n ac
  | NotMatchable (l, t, r) ->
    printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r)
  | TermWithMessage (f, t) ->
    sprintf f (to_s t) |> printfn "TYPER FAILED: %s"
  | NotInductive t ->
    printfn "TYPER FAILED: '%s' is not inductive" (to_s t)

()
