module nml.Stages
open Microsoft.FSharp.Collections

let inline to_s x = x.ToString()

type Stage =
  | SVar of string
  | SZero
  | SInf
  | SSucc of Stage
  | SAdd of Stage * Stage
  override this.ToString () =
    match this with
      | SVar v -> v
      | SZero -> "0" | SInf -> "Inf"
      | SSucc s -> sprintf "^%s" (to_s s)
      | SAdd (s, t) -> sprintf "(%s + %s)" (to_s s) (to_s t)

type StageInequality = 
  | StageInequality of Stage * Stage
  override this.ToString () =
    let (StageInequality (s, t)) = this in
    sprintf "%s <= %s" (to_s s) (to_s t)

let (<=^) x y = StageInequality (x, y)
let (+^) x y = SAdd (x, y)
let rec SNat = function
  | 0u -> SZero
  | n -> SSucc (SNat (n - 1u))
let rec SSuccN n s =
  match n with
    | 0u -> s
    | n -> SSuccN (n - 1u) (SSucc s)

//[<AutoOpen>]
module StageOp = 
  begin
    
    let lmap f = function
      | StageInequality (l, r) -> StageInequality (f l, r)
    
    let rmap f = function
      | StageInequality (l, r) -> StageInequality (l, f r)

    let bimap f = function
      | StageInequality (l, r) -> StageInequality (f l, f r)
    
    let substIn name svl ssbj =
      let rec sub = function
        | SVar n when n = name -> svl
        | SSucc s -> SSucc (sub s)
        | SAdd (s, t) -> SAdd (sub s, sub t)
        | x -> x
      in sub ssbj

    let rec fvOf = function
      | SVar v -> set [v]
      | SSucc s -> fvOf s
      | SAdd (s, t) -> Set.union (fvOf s) (fvOf t)
      | _ -> set []

    let tryGetDiff a b =
      let rec d = function
        | (x, y) when x = y -> Some id
        | (SSucc x, SSucc y) -> d (x, y)
        | (SZero, y) -> Some (fun _ -> y)
        | (x, SInf) -> Some (fun _ -> SInf)
        | (x, SSucc (SSucc y)) ->
          match ((x, SSucc y) |> d) with
            | Some f -> Some (fun x -> SSucc (f x))
            | None -> None
        | (x, SSucc y) when x = y -> Some (fun x -> SSucc x)
        | _ -> None
      in d (a, b)

    let rec isNat = function
      | SSucc s -> isNat s
      | SAdd (s, t) -> isNat s && isNat t
      | SZero -> true
      | _ -> false

    let toNat s = 
      let rec f = function
        | SZero -> 0u
        | SSucc s -> 1u + f s
        | SAdd (s, t) -> f s + f t
        | _ -> failwith "not nat"
      in
      f s

    let prettify s =
      let rec p = function
        | x when isNat x -> toNat x |> SNat
        | SAdd (SSucc s, t) -> SSucc (SAdd (p s, p t) |> p)
        | SAdd (s, SSucc t) -> SSucc (SAdd (p s, p t) |> p)
        | SAdd (s, t) when isNat s -> p t |> SSuccN (toNat s)
        | SAdd (s, t) when isNat t -> p s |> SSuccN (toNat t)
        | SAdd (s, t) -> SAdd (p s, p t)
        | SSucc s -> SSucc (p s)
        | x -> x
      in p s
    
    let check sieq =
      let rec f = function
        | (SSucc s, SSucc t) -> f (s, t)
        | (SZero, _) | (_, SInf) -> []
        | (SAdd (s, SZero), t) | (SAdd (SZero, s), t) 
        | (s, SAdd (t, SZero)) | (s, SAdd (SZero, t)) -> f (s, t)
        | (SAdd (s, SSucc t), u) | (SAdd (SSucc s, t), u) -> f (SSucc (SAdd (s, t)), u)
        | (s, SAdd (t, SSucc u)) | (s, SAdd (SSucc t, u)) -> f (s, SSucc (SAdd (t, u)))
        | (SAdd (s, x), SAdd (t, y)) | (SAdd (x, s), SAdd (t, y))
        | (SAdd (s, x), SAdd (y, t)) | (SAdd (x, s), SAdd (y, t)) when ((tryGetDiff x y |> Option.isSome) || (tryGetDiff y x |> Option.isSome)) ->
          match (tryGetDiff x y) with
            | Some g -> (s, g t) |> f
            | None -> 
              match (tryGetDiff y x) with
                | Some g -> (g s, t) |> f
                | None -> [ (SAdd (s, x), SAdd (t, y)) ]
        | (SVar v, SVar u) when v = u -> []
        | (s, SVar v) when (fvOf s |> Set.contains v) -> failwith "inconsistent"
        | (SVar v, t) when (fvOf t |> Set.contains v) -> []
        | (a, b) -> [ (a, b) ]
      in
      try
        let (StageInequality (a, b)) = sieq in
        let r = f (prettify a, prettify b) |> List.map StageInequality in
        if r = [sieq] then Some []
        else r |> List.map (bimap prettify) |> Some
      with
        | _ -> None

    let unify cs =
      let rec u = function
        | x :: y :: rest when x = y -> x :: rest |> u
        | StageInequality (sx, sy) :: rest when sx = sy -> u rest
        | StageInequality (SSucc sx, SSucc sy) :: rest -> (sx <=^ sy) :: rest |> u
        | StageInequality (SVar x, sy) :: rest when (fvOf sy |> Set.contains x |> not) ->
          let c = SVar x <=^ sy in
          match (check c) with
            | Some xs ->
              let f xs = xs |> List.map (rmap (substIn x sy)) in
              [c |> bimap prettify] |> List.append (List.append xs rest |> f |> u) 
            | None -> failwith "unify failed 1"
        | StageInequality (sx, SVar y) :: rest when (fvOf sx |> Set.contains y |> not) ->
          let c = sx <=^ SVar y in
          match (check c) with
            | Some xs ->
              let f xs = xs |> List.map (lmap (substIn y sx)) in
              [c |> bimap prettify] |> List.append (List.append xs rest |> f |> u) 
            | None -> failwith "unify failed 2"
        | StageInequality (SVar x, sy) :: rest -> (SVar x <=^ sy |> bimap prettify) :: u rest
        | StageInequality (_, SVar _) :: _ & xs ->
          printfn "%A" xs;
          failwith "inconsistent"
        | StageInequality (sx, sy) :: rest ->
          let c = sx <=^ sy in
          match (check c) with
            | Some xs -> [c |> bimap prettify] |> List.append (List.append xs rest |> u)
            | None -> failwith "unify failed 3"
        | [] -> []
      in u cs
    
    let eval n xs =
      List.append xs [n] |> unify

    let cstr = [
      SVar "w" +^ SNat 3u <=^ SVar "x";
      SVar "x" <=^ SVar "y" +^ SNat 1u;
      SVar "y" <=^ SVar "z" +^ SNat 1u;
      SVar "z" <=^ SVar "w" +^ SNat 1u;
      SVar "v" <=^ SVar "x" +^ SVar "y" +^ SVar "z"
    ]

    let f () = unify (unify (List.rev cstr)) |> List.iter (to_s >> printfn "%s")

    ()
  end