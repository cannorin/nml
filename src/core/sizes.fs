module nml.Sizes
open Microsoft.FSharp.Collections

let inline to_s x = x.ToString()

type Size =
  | SVar of string
  | SZero
  | SInf
  | SSucc of Size
  | SAdd of Size * Size
  override this.ToString () =
    let rec p i = function
      | SSucc s -> p (i + 1u) s
      | SZero -> to_s i
      | s -> sprintf "%s + %i" (to_s s) i
    in
    match this with
      | SVar v -> v
      | SZero -> "0" | SInf -> "Inf"
      | SSucc s -> SSucc s |> p 0u
      | SAdd (s, t) -> sprintf "(%s + %s)" (to_s s) (to_s t)

type SizeInequality = 
  | SizeInequality of Size * Size
  override this.ToString () =
    let (SizeInequality (s, t)) = this in
    sprintf "[%s <= %s]" (to_s s) (to_s t)

let (<=^) x y = SizeInequality (x, y)
let (+^) x y = SAdd (x, y)
let rec SNat = function
  | 0u -> SZero
  | n -> SSucc (SNat (n - 1u))
let rec SSuccN n s =
  match n with
    | 0u -> s
    | n -> SSuccN (n - 1u) (SSucc s)

//[<AutoOpen>]
module SizeOp = 
  begin
    
    let lmap f = function
      | SizeInequality (l, r) -> SizeInequality (f l, r)
    
    let rmap f = function
      | SizeInequality (l, r) -> SizeInequality (l, f r)

    let bimap f = function
      | SizeInequality (l, r) -> SizeInequality (f l, f r)
    
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
        | SAdd (SInf, _) | SAdd (_, SInf) | SSucc SInf -> SInf
        | SAdd (SZero, t) | SAdd (t, SZero) -> t
        | SAdd (SSucc s, t) -> SSucc (SAdd (p s, p t) |> p)
        | SAdd (s, SSucc t) -> SSucc (SAdd (p s, p t) |> p)
        | SAdd (s, t) when isNat s -> p t |> SSuccN (toNat s)
        | SAdd (s, t) when isNat t -> p s |> SSuccN (toNat t)
        | SAdd (s, t) -> SAdd (p s, p t)
        | SSucc s -> SSucc (p s)
        | x -> x
      in p s
 
    let substIn name svl ssbj =
      let rec sub = function
        | SVar n when n = name -> svl
        | SSucc s -> SSucc (sub s)
        | SAdd (s, t) -> SAdd (sub s, sub t)
        | x -> x
      in sub ssbj |> prettify
   
    let check sieq =
      let rec f = function
        | (x, y) when x = y -> []
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
        | (SVar _, _) & (l, r) | (_, SVar _) & (r, l) -> [ (l, r) ]
        | (SInf, SSucc t) -> f (SInf, t)
        | (_, SZero) | (SInf, _) -> failwith "inconsistent"
        | (a, b) -> [ (a, b) ]
      in
      try
        let (SizeInequality (a, b)) = sieq in
        let r = f (prettify a, prettify b) |> List.map SizeInequality in
        if r = [sieq] then Some []
        else r |> List.map (bimap prettify) |> Some
      with
        | _ -> None

    let unify cs =
      let rec u = function
        | x :: y :: rest when x = y -> x :: rest |> u
        | SizeInequality (sx, sy) :: rest when sx = sy -> u rest
        | SizeInequality (SSucc sx, SSucc sy) :: rest -> (sx <=^ sy) :: rest |> u
        | SizeInequality (SVar x, sy) :: rest when (fvOf sy |> Set.contains x |> not) ->
          let c = SVar x <=^ sy in
          match (check c) with
            | Some xs ->
              let f xs = xs |> List.map (rmap (substIn x sy)) in
              [c |> bimap prettify] |> List.append (List.append xs rest |> f |> u) 
            | None -> failwith "unify failed 1"
        | SizeInequality (sx, SVar y) :: rest when (fvOf sx |> Set.contains y |> not) ->
          let c = sx <=^ SVar y in
          match (check c) with
            | Some xs ->
              let f xs = xs |> List.map (lmap (substIn y sx)) in
              [c |> bimap prettify] |> List.append (List.append xs rest |> f |> u) 
            | None -> failwith "unify failed 2"
        | SizeInequality (SVar x, sy) :: rest -> (SVar x <=^ sy |> bimap prettify) :: u rest
        | SizeInequality (_, SVar _) :: _ & xs ->
          printfn "%A" xs;
          failwith "inconsistent"
        | SizeInequality (sx, sy) :: rest ->
          let c = sx <=^ sy in
          match (check c) with
            | Some xs -> [c |> bimap prettify] |> List.append (List.append xs rest |> u)
            | None -> 
              printfn "%s" (to_s c);
              failwith "unify failed 3"
        | [] -> []
      in u cs
    
  end

