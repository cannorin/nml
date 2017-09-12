[<AutoOpen>]
module nml.Prelude

open Microsoft.FSharp.Collections

type nat = uint32

[<CustomEquality; NoComparison>]
type EqualityNull<'T> = 
  | Value of 'T
  | Null
  override x.Equals(yobj) =
    match yobj with
      | :? EqualityNull<'T> as y -> true
      | _ -> false
  override x.GetHashCode() = 0

[<CustomEquality; NoComparison>]
type NameCompared<'T> = 
  { value: 'T; name: string }
  override x.Equals(yobj) =
    match yobj with
      | :? NameCompared<'T> as y -> x.name = y.name
      | _ -> false
  override x.GetHashCode() = 0

module Map = begin
  let map2 f m =
    m |> Map.toList |> List.map f |> Map.ofList

  let keys m =
    m |> Map.toList |> List.map fst |> Set.ofList
end


let inline to_s x = x.ToString()
let inline (?|) x y = defaultArg x y

let inline fstOf3 (x, _, _) = x
let inline sndOf3 (_, y, _) = y
let inline trdOf3 (_, _, z) = z

let inline cprintfn color p x =
  System.Console.ForegroundColor <- color;
  printfn p x;
  System.Console.ResetColor ()

let genUniq ng =
  let a = ng % 26 in
  let p = ng / 26 in
  (new string [| for i in 0..p do yield [|'a'..'z'|].[a] |], ng + 1)

let rec genUniqs uniq i =
  if i > 0 then
    let (x, nu) = genUniq uniq in
    let (rest, fu) = genUniqs nu (i - 1) in
    (x :: rest, fu)
  else
    ([], uniq)

let inline times i f =
  let rec t i f acc =
    if i <= 0 then acc else t (i - 1) f (f acc)
  in t i f

let inline is_op s = s |> String.forall (fun c -> System.Char.IsLetterOrDigit c || c = '_') |> not

let inline handle_op s =
  if (is_op s) then
    "(" + s + ")"
  else
    s

let inline listen x =
  printfn "%s" (to_s x);
  x

let inline printsn x =
  printfn "%s" (to_s x)

()
