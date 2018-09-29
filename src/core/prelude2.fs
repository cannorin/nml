[<AutoOpen>]
module nml.Prelude

[<CustomEquality; NoComparison; StructuredFormatDisplay("EqualityNull"); Struct>]
type EqualityNull<'T> = 
  | EValue of 'T
  | ENull
  override x.Equals(yobj) =
    match yobj with
      | :? EqualityNull<'T> -> true
      | _ -> false
  override x.GetHashCode() = 0

module EqualityNull =
  let inline map f x = match x with EValue v -> EValue (f v) | ENull -> ENull
  let inline toOption x = match x with EValue v -> Some v | ENull -> None
  let inline ofOption o = match o with Some x -> EValue x | None -> ENull

[<CustomEquality; NoComparison; Struct>]
type NameCompared<'T> = 
  { value: 'T; name: string }
  override x.Equals(yobj) =
    match yobj with
      | :? NameCompared<'T> as y -> x.name = y.name
      | _ -> false
  override x.GetHashCode() = 0

[<Struct>]
type With<'T, 'U> =
  { item: 'T; info: 'U }
  override x.ToString() = to_s x.item

module With =
  let inline itemof x = x.item
  let inline infoof x = x.info
  let inline bind f x : With<_, _> = f x.item
  let inline map f x = { item = f x.item; info = x.info }
  let inline mapInfo f x = { item = x.item; info = f x.info }
  let inline sameInfoOf orig x = { item = x; info = orig.info }
  let inline info i x = { item = x; info = i }
  let inline noinfo x = { item = x; info = Unchecked.defaultof<_> }
 
let (|With|) x = With (x.item, x.info)
let (|Item|) x = Item x.item
let (|Info|) x = Info x.info

let (|When|_|) p x = if p x then Some When else None
let (|Choose|_|) p x = p x

let genUniq ng =
  let a = ng % 26 in
  let p = ng / 26 in
  (new string [| for i = 0 to p do yield [|'a'..'z'|].[a] |], ng + 1)

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

let inline is_op s = 
  s |> String.forall (fun c -> System.Char.IsLetterOrDigit c || c = '_') |> not

let inline handle_op s =
  if (is_op s) then
    "(" + s + ")"
  else
    s

let inline sprint_qualified xs =
  xs |> List.map handle_op |> String.concat "."

let inline namespaceof qualified = qualified |> List.take (List.length qualified - 1)

let inline tee x =
  printfn "%s" (to_s x);
  x

let inline indent i str =
  String.replicate i " " + str
