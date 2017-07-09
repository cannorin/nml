[<AutoOpen>]
module nml.Prelude

open Mono.Terminal

let inline (?|) x y = defaultArg x y

let inline cprintfn color p x =
  System.Console.ForegroundColor <- color;
  printfn p x;
  System.Console.ResetColor ()

let editor = new LineEditor ("nml", 300)
let inline scan prompt = editor.Edit(prompt, "")

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


()
