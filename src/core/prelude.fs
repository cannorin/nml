(*
The X11 License
prelude.fs - my prelude
Copyright(c) 2018 cannorin
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*)

[<AutoOpen>]
module Prelude

open System
open System.Text.RegularExpressions

let inline to_s x = x.ToString()

let inline (?|) opt df = defaultArg opt df

let inline undefined (x: 'a) : 'b = NotImplementedException(to_s x) |> raise

let inline reraise' ex = System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(ex).Throw(); failwith "impossible"

let private ccl (fc: ConsoleColor) =
  Console.ForegroundColor <- fc;
  { new IDisposable with
      member x.Dispose() = Console.ResetColor() }

let cprintf color format =
  Printf.kprintf (fun s -> use c = ccl color in printf "%s" s) format

let cprintfn color format =
  Printf.kprintf (fun s -> use c = ccl color in printfn "%s" s) format

let (|Regex|_|) pattern input =
  let m = Regex.Match(input, pattern)
  if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
  else None

let (|DefaultValue|) dv x =
  match x with
    | Some v -> v
    | None -> dv

module Flag =
  let inline combine (xs: ^flag seq) : ^flag
    when ^flag: enum<int> =
      xs |> Seq.fold (|||) (Unchecked.defaultof< ^flag >)

  let inline is (x: ^flag) (flags: ^flag) : bool
    when ^flag: enum<int> =
      (x &&& flags) = x 

module Number =
  open System.Globalization

  let inline tryParse< ^T when ^T: (static member TryParse: string -> ^T byref -> bool) > str : ^T option =
    let mutable ret = Unchecked.defaultof<_> in
    if (^T: (static member TryParse: string -> ^T byref -> bool) (str, &ret)) then
      Some ret
    else
      None

  let inline tryParseWith< ^T when ^T: (static member TryParse: string -> NumberStyles -> IFormatProvider -> ^T byref -> bool) > str styleo formato : ^T option =
    let mutable ret = Unchecked.defaultof<_> in
    let style = styleo ?| NumberStyles.None in
    let format = formato ?| CultureInfo.InvariantCulture in
    if (^T: (static member TryParse: string -> NumberStyles -> IFormatProvider -> ^T byref -> bool) (str, style, format, &ret)) then
      Some ret
    else
      None

module String =
  open System.Text
  open System.Globalization

  let inline startsWith (s: ^a) (str: ^String) : bool = (^String: (member StartsWith: ^a -> bool) str, s)

  let inline endsWith (s: ^a) (str: ^String) : bool = (^String: (member EndsWith: ^a -> bool) str, s)

  let inline contains (s: ^a) (str: ^String) : bool = (^String: (member IndexOf: ^a -> int) str, s) <> -1

  let inline findIndex (q: ^T) (str: ^String) = 
    (^String: (member IndexOf: ^T -> int) (str, q))

  let inline findIndexAfter (q: ^T) i (str: ^String) = 
    (^String: (member IndexOf: ^T -> int -> int) (str, q, i))

  let inline findLastIndex (q: ^T) (str: ^String) = 
    (^String: (member LastIndexOf: ^T -> int) (str, q))

  let inline findLastIndexAfter (q: ^T) i (str: ^String) = 
    (^String: (member LastIndexOf: ^T -> int -> int) (str, q, i))

  let inline insertAt s i (str: string) = str.Insert(i, s)

  let inline removeAfter i (str: string) = str.Remove i

  let inline remove startIndex endIndex (str: string) = str.Remove(startIndex, endIndex)

  let inline substringAfter i (str: string) = str.Substring i

  let inline substring startIndex endIndex (str: string) = str.Substring(startIndex, endIndex)

  let inline normalize (nfo: NormalizationForm option) (str: string) = 
    match nfo with Some nf -> str.Normalize nf | None -> str.Normalize()

  let inline toLower (cio: CultureInfo option) (str: string) =
    match cio with Some ci -> str.ToLower ci | None -> str.ToLowerInvariant()

  let inline toUpper (cio: CultureInfo option) (str: string) =
    match cio with Some ci -> str.ToUpper ci | None -> str.ToUpperInvariant()

  let inline padLeft i (str: string) = str.PadLeft i

  let inline padLeftBy i c (str: string) = str.PadLeft(i, c)
  
  let inline padRight i (str: string) = str.PadRight i

  let inline padRightBy i c (str: string) = str.PadRight(i, c)

  let inline trim (str: string) = str.Trim()

  let inline replace (before: ^T) (after: ^T) (s: ^String) =
    (^String: (member Replace: ^T -> ^T -> ^String) (s, before, after))

  let inline splitBy (sp: ^T) (s: ^String) =
    (^String: (member Split: ^T array -> StringSplitOptions -> ^String array) (s, [|sp|], StringSplitOptions.None))

  let inline splitBySeq (sp: ^T seq) (s: ^String) =
    (^String: (member Split: ^T array -> StringSplitOptions -> ^String array) (s, Seq.toArray sp, StringSplitOptions.None))

  let inline removeEmptyEntries (sp: string array) = sp |> Array.filter (String.IsNullOrEmpty >> not)

  let inline toChars (s: string) = s.ToCharArray()

  let inline ofChars (cs: char seq) = new String(cs |> Seq.toArray)

  let inline nth i (str: string) = str.[i]

  let inline rev (str: string) = 
    new String(str.ToCharArray() |> Array.rev)

  let inline private whileBase pred act str =
    if String.IsNullOrEmpty str then
      ""
    else
      let mutable i = 0
      while i < String.length str && str |> nth i |> pred do i <- i + 1 done
      if i = 0 then ""
      else str |> act i

  let inline take i str =
    if i = 0 then ""
    else if i >= String.length str then str
    else removeAfter i str

  let inline skip i str =
    if i = 0 then str
    else if i >= String.length str then ""
    else substringAfter i str

  let inline takeWhile predicate (str: string) =
    whileBase predicate take str

  let inline skipWhile predicate (str: string) =
    whileBase predicate skip str

let inline (!!) (x: Lazy<'a>) = x.Value

module Lazy =
  let inline run (x: Lazy<'a>) = x.Value
  
  let inline bind (f: 'a -> Lazy<'b>) (x: Lazy<'a>) =
    lazy (!!x |> f) |> run

  let inline map (f: 'a -> 'b) (x: Lazy<'a>) =
    lazy (!!x |> f)

  let inline flatten (x: Lazy<Lazy<'a>>) = lazy (!!(!!x))

[<Struct>]
type LazyBuilder =
  member inline this.Bind(m, f) = Lazy.bind f m
  member inline this.Return x = lazy x
  member inline this.ReturnFrom lx = lx
  member inline this.Zero () = lazy ()
  member inline this.Combine(a, _) = a
  member inline this.Delay f = lazy (!!f())

let doLazy = LazyBuilder ()

module List = 
  let rec takeToEnd n xs =
    if List.length xs > n then
      (xs |> List.take n) :: takeToEnd n (xs |> List.skip n)
    else
      [xs]

module Tuple =
  let inline map2 f g (x, y) = (f x, g y)
  let inline map3 f g h (x, y, z) = (f x, g y, h z)
  let inline map4 f g h i (x, y, z, w) = (f x, g y, h z, i w)
  let inline map5 f g h i j (x, y, z, w, v) = (f x, g y, h z, i w, j v)

module Result =
  let inline toOption res =
    match res with
      | Ok x -> Some x
      | Error _ -> None
  
  let inline toChoice res =
    match res with
      | Ok x -> Choice1Of2 x
      | Error e -> Choice2Of2 e

  let inline ofChoice cic =
    match cic with
      | Choice1Of2 x -> Ok x
      | Choice2Of2 e -> Error e

  let inline get res =
    match res with
      | Ok x -> x
      | Error e -> reraise' e

  let inline defaultWith f res =
    match res with
      | Ok x -> x
      | Error e -> f e

  let inline defaultValue y res =
    match res with
      | Ok x -> x
      | Error _ -> y

module PerformanceMeasurement =
  let inline time repeats task =
    let times = 
      seq {
        for _ in 1 .. repeats do
          let stopWatch = System.Diagnostics.Stopwatch.StartNew() in
          do task () |> ignore;
          do stopWatch.Stop();
          yield stopWatch.Elapsed.TotalMilliseconds
      }
    in
    printfn "%A: %fms" task (Seq.average times);
    task ()

module Async =
  open System.Threading
  open System.Threading.Tasks
  open Microsoft.FSharp.Control

  let inline run x = Async.RunSynchronously x

  let withTimeout (timeout : TimeSpan) a =
    async {
      try
        let! child = Async.StartChild(a, int timeout.TotalMilliseconds) in
        let! result = child in
        return Some result
      with
        | :? TimeoutException -> return None
    }

type TypeWrapper<'T> = struct end
type ty<'T> = TypeWrapper<'T>
let inline ty<'T> = Unchecked.defaultof<ty<'T>>

type MeasureWrapper< [<Measure>] 'm > = struct end
type measure< [<Measure>] 'm > = MeasureWrapper<'m>
let inline measure< [<Measure>] 'm > = Unchecked.defaultof<measure<'m>>

let inline intWithMeasure (_: measure<'m>) (i: ^i) : int<'m> =
  (int i) * LanguagePrimitives.Int32WithMeasure<'m> 1

let inline floatWithMeasure (_: measure<'m>) (i: ^i) : float<'m> =
  (float i) * LanguagePrimitives.FloatWithMeasure<'m> 1.0

module Path =
  open System.IO
  let makeRelativeTo parentDir file =
    let filePath = new Uri(file)
    let path =
      new Uri (
        if (parentDir |> String.endsWith (to_s Path.DirectorySeparatorChar) |> not) then
          sprintf "%s%c" parentDir Path.DirectorySeparatorChar
        else
          parentDir
      )
    Uri.UnescapeDataString(path.MakeRelativeUri(filePath) |> to_s |> String.replace '/' Path.DirectorySeparatorChar)

 