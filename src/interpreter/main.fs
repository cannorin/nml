open nml
open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Evaluation
open nml.UniversalContext
open nml.Builtin
open Microsoft.FSharp.Collections
open System
open System.IO
open Mono.Terminal

let editor = new LineEditor ("nml", 300)
let inline scan prompt = editor.Edit(prompt, "")

let tryRun ctx code quiet =
  try
    let e = parseTerm code in
    let e' = e |> toUntypedTerm ctx in
    let (e'', te) = inferWithContext_dbg ctx e' false in
    cprintfn ConsoleColor.DarkGray "type: %s" (to_s te);
    let rec loop t i =
      let t' = t |> eval (ctx |> toEvalContext) in
      if (not quiet) then cprintfn ConsoleColor.DarkGray "----> %s" (to_s t');
      match (t' |> next (ctx |> toEvalContext)) with
        | Reducible t'' -> loop t'' (i + 1)
        | Halted -> if quiet then cprintfn ConsoleColor.DarkGray "----> %s" (to_s t') else ()
    in loop e'' 0
  with
    | ParserFailed msg -> printfn "PARSER FAILED: %s" msg
    | TyperFailed tf -> printTyperErr tf
    | e -> printfn "NATIVE ERROR: %s" e.Message

let rec loop ctx inc =
  let i =
    match inc with
      | Some x ->
        x + scan "- ";
      | None ->
        scan "> "
  in
  if (String.IsNullOrWhiteSpace i) then
    loop ctx inc
  else if (not <| i.Trim().EndsWith ";;") then
    loop ctx (Some (i + "\n"))
  let i = i.Trim() in
  let i = i.Remove(i.Length - 2, 2) in
  if (String.length i = 0) then
    loop ctx None
  else if (i = "showVars") then
    ctx |> printContext;
    printfn "";
    loop ctx None
  else
    tryRun ctx i false
  printfn "";
  loop ctx None

[<EntryPoint>]
let main argv =
  match (argv |> Array.toList) with
    | "--quiet" :: filename :: _
    | filename :: _ when File.Exists filename ->
      let code = File.ReadAllText filename in
      let ctx = defaultContext in
      tryRun ctx code (argv.[0] = "--quiet")
    | [] -> 
      printfn "nml REPL ver.???";
      printfn "";
      printfn "type <term>;; to execute a term.";
      printfn " term := 0, 1, .. / true / false / (t, t, ..) / [t; t; ..]";
      printfn "       / x / t t / t; t / fun x y .. -> t / fun () -> t ";
      printfn "       / let x = t in t / let f x .. = t in t / let f () = t in t";
      printfn "       / if t then t else t / match t with pattern -> t | pattern -> t ..";
      printfn "       / fixpoint f of pattern -> t  | pattern -> t ..";
      printfn "       / <( t )> / let! x = t in t / t !; t";
      printfn "";
      printfn "type 'showVars;;' to show predefined functions.";
      printfn "example: let! x = readNat () in";
      printfn "         let! y = readNat () in";
      printfn "         print (x + y);;";
      printfn "";
      loop defaultContext None
    | filename :: _ -> failwith "file doesn't exist"
    | _ -> ()
  0

