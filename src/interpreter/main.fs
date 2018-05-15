open nml
open nml.Ast
open nml.Parser
open nml.Typer
open nml.Evaluation
open nml.Contexts
open nml.Builtin
open Microsoft.FSharp.Collections
open System
open System.IO
open Mono.Terminal

let editor = new LineEditor ("nml", 300)
editor.TabAtStartCompletes <- false
let inline scan prompt = editor.Edit(prompt, "")

let tryRun ctx fn input =
  try
    let (tls, _) = NmlParser.parseToplevelWithFileName fn input |> ParserUtils.toToplevelAndNewContext ctx ["repl"]
    let rec e ctx runDefer t =
      match (t |> next (ctx |> Context.termMap snd)) with
        | Halted result -> result
        | Reducible t ->
          if runDefer then
            cprintfn ConsoleColor.DarkGray "----> %s" (to_s t)
            UTmDefer (e ctx true t)
          else UTmDefer t
    let (ctx', tls') =
      let rec evalTop ctx newtls =
        function
          | [] -> (ctx, newtls)
          | ct :: rest ->
            let inline id2 _ t = t
            let newtl =
              match ct with
                | TopTermDef (name, (ty, tm), info) ->
                  let tm' = e ctx false tm
                  TopTermDef (name, (ty, tm'), info)
                | TopDo ((ty, tm), info) ->
                  let tm' = e ctx true tm
                  cprintfn ConsoleColor.DarkGray "----> %s" (to_s tm')
                  TopDo ((ty, tm'), info)
                | TopOpen _ -> ct
                | TopModule (name, subtops, info) ->
                  let subtops' = subtops |> evalTop ctx [] |> snd |> List.rev
                  TopModule (name, subtops', info) 
                | tydef ->
                  tydef
            rest |> evalTop (ctx |> Context.addToplevels [newtl] id2) (newtl :: newtls)
      evalTop ctx [] tls
    if tls' |> List.forall (function | TopDo _ -> true | _ -> false) |> not then
      printfn ""
    tls' |> List.filter (function | TopDo _ -> false | _ -> true)
         |> TopLevel<_>.print
         |> cprintfn ConsoleColor.DarkGray "%s"
    ctx'
  with 
    | ParserFailed msg ->
      printfn "PARSER FAILED: %s" msg
      ctx
    | TyperFailed e ->
      Typer.printTypeError e
      ctx
    | e -> 
      printfn "NATIVE ERROR: %s" e.Message 
      ctx

let rec repl ctx prompt count lines =
  let currentLine = scan prompt |> String.trim
  if String.IsNullOrWhiteSpace currentLine then
    repl ctx prompt count lines
  else if currentLine |> String.contains ";;" |> not then
    repl ctx "- " count (currentLine :: lines)
  else
    let currentLine =
      currentLine |> String.splitBy ";;" |> String.removeEmptyEntries |> Array.tryHead ?| ""
    let lines = currentLine :: lines
    let input = lines |> List.rev |> String.concat Environment.NewLine
    let ctx' = input |> tryRun ctx (sprintf "repl#%i" count)
    printfn ""
    repl ctx' "> " (count + 1) []

[<EntryPoint>]
let main argv =
  match (argv |> Array.toList) with
    | "--quiet" :: filename :: _
    | filename :: _ when File.Exists filename ->
      let code = File.ReadAllText filename in
      tryRun defaultContext filename code |> ignore
    | [] -> 
      printfn "nml REPL ver.???";
      printfn "";
      printfn "type 'exit 0;;' to exit.";
      printfn "";
      repl defaultContext "> " 0 []
    | filename :: _ -> failwith "file doesn't exist"
    | _ -> ()
  0

