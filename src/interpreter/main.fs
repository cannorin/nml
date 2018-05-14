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

let tryRun ctx input =
  try
    let (tls, _) = NmlParser.parseToplevel input |> ParserUtils.toToplevelAndNewContext ctx ["repl"]
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
    | TyperFailed (UnifyFailed (a, b, ut)) ->
      printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
      ctx
    | TyperFailed (UnknownVar (n, _)) ->
      printfn "TYPER FAILED: '%s' is not defined (unknown variable)" (sprint_qualified n)
      ctx
    | TyperFailed (NotMatchable (l, t, r)) ->
      printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r)
      ctx
    | TyperFailed (TermWithMessage (f, t)) ->
      sprintf f (to_s t) |> printfn "TYPER FAILED: %s"
      ctx
    | e -> 
      printfn "NATIVE ERROR: %s" e.Message 
      ctx

let rec repl lines ctx prompt =
  let currentLine = scan prompt |> String.trim
  if String.IsNullOrWhiteSpace currentLine then
    repl lines ctx prompt
  else if currentLine |> String.contains ";;" |> not then
    repl (currentLine :: lines) ctx "- "
  else
    let currentLine =
      currentLine |> String.splitBy ";;" |> String.removeEmptyEntries |> Array.tryHead ?| ""
    let lines = currentLine :: lines
    let input = lines |> List.rev |> String.concat Environment.NewLine
    let ctx' = input |> tryRun ctx
    printfn ""
    repl [] ctx' "> "

[<EntryPoint>]
let main argv =
  match (argv |> Array.toList) with
    | "--quiet" :: filename :: _
    | filename :: _ when File.Exists filename ->
      let code = File.ReadAllText filename in
      tryRun defaultContext code |> ignore
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
      repl [] defaultContext "> "
    | filename :: _ -> failwith "file doesn't exist"
    | _ -> ()
  0

