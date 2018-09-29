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
open FSharp.CommandLine

let editor = new LineEditor ("nml", 300)
editor.TabAtStartCompletes <- true
editor.HeuristicsMode <- "csharp"
let inline scan prompt = editor.Edit(prompt, "")

let tryRun (ctx: EvalContext) fn quiet input =
  try
    let tls, _ =
      NmlParser.parseToplevelWithFileName fn input
      |> ParserUtils.toToplevelAndNewContextEval ctx ["repl"]
    let (ctx', tls') =
      let rec evalTop (ctx: EvalContext) newtls =
        function
          | [] -> (ctx, newtls)
          | ct :: rest ->
            let inline id2 _ t = t
            let newtl =
              match ct with
                | TopTermDef _ -> ct
                | TopDo ((ty, tm), info) ->
                  if not quiet then
                    cprintfn ConsoleColor.DarkGray "type: %s" (to_s ty)
                  
                  let tm' =
                    eval' (ctx |> Context.termMap snd)
                    <| With.noinfo (TmRun (TimeInf, tm))
                  
                  if not quiet then
                    cprintfn ConsoleColor.DarkGray "====> %s" (to_s tm')
                  TopDo ((ty, tm'), info)
                | TopOpen _ -> ct
                | TopModule (name, subtops, info) ->
                  let subtops' = subtops |> evalTop ctx [] |> snd |> List.rev
                  TopModule (name, subtops', info) 
                | tydef ->
                  tydef
            rest |> evalTop (ctx |> Context.addToplevels [newtl] id2) (newtl :: newtls)
      evalTop ctx [] tls
    tls' |> List.filter (function | TopDo _ -> false | _ -> true)
         |> List.rev
         |> TopLevel<_>.print
         |> function 
              | s when String.IsNullOrWhiteSpace s -> () 
              | s -> cprintfn ConsoleColor.DarkGray "%s" s
    ctx'
  with 
    | ParserFailedWithPos (msg, src) ->
      printfn "PARSER FAILED: (%A): %s" src msg
      ctx
    | ParserFailed msg ->
      printfn "PARSER FAILED: %s" msg
      ctx
    | TyperFailed e ->
      Typer.printTypeError e
      ctx
    (*
    | e -> 
      printfn "NATIVE ERROR: %s" e.Message 
      ctx
    *)

type Completion = Mono.Terminal.LineEditor.Completion
type AutoCompleteHandler = Mono.Terminal.LineEditor.AutoCompleteHandler

let cmplCtx = ref Context.Empty
let listener text pos =
  let prefix, cmpl =
    let names ctx =
      ctx
        |> List.choose (
          function
            TermContext (name, _)
          | ModuleContext (name, _) -> Some [name]
          | TypeContext (_, TyScheme (_, NotTemporal (TyDataType(_, _, { cstrs = cstrs })))) ->
            cstrs |> List.map (fun c -> c.name) |> Some
          | _ -> None
        ) 
        |> List.concat

    if String.IsNullOrWhiteSpace text then
      "", names !cmplCtx |> Array.ofList
    else
      let pf =
        text |> String.take (pos)
             |> String.rev
             |> String.takeWhile (fun c -> "._" |> String.contains c || Char.IsLetterOrDigit c)
             |> String.rev
      if pf |> String.contains "." then
        let mname =
          if pf |> String.endsWith "." then pf |> String.take (String.length pf - 1) else pf
        pf,
        !cmplCtx
          |> Context.findModuleItems (mname |> String.splitBy '.' |> List.ofArray)
          |> names
          |> Array.ofList
      else
        pf, 
        names !cmplCtx
          |> List.filter (String.startsWith pf)
          |> List.map (String.skip (String.length pf))
          |> Array.ofList
  new Completion(prefix, cmpl)
editor.AutoCompleteEvent <- new AutoCompleteHandler(listener)

let rec repl ctx prompt quiet count lines =
  cmplCtx := ctx
  let currentLine = scan prompt |> String.trim
  if String.IsNullOrWhiteSpace currentLine then
    repl ctx prompt quiet count lines
  else if currentLine |> String.contains ";;" |> not then
    repl ctx "- " quiet count (currentLine :: lines)
  else
    let currentLine =
      currentLine |> String.splitBy ";;" |> String.removeEmptyEntries |> Array.tryHead ?| ""
    let lines = currentLine :: lines
    let input = lines |> List.rev |> String.concat Environment.NewLine
    let ctx' = input |> tryRun ctx (sprintf "repl#%i" count) quiet
    printfn ""
    repl ctx' "> " quiet (count + 1) []

open Options
open Commands
 
let quietFlag =
  commandFlag {
    names [ "quiet"; "q" ]
    description "do not print verbose informations"
  }

let loadOption =
  commandOption {
    names [ "load"; "l" ]
    description "source files to load"
    takes (format("%s").withNames ["filename"])
    suggests (fun _ -> [CommandSuggestion.Files (Some "*.nml")])
  }

let mainCommand =
  command {
    name "nmli"
    description "nml interpreter"
    opt quiet in
      quietFlag |> CommandOption.zeroOrExactlyOne
                |> CommandOption.whenMissingUse false
    opt loads in 
      loadOption |> CommandOption.zeroOrMore
    let! args = Command.args

    let initCtx =
      loads |> List.fold (fun state fn -> tryRun state fn true (File.ReadAllText fn)) 
                         (defaultContext
                          |> Context.termMap (fun tm -> 
                              Term.getType tm |> Typer.generalizeAllFV, Term.eraseType tm
                             )
                         )

    do 
      match args with
        | [] ->
          printfn "nml REPL ver.???";
          printfn "";
          printfn "type 'exit 0;;' to exit.";
          printfn "";
          repl initCtx "> " quiet 0 [] 
        | filename :: rest when File.Exists filename ->
          let code = File.ReadAllText filename in
          code |> tryRun initCtx filename quiet |> ignore
        | filename :: _ -> failwithf "file '%s' doesn't exist" filename
        | [] -> ()
    return 0
  }

[<EntryPoint>]
let rec main argv =
  Command.runAsEntryPoint argv mainCommand
