open nml
open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Evaluation
open nml.Contexts
open nml.Builtin
open Microsoft.FSharp.Collections
open System
open System.IO
open Mono.Terminal
open System.Text
open nml.Parser
open nml.Parser

let editor = new LineEditor ("nml", 300)
let inline scan prompt = editor.Edit(prompt, "")

let rec repl lines ctx prompt =
  let currentLine = scan prompt |> String.trim
  if String.IsNullOrWhiteSpace currentLine then
    repl lines ctx prompt
  else
    let lines = currentLine :: lines
    let input = lines |> List.rev |> String.concat Environment.NewLine
    let reset = ([], ctx, "> ")
    let (lines', ctx', prompt') =
      try
        let (tls, _) = TopLevelParser.parse input |> TopLevelParser.toToplevelAndNewContext ctx ["repl"]
        let rec e ctx runDefer t =
          match (t |> next (ctx |> Context.termMap snd)) with
            | Halted result -> result
            | Reducible t ->
              if runDefer then UTmDefer (e ctx true t) else UTmDefer t
        let (ctx', tls') =
          let rec evalTop ctx newtls =
            function
              | [] -> (ctx, newtls)
              | ct :: rest ->
                let inline id2 _ t = t
                let newtl =
                  match ct with
                    | TopLet (name, (ty, tm)) ->
                      let tm' = e ctx false tm
                      TopLet (name, (ty, tm'))
                    | TopDo (ty, tm) ->
                      let tm' = e ctx true tm
                      cprintfn ConsoleColor.DarkGray "----> %s" (to_s tm)
                      TopDo (ty, tm')
                    | TopOpen name -> TopOpen name
                    | TopModule (name, subtops) ->
                      let subtops' = subtops |> evalTop ctx [] |> snd |> List.rev
                      TopModule (name, subtops') 
                    | tydef ->
                      tydef
                rest |> evalTop (ctx |> Context.addToplevels [newtl] id2) (newtl :: newtls)
          evalTop ctx [] tls
        TopLevel.print tls' |> printfn "%s"
        ([], ctx', "> ")
      with 
        | ParserFailedAtEof -> (lines, ctx, "- ")
        | ParserFailed msg ->
          printfn "PARSER FAILED: %s" msg
          reset
        | TyperFailed (UnifyFailed (a, b, ut)) ->
          printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
          reset
        | TyperFailed (UnknownVar (n, _)) ->
          printfn "TYPER FAILED: '%s' is not defined (unknown variable)" (sprint_qualified n)
          reset
        | TyperFailed (NotMatchable (l, t, r)) ->
          printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r)
          reset
        | TyperFailed (TermWithMessage (f, t)) ->
          sprintf f (to_s t) |> printfn "TYPER FAILED: %s"
          reset
        | e -> 
          printfn "NATIVE ERROR: %s" e.Message 
          reset
    repl lines' ctx' prompt'

let inline debug () =

  let code = @"
let append xs ys =
  (
    fixpoint f of
      | [] -> ys
      | h :: t -> h :: f t
  ) xs
;;

let max x y = if x > y then x else y ;;

inductive Bst a =
    Node of a * Bst a * Bst a
  | Leaf
end

module Bst = begin
  let insert x = 
    fixpoint f of
      Leaf -> Node (x, Leaf, Leaf)
    | Node (y, left, right) ->
      if x < y then
        Node (y, f left, right)
      else
        Node (y, left, f right)
  ;;

  let contains x =
    fixpoint f of
      Leaf -> false
    | Node (y, left, right) ->
      if x < y then f left
      else if x = y then true
      else f right
  ;;

  let height =
    fixpoint f of
      Leaf -> 0
    | Node (_, left, right) ->
      1 + max (f left) (f right)
  ;;

  let itemsAtDepth depth tree =
    let f = 
      fixpoint f of
        Leaf -> fun _ -> []
      | Node (a, left, right) ->
        begin fun d ->
          if d = depth then
            [a]
          else
            append (f left (d+1)) (f right (d+1))
        end
    in f tree 0
  ;;

end
  

"

  repl [] defaultContext "> "
  (*
  let (toplevel, ctx) = 
    code |> TopLevelParser.parse |> TopLevelParser.toToplevelAndNewContext defaultContext []

  printfn "%s" (TopLevel<_>.print toplevel)
  Console.ReadLine() |> ignore
  *)


[<EntryPoint>]
let main argv =

#if DEBUG
  debug ()
  Environment.Exit 0;
#endif

  match (argv |> Array.toList) with
    //| "--quiet" :: filename :: _
    //| filename :: _ when File.Exists filename ->
    //  let code = File.ReadAllText filename in
    //  let ctx = defaultContext in
    //  tryRun ctx code (argv.[0] = "--quiet")
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

