open nml
open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Evaluation
open nml.UniversalContext
open nml.Builtin
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Collections
open System

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
    try
      let e = parseTerm i in
      let (e', te) = inferWithContext ctx e in
      cprintfn ConsoleColor.DarkGray "type: %s" (to_s te);
      cprintfn ConsoleColor.DarkGray "eval: %s" (to_s e')
      let t = evalWithContext e' (ctx |> toEvalContext) in
      let rec l i = function
        | URun t ->
          cprintfn ConsoleColor.DarkGray "----> %s" (to_s t);
          evalWithContext (URun t) (ctx |> toEvalContext) |> l (i + 1)
        | t ->
          t |> to_s |> cprintfn ConsoleColor.DarkGray "----> %s"
      in l 0 t;
    with
      | ParserFailed msg -> printfn "PARSER FAILED: %s" msg
      | TyperFailed (UnifyFailed (a, b, ut)) ->
        printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
      | TyperFailed (UnknownVar (n, ctx)) ->
        printfn "TYPER FAILED: '%s' is not defined (unknown variable)" n
      | TyperFailed (NotMatchable (l, t, r)) ->
        printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r)
      | TyperFailed (TermWithMessage (f, t)) ->
        sprintf f (to_s t) |> printfn "TYPER FAILED: %s"
      | e -> printfn "RUNTIME ERROR: %s" e.Message
    printfn "";
    loop ctx None

[<EntryPoint>]
let main argv =
  printfn "nml REPL ver.???";
  printfn "";
  printfn "type <term>;; to execute a term.";
  printfn " term := 0, 1, .. | true | false | (t, t, ..) | [t; t; ..]";
  printfn "       | x | t t | t; t | fun x y .. -> t | fun () -> t ";
  printfn "       | let x = t in t | let f x .. = t in t | let f () = t in t";
  printfn "       | if t then t else t | match t with t -> t ..";
  printfn "       | <( t )> | let! x = t in t | t !; t";
  printfn "";
  printfn "type 'showVars;;' to show predefined functions.";
  printfn "example: let! x = readNat () in";
  printfn "         let! y = readNat () in";
  printfn "         print (add x y);;";
  printfn "";
  loop defaultContext None;
  0

