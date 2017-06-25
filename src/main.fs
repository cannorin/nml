open nml
open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Evaluation
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Collections
open System
open Mono.Terminal

type ExecutionContext = (string * Type * UntypedTerm) list

let toTyperContext = List.map (fun (n, t, _) -> (n, t))
let toEvalContext = List.map (fun (n, _, e) -> (n, e)) >> Map.ofList

let editor = new LineEditor ("nml", 300)
let inline scan prompt = editor.Edit(prompt, "")

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
  if (i = "showVars") then
    for (nm, ty, _) in ctx do
      printfn "- %s : %s" nm (to_s ty)
    printfn "";
    loop ctx None
  else if (String.length i = 0) then
    loop ctx None
  else
    try
      let e = parseTerm i in
      let te = inferWithContext (ctx |> toTyperContext) e in
      printfn "type: %s" (to_s te);
      printfn "eval: %s" (to_s e)
      let t = evalWithContext e (ctx |> toEvalContext) in
      let rec l i = function
        | URun t ->
          printfn "----> %s" (to_s t);
          evalWithContext (URun t) (ctx |> toEvalContext) |> l (i + 1)
        | t ->
          t |> to_s |> printfn "----> %s"
      in l 0 t;
    with
      | ParserFailed msg -> printfn "PARSER FAILED: %s" msg
      | TyperFailed (UnifyFailed (a, b, ut)) ->
        printfn "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut)
      | TyperFailed (UnknownVar (n, _)) ->
        printfn "TYPER FAILED: '%s' is not defined (unknown variable)" n
      | e -> printfn "RUNTIME ERROR: %s" e.Message
    printfn "";
    loop ctx None

let ExtFun name t f =
  (name, t, ExternalFun name t f)

let RawTerm name t =
  (name, (infer t), t)

[<EntryPoint>]
let main argv =
  printfn "nml REPL ver.???";
  printfn "";
  printfn "type <term>;; to execute a term.";
  printfn "terms := 0,1,... | true | false | (t,t,...)";
  printfn "       | fun x -> t | t t | if t then t else t";
  printfn "       | let x = t in t | <( t )> | let! x = t in t";
  printfn "       | let f x y... = t in t | fun x y... -> t";
  printfn "       | let f () = t in t | fun () -> t";
  printfn "";
  printfn "type 'showVars;;' to show predefined functions.";
  printfn "example: let! x = readNat () in";
  printfn "         let! y = readNat () in";
  printfn "         add x y;;";
  printfn "";
  let impossible = ULiteral LUnit in
  loop [
    RawTerm "id" (ULet ("id", UFun ("x", UVar "x"), UVar "id"));
    ExtFun "exit" (Fun(Nat, Deferred Unit)) (function
      | ULiteral (LNat x) :: _ -> Environment.Exit(x); ULiteral LUnit
      | _ -> impossible
    );
    ExtFun "add" (foldFun [Nat; Nat] Nat) (function
      | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a + b) |> ULiteral
      | _ -> impossible
    );
    ExtFun "mul" (foldFun [Nat; Nat] Nat) (function
      | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a * b) |> ULiteral
      | _ -> impossible
    );
    ExtFun "mod" (foldFun [Nat; Nat] Nat) (function
      | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a % b) |> ULiteral
      | _ -> impossible
    );
    ExtFun "eq" (Forall (set ["a"], foldFun [TypeVar "a"; TypeVar "a"] Bool)) (function
      | a :: b :: _ -> (a = b) |> LBool |> ULiteral
      | _ -> impossible
    );
    ExtFun "gt" (foldFun [Nat; Nat] Bool) (function
      | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a > b) |> LBool |> ULiteral
      | _ -> impossible
    );
    ExtFun "lt" (foldFun [Nat; Nat] Bool) (function
      | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a < b) |> LBool |> ULiteral
      | _ -> impossible
    );
    ExtFun "and" (foldFun [Bool; Bool] Bool) (function
      | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a && b) |> LBool |> ULiteral
      | _ -> impossible
    );
    ExtFun "or" (foldFun [Bool; Bool] Bool) (function
      | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a || b) |> LBool |> ULiteral
      | _ -> impossible
    );
    RawTerm "ignore" (ULet("_", UFun("__", ULiteral LUnit), UVar "_"));
    ExtFun "readNat" (Fun(Unit, Deferred Nat)) (fun _ ->
        scan "readNat> " 
          |> int32
          |> LNat |> ULiteral |> UDefer 
    );
    ExtFun "writeNat" (Fun(Nat, Deferred Unit)) (function
      | ULiteral (LNat i) :: _ ->
        printfn "%i" i;
        LUnit |> ULiteral |> UDefer
      | _ -> impossible
    );
    ExtFun "car" (Forall (set ["a"; "b"], Fun(TTuple(TypeVar "a", TypeVar "b"), TypeVar "a"))) (function
      | UTuple (a, b) :: _ -> a
      | _ -> impossible
    );
    ExtFun "cdr" (Forall (set ["a"; "b"], Fun(TTuple(TypeVar "a", TypeVar "b"), TypeVar "b"))) (function
      | UTuple (a, b) :: _ -> b
      | _ -> impossible
    );
  ] None
  0

