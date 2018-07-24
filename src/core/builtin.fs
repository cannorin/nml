module nml.Builtin

open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Contexts
open Microsoft.FSharp.Collections
open System

let DefType name t =
  TypeContext (name, t)

let DefTypeOp name printer =
  TypeContext (name, TypeOp ([name], [], printer))

let DefVariant name ts =
  TypeContext (name, Variant ([name], [], ts))

let DefInductiveVariant name f =
  TypeContext (name, InductiveVariant ([name], [], f))

let DefPolyVariant name targs ts =
  TypeContext (name, Variant ([name], targs |> List.map TyVar, ts))

let DefPolyInductiveVariant name targs f =
  TypeContext (name, InductiveVariant ([name], targs |> List.map TyVar, f))

let builtinTypes = [
  DefInductiveVariant "Nat" (fun self -> [ NewRecConst ("Succ", [self]); NewConst ("0", []) ]);
]

let impossible = UTmLiteral LUnit

let DefFun name targs tret f =
  let (_, timeret) = getTimeOfType tret
  let e xs = UTmApply (ExternalFun name (foldFun TyFun targs tret) f, xs) |> times timeret UTmRun |> times timeret UTmDefer in
  let t = foldFun TyFun targs tret in
  TermContext (name, (t, ExternalFun name t e))

let DefPolyFun name tas targs tret f =
  let (_, timeret) = getTimeOfType tret
  let e xs = UTmApply (ExternalFun name (TyScheme (set tas, foldFun TyFun targs tret)) f, xs) |> times timeret UTmRun |> times timeret UTmDefer in
  let t = TyScheme (set tas, foldFun TyFun targs tret) in
  TermContext (name, (t, ExternalFun name t e))

let DefRawTerm name term =
  try
    let (t', tt) = inferWithContext (builtinTypes |> Context.termMap fst) term in
    let fv = fvOf tt in
    if (Set.count fv > 0) then
      TermContext (name, (TyScheme (fv, tt), t'))
    else
      TermContext (name, (tt, t'))
  with
    | TyperFailed tf -> printTypeError tf; failwith ""
    | e -> printfn "RUNTIME ERROR: %s" e.InnerException.Message; failwith "";

let DefRawCode name s =
  try
    let t = NmlParser.parseTerm s |> ParserUtils.toUntypedTerm builtinTypes in
    let (t', tt) = inferWithContext (builtinTypes |> Context.termMap fst) t in
    let fv = fvOf tt in
    if (Set.count fv > 0) then
      TermContext (name, (TyScheme (fv, tt), t'))
    else
      TermContext (name, (tt, t'))
  with
    | ParserFailed msg -> sprintf "PARSER FAILED: %s" msg |> failwith
    | TyperFailed tf -> printTypeError tf; failwith ""
    | e -> printfn "RUNTIME ERROR: %s" e.InnerException.Message; failwith "";

let addTerm name term ctx =
  let (t', tt) = inferWithContext (ctx |> Context.termMap fst) term in
  let fv = fvOf tt in
  if (Set.count fv > 0) then
    TermContext (name, (TyScheme (fv, tt), t')) :: ctx
  else
    TermContext (name, (tt, t')) :: ctx

let builtinTerms = [
  DefRawTerm "run_" (UTmFun (UTmRun (UTmBoundVar 0)));
  DefFun "exit" [TyNat] (TyDeferred TyUnit) (function
    | UTmLiteral (LNat x) :: _ -> Environment.Exit(int32 x); UTmLiteral LUnit
    | _ -> impossible
  );
  DefFun "+" [TyNat; TyNat] TyNat (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a + b) |> UTmLiteral
    | _ -> impossible
  );
  DefFun "*" [TyNat; TyNat] TyNat (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a * b) |> UTmLiteral
    | _ -> impossible
  );
  DefFun "%" [TyNat; TyNat] TyNat (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a % b) |> UTmLiteral
    | _ -> impossible
  );
  DefFun "-?" [TyNat; TyNat] (TyOption TyNat) (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ ->
      if (a > b) then
        UTmConstruct (["Some"], [LNat (a - b) |> UTmLiteral])
      else
        UTmConstruct (["None"], [])
    | _ -> impossible
  );
  DefPolyFun "=" ["a"] [TyVar "a"; TyVar "a"] TyBool (function
    | a :: b :: _ -> (a = b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefPolyFun "<>" ["a"] [TyVar "a"; TyVar "a"] TyBool (function
    | a :: b :: _ -> (a <> b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "not" [TyBool] TyBool (function
    | UTmLiteral (LBool b) :: _ -> not b |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun ">" [TyNat; TyNat] TyBool (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> (a > b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "<" [TyNat; TyNat] TyBool (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> (a < b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "&&" [TyBool; TyBool] TyBool (function
    | UTmLiteral (LBool a) :: UTmLiteral (LBool b) :: _ -> (a && b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "||" [TyBool; TyBool] TyBool (function
    | UTmLiteral (LBool a) :: UTmLiteral (LBool b) :: _ -> (a || b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "readNat" [TyUnit] (TyDeferred TyNat) (fun _ ->
      printf "readNat> ";
      Console.ReadLine()
        |> uint32
        |> LNat |> UTmLiteral
  );
  DefPolyFun "print" ["a"] [TyVar "a"] (TyDeferred TyUnit) (function
    | x :: _ ->
      printfn "print> %s" (to_s x); UTmLiteral LUnit
    | _ -> printfn "print> ???"; impossible
  );
  DefFun "pause" [TyUnit] (TyDeferred TyUnit) (function
    | _ ->
      printf "pause> press enter to continue ..";
      Console.ReadLine () |> ignore;
      UTmLiteral LUnit
  );
]

open System.IO

let defaultContext =
  let ctx = List.append builtinTypes builtinTerms
  let stdlibPath = Path.Combine(AppContext.BaseDirectory, "stdlib.nml")
  let (_, stdlib) = 
    File.ReadAllText stdlibPath
      |> NmlParser.parseToplevelWithFileName stdlibPath
      |> ParserUtils.toToplevelBase ctx NmlParser.parseToplevelWithFileName ctx []
  stdlib @ ctx

()
