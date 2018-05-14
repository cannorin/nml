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
  DefPolyVariant "Option" ["a"] [ NewConst ("Some", [TyVar "a"]); NewConst ("None", []) ];
  DefPolyVariant "Either" ["a"; "b"] [ NewConst ("Left", [TyVar "a"]); NewConst ("Right", [TyVar "b"]) ];
  DefInductiveVariant "Nat" (fun self -> [ NewRecConst ("Succ", [self]); NewConst ("0", []) ]);
  DefPolyInductiveVariant "List" ["a"] (fun self -> [ NewConst ("Nil", []); NewRecConst ("Cons", [TyVar "a"; self]) ])
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
  DefRawCode "id" "fun x -> x";
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
  DefRawCode "tryPred" "fun i -> match i with Succ n -> Some n | 0 -> None";
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
  DefRawCode "ignore" "fun _ -> ()";
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
  DefRawCode "defaultArg" "fun o d -> match o with Some x -> x | None -> d";
  DefRawCode "|>" "fun x f -> f x";
  DefRawCode "||>" "fun x f -> match x with (a, b) -> f a b";
  DefRawCode "|||>" "fun x f -> match x with (a, b, c) -> f a b c"
  DefRawCode "<|" "fun f x -> f x";
  DefRawCode "<||" "fun f x -> match x with (a, b) -> f a b";
  DefRawCode "<|||" "fun f x -> match x with (a, b, c) -> f a b c";
  DefRawCode ">>" "fun f g x -> g (f x)";
  DefRawCode "<<" "fun g f x -> g (f x)";
  DefRawCode "?|" "fun x d -> match x with Some x -> x | None -> d";
  DefRawCode ";" "fun a b -> let _ = a in b";
  DefRawCode "!;" "fun a b -> let! _ = a in b";
  //DefRawTerm "!;" (UTmFun (UTmFun (UTmLet ("_", UTmRun (UTmBoundVar 1), UTmBoundVar 0))));
  DefRawCode "::" "fun x t -> Cons (x, t)";
]

let testModule =
  ModuleContext("Test",
    [
      TermContext("number", (TyNat, UTmLiteral (LNat 42u)))
      DefRawCode "succ2" "fun a -> Succ (Succ a)"
    ]
  )

let defaultContext = testModule :: List.append builtinTypes builtinTerms

()
