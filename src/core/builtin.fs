module nml.Builtin

open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Stages
open nml.Stages.StageOp
open nml.UniversalContext
open Microsoft.FSharp.Collections
open System

let DefType t =
  TypeContext t

let DefTypeOp name printer =
  TypeContext (TypeOp (name, [], printer))

let DefVariant name ts =
  TypeContext (Variant (name, [], ts))

let DefInductiveVariant name f =
  TypeContext (InductiveVariant (name, [], f, SVar "x"))

let DefPolyVariant name targs ts =
  TypeContext (Variant (name, targs |> List.map TypeVar, ts))

let DefPolyInductiveVariant name targs f =
  TypeContext (InductiveVariant (name, targs |> List.map TypeVar, f, SVar "x"))

let builtinTypes = 
  let inline N x = NewConst x in
  let inline NR x = NewRecConst x in
  [
    DefPolyVariant "Option" ["a"] [ N ("Some", [TypeVar "a"]); N ("None", []) ];
    DefPolyVariant "Either" ["a"; "b"] [ N ("Left", [TypeVar "a"]); N ("Right", [TypeVar "b"]) ];
    DefInductiveVariant "Nat" (fun self -> [ NR ("Succ", [self]); N ("0", []) ]);
    DefPolyInductiveVariant "List" ["a"] (fun self -> [ N ("Nil", []); NR ("Cons", [TypeVar "a"; self]) ])
  ]

let impossible = UTmLiteral LUnit

let DefFun name targs tret f =
  let (_, timeret) = getTimeOfType tret
  let e xs = UTmApply (ExternalFun name (foldFun targs tret) f, xs) |> times timeret UTmRun |> times timeret UTmDefer in
  let t = foldFun targs tret in
  TermContext (name, t, ExternalFun name t e)

let DefPolyFun name tas scs targs tret f =
  let scs = scs |> List.choose (function | StageInequality (SVar a, b) -> Some (a, b) | _ -> None) |> Map.ofList in
  let (_, timeret) = getTimeOfType tret
  let e xs = UTmApply (ExternalFun name (Scheme (set tas, scs, foldFun targs tret)) f, xs) |> times timeret UTmRun |> times timeret UTmDefer in
  let t = Scheme (set tas, scs, foldFun targs tret) in
  TermContext (name, t, ExternalFun name t e)

let DefRawTerm name term =
  try
    let (t', tt) = inferWithContext builtinTypes term in
    TermContext (name, tt, t')
  with
    | TyperFailed (UnifyFailed (a, b, ut)) ->
      sprintf "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut) |> failwith
    | TyperFailed (UnknownVar (n, ctx)) ->
      printfn "TYPER FAILED: '%s' is not defined (unknown variable)" n; failwith "";
    | TyperFailed (NotMatchable (l, t, r)) ->
      printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r); failwith ""
    | TyperFailed (TermWithMessage (f, tm)) ->
      sprintf f (to_s tm) |> printfn "TYPER FAILED: %s"; failwith "";
    | e -> printfn "RUNTIME ERROR: %s" e.InnerException.Message; failwith "";


let DefRawCode name s =
  try
    let t = parseTerm s |> toUntypedTerm builtinTypes in
    let (t', tt) = inferWithContext builtinTypes t in
    TermContext (name, tt, t')
  with
    | ParserFailed msg -> sprintf "PARSER FAILED: %s" msg |> failwith
    | TyperFailed (UnifyFailed (a, b, ut)) ->
      sprintf "TYPER FAILED: '%s' and '%s' are incompatible types.\n------------> %s" (to_s a) (to_s b) (to_s ut) |> failwith
    | TyperFailed (UnknownVar (n, ctx)) ->
      printfn "TYPER FAILED: '%s' is not defined (unknown variable)" n; failwith "";
    | TyperFailed (NotMatchable (l, t, r)) ->
      printfn "TYPER FAILED: invalid match pattern for type '%s':\n------------> %s -> %s" (to_s t) (to_s l) (to_s r); failwith ""
    | TyperFailed (TermWithMessage (f, tm)) ->
      sprintf f (to_s tm) |> printfn "TYPER FAILED: %s"; failwith "";
    | e -> printfn "RUNTIME ERROR: %s" e.InnerException.Message; failwith "";

let addTerm name term ctx =
  let (t', tt) = inferWithContext ctx term in
  TermContext (name, tt, t') :: ctx

let inline DefSVar n = SVar n <=^ SInf

let builtinTerms = [
  DefRawCode "id" "fun x -> x";
  DefRawTerm "run_" (UTmFun (UTmRun (UTmBoundVar 0)));
  DefFun "exit" [Nat] (Deferred Unit) (function
    | UTmLiteral (LNat x) :: _ -> Environment.Exit(int32 x); UTmLiteral LUnit
    | _ -> impossible
  );
  DefPolyFun "+" [] [DefSVar "b"; DefSVar "c"] [NatS (SVar "b"); NatS (SVar "c")] (NatS (SVar "b" +^ SVar "c")) (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a + b) |> UTmLiteral
    | _ -> impossible
  );
  DefPolyFun "*" [] [DefSVar "b"; DefSVar "c"] [NatS (SVar "b"); NatS (SVar "c")] (NatS SInf) (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a * b) |> UTmLiteral
    | _ -> impossible
  );
  DefPolyFun "%" [] [DefSVar "b"; DefSVar "c"; SVar "d" <=^ SVar "b"; SVar "d" <=^ SVar "c"] [NatS (SVar "b"); NatS (SVar "c")] (NatS (SVar "d")) (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> LNat (a % b) |> UTmLiteral
    | _ -> impossible
  );
  DefRawCode "tryPred" "fun i -> match i with Succ n -> Some n | 0 -> None";
  DefPolyFun "-?" [] [DefSVar "b"; DefSVar "c"; SVar "d" <=^ SVar "b"] [NatS (SVar "b"); NatS (SVar "c")] (TOption (NatS (SVar "d"))) (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ ->
      if (a > b) then
        UTmConstruct ("Some", [LNat (a - b) |> UTmLiteral])
      else
        UTmConstruct ("None", [])
    | _ -> impossible
  );
  DefPolyFun "=" ["a"] [] [TypeVar "a"; TypeVar "a"] Bool (function
    | a :: b :: _ -> (a = b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefPolyFun "<>" ["a"] [] [TypeVar "a"; TypeVar "a"] Bool (function
    | a :: b :: _ -> (a <> b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "not" [Bool] Bool (function
    | UTmLiteral (LBool b) :: _ -> not b |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun ">" [Nat; Nat] Bool (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> (a > b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "<" [Nat; Nat] Bool (function
    | UTmLiteral (LNat a) :: UTmLiteral (LNat b) :: _ -> (a < b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "&&" [Bool; Bool] Bool (function
    | UTmLiteral (LBool a) :: UTmLiteral (LBool b) :: _ -> (a && b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefFun "||" [Bool; Bool] Bool (function
    | UTmLiteral (LBool a) :: UTmLiteral (LBool b) :: _ -> (a || b) |> LBool |> UTmLiteral
    | _ -> impossible
  );
  DefRawCode "ignore" "fun _ -> ()";
  DefFun "readNat" [Unit] (Deferred Nat) (fun _ ->
      printf "readNat> ";
      Console.ReadLine()
        |> uint32
        |> LNat |> UTmLiteral
  );
  DefPolyFun "print" ["a"] [] [TypeVar "a"] (Deferred Unit) (function
    | x :: _ ->
      printfn "print> %s" (to_s x); UTmLiteral LUnit
    | _ -> printfn "print> ???"; impossible
  );
  DefFun "pause" [Unit] (Deferred Unit) (function
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

let defaultContext = List.append builtinTypes builtinTerms

()
