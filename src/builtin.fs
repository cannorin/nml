module nml.Builtin

open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Evaluation
open nml.UniversalContext
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Collections
open System

let DefType t =
  TypeContext t

let DefVariant name ts =
  TypeContext (Variant (name, [], ts))

let DefInductiveVariant name f =
  TypeContext (InductiveVariant (name, [], f))

let DefPolyVariant name targs ts =
  TypeContext (Variant (name, targs |> List.map TypeVar, ts))

let DefPolyInductiveVariant name targs f =
  TypeContext (InductiveVariant (name, targs |> List.map TypeVar, f))

let builtinTypes = [
  DefPolyVariant "Option" ["a"] [ ("Some", [TypeVar "a"]); ("None", []) ];
  DefPolyVariant "Either" ["a"; "b"] [ ("Left", [TypeVar "a"]); ("Right", [TypeVar "b"]) ];
  DefInductiveVariant "Nat" (fun self -> [ ("Succ", [self]); ("0", []) ]);
  DefPolyInductiveVariant "List" ["a"] (fun self -> [ ("Nil", []); ("Cons", [TypeVar "a"; self]) ])
]

let impossible = ULiteral LUnit

let DefFun name targs tret f =
  let (tret', timeret) = getTimeOfType tret in
  if timeret > 0 then
    let ext = ExternalFun name (foldFun targs tret') f in
    let (vs, _) = targs |> List.length |> genUniqs 0 in
    TermContext (name, foldFun targs tret, ext |> foldApply (vs |> List.map UVar) |> addRun timeret |> delayTermBy timeret |> List.foldBack (fun x b -> UFun(x, b)) vs)
  else
    TermContext (name, foldFun targs tret, ExternalFun name (foldFun targs tret) f)

let DefPolyFun name tas targs tret f =
  let (tret', timeret) = getTimeOfType tret in
  if timeret > 0 then
    let ext = ExternalFun name (Scheme (set tas, foldFun targs tret')) f in
    let (vs, _) = targs |> List.length |> genUniqs 0 in
    TermContext (name, Scheme (set tas, foldFun targs tret), ext |> foldApply (vs |> List.map UVar) |> addRun timeret |> delayTermBy timeret |> List.foldBack (fun x b -> UFun(x, b)) vs)
  else
    TermContext (name, Scheme (set tas, foldFun targs tret), ExternalFun name (Scheme (set tas, foldFun targs tret)) f)

let RawTerm name s =
  try
    let t = parseTerm s in
    let (t', tt) = inferWithContext builtinTypes t in
    let fv = fvOf tt in
    if (Set.count fv > 0) then
      TermContext (name, Scheme (fv, tt), t')
    else
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
  let fv = fvOf tt in
  if (Set.count fv > 0) then
    TermContext (name, Scheme (fv, tt), t') :: ctx
  else
    TermContext (name, tt, t') :: ctx

let builtinTerms = [
  RawTerm "id" "fun x -> x";
  DefFun "exit" [Nat] (Deferred Unit) (function
    | ULiteral (LNat x) :: _ -> Environment.Exit(int32 x); ULiteral LUnit
    | _ -> impossible
  );
  DefFun "+" [Nat; Nat] Nat (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a + b) |> ULiteral
    | _ -> impossible
  );
  DefFun "*" [Nat; Nat] Nat (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a * b) |> ULiteral
    | _ -> impossible
  );
  DefFun "%" [Nat; Nat] Nat (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a % b) |> ULiteral
    | _ -> impossible
  );
  RawTerm "tryPred" "fun i -> match i with Succ n -> Some n | 0 -> None";
  DefFun "-?" [Nat; Nat] (TOption Nat) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ ->
      if (a > b) then
        UConstruct ("Some", [LNat (a - b) |> ULiteral])
      else
        UConstruct ("None", [])
    | _ -> impossible
  );
  DefPolyFun "=" ["a"] [TypeVar "a"; TypeVar "a"] Bool (function
    | a :: b :: _ -> (a = b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefPolyFun "<>" ["a"] [TypeVar "a"; TypeVar "a"] Bool (function
    | a :: b :: _ -> (a <> b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "not" [Bool] Bool (function
    | ULiteral (LBool b) :: _ -> not b |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun ">" [Nat; Nat] Bool (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a > b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "<" [Nat; Nat] Bool (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a < b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "&&" [Bool; Bool] Bool (function
    | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a && b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "||" [Bool; Bool] Bool (function
    | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a || b) |> LBool |> ULiteral
    | _ -> impossible
  );
  RawTerm "ignore" "fun _ -> ()";
  DefFun "readNat" [Unit] (Deferred Nat) (fun _ ->
      scan "readNat> " 
        |> uint32
        |> LNat |> ULiteral
  );
  DefPolyFun "print" ["a"] [TypeVar "a"] (Deferred Unit) (function
    | x :: _ ->
      printfn "print> %s" (to_s x);
      ULiteral LUnit
    | _ -> impossible
  );
  DefFun "pause" [Unit] (Deferred Unit) (function
    | _ ->
      printf "pause> press enter to continue ..";
      Console.ReadLine () |> ignore;
      ULiteral LUnit
  );
  RawTerm "defaultArg" "fun o d -> match o with Some x -> x | None -> d";
  RawTerm "|>" "fun x f -> f x";
  RawTerm "||>" "fun x f -> match x with (a, b) -> f a b";
  RawTerm "|||>" "fun x f -> match x with (a, b, c) -> f a b c"
  RawTerm "<|" "fun f x -> f x";
  RawTerm "<||" "fun f x -> match x with (a, b) -> f a b";
  RawTerm "<|||" "fun f x -> match x with (a, b, c) -> f a b c";
  RawTerm ">>" "fun f g x -> g (f x)";
  RawTerm "<<" "fun g f x -> g (f x)";
  RawTerm "?|" "fun x d -> match x with Some x -> x | None -> d";
  RawTerm ";" "fun a b -> let _ = a in b";
  RawTerm "!;" "fun a b -> let! _ = a in b";
  RawTerm "::" "fun x t -> Cons (x, t)";
]

let defaultContext = List.append builtinTypes builtinTerms

()
