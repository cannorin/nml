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

let builtinTypes = []

let impossible = ULiteral LUnit

let DefFun name t f =
  TermContext (name, t, ExternalFun name t f)

let DefPolyFun name tas t f =
  TermContext (name, Scheme (set tas, t), ExternalFun name (Scheme (set tas, t)) f)

let RawTerm name t =
  let (t', tt) = inferWithContext builtinTypes t in
  let fv = fvOf tt in
  if (Set.count fv > 0) then
    TermContext (name, Scheme (fv, tt), t')
  else
    TermContext (name, tt, t')

let addTerm name term ctx =
  let (t', tt) = inferWithContext ctx term in
  let fv = fvOf tt in
  if (Set.count fv > 0) then
    TermContext (name, Scheme (fv, tt), t') :: ctx
  else
    TermContext (name, tt, t') :: ctx

let builtinTerms = [
  RawTerm "id" (ULet ("id", UFun ("x", UVar "x"), UVar "id"));
  DefFun "exit" (Fun(Nat, Deferred Unit)) (function
    | ULiteral (LNat x) :: _ -> Environment.Exit(x); ULiteral LUnit
    | _ -> impossible
  );
  DefFun "add" (foldFun [Nat; Nat] Nat) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a + b) |> ULiteral
    | _ -> impossible
  );
  DefFun "mul" (foldFun [Nat; Nat] Nat) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a * b) |> ULiteral
    | _ -> impossible
  );
  DefFun "mod" (foldFun [Nat; Nat] Nat) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> LNat (a % b) |> ULiteral
    | _ -> impossible
  );
  DefPolyFun "eq" ["a"] (foldFun [TypeVar "a"; TypeVar "a"] Bool) (function
    | a :: b :: _ -> (a = b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "gt" (foldFun [Nat; Nat] Bool) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a > b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "lt" (foldFun [Nat; Nat] Bool) (function
    | ULiteral (LNat a) :: ULiteral (LNat b) :: _ -> (a < b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "and" (foldFun [Bool; Bool] Bool) (function
    | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a && b) |> LBool |> ULiteral
    | _ -> impossible
  );
  DefFun "or" (foldFun [Bool; Bool] Bool) (function
    | ULiteral (LBool a) :: ULiteral (LBool b) :: _ -> (a || b) |> LBool |> ULiteral
    | _ -> impossible
  );
  RawTerm "ignore" (ULet("_", UFun("__", ULiteral LUnit), UVar "_"));
  DefFun "readNat" (Fun(Unit, Deferred Nat)) (fun _ ->
      scan "readNat> " 
        |> int32
        |> LNat |> ULiteral |> UDefer 
  );
  DefPolyFun "print" ["a"] (Fun (TypeVar "a", Deferred Unit)) (function
    | x :: _ ->
      printfn "print> %s" (to_s x);
      ULiteral LUnit |> UDefer
    | _ -> impossible
  );
  DefPolyFun "car" ["a"; "b"] (Fun(TTuple [TypeVar "a"; TypeVar "b"], TypeVar "a")) (function
    | UTuple [a; b] :: _ -> a
    | _ -> impossible
  );
  DefPolyFun "cdr" ["a"; "b"] (Fun(TTuple [TypeVar "a"; TypeVar "b"], TypeVar "b")) (function
    | UTuple [a; b] :: _ -> b
    | _ -> impossible
  );
]

let defaultContext = List.append builtinTypes builtinTerms

()
