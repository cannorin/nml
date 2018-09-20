module nml.Builtin

open nml.Ast
open nml.Parser
open nml.Typer
open nml.Helper
open nml.Contexts
open System
open FSharp.Collections

let builtinTypes : TermContext =
  [
    "Nat", TyNat
    "Bool", TyBool
    "Unit", TyUnit
    "List", TyList (NTTyVar "a")
    "Option", TyOption (NTTyVar "a")
  ] |> List.map (Tuple.map2 id (NotTemporal >> generalizeAllFV) >> TypeContext)

let builtin name ty f =
  let inline f xs =
    try f (xs |> List.map With.itemof) |> With.noinfo |> Some
    with MatchFailureException _ -> None
  let ty = NmlParser.parseType ty 
           |> ParserUtils.toKnownType builtinTypes
  let tm = TmBuiltin (name, generalizeAllFV ty, BuiltinFunc f |> EValue)
           |> With.info { ty=ty; source=Builtin }
  TermContext (name, tm)

let runnableBuiltin name ty f =
  let inline f (ti, xs) =
    try f (ti, (xs |> List.map With.itemof)) |> With.noinfo |> Some
    with MatchFailureException _ -> None
  let ty = NmlParser.parseType ty 
           |> ParserUtils.toKnownType builtinTypes
  let tm = TmRunnableBuiltin (name, generalizeAllFV ty, RunnableBuiltinFunc f |> EValue)
           |> With.info { ty=ty; source=Builtin }
  TermContext (name, tm)

#nowarn "0025" // suppress incomplete pattern warning; match failures shall be catched by caller
let builtinTerms : TermContext = [
  builtin "+" "Nat -> Nat -> Nat" <| function 
    | [TmLiteral (LNat n); TmLiteral (LNat m)] -> TmLiteral (LNat (n+m))
  builtin "*" "Nat -> Nat -> Nat" <| function
    | [TmLiteral (LNat n); TmLiteral (LNat m)] -> TmLiteral (LNat (n*m))
  builtin "%" "Nat -> Nat -> Nat" <| function
    | [TmLiteral (LNat n); TmLiteral (LNat m)] -> TmLiteral (LNat (n%m))
  builtin "-?" "Nat -> Nat -> Option Nat" <| function 
    | [TmLiteral (LNat n); TmLiteral (LNat m)] ->
      if n >= m then
        TmConstruct(["Some"], [TmLiteral (LNat (n-m)) |> With.noinfo])
      else
        TmConstruct(["None"], [])
  builtin "=" "a -> a -> Bool" <| function
    | [a; b] when Term.isStructural a && Term.isStructural b ->
      TmLiteral (LBool (a = b))
  builtin "<>" "a -> a -> Bool" <| function
    | [a; b] when Term.isStructural a && Term.isStructural b ->
      TmLiteral (LBool (a = b))
  builtin ">" "Nat -> Nat -> Bool" <| function
    | [TmLiteral (LNat n); TmLiteral (LNat m)] -> TmLiteral (LBool (n > m))
  builtin "<" "Nat -> Nat -> Bool" <| function
    | [TmLiteral (LNat n); TmLiteral (LNat m)] -> TmLiteral (LBool (n < m))
  builtin "&&" "Bool -> Bool -> Bool" <| function
    | [TmLiteral (LBool n); TmLiteral (LBool m)] -> TmLiteral (LBool (n && m))
  builtin "||" "Bool -> Bool -> Bool" <| function
    | [TmLiteral (LBool n); TmLiteral (LBool m)] -> TmLiteral (LBool (n || m))
  builtin "not" "Bool -> Bool -> Bool" <| function
    | [TmLiteral (LBool b)] -> TmLiteral (LBool (not b))
  
  runnableBuiltin "readNat" "Unit -> Next Nat" <| function
    | ti, [TmLiteral LUnit] when ti <> TimeN Z ->
      printf "readNat> "
      Console.ReadLine() |> uint32 |> LNat |> TmLiteral
  runnableBuiltin "print" "a -> Next Unit" <| function
    | ti, [x] when ti <> TimeN Z ->
      printfn "print: %A" x
      TmLiteral LUnit
  runnableBuiltin "pause" "Unit -> Next Unit" <| function
    | ti, [TmLiteral LUnit] when ti <> TimeN Z ->
      printf "pause: press Enter to continue..."
      Console.ReadLine() |> ignore
      TmLiteral LUnit
  runnableBuiltin "exit" "Nat -> Next Unit" <| function
    | ti, [TmLiteral (LNat code)] when ti <> TimeN Z ->
      Environment.Exit (int code)
      TmLiteral LUnit
]

open System.IO

let defaultContext : TermContext =
  let ctx = List.append builtinTypes builtinTerms
  let stdlibPath = Path.Combine(AppContext.BaseDirectory, "stdlib.nml")
  let (_, stdlib) = 
    File.ReadAllText stdlibPath
      |> NmlParser.parseToplevelWithFileName stdlibPath
      |> ParserUtils.toToplevelBase
           ctx
           NmlParser.parseToplevelWithFileName
           (fun ctx -> Typer.inferWithContext (ctx |> Context.termMap (Term.getType >> generalizeAllFV)))
           ctx
           []
  stdlib @ ctx
