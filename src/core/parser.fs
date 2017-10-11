module nml.Parser

open FParsec
open nml.Ast
open nml.Typer
open nml.Helper
open nml.UniversalContext
open FSharp.Collections

type ParsedTerm =
  | PTmVar of string
  | PTmLiteral of Literal
  | PTmTuple of ParsedTerm list
  | PTmList of ParsedTerm list
  | PTmFun of string  * ParsedTerm
  | PTmFunUnit of ParsedTerm
  | PTmApply of ParsedTerm * ParsedTerm
  | PTmIf of ParsedTerm * ParsedTerm * ParsedTerm
  | PTmLet of string * ParsedTerm * ParsedTerm
  | PTmFixMatch of string * (ParsedTerm * ParsedTerm) list
  | PTmDefer of ParsedTerm
  | PTmRun of ParsedTerm
  | PTmLetDefer of string * ParsedTerm * ParsedTerm
  // | PTmModuleVal of string * string
  | PTmOp2 of ParsedTerm * string * ParsedTerm
  | PTmMatch of ParsedTerm * (ParsedTerm * ParsedTerm) list

let rec fvOfTerm = function
  | UTmFreeVar x when x <> "_" -> set [x]
  | UTmApply (l, rs) ->
    l :: rs |> List.map (fvOfTerm >> Set.toList) |> List.concat |> Set.ofList
  | UTmTuple xs
  | UTmConstruct (_, xs) ->
    xs |> List.map (fvOfTerm >> Set.toList) |> List.concat |> Set.ofList
  | UTmFun x
  | UTmDefer x
  | UTmRun x -> fvOfTerm x
  | UTmLet (x, v, b) -> Set.union (fvOfTerm v) (fvOfTerm b) |> Set.difference (set [x])
  | UTmMatch (x, cs) ->
    cs |> List.map (fun (pt, bd) -> Set.difference (fvOfTerm pt) (fvOfTerm bd) |> Set.toList)
       |> List.concat
       |> Set.ofList
       |> Set.union (fvOfTerm x)
  | UTmFixMatch cs ->
    UTmMatch (UTmLiteral LUnit, cs) |> fvOfTerm
  | _ -> set []

let toUntypedTerm ctx pt =
  let rec totc stack (pt, bd) =
    let fv = fvOfTerm (pt |> tot []) |> Set.remove "::" |> Set.toList in
    (pt |> tot (List.append fv stack), bd |> tot (List.append fv stack))
  and tot stack = function
    | PTmVar x ->
      // constructor without arguments
      if (ctx |> findConstructor x (Some []) |> Option.isSome) then
        UTmConstruct (x, [])
      else
        match (stack |> List.tryFindIndex ((=) x)) with
          | Some i -> UTmBoundVar i
          | None -> UTmFreeVar x
    | PTmLiteral l -> UTmLiteral l
    | PTmTuple xs -> UTmTuple (xs |> List.map (tot stack))
    | PTmList [] -> UTmConstruct ("Nil", [])
    | PTmList xs -> xs |> List.rev |> List.fold (fun l x -> UTmConstruct ("Cons", [tot stack x; l])) (UTmConstruct ("Nil", []))
    | PTmFun (arg, body) -> UTmFun (body |> tot (arg :: stack))
    | PTmFunUnit body -> UTmFun (body |> tot ("" :: stack))
    // immediate constructor handling
    | PTmApply (PTmVar x, PTmTuple xs) when (ctx |> findConstructor x (Some xs) |> Option.isSome) ->
      UTmConstruct (x, xs |> List.map (tot stack))
    // immediate constructor handling
    | PTmApply (PTmVar x, y) when (ctx |> findConstructor x (Some [y]) |> Option.isSome)  ->
      UTmConstruct (x, [y |> tot stack])
    | PTmApply (l, r) ->
      match (l |> tot stack) with
        | UTmApply (l', r') -> UTmApply (l', List.append r' [tot stack r])
        | x -> UTmApply (x, [tot stack r])
    | PTmDefer x -> UTmDefer (tot stack x)
    | PTmRun x -> UTmRun (tot stack x)
    | PTmLet (x, r, b) ->
      UTmLet (x, r |> tot stack, b |> tot stack)
    | PTmLetDefer (x, r, b) ->
      UTmLetDefer (x, r |> tot stack, b |> tot stack)
      // UTmDefer (PTmLet (x, PTmRun r, b) |> tot stack)
    | PTmOp2 (l, op, r) ->
      PTmApply (PTmApply (PTmVar op, l), r) |> tot stack
    | PTmIf (x, t, e) ->
      PTmMatch (x, [ (PTmLiteral (LBool true), t); (PTmLiteral (LBool false), e) ]) |> tot stack
    | PTmMatch (x, cs) ->
      UTmMatch (x |> tot stack, cs |> List.map (totc stack))
    | PTmFixMatch (n, cs) ->
      UTmFixMatch (cs |> List.map (totc (n :: stack)))
  in tot [] pt


exception ParserFailed of string

let term, termRef = createParserForwardedToRef<ParsedTerm, unit>()
//let typ, typRef = createParserForwardedToRef<Type, unit>()

let ws x = x .>> spaces
let syn x = pstring x |> ws
let between s1 s2 p = syn s1 >>. p .>> syn s2
let listing sep x =
  sepBy1 x sep
let reserved = set [ "let"; "rec"; "local"; "macro"; "in"; "fun"; "true"; "false"; "run"; "if"; "then"; "else"; "type"; "variant"; "inductive"; "match"; "with"; "function"; "fixpoint"; "of"; "begin"; "end" ]
let identifierString = many1Satisfy (List.concat [['a'..'z']; ['A'..'Z']; ['_']; ['0'..'9']] |> isAnyOf)
let identifier : Parser<string, unit> =
  let expectedIdentifier = expected "identifier"
  fun stream ->
    let state = stream.State
    let reply = identifierString stream
    if reply.Status = Ok && not (reserved |> Set.contains reply.Result || System.Char.IsDigit (reply.Result.[0])) then reply
    else
      stream.BacktrackTo(state)
      Reply(Error, expectedIdentifier)

let op_chars = "+-*/<>%&|^~=!?:;".ToCharArray() |> Set.ofArray
let op_reserved = [ "->"; "<("; ")>"; "||"; "&&"; "|>" ]

let isSymbolicOperatorChar = isAnyOf op_chars
//let remainingOpChars_ws = manySatisfy isSymbolicOperatorChar .>> spaces

let opp = new OperatorPrecedenceParser<ParsedTerm, string, unit>()

opp.OperatorConflictErrorFormatter <-
  fun (pos1, op1, afterString1) (pos2, op2, afterString2) ->
    let msg = sprintf "The operator '%s' conflicts with the previous operator '%s' at %A."
                      (op2.String + afterString2)
                      (op1.String + afterString1) pos1
    in messageError msg

let op_app = InfixOperator (" ", manySatisfy (isNoneOf op_chars) .>> spaces, 1000, Associativity.Left, (), fun _ l r -> PTmApply (l, r)) in
opp.AddOperator(op_app);
  
let addOp2Ext prefix precedence associativity =
  let op = InfixOperator (prefix, 
                          manySatisfy (isAnyOf op_chars) .>> spaces,
                          precedence, 
                          associativity, 
                          (),
                          fun remOpChars expr1 expr2 -> PTmOp2 (expr1, prefix + remOpChars, expr2)
                         )
  in
  opp.AddOperator(op)

let addOp2Res x pcd asy =
  for i in (op_chars |> Set.map (fun c -> sprintf "%s%c" x c) |> Set.filter (fun s -> op_reserved |> List.contains s |> not)) do
    addOp2Ext i pcd asy

// the operator definitions:
addOp2Ext "!;" 10 Associativity.Right
addOp2Ext ";"  10 Associativity.Right
addOp2Ext "|>" 15 Associativity.Left

addOp2Ext "&&" 20 Associativity.Left
addOp2Ext "||" 20 Associativity.Left

addOp2Ext "&"  30 Associativity.Left
addOp2Res "|"  30 Associativity.Left

addOp2Ext "<"  30 Associativity.Left
addOp2Ext ">"  30 Associativity.Left
addOp2Ext "="  30 Associativity.Left

addOp2Ext "^"  34 Associativity.Right

addOp2Ext "?|" 35 Associativity.Left
addOp2Ext "::" 35 Associativity.Right

addOp2Ext "+"  40 Associativity.Left
addOp2Res "-"  40 Associativity.Left

addOp2Ext "%"  50 Associativity.Left
addOp2Ext "*"  50 Associativity.Left
addOp2Ext "/"  50 Associativity.Left

addOp2Ext "**" 60 Associativity.Right
// end of definitions.


let name = identifier
let opvar = pstring "(" >>. many1Satisfy (isAnyOf op_chars) .>> pstring ")"

(*
let type_nat = syn "Nat" >>% Nat
let type_bool = syn "Bool" >>% Bool
let type_unit = syn "Unit" >>% Unit
let type_var = ws name |>> TypeName
let type_fun = sepEndBy1 typ (syn "->") |>> (fun ts -> 
    match (ts |> List.rev) with
      | t :: [] -> t
      | rt :: argst -> foldFun (argst |> List.rev) rt
      | [] -> failwith "impossible"
  )
let type_tuple = sepEndBy1 typ (syn "*") |>> (fun ts ->
    match ts with
      | t :: [] -> t
      | [] -> failwith "impossible"
      | xs -> TTuple xs
  )
let type_app = sepEndBy1 typ spaces1 |>> (fun ts ->
    match (ts |> List.rev with)
      | t :: [] -> t
      | (TypeName x) :: argst -> TypeOp (x, argst |> List.rev, None)
      | _ -> failwith "impossible"
*)


let unitparam = syn "()" |>> (fun x -> [x])

let variable = ws (name <|> opvar) |>> PTmVar
let literal_nat = ws puint32 <?> "Nat" |>> (LNat >> PTmLiteral)
let literal_bool = ((stringReturn "true" true) <|> (stringReturn "false" false)) |> ws |>> (LBool >> PTmLiteral)
let literal_unit = syn "()" >>% PTmLiteral LUnit

let inline (<+>) a b =
  tuple2 a b |>> (fun (x, y) -> List.append [x] y)

let expr_tuple = (term |> listing (syn ",")) |> between "(" ")" |>> (fun xs -> if (List.length xs = 1) then xs.[0] else PTmTuple xs)

let makeList t = 
  let rec m = function
    | [PTmOp2 (l, ";", r)] -> l :: m [r]
    | x -> x
  in m t |> PTmList

let expr_list = (sepEndBy term (syn ";")) |> between "[" "]" |>> makeList

let makeFun (args, body) =
  match args with
    | "()" :: [] -> PTmFunUnit body
    | _ -> body |> List.foldBack (fun x t -> PTmFun(x, t)) args
let expr_lambda = tuple2 (syn "fun" >>. (unitparam <|> sepEndBy1 name spaces1) .>> syn "->") term |>> makeFun

let makeLet (vars, value, expr) =
  assert (vars <> []);
  let (h, t) = match vars with h :: t -> (h, t) | _ -> failwith "impossible" in
  if (List.length t = 0) then
    PTmLet (h, value, expr)
  else
    PTmLet (h, makeFun (t, value), expr)
  
let toDefer = function
  | PTmLet(n, r, b) -> PTmLetDefer(n, r, b)
  | x -> PTmDefer x

let expr_let = tuple3 (syn "let" >>. (ws (name <|> opvar) <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  makeLet

let expr_letdefer = tuple3 (syn "let!" >>. (ws name <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  (makeLet >> toDefer)

let expr_defer = syn "<(" >>. term .>> syn ")>" |>> PTmDefer

let expr_if = tuple3 (syn "if" >>. term) (syn "then" >>. term) (syn "else" >>. term) |>> PTmIf

let matchpatterns = (syn "|" <|> syn "") >>. (sepBy1 (tuple2 (term .>> syn "->") term) (syn "|"))

let expr_match = tuple2 (syn "match" >>. term) (syn "with" >>. matchpatterns) |>> PTmMatch

let expr_function = (syn "function" >>. matchpatterns) |>> (fun cases -> PTmFun ("x", PTmMatch (PTmVar "x", cases)))

let expr_fixpoint = tuple2 (syn "fixpoint" >>. ws name) (syn "of" >>. matchpatterns) |>> PTmFixMatch

let expr_apply, eaRef = createParserForwardedToRef<ParsedTerm, unit>()

let not_left_recursive = 
  choice [
    literal_nat
    literal_bool
    literal_unit
    attempt variable
    expr_tuple
    expr_list
    expr_letdefer
    attempt expr_function
    expr_fixpoint
    expr_lambda
    expr_let
    expr_defer
    expr_if
    expr_match
    (syn "(" >>. ws (expr_apply <|> opp.ExpressionParser) .>> syn ")")
  ]

do eaRef := tuple2 not_left_recursive (sepEndBy1 not_left_recursive spaces) |>> (fun (x, ys) -> 
    if (List.isEmpty ys) then 
      x
    else
      List.fold (fun t i -> PTmApply(t, i)) x ys
  )

do termRef := choice [
    syn "begin" >>. term .>> syn "end"
    attempt expr_letdefer
    attempt expr_function
    attempt expr_fixpoint
    attempt expr_lambda
    attempt expr_let
    attempt expr_if
    attempt expr_match
    attempt opp.ExpressionParser
    expr_apply
  ]


opp.TermParser <- attempt expr_apply <|> not_left_recursive

let nml_term = spaces >>. term .>> spaces .>> eof

let parseTerm text =
  match run nml_term text with
    | Success (r, _, _) -> r
    | Failure (msg, _, _) -> ParserFailed msg |> raise
()

