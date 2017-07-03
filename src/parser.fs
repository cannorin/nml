module nml.Parser

open FParsec
open nml.Ast
open nml.Typer
open nml.Helper
open FSharp.Collections

exception ParserFailed of string

let term, termRef = createParserForwardedToRef<UntypedTerm, unit>()
//let typ, typRef = createParserForwardedToRef<Type, unit>()

let ws x = x .>> spaces
let syn x = pstring x |> ws
let between s1 s2 p = syn s1 >>. p .>> syn s2
let listing sep x =
  sepBy1 x sep
let reserved = set [ "let"; "rec"; "local"; "macro"; "in"; "fun"; "true"; "false"; "run"; "if"; "then"; "else"; "type"; "match"; "with";  ]
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

let op_chars = "+-*/<>%&|^~=!?:;.".ToCharArray() |> Set.ofArray
let op_reserved = [ "->"; "<("; ")>"; "||"; "&&"; "|>" ]

let isSymbolicOperatorChar = isAnyOf op_chars
//let remainingOpChars_ws = manySatisfy isSymbolicOperatorChar .>> spaces

let opp = new OperatorPrecedenceParser<UntypedTerm, string, unit>()

opp.OperatorConflictErrorFormatter <-
  fun (pos1, op1, afterString1) (pos2, op2, afterString2) ->
    let msg = sprintf "The operator '%s' conflicts with the previous operator '%s' at %A."
                      (op2.String + afterString2)
                      (op1.String + afterString1) pos1
    in messageError msg

let addOp2Ext prefix precedence associativity =
  let op = InfixOperator (prefix, 
                          manySatisfy (isAnyOf op_chars) .>> spaces,
                          precedence, 
                          associativity, 
                          (),
                          fun remOpChars expr1 expr2 -> UOp2 (expr1, prefix + remOpChars, expr2)
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

let variable = ws (name <|> opvar) |>> UVar
let literal_nat = ws puint32 <?> "Nat" |>> (LNat >> ULiteral)
let literal_bool = ((stringReturn "true" true) <|> (stringReturn "false" false)) |> ws |>> (LBool >> ULiteral)
let literal_unit = syn "()" >>% ULiteral LUnit

let inline (<+>) a b =
  tuple2 a b |>> (fun (x, y) -> List.append [x] y)

let expr_tuple = (term |> listing (syn ",")) |> between "(" ")" |>> (fun xs -> if (List.length xs = 1) then xs.[0] else UTuple xs)

let makeList t = 
  let rec m = function
    | [UOp2 (l, ";", r)] -> l :: m [r]
    | x -> x
  in m t |> UList

let expr_list = (sepEndBy term (syn ";")) |> between "[" "]" |>> makeList

let makeFun (args, body) =
  match args with
    | "()" :: [] -> UFunUnit body
    | _ -> body |> List.foldBack (fun x t -> UFun(x, t)) args
let expr_lambda = tuple2 (syn "fun" >>. (unitparam <|> sepEndBy1 name spaces1) .>> syn "->") term |>> makeFun

let makeLet (vars, value, expr) =
  assert (vars <> []);
  let (h :: t) = vars in
  if (List.length t = 0) then
    ULet (h, value, expr)
  else
    ULet (h, makeFun (t, value), expr)
  
let toDefer = function
  | ULet(n, r, b) -> ULetDefer(n, r, b)
  | x -> UDefer x

let expr_let = tuple3 (syn "let" >>. (ws (name <|> opvar) <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  makeLet

let expr_letdefer = tuple3 (syn "let!" >>. (ws name <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  (makeLet >> toDefer)

let expr_defer = syn "<(" >>. term .>> syn ")>" |>> UDefer

let expr_if = tuple3 (syn "if" >>. term) (syn "then" >>. term) (syn "else" >>. term) |>> UIf

let expr_match = tuple2 (syn "match" >>. term) (syn "with" >>. sepBy1 (tuple2 (term .>> syn "->") term) (syn "|")) |>> UMatch

let expr_apply, eaRef = createParserForwardedToRef<UntypedTerm, unit>()

let not_left_recursive = 
  choice [
    literal_nat
    literal_bool
    literal_unit
    attempt variable
    expr_lambda
    expr_tuple
    expr_list
    expr_letdefer
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
      List.fold (fun t i -> UApply(t, i)) x ys
  )

do termRef := choice [
    attempt expr_apply
    opp.ExpressionParser
  ]


opp.TermParser <- attempt expr_apply <|> not_left_recursive

let nml_term = spaces >>. term .>> spaces .>> eof

let parseTerm text =
  match run nml_term text with
    | Success (r, _, _) -> r
    | Failure (msg, _, _) -> ParserFailed msg |> raise
()
