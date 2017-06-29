module nml.Parser

open FParsec
open nml.Ast
open nml.Typer
open nml.Helper
open FSharp.Collections

exception ParserFailed of string

let term, termRef = createParserForwardedToRef<UntypedTerm, unit>()
// let typ, typRef = createParserForwardedToRef<Type, unit>()

let ws x = x .>> spaces
let syn x = pstring x |> ws
let between s1 s2 p = syn s1 >>. p .>> syn s2
let listing sep x =
  sepBy1 x sep
let reserved = set [ "let"; "rec"; "local"; "macro"; "in"; "fun"; "true"; "false"; "run"; "if"; "then"; "else"; "type"; "match"; "with";  ]
let identifierString = many1Satisfy (List.concat [['a'..'z']; ['A'..'z']; ['_']; ['0'..'9']] |> isAnyOf)
let identifier : Parser<string, unit> =
  let expectedIdentifier = expected "identifier"
  fun stream ->
    let state = stream.State
    let reply = identifierString stream
    if reply.Status = Ok && not (reserved |> Set.contains reply.Result || System.Char.IsDigit (reply.Result.[0])) then reply
    else
      stream.BacktrackTo(state)
      Reply(Error, expectedIdentifier)

let op_chars = "+-*/<>%&|^~=?:;".ToCharArray () |> Set.ofArray
let op_reserved = set [ "::"; ";"; "->"; "="; "<>"; "&"; "|"; "&&"; "||"; ]
let operatorString = many1Satisfy (op_chars |> isAnyOf)
let genop isUser : Parser<string, unit> =
  let expectedOperator = expected "operator"
  fun stream ->
    let state = stream.State
    let reply = operatorString stream
    if reply.Status = Ok && not (isUser && op_reserved |> Set.contains reply.Result) then
      reply
    else
      stream.BacktrackTo(state)
      Reply(Error, expectedOperator)

let name = identifier
let op = genop false
let op_user = genop true

(*
let type_nat = syn "Nat" >>% Nat
let type_bool = syn "Bool" >>% Bool
let type_unit = syn "Unit" >>% Unit
let type_var = ws name |>> TypeVar
let type_fun = (typ .>> syn "->") .>>. typ
*)


let unitparam = syn "()" |>> (fun x -> [x])

let variable = ws name |>> UVar
let literal_nat = ws pint32 <?> "int32" |>> (LNat >> ULiteral)
let literal_bool = ((stringReturn "true" true) <|> (stringReturn "false" false)) |> ws |>> (LBool >> ULiteral)
let literal_unit = syn "()" >>% ULiteral LUnit

let inline (<+>) a b =
  tuple2 a b |>> (fun (x, y) -> List.append [x] y)

let expr_tuple = (term |> listing (syn ",")) |> between "(" ")" |>> (fun xs -> if (List.length xs = 1) then xs.[0] else UTuple xs)

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
    ULet(h, makeFun (t, value), expr)
let toDefer = function
  | ULet(n, r, b) -> ULetDefer(n, r, b)
  | x -> UDefer x
let expr_let = tuple3 (syn "let" >>. (ws (name <|> (syn "(" >>. op_user .>> syn ")")) <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  makeLet
let expr_letdefer = tuple3 (syn "let!" >>. (ws name <+> (unitparam <|> sepEndBy name spaces1)) .>> syn "=") (term .>> syn "in") term |>>  (makeLet >> toDefer)

let expr_defer = syn "<(" >>. term .>> syn ")>" |>> UDefer

let expr_if = tuple3 (syn "if" >>. term) (syn "then" >>. term) (syn "else" >>. term) |>> UIf

let expr_match = tuple2 (syn "match" >>. term) (syn "with" >>. sepBy1 (tuple2 (term .>> syn "->") term) (syn "|")) |>> UMatch

let expr_apply, eaRef = createParserForwardedToRef<UntypedTerm, unit>()
//let expr_op2, opRef = createParserForwardedToRef<UntypedTerm, unit>()

let not_left_recursive = 
  choice [
    literal_nat
    literal_bool
    literal_unit
    expr_lambda
    expr_tuple
    expr_letdefer
    expr_let
    expr_defer
    expr_if
    expr_match
    variable
    (syn "(" >>. ws expr_apply .>> syn ")")
  ]

do eaRef := tuple2 not_left_recursive (sepEndBy not_left_recursive spaces) |>> (fun (x, ys) -> 
    if (List.isEmpty ys) then 
      x
    else
      List.fold (fun t i -> UApply(t, i)) x ys
  )

do termRef := choice [
    expr_apply
    not_left_recursive
  ]

let nml_term = attempt (spaces >>. term .>> spaces .>> eof)

let parseTerm text =
  match run nml_term text with
    | Success (r, _, _) -> r
    | Failure (msg, _, _) -> ParserFailed msg |> raise
()
