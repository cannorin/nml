module nml.Parser.NmlParser

open FParsec
open nml.Ast
open nml.Typer
open nml.Helper
open nml.Contexts
open FSharp.Collections
open System
open nml.Parser
open nml.Parser.ParserUtils

[<AutoOpen>]
module private ParsecUtils =
  let inline (<||>) a b = attempt (a |>> Choice1Of2) <|> (b |>> Choice2Of2)
  let ws x = x .>> spaces
  let syn x = pstring x |> ws
  let between s1 s2 p = syn s1 >>? p .>>? syn s2
  let listing sep x =
    sepBy1 x sep

  let toplevel_keywords =
    set [ "open"; "module"; "type"; "variant"; "inductive"; "def"; "do"; ";;" ]

  let term_keywords =
    set [ "let"; "rec"; "local"; "macro"; "in"; "fun"; 
          "run"; "match"; "with"; "function"; "fixpoint";
          "of"; "if"; "then"; "else"; "true"; "false"; "begin"; "end";
        ]

  let reserved = Set.union toplevel_keywords term_keywords
  
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

  let name = identifier
  let qualified_name = sepBy1 name (pstring ".")

  let inline getInfo x =
    getPosition .>>. x .>>. getPosition
      |>> fun ((startpos, x), endpos) -> (x, {startPos=startpos; endPos=endpos})

  let inline prepareOpp op_chars op_reserved op2Handler =
    let opp = new OperatorPrecedenceParser<'t, string, unit>()
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
                              op2Handler prefix
                             )
      in
      opp.AddOperator(op)
    let addOp2Res x pcd asy =
      for i in op_chars |> Set.map (fun c -> sprintf "%s%c" x c)
                        |> Set.filter (fun s -> op_reserved |> List.contains s |> not) do
        addOp2Ext i pcd asy
    
    (opp, addOp2Ext, addOp2Res)
  
  let optional opt = attempt (opt >>% ()) <|> spaces

  let unitparam = syn "()" |>> List.singleton
  
  let infoConst cstr x =
    x |> getInfo |>> withinfof cstr



let ty, tyRef = createParserForwardedToRef<ParsedType, unit>()
let term, termRef = createParserForwardedToRef<ParsedTermWithInfo, unit>()
let toplevel, toplevelRef = createParserForwardedToRef<ParsedTopLevelWithInfo, unit>()

// type parser
let _ =
  let (opp, addOp2Ext, addOp2Res) =
    let op_chars = "+-*/<>%&^~=!?:;".ToCharArray() |> Set.ofArray
    let op_reserved = [ "->"; "*" ]
    prepareOpp
      op_chars
      op_reserved 
      (fun prefix remOpChars expr1 expr2 ->
        match (prefix + remOpChars) with
          | "->" ->
            PTyFun (expr1, expr2)
          | "*" ->
            PTyTuple (expr1, expr2)
          | x ->
            PTyApp ([x], [expr1; expr2]))
  
  // the operator definitions:
  do
    addOp2Ext "->" 10 Associativity.Right
    addOp2Ext "*"  50 Associativity.Right
    addOp2Ext "&"  30 Associativity.Left
    addOp2Ext "="  30 Associativity.Left
    addOp2Ext "^"  34 Associativity.Right
    addOp2Ext "?" 35 Associativity.Left
    addOp2Ext ":" 35 Associativity.Right
    addOp2Ext "+"  40 Associativity.Left
    addOp2Res "-"  40 Associativity.Left
    addOp2Ext "%"  50 Associativity.Left
    addOp2Ext "/"  50 Associativity.Left
  // end of definitions.

  let type_var = ws qualified_name |>> PTyVar

  let type_app, taRef = createParserForwardedToRef<ParsedType, unit>()

  let type_defer = syn "<" >>. ws ty .>> syn ">" |>> PTyDefer

  let type_explicit = syn "(" >>. ws ty .>> syn ")" |>> PTyExplicit
 
  let not_left_recursive =
    choice [
      type_explicit;
      type_defer;
      type_var;
    ]

  do taRef := not_left_recursive .>>.? sepEndBy1 not_left_recursive spaces |>> (function
      | x, [] -> x
      | PTyVar x, argst -> PTyApp (x, argst |> List.rev)
      | _,_ -> failwith "impossible"
    )

  do tyRef := 
      choice [
          attempt opp.ExpressionParser;
          type_app;
        ]
  
  do opp.TermParser <- attempt type_app <|> not_left_recursive

// term parser
let _ =
  let op_chars = "+-*/<>%&|^~=!?:;".ToCharArray() |> Set.ofArray
  let op_reserved = [ "->"; "<("; ")>"; "||"; "&&"; "|>"; ";;" ]

  let (opp, addOp2Ext, addOp2Res) =
    prepareOpp
      op_chars
      op_reserved
      (fun prefix remOpChars expr1 expr2 ->
        let newInfo =
          Option.map2 (fun x y -> { startPos = x.startPos; endPos = x.endPos }) expr1.info expr2.info
        { item = PTmOp2 (expr1, prefix + remOpChars, expr2); info = newInfo } )
 
  // the operator definitions:
  do
    addOp2Ext "!;" 10 Associativity.Right
    addOp2Res ";"  10 Associativity.Right
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

  let opvar = pstring "(" >>? many1Satisfy (isAnyOf op_chars) .>> pstring ")"
  
  let variable = ws (qualified_name <|> (opvar |>> List.singleton)) |> infoConst PTmVar
  let literal_nat = ws puint32 <?> "Nat" |> infoConst (LNat >> PTmLiteral)
  let literal_bool = ((stringReturn "true" true) <|> (stringReturn "false" false)) |> ws |> infoConst (LBool >> PTmLiteral)
  let literal_unit = syn "()" |> infoConst (fun _ -> PTmLiteral LUnit)

  let inline (<+>) a b =
    tuple2 a b |>> (fun (x, y) -> List.append [x] y)

  let expr_tuple = 
    (term |> listing (syn ",")) |> between "(" ")"
    |> infoConst (fun xs -> if (List.length xs = 1) then xs.[0].item else PTmTuple xs)

  let expr_list = (sepEndBy term (syn ";")) |> between "[" "]" |> infoConst makeList

  let expr_lambda = 
    tuple2
      (syn "fun" >>? (unitparam <|> sepEndBy1 name spaces1) .>> syn "->") term 
    |> infoConst makeFun

  let expr_let = 
    tuple3 
      (syn "let" >>? (ws (name <|> opvar) <+> (unitparam <|> sepEndBy name spaces1)) .>>? syn "=")
      (term .>>? syn "in")
      term
    |> infoConst makeLet

  let expr_letdefer =
    tuple3
      (syn "let!" >>? (ws name <+> (unitparam <|> sepEndBy name spaces1)) .>>? syn "=")
      (term .>>? syn "in")
      term
    |> infoConst makeLet |>> toDefer

  let expr_defer = syn "<(" >>. term .>> syn ")>" |> infoConst PTmDefer

  let expr_if = tuple3 (syn "if" >>? term) (syn "then" >>? term) (syn "else" >>? term) |> infoConst PTmIf

  let matchpatterns = (syn "|" <|> syn "") >>? (sepBy1 (tuple2 (term .>>? syn "->") term) (syn "|"))

  let expr_match = tuple2 (syn "match" >>. term) (syn "with" >>. matchpatterns) |> infoConst PTmMatch

  let expr_function = 
    (syn "function" >>? matchpatterns)
    |> getInfo
    |>> (fun (cases, info) -> withinfo info <| PTmFun ("x", withinfo info <| PTmMatch (withinfo info <| PTmVar ["x"], cases)))

  let expr_fixpoint =
    tuple2
      (syn "fixpoint" >>? ws name)
      (syn "of" >>? matchpatterns)
    |> infoConst PTmFixMatch

  let expr_apply, eaRef = createParserForwardedToRef<ParsedTermWithInfo, unit>()

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
      (syn "(" >>? ws (expr_apply <|> opp.ExpressionParser) .>> syn ")")
    ] 

  do eaRef :=
      not_left_recursive .>>.? sepEndBy1 not_left_recursive spaces
      |> infoConst (fun (x, ys) -> 
        if (List.isEmpty ys) then 
          x.item
        else
          List.fold (fun t i -> PTmApply(t, i) |> sameInfoOf t) x ys |> itemof
      )

  do termRef :=
      choice [
        syn "begin" >>? term .>> syn "end"
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

  do opp.TermParser <- attempt expr_apply <|> not_left_recursive

// toplevel parser
let implicitModule =
  let inline (<+>) a b =
    a .>>.? b |>> (fun (x, y) -> List.append [x] y)

  let toplevel_open = syn "open" >>? ws qualified_name .>>? optional (syn ";;") |> infoConst PTopOpen

  let toplevel_module =
    tuple2
      (syn "module" >>? ws name .>>? syn "=")
      (syn "begin" >>? many toplevel .>>? syn "end")
    |> infoConst PTopModule
  
  let toplevel_let =
    tuple2
      (syn "def" >>? sepEndBy name spaces1 .>>? syn "=")
      (ws term .>>? optional (syn ";;"))
    |> infoConst (fun (name :: args, body) -> PTopTermDef (name, args, body))
  
  let toplevel_do = syn "do" >>? ws term .>>? optional (syn ";;") |> infoConst PTopDo
  
  let variantCase = 
    tuple2
      (ws name)
      ( (syn "of" >>? ty |>> Some) <|> (syn "" |>> fun _ -> None) )
  
  let toplevel_variantdef = 
    tuple2 (syn "variant" >>? sepEndBy1 name spaces1)
           (syn "=" >>? (syn "|" <|> syn "") >>?
              sepEndBy1 variantCase (syn "|")
           )
      |> infoConst (function
        | name :: tprms, xs -> PTopTypeDef(PTTKVariant, name, tprms, xs)
        | _,_ -> "" |> ParserFailed |> raise
      )

  let toplevel_inductivedef = 
    tuple2 (syn "inductive" >>? sepEndBy1 name spaces1)
           (syn "=" >>? (syn "|" <|> syn "") >>?
              sepEndBy1 variantCase (syn "|")
           )
      |> infoConst (function
        | name :: tprms, xs -> PTopTypeDef(PTTKInductive, name, tprms, xs)
        | _,_ -> "" |> ParserFailed |> raise
      )
  

  do toplevelRef := choice [
      toplevel_open;
      toplevel_module;
      attempt toplevel_let;
      attempt toplevel_do;
      attempt toplevel_variantdef;
      attempt toplevel_inductivedef;
      attempt term |> infoConst PTopDo
    ]
  
  many toplevel

let inline private parse parser text =
  match run (spaces >>. parser .>> spaces .>> eof) text with
      | Success (r, _, _) -> r
      | Failure (msg, err, _) ->
          ParserFailed msg |> raise

let inline parseTerm text = parse term text
let inline parseType text = parse ty text
let inline parseToplevel text = parse implicitModule text