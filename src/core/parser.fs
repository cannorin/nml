module nml.Parser

open FParsec
open nml.Ast
open nml.Typer
open nml.Helper
open nml.Contexts
open FSharp.Collections
open System

exception ParserFailed of string

let ws x = x .>> spaces
let syn x = pstring x |> ws
let between s1 s2 p = syn s1 >>. p .>> syn s2
let listing sep x =
  sepBy1 x sep
let reserved = set [ "let"; "rec"; "local"; "macro"; "in"; "fun"; "true"; "false"; "run"; "if"; "then"; "else"; "type"; "variant"; "inductive"; "match"; "with"; "function"; "fixpoint"; "of"; "begin"; "end"; "open"; "module" ]
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

module TypeParser =

  type ParsedType =
    | PTyVar of qualified_name
    | PTyApp of qualified_name * ParsedType list
    | PTyFun of ParsedType * ParsedType
    | PTyTuple of ParsedType * ParsedType
    | PTyDefer of ParsedType
    | PTyExplicit of ParsedType

  let rec toKnownType ctx =
    function
      | PTyVar ["Unit"] -> Unit
      | PTyVar ["Bool"] -> Bool
      | PTyVar x ->
        match (ctx |> Context.findType x) with
          | Some (DataType (_, [], cts, p)) ->
            DataType (x, [], cts, p)
          | Some (DataTypeSelf (_, [])) ->
            DataTypeSelf (x, [])
          | Some (DataType _)
          | Some (DataTypeSelf _) ->
            sprintf "Insufficient type argument(s) for type constructor '%s'" (sprint_qualified x) |> ParserFailed |> raise
          | Some t -> t
          | None ->
            match x with
              | [v] -> TypeVar v
              | _ -> sprintf "Unknown type '%s'" (sprint_qualified x) |> ParserFailed |> raise
      | PTyDefer x -> Deferred (toKnownType ctx x)
      | PTyFun (a, b) -> Fun (toKnownType ctx a, toKnownType ctx b)
      | PTyTuple (l, r) ->
        match (r, toKnownType ctx r) with
          | PTyTuple _, DataType (["*"], ts, _, _) ->
            TTuple (toKnownType ctx l :: ts)
          | _, x -> TTuple [toKnownType ctx l; x]
      | PTyApp (name, ts) ->
        match (ctx |> Context.findType name) with
          | Some (DataType (_, vts, cts, p)) ->
            if (List.length ts <> List.length vts) then
              sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name) |> ParserFailed |> raise
            
            let ts = ts |> List.map (toKnownType ctx)
            let asgn = 
              vts |> List.map2 (fun x -> function | TypeVar y -> (y, x) |> Some | _ -> None) ts
                  |> List.choose id
                  |> Map.ofList
                  |> Assign in
            let cts' = cts |> List.map (argsmap (substAll asgn)) in
            DataType (name, ts, cts', p)
          | Some (DataTypeSelf (_, vts)) ->
            if List.length ts = List.length vts then
              DataTypeSelf (name, ts |> List.map (toKnownType ctx))
            else
              sprintf "The length of type argument(s) is not correct for type constructor '%s'" (sprint_qualified name) |> ParserFailed |> raise 
          | _ ->
            sprintf "Unknown datatype: '%s'" (sprint_qualified name) |> ParserFailed |> raise
      | PTyExplicit x -> toKnownType ctx x

  let typ, tyRef = createParserForwardedToRef<ParsedType, unit>()

  let op_chars = "+-*/<>%&^~=!?:;".ToCharArray() |> Set.ofArray
  let op_reserved = [ "->"; "*" ]

  let isSymbolicOperatorChar = isAnyOf op_chars

  let (opp, addOp2Ext, addOp2Res) =
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

  let type_defer = syn "<" >>. ws typ .>> syn ">" |>> PTyDefer

  let type_explicit = syn "(" >>. ws typ .>> syn ")" |>> PTyExplicit
 
  let not_left_recursive =
    choice [
      type_explicit;
      type_defer;
      type_var;
    ]

  do taRef := tuple2 not_left_recursive (sepEndBy1 not_left_recursive spaces) |>> (function
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
   
  let parse text =
    match run (spaces >>. typ .>> spaces .>> eof) text with
      | Success (r, _, _) -> r
      | Failure (msg, _, _) -> ParserFailed msg |> raise

module TermParser =

  type ParsedTerm =
    | PTmVar of qualified_name
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
    | PTmModuleVal of string * string
    | PTmOp2 of ParsedTerm * string * ParsedTerm
    | PTmMatch of ParsedTerm * (ParsedTerm * ParsedTerm) list

  let toUntypedTerm ctx pt =
    let rec getVariablePatterns =
      function
        | UTmFreeVar [x] when x <> "_" -> [x]
        | UTmTuple xs 
        | UTmConstruct (_, xs) 
        | UTmApply (UTmFreeVar ["::"], xs) -> xs |> List.map getVariablePatterns |> List.concat 
        | _ -> []

    let rec totc stack (pt, bd) =
      let fv = pt |> tot [] |> getVariablePatterns in
      (pt |> tot (List.append fv stack), bd |> tot (List.append fv stack))
    and tot stack = function
      | PTmVar x ->
        // constructor without arguments
        if (ctx |> Context.findConstructor x (Some []) |> Option.isSome) then
          UTmConstruct (x, [])
        else
          match x with
            | [v] ->
              match (stack |> List.tryFindIndex ((=) v)) with
                | Some i -> UTmBoundVar i
                | None -> UTmFreeVar x
            | _ -> UTmFreeVar x
      | PTmLiteral l -> UTmLiteral l
      | PTmTuple xs -> UTmTuple (xs |> List.map (tot stack))
      | PTmList [] -> UTmConstruct (["Nil"], [])
      | PTmList xs -> xs |> List.rev |> List.fold (fun l x -> UTmConstruct (["Cons"], [tot stack x; l])) (UTmConstruct (["Nil"], []))
      | PTmFun (arg, body) -> UTmFun (body |> tot (arg :: stack))
      | PTmFunUnit body -> UTmFun (body |> tot ("" :: stack))
      // immediate constructor handling
      | PTmApply (PTmVar x, PTmTuple xs) when (ctx |> Context.findConstructor x (Some xs) |> Option.isSome) ->
        UTmConstruct (x, xs |> List.map (tot stack))
      // immediate constructor handling
      | PTmApply (PTmVar x, y) when (ctx |> Context.findConstructor x (Some [y]) |> Option.isSome)  ->
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
        PTmApply (PTmApply (PTmVar [op], l), r) |> tot stack
      | PTmIf (x, t, e) ->
        PTmMatch (x, [ (PTmLiteral (LBool true), t); (PTmLiteral (LBool false), e) ]) |> tot stack
      | PTmMatch (x, cs) ->
        UTmMatch (x |> tot stack, cs |> List.map (totc stack))
      | PTmFixMatch (n, cs) ->
        UTmFixMatch (cs |> List.map (totc (n :: stack)))
      | x ->
        NotImplementedException(sprintf "%A is not yet supported" (x.GetType().Name)) |> raise
    in tot [] pt

  let term, termRef = createParserForwardedToRef<ParsedTerm, unit>()

  let op_chars = "+-*/<>%&|^~=!?:;".ToCharArray() |> Set.ofArray
  let op_reserved = [ "->"; "<("; ")>"; "||"; "&&"; "|>"; ";;" ]

  let isSymbolicOperatorChar = isAnyOf op_chars

  let (opp, addOp2Ext, addOp2Res) =
    prepareOpp
      op_chars
      op_reserved
      (fun prefix remOpChars expr1 expr2 -> PTmOp2 (expr1, prefix + remOpChars, expr2))
 
  // the operator definitions:
  do
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

  let opvar = pstring "(" >>. many1Satisfy (isAnyOf op_chars) .>> pstring ")"

  let unitparam = syn "()" |>> (fun x -> [x])

  let variable = ws (qualified_name <|> (opvar |>> List.singleton)) |>> PTmVar
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
    let (h :: t) = vars in
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

  let expr_function = (syn "function" >>. matchpatterns) |>> (fun cases -> PTmFun ("x", PTmMatch (PTmVar ["x"], cases)))

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

  do opp.TermParser <- attempt expr_apply <|> not_left_recursive

  let parse text =
    match run (spaces >>. term .>> spaces .>> eof) text with
      | Success (r, _, _) -> r
      | Failure (msg, _, _) -> ParserFailed msg |> raise

let inline parseBy parser text =
  match run (spaces >>. parser .>> spaces .>> eof) text with Success (r, _, _) -> r | Failure (msg, _, _) -> ParserFailed msg |> raise 

module TopLevelParser =
  open TermParser
  open TypeParser
  open System.Runtime.InteropServices.ComTypes
  open FParsec

  type PTTypeKind = PTTKVariant | PTTKInductive

  type ParsedTopLevel =
    | PTopOpen of qualified_name
    | PTopModule of string * ParsedTopLevel list
    | PTopLet of string * string list * ParsedTerm
    | PTopTypeDef of kind: PTTypeKind * name:string * tyParams:string list * cstrs: (string * ParsedType option) list
    | PTopDo of ParsedTerm

  let rec toToplevelAndNewContext ctx (moduleName: qualified_name) =
    let inline (+>>) x (xs, ctx) = (x :: xs, ctx)
    let inline orEmpty x = x |> Option.defaultValue (DataType (["*"], [], [], ENull))
    function
      | toplevel :: remaining ->
        match toplevel with
          | PTopOpen qn ->
            TopOpen qn +>> toToplevelAndNewContext (ctx |> Context.openModule qn) moduleName remaining
          | PTopModule (name, toplevels) ->
            let top = TopModule(name, toplevels |> toToplevelAndNewContext ctx (moduleName @ [name]) |> fst)
            top +>> toToplevelAndNewContext (ctx |> Context.addToplevels [top] (fun _ -> id)) moduleName remaining
          | PTopLet (name, args, pt) ->
            let tm =
              TermParser.makeFun (args, pt)
                 |> TermParser.toUntypedTerm ctx
            let (tm, ty) = Typer.inferWithContext (ctx |> Context.termMap fst) tm
            TopLet (name, (ty, tm)) +>> toToplevelAndNewContext (ctx |> Context.addTerm name (ty, tm)) moduleName remaining
          | PTopDo pt ->
            let tm = TermParser.toUntypedTerm ctx pt
            let (tm, ty) = Typer.inferWithContext (ctx |> Context.termMap fst) tm
            TopDo (ty, tm) +>> toToplevelAndNewContext ctx moduleName remaining
          | PTopTypeDef (kind, name, typrms, cstrs) ->
            let qualifiedName = moduleName @ [name]
            let ctx' =
              match kind with
                | PTTKVariant -> ctx
                | PTTKInductive -> ctx |> Context.addType name (DataTypeSelf(qualifiedName, typrms |> List.map TypeVar))
            let cstrs' =
              cstrs |> List.map (fun (n, pt) -> (n, pt |> Option.map (TypeParser.toKnownType ctx') |> orEmpty))
                    |> List.map (fun (n, ty) ->
                        match ty with
                          | DataType (["*"], ts, [], _) ->
                            { name = n; args = ts; isRecursive = ts |> List.exists (containsSelf qualifiedName) }
                          | _ ->
                            { name = n; args = [ty]; isRecursive = containsSelf qualifiedName ty }
                       )
            let ty = DataType(qualifiedName, typrms |> List.map TypeVar, cstrs', ENull)
            TopTypeDef(name, ty) +>> toToplevelAndNewContext (ctx |> Context.addType name ty) moduleName remaining
      | [] -> ([], ctx)
          

  let until sym parser : Parser<_, unit> =
    let s = charsTillString sym true Int32.MaxValue
    fun stream ->
      let state = stream.State
      let reply = s stream
      if reply.Status = Ok then
        try
          reply.Result |> parser |> Reply
        with
          | ParserFailed msg ->
            stream.BacktrackTo(state)
            Reply(Error, messageError msg)
      else
        stream.BacktrackTo(state)
        Reply(Error, expected sym)


  let untilOneOf syns parser =
    syns |> List.map (fun syn -> attempt (charsTillString syn true Int32.MaxValue |>> parser)) |> choice
  
  let toplevel, tlRef = createParserForwardedToRef<ParsedTopLevel, unit>()

  let toplevel_open = syn "open" >>. ws qualified_name .>> syn ";;" |>> PTopOpen

  let toplevel_module = tuple2 (syn "module" >>. ws name) (syn "=" >>. syn "begin" >>. (sepEndBy toplevel spaces1 .>> syn "end")) |>> PTopModule

  let toplevel_let = tuple2 (syn "let" >>. ws name <+> (unitparam <|> sepEndBy name spaces1) .>> syn "=") (TermParser.parse |> until ";;") |>> (fun (name :: args, body) -> PTopLet (name, args, body))

  let variantCase = (tuple2 (ws name) ( (syn "of" >>. typ |>> Some) <|> (syn "" |>> fun _ -> None) ))

  let toplevel_variantdef = 
    tuple2 (syn "variant" >>. sepEndBy1 name spaces1)
           (syn "=" >>. (syn "|" <|> syn "") >>. 
              until "end" (String.splitBy "|" >> Array.map (parseBy variantCase) ) |>> List.ofArray
           )
      |>> function
        | name :: tprms, xs -> PTopTypeDef(PTTKVariant, name, tprms, xs)
        | _,_ -> "" |> ParserFailed |> raise

  let toplevel_inductivedef = 
    tuple2 (syn "inductive" >>. sepEndBy1 name spaces1) 
           (syn "=" >>. (syn "|" <|> syn "") >>. 
              until "end" (String.splitBy "|" >> Array.map (parseBy variantCase) ) |>> List.ofArray
           )
      |>> function
        | name :: tprms, xs -> PTopTypeDef(PTTKInductive, name, tprms, xs)
        | _,_ -> "" |> ParserFailed |> raise
  
  let toplevel_do = syn "do" >>. (TermParser.parse |> until ";;") |>> PTopDo

  do tlRef := choice [
      toplevel_open;
      toplevel_module;
      attempt toplevel_let;
      attempt toplevel_do;
      attempt toplevel_variantdef;
      attempt toplevel_inductivedef;
      attempt (TermParser.parse |> until ";;" |>> PTopDo)
    ]

  let implicitModule = sepEndBy toplevel spaces

  exception ParserFailedAtEof

  let parse text =
    match run (spaces >>. implicitModule .>> spaces .>> eof) text with
      | Success (r, _, _) -> r
      | Failure (msg, err, _) ->
        use str = new CharStream(text, 0, text.Length) in
        if err.Position.Index = str.IndexOfLastCharPlus1 then
          ParserFailedAtEof |> raise
        else
          ParserFailed msg |> raise