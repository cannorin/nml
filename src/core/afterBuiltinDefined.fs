namespace nml.Parser
open nml
open nml.Ast
open nml.Contexts
open nml.Helper
open nml.Parser
open nml.Parser.NmlParser
open nml.Parser.ParserUtils
open nml.Builtin
open System.IO

[<AutoOpen>]
module AfterBuiltinDefined =
  module ParserUtils =
    let inline toToplevelAndNewContext (ctx: Context<'Term>)
                                (typeExtractor: 'Term -> PolyType)
                                (termConverter: TypedTerm -> 'Term)
                                (moduleName: qualified_name)
                                (ptop: ParsedTopLevelWithSource list)
                                : TopLevel<'Term> list * Context<'Term> = 
      toToplevelBase
        ctx
        parseToplevelWithFileName
        (fun ctx -> Typer.inferWithContext (ctx |> Context.termMap typeExtractor) >> termConverter)
        (defaultContext |> Context.termMap termConverter)
        moduleName
        ptop

    let inline toToplevelAndNewContextTyped (ctx: TermContext) modName ptop : _ * TermContext =
      toToplevelAndNewContext ctx (Term.getType >> Typer.generalizeAllFV) id modName ptop

    let inline toToplevelAndNewContextEval (ctx: EvalContext) modName ptop : _ * EvalContext =
      toToplevelAndNewContext
        ctx
        fst
        (fun tm ->
          tm |> Term.getType |> Typer.generalizeAllFV,
          Term.eraseType tm)
        modName
        ptop
    