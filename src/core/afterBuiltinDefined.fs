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
    let toToplevelAndNewContext ctx moduleName = 
      toToplevelBase ctx parseToplevelWithFileName defaultContext moduleName
    