module nml.UniversalContext

open nml.Ast
open nml.Helper
open Microsoft.FSharp.Collections

type ContextItem =
  | TermContext of string * Type * UntypedTerm

type Context = ContextItem list

let printContext ctx =
  for x in ctx do
    match x with
      | TermContext (n, ty, te) ->
        printfn "- let %s : %s" n (to_s ty)

let toTyperMap ctx =
  ctx
    |> List.choose (function | TermContext (n, t, _) -> Some (n, t))
    |> List.rev |> Map.ofList |> Map.toList

let toEvalContext ctx =
  ctx
    |> List.choose (function | TermContext (n, _, t) -> Some (n, t))
    |> Map.ofList

let typerFind name ctx =
  ctx 
    |> List.choose (function | TermContext (s, t, _) when name = s -> Some t | _ -> None )
    |> List.tryHead

let evalFind name ctx =
  ctx
    |> List.choose (function | TermContext (s, _, t) when name = s -> Some t | _ -> None )
    |> List.tryHead

let typerAdd name t ctx =
  TermContext (name, t, UVar name) :: (ctx |> List.filter (function | TermContext (s, _, _) -> s <> name ))


