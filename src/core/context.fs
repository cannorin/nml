module nml.UniversalContext

open nml.Ast
open nml.Helper
open Microsoft.FSharp.Collections

type ContextItem =
  | TypeContext of string * Type
  | ModuleContext of string * ContextItem list
  | TermContext of string * Type * UntypedTerm

type Context = ContextItem list

let printContext ctx =
  for x in ctx do
    match x with
      | TypeContext (_, DataType (name, targs, cts, _)) ->
        let s = List.concat [targs |> List.map to_s; [name]] |> String.concat " " in
        let cs = 
          cts |> List.map ((fun c -> 
              if (List.length c.args > 0) then
                sprintf "%s of %s" c.name (c.args |> List.map to_s |> String.concat " * ") 
              else c.name
            )) |> String.concat " | "
        in
        if (String.length cs > 0) then
          printfn "- type %s = %s" s cs
        else
          printfn "- type %s" s
      | TypeContext (name, ty) -> printfn "- type %s = %s" name (to_s ty)
      | TermContext (n, ty, te) ->
        printfn "- let %s : %s" (handle_op n) (to_s ty)
      | ModuleContext (n, _) -> printfn "- module %s = begin .. end" n

let findType name ctx =
  ctx |> List.choose (function | TypeContext (nm, t) when nm = name -> Some t | _ -> None) |> List.tryHead

let findConstructor<'a> name (args : 'a list option) ctx =
  let al = args |> Option.map List.length in
  ctx 
    |> List.choose (function 
        | TypeContext (_, DataType (vs, targs, ts, _)) ->
          ts 
            |> List.tryFind (fun c -> c.name = name && (al |> Option.map ((=) (List.length c.args)) ?| true))
            |> Option.map (fun c -> (DataType (vs, targs, ts, ENull), c.args))
        | _ -> None
      )
    |> List.tryHead

let rec findInModule names ctx =
  match names with
    | name :: [] -> 
      ctx |> List.choose (function | TermContext (s, t, u) when name = s -> Some (t, u) | _ -> None )
          |> List.tryHead
    | mdl :: names ->
      ctx |> List.choose (function 
              | ModuleContext (nm, ctx) when nm = mdl ->
                findInModule names ctx
              | _ -> None
             )
          |> List.tryHead
    | [] -> None
      

let toTyperMap ctx =
  ctx
    |> List.choose (function | TermContext (n, t, _) -> Some (n, t) | _ -> None)
    |> List.rev |> Map.ofList |> Map.toList

let toEvalContext ctx =
  ctx
    |> List.choose (function | TermContext (n, _, t) -> Some (n, t) | _ -> None)
    |> Map.ofList

let typerFind name ctx =
  ctx 
    |> List.choose (function | TermContext (s, t, _) when name = s -> Some t | _ -> None )
    |> List.tryHead

let evalFind name ctx =
  ctx
    |> List.choose (function | TermContext (s, _, t) when name = s -> Some t | _ -> None )
    |> List.tryHead

(*
let findModule mdfrs ctx =
  ctx 
    |> List.choose (function
        | TopLevelContext (Module (m, ts)) when m = mdfrs -> Some (Module (m, ts))
        | _ -> None
      )
    |> List.tryHead
*)

let typerAdd name t ctx =
  TermContext (name, t, UTmFreeVar name) :: (ctx |> List.filter (function | TermContext (s, _, _) -> s <> name | _ -> true ))


