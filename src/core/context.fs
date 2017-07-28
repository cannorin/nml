module nml.UniversalContext

open nml.Ast
open nml.Helper
open Microsoft.FSharp.Collections

type ContextItem =
  | TypeContext of Type
  //| TopLevelContext of TopLevel
  | TermContext of string * Type * UntypedTerm

type Context = ContextItem list

let printContext ctx =
  for x in ctx do
    match x with
      | TypeContext (DataType (name, targs, cts, _, _)) when (List.isEmpty cts |> not) ->
        let s = List.concat [targs |> List.map to_s; [name]] |> String.concat " " in
        let cs = 
          cts |> List.map ((fun (n, ts) -> 
              if (List.length ts > 0) then
                sprintf "%s of %s" n (ts |> List.map to_s |> String.concat " * ") 
              else n
            )) |> String.concat " | " in
        printfn "- type %s = %s" s cs
      | TermContext (n, ty, te) ->
        printfn "- let %s : %s" (handle_op n) (to_s ty)
      | _ -> ()

let findType name ctx =
  ctx |> List.choose (function | TypeContext (DataType (vs, ts, cts, st, h)) when vs = name -> DataType (vs, ts, cts, st, h) |> Some | _ -> None) |> List.tryHead

let findConstructor<'a> name (args : 'a list option) ctx =
  let al = args |> Option.map List.length in
  ctx 
    |> List.choose (function 
        | TypeContext (DataType (vs, targs, ts, s, h)) when (List.isEmpty ts |> not) ->
          ts 
            |> List.tryFind (fun (n, xs) -> n = name && (al |> Option.map ((=) (List.length xs)) ?| true))
            |> Option.map (fun (_, xs) -> (DataType (vs, targs, ts, s, h), xs))
        | _ -> None
      )
    |> List.tryHead

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


