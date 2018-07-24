module nml.Contexts

open nml.Ast
open nml.Helper
open Microsoft.FSharp.Collections

type Qualified<'Item> = Qualified of 'Item * string list

type ContextItem<'Term> =
  | TypeContext of string * Type
  | ModuleContext of string * ContextItem<'Term> list
  | TermContext of string * 'Term

type Context<'Term> = ContextItem<'Term> list

type InferredTermContext = Context<UntypedTerm * Type>

type TyperContext = Context<Type>

type EvalContext = Context<UntypedTerm>

module Context =
  open System

  let rec termMap f ctx =
    ctx |> List.map (function
            | TermContext (name, tm) -> TermContext (name, f tm)
            | TypeContext (name, ty) -> TypeContext (name, ty)
            | ModuleContext (name, ctx) -> ModuleContext (name, termMap f ctx)
           )
  
  let rec tryFindRec chooser (qualifiedName: qualified_name) ctx =
    match qualifiedName with
      | [] -> None
      | name :: [] ->
        ctx |> List.choose (chooser name)
            |> List.tryHead
      | modName :: qualifiedName ->
        [
          ctx |> List.choose (chooser "")
              |> List.tryHead;
          ctx |> List.choose (function | ModuleContext (n, ctx) when n = modName -> Some ctx | _ -> None)
              |> List.choose (tryFindRec chooser qualifiedName)
              |> List.tryHead
        ] |> List.choose id |> List.tryHead
  
  let inline findTerm qualifiedName ctx =
    tryFindRec (fun name ->
      function
        | TermContext (n, tm) when n = name -> Some tm
        | _ -> None
    ) qualifiedName ctx

  let inline findType qualifiedName ctx =
    tryFindRec (fun name -> 
      function
        | TypeContext (n, ty) when n = name -> Some ty
        | TypeContext (_, TyDataType(n, _, _, _, _)) & TypeContext (_, ty) when n = qualifiedName -> Some ty
        | _ -> None
    ) qualifiedName ctx

  let inline findConstructor qualifiedName (args: 'a list option) ctx =
    let aLen = args |> Option.map List.length
    tryFindRec (fun name ->
                  function
                    | TypeContext (_, TyDataType (vs, targs, ts, p, info)) ->
                      ts |> List.tryFind (fun c -> c.name = name && aLen |> Option.map ((=) (List.length c.args)) ?| true)
                         |> Option.map (fun c -> (TyDataType (vs, targs, ts, p, info), c.args))
                    | _ -> None

               ) qualifiedName ctx

  let inline findModuleItems qualifiedName ctx =
    let ctx' =
      let rec f ct =
        function
          | [] -> []
          | name :: remaining ->
            let cts' =
              ct |> List.choose (function | ModuleContext (n, ctx') when n = name -> Some ctx' | _ -> None)
            if List.length remaining = 0 then
              List.concat cts'
            else
              cts' |> List.map (fun ct' -> f ct' remaining)
                   |> List.concat
      f ctx qualifiedName
    ctx'

  let inline openModule qualifiedName ctx =
    findModuleItems qualifiedName ctx @ ctx

  let inline addTerm name tm ctx = TermContext (name, tm) :: ctx

  let inline removeTerm name ctx =
    ctx |> List.filter (function | TermContext (n, _) when n = name -> false | _ -> true)

  let inline addType name ty ctx =
    TypeContext (name, ty) :: ctx   
   
  let rec private at tls _targetCtx _ctx evaluator =
    match tls with
      | [] -> _targetCtx
      | toplevel :: remainings ->
        match toplevel with
          | TopOpen (name, _) ->
            let c = findModuleItems name _ctx
            at remainings (c @ _targetCtx) (c @ _ctx) evaluator
          | TopTypeDef (name, ty, _) ->
            let extend c =
              TypeContext (name, ty) :: c
            at remainings (extend _targetCtx) (extend _ctx) evaluator
          | TopModule (name, subtls, _) ->
            let extend c =
              ModuleContext (name, at subtls [] _ctx evaluator) :: c
            at remainings (extend _targetCtx) (extend _ctx) evaluator
          | TopTermDef (name, tm, _) ->
            let extend c =
              TermContext (name, evaluator _ctx tm) :: c
            at remainings (extend _targetCtx) (extend _ctx) evaluator
          | TopDo (tm, _) ->
            evaluator _ctx tm |> ignore
            at remainings _targetCtx _ctx evaluator

  let fromToplevels ctx evaluator toplevels =
    at toplevels [] ctx evaluator

  let addToplevels toplevels evaluator ctx =
    at toplevels ctx ctx evaluator

  let toTyperMap ctx =
    ctx
      |> List.choose (function | TermContext (n, t) -> Some (n, t) | _ -> None)
      |> List.rev |> Map.ofList |> Map.toList
  
  let print ctx = 
    let rec p idt cs = [
        for c in cs do
          yield!
            match c with
              | TypeContext (name, ty) -> [ sprintf "type %s = %s" (handle_op name) (to_s ty) |> indent idt ]
              | TermContext (name, (ty, _)) -> [ sprintf "let %s : %s"  (handle_op name) (to_s ty) |> indent idt ]
              | ModuleContext (name, cs') ->
                (sprintf "module %s =" name |> indent idt) :: p (idt + 2) cs'
      ]
    p 0 ctx |> String.concat Environment.NewLine
