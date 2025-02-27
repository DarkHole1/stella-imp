open AbsStella

type tyError =
  | MissingMain
  | UndefinedVariable
  | UnexpectedTypeOfExpression
  | NotAFunction
  | NotATuple
  | NotARecord
  | NotAList
  | UnexpectedLambda
  | UnexpectedTypeForParameter
  | UnexpectedTuple
  | UnexpectedRecord
  | UnexpectedVariant
  | UnexpectedList
  | UnexpectedInjection
  | MissingRecordFields
  | UnexpectedRecordFields
  | UnexpectedFieldAccess
  | UnexpectedVariantLabel
  | TupleIndexOutOfBounds
  | UnexpectedTupleLength
  | AmbiguousSumType
  | AmbiguousList
  | IllegalEmptyMatching
  | NonexhaustiveMatchPatterns
  | UnexpectedPatternForType
  | DuplicateRecordFields
  | DuplicateRecordTypeFields
  | DuplicateVariantTypeFields

exception TyExn of tyError

let not_implemented () = raise (Failure "Not implemented")

let showError (err : tyError) : string =
  match err with
  | MissingMain ->
      "ERROR_MISSING_MAIN\n  в программе отсутствует функция main\n"
  | _ -> not_implemented ()

type context = (string * typeT) list

let put (ctx : context) (s : string) (ty : typeT) : context = (s, ty) :: ctx

let put_params (ctx : context) (params : paramDecl list) : context =
  List.concat
    [
      List.map (fun (AParamDecl (StellaIdent name, ty)) -> (name, ty)) params;
      ctx;
    ]

let rec get (ctx : context) (s : string) : typeT option =
  match ctx with
  | (s', ty) :: ctx' -> if s = s' then Some ty else get ctx' s
  | _ -> None

let checkMain (ctx : context) : unit =
  match get ctx "main" with None -> raise (TyExn MissingMain) | _ -> ()

let typecheck (ctx : context) (expr : AbsStella.expr) (ty : AbsStella.typeT) =
  Printf.printf "typechecker is not implemented\n"

let typecheckProgram (program : program) =
  match program with
  | AProgram (_, _, decls) ->
      let ctx =
        List.fold_left
          (fun a b ->
            match b with
            | DeclFun
                (_, StellaIdent name, params, SomeReturnType tyReturn, _, _, _)
              ->
                let tyParams =
                  List.map (fun (AParamDecl (name, tyParam)) -> tyParam) params
                in
                put a name (TypeFun (tyParams, tyReturn))
            | _ -> not_implemented ())
          [] decls
      in
      checkMain ctx;
      List.fold_left
        (fun _ decl ->
          match decl with
          (* TODO: Add decl support *)
          | DeclFun
              ([], _, params, SomeReturnType tyReturn, NoThrowType, [], expr) ->
              let ctx' = put_params ctx params in
              typecheck ctx' expr tyReturn
          | _ -> not_implemented ())
        () decls

(*
let infer (expr : AbsStella.expr) : AbsStella.typeT =
  Printf.printf "typechecker is not implemented\n"
*)
