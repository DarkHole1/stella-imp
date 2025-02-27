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
  | MissingMain -> "ERROR_MISSING_MAIN\n  в программе отсутствует функция MAIN\n"
  | _ -> not_implemented ()

type context = (string * typeT) list

let put (ctx : context) (s : string) (ty : typeT) : context = (s, ty) :: ctx

let rec get (ctx : context) (s : string) : typeT option =
  match ctx with
  | (s', ty) :: ctx' -> if s = s' then Some ty else get ctx' s
  | _ -> None

let checkMain (ctx : context) : unit =
  match get ctx "main" with None -> raise (TyExn MissingMain) | _ -> ()

let typecheckProgram (program : program) =
  match program with
  | AProgram (_, _, decls) ->
      (* let context in  *)
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
            | _ -> a)
          [] decls
      in
      checkMain ctx
(* Printf.printf "typechecker is not implemented\n" *)

let typecheck (expr : AbsStella.expr) (ty : AbsStella.typeT) =
  Printf.printf "typechecker is not implemented\n"

(*
let infer (expr : AbsStella.expr) : AbsStella.typeT =
  Printf.printf "typechecker is not implemented\n"
*)
