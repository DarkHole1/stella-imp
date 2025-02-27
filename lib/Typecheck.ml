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

let checkMain (decls : decl list) =
  let isMain o =
    match o with
    | DeclFun (_, AbsStella.StellaIdent id, _, _, _, _, _) -> id = "main"
    | _ -> false
  in
  List.fold_left (fun b obj -> b || isMain obj) false decls

let typecheckProgram (program : program) =
  match program with
  | AProgram (_, _, decls) ->
      if checkMain decls then () else raise (Failure "No main")
(* Printf.printf "typechecker is not implemented\n" *)

let typecheck (expr : AbsStella.expr) (ty : AbsStella.typeT) =
  Printf.printf "typechecker is not implemented\n"

(*
let infer (expr : AbsStella.expr) : AbsStella.typeT =
  Printf.printf "typechecker is not implemented\n"
*)
