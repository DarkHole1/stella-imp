type tyError =
  MissingMain
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

let typecheckProgram (program : AbsStella.program) =
  Printf.printf "typechecker is not implemented\n"

let typecheck (expr : AbsStella.expr) (ty : AbsStella.typeT) =
  Printf.printf "typechecker is not implemented\n"

(*
let infer (expr : AbsStella.expr) : AbsStella.typeT =
  Printf.printf "typechecker is not implemented\n"
*)
