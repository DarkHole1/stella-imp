open AbsStella
open Utils

type t =
  | MissingMain
  | UndefinedVariable of string * expr
  | UnexpectedTypeForExpression of typeT * typeT * expr
  | NotAFunction of typeT * expr
  | NotATuple of typeT * expr
  | NotARecord of typeT * expr
  | NotAList of typeT * expr
  | UnexpectedLambda of typeT * expr
  | UnexpectedTypeForParameter of typeT * typeT * paramDecl
  | UnexpectedTuple of typeT * expr
  | UnexpectedRecord of typeT * expr
  | UnexpectedVariant of typeT * expr
  | UnexpectedList of typeT * expr
  | UnexpectedInjection of typeT * expr
  | MissingRecordFields of string list * typeT * expr
  | UnexpectedRecordFields of string list * typeT * expr
  | UnexpectedFieldAccess of typeT * string * expr
  | UnexpectedVariantLabel of typeT * string * expr
  | TupleIndexOutOfBounds of typeT * int * expr
  | UnexpectedTupleLength of int * int * expr
  | AmbiguousSumType of expr
  | AmbiguousVariantType of expr
  | AmbiguousList of expr
  | IllegalEmptyMatching of expr
  | NonexhaustiveMatchPatterns of expr * expr
  | UnexpectedPatternForType of pattern * typeT
  | DuplicateRecordFields of string list * expr
  | DuplicateRecordTypeFields of string list * typeT
  | DuplicateVariantTypeFields of string list * typeT
  | ExceptionTypeNotDeclared of expr
  | AmbiguousThrowType of expr
  | AmbiguousReferenceType of expr
  | AmbiguousPanicType of expr
  | NotAReference of typeT * expr
  | UnexpectedMemoryAddress of typeT * expr
  | UnexpectedSubtype of typeT * typeT * expr
  | OccursCheckInfiniteType of typeT
  | NotAGenericFunction of typeT
  | IncorrectNumberOfTypeArguments of typeT * typeT list
  | UndefinedTypeVariable of typeT

exception TyExn of t

let show (err : t) : string =
  let prtExpr = PrintStella.printTree (default_pad PrintStella.prtExpr) in
  let prtTypeT = PrintStella.printTree (default_pad PrintStella.prtTypeT) in
  let prtPattern = PrintStella.printTree (default_pad PrintStella.prtPattern) in
  match err with
  | MissingMain -> "ERROR_MISSING_MAIN\n  в программе отсутствует функция main"
  | UndefinedVariable (name, expr) ->
      "ERROR_UNDEFINED_VARIABLE\n  неизвестная переменная\n    " ^ name
      ^ "\n  в выражении\n    " ^ prtExpr expr
  | UnexpectedTypeForExpression (ty1, ty2, expr) ->
      "ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION\n  ожидался тип\n    "
      ^ prtTypeT ty1 ^ "\n  но получен тип\n    " ^ prtTypeT ty2
      ^ "\n  в выражении\n    " ^ prtExpr expr
  | NotAFunction (ty, expr) ->
      "ERROR_NOT_A_FUNCTION\n  ожидалась функция в выражении\n    "
      ^ prtExpr expr ^ "\n  но получен тип\n    " ^ prtTypeT ty
  | NotATuple (ty, expr) ->
      "ERROR_NOT_A_TUPLE\n  ожидался кортёж в выражении\n    " ^ prtExpr expr
      ^ "\n  но получен тип\n    " ^ prtTypeT ty
  | NotARecord (ty, expr) ->
      "ERROR_NOT_A_RECORD\n  ожидалась запись в выражении\n    " ^ prtExpr expr
      ^ "\n  но получен тип\n    " ^ prtTypeT ty
  | NotAList (ty, expr) ->
      "ERROR_NOT_A_LIST\n  ожидался список в выражении\n    " ^ prtExpr expr
      ^ "\n  но получен тип\n    " ^ prtTypeT ty
  | UnexpectedLambda (ty, expr) ->
      "ERROR_UNEXPECTED_LAMBDA\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получена лямбда в выражении\n    " ^ prtExpr expr
  | UnexpectedTypeForParameter (ty1, ty2, AParamDecl (StellaIdent name, _)) ->
      "ERROR_UNEXPECTED_TYPE_FOR_PARAMETER\n  для параметра\n    " ^ name
      ^ "\n  ожидался тип\n    " ^ prtTypeT ty1 ^ "\n  но получен тип\n    "
      ^ prtTypeT ty2
  | UnexpectedTuple (ty, expr) ->
      "ERROR_UNEXPECTED_TUPLE\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получен кортёж в выражении\n    " ^ prtExpr expr
  | UnexpectedRecord (ty, expr) ->
      "ERROR_UNEXPECTED_RECORD\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получена запись в выражении\n    " ^ prtExpr expr
  | UnexpectedVariant (ty, expr) ->
      "ERROR_UNEXPECTED_VARIANT\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получен вариант в выражении\n    " ^ prtExpr expr
  | UnexpectedList (ty, expr) ->
      "ERROR_UNEXPECTED_LIST\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получен список в выражении\n    " ^ prtExpr expr
  | UnexpectedInjection (ty, expr) ->
      "ERROR_UNEXPECTED_INJECTION\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получена инъекция в выражении\n    " ^ prtExpr expr
  | MissingRecordFields (missing, ty, expr) ->
      "ERROR_MISSING_RECORD_FIELDS\n  отсуствуют поля\n    "
      ^ String.concat "\n    " missing
      ^ "\n  для типа\n    " ^ prtTypeT ty ^ "\n  в выражении\n    "
      ^ prtExpr expr
  | UnexpectedRecordFields (extra, ty, expr) ->
      "ERROR_UNEXPECTED_RECORD_FIELDS\n  присутствуют лишние поля\n    "
      ^ String.concat "\n    " extra
      ^ "\n  для типа\n    " ^ prtTypeT ty ^ "\n  в выражении\n    "
      ^ prtExpr expr
  | UnexpectedFieldAccess (ty, field, expr) ->
      "ERROR_UNEXPECTED_FIELD_ACCESS\n  в типе\n    " ^ prtTypeT ty
      ^ "\n  отсутствует поле\n    " ^ field ^ "\n  в выражении\n    "
      ^ prtExpr expr
  | UnexpectedVariantLabel (ty, variant, expr) ->
      "ERROR_UNEXPECTED_VARIANT_LABEL\n  в типе\n    " ^ prtTypeT ty
      ^ "\n  отсутствует вариант\n    " ^ variant ^ "\n  в выражении\n    "
      ^ prtExpr expr
  | TupleIndexOutOfBounds (ty, index, expr) ->
      "ERROR_TUPLE_INDEX_OUT_OF_BOUNDS\n  индекс\n    " ^ Int.to_string index
      ^ "\n  выходит за пределы тип\n    " ^ prtTypeT ty
      ^ "\n  в выражении\n    " ^ prtExpr expr
  | UnexpectedTupleLength (len1, len2, expr) ->
      "ERROR_UNEXPECTED_TUPLE_LENGTH\n  ожидался кортёж длиной\n    "
      ^ Int.to_string len1 ^ "\n  но получен кортёж длиной\n    "
      ^ Int.to_string len2 ^ "\n  в выражении\n    " ^ prtExpr expr
  | AmbiguousSumType expr ->
      "ERROR_AMBIGUOUS_SUM_TYPE\n\
      \  невозможно определить тип инъекции в выражении\n\
      \    " ^ prtExpr expr
  | AmbiguousVariantType expr ->
      "ERROR_AMBIGUOUS_VARIANT_TYPE\n\
      \  невозможно определить тип варианта в выражении\n\
      \    " ^ prtExpr expr
  | AmbiguousList expr ->
      "ERROR_AMBIGUOUS_LIST\n\
      \  невозможно определить тип списка в выражении\n\
      \    " ^ prtExpr expr
  | IllegalEmptyMatching expr ->
      "ERROR_ILLEGAL_EMPTY_MATCHING\n\
      \  match-выражение с пустым списком альтернатив\n\
      \    " ^ prtExpr expr
  | NonexhaustiveMatchPatterns (expr_unmatched, expr_full) ->
      "ERROR_NONEXHAUSTIVE_MATCH_PATTERNS\n  выражение\n    "
      ^ prtExpr expr_full ^ "\n  не покрывает значение\n    "
      ^ prtExpr expr_unmatched
  | UnexpectedPatternForType (pat, ty) ->
      "ERROR_UNEXPECTED_PATTERN_FOR_TYPE\n  образец\n    " ^ prtPattern pat
      ^ "\n  не соответствует типу\n    " ^ prtTypeT ty
  | DuplicateRecordFields (dup, expr) ->
      "ERROR_DUPLICATE_RECORD_FIELDS\n  в выражении\n    " ^ prtExpr expr
      ^ "\n  дублируются поля\n    " ^ String.concat "\n    " dup
  | DuplicateRecordTypeFields (dup, ty) ->
      "ERROR_DUPLICATE_RECORD_TYPE_FIELDS\n  в типе\n    " ^ prtTypeT ty
      ^ "\n  дублируются поля\n    " ^ String.concat "\n    " dup
  | DuplicateVariantTypeFields (dup, ty) ->
      "ERROR_DUPLICATE_VARIANT_TYPE_FIELDS\n  в типе\n    " ^ prtTypeT ty
      ^ "\n  дублируются варианты\n    " ^ String.concat "\n    " dup
  | ExceptionTypeNotDeclared expr ->
      "ERROR_EXCEPTION_TYPE_NOT_DECLARED\n  в выражении\n    " ^ prtExpr expr
      ^ "\n  используются ошибки, но их тип не определён в программе"
  | AmbiguousThrowType expr ->
      "ERROR_AMBIGUOUS_THROW_TYPE\n  в выражении\n    " ^ prtExpr expr
      ^ "\n  невозможно определить тип throw"
  | AmbiguousReferenceType expr ->
      "ERROR_AMBIGUOUS_REFERENCE_TYPE\n  в выражении\n    " ^ prtExpr expr
      ^ "\n  невозможно определить тип адреса памяти"
  | AmbiguousPanicType expr ->
      "ERROR_AMBIGUOUS_PANIC_TYPE\n  в выражении\n    " ^ prtExpr expr
      ^ "\n  невозможно определить тип ошибки"
  | NotAReference (ty, expr) ->
      "ERROR_NOT_A_REFERENCE\n  ожидалась ссылка в выражении\n    "
      ^ prtExpr expr ^ "\n  но получен тип\n    " ^ prtTypeT ty
  | UnexpectedMemoryAddress (ty, expr) ->
      "ERROR_UNEXPECTED_MEMORY_ADDRESS\n  ожидался тип\n    " ^ prtTypeT ty
      ^ "\n  но получен адрес памяти в выражении\n    " ^ prtExpr expr
  | UnexpectedSubtype (ty1, ty2, expr) ->
      "ERROR_UNEXPECTED_SUBTYPE\n  ожидался подтип типа\n    " ^ prtTypeT ty1
      ^ "\n  но получен тип\n    " ^ prtTypeT ty2 ^ "\n  в выражении\n    "
      ^ prtExpr expr
  | OccursCheckInfiniteType ty ->
      "ERROR_OCCURS_CHECK_INFINITE_TYPE\n\
      \  в результате унификации возник бесконечный тип\n\
      \   " ^ prtTypeT ty
  | NotAGenericFunction ty ->
      "ERROR_NOT_A_GENERIC_FUNCTION\n  тип\n    " ^ prtTypeT ty
      ^ "\n не является обобщённым"
  | IncorrectNumberOfTypeArguments (ty, tys) ->
      "ERROR_INCORRECT_NUMBER_OF_TYPE_ARGUMENTS\n  типа\n    " ^ prtTypeT ty
      ^ "\n  применено недостаточное количество аргументов"
  | UndefinedTypeVariable ty ->
      "ERROR_UNDEFINED_TYPE_VARIABLE\n  переменная\n    " ^ prtTypeT ty
      ^ "\n  не определена"

let missing_main () = raise (TyExn MissingMain)
let undefined_variable a b = raise (TyExn (UndefinedVariable (a, b)))

let unexpected_type_for_expression a b c =
  raise (TyExn (UnexpectedTypeForExpression (a, b, c)))

let not_a_function a b = raise (TyExn (NotAFunction (a, b)))
let not_a_tuple a b = raise (TyExn (NotATuple (a, b)))
let not_a_record a b = raise (TyExn (NotARecord (a, b)))
let not_a_list a b = raise (TyExn (NotAList (a, b)))
let unexpected_lambda a b = raise (TyExn (UnexpectedLambda (a, b)))

let unexpected_type_for_parameter a b c =
  raise (TyExn (UnexpectedTypeForParameter (a, b, c)))

let unexpected_tuple a b = raise (TyExn (UnexpectedTuple (a, b)))
let unexpected_record a b = raise (TyExn (UnexpectedRecord (a, b)))
let unexpected_variant a b = raise (TyExn (UnexpectedVariant (a, b)))
let unexpected_list a b = raise (TyExn (UnexpectedList (a, b)))
let unexpected_injection a b = raise (TyExn (UnexpectedInjection (a, b)))
let missing_record_fields a b c = raise (TyExn (MissingRecordFields (a, b, c)))

let unexpected_record_fields a b c =
  raise (TyExn (UnexpectedRecordFields (a, b, c)))

let unexpected_field_access a b c =
  raise (TyExn (UnexpectedFieldAccess (a, b, c)))

let unexpected_variant_label a b c =
  raise (TyExn (UnexpectedVariantLabel (a, b, c)))

let tuple_index_out_of_bounds a b c =
  raise (TyExn (TupleIndexOutOfBounds (a, b, c)))

let unexpected_tuple_length a b c =
  raise (TyExn (UnexpectedTupleLength (a, b, c)))

let ambiguous_sum_type a = raise (TyExn (AmbiguousSumType a))
let ambiguous_variant_type a = raise (TyExn (AmbiguousVariantType a))
let ambiguous_list a = raise (TyExn (AmbiguousList a))
let illegal_empty_matching a = raise (TyExn (IllegalEmptyMatching a))

let nonexhaustive_match_patterns a b =
  raise (TyExn (NonexhaustiveMatchPatterns (a, b)))

let unexpected_pattern_for_type a b =
  raise (TyExn (UnexpectedPatternForType (a, b)))

let duplicate_record_fields a b = raise (TyExn (DuplicateRecordFields (a, b)))

let duplicate_record_type_fields a b =
  raise (TyExn (DuplicateRecordTypeFields (a, b)))

let duplicate_variant_type_fields a b =
  raise (TyExn (DuplicateVariantTypeFields (a, b)))

let exception_type_not_declared a = raise (TyExn (ExceptionTypeNotDeclared a))
let ambiguous_throw_type a = raise (TyExn (AmbiguousThrowType a))
let ambiguous_reference_type a = raise (TyExn (AmbiguousReferenceType a))
let ambiguous_panic_type a = raise (TyExn (AmbiguousPanicType a))
let not_a_reference a b = raise (TyExn (NotAReference (a, b)))

let unexpected_memory_address a b =
  raise (TyExn (UnexpectedMemoryAddress (a, b)))

let unexpected_subtype a b c = raise (TyExn (UnexpectedSubtype (a, b, c)))
let occurs_check_infinite_type a = raise (TyExn (OccursCheckInfiniteType a))
let not_a_generic_function a = raise (TyExn (NotAGenericFunction a))

let incorrect_number_of_type_arguments a b =
  raise (TyExn (IncorrectNumberOfTypeArguments (a, b)))

let undefined_type_variable a = raise (TyExn (UndefinedTypeVariable a))


let missing_main' () () = raise (TyExn MissingMain)
let undefined_variable' a b () = raise (TyExn (UndefinedVariable (a, b)))

let unexpected_type_for_expression' a b c () =
  raise (TyExn (UnexpectedTypeForExpression (a, b, c)))

let not_a_function' a b () = raise (TyExn (NotAFunction (a, b)))
let not_a_tuple' a b () = raise (TyExn (NotATuple (a, b)))
let not_a_record' a b () = raise (TyExn (NotARecord (a, b)))
let not_a_list' a b () = raise (TyExn (NotAList (a, b)))
let unexpected_lambda' a b () = raise (TyExn (UnexpectedLambda (a, b)))

let unexpected_type_for_parameter' a b c () =
  raise (TyExn (UnexpectedTypeForParameter (a, b, c)))

let unexpected_tuple' a b () = raise (TyExn (UnexpectedTuple (a, b)))
let unexpected_record' a b () = raise (TyExn (UnexpectedRecord (a, b)))
let unexpected_variant' a b () = raise (TyExn (UnexpectedVariant (a, b)))
let unexpected_list' a b () = raise (TyExn (UnexpectedList (a, b)))
let unexpected_injection' a b () = raise (TyExn (UnexpectedInjection (a, b)))
let missing_record_fields' a b c () = raise (TyExn (MissingRecordFields (a, b, c)))

let unexpected_record_fields' a b c () =
  raise (TyExn (UnexpectedRecordFields (a, b, c)))

let unexpected_field_access' a b c () =
  raise (TyExn (UnexpectedFieldAccess (a, b, c)))

let unexpected_variant_label' a b c () =
  raise (TyExn (UnexpectedVariantLabel (a, b, c)))

let tuple_index_out_of_bounds' a b c () =
  raise (TyExn (TupleIndexOutOfBounds (a, b, c)))

let unexpected_tuple_length' a b c () =
  raise (TyExn (UnexpectedTupleLength (a, b, c)))

let ambiguous_sum_type' a () = raise (TyExn (AmbiguousSumType a))
let ambiguous_variant_type' a () = raise (TyExn (AmbiguousVariantType a))
let ambiguous_list' a () = raise (TyExn (AmbiguousList a))
let illegal_empty_matching' a () = raise (TyExn (IllegalEmptyMatching a))

let nonexhaustive_match_patterns' a b () =
  raise (TyExn (NonexhaustiveMatchPatterns (a, b)))

let unexpected_pattern_for_type' a b () =
  raise (TyExn (UnexpectedPatternForType (a, b)))

let duplicate_record_fields' a b () = raise (TyExn (DuplicateRecordFields (a, b)))

let duplicate_record_type_fields' a b () =
  raise (TyExn (DuplicateRecordTypeFields (a, b)))

let duplicate_variant_type_fields' a b () =
  raise (TyExn (DuplicateVariantTypeFields (a, b)))

let exception_type_not_declared' a () = raise (TyExn (ExceptionTypeNotDeclared a))
let ambiguous_throw_type' a () = raise (TyExn (AmbiguousThrowType a))
let ambiguous_reference_type' a () = raise (TyExn (AmbiguousReferenceType a))
let ambiguous_panic_type' a () = raise (TyExn (AmbiguousPanicType a))
let not_a_reference' a b () = raise (TyExn (NotAReference (a, b)))

let unexpected_memory_address' a b () =
  raise (TyExn (UnexpectedMemoryAddress (a, b)))

let unexpected_subtype' a b c () = raise (TyExn (UnexpectedSubtype (a, b, c)))
let occurs_check_infinite_type' a () = raise (TyExn (OccursCheckInfiniteType a))
let not_a_generic_function' a () = raise (TyExn (NotAGenericFunction a))

let incorrect_number_of_type_arguments' a b () =
  raise (TyExn (IncorrectNumberOfTypeArguments (a, b)))

let undefined_type_variable' a () = raise (TyExn (UndefinedTypeVariable a))
