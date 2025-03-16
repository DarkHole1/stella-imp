open Stella

let pp (s : 'a -> ShowStella.showable) (fmt : Format.formatter) (v : 'a) : unit
    =
  Format.pp_print_string fmt (ShowStella.show (s v))

let pp_expr = pp ShowStella.showExpr
let pp_typeT = pp ShowStella.showTypeT
let[@warning "-unused-value-declaration"] expr = Alcotest.testable pp_expr ( = )
let typeT = Alcotest.testable pp_typeT Typecheck.eq

let parse_string_expr (s : string) =
  Lexing.from_string s |> ParStella.pExpr LexStella.token

let parse_string_typeT (s : string) =
  Lexing.from_string s |> ParStella.pTypeT LexStella.token

let typecheck (ctx : Typecheck.context) (expr : string) (ty : string) =
  let ctx' = ctx in
  let expr' = parse_string_expr expr in
  let ty' = parse_string_typeT ty in
  Typecheck.typecheck ctx' expr' ty'

let typecheck' = typecheck []
let check_typecheck (_ : string) = typecheck
let check_typecheck' (_ : string) = typecheck'

let infer (ctx : Typecheck.context) (expr : string) =
  let ctx' = ctx in
  let expr' = parse_string_expr expr in
  Typecheck.infer ctx' expr'

let infer' = infer []

let check_infer (d : string) (ty : string) (ctx : Typecheck.context)
    (expr : string) =
  let ty' = parse_string_typeT ty in
  Alcotest.check typeT d ty' (infer ctx expr)

let check_infer' (d : string) (ty : string) (expr : string) =
  let ty' = parse_string_typeT ty in
  Alcotest.check typeT d ty' (infer [] expr)

type what = Check | Infer | Both

let o : Typecheck.context = []
let in_context (ctx : Typecheck.context) (expr : string) = (ctx, expr)

let check_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
  (Check, ctx, expr, ty)

let infer_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
  (Infer, ctx, expr, ty)

let both_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
  (Both, ctx, expr, ty)

let check (d : string)
    ((w, ctx, expr, ty) : what * Typecheck.context * string * string) =
  match w with
  | Check -> check_typecheck d ctx expr ty
  | Infer -> check_infer d ty ctx expr
  | Both ->
      check_typecheck d ctx expr ty;
      check_infer d ty ctx expr

let check_err (d : string) (chk : exn -> bool)
    ((w, ctx, expr, ty) : what * Typecheck.context * string * string) =
  match w with
  | Check ->
      Alcotest.match_raises d chk (fun () -> check_typecheck d ctx expr ty)
  | Infer -> Alcotest.match_raises d chk (fun () -> check_infer d ty ctx expr)
  | Both ->
      Alcotest.match_raises d chk (fun () -> check_typecheck d ctx expr ty);
      Alcotest.match_raises d chk (fun () -> check_infer d ty ctx expr)

let ( |- ) = in_context
let ( <= ) = check_with
let ( => ) = infer_with
let ( <=> ) = both_with

module E = struct
  let common (e : exn) = match e with Typecheck.TyExn _ -> false | _ -> true

  let missing_main (e : exn) =
    match e with Typecheck.TyExn MissingMain -> false | _ -> true

  let undefined_variable (e : exn) =
    match e with Typecheck.TyExn (UndefinedVariable _) -> false | _ -> true

  let unexpected_type_for_expression (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTypeForExpression _) -> false
    | _ -> true

  let not_a_function (e : exn) =
    match e with Typecheck.TyExn (NotAFunction _) -> false | _ -> true

  let not_a_tuple (e : exn) =
    match e with Typecheck.TyExn (NotATuple _) -> false | _ -> true

  let not_a_record (e : exn) =
    match e with Typecheck.TyExn (NotARecord _) -> false | _ -> true

  let not_a_list (e : exn) =
    match e with Typecheck.TyExn (NotAList _) -> false | _ -> true

  let unexpected_lambda (e : exn) =
    match e with Typecheck.TyExn (UnexpectedLambda _) -> false | _ -> true

  let unexpected_type_for_parameter (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTypeForParameter _) -> false
    | _ -> true

  let unexpected_tuple (e : exn) =
    match e with Typecheck.TyExn (UnexpectedTuple _) -> false | _ -> true

  let unexpected_record (e : exn) =
    match e with Typecheck.TyExn (UnexpectedRecord _) -> false | _ -> true

  let unexpected_variant (e : exn) =
    match e with Typecheck.TyExn (UnexpectedVariant _) -> false | _ -> true

  let unexpected_list (e : exn) =
    match e with Typecheck.TyExn (UnexpectedList _) -> false | _ -> true

  let unexpected_injection (e : exn) =
    match e with Typecheck.TyExn (UnexpectedInjection _) -> false | _ -> true

  let missing_record_fields (e : exn) =
    match e with Typecheck.TyExn (MissingRecordFields _) -> false | _ -> true

  let unexpected_record_fields (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedRecordFields _) -> false
    | _ -> true

  let unexpected_field_access (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedFieldAccess _) -> false
    | _ -> true

  let unexpected_variant_label (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedVariantLabel _) -> false
    | _ -> true

  let tuple_index_out_of_bounds (e : exn) =
    match e with
    | Typecheck.TyExn (TupleIndexOutOfBounds _) -> false
    | _ -> true

  let unexpected_tuple_length (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTupleLength _) -> false
    | _ -> true

  let ambiguous_sum_type (e : exn) =
    match e with Typecheck.TyExn (AmbiguousSumType _) -> false | _ -> true

  let ambiguous_variant_type (e : exn) =
    match e with Typecheck.TyExn (AmbiguousVariantType _) -> false | _ -> true

  let ambiguous_list (e : exn) =
    match e with Typecheck.TyExn (AmbiguousList _) -> false | _ -> true

  let illegal_empty_matching (e : exn) =
    match e with Typecheck.TyExn (IllegalEmptyMatching _) -> false | _ -> true

  let nonexhaustive_match_patterns (e : exn) =
    match e with
    | Typecheck.TyExn (NonexhaustiveMatchPatterns _) -> false
    | _ -> true

  let unexpected_pattern_for_type (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedPatternForType _) -> false
    | _ -> true

  let duplicate_record_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateRecordFields _) -> false
    | _ -> true

  let duplicate_record_type_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateRecordTypeFields _) -> false
    | _ -> true

  let duplicate_variant_type_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateVariantTypeFields _) -> false
    | _ -> true
end
