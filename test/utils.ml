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

module type Context = sig
  val structural_subtyping : bool
  val ambiguous_types_as_bottom : bool
  val exception_type : string option
end

module Make (Ctx : Context) = struct
  module TC = Typecheck.Make (struct
    let ambiguous =
      if Ctx.ambiguous_types_as_bottom then fun _ -> parse_string_typeT "Bot"
      else fun e -> raise e

    let exception_type = Option.map parse_string_typeT Ctx.exception_type
    let is_subtyping = Ctx.structural_subtyping

    let eq =
      if Ctx.structural_subtyping then Typecheck.subtype else Typecheck.eq

    let unexpected_type =
      if Ctx.structural_subtyping then fun ty1 ty2 expr ->
        raise (Typecheck.TyExn (UnexpectedSubtype (ty1, ty2, expr)))
      else fun ty1 ty2 expr ->
        raise (Typecheck.TyExn (UnexpectedTypeForExpression (ty1, ty2, expr)))
  end)

  let typecheck (ctx : Typecheck.context) (expr : string) (ty : string) =
    let ctx' = ctx in
    let expr' = parse_string_expr expr in
    let ty' = parse_string_typeT ty in
    TC.typecheck ctx' expr' ty'

  let typecheck' = typecheck []
  let check_typecheck (_ : string) = typecheck
  let check_typecheck' (_ : string) = typecheck'

  let infer (ctx : Typecheck.context) (expr : string) =
    let ctx' = ctx in
    let expr' = parse_string_expr expr in
    TC.infer ctx' expr'

  let infer' = infer []

  let check_infer (d : string) (ty : string) (ctx : Typecheck.context)
      (expr : string) =
    let ty' = parse_string_typeT ty in
    Alcotest.check typeT d ty' (infer ctx expr)

  let check_infer' (d : string) (ty : string) (expr : string) =
    let ty' = parse_string_typeT ty in
    Alcotest.check typeT d ty' (infer [] expr)

  type what = Check | Infer | Both
  type context = (string * string) list

  let o : context = []
  let in_context (ctx : context) (expr : string) = (ctx, expr)

  let check_with ((ctx, expr) : context * string) (ty : string) =
    (Check, ctx, expr, ty)

  let infer_with ((ctx, expr) : context * string) (ty : string) =
    (Infer, ctx, expr, ty)

  let both_with ((ctx, expr) : context * string) (ty : string) =
    (Both, ctx, expr, ty)

  let check (d : string) ((w, ctx, expr, ty) : what * context * string * string)
      =
    let ctx' = List.map (fun (n, ty) -> (n, parse_string_typeT ty)) ctx in
    match w with
    | Check -> check_typecheck d ctx' expr ty
    | Infer -> check_infer d ty ctx' expr
    | Both ->
        check_typecheck d ctx' expr ty;
        check_infer d ty ctx' expr

  let check_err (d : string) (chk : exn -> bool)
      ((w, ctx, expr, ty) : what * context * string * string) =
    let ctx' = List.map (fun (n, ty) -> (n, parse_string_typeT ty)) ctx in
    match w with
    | Check ->
        Alcotest.match_raises d chk (fun () -> check_typecheck d ctx' expr ty)
    | Infer ->
        Alcotest.match_raises d chk (fun () -> check_infer d ty ctx' expr)
    | Both ->
        Alcotest.match_raises d chk (fun () -> check_typecheck d ctx' expr ty);
        Alcotest.match_raises d chk (fun () -> check_infer d ty ctx' expr)

  let ( |- ) = in_context
  let ( <= ) = check_with
  let ( => ) = infer_with
  let ( <=> ) = both_with
end

include Make (struct
  let structural_subtyping = false
  let ambiguous_types_as_bottom = false
  let exception_type = None
end)

module E = struct
  let common (e : exn) = match e with Typecheck.TyExn _ -> true | _ -> false

  let missing_main (e : exn) =
    match e with Typecheck.TyExn MissingMain -> true | _ -> false

  let undefined_variable (e : exn) =
    match e with Typecheck.TyExn (UndefinedVariable _) -> true | _ -> false

  let unexpected_type_for_expression (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTypeForExpression _) -> true
    | _ -> false

  let not_a_function (e : exn) =
    match e with Typecheck.TyExn (NotAFunction _) -> true | _ -> false

  let not_a_tuple (e : exn) =
    match e with Typecheck.TyExn (NotATuple _) -> true | _ -> false

  let not_a_record (e : exn) =
    match e with Typecheck.TyExn (NotARecord _) -> true | _ -> false

  let not_a_list (e : exn) =
    match e with Typecheck.TyExn (NotAList _) -> true | _ -> false

  let unexpected_lambda (e : exn) =
    match e with Typecheck.TyExn (UnexpectedLambda _) -> true | _ -> false

  let unexpected_type_for_parameter (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTypeForParameter _) -> true
    | _ -> false

  let unexpected_tuple (e : exn) =
    match e with Typecheck.TyExn (UnexpectedTuple _) -> true | _ -> false

  let unexpected_record (e : exn) =
    match e with Typecheck.TyExn (UnexpectedRecord _) -> true | _ -> false

  let unexpected_variant (e : exn) =
    match e with Typecheck.TyExn (UnexpectedVariant _) -> true | _ -> false

  let unexpected_list (e : exn) =
    match e with Typecheck.TyExn (UnexpectedList _) -> true | _ -> false

  let unexpected_injection (e : exn) =
    match e with Typecheck.TyExn (UnexpectedInjection _) -> true | _ -> false

  let missing_record_fields (e : exn) =
    match e with Typecheck.TyExn (MissingRecordFields _) -> true | _ -> false

  let unexpected_record_fields (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedRecordFields _) -> true
    | _ -> false

  let unexpected_field_access (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedFieldAccess _) -> true
    | _ -> false

  let unexpected_variant_label (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedVariantLabel _) -> true
    | _ -> false

  let tuple_index_out_of_bounds (e : exn) =
    match e with
    | Typecheck.TyExn (TupleIndexOutOfBounds _) -> true
    | _ -> false

  let unexpected_tuple_length (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedTupleLength _) -> true
    | _ -> false

  let ambiguous_sum_type (e : exn) =
    match e with Typecheck.TyExn (AmbiguousSumType _) -> true | _ -> false

  let ambiguous_variant_type (e : exn) =
    match e with Typecheck.TyExn (AmbiguousVariantType _) -> true | _ -> false

  let ambiguous_list (e : exn) =
    match e with Typecheck.TyExn (AmbiguousList _) -> true | _ -> false

  let illegal_empty_matching (e : exn) =
    match e with Typecheck.TyExn (IllegalEmptyMatching _) -> true | _ -> false

  let nonexhaustive_match_patterns (e : exn) =
    match e with
    | Typecheck.TyExn (NonexhaustiveMatchPatterns _) -> true
    | _ -> false

  let unexpected_pattern_for_type (e : exn) =
    match e with
    | Typecheck.TyExn (UnexpectedPatternForType _) -> true
    | _ -> false

  let duplicate_record_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateRecordFields _) -> true
    | _ -> false

  let duplicate_record_type_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateRecordTypeFields _) -> true
    | _ -> false

  let duplicate_variant_type_fields (e : exn) =
    match e with
    | Typecheck.TyExn (DuplicateVariantTypeFields _) -> true
    | _ -> false
end
