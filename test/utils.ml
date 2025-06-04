open Stella

let pp (s : 'a -> ShowStella.showable) (fmt : Format.formatter) (v : 'a) : unit
    =
  Format.pp_print_string fmt (ShowStella.show (s v))

let pp_expr = pp ShowStella.showExpr
let pp_typeT = pp ShowStella.showTypeT
let[@warning "-unused-value-declaration"] expr = Alcotest.testable pp_expr ( = )

let strict_eq ty1 ty2 =
  let r = ref [] in
  Typecheck.make_eq r ty1 ty2 && List.length !r = 0

let typeT = Alcotest.testable pp_typeT strict_eq

let parse_string_expr (s : string) =
  Lexing.from_string s |> ParStella.pExpr LexStella.token

let parse_string_typeT (s : string) =
  Lexing.from_string s |> ParStella.pTypeT LexStella.token

module type Context = sig
  val structural_subtyping : bool
  val reconstruction : bool
  val ambiguous_types_as_bottom : bool
  val exception_type : string option
end

module Make (Ctx : Context) = struct
  let restrictions = ref []
  let counter = ref 0

  let fresh_var () =
    counter := !counter + 1;
    Printf.sprintf "?T%d" !counter

  module TC = Typecheck.Make (struct
    let ambiguous =
      if Ctx.ambiguous_types_as_bottom then fun _ -> parse_string_typeT "Bot"
      else fun f -> f ()

    let exception_type = Option.map parse_string_typeT Ctx.exception_type
    let is_subtyping = Ctx.structural_subtyping
    let is_reconstruction = Ctx.reconstruction

    let eq =
      if Ctx.structural_subtyping then Typecheck.subtype
      else Typecheck.make_eq restrictions

    let unexpected_type =
      if Ctx.structural_subtyping then Errors.unexpected_subtype
      else Errors.unexpected_type_for_expression

    let fresh_var = fresh_var
    let restrictions = restrictions
  end)

  let typecheck (ctx : Typecheck.context) (expr : string) (ty : string) =
    let ctx' = ctx in
    let expr' = parse_string_expr expr in
    let ty' = parse_string_typeT ty in
    TC.typecheck ctx' expr' ty'

  let typecheck' = typecheck Context.empty
  let check_typecheck (_ : string) = typecheck
  let check_typecheck' (_ : string) = typecheck'

  let infer (ctx : Typecheck.context) (expr : string) =
    let ctx' = ctx in
    let expr' = parse_string_expr expr in
    TC.infer ctx' expr'

  let infer' = infer Context.empty

  let check_infer (d : string) (ty : string) (ctx : Typecheck.context)
      (expr : string) =
    let ty' = parse_string_typeT ty in
    Alcotest.check typeT d ty' (infer ctx expr)

  let check_infer' (d : string) (ty : string) (expr : string) =
    let ty' = parse_string_typeT ty in
    Alcotest.check typeT d ty' (infer Context.empty expr)

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
    let ctx' =
      List.map (fun (n, ty) -> parse_string_typeT ty |> Context.from_var n) ctx
      |> Context.concat
    in
    match w with
    | Check -> check_typecheck d ctx' expr ty
    | Infer -> check_infer d ty ctx' expr
    | Both ->
        check_typecheck d ctx' expr ty;
        check_infer d ty ctx' expr

  let check_err (d : string) (chk : exn -> bool)
      ((w, ctx, expr, ty) : what * context * string * string) =
    let ctx' =
      List.map (fun (n, ty) -> parse_string_typeT ty |> Context.from_var n) ctx
      |> Context.concat
    in
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
  let reconstruction = false
  let exception_type = None
end)

module E = struct
  let common (e : exn) = match e with Errors.TyExn _ -> true | _ -> false

  let missing_main (e : exn) =
    match e with Errors.TyExn MissingMain -> true | _ -> false

  let undefined_variable (e : exn) =
    match e with Errors.TyExn (UndefinedVariable _) -> true | _ -> false

  let unexpected_type_for_expression (e : exn) =
    match e with
    | Errors.TyExn (UnexpectedTypeForExpression _) -> true
    | _ -> false

  let not_a_function (e : exn) =
    match e with Errors.TyExn (NotAFunction _) -> true | _ -> false

  let not_a_tuple (e : exn) =
    match e with Errors.TyExn (NotATuple _) -> true | _ -> false

  let not_a_record (e : exn) =
    match e with Errors.TyExn (NotARecord _) -> true | _ -> false

  let not_a_list (e : exn) =
    match e with Errors.TyExn (NotAList _) -> true | _ -> false

  let unexpected_lambda (e : exn) =
    match e with Errors.TyExn (UnexpectedLambda _) -> true | _ -> false

  let unexpected_type_for_parameter (e : exn) =
    match e with
    | Errors.TyExn (UnexpectedTypeForParameter _) -> true
    | _ -> false

  let unexpected_tuple (e : exn) =
    match e with Errors.TyExn (UnexpectedTuple _) -> true | _ -> false

  let unexpected_record (e : exn) =
    match e with Errors.TyExn (UnexpectedRecord _) -> true | _ -> false

  let unexpected_variant (e : exn) =
    match e with Errors.TyExn (UnexpectedVariant _) -> true | _ -> false

  let unexpected_list (e : exn) =
    match e with Errors.TyExn (UnexpectedList _) -> true | _ -> false

  let unexpected_injection (e : exn) =
    match e with Errors.TyExn (UnexpectedInjection _) -> true | _ -> false

  let missing_record_fields (e : exn) =
    match e with Errors.TyExn (MissingRecordFields _) -> true | _ -> false

  let unexpected_record_fields (e : exn) =
    match e with Errors.TyExn (UnexpectedRecordFields _) -> true | _ -> false

  let unexpected_field_access (e : exn) =
    match e with Errors.TyExn (UnexpectedFieldAccess _) -> true | _ -> false

  let unexpected_variant_label (e : exn) =
    match e with Errors.TyExn (UnexpectedVariantLabel _) -> true | _ -> false

  let tuple_index_out_of_bounds (e : exn) =
    match e with Errors.TyExn (TupleIndexOutOfBounds _) -> true | _ -> false

  let unexpected_tuple_length (e : exn) =
    match e with Errors.TyExn (UnexpectedTupleLength _) -> true | _ -> false

  let ambiguous_sum_type (e : exn) =
    match e with Errors.TyExn (AmbiguousSumType _) -> true | _ -> false

  let ambiguous_variant_type (e : exn) =
    match e with Errors.TyExn (AmbiguousVariantType _) -> true | _ -> false

  let ambiguous_list (e : exn) =
    match e with Errors.TyExn (AmbiguousList _) -> true | _ -> false

  let illegal_empty_matching (e : exn) =
    match e with Errors.TyExn (IllegalEmptyMatching _) -> true | _ -> false

  let nonexhaustive_match_patterns (e : exn) =
    match e with
    | Errors.TyExn (NonexhaustiveMatchPatterns _) -> true
    | _ -> false

  let unexpected_pattern_for_type (e : exn) =
    match e with
    | Errors.TyExn (UnexpectedPatternForType _) -> true
    | _ -> false

  let duplicate_record_fields (e : exn) =
    match e with Errors.TyExn (DuplicateRecordFields _) -> true | _ -> false

  let duplicate_record_type_fields (e : exn) =
    match e with
    | Errors.TyExn (DuplicateRecordTypeFields _) -> true
    | _ -> false

  let duplicate_variant_type_fields (e : exn) =
    match e with
    | Errors.TyExn (DuplicateVariantTypeFields _) -> true
    | _ -> false

  let exception_type_not_declared (e : exn) =
    match e with
    | Errors.TyExn (ExceptionTypeNotDeclared _) -> true
    | _ -> false

  let ambiguous_throw_type (e : exn) =
    match e with Errors.TyExn (AmbiguousThrowType _) -> true | _ -> false

  let ambiguous_reference_type (e : exn) =
    match e with Errors.TyExn (AmbiguousReferenceType _) -> true | _ -> false

  let ambiguous_panic_type (e : exn) =
    match e with Errors.TyExn (AmbiguousPanicType _) -> true | _ -> false

  let not_a_reference (e : exn) =
    match e with Errors.TyExn (NotAReference _) -> true | _ -> false

  let unexpected_memory_address (e : exn) =
    match e with Errors.TyExn (UnexpectedMemoryAddress _) -> true | _ -> false

  let unexpected_subtype (e : exn) =
    match e with Errors.TyExn (UnexpectedSubtype _) -> true | _ -> false
end
