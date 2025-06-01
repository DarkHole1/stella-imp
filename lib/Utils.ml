open AbsStella

let get_ident (StellaIdent i) = i
let to_ident i = StellaIdent i
let get_extension_name (ExtensionName n) = n
let to_extension_name n = ExtensionName n
let get_memory_address (MemoryAddress m) = m
let to_memory_addres m = MemoryAddress m

let get_program (AProgram (language, extensions, decls)) =
  (language, extensions, decls)

let to_program language extensions decls = AProgram (language, extensions, decls)
let get_program' (AProgram (_, extensions, decls)) = (extensions, decls)
let to_program' extension decls = AProgram (LanguageCore, extension, decls)
let get_language LanguageCore = ()
let to_language () = LanguageCore
let get_extension (AnExtension extension_names) = extension_names
let to_extension extension_names = AnExtension extension_names

let get_extension' (AnExtension extension_names) =
  List.map get_extension_name extension_names

let to_extension' extension_names = List.map to_extension_name extension_names
let get_local_decl (ALocalDecl decl) = decl
let to_local_decl decl = ALocalDecl decl
let get_annotation InlineAnnotation = ()
let to_annotation () = InlineAnnotation
let get_param_decl (AParamDecl (ident, ty)) = (ident, ty)
let to_param_decl ident ty = AParamDecl (ident, ty)
let get_param_decl' (AParamDecl (StellaIdent ident, ty)) = (ident, ty)
let to_param_decl' ident ty = AParamDecl (StellaIdent ident, ty)

let return_type_to_option = function
  | NoReturnType -> None
  | SomeReturnType ty -> Some ty

let option_to_return_type = function
  | None -> NoReturnType
  | Some ty -> SomeReturnType ty

let map_return_type f r =
  return_type_to_option r |> Option.map f |> option_to_return_type

let throw_type_to_option = function
  | NoThrowType -> None
  | SomeThrowType ty -> Some ty

let option_to_throw_type = function
  | None -> NoThrowType
  | Some ty -> SomeThrowType ty

let map_throw_type f t =
  throw_type_to_option t |> Option.map f |> option_to_throw_type

let get_match_case (AMatchCase (pattern, expr)) = (pattern, expr)
let to_match_case pattern expr = AMatchCase (pattern, expr)

let optional_typing_to_option = function
  | NoTyping -> None
  | SomeTyping ty -> Some ty

let option_to_optional_typing = function
  | None -> NoTyping
  | Some ty -> SomeTyping ty

let map_optional_typing f t =
  optional_typing_to_option t |> Option.map f |> option_to_optional_typing

let pattern_data_to_option = function
  | NoPatternData -> None
  | SomePatternData data -> Some data

let option_to_pattern_data = function
  | None -> NoPatternData
  | Some data -> SomePatternData data

let map_pattern_data f d =
  pattern_data_to_option d |> Option.map f |> option_to_pattern_data

let expr_data_to_option = function
  | NoExprData -> None
  | SomeExprData data -> Some data

let option_to_expr_data = function
  | None -> NoExprData
  | Some data -> SomeExprData data

let map_expr_data f d =
  expr_data_to_option d |> Option.map f |> option_to_expr_data

let get_labelled_pattern (ALabelledPattern (ident, pattern)) = (ident, pattern)
let to_labelled_pattern ident pattern = ALabelledPattern (ident, pattern)

let get_labelled_pattern' (ALabelledPattern (StellaIdent ident, pattern)) =
  (ident, pattern)

let to_labelled_pattern' ident pattern =
  ALabelledPattern (StellaIdent ident, pattern)

let get_binding (ABinding (ident, expr)) = (ident, expr)
let to_binding ident expr = ABinding (ident, expr)
let get_binding' (ABinding (StellaIdent ident, expr)) = (ident, expr)
let to_binding' ident expr = ABinding (StellaIdent ident, expr)
let get_variant_field_type (AVariantFieldType (ident, ty)) = (ident, ty)
let to_variant_field_type ident ty = AVariantFieldType (ident, ty)

let get_variant_field_type' (AVariantFieldType (StellaIdent ident, ty)) =
  (ident, ty)

let to_variant_field_type' ident ty = AVariantFieldType (StellaIdent ident, ty)
let get_record_field_type (ARecordFieldType (ident, ty)) = (ident, ty)
let to_record_field_type ident ty = ARecordFieldType (ident, ty)

let get_record_field_type' (ARecordFieldType (StellaIdent ident, ty)) =
  (ident, ty)

let to_record_field_type' ident ty = ARecordFieldType (StellaIdent ident, ty)
let get_typing (ATyping (expr, ty)) = (expr, ty)
let to_typing expr ty = ATyping (expr, ty)

module Extensions = struct
  type t = string list

  let make (extensions : string list) : t = extensions

  (* Stage 1 *)
  let unit_type : t -> bool = List.mem "#unit-type"
  let pairs : t -> bool = List.mem "#pairs"
  let tuples : t -> bool = List.mem "#tuples"
  let records : t -> bool = List.mem "#records"
  let let_bindings : t -> bool = List.mem "#let-bindings"
  let type_ascriptions : t -> bool = List.mem "#type-ascriptions"
  let sum_types : t -> bool = List.mem "#sum-types"
  let lists : t -> bool = List.mem "#lists"
  let variants : t -> bool = List.mem "#variants"
  let fixpoint_combinator : t -> bool = List.mem "#fixpoint-combinator"

  (* Stage 1 ext *)
  let natural_literals : t -> bool = List.mem "#natural-literals"

  let nested_function_declarations : t -> bool =
    List.mem "#nested-function-declarations"

  let nullary_functions : t -> bool = List.mem "#nullary-functions"

  let multiparameter_functions : t -> bool =
    List.mem "#multiparameter-functions"

  let structural_patterns : t -> bool = List.mem "#structural-patterns"
  let nullary_variant_labels : t -> bool = List.mem "#nullary-variant-labels"
  let letrec_bindings : t -> bool = List.mem "#letrec-bindings"
  let pattern_ascriptions : t -> bool = List.mem "#pattern-ascriptions"

  (* Stage 2 *)
  let sequencing : t -> bool = List.mem "#sequencing"
  let references : t -> bool = List.mem "#references"
  let panic : t -> bool = List.mem "#panic"
  let exceptions : t -> bool = List.mem "#exceptions"

  let exception_type_annotation : t -> bool =
    List.mem "#exception-type-annotation"

  let structural_subtyping : t -> bool = List.mem "#structural-subtyping"

  let ambiguous_type_as_bottom : t -> bool =
    List.mem "#ambiguous-type-as-bottom"

  (* Stage 2 ext *)
  let open_variant_exceptions : t -> bool = List.mem "#open-variant-exceptions"
  let try_cast_as : t -> bool = List.mem "#try-cast-as"
  let type_cast_patterns : t -> bool = List.mem "#type-cast-patterns"

  (* Stage 3 *)
  let type_reconstruction : t -> bool = List.mem "#type-reconstruction"
  let universal_types : t -> bool = List.mem "#universal-types"
end

let get_extensions (AProgram (_, extensions, _)) =
  List.concat_map get_extension' extensions

let get_extensions' program = get_extensions program |> Extensions.make

let get_record_fields (fields : recordFieldType list) =
  List.map get_record_field_type' fields

let get_binders (binders : binding list) = List.map get_binding' binders

let rec traverse_type (f : (typeT -> typeT) -> typeT -> typeT) =
  let f = f (traverse_type f) in
  function
  | TypeAuto -> TypeAuto
  | TypeFun (tys, ty) -> TypeFun (List.map f tys, f ty)
  | TypeForAll (idents, ty) -> TypeForAll (idents, f ty)
  | TypeRec (ident, ty) -> TypeRec (ident, f ty)
  | TypeSum (ty1, ty2) -> TypeSum (f ty1, f ty2)
  | TypeTuple tys -> TypeTuple (List.map f tys)
  | TypeRecord fields ->
      TypeRecord
        (List.map
           (fun (ARecordFieldType (ident, ty)) ->
             ARecordFieldType (ident, f ty))
           fields)
  | TypeVariant fields ->
      TypeVariant
        (List.map
           (fun (AVariantFieldType (ident, ty)) ->
             AVariantFieldType (ident, map_optional_typing f ty))
           fields)
  | TypeList ty -> TypeList (f ty)
  | TypeBool -> TypeBool
  | TypeNat -> TypeNat
  | TypeUnit -> TypeUnit
  | TypeTop -> TypeTop
  | TypeBottom -> TypeBottom
  | TypeRef ty -> TypeRef (f ty)
  | TypeVar ident -> TypeVar ident

let rec traverse_expr (f : (expr -> expr) -> expr -> expr) =
  let f = f (traverse_expr f) in
  function
  | Sequence (e1, e2) -> Sequence (f e1, f e2)
  | Assign (e1, e2) -> Assign (f e1, f e2)
  | If (e1, e2, e3) -> If (f e1, f e2, f e3)
  | Let (patterns, expr) -> Let (patterns, f expr)
  | LetRec (patterns, expr) -> LetRec (patterns, f expr)
  | TypeAbstraction (idents, expr) -> TypeAbstraction (idents, f expr)
  | LessThan (e1, e2) -> LessThan (f e1, f e2)
  | LessThanOrEqual (e1, e2) -> LessThanOrEqual (f e1, f e2)
  | GreaterThan (e1, e2) -> GreaterThan (f e1, f e2)
  | GreaterThanOrEqual (e1, e2) -> GreaterThanOrEqual (f e1, f e2)
  | Equal (e1, e2) -> Equal (f e1, f e2)
  | NotEqual (e1, e2) -> NotEqual (f e1, f e2)
  | TypeAsc (expr, ty) -> TypeAsc (f expr, ty)
  | TypeCast (expr, ty) -> TypeAsc (f expr, ty)
  | Abstraction (params, expr) -> Abstraction (params, f expr)
  | Variant (ident, exprData) -> Variant (ident, map_expr_data f exprData)
  | Match (expr, cases) ->
      Match
        ( f expr,
          List.map
            (fun (AMatchCase (pattern, expr)) -> AMatchCase (pattern, f expr))
            cases )
  | List exprs -> List (List.map f exprs)
  | Add (e1, e2) -> Add (f e1, f e2)
  | Subtract (e1, e2) -> Subtract (f e1, f e2)
  | LogicOr (e1, e2) -> LogicOr (f e1, f e2)
  | Multiply (e1, e2) -> Multiply (f e1, f e2)
  | Divide (e1, e2) -> Divide (f e1, f e2)
  | LogicAnd (e1, e2) -> LogicAnd (f e1, f e2)
  | Ref expr -> Ref (f expr)
  | Deref expr -> Deref (f expr)
  | Application (expr, exprs) -> Application (f expr, List.map f exprs)
  | TypeApplication (expr, tys) -> TypeApplication (f expr, tys)
  | DotRecord (expr, ident) -> DotRecord (f expr, ident)
  | DotTuple (expr, offset) -> DotTuple (f expr, offset)
  | Tuple exprs -> Tuple (List.map f exprs)
  | Record bindings ->
      Record
        (List.map
           (fun (ABinding (ident, expr)) -> ABinding (ident, f expr))
           bindings)
  | ConsList (e1, e2) -> ConsList (f e1, f e2)
  | Head expr -> Head (f expr)
  | IsEmpty expr -> IsEmpty (f expr)
  | Tail expr -> Tail (f expr)
  | Throw expr -> Throw (f expr)
  | TryCatch (e1, pattern, e2) -> TryCatch (f e1, pattern, f e2)
  | TryWith (e1, e2) -> TryWith (f e1, f e2)
  | TryCastAs (e1, ty, pattern, e2, e3) -> TryCastAs (f e1, ty, pattern, e2, e3)
  | Inl expr -> Inl (f expr)
  | Inr expr -> Inr (f expr)
  | Succ expr -> Succ (f expr)
  | LogicNot expr -> LogicNot (f expr)
  | Pred expr -> Pred (f expr)
  | IsZero expr -> IsZero (f expr)
  | Fix expr -> Fix (f expr)
  | NatRec (e1, e2, e3) -> NatRec (f e1, f e2, f e3)
  | Fold (ty, expr) -> Fold (ty, f expr)
  | Unfold (ty, expr) -> Unfold (ty, f expr)
  | Panic -> Panic
  | ConstTrue -> ConstTrue
  | ConstFalse -> ConstFalse
  | ConstUnit -> ConstUnit
  | ConstInt n -> ConstInt n
  | ConstMemory m -> ConstMemory m
  | Var name -> Var name

let not_implemented s = raise (Failure ("Not implemented: " ^ s))

let pad_doc (pad_size : int) (d : PrintStella.doc) =
 fun buf i -> d buf (i + pad_size)

let pad_prt (pad_size : int) (prt : int -> 'a -> PrintStella.doc) =
 fun i e -> prt i e |> pad_doc pad_size

let default_pad (prt : int -> 'a -> PrintStella.doc) = pad_prt 4 prt
