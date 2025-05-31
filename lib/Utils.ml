open AbsStella

let get_ident (StellaIdent i) = i
let get_extension_name (ExtensionName n) = n
let get_memory_address (MemoryAddress m) = m

let get_program (AProgram (language, extensions, decls)) =
  (language, extensions, decls)

let get_program' (AProgram (_, extensions, decls)) = (extensions, decls)
let get_language LanguageCore = ()
let get_extension (AnExtension extension_names) = extension_names

let get_extension' (AnExtension extension_names) =
  List.map get_extension_name extension_names

let get_local_decl (ALocalDecl decl) = decl
let get_annotation InlineAnnotation = ()
let get_param_decl (AParamDecl (ident, ty)) = (ident, ty)
let get_param_decl' (AParamDecl (StellaIdent ident, ty)) = (ident, ty)

let return_type_to_option = function
  | NoReturnType -> None
  | SomeReturnType ty -> Some ty

let throw_type_to_option = function
  | NoThrowType -> None
  | SomeThrowType ty -> Some ty

let get_match_case (AMatchCase (pattern, expr)) = (pattern, expr)

let optional_typing_to_option = function
  | NoTyping -> None
  | SomeTyping ty -> Some ty

let pattern_data_to_option = function
  | NoPatternData -> None
  | SomePatternData data -> Some data

let expr_data_to_option = function
  | NoExprData -> None
  | SomeExprData data -> Some data

let get_labelled_pattern (ALabelledPattern (ident, pattern)) = (ident, pattern)

let get_labelled_pattern' (ALabelledPattern (StellaIdent ident, pattern)) =
  (ident, pattern)

let get_binding (ABinding (ident, expr)) = (ident, expr)
let get_binding' (ABinding (StellaIdent ident, expr)) = (ident, expr)
let get_variant_field_type (AVariantFieldType (ident, ty)) = (ident, ty)

let get_variant_field_type' (AVariantFieldType (StellaIdent ident, ty)) =
  (ident, ty)

let get_record_field_type (ARecordFieldType (ident, ty)) = (ident, ty)

let get_record_field_type' (ARecordFieldType (StellaIdent ident, ty)) =
  (ident, ty)

let get_typing (ATyping (expr, ty)) = (expr, ty)

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

let traverse_type (f : typeT -> typeT) = function
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
             AVariantFieldType
               ( ident,
                 match ty with
                 | NoTyping -> NoTyping
                 | SomeTyping ty -> SomeTyping (f ty) ))
           fields)
  | TypeList ty -> TypeList (f ty)
  | TypeBool -> TypeBool
  | TypeNat -> TypeNat
  | TypeUnit -> TypeUnit
  | TypeTop -> TypeTop
  | TypeBottom -> TypeBottom
  | TypeRef ty -> TypeRef (f ty)
  | TypeVar ident -> TypeVar ident
