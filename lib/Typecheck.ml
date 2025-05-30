open AbsStella

type tyError =
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
[@@deriving show]

exception TyExn of tyError

let not_implemented s = raise (Failure ("Not implemented: " ^ s))

let pad_doc (pad_size : int) (d : PrintStella.doc) =
 fun buf i -> d buf (i + pad_size)

let pad_prt (pad_size : int) (prt : int -> 'a -> PrintStella.doc) =
 fun i e -> prt i e |> pad_doc pad_size

let default_pad (prt : int -> 'a -> PrintStella.doc) = pad_prt 4 prt

let show_error (err : tyError) : string =
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

type context = Context.t

let make_eq (restrictions : (typeT * typeT) list ref) =
  let rec eq (ty1 : typeT) (ty2 : typeT) : bool =
    match (ty1, ty2) with
    | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
        List.compare_lengths tyArgs1 tyArgs2 = 0
        && List.for_all2 eq tyArgs1 tyArgs2
        && eq tyRet1 tyRet2
    | TypeSum (ty11, ty12), TypeSum (ty21, ty22) -> eq ty11 ty21 && eq ty12 ty22
    | TypeTuple tys1, TypeTuple tys2 ->
        List.compare_lengths tys1 tys2 = 0 && List.for_all2 eq tys1 tys2
    | TypeRecord fields1, TypeRecord fields2 ->
        List.compare_lengths fields1 fields2 = 0
        && List.for_all2
             (fun (ARecordFieldType (StellaIdent name1, ty1))
                  (ARecordFieldType (StellaIdent name2, ty2)) ->
               name1 = name2 && eq ty1 ty2)
             fields1 fields2
    | TypeVariant fields1, TypeVariant fields2 ->
        List.compare_lengths fields1 fields2 = 0
        && List.for_all2
             (fun (AVariantFieldType (StellaIdent name1, typing1))
                  (AVariantFieldType (StellaIdent name2, typing2)) ->
               name1 = name2
               &&
               match (typing1, typing2) with
               | SomeTyping ty1, SomeTyping ty2 -> eq ty1 ty2
               | NoTyping, NoTyping -> true
               | _ -> false)
             fields1 fields2
    | TypeList ty1, TypeList ty2 -> eq ty1 ty2
    | TypeBool, TypeBool -> true
    | TypeNat, TypeNat -> true
    | TypeUnit, TypeUnit -> true
    | TypeRef ty1, TypeRef ty2 -> eq ty1 ty2
    | TypeBottom, TypeBottom -> true
    | TypeVar (StellaIdent name1), TypeVar (StellaIdent name2) ->
        if name1 = name2 then true
        else if String.starts_with ~prefix:"?" name1 then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | TypeVar (StellaIdent name), _ ->
        if String.starts_with ~prefix:"?" name then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | _, TypeVar (StellaIdent name) ->
        if String.starts_with ~prefix:"?" name then (
          restrictions := (ty1, ty2) :: !restrictions;
          true)
        else false
    | _ -> false
  in
  eq

(* TODO: Check creation *)
let neq (ty1 : typeT) (ty2 : typeT) : bool = make_eq (ref []) ty1 ty2 |> not

let rec subtype (ty1 : typeT) (ty2 : typeT) : bool =
  (* print_endline
    ("Checking subtype "
    ^ PrintStella.printTree PrintStella.prtTypeT ty1
    ^ " with supertype "
    ^ PrintStella.printTree PrintStella.prtTypeT ty2); *)
  match (ty1, ty2) with
  | _, TypeTop -> true
  | TypeBottom, _ -> true
  | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
      List.compare_lengths tyArgs1 tyArgs2 = 0
      && List.for_all2 subtype tyArgs1 tyArgs2
      && subtype tyRet2 tyRet1
  | TypeSum (ty11, ty12), TypeSum (ty21, ty22) ->
      subtype ty11 ty21 && subtype ty12 ty22
  | TypeRecord fields1, TypeRecord fields2 ->
      let fields' =
        List.map
          (fun (ARecordFieldType (StellaIdent name, ty)) -> (name, ty))
          fields1
      in
      List.compare_lengths fields1 fields2 >= 0
      && List.for_all
           (fun (ARecordFieldType (StellaIdent name, ty)) ->
             match List.assoc_opt name fields' with
             | Some ty' -> subtype ty' ty
             | _ -> false)
           fields2
  | TypeVariant fields1, TypeVariant fields2 ->
      let fields' =
        List.map
          (fun (AVariantFieldType (StellaIdent name, typing)) -> (name, typing))
          fields2
      in
      List.compare_lengths fields1 fields2 <= 0
      && List.for_all
           (fun (AVariantFieldType (StellaIdent name, typing')) ->
             match List.assoc_opt name fields' with
             | Some typing -> (
                 match (typing', typing) with
                 | SomeTyping ty', SomeTyping ty -> subtype ty' ty
                 | NoTyping, NoTyping -> true
                 | _ -> false)
             | None -> false)
           fields1
  | TypeList ty1, TypeList ty2 -> subtype ty1 ty2
  | TypeBool, TypeBool -> true
  | TypeNat, TypeNat -> true
  | TypeUnit, TypeUnit -> true
  | TypeRef ty1, TypeRef ty2 -> subtype ty1 ty2 && subtype ty2 ty1
  | _ -> false

let check_main (ctx : context) : unit =
  match Context.get ctx "main" with
  | None -> raise (TyExn MissingMain)
  | _ -> ()

let rec synthesis_by_type (ty : typeT) : expr =
  match ty with
  (*
  | TypeAuto
  | TypeFun of typeT list * typeT
  | TypeForAll of stellaIdent list * typeT
  | TypeRec of stellaIdent * typeT
  *)
  | TypeSum (tyL, tyR) -> Inl (synthesis_by_type tyL)
  | TypeTuple types -> Tuple (List.map synthesis_by_type types)
  | TypeRecord fieldTypes ->
      let fields =
        List.map
          (fun (ARecordFieldType (ident, ty)) ->
            ABinding (ident, synthesis_by_type ty))
          fieldTypes
      in
      Record fields
  | TypeVariant (AVariantFieldType (ident, typing) :: _) ->
      let data =
        match typing with
        | SomeTyping ty -> SomeExprData (synthesis_by_type ty)
        | NoTyping -> NoExprData
      in
      Variant (ident, data)
  | TypeList _ -> List []
  | TypeBool -> ConstFalse
  | TypeNat -> ConstInt 0
  | TypeUnit -> ConstUnit
  (*
  | TypeTop
  | TypeBottom
  | TypeRef of typeT
  | TypeVar of stellaIdent
  *)
  | _ -> not_implemented "synthesis_by_type"

let rec matches (p : pattern) (term : expr) : bool =
  match (p, term) with
  (*
    | PatternCastAs of pattern * typeT
    *)
  | PatternAsc (p', _), _ -> matches p' term
  | PatternVariant (ident, NoPatternData), Variant (ident', NoExprData) ->
      ident = ident'
  | ( PatternVariant (ident, SomePatternData p'),
      Variant (ident', SomeExprData expr') ) ->
      ident = ident' && matches p' expr'
  | PatternInl p', Inl expr' -> matches p' expr'
  | PatternInr p', Inr expr' -> matches p' expr'
  | PatternTuple ps, Tuple exprs -> List.for_all2 matches ps exprs
  | PatternRecord lps, Record fields ->
      let fields' =
        List.map (fun (ABinding (ident, expr)) -> (ident, expr)) fields
      in
      List.map
        (fun (ALabelledPattern (ident, p')) -> (p', List.assoc ident fields'))
        lps
      |> List.for_all (fun (p', expr') -> matches p' expr')
  | PatternList ps, List exprs ->
      List.compare_lengths ps exprs = 0 && List.for_all2 matches ps exprs
  | PatternCons (p1, p2), List (e1 :: e2) ->
      matches p1 e1 && matches p2 (List e2)
  | PatternFalse, ConstFalse -> true
  | PatternTrue, ConstTrue -> true
  | PatternUnit, ConstUnit -> true
  | PatternInt n, ConstInt n' -> n = n'
  | PatternSucc p', ConstInt n -> n > 0 && matches p' (ConstInt (n - 1))
  | PatternVar _, _ -> true
  | _ -> false

let[@warning "-partial-match"] next_variant (Variant (ident, _))
    (TypeVariant fields) =
  let index =
    List.mapi (fun a b -> (b, a)) fields
    |> List.find_map (fun (AVariantFieldType (ident', _), idx) ->
           if ident = ident' then Some idx else None)
    |> Option.get
  in
  match List.nth_opt fields (index + 1) with
  | Some (AVariantFieldType (ident', NoTyping)) ->
      Some (Variant (ident', NoExprData))
  | Some (AVariantFieldType (ident', SomeTyping ty')) ->
      Some (Variant (ident', SomeExprData (synthesis_by_type ty')))
  | None -> None

let rec next_unmatched (p : pattern) (term : expr) (ty : typeT) : expr option =
  match (p, term, ty) with
  (*
    | PatternCastAs of pattern * typeT
    *)
  | PatternAsc (p', _), _, _ -> next_unmatched p' term ty
  | ( PatternVariant (ident, NoPatternData),
      Variant (_, NoExprData),
      TypeVariant fields ) ->
      next_variant term ty
  | ( PatternVariant (ident, SomePatternData p'),
      Variant (_, SomeExprData expr'),
      TypeVariant fields ) -> (
      let ty' =
        List.find_map
          (fun (AVariantFieldType (ident', ty)) ->
            if ident = ident' then
              match ty with SomeTyping ty' -> Some ty' | NoTyping -> None
            else None)
          fields
        |> Option.get
      in
      match next_unmatched p' expr' ty' with
      | Some expr'' -> Some (Variant (ident, SomeExprData expr''))
      | None -> next_variant term ty)
  | PatternInl p', Inl expr', TypeSum (tyL, tyR) -> (
      match next_unmatched p' expr' tyL with
      | Some expr'' -> Some (Inl expr'')
      | None -> Some (Inr (synthesis_by_type tyR)))
  | PatternInr p', Inr expr', TypeSum (tyL, tyR) -> (
      match next_unmatched p' expr' tyR with
      | Some expr'' -> Some (Inr expr'')
      | None -> None)
  | PatternTuple (p' :: ps), Tuple (expr' :: exprs), TypeTuple (ty' :: tys) -> (
      match next_unmatched (PatternTuple ps) (Tuple exprs) (TypeTuple tys) with
      | Some (Tuple exprs') -> Some (Tuple (expr' :: exprs'))
      | _ -> (
          match next_unmatched p' expr' ty' with
          | Some expr'' ->
              Some (Tuple (expr'' :: List.map synthesis_by_type tys))
          | _ -> None))
  | ( PatternRecord (ALabelledPattern (ident, lp) :: lps),
      Record fields,
      TypeRecord tys ) -> (
      let tysL =
        List.map (fun (ARecordFieldType (ident, ty)) -> (ident, ty)) tys
      in
      let fieldsL =
        List.map (fun (ABinding (ident, field)) -> (ident, field)) fields
      in
      let ty = List.assoc ident tysL in
      let expr' = List.assoc ident fieldsL in
      let tys' =
        List.filter (fun (ARecordFieldType (ident', _)) -> ident <> ident') tys
      in
      let fields' =
        List.filter (fun (ABinding (ident', _)) -> ident <> ident') fields
      in
      match
        next_unmatched (PatternRecord lps) (Record fields') (TypeRecord tys')
      with
      | Some (Record fields'') ->
          Some (Record (ABinding (ident, expr') :: fields''))
      | _ -> (
          match next_unmatched lp expr' ty with
          | Some expr'' ->
              let fields'' =
                ABinding (ident, expr'')
                :: List.map
                     (fun (ARecordFieldType (ident, ty')) ->
                       ABinding (ident, synthesis_by_type ty'))
                     tys'
              in
              Some (Record fields'')
          | None -> None))
  | PatternList (p' :: ps), List (expr' :: exprs), TypeList ty' -> (
      match next_unmatched (PatternList ps) (List exprs) ty with
      | Some (List exprs') -> Some (List (expr' :: exprs'))
      | _ -> (
          match next_unmatched p' expr' ty' with
          | Some expr'' -> Some (List [ expr'' ])
          | None -> None))
  | PatternList [], List [], TypeList ty' ->
      Some (List [ synthesis_by_type ty' ])
  | PatternCons (p1, p2), List (e1 :: e2), TypeList ty' -> (
      match next_unmatched p2 (List e2) ty with
      | Some (List exprs') -> Some (List (e1 :: exprs'))
      | _ -> (
          match next_unmatched p1 e1 ty' with
          | Some expr'' -> Some (List [ expr'' ])
          | None -> None))
  | PatternFalse, ConstFalse, TypeBool -> Some ConstTrue
  | PatternTrue, ConstTrue, TypeBool -> None
  | PatternUnit, ConstUnit, TypeUnit -> None
  | PatternInt n, ConstInt _, TypeNat -> Some (ConstInt (n + 1))
  | PatternSucc p', ConstInt n, TypeNat -> (
      match next_unmatched p' (ConstInt (n - 1)) TypeNat with
      | Some (ConstInt n') -> Some (ConstInt (n' + 1))
      | _ -> None)
  | PatternVar _, _, _ -> None
  | _ -> None

let check_exhaustivness (ps : pattern list) (ty : typeT) : expr option =
  match ty with
  (* W/O cast as if it typecheked -> there is wildcard *)
  | TypeFun _ -> None
  | TypeTop -> None
  | TypeBottom -> None
  | TypeRef _ -> None
  | _ ->
      let init = synthesis_by_type ty in
      let rec check_exhaustivness' (term : expr) : expr option =
        match List.find_opt (fun p -> matches p term) ps with
        | Some p -> (
            match next_unmatched p term ty with
            | Some term' -> check_exhaustivness' term'
            | None -> None)
        | None -> Some term
      in
      check_exhaustivness' init

let rec deconstruct_pattern_binder (p : pattern) (ty : typeT) : context =
  match (p, ty) with
  (*
  | PatternCastAs of pattern * typeT
  *)
  | PatternAsc (p', ty'), _ ->
      if neq ty' ty then raise (TyExn (UnexpectedPatternForType (p, ty)))
      else deconstruct_pattern_binder p' ty
  | PatternVariant (StellaIdent name, patternData), TypeVariant fieldTypes -> (
      let rec find fieldTypes =
        match fieldTypes with
        | AVariantFieldType (StellaIdent name', typing) :: fieldTypes' ->
            if name = name' then typing else find fieldTypes'
        | _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
      in
      let typing = find fieldTypes in
      match (typing, patternData) with
      | SomeTyping ty', SomePatternData p' -> deconstruct_pattern_binder p' ty'
      | NoTyping, NoPatternData -> Context.empty
      | _ -> raise (TyExn (UnexpectedPatternForType (p, ty))))
  | PatternVariant _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternInl p', TypeSum (tyL, _) -> deconstruct_pattern_binder p' tyL
  | PatternInl _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternInr p', TypeSum (_, tyR) -> deconstruct_pattern_binder p' tyR
  | PatternInr _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternTuple ps, TypeTuple types ->
      if List.compare_lengths ps types <> 0 then
        raise (TyExn (UnexpectedPatternForType (p, ty)))
      else
        List.combine ps types
        |> List.map (fun (p', ty') -> deconstruct_pattern_binder p' ty')
        |> Context.concat
  | PatternTuple _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternRecord lps, TypeRecord ftys ->
      (* TODO Check fields *)
      let types =
        List.map
          (fun (ARecordFieldType (StellaIdent name, ty)) -> (name, ty))
          ftys
      in
      List.map
        (fun (ALabelledPattern (StellaIdent name, p')) ->
          List.assoc name types |> deconstruct_pattern_binder p')
        lps
      |> Context.concat
  | PatternRecord _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternList ps, TypeList ty' ->
      List.map (fun p' -> deconstruct_pattern_binder p' ty') ps
      |> Context.concat
  | PatternList _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternCons (p1, p2), TypeList ty' ->
      Context.concat
        [ deconstruct_pattern_binder p1 ty'; deconstruct_pattern_binder p2 ty ]
  | PatternCons _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternFalse, TypeBool -> Context.empty
  | PatternFalse, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternTrue, TypeBool -> Context.empty
  | PatternTrue, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternUnit, TypeUnit -> Context.empty
  | PatternUnit, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternInt _, TypeNat -> Context.empty
  | PatternInt _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternSucc p', TypeNat -> deconstruct_pattern_binder p' TypeNat
  | PatternSucc _, _ -> raise (TyExn (UnexpectedPatternForType (p, ty)))
  | PatternVar (StellaIdent name), _ -> Context.from_var name ty
  | _, _ -> not_implemented "deconstruct_pattern_binder"

let find_dup (xs : string list) =
  let rec find_dup' (xs : string list) (dup : string list) =
    match xs with
    | x :: xs' ->
        let dup' =
          if List.mem x xs' && not (List.mem x dup) then x :: dup else dup
        in
        find_dup' xs' dup'
    | _ -> dup
  in
  find_dup' xs []

let rec check_type (ctx : context) (ty : typeT) =
  match ty with
  | TypeFun (types, res) ->
      List.iter (check_type ctx) types;
      check_type ctx res
  | TypeSum (ty1, ty2) ->
      check_type ctx ty1;
      check_type ctx ty2
  | TypeTuple types -> List.iter (check_type ctx) types
  | TypeRecord fieldTypes ->
      let dup =
        List.map
          (fun (ARecordFieldType (StellaIdent name, _)) -> name)
          fieldTypes
        |> find_dup
      in
      if List.compare_length_with dup 0 > 0 then
        raise (TyExn (DuplicateRecordTypeFields (dup, ty)))
      else
        List.map (fun (ARecordFieldType (_, ty)) -> ty) fieldTypes
        |> List.iter (check_type ctx)
  | TypeVariant varTypes ->
      let dup =
        List.map
          (fun (AVariantFieldType (StellaIdent name, _)) -> name)
          varTypes
        |> find_dup
      in
      if List.compare_length_with dup 0 > 0 then
        raise (TyExn (DuplicateVariantTypeFields (dup, ty)))
      else
        List.filter_map
          (fun (AVariantFieldType (_, typing)) ->
            match typing with SomeTyping ty -> Some ty | NoTyping -> None)
          varTypes
        |> List.iter (check_type ctx)
  | TypeList ty -> check_type ctx ty
  | TypeRef ty -> check_type ctx ty
  | TypeVar (StellaIdent name) ->
      if Context.has_type ctx name then ()
      else raise (TyExn (UndefinedTypeVariable ty))
  | _ -> ()

let auto_fresh (fresh_var : unit -> string) (ctx : context) : context =
  let rec auto_fresh' = function
    | TypeAuto -> TypeVar (StellaIdent (fresh_var ()))
    | TypeFun (tys, ty) -> TypeFun (List.map auto_fresh' tys, auto_fresh' ty)
    | TypeForAll (idents, ty) -> TypeForAll (idents, auto_fresh' ty)
    | TypeRec (ident, ty) -> TypeRec (ident, auto_fresh' ty)
    | TypeSum (tyL, tyR) -> TypeSum (auto_fresh' tyL, auto_fresh' tyR)
    | TypeTuple tys -> TypeTuple (List.map auto_fresh' tys)
    | TypeRecord fields ->
        TypeRecord
          (List.map
             (fun (ARecordFieldType (name, ty)) ->
               ARecordFieldType (name, auto_fresh' ty))
             fields)
    | TypeVariant fields ->
        TypeVariant
          (List.map
             (fun (AVariantFieldType (name, optionalTyping)) ->
               AVariantFieldType
                 ( name,
                   match optionalTyping with
                   | SomeTyping ty -> SomeTyping (auto_fresh' ty)
                   | x -> x ))
             fields)
    | TypeList ty -> TypeList (auto_fresh' ty)
    | TypeRef ty -> TypeRef (auto_fresh' ty)
    | ty -> ty
  in
  Context.map (fun (name, ty) -> (name, auto_fresh' ty)) ctx

let rec fresh_decls (fresh_var : unit -> string) (decls : decl list) : decl list
    =
  let rec fresh_type = function
    | TypeAuto -> TypeVar (StellaIdent (fresh_var ()))
    | TypeFun (tys, ty) -> TypeFun (List.map fresh_type tys, fresh_type ty)
    | TypeForAll (idents, ty) -> TypeForAll (idents, fresh_type ty)
    | TypeRec (ident, ty) -> TypeRec (ident, fresh_type ty)
    | TypeSum (tyL, tyR) -> TypeSum (fresh_type tyL, fresh_type tyR)
    | TypeTuple tys -> TypeTuple (List.map fresh_type tys)
    | TypeRecord fields ->
        TypeRecord
          (List.map
             (fun (ARecordFieldType (name, ty)) ->
               ARecordFieldType (name, fresh_type ty))
             fields)
    | TypeVariant fields ->
        TypeVariant
          (List.map
             (fun (AVariantFieldType (name, optionalTyping)) ->
               AVariantFieldType
                 ( name,
                   match optionalTyping with
                   | SomeTyping ty -> SomeTyping (fresh_type ty)
                   | x -> x ))
             fields)
    | TypeList ty -> TypeList (fresh_type ty)
    | TypeRef ty -> TypeRef (fresh_type ty)
    | ty -> ty
  in
  let fresh_params =
    List.map (fun (AParamDecl (ident, ty)) -> AParamDecl (ident, fresh_type ty))
  in
  let fresh_return = function
    | SomeReturnType ty -> SomeReturnType (fresh_type ty)
    | NoReturnType -> NoReturnType
  in
  let fresh_throws = function
    | SomeThrowType ty -> SomeThrowType (List.map fresh_type ty)
    | NoThrowType -> NoThrowType
  in
  let rec fresh_expr : expr -> expr = function
    | Sequence (e1, e2) -> Sequence (fresh_expr e1, fresh_expr e2)
    | Assign (e1, e2) -> Assign (fresh_expr e1, fresh_expr e2)
    | If (e1, e2, e3) -> If (fresh_expr e1, fresh_expr e2, fresh_expr e3)
    | Let (patterns, expr) ->
        (* I don't know what to do with patterns in let *)
        Let (patterns, fresh_expr expr)
    | LetRec (patterns, expr) -> LetRec (patterns, fresh_expr expr)
    | TypeAbstraction (idents, expr) -> TypeAbstraction (idents, fresh_expr expr)
    | LessThan (e1, e2) -> LessThan (fresh_expr e1, fresh_expr e2)
    | LessThanOrEqual (e1, e2) -> LessThanOrEqual (fresh_expr e1, fresh_expr e2)
    | GreaterThan (e1, e2) -> GreaterThan (fresh_expr e1, fresh_expr e2)
    | GreaterThanOrEqual (e1, e2) ->
        GreaterThanOrEqual (fresh_expr e1, fresh_expr e2)
    | Equal (e1, e2) -> Equal (fresh_expr e1, fresh_expr e2)
    | NotEqual (e1, e2) -> NotEqual (fresh_expr e1, fresh_expr e2)
    | TypeAsc (expr, ty) -> TypeAsc (fresh_expr expr, fresh_type ty)
    | TypeCast (expr, ty) -> TypeAsc (fresh_expr expr, fresh_type ty)
    | Abstraction (params, expr) ->
        Abstraction (fresh_params params, fresh_expr expr)
    | Variant (ident, exprData) ->
        Variant
          ( ident,
            match exprData with
            | SomeExprData expr -> SomeExprData (fresh_expr expr)
            | NoExprData -> NoExprData )
    | Match (expr, cases) ->
        Match
          ( fresh_expr expr,
            List.map
              (fun (AMatchCase (pattern, expr)) ->
                AMatchCase (pattern, fresh_expr expr))
              cases )
    | List exprs -> List (List.map fresh_expr exprs)
    | Add (e1, e2) -> Add (fresh_expr e1, fresh_expr e2)
    | Subtract (e1, e2) -> Subtract (fresh_expr e1, fresh_expr e2)
    | LogicOr (e1, e2) -> LogicOr (fresh_expr e1, fresh_expr e2)
    | Multiply (e1, e2) -> Multiply (fresh_expr e1, fresh_expr e2)
    | Divide (e1, e2) -> Divide (fresh_expr e1, fresh_expr e2)
    | LogicAnd (e1, e2) -> LogicAnd (fresh_expr e1, fresh_expr e2)
    | Ref expr -> Ref (fresh_expr expr)
    | Deref expr -> Deref (fresh_expr expr)
    | Application (expr, exprs) ->
        Application (fresh_expr expr, List.map fresh_expr exprs)
    | TypeApplication (expr, tys) ->
        TypeApplication (fresh_expr expr, List.map fresh_type tys)
    | DotRecord (expr, ident) -> DotRecord (fresh_expr expr, ident)
    | DotTuple (expr, offset) -> DotTuple (fresh_expr expr, offset)
    | Tuple exprs -> Tuple (List.map fresh_expr exprs)
    | Record bindings ->
        Record
          (List.map
             (fun (ABinding (ident, expr)) -> ABinding (ident, fresh_expr expr))
             bindings)
    | ConsList (e1, e2) -> ConsList (fresh_expr e1, fresh_expr e2)
    | Head expr -> Head (fresh_expr expr)
    | IsEmpty expr -> IsEmpty (fresh_expr expr)
    | Tail expr -> Tail (fresh_expr expr)
    | Throw expr -> Throw (fresh_expr expr)
    | TryCatch (e1, pattern, e2) ->
        TryCatch (fresh_expr e1, pattern, fresh_expr e2)
    | TryWith (e1, e2) -> TryWith (fresh_expr e1, fresh_expr e2)
    | TryCastAs (e1, ty, pattern, e2, e3) ->
        TryCastAs (fresh_expr e1, fresh_type ty, pattern, e2, e3)
    | Inl expr -> Inl (fresh_expr expr)
    | Inr expr -> Inr (fresh_expr expr)
    | Succ expr -> Succ (fresh_expr expr)
    | LogicNot expr -> LogicNot (fresh_expr expr)
    | Pred expr -> Pred (fresh_expr expr)
    | IsZero expr -> IsZero (fresh_expr expr)
    | Fix expr -> Fix (fresh_expr expr)
    | NatRec (e1, e2, e3) -> NatRec (fresh_expr e1, fresh_expr e2, fresh_expr e3)
    | Fold (ty, expr) -> Fold (fresh_type ty, fresh_expr expr)
    | Unfold (ty, expr) -> Fold (fresh_type ty, fresh_expr expr)
    | expr -> expr
  in
  List.map
    (function
      | DeclFun (annotations, ident, params, tyRet, throws, decls, expr) ->
          DeclFun
            ( annotations,
              ident,
              fresh_params params,
              fresh_return tyRet,
              fresh_throws throws,
              fresh_decls fresh_var decls,
              fresh_expr expr )
      | DeclFunGeneric
          (annotations, ident, tyArgs, params, tyRet, throws, decls, expr) ->
          DeclFunGeneric
            ( annotations,
              ident,
              tyArgs,
              fresh_params params,
              fresh_return tyRet,
              fresh_throws throws,
              fresh_decls fresh_var decls,
              fresh_expr expr )
      | DeclTypeAlias (ident, ty) -> DeclTypeAlias (ident, fresh_type ty)
      | DeclExceptionType ty -> DeclExceptionType (fresh_type ty)
      | DeclExceptionVariant (ident, ty) ->
          DeclExceptionVariant (ident, fresh_type ty))
    decls

let put_params (ctx : context) (params : paramDecl list) : context =
  List.iter (fun (AParamDecl (_, ty)) -> check_type ctx ty) params;
  List.map
    (fun (AParamDecl (StellaIdent name, ty)) -> Context.from_var name ty)
    params
  |> Context.concat |> Fun.flip Context.merge ctx

let rec used_vars (ty : typeT) : Set.Make(String).t =
  let module StringSet = Set.Make (String) in
  match ty with
  | TypeFun (tys, ty) ->
      List.fold_left
        (fun s ty -> StringSet.union s (used_vars ty))
        StringSet.empty (ty :: tys)
  | TypeForAll (idents, ty) ->
      let res = used_vars ty in
      let var =
        List.map (fun (StellaIdent name) -> name) idents |> StringSet.of_list
      in
      StringSet.diff res var
  (* | TypeRec of stellaIdent * typeT not supported *)
  | TypeSum (ty1, ty2) -> StringSet.union (used_vars ty1) (used_vars ty2)
  | TypeTuple tys ->
      List.fold_left
        (fun s ty -> StringSet.union s (used_vars ty))
        StringSet.empty tys
  | TypeRecord fields ->
      List.fold_left
        (fun s (ARecordFieldType (_, ty)) -> StringSet.union s (used_vars ty))
        StringSet.empty fields
  | TypeVariant fields ->
      List.fold_left
        (fun s (AVariantFieldType (_, typing)) ->
          match typing with
          | SomeTyping ty -> StringSet.union s (used_vars ty)
          | _ -> s)
        StringSet.empty fields
  | TypeList ty -> used_vars ty
  | TypeRef ty -> used_vars ty
  | TypeVar (StellaIdent name) -> StringSet.singleton name
  | _ -> StringSet.empty

let check_recur (var : string) (_in : typeT) : bool =
  let rec check_recur' (_in : typeT) : bool =
    match _in with
    | TypeFun (tys, ty) -> List.exists check_recur' tys || check_recur' ty
    | TypeForAll (idents, ty) ->
        if List.exists (fun (StellaIdent name) -> name = var) idents then false
        else check_recur' ty
    | TypeRec (StellaIdent name, ty) ->
        if name = var then false else check_recur' ty
    | TypeSum (tyL, tyR) -> check_recur' tyL || check_recur' tyR
    | TypeTuple tys -> List.exists check_recur' tys
    | TypeRecord fields ->
        List.exists
          (fun (ARecordFieldType (name, ty)) -> check_recur' ty)
          fields
    | TypeVariant fields ->
        List.exists
          (fun (AVariantFieldType (name, typing)) ->
            match typing with
            | SomeTyping ty -> check_recur' ty
            | NoTyping -> false)
          fields
    | TypeList ty -> check_recur' ty
    | TypeRef ty -> check_recur' ty
    | TypeVar (StellaIdent name) -> name = var
    | _ -> false
  in
  check_recur' _in

module type Context = sig
  val ambiguous : exn -> typeT
  val exception_type : typeT option
  val is_subtyping : bool
  val eq : typeT -> typeT -> bool
  val unexpected_type : typeT -> typeT -> expr -> 'a
  val fresh_var : unit -> string
  val restrictions : (typeT * typeT) list ref
end

module Make (Ctx : Context) = struct
  let neq (ty1 : typeT) (ty2 : typeT) : bool = Ctx.eq ty1 ty2 |> not

  let rec substitute (from : string) (_to : typeT) (_in : typeT) =
    let rec s (_in : typeT) =
      match _in with
      | TypeFun (tys, ty) -> TypeFun (List.map s tys, s ty)
      | TypeForAll (idents, ty) ->
          if List.exists (fun (StellaIdent name) -> name = from) idents then _in
          else
            let module StringSet = Set.Make (String) in
            let used = used_vars _to in
            if
              List.exists
                (fun (StellaIdent name) -> StringSet.mem name used)
                idents
            then
              let ty', names =
                List.fold_left
                  (fun ((ty, names) : typeT * stellaIdent list)
                       (StellaIdent name) ->
                    let fresh_name = StellaIdent ("!" ^ Ctx.fresh_var ()) in
                    let fresh_ty = TypeVar fresh_name in
                    (substitute name fresh_ty ty, fresh_name :: names))
                  (ty, []) idents
              in
              TypeForAll (names, s ty')
            else TypeForAll (idents, s ty)
      | TypeRec (StellaIdent name, ty) ->
          if name = from then _in else TypeRec (StellaIdent name, s ty)
      | TypeSum (tyL, tyR) -> TypeSum (s tyL, s tyR)
      | TypeTuple tys -> TypeTuple (List.map s tys)
      | TypeRecord fields ->
          TypeRecord
            (List.map
               (fun (ARecordFieldType (name, ty)) ->
                 ARecordFieldType (name, s ty))
               fields)
      | TypeVariant fields ->
          TypeVariant
            (List.map
               (fun (AVariantFieldType (name, typing)) ->
                 AVariantFieldType
                   ( name,
                     match typing with
                     | SomeTyping ty -> SomeTyping (s ty)
                     | NoTyping -> NoTyping ))
               fields)
      | TypeList ty -> TypeList (s ty)
      | TypeRef ty -> TypeRef (s ty)
      | TypeVar (StellaIdent name) -> if name = from then _to else _in
      | _ -> _in
    in
    s _in

  let apply_type (tys : typeT list) (names : string list) (ty : typeT) : typeT =
    let names' = List.map (fun x -> StellaIdent x) names in
    if List.compare_lengths tys names <> 0 then
      raise
        (TyExn (IncorrectNumberOfTypeArguments (TypeForAll (names', ty), tys)))
    else
      List.fold_left2 (fun ty from _to -> substitute from _to ty) ty names tys

  let unify (restrictions : (typeT * typeT) list) : typeT -> typeT =
    let rec unify' (restrictions : (typeT * typeT) list)
        (sigma : typeT -> typeT) : typeT -> typeT =
      match restrictions with
      | (ty1, ty2) :: restrictions' -> (
          match (ty1, ty2) with
          | TypeVar (StellaIdent name), TypeVar (StellaIdent name') ->
              if name = name' then unify' restrictions' sigma
              else
                let subs = substitute name (TypeVar (StellaIdent name')) in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | TypeVar (StellaIdent name), _ ->
              if check_recur name ty2 then
                raise (TyExn (OccursCheckInfiniteType ty2))
              else
                let subs = substitute name ty2 in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | _, TypeVar (StellaIdent name) ->
              if check_recur name ty1 then
                raise (TyExn (OccursCheckInfiniteType ty1))
              else
                let subs = substitute name ty1 in
                unify'
                  (List.map (fun (a, b) -> (subs a, subs b)) restrictions')
                  (fun t -> sigma t |> subs)
          | TypeFun (tyArgs1, tyRet1), TypeFun (tyArgs2, tyRet2) ->
              let restrictions'' =
                List.concat
                  [
                    List.combine tyArgs1 tyArgs2;
                    [ (tyRet1, tyRet2) ];
                    restrictions';
                  ]
              in
              unify' restrictions'' sigma
          (* | TypeForAll not supported :shrug: *)
          (* | TypeRec not supported too *)
          | TypeSum (tyL1, tyR1), TypeSum (tyL2, tyR2) ->
              let restrictions'' =
                (tyL1, tyL2) :: (tyR1, tyR2) :: restrictions'
              in
              unify' restrictions'' sigma
          | TypeTuple tys1, TypeTuple tys2 ->
              let restrictions'' =
                List.concat [ List.combine tys1 tys2; restrictions' ]
              in
              unify' restrictions'' sigma
          | TypeRecord fields1, TypeRecord fields2 ->
              let fields1' =
                List.map
                  (fun (ARecordFieldType (StellaIdent name, ty')) ->
                    (name, ty'))
                  fields1
              in
              let fields2' =
                List.map
                  (fun (ARecordFieldType (StellaIdent name, ty')) ->
                    (name, ty'))
                  fields2
              in
              let rec convert (fields1 : (string * typeT) list)
                  (fields2 : (string * typeT) list)
                  ((fieldPairs, missingFields, extraFields) :
                    (typeT * typeT) list * string list * string list) =
                match fields1 with
                | (name, ty1) :: fields' -> (
                    match List.assoc_opt name fields2 with
                    | Some ty ->
                        convert fields'
                          (List.remove_assoc name fields2)
                          ((ty1, ty) :: fieldPairs, missingFields, extraFields)
                    | _ ->
                        convert fields'
                          (List.remove_assoc name fields2)
                          (fieldPairs, missingFields, name :: extraFields))
                | _ ->
                    ( fieldPairs,
                      List.concat
                        [ List.map (fun (a, _) -> a) fields2; missingFields ],
                      extraFields )
              in
              let fieldPairs, missingFields, extraFields =
                convert fields1' fields2' ([], [], [])
              in
              if List.compare_length_with extraFields 0 <> 0 then
                (* TODO: Version for unify *)
                raise
                  (TyExn (UnexpectedRecordFields (extraFields, ty2, ConstUnit)))
              else if List.compare_length_with missingFields 0 <> 0 then
                raise
                  (TyExn (MissingRecordFields (missingFields, ty2, ConstUnit)))
              else unify' fieldPairs sigma
          (* | TypeVariant tricky not supported *)
          | TypeList ty1', TypeList ty2' ->
              unify' ((ty1', ty2') :: restrictions') sigma
          | TypeRef ty1', TypeRef ty2' ->
              unify' ((ty1', ty2') :: restrictions') sigma
          | _ ->
              (* TODO: Add unification error *)
              raise (TyExn (UnexpectedTypeForExpression (ty1, ty2, ConstUnit))))
      | [] -> sigma
    in
    unify' restrictions Fun.id

  let rec typecheck (ctx : context) (expr : expr) (ty : typeT) =
    (* print_endline
    ("Checking expr "
    ^ PrintStella.printTree PrintStella.prtExpr expr
    ^ " with type "
    ^ PrintStella.printTree PrintStella.prtTypeT ty); *)
    match (expr, ty) with
    | Sequence (e1, e2), _ ->
        typecheck ctx e1 TypeUnit;
        typecheck ctx e2 ty
    | Assign (e1, e2), _ -> (
        if neq TypeUnit ty then Ctx.unexpected_type ty TypeUnit expr
        else
          match infer ctx e1 with
          | TypeRef ty' -> typecheck ctx e2 ty'
          | ty' -> raise (TyExn (NotAReference (ty', e1))))
    | If (eIf, eThen, eElse), _ ->
        typecheck ctx eIf TypeBool;
        typecheck ctx eThen ty;
        typecheck ctx eElse ty
    | Let (binders, expr'), _ ->
        (* TODO: check semantics *)
        let bindersCtx =
          List.map
            (fun (APatternBinding (p, expr'')) ->
              deconstruct_pattern_binder p (infer ctx expr''))
            binders
          |> Context.concat
        in
        let ctx' = Context.concat [ bindersCtx; ctx ] in
        typecheck ctx' expr' ty
    (* LetRec TODO *)
    | TypeAbstraction (tys, expr), TypeForAll (tysP, ty) ->
        if List.compare_lengths tys tysP <> 0 then
          Ctx.unexpected_type ty (infer ctx expr) expr
        else
          let ctx' =
            List.map (fun (StellaIdent a) -> a) tys
            |> List.fold_left Context.put_type ctx
          in
          let ty' =
            List.fold_left2
              (fun ty (StellaIdent from) _to ->
                substitute from (TypeVar _to) ty)
              ty tysP tys
          in
          typecheck ctx' expr ty'
    | TypeAbstraction _, _ -> Ctx.unexpected_type ty (infer ctx expr) expr
    | LessThan (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LessThanOrEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | GreaterThan (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | GreaterThanOrEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Equal (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | NotEqual (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | TypeAsc (e1, ty'), _ ->
        if neq ty' ty then Ctx.unexpected_type ty ty' expr
        else (
          check_type ctx ty';
          typecheck ctx e1 ty')
    | Abstraction (params, expr'), TypeFun (tyParams, tyReturn) ->
        (* Check arity *)
        (* List.compare_lengths tyParams params = 0 *)
        List.iter2
          (fun ty (AParamDecl (ident, ty')) ->
            if neq ty' ty then
              raise
                (TyExn
                   (UnexpectedTypeForParameter (ty, ty', AParamDecl (ident, ty))))
            else ())
          tyParams params;
        let ctx' = put_params ctx params in
        check_type ctx' tyReturn;
        typecheck ctx' expr' tyReturn
    | Abstraction _, TypeTop -> infer ctx expr |> ignore
    | Abstraction _, _ -> raise (TyExn (UnexpectedLambda (ty, expr)))
    | Variant (StellaIdent name, SomeExprData expr'), TypeVariant fieldTypes ->
        (* TODO: No expr data *)
        let rec find (fieldTypes : variantFieldType list) =
          match fieldTypes with
          | AVariantFieldType (StellaIdent name', SomeTyping ty') :: fieldTypes'
            ->
              if name = name' then ty' else find fieldTypes'
          | _ -> raise (TyExn (UnexpectedVariantLabel (ty, name, expr)))
        in
        let ty' = find fieldTypes in
        typecheck ctx expr' ty'
    | Variant _, TypeTop -> infer ctx expr |> ignore
    | Variant _, _ -> raise (TyExn (UnexpectedVariant (ty, expr)))
    | Match (_, []), _ -> raise (TyExn (IllegalEmptyMatching expr))
    | Match (expr', cases), _ -> (
        let ty' = infer ctx expr' in
        List.iter
          (fun (AMatchCase (pat, expr'')) ->
            let ctx' =
              Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
            in
            typecheck ctx' expr'' ty)
          cases;
        let ps = List.map (fun (AMatchCase (p, _)) -> p) cases in
        match check_exhaustivness ps ty' with
        | Some expr'' ->
            raise (TyExn (NonexhaustiveMatchPatterns (expr'', expr)))
        | None -> ())
    | List exprs, TypeList ty' ->
        List.iter (fun expr' -> typecheck ctx expr' ty') exprs
    | List [], TypeTop -> ()
    | List _, TypeTop -> infer ctx expr |> ignore
    | List _, _ -> raise (TyExn (UnexpectedList (ty, expr)))
    | Add (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Subtract (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LogicOr (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool
    | Multiply (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | Divide (e1, e2), _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat
    | LogicAnd (e1, e2), _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool
    | Ref expr', TypeRef ty' -> typecheck ctx expr' ty'
    | Ref expr', TypeTop -> typecheck ctx expr' ty
    | Ref _, _ -> Ctx.unexpected_type ty (infer ctx expr) expr
    | Deref _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Application _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | TypeApplication (expr, tys), _ -> (
        let ty' = infer ctx expr in
        match ty' with
        | TypeForAll (tys', tyRes) ->
            let tys' = List.map (fun (StellaIdent i) -> i) tys' in
            let ty'' = apply_type tys tys' tyRes in
            if neq ty'' ty then Ctx.unexpected_type ty ty'' expr
        | _ -> raise (TyExn (NotAGenericFunction ty')))
    | DotRecord _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | DotTuple _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Tuple exprs, TypeTuple tyExprs ->
        if List.compare_lengths exprs tyExprs <> 0 then
          raise
            (TyExn
               (UnexpectedTupleLength
                  (List.length tyExprs, List.length exprs, expr)))
        else
          List.fold_left
            (fun _ (expr, ty) -> typecheck ctx expr ty)
            ()
            (List.combine exprs tyExprs)
    | Tuple _, TypeTop -> infer ctx expr |> ignore
    | Tuple _, _ -> raise (TyExn (UnexpectedTuple (ty, expr)))
    | Record fields, TypeRecord fieldTypes ->
        let fields' =
          List.map
            (fun (ABinding (StellaIdent name, expr')) -> (name, expr'))
            fields
        in
        let rec findDupFields (fields : (string * _) list)
            (dupFields : string list) =
          match fields with
          | (name, _) :: fields' ->
              let dupFields' =
                if List.mem_assoc name fields' && not (List.mem name dupFields)
                then name :: dupFields
                else dupFields
              in
              findDupFields fields' dupFields'
          | _ -> dupFields
        in
        let dupFields = findDupFields fields' [] in
        if List.compare_length_with dupFields 0 <> 0 then
          raise (TyExn (DuplicateRecordFields (dupFields, expr)))
        else
          let fieldTypes' =
            List.map
              (fun (ARecordFieldType (StellaIdent name, ty')) -> (name, ty'))
              fieldTypes
          in
          let rec convert (fields : (string * expr) list)
              (types : (string * typeT) list)
              ((fieldExpr, missingFields, extraFields) :
                (expr * typeT) list * string list * string list) =
            match fields with
            | (name, expr) :: fields' -> (
                match List.assoc_opt name types with
                | Some ty ->
                    convert fields'
                      (List.remove_assoc name types)
                      ((expr, ty) :: fieldExpr, missingFields, extraFields)
                | _ ->
                    convert fields'
                      (List.remove_assoc name types)
                      (fieldExpr, missingFields, name :: extraFields))
            | _ ->
                ( fieldExpr,
                  List.concat
                    [ List.map (fun (a, _) -> a) types; missingFields ],
                  extraFields )
          in
          let fieldExpr, missingFields, extraFields =
            convert fields' fieldTypes' ([], [], [])
          in
          if List.compare_length_with extraFields 0 <> 0 && not Ctx.is_subtyping
          then raise (TyExn (UnexpectedRecordFields (extraFields, ty, expr)))
          else if List.compare_length_with missingFields 0 <> 0 then
            raise (TyExn (MissingRecordFields (missingFields, ty, expr)))
          else List.iter (fun (expr', ty') -> typecheck ctx expr' ty') fieldExpr
    | Record _, TypeTop -> infer ctx expr |> ignore
    | Record _, _ -> raise (TyExn (UnexpectedRecord (ty, expr)))
    | ConsList (e1, e2), TypeList ty' ->
        typecheck ctx e1 ty';
        typecheck ctx e2 ty
    | ConsList _, _ -> raise (TyExn (UnexpectedList (ty, expr)))
    | Head _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Tail _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | IsEmpty _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
    | Panic, _ -> ()
    | Throw expr', _ -> (
        match Ctx.exception_type with
        | Some ty' -> typecheck ctx expr' ty'
        | None -> raise (TyExn (ExceptionTypeNotDeclared expr)))
    | TryCatch (e1, pat, e2), _ ->
        typecheck ctx e1 ty;
        let exception_type =
          match Ctx.exception_type with
          | Some ty -> ty
          | None -> raise (TyExn (ExceptionTypeNotDeclared expr))
        in
        let ctx' =
          Context.concat [ deconstruct_pattern_binder pat exception_type ]
        in
        typecheck ctx' e2 ty
    | TryWith (e1, e2), _ ->
        typecheck ctx e1 ty;
        typecheck ctx e2 ty
    | Inl expr', TypeSum (tyL, _) -> typecheck ctx expr' tyL
    | Inl expr', TypeTop -> typecheck ctx expr' TypeTop
    | Inl _, _ -> raise (TyExn (UnexpectedInjection (ty, expr)))
    | Inr expr', TypeSum (_, tyR) -> typecheck ctx expr' tyR
    | Inr expr', TypeTop -> typecheck ctx expr' TypeTop
    | Inr _, _ -> raise (TyExn (UnexpectedInjection (ty, expr)))
    | Succ expr', _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx expr' TypeNat
    | LogicNot expr', _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx expr' TypeBool
    | Pred expr', _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr
        else typecheck ctx expr' TypeNat
    | IsZero expr', _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr
        else typecheck ctx expr' TypeNat
    | Fix _, _ ->
        let ty' = infer ctx expr in
        if neq ty' ty then Ctx.unexpected_type ty ty' expr
    | NatRec (eN, eZ, eS), _ ->
        typecheck ctx eN TypeNat;
        typecheck ctx eZ ty;
        typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)))
    | ConstTrue, _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr else ()
    | ConstFalse, _ ->
        if neq TypeBool ty then Ctx.unexpected_type ty TypeBool expr else ()
    | ConstUnit, _ ->
        if neq TypeUnit ty then Ctx.unexpected_type ty TypeUnit expr else ()
    | ConstInt _, _ ->
        if neq TypeNat ty then Ctx.unexpected_type ty TypeNat expr else ()
    | ConstMemory _, TypeRef _ -> ()
    | ConstMemory _, TypeTop -> ()
    | ConstMemory _, _ -> raise (TyExn (UnexpectedMemoryAddress (ty, expr)))
    | Var (StellaIdent name), _ -> (
        match Context.get ctx name with
        | None -> raise (TyExn (UndefinedVariable (name, expr)))
        | Some ty' -> if neq ty' ty then Ctx.unexpected_type ty ty' expr else ()
        )
    | a, _ ->
        print_endline (ShowStella.show (ShowStella.showExpr a));
        not_implemented "typecheck"

  and infer (ctx : context) (expr : AbsStella.expr) : AbsStella.typeT =
    match expr with
    | Sequence (e1, e2) ->
        typecheck ctx e1 TypeUnit;
        infer ctx e2
    | Assign (e1, e2) ->
        (match infer ctx e1 with
        | TypeRef ty' -> typecheck ctx e2 ty'
        | ty' -> raise (TyExn (NotAReference (ty', e1))));
        TypeUnit
    | If (eIf, eThen, eElse) ->
        typecheck ctx eIf TypeBool;
        let ty = infer ctx eThen in
        typecheck ctx eElse ty;
        ty
    | Let (binders, expr') ->
        (* TODO check semantics of let a = ..., b = a <- impossible in such tc *)
        let bindersCtx =
          List.map
            (fun (APatternBinding (p, expr'')) ->
              deconstruct_pattern_binder p (infer ctx expr''))
            binders
          |> Context.concat
        in
        let ctx' = Context.concat [ bindersCtx; ctx ] in
        infer ctx' expr'
    (* | LetRec of patternBinding list * expr TODO *)
    | TypeAbstraction (tys, expr) ->
        let ctx' =
          List.map (fun (StellaIdent a) -> a) tys
          |> List.fold_left Context.put_type ctx
        in
        infer ctx' expr
    | LessThan (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | LessThanOrEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | GreaterThan (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | GreaterThanOrEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | Equal (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | NotEqual (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeBool
    | TypeAsc (expr', ty) ->
        check_type ctx ty;
        typecheck ctx expr' ty;
        ty
    | Abstraction (params, expr') ->
        let ctx' = put_params ctx params in
        let tyReturn = infer ctx' expr' in
        TypeFun (List.map (fun (AParamDecl (_, ty)) -> ty) params, tyReturn)
    | Variant (ident, data) ->
        if Ctx.is_subtyping then
          TypeVariant
            [
              AVariantFieldType
                ( ident,
                  match data with
                  | SomeExprData data' -> SomeTyping (infer ctx data')
                  | NoExprData -> NoTyping );
            ]
        else raise (TyExn (AmbiguousVariantType expr))
    | Match (_, []) -> raise (TyExn (IllegalEmptyMatching expr))
    | Match (expr', AMatchCase (pat, expr'') :: cases) ->
        let ty' = infer ctx expr' in
        let tyRes =
          let ctx' =
            Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
          in
          infer ctx' expr''
        in
        List.iter
          (fun (AMatchCase (pat, expr'')) ->
            let ctx' =
              Context.concat [ deconstruct_pattern_binder pat ty'; ctx ]
            in
            typecheck ctx' expr'' tyRes)
          cases;
        let ps =
          List.map
            (fun (AMatchCase (p, _)) -> p)
            (AMatchCase (pat, expr'') :: cases)
        in
        (match check_exhaustivness ps ty' with
        | Some expr'' ->
            raise (TyExn (NonexhaustiveMatchPatterns (expr'', expr)))
        | None -> ());
        tyRes
    | List (expr' :: exprs) ->
        let ty = infer ctx expr' in
        List.iter (fun expr'' -> typecheck ctx expr'' ty) exprs;
        TypeList ty
    | List [] -> TypeList (Ctx.ambiguous (TyExn (AmbiguousList expr)))
    | Add (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | Subtract (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | LogicOr (e1, e2) ->
        typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool;
        TypeBool
    | Multiply (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | Divide (e1, e2) ->
        typecheck ctx e1 TypeNat;
        typecheck ctx e2 TypeNat;
        TypeNat
    | LogicAnd (e1, e2) ->
        typecheck ctx e1 TypeBool;
        typecheck ctx e2 TypeBool;
        TypeBool
    | Ref expr' -> TypeRef (infer ctx expr')
    | Deref expr' -> (
        match infer ctx expr' with
        | TypeRef ty' -> ty'
        | ty' -> raise (TyExn (NotAReference (ty', expr'))))
    | Application (eFun, eArgs) -> (
        (* TODO: Incorrect arity *)
        let tyFun = infer ctx eFun in
        match tyFun with
        | TypeFun (tyArgs, tyReturn) ->
            List.iter
              (fun (eArg, tyArg) -> typecheck ctx eArg tyArg)
              (List.combine eArgs tyArgs);
            tyReturn
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let fresh_args =
                List.map
                  (fun e ->
                    let ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
                    typecheck ctx e ty;
                    ty)
                  eArgs
              in
              let fresh_ret = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeFun (fresh_args, fresh_ret), tyFun) :: !Ctx.restrictions;
              fresh_ret)
            else raise (TyExn (NotAFunction (tyFun, expr)))
        | _ -> raise (TyExn (NotAFunction (tyFun, expr))))
    | TypeApplication (expr, tys) -> (
        let ty' = infer ctx expr in
        match ty' with
        | TypeForAll (tys', tyRes) ->
            let tys' = List.map (fun (StellaIdent i) -> i) tys' in
            let ty'' = apply_type tys tys' tyRes in
            ty''
        | _ -> raise (TyExn (NotAGenericFunction ty')))
    | DotRecord (expr', StellaIdent name) -> (
        let tyRec = infer ctx expr' in
        match tyRec with
        | TypeRecord fields ->
            let rec find_field (fields : recordFieldType list) =
              match fields with
              | ARecordFieldType (StellaIdent name', tyField) :: fields' ->
                  if name' = name then tyField else find_field fields'
              | [] -> raise (TyExn (UnexpectedFieldAccess (tyRec, name, expr)))
            in
            find_field fields
        | TypeVar (StellaIdent name') ->
            if String.starts_with ~prefix:"?" name' then (
              let fresh_ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                ( TypeRecord [ ARecordFieldType (StellaIdent name, fresh_ty) ],
                  tyRec )
                :: !Ctx.restrictions;
              fresh_ty)
            else raise (TyExn (NotARecord (tyRec, expr)))
        | _ -> raise (TyExn (NotARecord (tyRec, expr))))
    | DotTuple (expr, n) -> (
        let ty = infer ctx expr in
        match ty with
        | TypeTuple tyTuple ->
            if List.compare_length_with tyTuple n < 0 || n <= 0 then
              raise (TyExn (TupleIndexOutOfBounds (ty, n, expr)))
            else List.nth tyTuple (n - 1)
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let ty1 = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              let ty2 = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeTuple [ ty1; ty2 ], ty) :: !Ctx.restrictions;
              List.nth [ ty1; ty2 ] (n - 1))
            else raise (TyExn (NotATuple (ty, expr)))
        | _ -> raise (TyExn (NotATuple (ty, expr))))
    | Tuple exprs -> TypeTuple (List.map (infer ctx) exprs)
    | Record bindings ->
        let dup =
          List.map (fun (ABinding (StellaIdent name, _)) -> name) bindings
          |> find_dup
        in
        if List.compare_length_with dup 0 <> 0 then
          raise (TyExn (DuplicateRecordFields (dup, expr)))
        else
          TypeRecord
            (List.map
               (fun (ABinding (ident, expr)) ->
                 ARecordFieldType (ident, infer ctx expr))
               bindings)
    | ConsList (eHead, eTail) ->
        let ty = infer ctx eHead in
        typecheck ctx eTail (TypeList ty);
        TypeList ty
    | Head expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeList tyElem -> tyElem
        | _ -> raise (TyExn (NotAList (ty, expr))))
    | IsEmpty expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeList _ -> TypeBool
        | _ -> raise (TyExn (NotAList (ty, expr))))
    | Tail expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeList tyElem -> TypeList tyElem
        | _ -> raise (TyExn (NotAList (ty, expr))))
    | Panic -> Ctx.ambiguous (TyExn (AmbiguousPanicType expr))
    | Throw expr' ->
        let tyRes = Ctx.ambiguous (TyExn (AmbiguousThrowType expr)) in
        (match Ctx.exception_type with
        | Some ty' -> typecheck ctx expr' ty'
        | None -> raise (TyExn (ExceptionTypeNotDeclared expr)));
        tyRes
    | TryCatch (e1, pat, e2) ->
        let ty = infer ctx e1 in
        let exception_type =
          match Ctx.exception_type with
          | Some ty -> ty
          | None -> raise (TyExn (ExceptionTypeNotDeclared expr))
        in
        let ctx' =
          Context.concat [ deconstruct_pattern_binder pat exception_type ]
        in
        typecheck ctx' e2 ty;
        ty
    | TryWith (e1, e2) ->
        let ty = infer ctx e1 in
        typecheck ctx e2 ty;
        ty
    | Inl expr' ->
        let right = Ctx.ambiguous (TyExn (AmbiguousSumType expr)) in
        let left = infer ctx expr' in
        TypeSum (left, right)
    | Inr expr' ->
        let left = Ctx.ambiguous (TyExn (AmbiguousSumType expr)) in
        let right = infer ctx expr' in
        TypeSum (left, right)
    | Succ expr' ->
        typecheck ctx expr' TypeNat;
        TypeNat
    | LogicNot expr' ->
        typecheck ctx expr' TypeBool;
        TypeBool
    | Pred expr' ->
        typecheck ctx expr' TypeNat;
        TypeNat
    | IsZero expr' ->
        typecheck ctx expr' TypeNat;
        TypeBool
    | Fix expr' -> (
        let ty = infer ctx expr' in
        match ty with
        | TypeFun ([ tyArg ], tyRet) ->
            if neq tyArg tyRet || neq tyRet tyArg then
              Ctx.unexpected_type
                (TypeFun ([ tyArg ], tyArg))
                (TypeFun ([ tyArg ], tyRet))
                expr
            else tyArg
        | TypeVar (StellaIdent name) ->
            if String.starts_with ~prefix:"?" name then (
              let fresh_ty = TypeVar (StellaIdent (Ctx.fresh_var ())) in
              Ctx.restrictions :=
                (TypeFun ([ fresh_ty ], fresh_ty), ty) :: !Ctx.restrictions;
              fresh_ty)
            else raise (TyExn (NotAFunction (ty, expr)))
        | _ -> raise (TyExn (NotAFunction (ty, expr))))
    | NatRec (eN, eZ, eS) ->
        typecheck ctx eN TypeNat;
        let ty = infer ctx eZ in
        typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)));
        ty
    | ConstTrue -> TypeBool
    | ConstFalse -> TypeBool
    | ConstUnit -> TypeUnit
    | ConstInt _ -> TypeNat
    | ConstMemory _ ->
        TypeRef (Ctx.ambiguous (TyExn (AmbiguousReferenceType expr)))
    | Var (StellaIdent name) -> (
        match Context.get ctx name with
        | Some ty -> ty
        | None -> raise (TyExn (UndefinedVariable (name, expr))))
    | _ -> not_implemented "infer"
end

let typecheckProgram (AProgram (_, extensions, decls) : program) =
  let extensions' =
    List.concat_map
      (fun (AnExtension ext) -> List.map (fun (ExtensionName name) -> name) ext)
      extensions
  in
  let ambiguous =
    if List.mem "#ambiguous-type-as-bottom" extensions' then fun e -> TypeBottom
    else fun e -> raise e
  in
  let exception_type =
    if List.mem "#open-variant-exceptions" extensions' then
      let variants =
        List.concat_map
          (function
            | DeclExceptionVariant (ident, ty) ->
                [ AVariantFieldType (ident, SomeTyping ty) ]
            | _ -> [])
          decls
      in
      if List.compare_length_with variants 0 = 0 then None
      else Some (TypeVariant variants)
    else
      List.find_map
        (fun decl ->
          match decl with DeclExceptionType ty -> Some ty | _ -> None)
        decls
  in
  let is_subtyping = List.mem "#structural-subtyping" extensions' in
  let is_reconstruction = List.mem "#type-reconstruction" extensions' in
  let restrictions = ref [] in
  let eq = if is_subtyping then subtype else make_eq restrictions in
  let unexpected_type =
    if is_subtyping then fun ty1 ty2 expr ->
      raise (TyExn (UnexpectedSubtype (ty1, ty2, expr)))
    else fun ty1 ty2 expr ->
      raise (TyExn (UnexpectedTypeForExpression (ty1, ty2, expr)))
  in
  let count = ref 0 in
  let fresh_var () : string =
    count := !count + 1;
    Printf.sprintf "?T%d" !count
  in
  let module M = Make (struct
    let ambiguous = ambiguous
    let exception_type = exception_type
    let is_subtyping = is_subtyping
    let eq = eq
    let unexpected_type = unexpected_type
    let fresh_var = fresh_var
    let restrictions = restrictions
  end) in
  let typecheck = M.typecheck in
  let decls = fresh_decls fresh_var decls in
  let ctx =
    List.fold_left
      (fun a b ->
        match b with
        | DeclFun (_, StellaIdent name, params, SomeReturnType tyReturn, _, _, _)
          ->
            let tyParams =
              List.map (fun (AParamDecl (name, tyParam)) -> tyParam) params
            in
            Context.put a name (TypeFun (tyParams, tyReturn))
        | DeclFunGeneric
            (_, StellaIdent name, tyP, params, SomeReturnType tyReturn, _, _, _)
          ->
            let tyParams =
              List.map (fun (AParamDecl (name, tyParam)) -> tyParam) params
            in
            Context.put a name (TypeForAll (tyP, TypeFun (tyParams, tyReturn)))
        | DeclExceptionType _ -> a
        | DeclExceptionVariant _ -> a
        | _ -> not_implemented "typecheckProgram")
      Context.empty decls
  in
  check_main ctx;
  List.iter
    (function
      (* TODO: Add decl support *)
      | DeclFun ([], _, params, SomeReturnType tyReturn, NoThrowType, [], expr)
        ->
          let ctx' = put_params ctx params in
          check_type ctx tyReturn;
          typecheck ctx' expr tyReturn
      | DeclFunGeneric
          ([], _, tyP, params, SomeReturnType tyReturn, NoThrowType, [], expr)
        ->
          let ctx' =
            List.map (fun (StellaIdent ident) -> ident) tyP
            |> List.fold_left Context.put_type ctx
          in
          let ctx' = put_params ctx' params in
          check_type ctx' tyReturn;
          typecheck ctx' expr tyReturn
      | DeclExceptionType _ -> ()
      | DeclExceptionVariant _ -> ()
      | _ -> not_implemented "typecheckProgram")
    decls;
  if is_reconstruction then
    let sigma = M.unify !restrictions in
    ignore sigma
  else ()
