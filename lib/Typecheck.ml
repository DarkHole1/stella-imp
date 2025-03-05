open AbsStella

type tyError =
  | MissingMain
  | UndefinedVariable of string * expr
  | UnexpectedTypeOfExpression of typeT * typeT * expr
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
  | UnexpectedVariantLabel
  | TupleIndexOutOfBounds of typeT * int * expr
  | UnexpectedTupleLength
  | AmbiguousSumType of expr
  | AmbiguousVariantType of expr
  | AmbiguousList of expr
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
  | MissingMain -> "ERROR_MISSING_MAIN\n  в программе отсутствует функция main"
  | UndefinedVariable (name, expr) ->
      "ERROR_UNDEFINED_VARIABLE\n  неизвестная переменная\n    " ^ name
      ^ "\n  в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | UnexpectedTypeOfExpression (ty1, ty2, expr) ->
      "ERROR_UNEXPECTED_TYPE_OF_EXPRESSION\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty1
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty2
      ^ "\n  в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | NotAFunction (ty, expr) ->
      "ERROR_NOT_A_FUNCTION\n  ожидалась функция в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
  | NotATuple (ty, expr) ->
      "ERROR_NOT_A_TUPLE\n  ожидался кортёж в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
  | NotARecord (ty, expr) ->
      "ERROR_NOT_A_RECORD\n  ожидалась запись в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
  | NotAList (ty, expr) ->
      "ERROR_NOT_A_LIST\n  ожидался список в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
  | UnexpectedLambda (ty, expr) ->
      "ERROR_UNEXPECTED_LAMBDA\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
      ^ "\n  но получена лямбда в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | UnexpectedTypeForParameter (ty1, ty2, AParamDecl (StellaIdent name, _)) ->
      "ERROR_UNEXPECTED_TYPE_FOR_PARAMETER\n  для параметра\n    " ^ name
      ^ "\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty1
      ^ "\n  но получен тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty2
  | UnexpectedTuple (ty, expr) ->
      "ERROR_UNEXPECTED_TUPLE\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
      ^ "\n  но получен кортёж в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | UnexpectedRecord (ty, expr) ->
      "ERROR_UNEXPECTED_RECORD\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
      ^ "\n  но получена запись в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | UnexpectedVariant (ty, expr) ->
      "ERROR_UNEXPECTED_VARIANT\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
      ^ "\n  но получен вариант в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | UnexpectedList (ty, expr) ->
      "ERROR_UNEXPECTED_LIST\n  ожидался тип\n    "
      ^ PrintStella.printTree PrintStella.prtTypeT ty
      ^ "\n  но получен список в выражении\n    "
      ^ PrintStella.printTree PrintStella.prtExpr expr
  | _ -> not_implemented ()

type context = (string * typeT) list

let put (ctx : context) (s : string) (ty : typeT) : context = (s, ty) :: ctx

let put_params (ctx : context) (params : paramDecl list) : context =
  List.concat
    [
      List.map (fun (AParamDecl (StellaIdent name, ty)) -> (name, ty)) params;
      ctx;
    ]

let rec get (ctx : context) (s : string) : typeT option =
  match ctx with
  | (s', ty) :: ctx' -> if s = s' then Some ty else get ctx' s
  | _ -> None

let checkMain (ctx : context) : unit =
  match get ctx "main" with None -> raise (TyExn MissingMain) | _ -> ()

let dePatternBinder (p : pattern) (ty : typeT) : context =
  match p with
  | PatternVar (StellaIdent name) -> [ (name, ty) ]
  | _ -> not_implemented ()

let rec typecheck (ctx : context) (expr : expr) (ty : typeT) =
  match (expr, ty) with
  | Sequence (e1, e2), _ ->
      typecheck ctx e1 TypeUnit;
      typecheck ctx e2 ty
  | If (eIf, eThen, eElse), _ ->
      typecheck ctx eIf TypeBool;
      typecheck ctx eThen ty;
      typecheck ctx eElse ty
  | Let (binders, expr'), _ ->
      (* TODO: check semantics *)
      let bindersCtx =
        List.concat_map
          (fun (APatternBinding (p, expr'')) ->
            dePatternBinder p (infer ctx expr''))
          binders
      in
      let ctx' = List.concat [ bindersCtx; ctx ] in
      typecheck ctx' expr' ty
  (* LetRec TODO *)
  | LessThan (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | LessThan (e1, e2), _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | LessThanOrEqual (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | LessThanOrEqual (e1, e2), _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | GreaterThan (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | GreaterThan (e1, e2), _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | GreaterThanOrEqual (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | GreaterThanOrEqual (e1, e2), _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | Equal (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | Equal _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | NotEqual (e1, e2), TypeBool ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | NotEqual _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | TypeAsc (e1, ty'), _ ->
      if ty != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else typecheck ctx e1 ty'
  | Abstraction (params, expr'), TypeFun (tyParams, tyReturn) ->
      (* Check arity *)
      (* List.compare_lengths tyParams params = 0 *)
      List.fold_left
        (fun _ (ty1, AParamDecl (ident, ty2)) ->
          if ty1 != ty2 then
            raise
              (TyExn
                 (UnexpectedTypeForParameter (ty1, ty2, AParamDecl (ident, ty2))))
          else ())
        ()
        (List.combine tyParams params);
      let ctx' = put_params ctx params in
      typecheck ctx' expr' tyReturn
  | Abstraction _, _ -> raise (TyExn (UnexpectedLambda (ty, expr)))
  | Variant _, TypeVariant _ ->
      (* TODO: Not infer, check *)
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  (* Match TODO *)
  | List _, TypeList _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | Add (e1, e2), TypeNat ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | Add _, _ -> raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | Subtract (e1, e2), TypeNat ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | Subtract _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | LogicOr (e1, e2), TypeBool ->
      typecheck ctx e1 TypeBool;
      typecheck ctx e2 TypeBool
  | LogicOr _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | Multiply (e1, e2), TypeNat ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | Multiply _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | Divide (e1, e2), TypeNat ->
      typecheck ctx e1 TypeNat;
      typecheck ctx e2 TypeNat
  | Divide _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | LogicAnd (e1, e2), TypeBool ->
      typecheck ctx e1 TypeBool;
      typecheck ctx e2 TypeBool
  | LogicAnd _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | Application _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | DotRecord _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | DotTuple _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | Tuple exprs, TypeTuple tyExprs ->
      if List.compare_lengths exprs tyExprs != 0 then () (* TODO: Error *)
      else
        List.fold_left
          (fun _ (expr, ty) -> typecheck ctx expr ty)
          ()
          (List.combine exprs tyExprs)
  | Tuple _, _ -> raise (TyExn (UnexpectedTuple (ty, expr)))
  | Record _, TypeRecord _ ->
      (* TODO missing / unexpected record fields *)
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | Record _, _ -> raise (TyExn (UnexpectedRecord (ty, expr)))
  | ConsList (e1, e2), TypeList ty' ->
      typecheck ctx e1 ty';
      typecheck ctx e2 ty
  | ConsList _, _ -> raise (TyExn (UnexpectedList (ty, expr)))
  | Head _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | Tail _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | IsEmpty _, _ ->
      let ty' = infer ctx expr in
      if ty' != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else ()
  | Inl expr', TypeSum (tyL, _) -> typecheck ctx expr' tyL
  | Inl _, _ -> raise (TyExn (UnexpectedInjection (ty, expr)))
  | Inr expr', TypeSum (_, tyR) -> typecheck ctx expr' tyR
  | Inr _, _ -> raise (TyExn (UnexpectedInjection (ty, expr)))
  | Succ expr', TypeNat -> typecheck ctx expr' TypeNat
  | Succ _, _ -> raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | LogicNot expr', TypeBool -> typecheck ctx expr' TypeBool
  | LogicNot _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | Pred expr', TypeNat -> typecheck ctx expr' TypeNat
  | Pred _, _ -> raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | IsZero expr', TypeNat -> typecheck ctx expr' TypeNat
  | IsZero _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | Fix expr', _ -> typecheck ctx expr' (TypeFun ([ ty ], ty))
  | NatRec (eN, eZ, eS), _ ->
      typecheck ctx eN TypeNat;
      typecheck ctx eN ty;
      typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)))
  | ConstTrue, TypeBool -> ()
  | ConstTrue, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | ConstFalse, TypeBool -> ()
  | ConstFalse, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeBool, expr)))
  | ConstUnit, TypeUnit -> ()
  | ConstUnit, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeUnit, expr)))
  | ConstInt _, TypeNat -> ()
  | ConstInt _, _ ->
      raise (TyExn (UnexpectedTypeOfExpression (ty, TypeNat, expr)))
  | Var (StellaIdent name), _ -> (
      match get ctx name with
      | None -> raise (TyExn (UndefinedVariable (name, expr)))
      | Some ty' ->
          if ty != ty' then
            raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
          else ())
  | a, _ ->
      print_endline (ShowStella.show (ShowStella.showExpr a));
      not_implemented ()

and infer (ctx : context) (expr : AbsStella.expr) : AbsStella.typeT =
  match expr with
  | Sequence (e1, e2) ->
      typecheck ctx e1 TypeUnit;
      infer ctx e2
  | If (eIf, eThen, eElse) ->
      typecheck ctx eIf TypeBool;
      let ty = infer ctx eThen in
      typecheck ctx eElse ty;
      ty
  | Let (binders, expr') ->
      (* TODO check semantics of let a = ..., b = a <- impossible in such tc *)
      let bindersCtx =
        List.concat_map
          (fun (APatternBinding (p, expr'')) ->
            dePatternBinder p (infer ctx expr''))
          binders
      in
      let ctx' = List.concat [ bindersCtx; ctx ] in
      infer ctx' expr'
  (* | LetRec of patternBinding list * expr TODO *)
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
      typecheck ctx expr' ty;
      ty
  | Abstraction (params, expr') ->
      let ctx' = put_params ctx params in
      let tyReturn = infer ctx' expr' in
      TypeFun (List.map (fun (AParamDecl (_, ty)) -> ty) params, tyReturn)
  | Variant _ -> raise (TyExn (AmbiguousVariantType expr))
  (* | Match of expr * matchCase list TODO: PM is hard *)
  | List (expr' :: exprs) ->
      let ty = infer ctx expr' in
      List.iter (fun expr'' -> typecheck ctx expr'' ty) exprs;
      ty
  | List [] -> raise (TyExn (AmbiguousList expr))
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
  | Application (eFun, eArgs) -> (
      (* TODO: Incorrect arity *)
      let tyFun = infer ctx eFun in
      match tyFun with
      | TypeFun (tyArgs, tyReturn) ->
          List.iter
            (fun (eArg, tyArg) -> typecheck ctx eArg tyArg)
            (List.combine eArgs tyArgs);
          tyReturn
      | _ -> raise (TyExn (NotAFunction (tyFun, expr))))
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
      | _ -> raise (TyExn (NotARecord (tyRec, expr))))
  | DotTuple (expr, n) -> (
      let ty = infer ctx expr in
      match ty with
      | TypeTuple tyTuple ->
          if List.compare_length_with tyTuple n > 0 || n <= 0 then
            raise (TyExn (TupleIndexOutOfBounds (ty, n, expr)))
          else List.nth tyTuple (n + 1)
      | _ -> raise (TyExn (NotATuple (ty, expr))))
  | Tuple exprs -> TypeTuple (List.map (infer ctx) exprs)
  | Record bindings ->
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
  | Inl _ -> raise (TyExn (AmbiguousSumType expr))
  | Inr _ -> raise (TyExn (AmbiguousSumType expr))
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
          if tyArg != tyRet then
            raise
              (TyExn
                 (UnexpectedTypeOfExpression
                    ( TypeFun ([ tyArg ], tyArg),
                      TypeFun ([ tyArg ], tyRet),
                      expr )))
          else ty
      | _ -> raise (TyExn (NotAFunction (ty, expr))))
  | NatRec (eN, eZ, eS) ->
      typecheck ctx eN TypeNat;
      let ty = infer ctx eN in
      typecheck ctx eS (TypeFun ([ TypeNat ], TypeFun ([ ty ], ty)));
      ty
  | ConstTrue -> TypeBool
  | ConstFalse -> TypeBool
  | ConstUnit -> TypeUnit
  | ConstInt _ -> TypeNat
  | Var (StellaIdent name) -> (
      match get ctx name with
      | Some ty -> ty
      | None -> raise (TyExn (UndefinedVariable (name, expr))))
  | _ -> not_implemented ()

let typecheckProgram (program : program) =
  match program with
  | AProgram (_, _, decls) ->
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
            | _ -> not_implemented ())
          [] decls
      in
      checkMain ctx;
      List.fold_left
        (fun _ decl ->
          match decl with
          (* TODO: Add decl support *)
          | DeclFun
              ([], _, params, SomeReturnType tyReturn, NoThrowType, [], expr) ->
              let ctx' = put_params ctx params in
              typecheck ctx' expr tyReturn
          | _ -> not_implemented ())
        () decls
