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

let not_implemented () = raise (Failure "Not implemented")

let showError (err : tyError) : string =
  match err with
  | MissingMain ->
      "ERROR_MISSING_MAIN\n  в программе отсутствует функция main"
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

let rec typecheck (ctx : context) (expr : expr) (ty : typeT) =
  match (expr, ty) with
  | Sequence (e1, e2), _ ->
      typecheck ctx e1 TypeUnit;
      typecheck ctx e2 ty
  (* | Assign of expr * expr *)
  | If (eIf, eThen, eElse), _ ->
      typecheck ctx eIf TypeBool;
      typecheck ctx eThen ty;
      typecheck ctx eElse ty
  (* Let, LetRec *)
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
  (* Equal, NotEqual (requires infer) *)
  | TypeAsc (e1, ty'), _ ->
      if ty != ty then
        raise (TyExn (UnexpectedTypeOfExpression (ty, ty', expr)))
      else typecheck ctx e1 ty'
  (* TypeCast *)
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
  (* Variant, Match, List *)
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
  (* Ref, deref *)
  (* | Application, DotRecord, DotTuple requires infer *)
  | Tuple exprs, TypeTuple tyExprs ->
      if List.compare_lengths exprs tyExprs != 0 then () (* TODO: Error *)
      else
        List.fold_left
          (fun _ (expr, ty) -> typecheck ctx expr ty)
          ()
          (List.combine exprs tyExprs)
  | Tuple _, _ -> raise (TyExn (UnexpectedTuple (ty, expr)))
  (* TODO *)
  (* | Record bindings, TypeRecord tyFields -> ()
  | Record _, _ -> raise (TyExn (UnexpectedRecord (ty, expr))) *)
  | ConsList (e1, e2), TypeList ty' ->
      typecheck ctx e1 ty';
      typecheck ctx e2 ty
  | ConsList _, _ -> raise (TyExn (UnexpectedList (ty, expr)))
  (* | Head expr', TypeList ty' -> ()
  | Head _, _ -> raise (TyExn (NotAList (ty, expr))) *)
  (* Head, Tail, IsEmpty requires infer *)
  (* Panic, throw, trycatch, trywith *)
  | Inl expr', TypeSum (tyL, _) -> typecheck ctx expr' tyL
  | Inl _, _ -> () (* TODO *)
  | Inr expr', TypeSum (_, tyR) -> typecheck ctx expr' tyR
  | Inr _, _ -> () (* TODO *)
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
  (* Fold, unfold *)
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
  (* ConstMemory *)
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

(*
let infer (expr : AbsStella.expr) : AbsStella.typeT =
  Printf.printf "typechecker is not implemented\n"
*)
