(* File generated by the BNF Converter (bnfc 2.9.5). *)

module SkelStella = struct
  open AbsStella

  type result = string

  let failure x = failwith "Undefined case." (* x discarded *)

  let rec transStellaIdent (x : stellaIdent) : result =
    match x with StellaIdent string -> failure x

  and transExtensionName (x : extensionName) : result =
    match x with ExtensionName string -> failure x

  and transMemoryAddress (x : memoryAddress) : result =
    match x with MemoryAddress string -> failure x

  and transProgram (x : program) : result =
    match x with AProgram (languagedecl, extensions, decls) -> failure x

  and transLanguageDecl (x : languageDecl) : result =
    match x with LanguageCore -> failure x

  and transExtension (x : extension) : result =
    match x with AnExtension extensionnames -> failure x

  and transDecl (x : decl) : result =
    match x with
    | DeclFun
        ( annotations,
          stellaident,
          paramdecls,
          returntype,
          throwtype,
          decls,
          expr ) ->
        failure x
    | DeclFunGeneric
        ( annotations,
          stellaident,
          stellaidents,
          paramdecls,
          returntype,
          throwtype,
          decls,
          expr ) ->
        failure x
    | DeclTypeAlias (stellaident, type') -> failure x
    | DeclExceptionType type' -> failure x
    | DeclExceptionVariant (stellaident, type') -> failure x

  and transLocalDecl (x : localDecl) : result =
    match x with ALocalDecl decl -> failure x

  and transAnnotation (x : annotation) : result =
    match x with InlineAnnotation -> failure x

  and transParamDecl (x : paramDecl) : result =
    match x with AParamDecl (stellaident, type') -> failure x

  and transReturnType (x : returnType) : result =
    match x with NoReturnType -> failure x | SomeReturnType type' -> failure x

  and transThrowType (x : throwType) : result =
    match x with NoThrowType -> failure x | SomeThrowType types -> failure x

  and transType (x : typeT) : result =
    match x with
    | TypeAuto -> failure x
    | TypeFun (types, type') -> failure x
    | TypeForAll (stellaidents, type') -> failure x
    | TypeRec (stellaident, type') -> failure x
    | TypeSum (type'0, type') -> failure x
    | TypeTuple types -> failure x
    | TypeRecord recordfieldtypes -> failure x
    | TypeVariant variantfieldtypes -> failure x
    | TypeList type' -> failure x
    | TypeBool -> failure x
    | TypeNat -> failure x
    | TypeUnit -> failure x
    | TypeTop -> failure x
    | TypeBottom -> failure x
    | TypeRef type' -> failure x
    | TypeVar stellaident -> failure x

  and transMatchCase (x : matchCase) : result =
    match x with AMatchCase (pattern, expr) -> failure x

  and transOptionalTyping (x : optionalTyping) : result =
    match x with NoTyping -> failure x | SomeTyping type' -> failure x

  and transPatternData (x : patternData) : result =
    match x with
    | NoPatternData -> failure x
    | SomePatternData pattern -> failure x

  and transExprData (x : exprData) : result =
    match x with NoExprData -> failure x | SomeExprData expr -> failure x

  and transPattern (x : pattern) : result =
    match x with
    | PatternCastAs (pattern, type') -> failure x
    | PatternAsc (pattern, type') -> failure x
    | PatternVariant (stellaident, patterndata) -> failure x
    | PatternInl pattern -> failure x
    | PatternInr pattern -> failure x
    | PatternTuple patterns -> failure x
    | PatternRecord labelledpatterns -> failure x
    | PatternList patterns -> failure x
    | PatternCons (pattern0, pattern) -> failure x
    | PatternFalse -> failure x
    | PatternTrue -> failure x
    | PatternUnit -> failure x
    | PatternInt integer -> failure x
    | PatternSucc pattern -> failure x
    | PatternVar stellaident -> failure x

  and transLabelledPattern (x : labelledPattern) : result =
    match x with ALabelledPattern (stellaident, pattern) -> failure x

  and transBinding (x : binding) : result =
    match x with ABinding (stellaident, expr) -> failure x

  and transExpr (x : expr) : result =
    match x with
    | Sequence (expr0, expr) -> failure x
    | Assign (expr0, expr) -> failure x
    | If (expr0, expr1, expr) -> failure x
    | Let (patternbindings, expr) -> failure x
    | LetRec (patternbindings, expr) -> failure x
    | TypeAbstraction (stellaidents, expr) -> failure x
    | LessThan (expr0, expr) -> failure x
    | LessThanOrEqual (expr0, expr) -> failure x
    | GreaterThan (expr0, expr) -> failure x
    | GreaterThanOrEqual (expr0, expr) -> failure x
    | Equal (expr0, expr) -> failure x
    | NotEqual (expr0, expr) -> failure x
    | TypeAsc (expr, type') -> failure x
    | TypeCast (expr, type') -> failure x
    | Abstraction (paramdecls, expr) -> failure x
    | Variant (stellaident, exprdata) -> failure x
    | Match (expr, matchcases) -> failure x
    | List exprs -> failure x
    | Add (expr0, expr) -> failure x
    | Subtract (expr0, expr) -> failure x
    | LogicOr (expr0, expr) -> failure x
    | Multiply (expr0, expr) -> failure x
    | Divide (expr0, expr) -> failure x
    | LogicAnd (expr0, expr) -> failure x
    | Ref expr -> failure x
    | Deref expr -> failure x
    | Application (expr, exprs) -> failure x
    | TypeApplication (expr, types) -> failure x
    | DotRecord (expr, stellaident) -> failure x
    | DotTuple (expr, integer) -> failure x
    | Tuple exprs -> failure x
    | Record bindings -> failure x
    | ConsList (expr0, expr) -> failure x
    | Head expr -> failure x
    | IsEmpty expr -> failure x
    | Tail expr -> failure x
    | Panic -> failure x
    | Throw expr -> failure x
    | TryCatch (expr0, pattern, expr) -> failure x
    | TryWith (expr0, expr) -> failure x
    | TryCastAs (expr0, type', pattern, expr1, expr) -> failure x
    | Inl expr -> failure x
    | Inr expr -> failure x
    | Succ expr -> failure x
    | LogicNot expr -> failure x
    | Pred expr -> failure x
    | IsZero expr -> failure x
    | Fix expr -> failure x
    | NatRec (expr0, expr1, expr) -> failure x
    | Fold (type', expr) -> failure x
    | Unfold (type', expr) -> failure x
    | ConstTrue -> failure x
    | ConstFalse -> failure x
    | ConstUnit -> failure x
    | ConstInt integer -> failure x
    | ConstMemory memoryaddress -> failure x
    | Var stellaident -> failure x

  and transPatternBinding (x : patternBinding) : result =
    match x with APatternBinding (pattern, expr) -> failure x

  and transVariantFieldType (x : variantFieldType) : result =
    match x with AVariantFieldType (stellaident, optionaltyping) -> failure x

  and transRecordFieldType (x : recordFieldType) : result =
    match x with ARecordFieldType (stellaident, type') -> failure x

  and transTyping (x : typing) : result =
    match x with ATyping (expr, type') -> failure x
end
