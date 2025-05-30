(* File generated by the BNF Converter (bnfc 2.9.5). *)

(* show functions *)

(* use string buffers for efficient string concatenations *)
type showable = Buffer.t -> unit

let show (s : showable) : string =
  let init_size = 16 in
  (* you may want to adjust this *)
  let b = Buffer.create init_size in
  s b;
  Buffer.contents b

let emptyS : showable = fun buf -> ()
let c2s (c : char) : showable = fun buf -> Buffer.add_char buf c
let s2s (s : string) : showable = fun buf -> Buffer.add_string buf s

let ( >> ) (s1 : showable) (s2 : showable) : showable =
 fun buf ->
  s1 buf;
  s2 buf

let showChar (c : char) : showable =
 fun buf -> Buffer.add_string buf ("'" ^ Char.escaped c ^ "'")

let showString (s : string) : showable =
 fun buf -> Buffer.add_string buf ("\"" ^ String.escaped s ^ "\"")

let showList (showFun : 'a -> showable) (xs : 'a list) : showable =
 fun buf ->
  let rec f ys =
    match ys with
    | [] -> ()
    | [ y ] -> showFun y buf
    | y :: ys ->
        showFun y buf;
        Buffer.add_string buf "; ";
        f ys
  in
  Buffer.add_char buf '[';
  f xs;
  Buffer.add_char buf ']'

let showInt (i : int) : showable = s2s (string_of_int i)
let showFloat (f : float) : showable = s2s (string_of_float f)

let rec showStellaIdent (AbsStella.StellaIdent i) : showable =
  s2s "StellaIdent " >> showString i

let rec showExtensionName (AbsStella.ExtensionName i) : showable =
  s2s "ExtensionName " >> showString i

let rec showMemoryAddress (AbsStella.MemoryAddress i) : showable =
  s2s "MemoryAddress " >> showString i

let rec showProgram (e : AbsStella.program) : showable =
  match e with
  | AbsStella.AProgram (languagedecl, extensions, decls) ->
      s2s "AProgram" >> c2s ' ' >> c2s '('
      >> showLanguageDecl languagedecl
      >> s2s ", "
      >> showList showExtension extensions
      >> s2s ", " >> showList showDecl decls >> c2s ')'

and showLanguageDecl (e : AbsStella.languageDecl) : showable =
  match e with AbsStella.LanguageCore -> s2s "LanguageCore"

and showExtension (e : AbsStella.extension) : showable =
  match e with
  | AbsStella.AnExtension extensionnames ->
      s2s "AnExtension" >> c2s ' ' >> c2s '('
      >> showList showExtensionName extensionnames
      >> c2s ')'

and showDecl (e : AbsStella.decl) : showable =
  match e with
  | AbsStella.DeclFun
      (annotations, stellaident, paramdecls, returntype, throwtype, decls, expr)
    ->
      s2s "DeclFun" >> c2s ' ' >> c2s '('
      >> showList showAnnotation annotations
      >> s2s ", "
      >> showStellaIdent stellaident
      >> s2s ", "
      >> showList showParamDecl paramdecls
      >> s2s ", " >> showReturnType returntype >> s2s ", "
      >> showThrowType throwtype >> s2s ", " >> showList showDecl decls
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.DeclFunGeneric
      ( annotations,
        stellaident,
        stellaidents,
        paramdecls,
        returntype,
        throwtype,
        decls,
        expr ) ->
      s2s "DeclFunGeneric" >> c2s ' ' >> c2s '('
      >> showList showAnnotation annotations
      >> s2s ", "
      >> showStellaIdent stellaident
      >> s2s ", "
      >> showList showStellaIdent stellaidents
      >> s2s ", "
      >> showList showParamDecl paramdecls
      >> s2s ", " >> showReturnType returntype >> s2s ", "
      >> showThrowType throwtype >> s2s ", " >> showList showDecl decls
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.DeclTypeAlias (stellaident, type') ->
      s2s "DeclTypeAlias" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showTypeT type' >> c2s ')'
  | AbsStella.DeclExceptionType type' ->
      s2s "DeclExceptionType" >> c2s ' ' >> c2s '(' >> showTypeT type'
      >> c2s ')'
  | AbsStella.DeclExceptionVariant (stellaident, type') ->
      s2s "DeclExceptionVariant" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showTypeT type' >> c2s ')'

and showLocalDecl (e : AbsStella.localDecl) : showable =
  match e with
  | AbsStella.ALocalDecl decl ->
      s2s "ALocalDecl" >> c2s ' ' >> c2s '(' >> showDecl decl >> c2s ')'

and showAnnotation (e : AbsStella.annotation) : showable =
  match e with AbsStella.InlineAnnotation -> s2s "InlineAnnotation"

and showParamDecl (e : AbsStella.paramDecl) : showable =
  match e with
  | AbsStella.AParamDecl (stellaident, type') ->
      s2s "AParamDecl" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showTypeT type' >> c2s ')'

and showReturnType (e : AbsStella.returnType) : showable =
  match e with
  | AbsStella.NoReturnType -> s2s "NoReturnType"
  | AbsStella.SomeReturnType type' ->
      s2s "SomeReturnType" >> c2s ' ' >> c2s '(' >> showTypeT type' >> c2s ')'

and showThrowType (e : AbsStella.throwType) : showable =
  match e with
  | AbsStella.NoThrowType -> s2s "NoThrowType"
  | AbsStella.SomeThrowType types ->
      s2s "SomeThrowType" >> c2s ' ' >> c2s '(' >> showList showTypeT types
      >> c2s ')'

and showTypeT (e : AbsStella.typeT) : showable =
  match e with
  | AbsStella.TypeAuto -> s2s "TypeAuto"
  | AbsStella.TypeFun (types, type') ->
      s2s "TypeFun" >> c2s ' ' >> c2s '(' >> showList showTypeT types
      >> s2s ", " >> showTypeT type' >> c2s ')'
  | AbsStella.TypeForAll (stellaidents, type') ->
      s2s "TypeForAll" >> c2s ' ' >> c2s '('
      >> showList showStellaIdent stellaidents
      >> s2s ", " >> showTypeT type' >> c2s ')'
  | AbsStella.TypeRec (stellaident, type') ->
      s2s "TypeRec" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showTypeT type' >> c2s ')'
  | AbsStella.TypeSum (type'0, type') ->
      s2s "TypeSum" >> c2s ' ' >> c2s '(' >> showTypeT type'0 >> s2s ", "
      >> showTypeT type' >> c2s ')'
  | AbsStella.TypeTuple types ->
      s2s "TypeTuple" >> c2s ' ' >> c2s '(' >> showList showTypeT types
      >> c2s ')'
  | AbsStella.TypeRecord recordfieldtypes ->
      s2s "TypeRecord" >> c2s ' ' >> c2s '('
      >> showList showRecordFieldType recordfieldtypes
      >> c2s ')'
  | AbsStella.TypeVariant variantfieldtypes ->
      s2s "TypeVariant" >> c2s ' ' >> c2s '('
      >> showList showVariantFieldType variantfieldtypes
      >> c2s ')'
  | AbsStella.TypeList type' ->
      s2s "TypeList" >> c2s ' ' >> c2s '(' >> showTypeT type' >> c2s ')'
  | AbsStella.TypeBool -> s2s "TypeBool"
  | AbsStella.TypeNat -> s2s "TypeNat"
  | AbsStella.TypeUnit -> s2s "TypeUnit"
  | AbsStella.TypeTop -> s2s "TypeTop"
  | AbsStella.TypeBottom -> s2s "TypeBottom"
  | AbsStella.TypeRef type' ->
      s2s "TypeRef" >> c2s ' ' >> c2s '(' >> showTypeT type' >> c2s ')'
  | AbsStella.TypeVar stellaident ->
      s2s "TypeVar" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> c2s ')'

and showMatchCase (e : AbsStella.matchCase) : showable =
  match e with
  | AbsStella.AMatchCase (pattern, expr) ->
      s2s "AMatchCase" >> c2s ' ' >> c2s '(' >> showPattern pattern >> s2s ", "
      >> showExpr expr >> c2s ')'

and showOptionalTyping (e : AbsStella.optionalTyping) : showable =
  match e with
  | AbsStella.NoTyping -> s2s "NoTyping"
  | AbsStella.SomeTyping type' ->
      s2s "SomeTyping" >> c2s ' ' >> c2s '(' >> showTypeT type' >> c2s ')'

and showPatternData (e : AbsStella.patternData) : showable =
  match e with
  | AbsStella.NoPatternData -> s2s "NoPatternData"
  | AbsStella.SomePatternData pattern ->
      s2s "SomePatternData" >> c2s ' ' >> c2s '(' >> showPattern pattern
      >> c2s ')'

and showExprData (e : AbsStella.exprData) : showable =
  match e with
  | AbsStella.NoExprData -> s2s "NoExprData"
  | AbsStella.SomeExprData expr ->
      s2s "SomeExprData" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'

and showPattern (e : AbsStella.pattern) : showable =
  match e with
  | AbsStella.PatternCastAs (pattern, type') ->
      s2s "PatternCastAs" >> c2s ' ' >> c2s '(' >> showPattern pattern
      >> s2s ", " >> showTypeT type' >> c2s ')'
  | AbsStella.PatternAsc (pattern, type') ->
      s2s "PatternAsc" >> c2s ' ' >> c2s '(' >> showPattern pattern >> s2s ", "
      >> showTypeT type' >> c2s ')'
  | AbsStella.PatternVariant (stellaident, patterndata) ->
      s2s "PatternVariant" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", "
      >> showPatternData patterndata
      >> c2s ')'
  | AbsStella.PatternInl pattern ->
      s2s "PatternInl" >> c2s ' ' >> c2s '(' >> showPattern pattern >> c2s ')'
  | AbsStella.PatternInr pattern ->
      s2s "PatternInr" >> c2s ' ' >> c2s '(' >> showPattern pattern >> c2s ')'
  | AbsStella.PatternTuple patterns ->
      s2s "PatternTuple" >> c2s ' ' >> c2s '('
      >> showList showPattern patterns
      >> c2s ')'
  | AbsStella.PatternRecord labelledpatterns ->
      s2s "PatternRecord" >> c2s ' ' >> c2s '('
      >> showList showLabelledPattern labelledpatterns
      >> c2s ')'
  | AbsStella.PatternList patterns ->
      s2s "PatternList" >> c2s ' ' >> c2s '('
      >> showList showPattern patterns
      >> c2s ')'
  | AbsStella.PatternCons (pattern0, pattern) ->
      s2s "PatternCons" >> c2s ' ' >> c2s '(' >> showPattern pattern0
      >> s2s ", " >> showPattern pattern >> c2s ')'
  | AbsStella.PatternFalse -> s2s "PatternFalse"
  | AbsStella.PatternTrue -> s2s "PatternTrue"
  | AbsStella.PatternUnit -> s2s "PatternUnit"
  | AbsStella.PatternInt integer ->
      s2s "PatternInt" >> c2s ' ' >> c2s '(' >> showInt integer >> c2s ')'
  | AbsStella.PatternSucc pattern ->
      s2s "PatternSucc" >> c2s ' ' >> c2s '(' >> showPattern pattern >> c2s ')'
  | AbsStella.PatternVar stellaident ->
      s2s "PatternVar" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> c2s ')'

and showLabelledPattern (e : AbsStella.labelledPattern) : showable =
  match e with
  | AbsStella.ALabelledPattern (stellaident, pattern) ->
      s2s "ALabelledPattern" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showPattern pattern >> c2s ')'

and showBinding (e : AbsStella.binding) : showable =
  match e with
  | AbsStella.ABinding (stellaident, expr) ->
      s2s "ABinding" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showExpr expr >> c2s ')'

and showExpr (e : AbsStella.expr) : showable =
  match e with
  | AbsStella.Sequence (expr0, expr) ->
      s2s "Sequence" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Assign (expr0, expr) ->
      s2s "Assign" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.If (expr0, expr1, expr) ->
      s2s "If" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr1 >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.Let (patternbindings, expr) ->
      s2s "Let" >> c2s ' ' >> c2s '('
      >> showList showPatternBinding patternbindings
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.LetRec (patternbindings, expr) ->
      s2s "LetRec" >> c2s ' ' >> c2s '('
      >> showList showPatternBinding patternbindings
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.TypeAbstraction (stellaidents, expr) ->
      s2s "TypeAbstraction" >> c2s ' ' >> c2s '('
      >> showList showStellaIdent stellaidents
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.LessThan (expr0, expr) ->
      s2s "LessThan" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.LessThanOrEqual (expr0, expr) ->
      s2s "LessThanOrEqual" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.GreaterThan (expr0, expr) ->
      s2s "GreaterThan" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.GreaterThanOrEqual (expr0, expr) ->
      s2s "GreaterThanOrEqual" >> c2s ' ' >> c2s '(' >> showExpr expr0
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.Equal (expr0, expr) ->
      s2s "Equal" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.NotEqual (expr0, expr) ->
      s2s "NotEqual" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.TypeAsc (expr, type') ->
      s2s "TypeAsc" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showTypeT type' >> c2s ')'
  | AbsStella.TypeCast (expr, type') ->
      s2s "TypeCast" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showTypeT type' >> c2s ')'
  | AbsStella.Abstraction (paramdecls, expr) ->
      s2s "Abstraction" >> c2s ' ' >> c2s '('
      >> showList showParamDecl paramdecls
      >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.Variant (stellaident, exprdata) ->
      s2s "Variant" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showExprData exprdata >> c2s ')'
  | AbsStella.Match (expr, matchcases) ->
      s2s "Match" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showList showMatchCase matchcases
      >> c2s ')'
  | AbsStella.List exprs ->
      s2s "List" >> c2s ' ' >> c2s '(' >> showList showExpr exprs >> c2s ')'
  | AbsStella.Add (expr0, expr) ->
      s2s "Add" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Subtract (expr0, expr) ->
      s2s "Subtract" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.LogicOr (expr0, expr) ->
      s2s "LogicOr" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Multiply (expr0, expr) ->
      s2s "Multiply" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Divide (expr0, expr) ->
      s2s "Divide" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.LogicAnd (expr0, expr) ->
      s2s "LogicAnd" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Ref expr ->
      s2s "Ref" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Deref expr ->
      s2s "Deref" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Application (expr, exprs) ->
      s2s "Application" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showList showExpr exprs >> c2s ')'
  | AbsStella.TypeApplication (expr, types) ->
      s2s "TypeApplication" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showList showTypeT types >> c2s ')'
  | AbsStella.DotRecord (expr, stellaident) ->
      s2s "DotRecord" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showStellaIdent stellaident
      >> c2s ')'
  | AbsStella.DotTuple (expr, integer) ->
      s2s "DotTuple" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showInt integer >> c2s ')'
  | AbsStella.Tuple exprs ->
      s2s "Tuple" >> c2s ' ' >> c2s '(' >> showList showExpr exprs >> c2s ')'
  | AbsStella.Record bindings ->
      s2s "Record" >> c2s ' ' >> c2s '('
      >> showList showBinding bindings
      >> c2s ')'
  | AbsStella.ConsList (expr0, expr) ->
      s2s "ConsList" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Head expr ->
      s2s "Head" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.IsEmpty expr ->
      s2s "IsEmpty" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Tail expr ->
      s2s "Tail" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Panic -> s2s "Panic"
  | AbsStella.Throw expr ->
      s2s "Throw" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.TryCatch (expr0, pattern, expr) ->
      s2s "TryCatch" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showPattern pattern >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.TryWith (expr0, expr) ->
      s2s "TryWith" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.TryCastAs (expr0, type', pattern, expr1, expr) ->
      s2s "TryCastAs" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showTypeT type' >> s2s ", " >> showPattern pattern >> s2s ", "
      >> showExpr expr1 >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.Inl expr ->
      s2s "Inl" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Inr expr ->
      s2s "Inr" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Succ expr ->
      s2s "Succ" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.LogicNot expr ->
      s2s "LogicNot" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Pred expr ->
      s2s "Pred" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.IsZero expr ->
      s2s "IsZero" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.Fix expr ->
      s2s "Fix" >> c2s ' ' >> c2s '(' >> showExpr expr >> c2s ')'
  | AbsStella.NatRec (expr0, expr1, expr) ->
      s2s "NatRec" >> c2s ' ' >> c2s '(' >> showExpr expr0 >> s2s ", "
      >> showExpr expr1 >> s2s ", " >> showExpr expr >> c2s ')'
  | AbsStella.Fold (type', expr) ->
      s2s "Fold" >> c2s ' ' >> c2s '(' >> showTypeT type' >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.Unfold (type', expr) ->
      s2s "Unfold" >> c2s ' ' >> c2s '(' >> showTypeT type' >> s2s ", "
      >> showExpr expr >> c2s ')'
  | AbsStella.ConstTrue -> s2s "ConstTrue"
  | AbsStella.ConstFalse -> s2s "ConstFalse"
  | AbsStella.ConstUnit -> s2s "ConstUnit"
  | AbsStella.ConstInt integer ->
      s2s "ConstInt" >> c2s ' ' >> c2s '(' >> showInt integer >> c2s ')'
  | AbsStella.ConstMemory memoryaddress ->
      s2s "ConstMemory" >> c2s ' ' >> c2s '('
      >> showMemoryAddress memoryaddress
      >> c2s ')'
  | AbsStella.Var stellaident ->
      s2s "Var" >> c2s ' ' >> c2s '(' >> showStellaIdent stellaident >> c2s ')'

and showPatternBinding (e : AbsStella.patternBinding) : showable =
  match e with
  | AbsStella.APatternBinding (pattern, expr) ->
      s2s "APatternBinding" >> c2s ' ' >> c2s '(' >> showPattern pattern
      >> s2s ", " >> showExpr expr >> c2s ')'

and showVariantFieldType (e : AbsStella.variantFieldType) : showable =
  match e with
  | AbsStella.AVariantFieldType (stellaident, optionaltyping) ->
      s2s "AVariantFieldType" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", "
      >> showOptionalTyping optionaltyping
      >> c2s ')'

and showRecordFieldType (e : AbsStella.recordFieldType) : showable =
  match e with
  | AbsStella.ARecordFieldType (stellaident, type') ->
      s2s "ARecordFieldType" >> c2s ' ' >> c2s '('
      >> showStellaIdent stellaident
      >> s2s ", " >> showTypeT type' >> c2s ')'

and showTyping (e : AbsStella.typing) : showable =
  match e with
  | AbsStella.ATyping (expr, type') ->
      s2s "ATyping" >> c2s ' ' >> c2s '(' >> showExpr expr >> s2s ", "
      >> showTypeT type' >> c2s ')'
