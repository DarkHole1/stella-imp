(* File generated by the BNF Converter (bnfc 2.9.5). *)

(* pretty-printer *)

open Printf

(* We use string buffers for efficient string concatenation.
   A document takes a buffer and an indentation, has side effects on the buffer
   and returns a new indentation. The indentation argument indicates the level
   of indentation to be used if a new line has to be started (because of what is
   already in the buffer) *)
type doc = Buffer.t -> int -> int

let rec printTree (printer : int -> 'a -> doc) (tree : 'a) : string =
  let buffer_init_size =
    64
    (* you may want to change this *)
  in
  let buffer = Buffer.create buffer_init_size in
  let _ = printer 0 tree buffer 0 in
  (* discard return value *)
  Buffer.contents buffer

let indent_width = 2
let spaces (i : int) : string = if i > 0 then String.make i ' ' else ""
let indent (i : int) : string = "\n" ^ spaces i

(* To avoid dependency on package extlib, which has
   Extlib.ExtChar.Char.is_whitespace, we employ the following awkward
   way to check a character for whitespace.
   Note: String.trim exists in the core libraries since Ocaml 4.00. *)
let isWhiteSpace (c : char) : bool = String.trim (String.make 1 c) = ""

(* this render function is written for C-style languages, you may want to change it *)
let render (s : string) : doc =
 fun buf i ->
  (* invariant: last char of the buffer is never whitespace *)
  let n = Buffer.length buf in
  let last = if n = 0 then None else Some (Buffer.nth buf (n - 1)) in
  let newindent =
    match s with "{" -> i + indent_width | "}" -> i - indent_width | _ -> i
  in
  let whitespace =
    match last with
    | None -> ""
    | Some '}' -> ( match s with ";" -> "" | _ -> indent newindent)
    | Some '{' | Some ';' -> if s = "}" then indent newindent else indent i
    | Some '[' | Some '(' -> ""
    | Some c -> (
        if isWhiteSpace c then ""
        else
          match s with
          | ";" | "," | ")" | "]" -> ""
          | "{" -> indent i
          | "}" -> indent newindent
          | _ -> if String.trim s = "" then "" else " ")
  in
  Buffer.add_string buf whitespace;
  Buffer.add_string buf s;
  newindent

let emptyDoc : doc = fun buf i -> i

let concatD (ds : doc list) : doc =
 fun buf i ->
  List.fold_left
    (fun accIndent elemDoc -> elemDoc buf accIndent)
    (emptyDoc buf i) ds

let parenth (d : doc) : doc = concatD [ render "("; d; render ")" ]
let prPrec (i : int) (j : int) (d : doc) : doc = if j < i then parenth d else d
let prtChar (_ : int) (c : char) : doc = render ("'" ^ Char.escaped c ^ "'")
let prtInt (_ : int) (i : int) : doc = render (string_of_int i)
let prtFloat (_ : int) (f : float) : doc = render (sprintf "%.15g" f)

let prtString (_ : int) (s : string) : doc =
  render ("\"" ^ String.escaped s ^ "\"")

let prtStellaIdent _ (AbsStella.StellaIdent i) : doc = render i

let rec prtStellaIdentListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtStellaIdent 0 x ]
  | _, x :: xs ->
      concatD [ prtStellaIdent 0 x; render ","; prtStellaIdentListBNFC 0 xs ]

let prtExtensionName _ (AbsStella.ExtensionName i) : doc = render i

let rec prtExtensionNameListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtExtensionName 0 x ]
  | _, x :: xs ->
      concatD
        [ prtExtensionName 0 x; render ","; prtExtensionNameListBNFC 0 xs ]

let prtMemoryAddress _ (AbsStella.MemoryAddress i) : doc = render i

let rec prtProgram (i : int) (e : AbsStella.program) : doc =
  match e with
  | AbsStella.AProgram (languagedecl, extensions, decls) ->
      prPrec i 0
        (concatD
           [
             prtLanguageDecl 0 languagedecl;
             prtExtensionListBNFC 0 extensions;
             prtDeclListBNFC 0 decls;
           ])

and prtLanguageDecl (i : int) (e : AbsStella.languageDecl) : doc =
  match e with
  | AbsStella.LanguageCore ->
      prPrec i 0 (concatD [ render "language"; render "core"; render ";" ])

and prtExtension (i : int) (e : AbsStella.extension) : doc =
  match e with
  | AbsStella.AnExtension extensionnames ->
      prPrec i 0
        (concatD
           [
             render "extend";
             render "with";
             prtExtensionNameListBNFC 0 extensionnames;
           ])

and prtExtensionListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, x :: xs ->
      concatD [ prtExtension 0 x; render ";"; prtExtensionListBNFC 0 xs ]

and prtDecl (i : int) (e : AbsStella.decl) : doc =
  match e with
  | AbsStella.DeclFun
      (annotations, stellaident, paramdecls, returntype, throwtype, decls, expr)
    ->
      prPrec i 0
        (concatD
           [
             prtAnnotationListBNFC 0 annotations;
             render "fn";
             prtStellaIdent 0 stellaident;
             render "(";
             prtParamDeclListBNFC 0 paramdecls;
             render ")";
             prtReturnType 0 returntype;
             prtThrowType 0 throwtype;
             render "{";
             prtDeclListBNFC 0 decls;
             render "return";
             prtExpr 0 expr;
             render "}";
           ])
  | AbsStella.DeclTypeAlias (stellaident, type_) ->
      prPrec i 0
        (concatD
           [
             render "type";
             prtStellaIdent 0 stellaident;
             render "=";
             prtTypeT 0 type_;
           ])
  | AbsStella.DeclExceptionType type_ ->
      prPrec i 0
        (concatD
           [ render "exception"; render "type"; render "="; prtTypeT 0 type_ ])
  | AbsStella.DeclExceptionVariant (stellaident, type_) ->
      prPrec i 0
        (concatD
           [
             render "exception";
             render "variant";
             prtStellaIdent 0 stellaident;
             render ":";
             prtTypeT 0 type_;
           ])

and prtDeclListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, x :: xs -> concatD [ prtDecl 0 x; prtDeclListBNFC 0 xs ]

and prtLocalDecl (i : int) (e : AbsStella.localDecl) : doc =
  match e with
  | AbsStella.ALocalDecl decl -> prPrec i 0 (concatD [ prtDecl 0 decl ])

and prtLocalDeclListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, x :: xs ->
      concatD [ prtLocalDecl 0 x; render ";"; prtLocalDeclListBNFC 0 xs ]

and prtAnnotation (i : int) (e : AbsStella.annotation) : doc =
  match e with
  | AbsStella.InlineAnnotation -> prPrec i 0 (concatD [ render "inline" ])

and prtAnnotationListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, x :: xs -> concatD [ prtAnnotation 0 x; prtAnnotationListBNFC 0 xs ]

and prtParamDecl (i : int) (e : AbsStella.paramDecl) : doc =
  match e with
  | AbsStella.AParamDecl (stellaident, type_) ->
      prPrec i 0
        (concatD [ prtStellaIdent 0 stellaident; render ":"; prtTypeT 0 type_ ])

and prtParamDeclListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtParamDecl 0 x ]
  | _, x :: xs ->
      concatD [ prtParamDecl 0 x; render ","; prtParamDeclListBNFC 0 xs ]

and prtReturnType (i : int) (e : AbsStella.returnType) : doc =
  match e with
  | AbsStella.NoReturnType -> prPrec i 0 (concatD [])
  | AbsStella.SomeReturnType type_ ->
      prPrec i 0 (concatD [ render "->"; prtTypeT 0 type_ ])

and prtThrowType (i : int) (e : AbsStella.throwType) : doc =
  match e with
  | AbsStella.NoThrowType -> prPrec i 0 (concatD [])
  | AbsStella.SomeThrowType types ->
      prPrec i 0 (concatD [ render "throws"; prtTypeTListBNFC 9 types ])

and prtTypeT (i : int) (e : AbsStella.typeT) : doc =
  match e with
  | AbsStella.TypeFun (types, type_) ->
      prPrec i 0
        (concatD
           [
             render "fn";
             render "(";
             prtTypeTListBNFC 0 types;
             render ")";
             render "->";
             prtTypeT 0 type_;
           ])
  | AbsStella.TypeRec (stellaident, type_) ->
      prPrec i 0
        (concatD
           [
             render "µ";
             prtStellaIdent 0 stellaident;
             render ".";
             prtTypeT 0 type_;
           ])
  | AbsStella.TypeSum (type_1, type_2) ->
      prPrec i 1 (concatD [ prtTypeT 2 type_1; render "+"; prtTypeT 2 type_2 ])
  | AbsStella.TypeTuple types ->
      prPrec i 2 (concatD [ render "{"; prtTypeTListBNFC 0 types; render "}" ])
  | AbsStella.TypeRecord recordfieldtypes ->
      prPrec i 2
        (concatD
           [
             render "{";
             prtRecordFieldTypeListBNFC 0 recordfieldtypes;
             render "}";
           ])
  | AbsStella.TypeVariant variantfieldtypes ->
      prPrec i 2
        (concatD
           [
             render "<|";
             prtVariantFieldTypeListBNFC 0 variantfieldtypes;
             render "|>";
           ])
  | AbsStella.TypeList type_ ->
      prPrec i 2 (concatD [ render "["; prtTypeT 0 type_; render "]" ])
  | AbsStella.TypeBool -> prPrec i 3 (concatD [ render "Bool" ])
  | AbsStella.TypeNat -> prPrec i 3 (concatD [ render "Nat" ])
  | AbsStella.TypeUnit -> prPrec i 3 (concatD [ render "Unit" ])
  | AbsStella.TypeTop -> prPrec i 3 (concatD [ render "Top" ])
  | AbsStella.TypeBottom -> prPrec i 3 (concatD [ render "Bot" ])
  | AbsStella.TypeRef type_ ->
      prPrec i 3 (concatD [ render "&"; prtTypeT 2 type_ ])
  | AbsStella.TypeVar stellaident ->
      prPrec i 3 (concatD [ prtStellaIdent 0 stellaident ])

and prtTypeTListBNFC i es : doc =
  match (i, es) with
  | 9, [ x ] -> concatD [ prtTypeT 9 x ]
  | 9, x :: xs -> concatD [ prtTypeT 9 x; render ","; prtTypeTListBNFC 9 xs ]
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtTypeT 0 x ]
  | _, x :: xs -> concatD [ prtTypeT 0 x; render ","; prtTypeTListBNFC 0 xs ]

and prtMatchCase (i : int) (e : AbsStella.matchCase) : doc =
  match e with
  | AbsStella.AMatchCase (pattern, expr) ->
      prPrec i 0 (concatD [ prtPattern 0 pattern; render "=>"; prtExpr 0 expr ])

and prtMatchCaseListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtMatchCase 0 x ]
  | _, x :: xs ->
      concatD [ prtMatchCase 0 x; render "|"; prtMatchCaseListBNFC 0 xs ]

and prtOptionalTyping (i : int) (e : AbsStella.optionalTyping) : doc =
  match e with
  | AbsStella.NoTyping -> prPrec i 0 (concatD [])
  | AbsStella.SomeTyping type_ ->
      prPrec i 0 (concatD [ render ":"; prtTypeT 0 type_ ])

and prtPatternData (i : int) (e : AbsStella.patternData) : doc =
  match e with
  | AbsStella.NoPatternData -> prPrec i 0 (concatD [])
  | AbsStella.SomePatternData pattern ->
      prPrec i 0 (concatD [ render "="; prtPattern 0 pattern ])

and prtExprData (i : int) (e : AbsStella.exprData) : doc =
  match e with
  | AbsStella.NoExprData -> prPrec i 0 (concatD [])
  | AbsStella.SomeExprData expr ->
      prPrec i 0 (concatD [ render "="; prtExpr 0 expr ])

and prtPattern (i : int) (e : AbsStella.pattern) : doc =
  match e with
  | AbsStella.PatternVariant (stellaident, patterndata) ->
      prPrec i 0
        (concatD
           [
             render "<|";
             prtStellaIdent 0 stellaident;
             prtPatternData 0 patterndata;
             render "|>";
           ])
  | AbsStella.PatternInl pattern ->
      prPrec i 0
        (concatD [ render "inl"; render "("; prtPattern 0 pattern; render ")" ])
  | AbsStella.PatternInr pattern ->
      prPrec i 0
        (concatD [ render "inr"; render "("; prtPattern 0 pattern; render ")" ])
  | AbsStella.PatternTuple patterns ->
      prPrec i 0
        (concatD [ render "{"; prtPatternListBNFC 0 patterns; render "}" ])
  | AbsStella.PatternRecord labelledpatterns ->
      prPrec i 0
        (concatD
           [
             render "{";
             prtLabelledPatternListBNFC 0 labelledpatterns;
             render "}";
           ])
  | AbsStella.PatternList patterns ->
      prPrec i 0
        (concatD [ render "["; prtPatternListBNFC 0 patterns; render "]" ])
  | AbsStella.PatternCons (pattern1, pattern2) ->
      prPrec i 0
        (concatD
           [
             render "(";
             prtPattern 0 pattern1;
             render ",";
             prtPattern 0 pattern2;
             render ")";
           ])
  | AbsStella.PatternFalse -> prPrec i 0 (concatD [ render "false" ])
  | AbsStella.PatternTrue -> prPrec i 0 (concatD [ render "true" ])
  | AbsStella.PatternUnit -> prPrec i 0 (concatD [ render "unit" ])
  | AbsStella.PatternInt integer -> prPrec i 0 (concatD [ prtInt 0 integer ])
  | AbsStella.PatternSucc pattern ->
      prPrec i 0
        (concatD
           [ render "succ"; render "("; prtPattern 0 pattern; render ")" ])
  | AbsStella.PatternVar stellaident ->
      prPrec i 0 (concatD [ prtStellaIdent 0 stellaident ])

and prtPatternListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtPattern 0 x ]
  | _, x :: xs ->
      concatD [ prtPattern 0 x; render ","; prtPatternListBNFC 0 xs ]

and prtLabelledPattern (i : int) (e : AbsStella.labelledPattern) : doc =
  match e with
  | AbsStella.ALabelledPattern (stellaident, pattern) ->
      prPrec i 0
        (concatD
           [ prtStellaIdent 0 stellaident; render "="; prtPattern 0 pattern ])

and prtLabelledPatternListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtLabelledPattern 0 x ]
  | _, x :: xs ->
      concatD
        [ prtLabelledPattern 0 x; render ","; prtLabelledPatternListBNFC 0 xs ]

and prtBinding (i : int) (e : AbsStella.binding) : doc =
  match e with
  | AbsStella.ABinding (stellaident, expr) ->
      prPrec i 0
        (concatD [ prtStellaIdent 0 stellaident; render "="; prtExpr 0 expr ])

and prtBindingListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtBinding 0 x ]
  | _, x :: xs ->
      concatD [ prtBinding 0 x; render ","; prtBindingListBNFC 0 xs ]

and prtExpr (i : int) (e : AbsStella.expr) : doc =
  match e with
  | AbsStella.Sequence (expr1, expr2) ->
      prPrec i 0 (concatD [ prtExpr 1 expr1; render ";"; prtExpr 0 expr2 ])
  | AbsStella.Assign (expr1, expr2) ->
      prPrec i 1 (concatD [ prtExpr 2 expr1; render ":="; prtExpr 1 expr2 ])
  | AbsStella.If (expr1, expr2, expr3) ->
      prPrec i 1
        (concatD
           [
             render "if";
             prtExpr 1 expr1;
             render "then";
             prtExpr 1 expr2;
             render "else";
             prtExpr 1 expr3;
           ])
  | AbsStella.Let (patternbindings, expr) ->
      prPrec i 0
        (concatD
           [
             render "let";
             prtPatternBindingListBNFC 0 patternbindings;
             render "in";
             prtExpr 0 expr;
           ])
  | AbsStella.LetRec (patternbindings, expr) ->
      prPrec i 0
        (concatD
           [
             render "letrec";
             prtPatternBindingListBNFC 0 patternbindings;
             render "in";
             prtExpr 0 expr;
           ])
  | AbsStella.LessThan (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render "<"; prtExpr 3 expr2 ])
  | AbsStella.LessThanOrEqual (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render "<="; prtExpr 3 expr2 ])
  | AbsStella.GreaterThan (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render ">"; prtExpr 3 expr2 ])
  | AbsStella.GreaterThanOrEqual (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render ">="; prtExpr 3 expr2 ])
  | AbsStella.Equal (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render "=="; prtExpr 3 expr2 ])
  | AbsStella.NotEqual (expr1, expr2) ->
      prPrec i 2 (concatD [ prtExpr 3 expr1; render "!="; prtExpr 3 expr2 ])
  | AbsStella.TypeAsc (expr, type_) ->
      prPrec i 3 (concatD [ prtExpr 3 expr; render "as"; prtTypeT 2 type_ ])
  | AbsStella.TypeCast (expr, type_) ->
      prPrec i 3
        (concatD
           [ prtExpr 3 expr; render "cast"; render "as"; prtTypeT 2 type_ ])
  | AbsStella.Abstraction (paramdecls, expr) ->
      prPrec i 3
        (concatD
           [
             render "fn";
             render "(";
             prtParamDeclListBNFC 0 paramdecls;
             render ")";
             render "{";
             render "return";
             prtExpr 0 expr;
             render "}";
           ])
  | AbsStella.Variant (stellaident, exprdata) ->
      prPrec i 3
        (concatD
           [
             render "<|";
             prtStellaIdent 0 stellaident;
             prtExprData 0 exprdata;
             render "|>";
           ])
  | AbsStella.Match (expr, matchcases) ->
      prPrec i 3
        (concatD
           [
             render "match";
             prtExpr 2 expr;
             render "{";
             prtMatchCaseListBNFC 0 matchcases;
             render "}";
           ])
  | AbsStella.List exprs ->
      prPrec i 3 (concatD [ render "["; prtExprListBNFC 0 exprs; render "]" ])
  | AbsStella.Add (expr1, expr2) ->
      prPrec i 3 (concatD [ prtExpr 3 expr1; render "+"; prtExpr 4 expr2 ])
  | AbsStella.Subtract (expr1, expr2) ->
      prPrec i 3 (concatD [ prtExpr 3 expr1; render "-"; prtExpr 4 expr2 ])
  | AbsStella.LogicOr (expr1, expr2) ->
      prPrec i 3 (concatD [ prtExpr 3 expr1; render "or"; prtExpr 4 expr2 ])
  | AbsStella.Multiply (expr1, expr2) ->
      prPrec i 4 (concatD [ prtExpr 4 expr1; render "*"; prtExpr 5 expr2 ])
  | AbsStella.Divide (expr1, expr2) ->
      prPrec i 4 (concatD [ prtExpr 4 expr1; render "/"; prtExpr 5 expr2 ])
  | AbsStella.LogicAnd (expr1, expr2) ->
      prPrec i 4 (concatD [ prtExpr 4 expr1; render "and"; prtExpr 5 expr2 ])
  | AbsStella.Ref expr ->
      prPrec i 5
        (concatD [ render "new"; render "("; prtExpr 5 expr; render ")" ])
  | AbsStella.Deref expr -> prPrec i 5 (concatD [ render "*"; prtExpr 5 expr ])
  | AbsStella.Application (expr, exprs) ->
      prPrec i 6
        (concatD
           [ prtExpr 6 expr; render "("; prtExprListBNFC 0 exprs; render ")" ])
  | AbsStella.DotRecord (expr, stellaident) ->
      prPrec i 6
        (concatD [ prtExpr 6 expr; render "."; prtStellaIdent 0 stellaident ])
  | AbsStella.DotTuple (expr, integer) ->
      prPrec i 6 (concatD [ prtExpr 6 expr; render "."; prtInt 0 integer ])
  | AbsStella.Tuple exprs ->
      prPrec i 6 (concatD [ render "{"; prtExprListBNFC 0 exprs; render "}" ])
  | AbsStella.Record bindings ->
      prPrec i 6
        (concatD [ render "{"; prtBindingListBNFC 0 bindings; render "}" ])
  | AbsStella.ConsList (expr1, expr2) ->
      prPrec i 6
        (concatD
           [
             render "cons";
             render "(";
             prtExpr 0 expr1;
             render ",";
             prtExpr 0 expr2;
             render ")";
           ])
  | AbsStella.Head expr ->
      prPrec i 6
        (concatD
           [ render "List::head"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.IsEmpty expr ->
      prPrec i 6
        (concatD
           [ render "List::isempty"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Tail expr ->
      prPrec i 6
        (concatD
           [ render "List::tail"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Panic -> prPrec i 6 (concatD [ render "panic!" ])
  | AbsStella.Throw expr ->
      prPrec i 6
        (concatD [ render "throw"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.TryCatch (expr1, pattern, expr2) ->
      prPrec i 6
        (concatD
           [
             render "try";
             render "{";
             prtExpr 0 expr1;
             render "}";
             render "catch";
             render "{";
             prtPattern 0 pattern;
             render "=>";
             prtExpr 0 expr2;
             render "}";
           ])
  | AbsStella.TryWith (expr1, expr2) ->
      prPrec i 6
        (concatD
           [
             render "try";
             render "{";
             prtExpr 0 expr1;
             render "}";
             render "with";
             render "{";
             prtExpr 0 expr2;
             render "}";
           ])
  | AbsStella.Inl expr ->
      prPrec i 6
        (concatD [ render "inl"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Inr expr ->
      prPrec i 6
        (concatD [ render "inr"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Succ expr ->
      prPrec i 6
        (concatD [ render "succ"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.LogicNot expr ->
      prPrec i 6
        (concatD [ render "not"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Pred expr ->
      prPrec i 6
        (concatD [ render "Nat::pred"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.IsZero expr ->
      prPrec i 6
        (concatD
           [ render "Nat::iszero"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.Fix expr ->
      prPrec i 6
        (concatD [ render "fix"; render "("; prtExpr 0 expr; render ")" ])
  | AbsStella.NatRec (expr1, expr2, expr3) ->
      prPrec i 6
        (concatD
           [
             render "Nat::rec";
             render "(";
             prtExpr 0 expr1;
             render ",";
             prtExpr 0 expr2;
             render ",";
             prtExpr 0 expr3;
             render ")";
           ])
  | AbsStella.Fold (type_, expr) ->
      prPrec i 6
        (concatD
           [
             render "fold";
             render "[";
             prtTypeT 0 type_;
             render "]";
             prtExpr 7 expr;
           ])
  | AbsStella.Unfold (type_, expr) ->
      prPrec i 6
        (concatD
           [
             render "unfold";
             render "[";
             prtTypeT 0 type_;
             render "]";
             prtExpr 7 expr;
           ])
  | AbsStella.ConstTrue -> prPrec i 7 (concatD [ render "true" ])
  | AbsStella.ConstFalse -> prPrec i 7 (concatD [ render "false" ])
  | AbsStella.ConstUnit -> prPrec i 7 (concatD [ render "unit" ])
  | AbsStella.ConstInt integer -> prPrec i 7 (concatD [ prtInt 0 integer ])
  | AbsStella.ConstMemory memoryaddress ->
      prPrec i 7 (concatD [ prtMemoryAddress 0 memoryaddress ])
  | AbsStella.Var stellaident ->
      prPrec i 7 (concatD [ prtStellaIdent 0 stellaident ])

and prtExprListBNFC i es : doc =
  match (i, es) with
  | 2, [ x ] -> concatD [ prtExpr 2 x; render ";" ]
  | 2, x :: xs -> concatD [ prtExpr 2 x; render ";"; prtExprListBNFC 2 xs ]
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtExpr 0 x ]
  | _, x :: xs -> concatD [ prtExpr 0 x; render ","; prtExprListBNFC 0 xs ]

and prtPatternBinding (i : int) (e : AbsStella.patternBinding) : doc =
  match e with
  | AbsStella.APatternBinding (pattern, expr) ->
      prPrec i 0 (concatD [ prtPattern 0 pattern; render "="; prtExpr 0 expr ])

and prtPatternBindingListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtPatternBinding 0 x ]
  | _, x :: xs ->
      concatD
        [ prtPatternBinding 0 x; render ","; prtPatternBindingListBNFC 0 xs ]

and prtVariantFieldType (i : int) (e : AbsStella.variantFieldType) : doc =
  match e with
  | AbsStella.AVariantFieldType (stellaident, optionaltyping) ->
      prPrec i 0
        (concatD
           [ prtStellaIdent 0 stellaident; prtOptionalTyping 0 optionaltyping ])

and prtVariantFieldTypeListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtVariantFieldType 0 x ]
  | _, x :: xs ->
      concatD
        [
          prtVariantFieldType 0 x; render ","; prtVariantFieldTypeListBNFC 0 xs;
        ]

and prtRecordFieldType (i : int) (e : AbsStella.recordFieldType) : doc =
  match e with
  | AbsStella.ARecordFieldType (stellaident, type_) ->
      prPrec i 0
        (concatD [ prtStellaIdent 0 stellaident; render ":"; prtTypeT 0 type_ ])

and prtRecordFieldTypeListBNFC i es : doc =
  match (i, es) with
  | _, [] -> concatD []
  | _, [ x ] -> concatD [ prtRecordFieldType 0 x ]
  | _, x :: xs ->
      concatD
        [ prtRecordFieldType 0 x; render ","; prtRecordFieldTypeListBNFC 0 xs ]

and prtTyping (i : int) (e : AbsStella.typing) : doc =
  match e with
  | AbsStella.ATyping (expr, type_) ->
      prPrec i 0 (concatD [ prtExpr 0 expr; render ":"; prtTypeT 0 type_ ])
