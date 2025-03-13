open Stella

let pp (s : 'a -> ShowStella.showable) (fmt : Format.formatter) (v : 'a) : unit
    =
  Format.pp_print_string fmt (ShowStella.show (s v))

let pp_expr = pp ShowStella.showExpr
let pp_typeT = pp ShowStella.showTypeT
let[@warning "-unused-value-declaration"] expr = Alcotest.testable pp_expr ( = )
let typeT = Alcotest.testable pp_typeT ( = )

let parse_string_expr (s : string) =
  Lexing.from_string s |> ParStella.pExpr LexStella.token

let parse_string_typeT (s : string) =
  Lexing.from_string s |> ParStella.pTypeT LexStella.token

let typecheck (ctx : Typecheck.context) (expr : string) (ty : string) =
  let ctx' = ctx in
  let expr' = parse_string_expr expr in
  let ty' = parse_string_typeT ty in
  Typecheck.typecheck ctx' expr' ty'

let typecheck' = typecheck []
let check_typecheck (_ : string) = typecheck
let check_typecheck' (_ : string) = typecheck'

let infer (ctx : Typecheck.context) (expr : string) =
  let ctx' = ctx in
  let expr' = parse_string_expr expr in
  Typecheck.infer ctx' expr'

let infer' = infer []

let check_infer (d : string) (ty : string) (ctx : Typecheck.context)
    (expr : string) =
  let ty' = parse_string_typeT ty in
  Alcotest.check typeT d ty' (infer ctx expr)

let check_infer' (d : string) (ty : string) (expr : string) =
  let ty' = parse_string_typeT ty in
  Alcotest.check typeT d ty' (infer [] expr)

let o : Typecheck.context = []

let in_context (ctx : Typecheck.context) (expr : string) = (ctx, expr)

let check_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
 fun (d : string) -> check_typecheck d ctx expr ty

let infer_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
 fun (d : string) -> check_infer d ty ctx expr

let both_with ((ctx, expr) : Typecheck.context * string) (ty : string) =
 fun (d : string) ->
  check_typecheck d ctx expr ty;
  check_infer d ty ctx expr

let check (d : string) (f : string -> unit) = f d

let (|-) = in_context
let (<=) = check_with
let (=>) = infer_with
let (<=>) = both_with