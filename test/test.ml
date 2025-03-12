open Stella

let pp (s : 'a -> ShowStella.showable) (fmt : Format.formatter) (v : 'a) : unit
    =
  Format.pp_print_string fmt (ShowStella.show (s v))

let pp_expr = pp ShowStella.showExpr
let pp_typeT = pp ShowStella.showTypeT
let[@warning "-unused-value-declaration"] expr = Alcotest.testable pp_expr ( = )
let typeT = Alcotest.testable pp_typeT ( = )

let test_basic_typecheck () =
  Typecheck.typecheck [] ConstTrue TypeBool;
  Typecheck.typecheck [] ConstFalse TypeBool;
  Typecheck.typecheck [] (ConstInt 0) TypeNat;
  Typecheck.typecheck [] ConstUnit TypeUnit

(* TODO *)
let test_parametrized_typecheck () =
  Typecheck.typecheck [] ConstTrue TypeBool;
  Typecheck.typecheck [] ConstFalse TypeBool;
  Typecheck.typecheck [] (ConstInt 0) TypeNat;
  Typecheck.typecheck [] ConstUnit TypeUnit

let test_basic_infer () =
  Alcotest.check typeT "true => Bool" TypeBool (Typecheck.infer [] ConstTrue);
  Alcotest.check typeT "false => Bool" TypeBool (Typecheck.infer [] ConstFalse);
  Alcotest.check typeT "0 => Nat" TypeNat (Typecheck.infer [] (ConstInt 0));
  Alcotest.check typeT "unit => Unit" TypeUnit (Typecheck.infer [] ConstUnit)

let () =
  Alcotest.run "Typecheck"
    [
      ( "basic-typecheck",
        [
          Alcotest.test_case "Basic typecheck" `Quick test_basic_typecheck;
          Alcotest.test_case "Basic infer" `Quick test_basic_infer;
          Alcotest.test_case "Typecheck parametrized types" `Quick
            test_parametrized_typecheck;
        ] );
    ]
