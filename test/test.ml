open Utils

let test_basic_typecheck () =
  check_typecheck' "true <= Bool" "true" "Bool";
  check_typecheck' "false <= Bool" "false" "Bool";
  check_typecheck' "0 <= Nat" "0" "Nat";
  check_typecheck' "unit <= Unit" "unit" "Unit"

let test_parametrized_typecheck () =
  check_typecheck "[true] <= [Bool]" [] "[true]" "[Bool]"

let test_basic_infer () =
  check_infer' "true => Bool" "Bool" "true";
  check_infer' "false => Bool" "Bool" "false";
  check_infer' "0 => Nat" "Nat" "0";
  check_infer' "unit => Unit" "Unit" "unit"

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
