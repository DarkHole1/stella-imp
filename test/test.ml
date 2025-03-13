open Utils

let test_basic_typecheck () =
  check_typecheck' "true <= Bool" "true" "Bool";
  check_typecheck' "false <= Bool" "false" "Bool";
  check_typecheck' "0 <= Nat" "0" "Nat";
  check_typecheck' "unit <= Unit" "unit" "Unit"

let test_parametrized_typecheck () =
  check_typecheck' "[true] <= [Bool]" "[true]" "[Bool]";
  check_typecheck' "[0] <= [Nat]" "[0]" "[Nat]";
  check_typecheck' "[unit, unit, unit] <= [Unit]" "[unit, unit, unit]" "[Unit]";

  check_typecheck' "{0, true} <= {Nat, Bool}" "{0, true}" "{Nat, Bool}";
  check_typecheck' "{false, unit} <= {Bool, Unit}" "{false, unit}"
    "{Bool, Unit}";

  check_typecheck' "{0, true, false, unit} <= {Nat, Bool, Bool, Unit}"
    "{0, true, false, unit}" "{Nat, Bool, Bool, Unit}";
  check_typecheck'
    "{true, 0, unit, false, unit} <= {Bool, Nat, Unit, Bool, Unit}"
    "{true, 0, unit, false, unit}" "{Bool, Nat, Unit, Bool, Unit}";

  check_typecheck'
    "{a = true, b = unit, foo_bar = 0} <= {a : Bool, b : Unit, foo_bar : Nat}"
    "{a = true, b = unit, foo_bar = 0}" "{a : Bool, b : Unit, foo_bar : Nat}";
  check_typecheck' "{a = unit, b = true} <= {b : Bool, a : Unit}"
    "{a = unit, b = true}" "{b : Bool, a : Unit}";
  check_typecheck' "{} <= {}" "{}" "{}";

  check_typecheck' "inl(true) <= Bool + Unit" "inl(true)" "Bool + Unit";
  check_typecheck' "inr(unit) <= Bool + Unit" "inr(unit)" "Bool + Unit";

  check_typecheck'
    "<| success = true |> <= <| success : Bool, failure : Unit |>"
    "<| success = true |>" "<| success : Bool, failure : Unit |>";
  check_typecheck'
    "<| failure = unit |> <= <| success : Bool, failure : Unit |>"
    "<| failure = unit |>" "<| success : Bool, failure : Unit |>"

let test_basic_infer () =
  check_infer' "true => Bool" "Bool" "true";
  check_infer' "false => Bool" "Bool" "false";
  check_infer' "0 => Nat" "Nat" "0";
  check_infer' "unit => Unit" "Unit" "unit"

let test_parametrized_infer () =
  check_infer' "[true] => [Bool]" "[Bool]" "[true]";
  check_infer' "[0] => [Nat]" "[Nat]" "[0]";
  check_infer' "[unit, unit, unit] => [Unit]" "[Unit]" "[unit, unit, unit]";

  check_infer' "{0, true} => {Nat, Bool}" "{Nat, Bool}" "{0, true}";
  check_infer' "{false, unit} => {Bool, Unit}" "{Bool, Unit}" "{false, unit}";

  check_infer' "{0, true, false, unit} => {Nat, Bool, Bool, Unit}"
    "{Nat, Bool, Bool, Unit}" "{0, true, false, unit}";
  check_infer' "{true, 0, unit, false, unit} => {Bool, Nat, Unit, Bool, Unit}"
    "{Bool, Nat, Unit, Bool, Unit}" "{true, 0, unit, false, unit}";

  check_infer'
    "{a = true, b = unit, foo_bar = 0} => {a : Bool, b : Unit, foo_bar : Nat}"
    "{a : Bool, b : Unit, foo_bar : Nat}" "{a = true, b = unit, foo_bar = 0}";
  check_infer' "{} => {}" "{}" "{}"

let () =
  Alcotest.run "Typecheck"
    [
      ( "basic-typecheck",
        [
          Alcotest.test_case "Basic typecheck" `Quick test_basic_typecheck;
          Alcotest.test_case "Basic infer" `Quick test_basic_infer;
          Alcotest.test_case "Typecheck parametrized types" `Quick
            test_parametrized_typecheck;
          Alcotest.test_case "Infer parametrized types" `Quick
            test_parametrized_infer;
        ] );
    ]
