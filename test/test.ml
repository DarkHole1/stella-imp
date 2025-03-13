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

let test_nested_typecheck () =
  check_typecheck' "{{{{{{{{{{0}}}}}}}}}} <= {{{{{{{{{{Nat}}}}}}}}}}"
    "{{{{{{{{{{0}}}}}}}}}}" "{{{{{{{{{{Nat}}}}}}}}}}";
  check_typecheck'
    "{a = {true, 0}, b = [unit, unit]} <= {a : {Bool, Nat}, b : [Unit]}"
    "{a = {true, 0}, b = [unit, unit]}" "{a : {Bool, Nat}, b : [Unit]}";

  check_typecheck'
    "inl(<| hello = [true, false] |>) <= <| hello = [Bool] |> + <| world = {{ \
     c : Unit }} |>"
    "inl(<| hello = [true, false] |>)"
    "<| hello : [Bool] |> + <| world : {{ c : Unit }} |>";
  check_typecheck'
    "inr(<| world = {{c = unit}} |>) <= <| hello = [Bool] |> + <| world = {{ c \
     : Unit }} |>"
    "inl(<| hello = [true, false] |>)"
    "<| hello : [Bool] |> + <| world : {{ c : Unit }} |>"

let test_operations_typecheck () =
  check_typecheck' "succ(0) <= Nat" "succ(0)" "Nat";
  check_typecheck' "Nat::pred(0) <= Nat" "Nat::pred(0)" "Nat";
  check_typecheck' "Nat::iszero(0) <= Bool" "Nat::iszero(0)" "Bool";

  check_typecheck' "{ 0 }.1 <= Nat" "{ 0 }.1" "Nat";
  check_typecheck' "{ 0, true }.2 <= Bool" "{ 0, true }.2" "Bool";
  check_typecheck' "{ 0, true, unit }.2 <= Bool" "{ 0, true, unit }.2" "Bool";

  check_typecheck' "{ a = 0, b = unit, foo = true }.a <= Nat"
    "{ a = 0, b = unit, foo = true }.a" "Nat";
  check_typecheck' "{ a = 0, b = unit, foo = true }.b <= Unit"
    "{ a = 0, b = unit, foo = true }.b" "Unit";
  check_typecheck' "{ a = 0, b = unit, foo = true }.foo <= Bool"
    "{ a = 0, b = unit, foo = true }.foo" "Bool";

  check_typecheck' "true as Bool <= Bool" "true as Bool" "Bool";
  check_typecheck' "inl(0) as (Nat + Unit) <= Nat + Unit" "inl(0) as (Nat + Unit)"
    "Nat + Unit";
  check_typecheck' "inr(unit) as (Nat + Unit) <= Nat + Unit"
    "inr(unit) as (Nat + Unit)" "Nat + Unit";
  check_typecheck'
    "<| a = 0 |> as <| a : Nat, b : Bool |> <= <| a : Nat, b : Bool |>"
    "<| a = 0 |> as <| a : Nat, b : Bool |>" "<| a : Nat, b : Bool |>";
  check_typecheck'
    "<| b = false |> as <| a : Nat, b : Bool |> <= <| a : Nat, b : Bool |>"
    "<| b = false |> as <| a : Nat, b : Bool |>" "<| a : Nat, b : Bool |>"

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

let test_nested_infer () =
  check_infer' "{{{{{{{{{{0}}}}}}}}}} <= {{{{{{{{{{Nat}}}}}}}}}}"
    "{{{{{{{{{{Nat}}}}}}}}}}" "{{{{{{{{{{0}}}}}}}}}}";
  check_infer'
    "{a = {true, 0}, b = [unit, unit]} <= {a : {Bool, Nat}, b : [Unit]}"
    "{a : {Bool, Nat}, b : [Unit]}" "{a = {true, 0}, b = [unit, unit]}"

let test_operations_infer () =
  check_infer' "succ(0) => Nat" "Nat" "succ(0)";
  check_infer' "Nat::pred(0) => Nat" "Nat" "Nat::pred(0)";
  check_infer' "Nat::iszero(0) => Bool" "Bool" "Nat::iszero(0)";

  check_infer' "{ 0 }.1 => Nat" "Nat" "{ 0 }.1";
  check_infer' "{ 0, true }.2 => Bool" "Bool" "{ 0, true }.2";
  check_infer' "{ 0, true, unit }.2 => Bool" "Bool" "{ 0, true, unit }.2";

  check_infer' "{ a = 0, b = unit, foo = true }.a => Nat" "Nat"
    "{ a = 0, b = unit, foo = true }.a";
  check_infer' "{ a = 0, b = unit, foo = true }.b => Unit" "Unit"
    "{ a = 0, b = unit, foo = true }.b";
  check_infer' "{ a = 0, b = unit, foo = true }.foo => Bool" "Bool"
    "{ a = 0, b = unit, foo = true }.foo";

  check_infer' "true as Bool => Bool" "Bool" "true as Bool";
  check_infer' "inl(0) as (Nat + Unit) => Nat + Unit" "Nat + Unit"
    "inl(0) as (Nat + Unit)";
  check_infer' "inr(unit) as (Nat + Unit) => Nat + Unit" "Nat + Unit"
    "inr(unit) as (Nat + Unit)";
  check_infer'
    "<| a = 0 |> as <| a : Nat, b : Bool |> => <| a : Nat, b : Bool |>"
    "<| a : Nat, b : Bool |>" "<| a = 0 |> as <| a : Nat, b : Bool |>";
  check_infer'
    "<| b = false |> as <| a : Nat, b : Bool |> => <| a : Nat, b : Bool |>"
    "<| a : Nat, b : Bool |>" "<| b = false |> as <| a : Nat, b : Bool |>"

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
          Alcotest.test_case "Typecheck nested types" `Quick
            test_nested_typecheck;
          Alcotest.test_case "Infer nested types" `Quick test_nested_infer;
          Alcotest.test_case "Typecheck basic operations" `Quick
            test_operations_typecheck;
          Alcotest.test_case "Infer basic operations" `Quick
            test_operations_infer;
        ] );
    ]
