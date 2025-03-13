open Utils

let test_basic () =
  check "true <=> Bool" (o |- "true" <=> "Bool");
  check "false <=> Bool" (o |- "false" <=> "Bool");
  check "0 <=> Nat" (o |- "0" <=> "Nat");
  check "unit <=> Unit" (o |- "unit" <=> "Unit")

let test_parametrized () =
  check "[true] <=> [Bool]" (o |- "[true]" <=> "[Bool]");
  check "[0] <=> [Nat]" (o |- "[0]" <=> "[Nat]");
  check "[unit, unit, unit] <=> [Unit]" (o |- "[unit, unit, unit]" <=> "[Unit]");

  check "{0, true} <=> {Nat, Bool}" (o |- "{0, true}" <=> "{Nat, Bool}");
  check "{false, unit} <=> {Bool, Unit}"
    (o |- "{false, unit}" <=> "{Bool, Unit}");

  check "{0, true, false, unit} <=> {Nat, Bool, Bool, Unit}"
    (o |- "{0, true, false, unit}" <=> "{Nat, Bool, Bool, Unit}");
  check "{true, 0, unit, false, unit} <=> {Bool, Nat, Unit, Bool, Unit}"
    (o |- "{true, 0, unit, false, unit}" <=> "{Bool, Nat, Unit, Bool, Unit}");

  check
    "{a = true, b = unit, foo_bar = 0} <=> {a : Bool, b : Unit, foo_bar : Nat}"
    (o |- "{a = true, b = unit, foo_bar = 0}"
   <=> "{a : Bool, b : Unit, foo_bar : Nat}");
  check "{a = unit, b = true} <=> {b : Bool, a : Unit}"
    (o |- "{a = unit, b = true}" <= "{b : Bool, a : Unit}");
  check "{} <=> {}" (o |- "{}" <=> "{}");

  check "inl(true) <= Bool + Unit" (o |- "inl(true)" <= "Bool + Unit");
  check "inr(unit) <= Bool + Unit" (o |- "inr(unit)" <= "Bool + Unit");

  check "<| success = true |> <= <| success : Bool, failure : Unit |>"
    (o |- "<| success = true |>" <= "<| success : Bool, failure : Unit |>");
  check "<| failure = unit |> <=> <| success : Bool, failure : Unit |>"
    (o |- "<| failure = unit |>" <= "<| success : Bool, failure : Unit |>")

let test_nested () =
  check "{{{{{{{{{{0}}}}}}}}}} <=> {{{{{{{{{{Nat}}}}}}}}}}"
    (o |- "{{{{{{{{{{0}}}}}}}}}}" <=> "{{{{{{{{{{Nat}}}}}}}}}}");
  check "{a = {true, 0}, b = [unit, unit]} <=> {a : {Bool, Nat}, b : [Unit]}"
    (o |- "{a = {true, 0}, b = [unit, unit]}"
   <=> "{a : {Bool, Nat}, b : [Unit]}");

  check
    "inl(<| hello = [true, false] |>) <= <| hello = [Bool] |> + <| world = {{ \
     c : Unit }} |>"
    (o |- "inl(<| hello = [true, false] |>)"
   <= "<| hello : [Bool] |> + <| world : {{ c : Unit }} |>");
  check
    "inr(<| world = {{c = unit}} |>) <= <| hello = [Bool] |> + <| world = {{ c \
     : Unit }} |>"
    (o |- "inl(<| hello = [true, false] |>)"
   <= "<| hello : [Bool] |> + <| world : {{ c : Unit }} |>")

let test_operations () =
  check "succ(0) <=> Nat" (o |- "succ(0)" <=> "Nat");
  check "Nat::pred(0) <=> Nat" (o |- "Nat::pred(0)" <=> "Nat");
  check "Nat::iszero(0) <=> Bool" (o |- "Nat::iszero(0)" <=> "Bool");

  check "{ 0 }.1 <=> Nat" (o |- "{ 0 }.1" <=> "Nat");
  check "{ 0, true }.2 <=> Bool" (o |- "{ 0, true }.2" <=> "Bool");
  check "{ 0, true, unit }.2 <=> Bool" (o |- "{ 0, true, unit }.2" <=> "Bool");

  check "{ a = 0, b = unit, foo = true }.a <=> Nat"
    (o |- "{ a = 0, b = unit, foo = true }.a" <=> "Nat");
  check "{ a = 0, b = unit, foo = true }.b <=> Unit"
    (o |- "{ a = 0, b = unit, foo = true }.b" <=> "Unit");
  check "{ a = 0, b = unit, foo = true }.foo <=> Bool"
    (o |- "{ a = 0, b = unit, foo = true }.foo" <=> "Bool");

  check "true as Bool <=> Bool" (o |- "true as Bool" <=> "Bool");
  check "inl(0) as (Nat + Unit) <=> Nat + Unit"
    (o |- "inl(0) as (Nat + Unit)" <=> "Nat + Unit");
  check "inr(unit) as (Nat + Unit) <=> Nat + Unit"
    (o |- "inr(unit) as (Nat + Unit)" <=> "Nat + Unit");
  check "<| a = 0 |> as <| a : Nat, b : Bool |> <=> <| a : Nat, b : Bool |>"
    (o |- "<| a = 0 |> as <| a : Nat, b : Bool |>" <=> "<| a : Nat, b : Bool |>");
  check "<| b = false |> as <| a : Nat, b : Bool |> <=> <| a : Nat, b : Bool |>"
    (o |- "<| b = false |> as <| a : Nat, b : Bool |>"
   <=> "<| a : Nat, b : Bool |>")

let () =
  Alcotest.run "Typecheck"
    [
      ( "basic-typecheck",
        [
          Alcotest.test_case "Basic types" `Quick test_basic;
          Alcotest.test_case "Parametrized types" `Quick test_parametrized;
          Alcotest.test_case "Nested types" `Quick test_nested;
          Alcotest.test_case "Basic operations" `Quick test_operations;
        ] );
      ("function-typecheck", []);
      ("basic-errors", []);
      ("match-typecheck", []);
      ("extensions", []);
    ]
