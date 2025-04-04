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

  check "List::head ([0, 0]) <=> Nat" (o |- "List::head ([0, 0])" <=> "Nat");
  check "List::tail ([true, false]) <=> [Bool]"
    (o |- "List::tail ([true, false])" <=> "[Bool]");
  check "List::isempty ([unit]) <=> Bool"
    (o |- "List::isempty ([unit])" <=> "Bool");

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
(* check "{ a = 0, b = true } as { b : Bool, a : Nat } <=> { a : Nat, b : Bool }"
    (o |- "{ a = 0, b = true } as { b : Bool, a : Nat }"
   <=> "{ a : Nat, b : Bool }") *)

let test_functions () =
  check "fn (x : Nat) { return x } <=> fn (Nat) -> Nat"
    (o |- "fn (x : Nat) { return x }" <=> "fn (Nat) -> Nat");
  check "fn (x : Nat) { return false } <=> fn (Nat) -> Bool"
    (o |- "fn (x : Nat) { return false }" <=> "fn (Nat) -> Bool");
  check "fn (x : Nat + Bool) { return x } <=> fn (Nat + Bool) -> Nat + Bool"
    (o |- "fn (x : Nat + Bool) { return x }" <=> "fn (Nat + Bool) -> Nat + Bool");
  check "(fn (x : Nat) { return x }) (0) <=> Nat"
    (o |- "(fn (x : Nat) { return x }) (0)" <=> "Nat");
  check "fix (fn (x : Nat) { return x }) <=> Nat"
    (o |- "fix (fn (x : Nat) { return x })" <=> "Nat");
  check
    "Nat::rec(0, unit, fn (_: Nat) { return fn (x : Unit) { return x; }}) <=> \
     Unit"
    (o |- "Nat::rec(0, unit, fn (_ : Nat) { return fn (x : Unit) { return x }})"
   <=> "Unit")

let test_basic_errors () =
  check_err "unexpected variable" E.undefined_variable (o |- "x" <=> "Bool");
  check_err "not a function (call)" E.not_a_function
    (o |- "(true) ()" <=> "Bool");
  check_err "not a function (fix)" E.not_a_function (o |- "fix(0)" <=> "Nat");
  check_err "not a tuple" E.not_a_tuple (o |- "unit . 1" <=> "Unit");
  check_err "not a record" E.not_a_record (o |- "0 . a" <=> "Nat");
  check_err "not a list (head)" E.not_a_list (o |- "List::head (0)" <=> "Nat");
  check_err "not a list (tail)" E.not_a_list
    (o |- "List::tail (unit)" <=> "[Unit]");
  check_err "not a list (isempty)" E.not_a_list
    (o |- "List::isempty (true)" <=> "Bool");
  check_err "unexpected lambda" E.unexpected_lambda
    (o |- "fn (a : Nat) { return b }" <= "Unit");
  check_err "unexpected type for parameter" E.unexpected_type_for_parameter
    (o |- "fn (a : Unit) { return b }" <= "fn (Nat) -> Nat");
  check_err "unexpected tuple" E.unexpected_tuple (o |- "{0, 0, 0}" <= "Nat");
  check_err "unexpected record" E.unexpected_record
    (o |- "{ foo = 0, bar = false }" <= "Bool");
  check_err "unexpected variant" E.unexpected_variant
    (o |- "<| abryvalg = unit |>" <= "Unit");
  check_err "unexpected list" E.unexpected_list (o |- "[0, 0]" <= "Nat");
  check_err "unexpected injection (left)" E.unexpected_injection
    (o |- "inl(true)" <= "Bool");
  check_err "unexpected injection (right)" E.unexpected_injection
    (o |- "inr(0)" <= "Nat");
  check_err "missing record fields 1" E.missing_record_fields
    (o |- "{bar = unit}" <= "{ foo : Nat, bar : Unit }");
  check_err "missing record fields 2" E.missing_record_fields
    (o |- "{foo = 0}" <= "{ foo : Nat, bar : Unit }");
  check_err "unexpected record fields 1" E.unexpected_record_fields
    (o |- "{foo = 0, baz = unit}" <= "{ foo : Nat }");
  check_err "unexpected record fields 2" E.unexpected_record_fields
    (o |- "{foo = 0, baz = unit}" <= "{ baz : Unit }");
  check_err "unexpected field access" E.unexpected_field_access
    (o |- "{foo = true}.fo" <=> "Bool");
  check_err "unexpected variant label" E.unexpected_variant_label
    (o |- "<| foo = 0 |>" <= "<| fooo : Nat |>");
  check_err "ambiguous sum type (left)" E.ambiguous_sum_type
    (o |- "inl(true)" => "Bool + Unit");
  check_err "ambiguous sum type (right)" E.ambiguous_sum_type
    (o |- "inr(unit)" => "Bool + Unit");
  check_err "ambiguous variant type" E.ambiguous_variant_type
    (o |- "<| success = true |>" => "<| success : Bool |>");
  check_err "ambiguous list" E.ambiguous_list (o |- "[]" => "[Unit]");
  (* Empty and non-exhaustive matching and unexpected patter will be in match tests *)
  check_err "duplicate record fields" E.duplicate_record_fields
    (o |- "{ foo = 0, bar = unit, foo = 0 }" <=> "{ foo : Nat, bar : Unit }");
  (* Can't check types directly, instead checking them in all introducing types contextes *)
  check_err "duplicate record type fields 1" E.duplicate_record_type_fields
    (o |- "fn (x : { foo : Nat, foo : Nat }) { return x.foo }"
   => "fn ({ foo : Nat }) -> Nat");
  check_err "duplicate record type fields 2" E.duplicate_record_type_fields
    (o |- "{ foo = 0 } as { foo : Nat, foo : Nat }" => "{ foo : Nat }");
  check_err "duplicate record type fields 3" E.duplicate_record_type_fields
    (o |- "fn (x : [{ foo : Nat, foo : Nat }]) { return List::head(x).foo }"
   => "fn ([{ foo : Nat }]) -> Nat");
  check_err "duplicate record type fields 4" E.duplicate_record_type_fields
    (o |- "[{ foo = 0 }] as [{ foo : Nat, foo : Nat }]" => "[{ foo : Nat }]");
  check_err "duplicate record type fields 5" E.duplicate_record_type_fields
    (o |- "fn (x : <| bazz : { foo : Nat, foo : Nat } |>) { return x }"
   => "fn (<| bazz : { foo : Nat } |>) -> <| bazz : { foo : Nat } |>");
  check_err "duplicate record type fields 6" E.duplicate_record_type_fields
    (o |- "<| bazz = { foo = 0 } |> as <| bazz : { foo : Nat, foo : Nat } |>"
   => "<| bazz : { foo : Nat } |>");
  check_err "duplicate record type fields 7" E.duplicate_record_type_fields
    (o |- "fn (x : {Bool, { foo : Nat, foo : Nat }}) { return x.2.foo }"
   => "fn ({Bool, { foo : Nat }}) -> Nat");
  check_err "duplicate record type fields 8" E.duplicate_record_type_fields
    (o |- "{true, { foo = 0 }} as {Bool, { foo : Nat, foo : Nat }}"
   => "{Bool, { foo : Nat }}");
  check_err "duplicate record type fields 9" E.duplicate_record_type_fields
    (o |- "fn (x : Bool + { foo : Nat, foo : Nat }) { return 0 }"
   => "fn ({ foo : Nat }) -> Nat");
  check_err "duplicate record type fields 10" E.duplicate_record_type_fields
    (o |- "inl(true) as (Bool + { foo : Nat, foo : Nat })"
   => "Bool + { foo : Nat }");

  check_err "duplicate variant type fields 1" E.duplicate_variant_type_fields
    (o |- "fn (x : <| foo : Nat, foo : Nat |>) { return 0 }"
   => "fn (<| foo : Nat |>) -> Nat");
  check_err "duplicate variant type fields 2" E.duplicate_variant_type_fields
    (o |- "<| foo = 0 |> as <| foo : Nat, foo : Nat |>" => "<| foo : Nat |>");
  check_err "duplicate variant type fields 3" E.duplicate_variant_type_fields
    (o |- "fn (x : [<| foo : Nat, foo : Nat |>]) { return 0 }"
   => "fn ([<| foo : Nat |>]) -> Nat");
  check_err "duplicate variant type fields 4" E.duplicate_variant_type_fields
    (o |- "[<| foo = 0 |>] as [<| foo : Nat, foo : Nat |>]"
   => "[<| foo : Nat |>]");
  check_err "duplicate variant type fields 5" E.duplicate_variant_type_fields
    (o |- "fn (x : { bazz : <| foo : Nat, foo : Nat |> }) { return 0 }"
   => "fn ({ bazz : <| foo : Nat |> }) -> Nat");
  check_err "duplicate variant type fields 6" E.duplicate_variant_type_fields
    (o |- "{ bazz = <| foo = 0 |> } as { bazz : <| foo : Nat, foo : Nat |> }"
   => "{ bazz : <| foo : Nat |> }");
  check_err "duplicate variant type fields 7" E.duplicate_variant_type_fields
    (o |- "fn (x : {Bool, <| foo : Nat, foo : Nat |>}) { return 0 }"
   => "fn ({Bool, <| foo : Nat |>}) -> Nat");
  check_err "duplicate variant type fields 8" E.duplicate_variant_type_fields
    (o |- "{true, <| foo = 0 |>} as {Bool, <| foo : Nat, foo : Nat |>}"
   => "{Bool, <| foo : Nat |>}");
  check_err "duplicate variant type fields 9" E.duplicate_variant_type_fields
    (o |- "fn (x : Bool + <| foo : Nat, foo : Nat |>) { return 0 }"
   => "fn (Bool + <| foo : Nat |>) -> Nat");
  check_err "duplicate variant type fields 10" E.duplicate_variant_type_fields
    (o |- "inl(true) as (Bool + <| foo : Nat, foo : Nat |>)"
   => "Bool + <| foo : Nat |>")

let test_seq () =
  check "unit ; 0 <=> Nat" (o |- "unit ; 0" <=> "Nat");
  check "unit ; true <=> Bool" (o |- "unit ; true" <=> "Bool");
  check "unit ; [{0, unit}] <=> [{Nat, Unit}]"
    (o |- "unit ; [{0, unit}]" <=> "[{Nat, Unit}]");

  check_err "true ; 0 <=> Nat" E.common (o |- "true ; 0" <=> "Nat");
  check_err "0 ; true <=> Bool" E.common (o |- "0 ; true" <=> "Bool");
  check_err "[unit] ; [{0, unit}] <=> [{Nat, Unit}]" E.common
    (o |- "[unit] ; [{0, unit}]" <=> "[{Nat, Unit}]")

let test_ref () =
  check "new (0) <=> & Nat" (o |- "new (0)" <=> "& Nat");
  check "new (true) <=> & Bool" (o |- "new (true)" <=> "& Bool");
  check "new ({0, true}) <=> & {Nat, Bool}"
    (o |- "new ({0, true})" <=> "& {Nat, Bool}");

  check "<0x00> <= & Nat" (o |- "<0x00>" <= "& Nat");
  check "<0x00> <= & Bool" (o |- "<0x00>" <= "& Bool");
  check "<0x00> <= & <|l : Bool|>" (o |- "<0x00>" <= "& <|l : Bool|>");

  check_err "<0x00> => & Nat" E.common (o |- "<0x00>" => "& Nat");

  check "*(new (0)) <=> Nat" (o |- "*(new (0))" <=> "Nat");
  check "*(new (true)) <=> Bool" (o |- "*(new (true))" <=> "Bool");
  check "*(new ({0, true})) <=> {Nat, Bool}"
    (o |- "*(new ({0, true}))" <=> "{Nat, Bool}");

  check_err "*true <=> Bool" E.common (o |- "*true" <=> "Bool");
  check_err "*false <=> Bool" E.common (o |- "*false" <=> "Bool");
  check_err "*0 <=> Nat" E.common (o |- "*0" <=> "Nat");

  check "(new(0)) := 0 <=> Unit" (o |- "(new(0)) := 0" <=> "Unit");
  check "(new(true)) := false <=> Unit" (o |- "(new(true)) := false" <=> "Unit");
  check "(new([unit])) := [unit, unit] <=> Unit"
    (o |- "(new([unit])) := [unit, unit]" <=> "Unit");

  check_err "(new(0)) := [false] <=> Unit" E.common
    (o |- "(new(0)) := [false]" <=> "Unit");
  check_err "(new(true)) := [false] <=> Unit" E.common
    (o |- "(new(true)) := [false]" <=> "Unit");
  check_err "(new([unit])) := [false] <=> Unit" E.common
    (o |- "(new([unit])) := [false]" <=> "Unit");

  check_err "0 := 0 <=> Unit" E.common (o |- "0 := 0" <=> "Unit");
  check_err "true := false <=> Unit" E.common (o |- "true := false" <=> "Unit");
  check_err "[unit] := [unit, unit] <=> Unit" E.common
    (o |- "[unit] := [unit, unit]" <=> "Unit")

let test_panic () =
  check "panic! <= Bool" (o |- "panic!" <= "Bool");
  check "panic! <= Nat" (o |- "panic!" <= "Nat");
  check "panic! <= {Bool, Nat}" (o |- "panic!" <= "{Bool, Nat}");

  check_err "panic! => Bool" E.common (o |- "panic!" => "Bool")

let test_errors () =
  let test tyn tyv ty =
    let open Make (struct
      let ambiguous = raise
      let exception_type = Some ty
      let is_subtyping = false
      let eq = Stella.Typecheck.eq
    end) in
    check
      ("(" ^ tyn ^ ") throw (" ^ tyv ^ ") <= Nat")
      (o |- "throw (" ^ tyv ^ ")" <= "Nat");
    check
      ("(" ^ tyn ^ ") throw (" ^ tyv ^ ") <= Bool")
      (o |- "throw (" ^ tyv ^ ")" <= "Bool");
    check
      ("(" ^ tyn ^ ") throw (" ^ tyv ^ ") <= {a : {Bool, Nat}}")
      (o |- "throw (" ^ tyv ^ ")" <= "{a : {Bool, Nat}}");

    check_err
      ("(" ^ tyn ^ ") throw (" ^ tyv ^ ") => Nat")
      E.common
      (o |- "throw (" ^ tyv ^ ")" => "Nat");

    check
      ("(" ^ tyn ^ ") try { 0 } with { 0 } <=> Nat")
      (o |- "try { 0 } with { 0 }" <=> "Nat");
    check
      ("(" ^ tyn ^ ") try { true } with { false } <=> Bool")
      (o |- "try { true } with { false }" <=> "Bool");
    check
      ("(" ^ tyn ^ ") try { throw(" ^ tyv ^ ") } with { false } <= Bool")
      (o |- "try { throw(" ^ tyv ^ ") } with { false }" <= "Bool");
    check
      ("(" ^ tyn ^ ") try { throw(" ^ tyv ^ ") } catch { _ => false } <= Bool")
      (o |- "try { throw(" ^ tyv ^ ") } catch { _ => false }" <= "Bool")
  in
  test "Nat" "0" Stella.AbsStella.TypeNat;
  test "Nat" "succ(0)" Stella.AbsStella.TypeNat;
  test "Nat" "Nat::pred(0)" Stella.AbsStella.TypeNat;
  test "Bool" "true" Stella.AbsStella.TypeBool;
  test "{Bool, Unit, Nat}" "{not (true), unit, {0, true}.1}"
    Stella.AbsStella.(TypeTuple [ TypeBool; TypeUnit; TypeNat ])

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
      ( "function-typecheck",
        [ Alcotest.test_case "Functions test" `Quick test_functions ] );
      ( "basic-errors",
        [ Alcotest.test_case "Basic errors" `Quick test_basic_errors ] );
      ("match-typecheck", []);
      ( "extensions",
        [
          Alcotest.test_case "Sequencing" `Quick test_seq;
          Alcotest.test_case "References" `Quick test_ref;
          Alcotest.test_case "Panics" `Quick test_panic;
          Alcotest.test_case "Errors" `Quick test_errors;
        ] );
    ]
