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

  check_err "true ; 0 <=> Nat" E.unexpected_type_for_expression
    (o |- "true ; 0" <=> "Nat");
  check_err "0 ; true <=> Bool" E.unexpected_type_for_expression
    (o |- "0 ; true" <=> "Bool");
  check_err "[unit] ; [{0, unit}] <=> [{Nat, Unit}]" E.unexpected_list
    (o |- "[unit] ; [{0, unit}]" <=> "[{Nat, Unit}]")

let test_ref () =
  check "new (0) <=> & Nat" (o |- "new (0)" <=> "& Nat");
  check "new (true) <=> & Bool" (o |- "new (true)" <=> "& Bool");
  check "new ({0, true}) <=> & {Nat, Bool}"
    (o |- "new ({0, true})" <=> "& {Nat, Bool}");

  check "<0x00> <= & Nat" (o |- "<0x00>" <= "& Nat");
  check "<0x00> <= & Bool" (o |- "<0x00>" <= "& Bool");
  check "<0x00> <= & <|l : Bool|>" (o |- "<0x00>" <= "& <|l : Bool|>");

  check_err "<0x00> => & Nat" E.ambiguous_reference_type
    (o |- "<0x00>" => "& Nat");

  check "*(new (0)) <=> Nat" (o |- "*(new (0))" <=> "Nat");
  check "*(new (true)) <=> Bool" (o |- "*(new (true))" <=> "Bool");
  check "*(new ({0, true})) <=> {Nat, Bool}"
    (o |- "*(new ({0, true}))" <=> "{Nat, Bool}");

  check_err "*true <=> Bool" E.not_a_reference (o |- "*true" <=> "Bool");
  check_err "*false <=> Bool" E.not_a_reference (o |- "*false" <=> "Bool");
  check_err "*0 <=> Nat" E.not_a_reference (o |- "*0" <=> "Nat");

  check "(new(0)) := 0 <=> Unit" (o |- "(new(0)) := 0" <=> "Unit");
  check "(new(true)) := false <=> Unit" (o |- "(new(true)) := false" <=> "Unit");
  check "(new([unit])) := [unit, unit] <=> Unit"
    (o |- "(new([unit])) := [unit, unit]" <=> "Unit");

  check_err "(new(0)) := [false] <=> Unit" E.unexpected_list
    (o |- "(new(0)) := [false]" <=> "Unit");
  check_err "(new(true)) := [false] <=> Unit" E.unexpected_list
    (o |- "(new(true)) := [false]" <=> "Unit");
  check_err "(new([unit])) := [false] <=> Unit" E.unexpected_type_for_expression
    (o |- "(new([unit])) := [false]" <=> "Unit");

  check_err "0 := 0 <=> Unit" E.not_a_reference (o |- "0 := 0" <=> "Unit");
  check_err "true := false <=> Unit" E.not_a_reference
    (o |- "true := false" <=> "Unit");
  check_err "[unit] := [unit, unit] <=> Unit" E.not_a_reference
    (o |- "[unit] := [unit, unit]" <=> "Unit")

let test_panic () =
  check "panic! <= Bool" (o |- "panic!" <= "Bool");
  check "panic! <= Nat" (o |- "panic!" <= "Nat");
  check "panic! <= {Bool, Nat}" (o |- "panic!" <= "{Bool, Nat}");

  check_err "panic! => Bool" E.ambiguous_panic_type (o |- "panic!" => "Bool")

let test_errors () =
  let test ty tyv =
    let open Make (struct
      let structural_subtyping = false
      let ambiguous_types_as_bottom = false
      let exception_type = Some ty
      let reconstruction = false
    end) in
    check
      ("(" ^ ty ^ ") throw (" ^ tyv ^ ") <= Nat")
      (o |- "throw (" ^ tyv ^ ")" <= "Nat");
    check
      ("(" ^ ty ^ ") throw (" ^ tyv ^ ") <= Bool")
      (o |- "throw (" ^ tyv ^ ")" <= "Bool");
    check
      ("(" ^ ty ^ ") throw (" ^ tyv ^ ") <= {a : {Bool, Nat}}")
      (o |- "throw (" ^ tyv ^ ")" <= "{a : {Bool, Nat}}");

    check_err
      ("(" ^ ty ^ ") throw (" ^ tyv ^ ") => Nat")
      E.ambiguous_throw_type
      (o |- "throw (" ^ tyv ^ ")" => "Nat");

    check
      ("(" ^ ty ^ ") try { 0 } with { 0 } <=> Nat")
      (o |- "try { 0 } with { 0 }" <=> "Nat");
    check
      ("(" ^ ty ^ ") try { true } with { false } <=> Bool")
      (o |- "try { true } with { false }" <=> "Bool");
    check
      ("(" ^ ty ^ ") try { throw(" ^ tyv ^ ") } with { false } <= Bool")
      (o |- "try { throw(" ^ tyv ^ ") } with { false }" <= "Bool");
    check
      ("(" ^ ty ^ ") try { throw(" ^ tyv ^ ") } catch { _ => false } <= Bool")
      (o |- "try { throw(" ^ tyv ^ ") } catch { _ => false }" <= "Bool")
  in
  test "Nat" "0";
  test "Nat" "succ(0)";
  test "Nat" "Nat::pred(0)";
  test "Bool" "true";
  test "{Bool, Unit, Nat}" "{not (true), unit, {0, true}.1}"

let test_subtyping () =
  let open Make (struct
    let structural_subtyping = true
    let ambiguous_types_as_bottom = false
    let exception_type = None
    let reconstruction = false
  end) in
  check "true <=> Bool" (o |- "true" <=> "Bool");
  check "false <=> Bool" (o |- "false" <=> "Bool");
  check "0 <=> Nat" (o |- "0" <=> "Nat");
  check "unit <=> Unit" (o |- "unit" <=> "Unit");

  check_err "true <= Nat" E.unexpected_subtype (o |- "true" <= "Nat");
  check_err "false <= Nat" E.unexpected_subtype (o |- "false" <= "Nat");
  check_err "0 <= Bool" E.unexpected_subtype (o |- "0" <= "Bool");
  check_err "0 <= Unit" E.unexpected_subtype (o |- "0" <= "Unit");

  check "{ a = 0, b = false, c = unit } <= { a : Nat }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ a : Nat }");
  check "{ a = 0, b = false, c = unit } <= { b : Bool }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ b : Bool }");
  check "{ a = 0, b = false, c = unit } <= { c : Unit }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ c : Unit }");
  check "{ a = 0, b = false, c = unit } <= { b : Bool, a : Nat }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ b : Bool, a : Nat }");
  check "{ a = 0, b = false, c = unit } <= { c : Unit, a : Nat }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ c : Unit, a : Nat }");
  check "{ a = 0, b = false, c = unit } <= { b : Bool, a : Nat }"
    (o |- "{ a = 0, b = false, c = unit }" <= "{ b : Bool, a : Nat }");
  check
    "{ a = 0, b = false, c = unit } as { a : Nat, b : Bool, c : Unit } <= { c \
     : Unit, a : Nat, b : Bool }"
    (o |- "{ a = 0, b = false, c = unit } as { a : Nat, b : Bool, c : Unit }"
   <= "{ c : Unit, a : Nat, b : Bool }");

  check "<| a = 0 |> as <| a : Nat |> <= <| a : Nat, b : Unit |>"
    (o |- "<| a = 0 |> as <| a : Nat |>" <= "<| a : Nat, b : Unit |>");
  check "<| b = unit |> as <| b : Unit |> <= <| a : Nat, b : Unit |>"
    (o |- "<| b = unit |> as <| b : Unit |>" <= "<| a : Nat, b : Unit |>");
  check "x <= <| a : { a : Nat }, b : Unit |>"
    ([ ("x", "<| a : { a : Nat, b : Bool } |>") ]
    |- "x" <= "<| a : { a : Nat }, b : Unit |>");

  check "0 <= Top" (o |- "0" <= "Top");
  check "unit <= Top" (o |- "unit" <= "Top");
  check "true <= Top" (o |- "true" <= "Top");
  check "{0, true} <= Top" (o |- "{0, true}" <= "Top");

  check "x <= Nat" ([ ("x", "Bot") ] |- "x" <= "Nat");
  check "x <= Bool" ([ ("x", "Bot") ] |- "x" <= "Bool");
  check "x <= Unit" ([ ("x", "Bot") ] |- "x" <= "Unit");
  check "x <= {a : Nat}" ([ ("x", "Bot") ] |- "x" <= "{a : Nat}");
  check "x <= {Bool, Unit}" ([ ("x", "Bot") ] |- "x" <= "{Bool, Unit}")

let test_ambiguous_as_bottom () =
  let open Make (struct
    let structural_subtyping = true
    let ambiguous_types_as_bottom = true
    let exception_type = Some "Unit"
    let reconstruction = false
  end) in
  check "inl (true) => Bool + Bot" (o |- "inl (true)" => "Bool + Bot");
  check "inr (true) => Bot + Bool" (o |- "inr (true)" => "Bot + Bool");
  check "[] => [Bot]" (o |- "[]" => "[Bot]");
  check "panic! => Bot" (o |- "panic!" => "Bot");
  check "throw (unit) => Bot" (o |- "throw (unit)" => "Bot");
  check "<0x00> => & Bot" (o |- "<0x00>" => "& Bot")

let test_variant_exceptions () =
  let open Make (struct
    let structural_subtyping = false
    let ambiguous_types_as_bottom = false
    let exception_type = Some "<| a : Unit, b : Nat |>"
    let reconstruction = false
  end) in
  check "throw (<| a = unit |>) <= Unit"
    (o |- "throw (<| a = unit |>)" <= "Unit");
  check "throw (<| b = 0 |>) <= Unit" (o |- "throw (<| b = 0 |>)" <= "Unit")

let test_unify () =
  let unify = TC.unify in
  let unify =
   fun (tys : string list) ->
    List.map
      (fun s ->
        let s' = String.split_on_char '=' s in
        let a, b = (List.hd s', List.tl s' |> List.hd) in
        (parse_string_typeT a, parse_string_typeT b))
      tys
    |> unify
  in
  let check = Alcotest.check typeT in
  let check_unify (msg : string) (x : string) (res : string) tys =
    let sigma = unify tys in
    let x' = Stella.AbsStella.TypeVar (StellaIdent x) in
    let res' = parse_string_typeT res in
    check msg res' (sigma x')
  in
  let check_not_unify (msg : string) tys =
    Alcotest.match_raises msg E.common (fun () ->
        let sigma = unify tys in
        ignore sigma)
  in
  (* Sanity check *)
  check_unify "X = Nat" "X" "Nat" [ "X = Nat" ];
  check_not_unify "Y = fn(Y) -> Y" [ "Y = fn(Y) -> Y" ];

  check_unify "X = Bool" "X" "Bool" [ "X = Bool" ];
  check_unify "X = Unit" "X" "Unit" [ "X = Unit" ];
  check_unify "Bool = X" "X" "Bool" [ "Bool = X" ];
  check_unify "Nat = X" "X" "Nat" [ "Nat = X" ];

  check_unify "X = Y, Y = X, Y = Nat" "X" "Nat" [ "X = Y"; "Y = X"; "Y = Nat" ];
  check_unify "X = Y, Y = Z, Unit = Z" "X" "Unit"
    [ "X = Y"; "Y = Z"; "Unit = Z" ];

  check_unify "[X] = [Nat]" "X" "Nat" [ "[X] = [Nat]" ];
  check_unify "[Nat] = [X]" "X" "Nat" [ "[X] = [Nat]" ];
  check_unify "[[X]] = [[Nat]]" "X" "Nat" [ "[[X]] = [[Nat]]" ];
  check_not_unify "[Nat] = [[X]]" [ "[Nat] = [[X]]" ];

  check_unify "{X, Nat} = {Bool, Y}" "X" "Bool" [ "{X, Nat} = {Bool, Y}" ];
  check_unify "{X, Nat} = {Bool, Y}" "Y" "Nat" [ "{X, Nat} = {Bool, Y}" ];
  check_unify "{X, Nat} = {Bool, Y}" "Y" "{Nat, Nat}"
    [ "{X, {Nat, Nat}} = {Bool, Y}" ];

  check_unify "{x : X} = {x : Bool}" "X" "Bool" [ "{x : X} = {x : Bool}" ];
  check_unify "{x : X} = {x : { y : Bool }}" "X" "{y : Bool}"
    [ "{x : X} = {x : { y : Bool }}" ];
  check_not_unify "{x : X} = {x : { y : Bool }, y : Bool}"
    [ "{x : X} = {x : { y : Bool }, y : Bool}" ];
  check_not_unify "{x : X, y : Bool} = {x : { y : Bool }}"
    [ "{x : X, y : Bool} = {x : { y : Bool }}" ];

  check_unify "X + Bool = Nat + Y" "X" "Nat" [ "X + Bool = Nat + Y" ];
  check_unify "X + Bool = Nat + Y" "Y" "Bool" [ "X + Bool = Nat + Y" ];
  check_unify "X + X = Nat + Y" "Y" "Nat" [ "X + X = Nat + Y" ];
  check_unify "X + X = Y" "Y" "X + X" [ "X + X = Y" ];
  check_not_unify "X + Y = Y" [ "X + Y = Y" ];

  check_unify "X = { x : { Y, Z } }, [Y] = Z, { z : Z } = { z : [Unit] }" "X"
    "{ x : { Unit, [Unit] }}"
    [ "X = { x : { Y, Z } }"; "[Y] = Z"; "{ z : Z } = { z : [Unit] }" ];

  check_unify "X = Bool" "X" "Bool" [ "X = Bool" ]

let test_reconstruction () =
  let check' = Alcotest.check typeT in
  let check_rec (msg : string) (s : string) (ty : string) (l : string)
      (r : string) =
    let open Make (struct
      let structural_subtyping = false
      let ambiguous_types_as_bottom = false
      let exception_type = None
      let reconstruction = false
    end) in
    let var = Stella.AbsStella.(TypeVar (StellaIdent (fresh_var ()))) in
    let ctx = Stella.Context.from_var s var in
    typecheck ctx l r;
    let sigma = TC.unify !restrictions in
    check' msg (parse_string_typeT ty) (sigma var)
  in
  let infer_rec (msg : string) (s : string) (ty : string) (l : string) =
    let open Make (struct
      let structural_subtyping = false
      let ambiguous_types_as_bottom = false
      let exception_type = None
      let reconstruction = false
    end) in
    let var = Stella.AbsStella.(TypeVar (StellaIdent (fresh_var ()))) in
    let ctx = Stella.Context.from_var s var in
    infer ctx l |> ignore;
    let sigma = TC.unify !restrictions in
    check' msg (parse_string_typeT ty) (sigma var)
  in
  let both_rec (msg : string) (s : string) (ty : string) (l : string)
      (r : string) =
    check_rec msg s ty l r;
    infer_rec msg s ty l
  in
  (* Sanity check *)
  both_rec "succ(x)" "x" "Nat" "succ(x)" "Nat";

  both_rec "if x then 0 else 0" "x" "Bool" "if x then 0 else 0" "Nat";
  both_rec "if true then x else 0" "x" "Nat" "if true then x else 0" "Nat";
  both_rec "if true then unit else x" "x" "Unit" "if true then unit else x"
    "Unit";

  both_rec "x < 0" "x" "Nat" "x < 0" "Bool";
  both_rec "0 < x" "x" "Nat" "0 < x" "Bool";
  both_rec "x <= 0" "x" "Nat" "x <= 0" "Bool";
  both_rec "0 <= x" "x" "Nat" "0 <= x" "Bool";
  both_rec "x > 0" "x" "Nat" "x > 0" "Bool";
  both_rec "0 > x" "x" "Nat" "0 > x" "Bool";
  both_rec "x >= 0" "x" "Nat" "x >= 0" "Bool";
  both_rec "0 >= x" "x" "Nat" "0 >= x" "Bool";
  both_rec "x == 0" "x" "Nat" "x == 0" "Bool";
  both_rec "0 == x" "x" "Nat" "0 == x" "Bool";
  both_rec "x != 0" "x" "Nat" "x != 0" "Bool";
  both_rec "0 != x" "x" "Nat" "0 != x" "Bool";

  both_rec "x as Nat" "x" "Nat" "x as Nat" "Nat";
  both_rec "x as Bool" "x" "Bool" "x as Bool" "Bool";

  both_rec "[x, 0]" "x" "Nat" "[x, 0]" "[Nat]";
  both_rec "[unit, x]" "x" "Unit" "[unit, x]" "[Unit]";

  both_rec "x + 0" "x" "Nat" "x + 0" "Nat";
  both_rec "0 + x" "x" "Nat" "0 + x" "Nat";
  both_rec "x - 0" "x" "Nat" "x - 0" "Nat";
  both_rec "0 - x" "x" "Nat" "0 - x" "Nat";
  both_rec "x or false" "x" "Bool" "x or false" "Bool";
  both_rec "false or x" "x" "Bool" "false or x" "Bool";
  both_rec "x * 0" "x" "Nat" "x * 0" "Nat";
  both_rec "0 * x" "x" "Nat" "0 * x" "Nat";
  both_rec "x / 0" "x" "Nat" "x / 0" "Nat";
  both_rec "0 / x" "x" "Nat" "0 / x" "Nat";
  both_rec "x and true" "x" "Bool" "x and true" "Bool";
  both_rec "true and x" "x" "Bool" "true and x" "Bool";

  both_rec "succ(x(0))" "x" "fn (Nat) -> Nat" "succ(x(0))" "Nat";
  both_rec "succ(x.y)" "x" "{ y : Nat }" "succ(x.y)" "Nat";
  both_rec "x.1;succ(x.2)" "x" "{ Unit, Nat }" "x.1;succ(x.2)" "Nat";

  both_rec "succ({ x = x, y = 0}.x)" "x" "Nat" "succ({ x = x, y = 0}.x)" "Nat";
  both_rec "succ({ 0, x }.2)" "x" "Nat" "succ({ 0, x }.2)" "Nat";

  both_rec "succ(fix(x)(unit))" "x" "fn (fn (Unit) -> Nat) -> fn (Unit) -> Nat"
    "succ(fix(x)(unit))" "Nat";
  both_rec
    "Nat::rec(x, unit, fn (x : Nat) { return fn (y : Unit) { return y } })" "x"
    "Nat"
    "Nat::rec(x, unit, fn (x : Nat) { return fn (y : Unit) { return y } })"
    "Unit";

  check_rec "succ(x)" "x" "Nat" "succ(x)" "Nat"

let test_bugs () =
  let open Make (struct
    let structural_subtyping = true
    let ambiguous_types_as_bottom = false
    let exception_type = Some "Top"
    let reconstruction = false
  end) in
  check "throw(true) <= Top" (o |- "throw (true)" <= "Top");
  check "match (0) { x => x } <=> Nat" (o |- "match (0) { x => x }" <=> "Nat");
  check "match (fn (n : Nat) { return 0 }) { x => 0 } <=> Nat"
    (o |- "match (fn (n : Nat) { return 0 }) { x => 0 }" <=> "Nat")
(* check "*(if Nat::iszero(n) then <0x01> else <0x02>) <= Nat"
    (o |- "*(if Nat::iszero(n) then <0x01> else <0x02>)" <= "Nat") *)

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
          Alcotest.test_case "Subtyping" `Quick test_subtyping;
          Alcotest.test_case "Ambiguous as bottom" `Quick
            test_ambiguous_as_bottom;
          Alcotest.test_case "Variant errors" `Quick test_variant_exceptions;
        ] );
      ( "type variables",
        [
          Alcotest.test_case "Unify" `Quick test_unify;
          Alcotest.test_case "Unify" `Quick test_reconstruction;
        ] );
      ("bugs", [ Alcotest.test_case "Bugs" `Quick test_bugs ]);
    ]
