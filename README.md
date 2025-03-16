Stella Language Implementation in OCaml
======

Build and run
```bash
dune exec stella typecheck test/HelloYogurt.stella
```
Tested on OCaml 4.14.1 and dune 3.17.2.

## Current state
- Basic typecheck works (but not tested fully on corner-cases);
- #natural-literals is fully supported (not tested);
- #nested-functions-declarations not supported;
- #nullary-functions and #multiparameter-functions mostly not supported, but code trying to be agnostic if possible;
- #structural-patterns supported except duplicate fields error;
- #nullary-variant-labels - like nullary functions, code is agnostic, but probably not everywhere supportted;
- #letrec-bindings - not supported at all.

Note:
- ERROR_AMBIGUOUS_LIST in doc vs ERROR_AMBIGUOUS_LIST_TYPE in reference implementation; in this implementation is using first error name;
- extensions don't checked now, we're assume that extension check is always succeed.

## TODO List:
- [x] Error messages for all types of errors
- [x] Equal / NotEqual errors (they actually only Nat)
- [x] Variant typecheck
- [x] Record typecheck
- [x] Match
- [x] Duplicate fields
- [ ] Tests (basic ready)
- [x] Match exhaustivness check
- [ ] #nullary-functions and #multiparameter-functions
- [ ] #letrec-bindings with #pattern-ascriptions
- [ ] #let-many-bindings