Stella Language Implementation in OCaml
======

Build and run
```bash
dune exec stella typecheck test/HelloYogurt.stella
```
Tested on OCaml 4.14.1 and dune 3.17.2.

## TODO List:
- [x] Error messages for all types of errors (almost)
- [x] Equal / NotEqual errors (they actually only Nat)
- [x] Variant typecheck
- [x] Record typecheck
- [ ] Match
- [x] Duplicate fields (probably not perfect in infer)
- [ ] Tests
- [ ] #nullary-functions and #multiparameter-functions
- [ ] #letrec-bindings with #pattern-ascriptions
- [ ] #let-many-bindings