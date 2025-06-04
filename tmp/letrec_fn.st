n
letrec f as fn (Nat) -> Nat = fn (a : Nat)
{
  return if Nat::iszero (a) then 0 else f (a)
}
in f (0)
f (0)
0
f
fn (a : Nat)
{
  return if Nat::iszero (a) then 0 else f (a)
}
LetRec ([APatternBinding (PatternAsc (PatternVar (StellaIdent "f"), TypeFun ([TypeNat], TypeNat)), Abstraction ([AParamDecl (StellaIdent "a", TypeNat)], If (IsZero (Var (StellaIdent "a")), ConstInt (0), Application (Var (StellaIdent "f"), [Var (StellaIdent "a")]))))], Application (Var (StellaIdent "f"), [ConstInt (0)]))
