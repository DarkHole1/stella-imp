n
letrec length as fn ([Nat]) -> Nat = fn (xs : [Nat])
{
  return if List::isempty (xs) then 0 else succ (length (List::tail (xs)))
}
in let list = cons (0, cons (0, [])) in length (list)
let list = cons (0, cons (0, [])) in length (list)
length (list)
list
length
cons (0, cons (0, []))
cons (0, [])
[]
0
0
fn (xs : [Nat])
{
  return if List::isempty (xs) then 0 else succ (length (List::tail (xs)))
}
LetRec ([APatternBinding (PatternAsc (PatternVar (StellaIdent "length"), TypeFun ([TypeList (TypeNat)], TypeNat)), Abstraction ([AParamDecl (StellaIdent "xs", TypeList (TypeNat))], If (IsEmpty (Var (StellaIdent "xs")), ConstInt (0), Succ (Application (Var (StellaIdent "length"), [Tail (Var (StellaIdent "xs"))])))))], Let ([APatternBinding (PatternVar (StellaIdent "list"), ConsList (ConstInt (0), ConsList (ConstInt (0), List ([]))))], Application (Var (StellaIdent "length"), [Var (StellaIdent "list")])))
