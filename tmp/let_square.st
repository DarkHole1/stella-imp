fn (m : Nat)
{
  return Nat::rec (n, m, fn (i : Nat)
  {
    return fn (r : Nat)
    {
      return succ (r)
    }
  }
  )
}
Nat::rec (n, 0, fn (i : Nat)
{
  return fn (r : Nat)
  {
    return let double = Nat::add (i) (i) in Nat::add (double) (succ (r))
  }
}
)
fn (i : Nat)
{
  return fn (r : Nat)
  {
    return let double = Nat::add (i) (i) in Nat::add (double) (succ (r))
  }
}
0
n
square (n)
n
square
