Nat::rec (n,
{
  0, 0
}
, fn (k : Nat)
{
  return fn (p :
  {
    Nat, Nat
  }
  )
  {
    return
    {
      succ (p . 1), p . 1
    }
  }
}
) . 2
Nat::rec (n,
{
  0, 0
}
, fn (k : Nat)
{
  return fn (p :
  {
    Nat, Nat
  }
  )
  {
    return
    {
      succ (p . 1), p . 1
    }
  }
}
)
fn (k : Nat)
{
  return fn (p :
  {
    Nat, Nat
  }
  )
  {
    return
    {
      succ (p . 1), p . 1
    }
  }
}
{
  0, 0
}
0
0
n
fn (m : Nat)
{
  return Nat::rec (m, n, fn (k : Nat)
  {
    return dec
  }
  )
}
fn (n : Nat)
{
  return fn (m : Nat)
  {
    return if Nat::iszero (n) then 0 else succ (div (sub (n) (m)) (m))
  }
}
fn (m : Nat)
{
  return if Nat::iszero (m) then panic! else fix (mkdiv) (n) (m)
}
div (n) (n)
n
div (n)
n
div
