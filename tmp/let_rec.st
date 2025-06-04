let y = let step = fn (i : Nat)
{
  return fn (cur : Nat)
  {
    return succ (cur)
  }
}
in Nat::rec (succ (0), 0, step) in y
y
let step = fn (i : Nat)
{
  return fn (cur : Nat)
  {
    return succ (cur)
  }
}
in Nat::rec (succ (0), 0, step)
Nat::rec (succ (0), 0, step)
step
0
succ (0)
0
fn (i : Nat)
{
  return fn (cur : Nat)
  {
    return succ (cur)
  }
}
