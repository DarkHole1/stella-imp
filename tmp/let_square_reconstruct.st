fn (m : auto)
{
  return Nat::rec (n, m, fn (i : auto)
  {
    return fn (r : auto)
    {
      return succ (r)
    }
  }
  )
}
Nat::rec (n, 0, fn (i : auto)
{
  return fn (r : auto)
  {
    return let double = Nat::add (i) (i) in Nat::add (double) (succ (r))
  }
}
)
fn (i : auto)
{
  return fn (r : auto)
  {
    return let double = Nat::add (i) (i) in Nat::add (double) (succ (r))
  }
}
0
n
square (n)
n
square
ERROR_UNEXPECTED_LAMBDA
  ожидался тип
    ?T2
  но получена лямбда в выражении
    fn (m : ?T1)
    {
      return Nat::rec (n, m, fn (i : auto)
      {
        return fn (r : auto)
        {
          return succ (r)
        }
      }
      )
    }
