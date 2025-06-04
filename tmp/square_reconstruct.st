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
    return Nat::add (i) (Nat::add (i) (succ (r)))
  }
}
)
fn (i : auto)
{
  return fn (r : auto)
  {
    return Nat::add (i) (Nat::add (i) (succ (r)))
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
