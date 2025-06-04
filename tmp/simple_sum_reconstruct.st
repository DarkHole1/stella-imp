if first then inl (succ (0)) else inr (unit)
inr (unit)
unit
inl (succ (0))
succ (0)
0
first
match test (input)
{
  inl (n) => n | inr (_) => 0
}
n
0
test (input)
input
test
ERROR_UNEXPECTED_INJECTION
  ожидался тип
    ?T1
  но получена инъекция в выражении
    inl (succ (0))
