if get_one? then <| value = 0 |> else <| failure = unit |>
<| failure = unit |>
unit
<| value = 0 |>
0
get_one?
match attempt (succeed)
{
  <| value = n |> => succ (n) | <| failure = f |> => 0
}
succ (n)
n
0
attempt (succeed)
succeed
attempt
