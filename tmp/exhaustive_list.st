match n
{
  [] => 0 | [a] => a | [a, b] => a | [a, b, c] => a | cons (1, xs) => 1 | cons (2, cons (3, xs)) => 2 | cons (a, cons (b, [1, 2])) => b | cons (a, cons (b, cons (c, cs))) => c
}
0
a
a
a
1
2
b
c
n
match n
{
  [] => 0 | cons (x, xs) => 0
}
0
0
n
