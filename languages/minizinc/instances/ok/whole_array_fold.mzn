% Whole-array aggregation: sum(x) is sum(i in index_set(x))(x[i]) — the
% stdlib's array[$T] overloads (MiniZinc handbook 4.2.2.7), over decision
% arrays, parameter arrays, flattened grids and Boolean arrays alike.
int: n = 3;
array[1..n] of var 1..n: q;
array[1..n] of int: c = [1, 2, 3];
array[1..2, 1..2] of var 0..9: g;
array[1..n] of var bool: b;
constraint sum(q) <= 6;
constraint sum(c) + product(q) >= 7;
constraint sum(g) <= 100;
constraint exists(b) \/ forall(b);
solve satisfy;
