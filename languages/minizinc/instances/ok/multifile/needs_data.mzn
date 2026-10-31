int: n;
array[1..n] of var 1..n: q;
constraint forall(i in 1..n)(q[i] >= 1);
solve satisfy;
