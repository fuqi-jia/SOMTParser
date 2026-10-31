int: n = abs(-2);
array[1..n] of var int: x;
constraint x[1] = -3 /\ x[2] = abs(x[1]);
constraint x[2] = 3;
solve satisfy;
