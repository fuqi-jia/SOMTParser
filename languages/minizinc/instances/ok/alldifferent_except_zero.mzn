include "alldifferent_except_0.mzn";
array[1..2, 1..3] of var -2..2: x;
constraint forall(r in 1..2)(alldifferent_except_0(x[r,..]));
constraint x[1,1] = 0 /\ x[1,2] = 0 /\ x[1,3] = -2;
solve satisfy;
