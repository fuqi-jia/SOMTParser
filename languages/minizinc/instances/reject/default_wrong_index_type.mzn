array[1..2,1..2] of var int: a;
constraint (a[0,true] default 7) = 7;
solve satisfy;
