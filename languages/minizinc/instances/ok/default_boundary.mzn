array[1..3] of var 1..3: a;
constraint a[1] = 2;
constraint a[2] = 3;
constraint a[3] = 1;
constraint sum(i in 1..3)(a[i-1] default 0) = 5;
constraint (a[0] default 7) = 7;
solve satisfy;
