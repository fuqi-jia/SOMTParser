enum LINKS = {a,b,c};
array[LINKS] of int: unused_x = array1d(LINKS, reverse(1..card(LINKS)));
constraint unused_x[a] = 3 /\ unused_x[b] = 2 /\ unused_x[c] = 1;
solve satisfy;
