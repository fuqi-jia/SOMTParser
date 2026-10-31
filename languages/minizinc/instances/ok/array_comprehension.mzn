int: marks = 3;

array[1..marks] of var 0..6: mark;
array[int] of var 0..6: differences =
    [mark[j] - mark[i] | i in 1..marks, j in i + 1..marks];

constraint mark[1] = 0;
constraint forall (i in 1..marks - 1) (mark[i] < mark[i + 1]);
constraint differences[1] != differences[2];
constraint differences[1] != differences[3];
constraint differences[2] != differences[3];
constraint differences[1] < differences[3];

solve minimize mark[marks];
