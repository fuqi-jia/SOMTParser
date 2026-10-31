array[-1..1] of int: table = array1d(-1..1, [7, 11, 7]);
var -1..1: i;
constraint table[i] = 7;
constraint nvalue([table[i], table[-i]]) = 1;
solve satisfy;
