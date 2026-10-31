include "cycle_b.mzn";
int: n = 1;
var 1..n: x;
solve satisfy;
