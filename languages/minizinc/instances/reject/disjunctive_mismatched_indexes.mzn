include "disjunctive.mzn";
array[1..2] of var int: s;
array[2..3] of var int: d;
constraint disjunctive(s, d);
solve satisfy;
