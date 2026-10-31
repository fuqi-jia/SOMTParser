include "global_cardinality.mzn";
array[1..2] of var int: x;
array[4..5] of int: cover=array1d(4..5,[1,2]);
array[0..1] of var int: counts;
constraint global_cardinality(x,cover,counts);
solve satisfy;
