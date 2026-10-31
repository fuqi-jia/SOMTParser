include "disjunctive.mzn";
constraint disjunctive([0, 1], [3, 0]);
solve satisfy;
