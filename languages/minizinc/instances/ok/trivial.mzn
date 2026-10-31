% Smallest model that exercises a declaration, a bound, a constraint and an objective.
var 1..5: x;
constraint x > 2;
solve minimize x;
