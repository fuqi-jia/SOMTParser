% Declared over four indices, given three values.
%
% MiniZinc checks this, and what it prevents is not a type error but a wrong
% answer: the missing `w[4]` would be undefined, and an SMT-LIB array being
% total means "undefined" reads as "unconstrained" rather than as an error. The
% check already existed for a value written in the model; a value arriving from
% a data file must meet the same one.
array[1..4] of int: w;
var 0..10: x;
constraint x > w[2];
solve satisfy;
