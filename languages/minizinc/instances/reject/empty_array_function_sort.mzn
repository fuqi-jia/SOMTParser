array[1..0] of string: values = [];
function bool: accepts_ints(array[int] of int: actual) = length(actual) = 0;
constraint accepts_ints(values);
solve satisfy;
