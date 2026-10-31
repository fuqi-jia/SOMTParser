array[1..2] of bool: flags = [true, false];
constraint numeric_total(flags) = 9;
function int: numeric_total(array[int] of int: values) =
    values[1] + values[2] + 8;

set of int: allowed = 1..2;
function var int: first(array[int] of var allowed: values) = values[1];
array[1..2] of var 1..3: values = [1, 3];
constraint not (first(values) = 1);
solve satisfy;
