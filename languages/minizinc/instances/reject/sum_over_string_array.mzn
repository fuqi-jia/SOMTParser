% String elements have no numeric coercion, including in empty arrays.
array[1..0] of string: words = [];
constraint sum(words) = 0;
solve satisfy;
