% Bool array elements coerce to 0/1 in numeric aggregates.
array[1..2] of var bool: b;
constraint sum(b) > 0;
solve satisfy;
