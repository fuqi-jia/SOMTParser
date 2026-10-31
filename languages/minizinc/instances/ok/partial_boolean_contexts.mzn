array[1..1] of var bool: a;
var 2..2: i;
var 0..0: x;

constraint not a[i];
constraint not (10 div x = 10);
constraint (10 div x = 10) -> false;

solve satisfy;
