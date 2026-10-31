var 0..10: x;
var bool: b;

constraint b -> 10 div x = 10;

solve minimize x;
