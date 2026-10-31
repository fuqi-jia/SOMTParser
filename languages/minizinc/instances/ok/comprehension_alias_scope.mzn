int: p = 99;
var int: total;
constraint total = sum([j | i in 1..3, p = 2*i where p >= 4, j in 1..p]) + p;
constraint total = 130;
solve satisfy;
