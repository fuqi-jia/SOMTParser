% Exact decimal/scientific constants and relational real division.
float: scale = 1.25e1;
var -2..2: offset;
var float: x;
var float: denominator;
var bool: use_ratio;

constraint x = scale / 2.0 + offset;
constraint use_ratio -> x / denominator = 1.0;
constraint not use_ratio;
constraint denominator = 0.0;

solve minimize x;
