array[1..2, 1..2] of int: matrix;
var int: x;
constraint x = matrix[1, 1];
solve satisfy;
