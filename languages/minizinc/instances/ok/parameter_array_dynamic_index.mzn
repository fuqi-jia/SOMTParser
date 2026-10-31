array[4..5, -1..0] of int: duration = array2d(4..5, -1..0, [2, 7, 11, 19]);
var -1..0: predecessor;
constraint predecessor = 0;
constraint duration[5, predecessor] = 19;
solve satisfy;
