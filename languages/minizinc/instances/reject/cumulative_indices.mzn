array[2..3] of var int: start;
constraint cumulative(start, [1, 1], [1, 1], 2);
solve satisfy;
