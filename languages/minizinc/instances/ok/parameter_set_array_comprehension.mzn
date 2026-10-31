array[1..2] of set of int: raw_colors = [{i} | i in {2, 1}];
array[4..5] of set of int: colors = array1d(4..5, raw_colors);
constraint 1 in colors[4];
constraint 2 in colors[5];
solve satisfy;
