array[3..4] of -1..1: from = array1d(3..4, [-1, 0]);
array[3..4] of -1..1: to = array1d(3..4, [0, 1]);
array[-1..1] of var bool: nodes;
array[3..4] of var bool: edges;
constraint connected(from, to, nodes, edges);
constraint not dconnected([1, 3], [2, 2], [true, true, true], [true, true]);
solve satisfy;
