array[4..5] of var int: x;
array[1..2] of var int: y;
constraint diffn(x,y,[1,1],[1,1]);
solve satisfy;
