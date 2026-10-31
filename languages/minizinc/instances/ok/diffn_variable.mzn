include "diffn.mzn";
array[4..5] of var 0..3: x;
array[4..5] of var 0..3: y;
array[4..5] of var 0..2: width;
array[4..5] of var 0..2: height;
constraint diffn(x,y,width,height);
solve satisfy;
