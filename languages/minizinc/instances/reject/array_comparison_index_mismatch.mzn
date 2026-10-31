array[1..2,1..2] of int:a=[|1,2|3,4|];array[1..1,1..4] of int:b=array2d(1..1,1..4,[1,2,3,4]);constraint a=b;solve satisfy;
