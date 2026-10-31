array[1..1,0..3] of int: a;
a = array2d(1..1,0..3,[|11,12|21,22|]);
constraint a[1,0] = 11 /\ a[1,1] = 12 /\ a[1,2] = 21 /\ a[1,3] = 22;
solve satisfy;
