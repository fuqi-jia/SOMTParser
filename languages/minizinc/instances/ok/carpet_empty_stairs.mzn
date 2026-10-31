set of int: Stairs = 1..0;
array[Stairs] of int: steps = [];
array[Stairs] of int: offsets = [sum(j in Stairs where j<i)(steps[j]) | i in Stairs];
array[Stairs] of set of int: rectangles = [(offsets[i]+1)..(offsets[i]+steps[i]) | i in Stairs];
array[1..0] of int: widths = [steps[i] | i in Stairs,j in rectangles[i]];
constraint forall(i in Stairs)(let {set of int:J=1..steps[i],array[J] of var bool:last} in last[steps[i]]);
solve satisfy;
