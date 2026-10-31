array[1..3] of var 1..2: a;
constraint forall(g in 1..2)
  (let {var 1..3: c} in count(a,g,c));
solve satisfy;
