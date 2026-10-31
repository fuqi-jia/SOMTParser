% The model half of a two-file instance: it declares the parameters and uses
% them BEFORE the instance file assigns them. That order is the point of the
% fixture -- a single pass that needed the value where it is used would refuse
% a legal model, which is a different class of wrong from declining a
% construct.
int: n;
array[1..n] of var 1..n: q;

constraint forall(i in 1..n, j in i+1..n)(q[i] != q[j]);

solve satisfy;
