% `index_set(a)` and the fixed-set folds.
%
% Sets are parse-time values in this subset, so these fold to numbers and to
% truth values rather than to terms. That is what lets the guard below decide
% its conditional at parse time -- and the guarded branch computes `max` of
% the set the guard just proved empty, which has no value at all.
array[3..7] of var 0..9: a;
array[1..0] of int: none = [];
array[1..4] of var 0..99: r;

constraint r[1] = min(index_set(a));
constraint r[2] = max(index_set(a));
constraint r[3] = card(index_set(a));

constraint if index_set(none) = {} then r[4] = 0
           else r[4] = max(index_set(none)) endif;

solve satisfy;
