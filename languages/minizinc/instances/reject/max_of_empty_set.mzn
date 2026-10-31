% `max` of an empty set is undefined in MiniZinc: there is no element to
% return. Refused rather than given a sentinel, which would be a number the
% source never wrote. A real model guards this with a conditional on
% `index_set(x) = {}`, which folds before this is reached.
array[1..0] of int: none = [];
array[1..1] of var 0..99: r;
constraint r[1] = max(index_set(none));
solve satisfy;
