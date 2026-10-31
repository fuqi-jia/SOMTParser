% `if c then a else b endif`, in both of its readings.
%
% The first two constraints have FIXED tests and fold here: the branch the
% test excludes is skipped without being elaborated. The third has a test on
% a decision variable and becomes an ite term whose definedness obligation
% follows the selected branch only.
int: k = 3;

array[1..3] of var 0..9: a;
var int: q;

constraint if k = 3 then a[1] = 1 else a[1] = 99 endif;

constraint if k = 1 then a[2] = 11
           elseif k = 3 then a[2] = 7
           else a[2] = 55 endif;

% `div` is partial. Only the branch the test selects has to be defined, so the
% nonzero guard belongs under the conditional rather than asserted outright.
constraint q = if a[3] != 0 then 100 div a[3] else 0 endif;

% An omitted `else` on a Bool branch is `true` by the specification.
constraint if k = 9 then a[3] = 0 endif;

solve satisfy;
