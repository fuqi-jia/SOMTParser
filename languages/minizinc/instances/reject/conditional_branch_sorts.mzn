% A test on a decision variable keeps both branches, so they must meet at one
% sort. Int and Bool do not, and guessing a coercion here would answer a
% different question than the model asks.
array[1..2] of var 0..9: a;
constraint a[1] = if a[2] > 0 then 5 else true endif;
solve satisfy;
