% The same data, declared over an index set that does NOT start at 1.
%
% The data uses `array1d` to carry the same non-1-based index set as this
% declaration. Plain `[3, 7, 5]` data is 1-based and would be rejected here.
%
% `w[2]` is deliberately checked: both the intended and a positional read are
% in bounds, but an indexing mistake would select a different data value.
array[0..2] of int: w;
var 0..10: x;
constraint x > w[2];
solve satisfy;
