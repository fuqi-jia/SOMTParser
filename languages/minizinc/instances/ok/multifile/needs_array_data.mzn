% A parameter ARRAY whose value arrives from the data file.
%
% `int: n;` and `array[1..3] of int: w;` are the same statement about where a
% value comes from, and a frontend that reads the first from a `.dzn` and
% refuses the second has read the data file and then declined to use it.
%
% `w[2]` is used as a bound rather than being merely declared, so the
% translated text carries the value: it distinguishes "the data was read" from
% "the data was accepted and ignored".
array[1..3] of int: w;
var 0..10: x;
constraint x > w[2];
solve satisfy;
