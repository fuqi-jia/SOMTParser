% A conditional that is never closed. Malformed input, so E_PARSE -- not
% E_UNSUPPORTED_CONSTRUCT, which is the bucket for a construct this subset has
% not implemented. The two feed different statistics.
int: k = 3;
array[1..1] of var 0..9: a;
constraint if k = 3 then a[1] = 1 else a[1] = 2;
solve satisfy;
