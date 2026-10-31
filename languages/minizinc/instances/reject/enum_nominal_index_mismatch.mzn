enum FIRST = {F0, F1};
enum SECOND = {S0, S1};
array[FIRST] of var int: values;
constraint values[S0] = 0;
solve satisfy;
