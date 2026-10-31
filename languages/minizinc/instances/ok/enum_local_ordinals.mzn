enum FIRST = {F0, F1};
enum SECOND = {S0, S1, S2};
array[SECOND] of var SECOND: selected;
constraint forall(i in SECOND)(selected[i] = i);
constraint enum2int(selected[S1]) = 2;
constraint enum2int(F1) = 2;
solve satisfy;
