array[COLOR] of set of COLOR: allowed;
set of COLOR: selected;
string: label;
constraint Blue in allowed[Red] /\ not (Green in allowed[Red]);
constraint card(allowed[Green]) = 0 /\ Red in allowed[Blue];
constraint Red in selected /\ Blue in selected /\ not (Green in selected);
constraint label = "Red";
enum COLOR = {Red, Green, Blue};
solve satisfy;
