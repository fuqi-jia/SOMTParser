include "globals.mzn";
int: W = 2;
int: H = 2;
int: C = 2;
set of int: Colors = 1..C;
set of int: Width = 1..W;
set of int: Height = 1..H;
array[Width, Height] of var Colors: puzzle;
array[Width, Height] of var 0..C: across = array2d(Width, Height, [
    if puzzle[w-1,h] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
array[Width, Height] of var 0..C: down = array2d(Width, Height, [
    if puzzle[w,h-1] default 0 != puzzle[w,h] then puzzle[w,h] else 0 endif
    | w in Width, h in Height]);
constraint forall(h in Height) (
    global_cardinality(across[..,h], set2array({0} union Colors),
                       [W-C] ++ [1 | c in Colors]));
constraint forall(w in Width) (
    global_cardinality(down[w,..], set2array({0} union Colors),
                       [H-C] ++ [1 | c in Colors]));
array[int] of var int: diff_across = [
    let {
        array[int] of var int: counts = global_cardinality(puzzle[..,h], set2array(Colors));
        var int: minimum = min(counts);
        var int: maximum = max(counts);
    } in maximum - minimum | h in Height];
array[int] of var int: diff_down = [
    let {
        array[int] of var int: counts = global_cardinality(puzzle[w,..], set2array(Colors));
        var int: minimum = min(counts);
        var int: maximum = max(counts);
    } in maximum - minimum | w in Width];
constraint symmetry_breaking_constraint(value_precede_chain(Colors, array1d(puzzle)));
var int: objective = max(diff_across ++ diff_down);
solve minimize objective;
