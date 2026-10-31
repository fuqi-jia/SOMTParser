# A ghost cannot reuse a program variable's name (typecheck/std.ml:
# ghost_disjoint) -- the layers must stay apart.
proc main(uint8 x) =
{ true && true }
ghost x@uint8 : x = x && x = x;
{ true && rng true }
