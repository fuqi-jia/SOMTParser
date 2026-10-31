# The unsigned prefix on signed operands is ill-formed, not a conversion
# (typecheck/std.ml: check_same_typ over the unsigned destination hint).
proc main(sint8 x, sint8 y) =
{ true && true }
uadd z x y;
{ true && true }
