# set/clear define a bit; an explicit wider annotation is a type error
# (parsers/common.ml: resolve_lcarry_with).
proc main(uint8 x) =
{ true && true }
set x@uint8;
{ true && true }
