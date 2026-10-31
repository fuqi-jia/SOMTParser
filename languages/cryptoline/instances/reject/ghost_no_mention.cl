# A ghost predicate conjunct that mentions none of the declared ghosts is
# rejected (parsers/common.ml: parse_ghost_at) -- it would be an assume that
# introduces no logical variable.
proc main(uint8 x) =
{ true && true }
ghost g@uint8 : x = x && true;
{ true && rng true }
