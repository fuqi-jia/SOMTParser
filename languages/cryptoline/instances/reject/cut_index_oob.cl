# A cuts selector must name a cut that precedes the predicate; ecut and rcut
# are numbered separately from 0 (doc/cryptoline.pdf).
proc main(uint8 x) =
{ true && true }
{ true && rng x = x prove with [ cuts [0] ] }
