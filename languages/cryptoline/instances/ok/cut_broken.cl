# A cut whose predicate does NOT follow from its prefix breaks the chain:
# fragment 0 fails, so the instance has a counterexample and the emitted
# refutation is satisfiable. `ecut` and `rcut` cut one side only
# (doc/cryptoline.pdf: "cut e && r is an alias of one ecut e followed by an
# rcut r").
proc main(uint8 x) =
{ true && true }
mov y x;
ecut y = x + 1;
rcut y = 0@8;
{ true && rng true }
