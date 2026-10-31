# Prove-with fact selection (doc/cryptoline.pdf: "Sometimes a predicate has to
# be proved with facts that have been cut off"). The chaining gives the final
# fragment only the immediately preceding cut's predicate (z <=u 6); the
# postcondition also needs y <=u 5, which is cut 0's fact, selected with
# `prove with [ cuts [0] ]`. Without the hint the final fragment cannot prove
# the conjunction and the instance has a counterexample.
proc main(uint8 x) =
{ true && rng x <=u 4 }
adds c y x 1@uint8;
cut true && rng y <=u 5;
adds c2 z y 1@uint8;
cut true && rng z <=u 6;
{ true && rng y <=u 5 /\ z <=u 6 prove with [ cuts [0] ] }
