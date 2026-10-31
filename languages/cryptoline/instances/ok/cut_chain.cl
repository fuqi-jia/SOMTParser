# `cut` splits the verification into fragments, each proved separately, with
# a fragment's postcondition becoming the next fragment's precondition
# (doc/cryptoline.pdf; ast/cryptoline.ml: cut_rspec "starts afresh with the
# predicate assumed"). Here the final `y <=u 5` is provable only THROUGH the
# cut: the last fragment starts afresh from the cut predicate alone, without
# the instruction that defined y.
proc main(uint8 x) =
{ true && rng x <=u 4 }
adds c y x 1@uint8;
cut true && rng y <=u 5;
assert true && rng y <=u 5;
{ true && rng y <=u 5 }
