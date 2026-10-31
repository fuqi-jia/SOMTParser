# A ghost variable is a logical constant usable only in specifications; its
# predicate is always assumed (doc/cryptoline.pdf). Here it captures the
# pre-state value of x across a modification.
proc main(uint8 x) =
{ true && true }
ghost x0@uint8 : x0 = x && x0 = x;
mov y x;
mov x 0@uint8;
{ eqn y = x0 && rng x = 0@uint8 }
