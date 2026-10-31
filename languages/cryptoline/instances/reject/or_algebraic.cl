# Disjunction is a range-predicate form; the algebraic half of a condition is
# conjunction-only (ast/cryptoline.mli: ebexp has no disjunction).
proc main(uint8 x) =
{ true && true }
{ eqn x = 1 \/ x = 2 && rng true }
