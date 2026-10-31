# Range division forms (docs/languages/cryptoline.md §4.5): udiv/sdiv map
# directly onto bvudiv/bvsdiv, total at a zero divisor.
proc main(uint8 x, uint8 y, sint8 a, sint8 b) =
{ true && rng 0 <u y }
nondet q@uint8;
nondet s@sint8;
{ true && rng and [ udiv x y = q, sdiv a b = s, ule (udiv x y) x ] }
