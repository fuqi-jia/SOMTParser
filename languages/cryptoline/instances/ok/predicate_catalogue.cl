# The predicate-expression catalogue tail (doc/cryptoline.pdf grammar):
# predicate connectives and prefix comparisons in the range half, modular
# equality suffixes, the eqmod modulus list, and the expression forms.
proc main(uint8 x, uint8 y, sint8 p) =
{ true && true }
nondet z@uint8;
{ eqn and [ sq x = x * x,
            poly 2 [ x, y, 3 ] = x + 2 * y + 12,
            adds [x, y, 1] = x + y + 1,
            muls [x, 2] = 2 * x,
            pow x 2 = x * x,
            x * x = sq x (mod [ 256 ]),
            (x + y) ** 2 = x * x + 2 * x * y + y * y ]
  &&
  rng and [ or [ x = y, x = z ],
            ~ (x = 0),
            and (x = x) (y = y),
            (x & y) | (x ^ y) = x | y \/ x = x,
            ult x (x + 1) \/ true,
            concat (shl x 1@uint8) (shr y 1@uint8) = concat (x << 1@uint8) (y >> 1@uint8),
            x = x (umod 2@uint8),
            x = x (mod 2@uint8),
            eqmod x y 2@uint8 \/ false,
            neg x = 0 - x,
            ! x = not x,
            x >>a 1@uint8 = sar x 1@uint8,
            const 8 255 = 255@uint8,
            const uint8 7 = 7@uint8,
            adds [ x, y ] = x + y,
            limbs 4 [ x, y ] = ulimbs 4 [ x, y ],
            slimbs 4 [ x, y ] = slimbs 4 [ x, y ] ]
}
