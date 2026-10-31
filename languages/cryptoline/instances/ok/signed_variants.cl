# The explicit signedness variants (doc/cryptoline.pdf: the u*/s* prefixes;
# Fu et al., CCS 2019, doi:10.1145/3319535.3354199). The prefix selects the
# unsigned/signed reading of the base instruction; the operands must carry
# that signedness already. Also set/clear/nop and the `intN` type spelling.
proc main(uint8 x, uint8 y, sint8 p, sint8 q, bit k) =
{ true && true }
uadd a x y;
sadd b p q;
usub c x y;
ssub d p q;
umul e x y;
smul f p q;
uadds ca s1 x y;
sadds cb s2 p q;
uadc g x y k;
sadc h p q k;
uadcs cc s3 x y k;
sadcs cd s4 p q k;
usubc nb1 d1 x y;
usubs nb2 d2 x y;
ssubc nb3 d3 p q;
usubb bor1 d4 x y;
ssubb bor2 d5 p q;
usbc r1 x y k;
ssbc r2 p q k;
usbcs c3 r3 x y k;
ssbbs c4 r4 p q k;
umuls ov1 m1 x y;
smuls ov2 m2 p q;
umull hi lo x y;
smull hs ls p q;
umulj wj x y;
smulj sj p q;
usplit h1 l1 x 4;
ssplit h2 l2 p 4;
uspl h3 l3 x 4;
sspl h4 l4 p 4;
set flag;
clear done;
nop;
{ eqn a = x + y /\ b = p + q && rng true }
