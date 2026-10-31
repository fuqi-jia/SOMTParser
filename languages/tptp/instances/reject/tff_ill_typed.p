% $sum over mixed numeric sorts: TPTP has no implicit $int-to-$real coercion,
% so this is what TPTP itself forbids -- a type error, not a fragment gap.
tff(bad, axiom, $greater($sum(1, 2.0), 0.0)).
