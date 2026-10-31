%--------------------------------------------------------------------------
% TFF arithmetic: interpreted numerics over $int and $real, one numeric sort
% per application -- TPTP has no implicit $int-to-$real coercion.
%--------------------------------------------------------------------------
tff(n_type, type, n: $int).
tff(r_type, type, r: $real).
tff(ax1, axiom, $greater($sum(n, 3), $uminus(5))).
tff(ax2, axiom, $lesseq($sum($product(5, $quotient_e(n, 5)), $remainder_e(n, 5)), n)).
tff(ax3, axiom, $greater($quotient(r, 2.0), $floor($uminus(1.5)))).
tff(ax4, axiom, $greatereq($ceiling(r), $truncate(r))).
tff(ax5, axiom, $is_int($to_real(n))).
tff(ax6, axiom, $greater($sum(r, 3/5), 1.5E-2)).
