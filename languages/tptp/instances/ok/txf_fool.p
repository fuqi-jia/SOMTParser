%--------------------------------------------------------------------------
% TXF (FOOL): $ite, $let, and the conflation of $o-sorted terms and formulas.
%--------------------------------------------------------------------------
txf(b_type, type, b: $o).
txf(c_type, type, c: $int).
txf(ax1, axiom, $ite(b, $sum(c, 1), 0) = 1).
txf(ax2, axiom, $let(two: $int, two := 2, $product(two, c)) = $sum(c, c)).
txf(ax3, axiom, b <=> $greatereq($let(f: ($int) > $int, f(X) := $sum(X, 1), f(c)), c)).
txf(ax4, axiom, $ite(b, ($greatereq(c, 0)), b)).
