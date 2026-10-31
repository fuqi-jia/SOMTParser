%--------------------------------------------------------------------------
% TFF: sort declarations, signatures, typed quantifiers and equality.
%--------------------------------------------------------------------------
tff(fruit_type, type, fruit: $tType).
tff(apple_type, type, apple: fruit).
tff(tree_type, type, tree: fruit > fruit).
tff(eats_type, type, eats: (fruit * fruit) > $o).
tff(ax1, axiom, ![X: fruit]: eats(X, apple)).
tff(ax2, axiom, ![X: fruit, Y: fruit]: (eats(X, Y) => eats(tree(X), tree(Y)))).
tff(eq_ax, axiom, ![X: fruit, Z: fruit]: (X = Z => tree(X) = tree(Z))).
tff(goal, conjecture, eats(apple, apple)).
