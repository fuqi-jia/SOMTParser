% p is applied before it is declared, so default typing assumes ($i) > $o; the
% later declaration conflicts with the recorded assumption.
tff(fruit_type, type, fruit: $tType).
tff(ax, axiom, p(a)).
tff(p_type, type, p: fruit > $o).
