% The same problem with the conjecture already negated, as a prover would
% write it. This file and socrates.p must produce the SAME formula: the two
% roles differ by exactly one negation, applied on one side or the other.
fof(ax1, axiom, ! [X] : (human(X) => mortal(X))).
fof(ax2, axiom, human(socrates)).
fof(goal, negated_conjecture, ~ mortal(socrates)).
