%--------------------------------------------------------------------------
% The classic. Two axioms and a conjecture; the conjecture is what makes the
% file a theorem-proving problem rather than a satisfiability one.
%--------------------------------------------------------------------------
fof(ax1, axiom, ! [X] : (human(X) => mortal(X))).
fof(ax2, axiom, human(socrates)).
fof(goal, conjecture, mortal(socrates)).
