% The included file carries the axiom the conjecture needs. Without it the
% problem is a different, unprovable one -- and still well-formed.
include('Axioms/mortality.ax').
fof(ax2, axiom, human(socrates)).
fof(goal, conjecture, mortal(socrates)).
