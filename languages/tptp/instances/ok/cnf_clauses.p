% CNF. Every variable here is implicitly universally quantified -- nothing in
% the file says so.
cnf(c1, axiom, ~ human(X) | mortal(X)).
cnf(c2, axiom, human(socrates)).
cnf(c3, negated_conjecture, ~ mortal(socrates)).
