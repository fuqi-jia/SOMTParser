% Repeated names are freshened within their quantifier scope.
fof(repeated, axiom, ![X] : (p(X) & (?[X,X] : q(X)) & r(X))).
fof(reference, conjecture, ![Y] : (p(Y) & (?[Z] : q(Z)) & r(Y))).
