% `x` is a constant and `X` is a variable; `AND` is not a keyword here but the
% gate types of other formats are, so a reader that case-folds the token stream
% merges the two names into one.
fof(a, axiom, ! [X] : p(X, x)).
