% Input file u2.p for the paper "Applying Saturation-Based Theorem Proving 
% to Open Problems in Positive Implicational Logic"
% ----
% This is a TPTP input file, for refuting candidate u2 as a sinlge axiom 
% for positive (viz., intuitionistic) implication.
% ----
% Vampire 5.0.1 will generate a saturated set of clauses (the one reported in 
% the paper), which corresponds to a model on which u2 is a theorem, but i(P,P) % is not a theorem --- thus ruling-out candidate u2 as a single axiom.
% ----
% The command used to generate this saturated set is as follows.
% vampire --mode portfolio --schedule casc_sat --saturation_algorithm lrs u2.p
% ----

fof(mp,axiom, ![X,Y]: ((p(i(X,Y)) & p(X)) => p(Y))).
fof(refl,conjecture, ![P]: p(i(P,P))).
fof(u2,axiom, ![X,Y,Z,U]: p(i(i(X, i(Y, Z)), i(i(i(U, X), Y), i(X, Z))))).