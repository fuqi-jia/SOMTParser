%--------------------------------------------------------------------------
% Authored for SOMTParser, not vendored.
%
% The shape comes from TPTP's LCL domain, where a problem encodes a LOGIC and
% the connectives are ordinary uninterpreted function symbols. TPTP's
% EXAMPLE_PROBLEMS/TPTP/LCL365-1.p writes exactly this:
%
%     is_a_theorem(implies(implies(not(X),X),X))
%
% `not`, `and`, `or` and `implies` here are function symbols of the object
% logic, not connectives of the meta logic. Passing those names through to
% declare-fun made the ENGINE reject them as reserved built-ins, and the
% rejection escaped the frontend as E_INTERNAL -- the bucket for a broken
% invariant -- on a perfectly legal input.
%
% The problem itself is not vendored because the TPTP library's
% redistribution terms were not established; this file reproduces the
% construct and nothing else.
%--------------------------------------------------------------------------
fof(modus_ponens, axiom,
    ( ! [X, Y] :
        ( ( is_a_theorem(X)
          & is_a_theorem(implies(X, Y)) )
       => is_a_theorem(Y) ) )).

fof(and_is_not_or, axiom,
    ( ! [X, Y] :
        ( is_a_theorem(not(and(X, Y)))
      <=> is_a_theorem(or(not(X), not(Y))) ) )).

fof(distinct_connectives, axiom,
    ( ! [X] : ~ ( and(X, X) = or(X, X) ) )).

fof(goal, conjecture,
    ( ? [X] : is_a_theorem(implies(X, not(not(X)))) )).
