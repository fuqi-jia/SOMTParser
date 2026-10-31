% A model whose syntax is fine and whose types are not.
%
% This exists to give the CLI contract test a second, structurally different
% failure: bad_syntax.mzn fails in the frontend's own tokenizer (E_PARSE),
% which never touches the Parser. This one gets all the way to the HIR and is
% refused by Uir::Hir::typeCheck (E_TYPE) -- and before that check existed it
% reached Parser::mkAdd, which printed "error: Kind mismatch ..." to *stdout*
% and then aborted the process with SIGABRT.
%
% Both halves of that are what the contract test asserts about this file:
% stdout stays empty, and the exit code is 1 (a benchmark that could not be
% translated), not 134.
%
% This file used to read `var bool: b; constraint b + 1 > 0;`. That is LEGAL
% MiniZinc -- the specification coerces bool to int in an arithmetic context,
% so `b + 1` is 1 or 2 -- and it was refused only because this frontend did
% not implement the coercion. The fixture was testing a gap and calling it a
% type error. When the coercion landed on 2026-08-14 the file started
% translating and the contract test caught it.
%
% The replacement is ill-sorted in the other direction, which MiniZinc does
% NOT coerce: there is no int-to-bool.
var int: x;
constraint x /\ true;
solve satisfy;
