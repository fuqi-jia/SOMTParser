"""CryptoLine verdict tests -- the cut chaining is a semantic property, not a
text pattern.

docs/languages/cryptoline.md §2.3/§4.4: a cut splits the verification into
independent fragments, each proved separately with the previous fragment's
cut predicates as its ONLY precondition (the official "starts afresh"). The
emitted script is a refutation (§2.5), so UNSAT means the program (or the
selected fragment) verifies and SAT means a source-level counterexample
exists. A program whose cut chaining is broken must report sat, and a program
whose postcondition holds only THROUGH the cut must report unsat; both are
pinned here with z3 as the solver.
"""

import pathlib

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp

ROOT = pathlib.Path(__file__).resolve().parents[2]
OK = ROOT / "languages" / "cryptoline" / "instances" / "ok"


def _fixture(name):
    return (OK / name).read_text()


_PRE_HINT = (
    "proc main(uint8 x) =\n"
    "{ true && rng x <=u 4 }\n"
    "adds c y x 1@uint8;\n"
    "cut true && rng y <=u 5;\n"
)
# The final fragment's chain knows only y <=u 5; the postcondition x <=u 4 is
# the PRECONDITION's fact, re-selected by the hint.
PRE_HINT_OK = _PRE_HINT + "{ true && rng x <=u 4 prove with [ precondition ] }\n"
PRE_HINT_DROPPED = _PRE_HINT + "{ true && rng x <=u 4 }\n"

_ASSUME_HINT = (
    "proc main(uint8 x) =\n"
    "{ true && rng true }\n"
    "assume true && rng x <=u 4;\n"
    "adds c y x 1@uint8;\n"
    "cut true && rng y <=u 5;\n"
)
# Assumes do not carry across a cut (the fragment starts afresh); the
# `all assumes` hint re-selects the fact for this predicate only.
ASSUME_HINT_OK = _ASSUME_HINT + "{ true && rng x <=u 4 prove with [ all assumes ] }\n"
ASSUME_HINT_DROPPED = _ASSUME_HINT + "{ true && rng x <=u 4 }\n"

_PROVE_WITH = (
    "proc main(uint8 x) =\n"
    "{ true && rng x <=u 4 }\n"
    "adds c y x 1@uint8;\n"
    "cut true && rng y <=u 5;\n"
    "adds c2 z y 1@uint8;\n"
    "cut true && rng z <=u 6;\n"
)
# The chain gives the final fragment only z <=u 6 (cut 1); the other conjunct
# y <=u 5 is cut 0's fact and must be selected.
PROVE_WITH_OK = _PROVE_WITH + "{ true && rng y <=u 5 /\\ z <=u 6 prove with [ cuts [0] ] }\n"
PROVE_WITH_DROPPED = _PROVE_WITH + "{ true && rng y <=u 5 /\\ z <=u 6 }\n"

_SAFETY = "proc main(uint8 x) =\n{ true && rng PRE }\nadd y x 1@uint8;\n{ true && rng true }\n"

# A callee whose contract is trusted in `call` mode but whose body does not
# establish it -- the inline mode executes the body and the caller's
# postcondition then has a counterexample (doc/cryptoline.pdf: call "is
# replaced by the pre-/post-conditions of p for verification", inline
# "replaces every occurrence of the corresponding formal parameters in the
# procedural body").
_WRONG_CONTRACT = (
    "proc wrong(uint8 a; uint8 r) =\n"
    "{ true && rng true }\n"
    "mov r a;\n"
    "{ true && rng r = 0@8 }\n"
    "proc main(uint8 x) =\n"
    "{ true && rng true }\n"
    "MODE wrong(x, y);\n"
    "{ true && rng y = 0@8 }\n"
)
# The caller violates the callee's precondition: the call asserts it.
_CALL_PRE_VIOLATED = (
    "proc dbl(uint8 a; uint8 r) =\n"
    "{ true && rng a <=u 100 }\n"
    "adds c r a a;\n"
    "{ true && rng r <=u 200 }\n"
    "proc main(uint8 x) =\n"
    "{ true && rng true }\n"
    "call dbl(x, y);\n"
    "{ true && rng y <=u 200 }\n"
)
# A ghost predicate is always ASSUMED: drop it and the captured value is free.
_GHOST_DROPPED = (
    "proc main(uint8 x) =\n"
    "{ true && true }\n"
    "ghost x0@uint8 : true && true;\n"
    "mov y x;\n"
    "mov x 0@uint8;\n"
    "{ eqn y = x0 && rng x = 0@uint8 }\n"
)

# (name, source, expected, check_index) with expected in {"verified", "fails"}.
VERDICT_CORPUS = [
    # The chained cut: the last fragment starts afresh from y <=u 5 alone and
    # still discharges the assert and the postcondition.
    ("cut_chain", _fixture("cut_chain.cl"), "verified", None),
    # The cut predicate y = x+1 does not follow from y = x: fragment 0 fails.
    ("cut_broken", _fixture("cut_broken.cl"), "fails", None),
    # The fixture that pinned the old refusal: its cut y <=u 4 does not follow
    # from the prefix (x is unconstrained), so the instance has a
    # counterexample even though everything after the cut verifies.
    ("cut_does_not_follow", _fixture("cut.cl"), "fails", None),
    # Prove-with fact selection: each hint is load-bearing -- the twin without
    # the hint must fail to verify.
    ("cut_prove_with", _fixture("cut_prove_with.cl"), "verified", None),
    ("cut_prove_with_hint_dropped", PROVE_WITH_DROPPED, "fails", None),
    ("cut_precondition_hint", PRE_HINT_OK, "verified", None),
    ("cut_precondition_hint_dropped", PRE_HINT_DROPPED, "fails", None),
    ("cut_all_assumes_hint", ASSUME_HINT_OK, "verified", None),
    ("cut_all_assumes_hint_dropped", ASSUME_HINT_DROPPED, "fails", None),
    # The selector is per-fragment: the broken ecut lives in fragment 0, the
    # broken rcut in fragment 1, and the (trivial) postcondition in 2.
    ("cut_broken_fragment0", _fixture("cut_broken.cl"), "fails", "0"),
    ("cut_broken_fragment1", _fixture("cut_broken.cl"), "fails", "1"),
    ("cut_broken_fragment2", _fixture("cut_broken.cl"), "verified", "2"),
    ("cut_chain_fragment1", _fixture("cut_chain.cl"), "verified", "1"),
    # Instruction safety is an obligation (§2.2): `add` asserts no overflow.
    ("safety_ok", _SAFETY.replace("PRE", "x <=u 4"), "verified", None),
    ("safety_fail", _SAFETY.replace("PRE", "true"), "fails", None),
    # Procedures (§2.3 of the manual's instruction list, and the procedure
    # grammar): call is the contract (assert pre, havoc outputs, assume
    # post); inline is the body; inlinespec is the body verified through the
    # contract.
    ("call_contract", _fixture("call.cl"), "verified", None),
    ("call_precondition_violated", _CALL_PRE_VIOLATED, "fails", None),
    # The inout actual's entry value is ghost-captured: x <=u 51 follows from
    # x_entry <=u 50 only because the assumed post reads the ghost copy.
    ("call_inout", _fixture("call_inout.cl"), "verified", None),
    ("inline_body", _fixture("inline.cl"), "verified", None),
    ("inlinespec_contract", _fixture("inlinespec.cl"), "verified", None),
    # The contract-vs-body difference, in both directions: a body that does
    # not establish the contract is trusted by call and exposed by inline.
    ("call_trusts_contract", _WRONG_CONTRACT.replace("MODE", "call"),
     "verified", None),
    ("inline_exposes_body", _WRONG_CONTRACT.replace("MODE", "inline"),
     "fails", None),
    # Ghosts: the predicate is always assumed, so the captured value survives
    # the overwrite; without it the capture is unconstrained and the
    # postcondition fails.
    ("ghost_capture", _fixture("ghost.cl"), "verified", None),
    ("ghost_predicate_dropped", _GHOST_DROPPED, "fails", None),
]


def verdict(source, check_index):
    options = {"check_index": check_index} if check_index is not None else None
    t = sp.translate(source=source, language="cryptoline", options=options)
    assert t.ok, t.diagnostic_items[0].message if t.diagnostic_items else "no model"
    solver = z3.Solver()
    solver.from_string(t.to_smt2())
    return solver.check()


@pytest.mark.parametrize(
    "name,source,expected,check_index",
    VERDICT_CORPUS,
    ids=[c[0] for c in VERDICT_CORPUS],
)
def test_cryptoline_verdict(name, source, expected, check_index):
    result = verdict(source, check_index)
    if expected == "verified":
        assert result == z3.unsat, f"{name}: expected verified (unsat), got {result}"
    else:
        assert result == z3.sat, f"{name}: expected a counterexample (sat), got {result}"
