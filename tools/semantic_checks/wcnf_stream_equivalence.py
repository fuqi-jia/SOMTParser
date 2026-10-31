"""Check the complete packed WCNF export by weighted-clause correspondence.

This independent checker reads the source and target once, retaining only one
clause from each. A successful check proves pointwise equality of feasibility
and total violated soft weight under the variable map i <-> x{i}. It does not
invoke a solver or claim to accept arbitrary SMT-LIB scripts: the target grammar
is Boolean declarations, disjunctive hard/soft assertions in source order, and
optional final check-sat/exit commands. Unsupported shapes fail verification.
"""
from dataclasses import dataclass
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re


class VerificationError(ValueError):
    """The input is invalid or the complete correspondence was not established."""


def _natural(token, *, positive=False):
    # bytes.isdigit accepts exactly ASCII decimal digits. Keep arbitrary
    # precision weights as bytes without a Python loop per digit.
    if not token or not token.isdigit():
        raise VerificationError(f"invalid unsigned decimal: {repr(token)[:80]}")
    normalized = token.lstrip(b"0") or b"0"
    if positive and normalized == b"0":
        raise VerificationError("weights and top must be positive")
    return normalized


def _index(token, *, positive=False):
    normalized = _natural(token, positive=positive)
    if (len(normalized) > 19
            or (len(normalized) == 19 and normalized > b"9223372036854775807")):
        raise VerificationError("variable index/count exceeds the supported signed 64-bit range")
    return int(normalized)


@lru_cache(maxsize=4096)
def _cached_positive_index(token):
    return _index(token, positive=True)


def _positive_index(token):
    """Reuse validation for recurring source and canonical target variables."""
    # Valid indices are at most 19 digits. Keep arbitrarily zero-padded source
    # spellings valid, but do not retain long raw tokens in the bounded cache.
    if len(token) > 19:
        return _index(token, positive=True)
    return _cached_positive_index(token)


def _at_least(left, right):
    return (len(left), left) >= (len(right), right)


@dataclass(frozen=True)
class Clause:
    literals: tuple
    # None denotes a hard clause; bytes preserve arbitrarily large weights.
    weight: object


class SourceClauses:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.declared_variables = None
        self.declared_clauses = None
        self.largest = 0
        self.clauses = self.hard = self.soft = self.literals = 0
        self.complete = False

    def __iter__(self):
        top = None
        unweighted = False
        for line_number, raw in enumerate(self.stream, 1):
            self.digest.update(raw)
            fields = raw.split()
            if not fields or fields[0].startswith(b"c"):
                continue
            if fields[0] == b"p":
                if self.declared_variables is not None or self.clauses:
                    raise VerificationError("misplaced/repeated source problem line")
                if len(fields) not in (4, 5) or fields[1] not in (b"cnf", b"wcnf"):
                    raise VerificationError("invalid source problem line")
                unweighted = fields[1] == b"cnf"
                if unweighted and len(fields) != 4:
                    raise VerificationError("unweighted CNF problem line has unexpected top")
                self.declared_variables = _index(fields[2])
                self.declared_clauses = _index(fields[3])
                top = _natural(fields[4], positive=True) if len(fields) == 5 else None
                continue
            if fields[0] == b"h":
                weight, tokens = None, fields[1:]
            elif unweighted:
                weight, tokens = b"1", fields
            else:
                weight, tokens = _natural(fields[0], positive=True), fields[1:]
                if top is not None and _at_least(weight, top):
                    weight = None
            if not tokens or tokens[-1] != b"0":
                raise VerificationError(f"source clause at line {line_number} lacks final zero")
            literals = []
            for token in tokens[:-1]:
                negative = token.startswith(b"-")
                variable = _positive_index(token[1:] if negative else token)
                if variable > self.largest:
                    self.largest = variable
                literals.append(-variable if negative else variable)
            self.clauses += 1
            self.literals += len(literals)
            self.hard += weight is None
            self.soft += weight is not None
            yield Clause(tuple(literals), weight)
        if self.declared_clauses is not None and self.clauses != self.declared_clauses:
            raise VerificationError("source header clause count does not match the entire file")
        if self.declared_variables is not None and self.largest > self.declared_variables:
            raise VerificationError("source literal exceeds declared variable count")
        if self.declared_variables is None and not self.clauses:
            raise VerificationError("headerless source has no clauses")
        self.complete = True


class TargetTokens:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.iterator = self._tokens()

    def _tokens(self):
        for raw in self.stream:
            self.digest.update(raw)
            # Strings and quoted symbols are outside the checked target grammar.
            # Its Boolean names and command atoms never contain semicolons.
            text = raw.split(b";", 1)[0]
            yield from re.findall(rb"[()]|[^()\s]+", text)

    def take(self, expected=None):
        token = next(self.iterator, None)
        if expected is not None and token != expected:
            raise VerificationError(f"expected target token {expected!r}, got {token!r}")
        return token


def _target_variable(token):
    if token is None or not token.startswith(b"x"):
        raise VerificationError(f"unsupported target variable {token!r}")
    suffix = token[1:]
    if suffix.startswith(b"0"):
        raise VerificationError("target variable does not use canonical source-index spelling")
    return _positive_index(suffix)


def _target_clause(tokens, command, declared):
    literals = []
    head = next(tokens, None)
    if head == b"(":
        _expect_token(tokens, b"or")
        while True:
            token = next(tokens, None)
            if token == b")":
                break
            negative = token == b"("
            if negative:
                _expect_token(tokens, b"not")
                token = next(tokens, None)
            variable = _target_variable(token)
            if variable > declared:
                raise VerificationError("target clause references an undeclared variable")
            if negative:
                _expect_token(tokens, b")")
            literals.append(-variable if negative else variable)
        if not literals:
            raise VerificationError("zero-argument or is invalid SMT-LIB; an empty clause must be false")
    elif head != b"false":
        raise VerificationError(f"unsupported target clause term {head!r}")
    weight = None
    if command == b"assert-soft":
        _expect_token(tokens, b":weight")
        weight = _natural(next(tokens, None), positive=True)
    _expect_token(tokens, b")")
    return Clause(tuple(literals), weight)


def _expect_token(tokens, expected):
    token = next(tokens, None)
    if token != expected:
        raise VerificationError(f"expected target token {expected!r}, got {token!r}")


def verify_streams(source_stream, target_stream):
    """Verify both complete streams, raising VerificationError on any mismatch."""
    return verify_clause_stream(SourceClauses(source_stream), target_stream)


def verify_clause_stream(source, target_stream):
    """Compare a complete source clause iterator to the restricted SMT grammar."""
    clauses = iter(source)
    target = TargetTokens(target_stream)
    declared = assertions = 0
    phase = "declarations"
    saw_check = saw_exit = False
    tokens = target.iterator
    while True:
        start = next(tokens, None)
        if start is None:
            break
        if saw_exit or start != b"(":
            raise VerificationError("unexpected target content outside a command")
        command = next(tokens, None)
        if command == b"declare-const":
            if phase != "declarations":
                raise VerificationError("target declaration after assertions/queries")
            declared += 1
            if _target_variable(next(tokens, None)) != declared:
                raise VerificationError("target declarations do not cover consecutive source indices")
            _expect_token(tokens, b"Bool")
            _expect_token(tokens, b")")
        elif command in (b"assert", b"assert-soft"):
            if phase == "queries":
                raise VerificationError("target assertion after a query")
            phase = "assertions"
            actual = _target_clause(tokens, command, declared)
            expected = next(clauses, None)
            assertions += 1
            if expected is None:
                raise VerificationError("extra target assertion")
            if actual != expected:
                raise VerificationError(f"weighted-clause correspondence fails at clause {assertions}")
        elif command in (b"check-sat", b"exit"):
            phase = "queries"
            if command == b"check-sat":
                if saw_check:
                    raise VerificationError("repeated target query outside checked grammar")
                saw_check = True
            else:
                saw_exit = True
            _expect_token(tokens, b")")
        else:
            raise VerificationError(f"target command outside checked grammar: {command!r}")
    if next(clauses, None) is not None:
        raise VerificationError("source has a clause missing from target")
    assert source.complete
    expected_variables = source.largest if source.declared_variables is None else source.declared_variables
    if declared != expected_variables:
        raise VerificationError("target variable domain does not match source variables")
    return dict(status="verified", method="complete ordered weighted-clause correspondence",
                feasibility_equivalent=True, pointwise_violation_cost_equal=True,
                variable_map="source index i maps to target Boolean x{i}",
                variables=declared, clauses=assertions, literals=source.literals,
                hard_clauses=source.hard, soft_clauses=source.soft,
                source_sha256=source.digest.hexdigest(), target_sha256=target.digest.hexdigest(),
                target_solver_parse="not-run", target_solve="not-run")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        with args.source.open("rb") as source, args.target.open("rb") as target:
            result = verify_streams(source, target)
    except (VerificationError, OSError) as error:
        result = dict(status="not-verified", reason=str(error))
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
