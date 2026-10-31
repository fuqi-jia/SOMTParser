"""Verify every DIMACS clause against a packed SMT Boolean export.

This verifies the Boolean relation, including unused header variables. Counting
weights and projection queries are outside its claim. Memory holds one source
clause and one target clause; clause boundaries may cross source lines.
"""
import argparse
import hashlib
import json
from pathlib import Path

try:
    from .wcnf_stream_equivalence import Clause, VerificationError, _index, verify_clause_stream
except ImportError:  # Direct command-line invocation, without installing tools.
    from wcnf_stream_equivalence import Clause, VerificationError, _index, verify_clause_stream


class DimacsClauses:
    def __init__(self, stream):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.declared_variables = None
        self.declared_clauses = None
        self.largest = 0
        self.clauses = self.hard = self.soft = self.literals = 0
        self.complete = False
        self.counting_directives = False

    def __iter__(self):
        literals = []
        for line, raw in enumerate(self.stream, 1):
            self.digest.update(raw)
            fields = raw.split()
            if not fields:
                continue
            if fields[0].startswith(b"c"):
                if fields[0] == b"c" and len(fields) > 1 and fields[1] in (b"p", b"t"):
                    self.counting_directives = True
                continue
            if fields[0] == b"p":
                if self.declared_variables is not None:
                    raise VerificationError("repeated DIMACS problem line")
                if len(fields) != 4 or fields[1] != b"cnf":
                    raise VerificationError("expected DIMACS problem line p cnf V C")
                self.declared_variables = _index(fields[2])
                self.declared_clauses = _index(fields[3])
                continue
            if self.declared_variables is None:
                raise VerificationError("DIMACS clauses precede problem line")
            for token in fields:
                negative = token.startswith(b"-")
                index = _index(token[1:] if negative else token)
                if index == 0:
                    self.clauses += 1
                    self.hard += 1
                    self.literals += len(literals)
                    yield Clause(tuple(literals), None)
                    literals = []
                else:
                    self.largest = max(self.largest, index)
                    literals.append(-index if negative else index)
        if self.declared_variables is None:
            raise VerificationError("missing DIMACS problem line")
        if literals:
            raise VerificationError("unterminated DIMACS clause")
        if self.clauses != self.declared_clauses:
            raise VerificationError("source header clause count does not match the entire file")
        if self.largest > self.declared_variables:
            raise VerificationError("source literal exceeds declared variable count")
        self.complete = True


def verify_streams(source_stream, target_stream):
    source = DimacsClauses(source_stream)
    result = verify_clause_stream(source, target_stream)
    result.update(method="complete ordered DIMACS clause correspondence",
                  source_format="dimacs-cnf", counting_semantics="not-checked",
                  has_counting_directives=source.counting_directives)
    return result


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
