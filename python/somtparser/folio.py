"""Strict reference parser and three-way entailment checks for FOLIO.

Z3 is an optional benchmark dependency. Universe is nonempty and unbounded.
Malformed annotations are reported, never repaired by guessing parentheses.
"""
import re
from ._nl_model import ModelError


class FolParser:
    def __init__(self):
        import z3

        self.z3 = z3
        self.domain = z3.DeclareSort("FolioEntity")
        self.constants, self.functions, self.predicates = {}, {}, {}

    def parse(self, text):
        if not isinstance(text, str) or len(text) > 32768:
            raise ModelError("invalid FOL annotation")
        tokens = re.findall(r"\s+|[\w][\w.’+_-]*|[∀∃¬∧∨⊕→↔⟷^=≠(),]", text)
        if "".join(tokens) != text:
            raise ModelError("unrecognized FOL token")
        self.tokens = [
            {"⟷": "↔", "^": "∧"}.get(t, t) for t in tokens if not t.isspace()
        ]
        self.pos = 0
        value = self.formula({}, 0)
        if self.pos != len(self.tokens):
            raise ModelError("trailing FOL tokens or unmatched parentheses")
        return value

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None or (expected is not None and token != expected):
            raise ModelError("unexpected FOL token; expected " + str(expected))
        self.pos += 1
        return token

    def identifier(self):
        token = self.take()
        if not re.fullmatch(r"[\w][\w.’+_-]*", token):
            raise ModelError("FOL identifier expected")
        return token

    def symbol(self, table, name, arity, result):
        if name in table:
            old_arity, symbol = table[name]
            if old_arity != arity:
                raise ModelError("inconsistent FOL symbol arity")
            return symbol
        symbol = self.z3.Function(name, *([self.domain] * arity), result)
        table[name] = arity, symbol
        return symbol

    def arguments(self, env):
        self.take("(")
        args = []
        if self.peek() != ")":
            args.append(self.term(env))
            while self.peek() == ",":
                self.take()
                args.append(self.term(env))
        self.take(")")
        return args

    def term(self, env):
        name = self.identifier()
        if self.peek() == "(":
            args = self.arguments(env)
            return self.symbol(self.functions, "fn_" + name, len(args), self.domain)(
                *args
            )
        if name in env:
            return env[name]
        if name not in self.constants:
            self.constants[name] = self.z3.Const("c_" + name, self.domain)
        return self.constants[name]

    def formula(self, env, minimum):
        z3, token = self.z3, self.peek()
        if token == "¬":
            self.take()
            left = z3.Not(self.formula(env, 6))
        elif token in ["∀", "∃"]:
            self.take()
            name = self.identifier()
            # Tokens such as ∀x∀y are distinct; a comma is not silently
            # interpreted as another binder or conjunction.
            variable = z3.Const("b_" + name, self.domain)
            body = self.formula(dict(env, **{name: variable}), 0)
            left = (z3.ForAll if token == "∀" else z3.Exists)([variable], body)
        elif token == "(":
            self.take()
            left = self.formula(env, 0)
            self.take(")")
        else:
            start = self.pos
            name = self.identifier()
            args = self.arguments(env) if self.peek() == "(" else []
            if self.peek() in ["=", "≠"]:
                self.pos = start
                first = self.term(env)
                comparison = self.take()
                second = self.term(env)
                left = first == second if comparison == "=" else first != second
            else:
                left = self.symbol(
                    self.predicates, "p_" + name, len(args), z3.BoolSort()
                )(*args)
        precedence = {"↔": 1, "→": 2, "⊕": 3, "∨": 4, "∧": 5}
        while self.peek() in precedence and precedence[self.peek()] >= minimum:
            operator = self.take()
            strength = precedence[operator]
            right = self.formula(env, strength if operator == "→" else strength + 1)
            left = {
                "↔": lambda: left == right,
                "→": lambda: z3.Implies(left, right),
                "⊕": lambda: z3.Xor(left, right),
                "∨": lambda: z3.Or(left, right),
                "∧": lambda: z3.And(left, right),
            }[operator]()
        return left


def classify(premises, conclusion, timeout_ms=5000):
    """Keep inconsistency and solver unknown distinct from ordinary labels."""
    import z3

    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*premises)
    consistent = str(solver.check())
    if consistent != "sat":
        return dict(
            label=None,
            status="inconsistent-premises"
            if consistent == "unsat"
            else "solver-unknown",
            consistency=consistent,
        )
    answers = []
    for query in [z3.Not(conclusion), conclusion]:
        solver.push()
        solver.add(query)
        answers.append(str(solver.check()))
        solver.pop()
    label = (
        "True"
        if answers[0] == "unsat"
        else "False"
        if answers[1] == "unsat"
        else "Uncertain"
        if answers == ["sat", "sat"]
        else None
    )
    return dict(
        label=label,
        status="classified" if label else "solver-unknown",
        consistency=consistent,
        negated_conclusion=answers[0],
        positive_conclusion=answers[1],
    )


def score_label(result, reference_label):
    """Compare published labels without confusing epistemic and solver unknown.

    Public FOLIO v0.0 spells the third label ``Unknown``; other releases and
    this classifier use ``Uncertain``. Preserve the raw label and solver
    outcomes, and normalize only these two explicit dataset spellings.
    """
    labels = {"True": "True", "False": "False", "Unknown": "Uncertain", "Uncertain": "Uncertain"}
    if not isinstance(reference_label, str) or reference_label not in labels:
        raise ModelError("unrecognized FOLIO reference label")
    row = dict(result, expected_label=reference_label,
               expected_label_canonical=labels[reference_label])
    if row.get("status") not in ("classified", "label-agreement", "label-disagreement"):
        return row
    label = row.get("label")
    proof = row.get("consistency") == "sat" and (
        label == "True" and row.get("negated_conclusion") == "unsat"
        or label == "False" and row.get("positive_conclusion") == "unsat"
        or label == "Uncertain" and row.get("negated_conclusion") == "sat"
        and row.get("positive_conclusion") == "sat")
    if not proof:
        raise ModelError("classified FOLIO label lacks its solver evidence")
    row["status"] = "label-agreement" if label == labels[reference_label] else "label-disagreement"
    return row


def folio_reference(record, timeout_ms=5000):
    parser = FolParser()
    premises = [parser.parse(s) for s in record["premises-FOL"]]
    conclusion = parser.parse(record["conclusion-FOL"])
    return classify(premises, conclusion, timeout_ms)
