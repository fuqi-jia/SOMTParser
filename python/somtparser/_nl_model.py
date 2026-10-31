"""Typed candidate models for natural-language formalization.

This compiler never executes candidate expressions. The only serialized target
symbols are compiler-generated names; source names are retained in beta.
"""
from fractions import Fraction
import re

SCHEMA = "somt-nl-model-v1"
SEMANTICS = "relational-v1"
MAX_TEXT = 131072
MAX_NODES = 10000
MAX_DEPTH = 64

IDENTIFIER_RULES = (
    "HIR identifiers are strings of 1 to 128 characters satisfying Python str.isidentifier(); "
    "they cannot start with a digit. ASCII [A-Za-z_][A-Za-z0-9_]* is a valid spelling pattern. "
    "The names true, false, tdiv, ite, and, or, not are reserved, case-insensitively. "
    "Represent source names with legal symbols and use each spelling consistently in its scope."
)
TERM_NAMESPACE_RULES = (
    "Top-level variable/constant declarations, functions/predicates, datatype constructors, and "
    "datatype selectors share one term namespace and require distinct symbol spellings. "
    "A constant and a predicate for that entity must have different identifiers; update only "
    "their respective uses. Lexically bound variables may shadow names in outer scopes. "
    "Different symbol spellings do not assert distinct domain values or a unique-name assumption."
)


class ModelError(ValueError):
    """An invalid or unsupported candidate, with a JSON-path diagnostic."""

    def __init__(self, message, path="model"):
        super().__init__(f"{path}: {message}")
        self.path = path
        self.message = message


def keys(value, required, optional=(), path="model"):
    if not isinstance(value, dict):
        raise ModelError("expected an object", path)
    missing = set(required) - value.keys()
    extra = value.keys() - set(required) - set(optional)
    if missing or extra:
        raise ModelError(
            f"missing fields {sorted(missing)}; unknown fields {sorted(extra)}", path
        )


def name(value, path):
    if not isinstance(value, str) or not value.isidentifier() or len(value) > 128:
        message = "expected an identifier of at most 128 characters"
        if not isinstance(value, str):
            message += "; name must be a string, got " + type(value).__name__
        else:
            shown = value if len(value) <= 80 else value[:77] + "..."
            message += "; got " + repr(shown)
            if not value:
                message += "; identifiers must not be empty"
            elif len(value) > 128:
                message += "; identifier length is " + str(len(value))
            elif value[0].isdigit():
                message += "; identifiers cannot start with a digit"
            else:
                message += "; use Unicode identifier syntax, for example ASCII [A-Za-z_][A-Za-z0-9_]*"
        raise ModelError(message, path)
    if value.lower() in {"true", "false", "tdiv", "ite", "and", "or", "not"}:
        raise ModelError("reserved expression identifier: " + repr(value), path)
    return value


def number(value, sort, path):
    if sort == "Int":
        if type(value) is not int or len(str(value)) > 512:
            raise ModelError(
                "expected an exact integer (not Boolean or floating point)", path
            )
        return Fraction(value)
    if (
        not isinstance(value, str)
        or len(value) > 512
        or not re.fullmatch(r"[+-]?(?:\d+(?:\.\d+)?|\d+/[1-9]\d*)", value)
    ):
        raise ModelError("real literals must be exact decimal/rational strings", path)
    return Fraction(value)


def numeral(value, real=False):
    def integer(n):
        text = str(abs(n)) + (".0" if real else "")
        return f"(- {text})" if n < 0 else text

    if value.denominator == 1:
        return integer(value.numerator)
    return f"(/ {integer(value.numerator)} {integer(value.denominator)})"


def conjunction(parts):
    parts = [p for p in parts if p != "true"]
    if not parts:
        return "true"
    return parts[0] if len(parts) == 1 else "(and " + " ".join(parts) + ")"


class Compiler:
    def __init__(self, model, source):
        self.model = model
        self.source = source
        self.domains = {}
        self.symbols = {}
        self.constants = {}
        self.projection = {}
        self.declarations = []
        self.axioms = []
        self.nodes = 0
        self.binder = 0
        self.rendered_characters = 0

    def span(self, item, path):
        span = item["span"]
        if (
            not isinstance(span, list)
            or len(span) != 2
            or any(type(i) is not int for i in span)
            or not 0 <= span[0] < span[1] <= len(self.source)
        ):
            raise ModelError(
                "span must index a nonempty slice of the exact source text", path
            )

    def sort(self, value, path):
        if not isinstance(value, str) or value not in {
            "Int",
            "Real",
            "Bool",
            *self.domains,
        }:
            raise ModelError("unknown sort", path)
        return value

    @staticmethod
    def target_sort(sort):
        return sort if sort in {"Int", "Real", "Bool"} else "Int"

    def domain_guard(self, value, sort):
        return f"(and (<= 0 {value}) (< {value} {len(self.domains[sort])}))"

    def emit(self):
        m = self.model
        keys(
            m,
            (
                "schema",
                "semantics",
                "decision",
                "domains",
                "symbols",
                "constraints",
                "objectives",
                "objective_order",
                "goal",
                "assumptions",
                "unresolved",
            ),
        )
        if m["schema"] != SCHEMA or m["semantics"] != SEMANTICS:
            raise ModelError("unsupported schema or semantics configuration")
        for field in [
            "domains",
            "symbols",
            "constraints",
            "objectives",
            "assumptions",
            "unresolved",
        ]:
            if not isinstance(m[field], list) or len(m[field]) > 1024:
                raise ModelError("expected a list with at most 1024 entries", field)
        for field in ["assumptions", "unresolved"]:
            if any(not isinstance(x, str) or not x.strip() for x in m[field]):
                raise ModelError("entries must be nonempty strings", field)
        if m["unresolved"]:
            raise ModelError(
                "unresolved interpretations: " + "; ".join(m["unresolved"]),
                "unresolved",
            )
        if m["decision"] not in ["satisfiability", "optimization", "validity"]:
            raise ModelError(
                "explicit satisfiability, optimization, or validity decision required"
            )
        if m["objective_order"] not in ["single", "lexicographic"]:
            raise ModelError(
                "only single and explicit lexicographic objective orders are supported"
            )
        for i, domain in enumerate(m["domains"]):
            path = f"domains[{i}]"
            keys(domain, ("name", "members", "span"), path=path)
            self.span(domain, path)
            n = name(domain["name"], path)
            if n in self.domains or n in {"Int", "Real", "Bool"}:
                raise ModelError("duplicate or reserved domain name", path)
            members = domain["members"]
            if not isinstance(members, list) or len(members) > 1024:
                raise ModelError("expected at most 1024 domain members", path)
            self.domains[n] = members
            for j, member in enumerate(members):
                name(member, path)
                if member in self.constants:
                    raise ModelError(
                        "domain member names must be globally distinct", path
                    )
                self.constants[member] = (str(j), n, "true")
        for i, symbol in enumerate(m["symbols"]):
            path = f"symbols[{i}]"
            keys(
                symbol, ("name", "sort", "arguments", "span"), ("lower", "upper"), path
            )
            self.span(symbol, path)
            n = name(symbol["name"], path)
            if n in self.symbols or n in self.constants:
                raise ModelError("duplicate symbol or domain member", path)
            sort = self.sort(symbol["sort"], path)
            args = symbol["arguments"]
            if not isinstance(args, list) or len(args) > 16:
                raise ModelError("expected at most 16 predicate argument sorts", path)
            args = [self.sort(a, path) for a in args]
            if args and sort != "Bool":
                raise ModelError("only Boolean predicates may have arguments", path)
            target = f"nl_s{i}"
            self.symbols[n] = (target, sort, args)
            self.declarations.append(
                f"(declare-fun {target} ({' '.join(self.target_sort(a) for a in args)}) {self.target_sort(sort)})"
            )
            if not args:
                self.projection[n] = {"target": target, "sort": sort}
                if sort in self.domains:
                    self.axioms.append(self.domain_guard(target, sort))
            for bound, op in [("lower", ">="), ("upper", "<=")]:
                if bound in symbol:
                    if args or sort not in ["Int", "Real"]:
                        raise ModelError(
                            "bounds require a scalar numeric variable", path
                        )
                    v = number(symbol[bound], sort, path)
                    self.axioms.append(f"({op} {target} {numeral(v, sort == 'Real')})")
            if "lower" in symbol and "upper" in symbol:
                if number(symbol["lower"], sort, path) > number(
                    symbol["upper"], sort, path
                ):
                    raise ModelError("reversed declaration bounds", path)
        constraints = [
            self.statement(c, f"constraints[{i}]")
            for i, c in enumerate(m["constraints"])
        ]
        if m["decision"] == "validity":
            if m["goal"] is None or m["objectives"]:
                raise ModelError("validity requires a goal and forbids objectives")
            constraints.append(f"(not {self.statement(m['goal'], 'goal')})")
        elif m["goal"] is not None:
            raise ModelError("a goal is only meaningful for validity")
        if (m["decision"] == "optimization") != bool(m["objectives"]):
            raise ModelError(
                "optimization requires objectives; other decisions forbid them"
            )
        if len(m["objectives"]) > 1 and m["objective_order"] != "lexicographic":
            raise ModelError("multiple objectives require explicit lexicographic order")
        objectives = []
        for i, obj in enumerate(m["objectives"]):
            path = f"objectives[{i}]"
            keys(obj, ("direction", "expr", "span"), path=path)
            self.span(obj, path)
            if obj["direction"] not in ["minimize", "maximize"]:
                raise ModelError("unknown objective direction", path)
            value, sort, defined = self.expr(obj["expr"], {}, path)
            if sort not in ["Int", "Real"]:
                raise ModelError("objective must be numeric", path)
            constraints.append(defined)
            objectives.append(f"({obj['direction']} {value})")
        priority = ["(set-option :opt.priority lex)"] if len(objectives) > 1 else []
        return "\n".join(
            [
                "(set-logic ALL)",
                *priority,
                *self.declarations,
                *(f"(assert {c})" for c in self.axioms + constraints),
                *objectives,
                "(check-sat)",
                "",
            ]
        )

    def statement(self, item, path):
        keys(item, ("expr", "span"), path=path)
        self.span(item, path)
        value, sort, defined = self.expr(item["expr"], {}, path)
        if sort != "Bool":
            raise ModelError("constraint/goal must be Boolean", path)
        return conjunction([defined, value])

    def expr(self, e, scope, path, depth=0):
        result = self._expr(e, scope, path, depth)
        size = sum(len(part) for part in result)
        self.rendered_characters += size
        if size > 1048576 or self.rendered_characters > 4194304:
            raise ModelError("expanded expression resource limit exceeded", path)
        return result

    def _expr(self, e, scope, path, depth=0):
        self.nodes += 1
        if depth > MAX_DEPTH or self.nodes > MAX_NODES:
            raise ModelError("expression resource limit exceeded", path)
        if not isinstance(e, dict):
            raise ModelError("expression must be a typed AST object", path)
        if "var" in e and "op" not in e:
            keys(e, ("var",), path=path)
            n = name(e["var"], path)
            if n in scope:
                return scope[n]
            if n in self.constants:
                return self.constants[n]
            if n not in self.symbols or self.symbols[n][2]:
                raise ModelError(f"unknown scalar symbol {n!r}", path)
            target, sort, _ = self.symbols[n]
            return target, sort, "true"
        if "literal" in e:
            keys(e, ("literal", "sort"), path=path)
            sort = e["sort"]
            if sort == "Bool" and type(e["literal"]) is bool:
                return str(e["literal"]).lower(), sort, "true"
            if sort not in ["Int", "Real"]:
                raise ModelError("invalid literal sort/value", path)
            return (
                numeral(number(e["literal"], sort, path), sort == "Real"),
                sort,
                "true",
            )
        if e.get("op") in ["forall", "exists"]:
            keys(e, ("op", "var", "domain", "body"), path=path)
            n = name(e["var"], path)
            domain = e["domain"]
            if not isinstance(domain, str) or domain not in self.domains:
                raise ModelError("quantifier requires an explicit finite domain", path)
            self.binder += 1
            target = f"nl_b{self.binder}"
            inner = dict(scope, **{n: (target, domain, "true")})
            value, sort, defined = self.expr(
                e["body"], inner, path + ".body", depth + 1
            )
            if sort != "Bool":
                raise ModelError("quantifier body must be Boolean", path)
            body = conjunction([defined, value])
            guard = self.domain_guard(target, domain)
            body = (
                f"(=> {guard} {body})"
                if e["op"] == "forall"
                else conjunction([guard, body])
            )
            return f"({e['op']} (({target} Int)) {body})", "Bool", "true"
        keys(e, ("op", "args"), ("symbol",), path)
        op = e["op"]
        if (
            not isinstance(op, str)
            or not isinstance(e["args"], list)
            or len(e["args"]) > 1024
        ):
            raise ModelError("invalid operator/argument list", path)
        args = [
            self.expr(a, scope, f"{path}.args[{i}]", depth + 1)
            for i, a in enumerate(e["args"])
        ]
        if op != "call" and "symbol" in e:
            raise ModelError(
                "symbol field is only valid on predicate applications", path
            )
        values = [a[0] for a in args]
        sorts = [a[1] for a in args]
        defined = conjunction([a[2] for a in args])

        def arity(n):
            if len(args) != n:
                raise ModelError(f"{op} expects {n} arguments", path)

        if op == "call":
            symbol = e.get("symbol")
            if not isinstance(symbol, str) or symbol not in self.symbols:
                raise ModelError("unknown predicate", path)
            target, sort, signature = self.symbols[symbol]
            if sort != "Bool" or signature != sorts:
                raise ModelError(
                    "predicate argument sorts do not match its declaration", path
                )
            value = f"({target} {' '.join(values)})" if args else target
            return conjunction([defined, value]), "Bool", "true"
        if op in ["and", "or", "not", "implies"]:
            if any(s != "Bool" for s in sorts) or not args:
                raise ModelError("logical operator requires Boolean operands", path)
            if op in ["not", "implies"]:
                arity(1 if op == "not" else 2)
            values = [conjunction([a[2], a[0]]) for a in args]
            target_op = "=>" if op == "implies" else op
            return f"({target_op} {' '.join(values)})", "Bool", "true"
        if op == "ite":
            arity(3)
            if sorts[0] != "Bool" or sorts[1] != sorts[2]:
                raise ModelError(
                    "ite needs a Boolean condition and equal branch sorts", path
                )
            d = conjunction(
                [args[0][2], f"(ite {values[0]} {args[1][2]} {args[2][2]})"]
            )
            v = f"(ite {' '.join(values)})"
            return (
                (conjunction([d, v]), "Bool", "true")
                if sorts[1] == "Bool"
                else (v, sorts[1], d)
            )
        if op in ["eq", "ne"] and len(args) == 2 and sorts[0] == sorts[1]:
            value = f"(= {' '.join(values)})"
            return (
                conjunction([defined, f"(not {value})" if op == "ne" else value]),
                "Bool",
                "true",
            )
        numeric = [
            "add",
            "sub",
            "mul",
            "div",
            "tdiv",
            "neg",
            "lt",
            "le",
            "gt",
            "ge",
            "eq",
            "ne",
        ]
        if op not in numeric or any(s not in ["Int", "Real"] for s in sorts):
            raise ModelError("unknown operator or incompatible operand sorts", path)
        arity(1 if op == "neg" else 2)
        real = "Real" in sorts or op == "div"
        if op == "tdiv" and real:
            raise ModelError("tdiv requires integers", path)
        values = [f"(to_real {v})" if real and s == "Int" else v for v, s, _ in args]
        smtop = {
            "add": "+",
            "sub": "-",
            "mul": "*",
            "div": "/",
            "neg": "-",
            "lt": "<",
            "le": "<=",
            "gt": ">",
            "ge": ">=",
            "eq": "=",
            "ne": "=",
        }.get(op)
        if op == "tdiv":
            a, b = values
            q = f"(div (ite (< {a} 0) (- {a}) {a}) (ite (< {b} 0) (- {b}) {b}))"
            value = f"(ite (= (< {a} 0) (< {b} 0)) {q} (- {q}))"
        else:
            value = f"({smtop} {' '.join(values)})"
        if op in ["div", "tdiv"]:
            defined = conjunction(
                [defined, f"(not (= {values[1]} {'0.0' if real else '0'}))"]
            )
        if op in ["lt", "le", "gt", "ge", "eq", "ne"]:
            return (
                conjunction([defined, f"(not {value})" if op == "ne" else value]),
                "Bool",
                "true",
            )
        return value, "Real" if real else "Int", defined


def compile_model(model, source):
    compiler = Compiler(model, source)
    script = compiler.emit()
    return script, compiler.projection, compiler.domains


def _replay_value(value, sort, domains, path):
    """Validate one exact source-level witness value's TYPE against its sort.

    Mirrors the projection's contract: Python bool for Bool, int for Int,
    a domain member NAME for a finite domain, and an exact
    int/Fraction/rational string for Real -- never a float. Being a member of
    the domain is a property of the model, checked by the caller as a
    violation rather than an interface error.
    """
    if sort == "Bool":
        if type(value) is not bool:
            raise ModelError(f"{path} requires an exact Boolean")
        return value
    if sort == "Int":
        if type(value) is not int:
            raise ModelError(f"{path} requires an exact integer")
        return Fraction(value)
    if sort in domains:
        if not isinstance(value, str):
            raise ModelError(f"{path} requires the name of a {sort!r} member")
        return value
    if type(value) not in [int, Fraction] and not isinstance(value, str):
        raise ModelError(f"{path} requires an exact rational, not a float")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ModelError(f"{path} requires an exact rational: {exc}") from exc


def replay_model(model, source, assignment):
    """Replay one exact source-level assignment against every source constraint.

    This is the typed configuration's witness check: the values are substituted
    into the candidate's own ASTs -- not into the emitted SMT -- so a wrong
    encoding or a wrong projection cannot validate itself. Evaluation mirrors
    the compiler's relational semantics exactly: arithmetic is rational
    (`Fraction`, no floats), a constraint holds iff its terms are DEFINED and
    its value is true, `ite` evaluates only the taken branch (so `1 div x` in
    the untaken branch cannot make a constraint undefined), quantifiers
    enumerate their explicit finite domains, and truncating division follows
    the same sign rule the encoding writes. Predicate applications cannot be
    replayed from scalar values -- their witness is an interpretation -- and
    are refused by name.

    Returns a factual report; interpreting it (validity polarity, optimality)
    stays with the caller:
      holds            -- the assignment satisfies everything the source
                          declares: bounds, domains, constraints, and the
                          objectives' definedness
      violations       -- [{kind, index, span, fragment}]; kind is "bound",
                          "domain", "constraint" or "objective-definedness"
      goal             -- the goal's value for a validity decision, else None
      objectives       -- [{value, defined}] in declaration order
    """
    domains = {d["name"]: d["members"] for d in model.get("domains", [])}
    env = {}
    declaration_violations = []
    for i, s in enumerate(model.get("symbols", [])):
        n = s["name"]
        if s["arguments"]:
            continue  # predicates carry no scalar value; see `call` below
        if n not in assignment:
            raise ModelError(f"missing value for symbol {n!r}")
        sort = s["sort"]
        value = _replay_value(assignment[n], sort, domains, n)
        env[n] = value
        # Declaration bounds and domain membership are source constraints too
        # -- the compiler asserts them as axioms -- so a value outside them is
        # a violation of the replayed model, not an interface error.
        if sort in domains and value not in domains[sort]:
            s0, s1 = s["span"]
            declaration_violations.append(
                {
                    "kind": "domain",
                    "index": i,
                    "span": [s0, s1],
                    "fragment": source[s0:s1],
                }
            )
        if sort in ["Int", "Real"]:
            below = "lower" in s and value < Fraction(s["lower"])
            above = "upper" in s and value > Fraction(s["upper"])
            if below or above:
                s0, s1 = s["span"]
                declaration_violations.append(
                    {
                        "kind": "bound",
                        "index": i,
                        "span": [s0, s1],
                        "fragment": source[s0:s1],
                    }
                )
    extra = set(assignment) - env.keys()
    if extra:
        raise ModelError(
            "assignment names no scalar symbol: " + ", ".join(sorted(extra))
        )
    members = {
        member
        for d in model.get("domains", [])
        for member in d["members"]
    }

    def ev(e, scope, path):
        """(value, defined); Bool values are Python bool, numeric are Fraction."""
        if not isinstance(e, dict):
            raise ModelError("expression must be a typed AST object", path)
        if "var" in e and "op" not in e:
            n = e["var"]
            if n in scope:
                return scope[n], True
            if n in members:
                return n, True
            if n in env:
                return env[n], True
            raise ModelError(f"unknown scalar symbol {n!r}", path)
        if "literal" in e:
            sort = e["sort"]
            if sort == "Bool":
                return bool(e["literal"]), True
            return Fraction(e["literal"]), True
        op = e.get("op")
        if op in ["forall", "exists"]:
            domain = e["domain"]
            if domain not in domains:
                raise ModelError("quantifier requires an explicit finite domain", path)
            outcomes = [
                ev(e["body"], dict(scope, **{e["var"]: member}), path + ".body")
                for member in domains[domain]
            ]
            # The encoding folds definedness into the body: each binding
            # contributes (defined AND value) to the aggregate.
            effective = [d and bool(v) for v, d in outcomes]
            return (all(effective) if op == "forall" else any(effective)), True
        args = [ev(a, scope, f"{path}.args[{i}]") for i, a in enumerate(e["args"])]
        if op == "call":
            raise ModelError(
                f"predicate {e.get('symbol')!r} cannot be replayed from scalar "
                "values; its witness is an interpretation, which this replay "
                "does not decode",
                path,
            )
        if op in ["and", "or"]:
            effective = [d and bool(v) for v, d in args]
            return (all(effective) if op == "and" else any(effective)), True
        if op == "not":
            (v, d) = args[0]
            return not (d and bool(v)), True
        if op == "implies":
            (v1, d1), (v2, d2) = args
            return not (d1 and bool(v1)) or (d2 and bool(v2)), True
        if op == "ite":
            (vc, dc) = args[0]
            # Only the TAKEN branch contributes value and definedness, exactly
            # as the encoding's (ite c d1 d2) guard short-circuits: evaluating
            # the other branch is harmless (ev is pure) but its definedness
            # must not count.
            (v, d) = args[1] if vc else args[2]
            return v, dc and d
        if op in ["eq", "ne"] and len(args) == 2:
            (v1, d1), (v2, d2) = args
            value = v1 == v2
            return (not value if op == "ne" else value), d1 and d2
        values = [v for v, _ in args]
        defined = all(d for _, d in args)
        if op in ["add", "sub", "mul"]:
            a, b = values
            return {"add": a + b, "sub": a - b, "mul": a * b}[op], defined
        if op == "neg":
            return -values[0], defined
        if op in ["div", "tdiv"]:
            a, b = values
            if b == 0:
                # The value is irrelevant once defined is false; the encoding
                # constrains only the guard.
                return Fraction(0), False
            if op == "div":
                return a / b, defined
            if a.denominator != 1 or b.denominator != 1:
                raise ModelError("tdiv requires integers", path)
            q = abs(a.numerator) // abs(b.numerator)
            return Fraction(q if (a < 0) == (b < 0) else -q), defined
        if op in ["lt", "le", "gt", "ge"]:
            a, b = values
            value = {"lt": a < b, "le": a <= b, "gt": a > b, "ge": a >= b}[op]
            return value, defined
        raise ModelError(f"unknown operator {op!r}", path)

    def statement(item, path):
        value, defined = ev(item["expr"], {}, path)
        return defined and bool(value)

    violations = list(declaration_violations)
    for i, c in enumerate(model.get("constraints", [])):
        if not statement(c, f"constraints[{i}]"):
            s0, s1 = c["span"]
            violations.append(
                {
                    "kind": "constraint",
                    "index": i,
                    "span": [s0, s1],
                    "fragment": source[s0:s1],
                }
            )
    goal = None
    if model.get("goal") is not None:
        goal = statement(model["goal"], "goal")
    objectives = []
    for i, obj in enumerate(model.get("objectives", [])):
        value, defined = ev(obj["expr"], {}, f"objectives[{i}]")
        objectives.append({"value": value, "defined": defined})
        if not defined:
            # The compiler asserts the objective's definedness as a constraint
            # of the model, so an undefined objective is a violation, not a
            # value -- and its reported value means nothing.
            s0, s1 = obj["span"]
            violations.append(
                {
                    "kind": "objective-definedness",
                    "index": i,
                    "span": [s0, s1],
                    "fragment": source[s0:s1],
                }
            )
    return {
        "holds": not violations,
        "violations": violations,
        "goal": goal,
        "objectives": objectives,
    }
