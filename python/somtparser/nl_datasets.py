"""Reference-side dataset adapters. Never pass these annotations to a proposer.

NL4Opt is interpreted as nonnegative continuous LP. This adapter preserves the
structured declarations plus separately recorded, content-bound corrections.
Unknown numbers, operators and aliases are errors, never silently zero-filled.
"""

from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
from importlib import resources
import json
from math import gcd
from pathlib import Path
import re
import xml.etree.ElementTree as ET

from ._nl_model import ModelError

NL4OPT_REVISION = "49f1e0d66b7fdcd33305a7f281c2a7c13f5620ea"
INDUSCP_REVISION = "82054fa8c3784e20ebc17bc972069370f37186a8"
LP_CONTEXT = {
    "numeric_domain": "NL4Opt task convention: decision variables are nonnegative continuous Real numbers, even for count nouns; use no General/Binary section.",
    "decision": "Single-objective linear optimization; preserve the requested direction and exact coefficients.",
}


def _unit_literal(text):
    """Recognize full numeric annotations in the source's existing units.

    This is lexical normalization, not dimensional analysis or unit conversion.
    An anchored grammar prevents text such as '2 dollars or 3' being guessed.
    """
    number = r"[+-]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?"
    match = re.fullmatch(
        rf"\$\s*({number})\.?|({number})\s*\$\.?|({number})\s+minutes?\.?", text
    )
    return next(x for x in match.groups() if x is not None) if match else text


def exact_number(value):
    if not isinstance(value, str):
        raise ModelError("reference number must be a string")
    text = _unit_literal(value.strip().lower())
    scale = Fraction(1)
    if text.endswith("percent") or text.endswith("%"):
        scale = Fraction(1, 100)
        text = re.sub(r"(?:percent|%)$", "", text).strip()
    text = re.sub(r"\s+times$", "", text)
    words = {
        "zero": 0,
        "one": 1,
        "two": 2,
        "three": 3,
        "four": 4,
        "five": 5,
        "six": 6,
        "seven": 7,
        "eight": 8,
        "nine": 9,
        "ten": 10,
        "fifteen": 15,
        "twenty": 20,
        "thirty": 30,
        "one hundred thousand": 100000,
        "twice": 2,
        "thrice": 3,
        "half": Fraction(1, 2),
        "third": Fraction(1, 3),
        "a third": Fraction(1, 3),
        "one third": Fraction(1, 3),
    }
    if text in words:
        return Fraction(words[text]) * scale
    # Only the explicitly recognized unit forms above are stripped.
    if not re.fullmatch(r"[+-]?(?:\d{1,3}(?:,\d{3})+|\d+)(?:\.\d+)?", text):
        raise ModelError("unsupported exact reference number: " + value)
    return Fraction(text.replace(",", "")) * scale


def nl4opt_records(root, split):
    if split not in ("train", "dev", "test"):
        raise ModelError("unknown NL4Opt split")
    seen = set()
    for line in (Path(root) / "generation_data" / (split + ".jsonl")).open(
        encoding="utf-8"
    ):
        for identifier, record in json.loads(line).items():
            if identifier in seen:
                raise ModelError("duplicate NL4Opt record identifier")
            seen.add(identifier)
            yield identifier, record


def _lcm(values):
    result = 1
    for value in values:
        result = result * value // gcd(result, value)
    return result


@dataclass(frozen=True)
class LinearReference:
    names: tuple
    rows: tuple  # (coefficient vector, upper bound), all <=
    objective: tuple
    maximize: bool
    adjustments: tuple = ()

    @property
    def objective_scale(self):
        return _lcm(x.denominator for x in self.objective)

    def to_lp(self):
        def expression(coefficients):
            terms = [
                ("+" if c >= 0 else "-") + " " + str(abs(c)) + " x" + str(i)
                for i, c in enumerate(coefficients)
                if c
            ]
            return " ".join(terms) if terms else "0 x0"

        lines = [
            "Maximize" if self.maximize else "Minimize",
            " obj: "
            + expression([int(x * self.objective_scale) for x in self.objective]),
            "Subject To",
        ]
        for i, (coeffs, limit) in enumerate(self.rows):
            scale = _lcm(x.denominator for x in (*coeffs, limit))
            lines.append(
                f" c{i}: "
                + expression([int(x * scale) for x in coeffs])
                + " <= "
                + str(int(limit * scale))
            )
        lines += ["Bounds"] + [f" x{i} >= 0" for i in range(len(self.names))] + ["End"]
        return "\n".join(lines) + "\n"


@lru_cache(maxsize=1)
def _correction_ledger():
    data = json.loads(
        resources.files(__package__)
        .joinpath("nl4opt_corrections.json")
        .read_text(encoding="utf-8")
    )
    if (
        data["schema"] != "somt-nl4opt-corrections-v1"
        or data["dataset_revision"] != NL4OPT_REVISION
    ):
        raise ModelError("incompatible NL4Opt correction ledger")
    return {entry["record_sha256"]: entry for entry in data["entries"]}


def _reviewed_record(record):
    encoded = json.dumps(
        record,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    )
    digest = hashlib.sha256(encoded.encode("utf-8")).hexdigest()
    entry = _correction_ledger().get(digest)
    if entry is None:
        return record, []
    result = json.loads(encoded)
    adjustments = []
    for change in entry["changes"]:
        change = json.loads(json.dumps(change))
        parent = result
        for key in change["path"][:-1]:
            parent = parent[key]
        key = change["path"][-1]
        if (
            parent[key] != change["before"]
            or change["source_quote"] not in record["document"]
        ):
            raise ModelError("reviewed correction precondition does not match")
        parent[key] = json.loads(json.dumps(change["after"]))
        adjustments.append(
            dict(
                kind="reviewed-annotation-correction",
                id=entry["id"],
                split=entry["split"],
                record_sha256=digest,
                **change,
            )
        )
    return result, adjustments


def nl4opt_reference(record, *, apply_corrections=True):
    """Import a reference with exact arithmetic and auditable corrections.

    Corrections apply only to exact record hashes in the reviewed ledger. The
    caller's record is never modified. Set apply_corrections=False to inspect
    raw annotations; unit-notation parsing still applies. Unreviewed duplicate
    aliases or empty objectives continue to raise instead of being guessed.
    """
    record, adjustments = (
        _reviewed_record(record) if apply_corrections else (record, [])
    )
    mapping = record["order_mapping"]
    if not mapping or any(type(v) is not int or v < 0 for v in mapping.values()):
        raise ModelError("invalid reference variable mapping")
    n = max(mapping.values()) + 1
    if set(mapping.values()) != set(range(n)):
        raise ModelError("noncontiguous reference variable mapping")
    names = tuple(next(k for k, v in mapping.items() if v == i) for i in range(n))

    def index(name):
        if name not in mapping:
            raise ModelError("unknown reference alias: " + str(name))
        return mapping[name]

    def number(value, path):
        result = exact_number(value)
        if _unit_literal(value.strip().lower()) != value.strip().lower():
            adjustments.append(
                dict(
                    kind="number-notation",
                    path=path,
                    before=value,
                    after=str(result),
                    rule="currency-or-minute-literal-v1",
                    semantics="magnitude in the source unit; no unit conversion",
                )
            )
        return result

    def vector(terms, path):
        result = [Fraction(0)] * n
        used = set()
        for name, value in terms.items():
            i = index(name)
            if i in used:
                raise ModelError("duplicate coefficient aliases")
            used.add(i)
            result[i] = number(value, path + [name])
        return result

    objective = record["obj_declaration"]
    direction = objective["direction"].lower()
    minimum = {
        "minimize",
        "minimum",
        "reduce",
        "minimizing",
        "decrease",
        "minimal",
        "lowest",
        "minimizes",
    }
    maximum = {"maximize", "maximum", "maximized", "most", "highest", "maximizing"}
    if direction not in minimum | maximum:
        raise ModelError("unknown objective direction")
    rows = []
    for position, constraint in enumerate(record["const_declarations"]):
        path = ["const_declarations", position]
        kind = constraint["type"]
        coeffs = [Fraction(0)] * n
        limit = Fraction(0)
        if kind == "linear":
            coeffs, limit = (
                vector(constraint["terms"], path + ["terms"]),
                number(constraint["limit"], path + ["limit"]),
            )
        elif kind == "sum":
            coeffs, limit = (
                [Fraction(1)] * n,
                number(constraint["limit"], path + ["limit"]),
            )
        elif kind in ("upperbound", "lowerbound"):
            coeffs[index(constraint["var"])] = Fraction(1)
            limit = number(constraint["limit"], path + ["limit"])
        elif kind == "ratio":
            ratio = number(constraint["limit"], path + ["limit"])
            coeffs = [-ratio] * n
            coeffs[index(constraint["var"])] += 1
        elif kind in ("xy", "xby"):
            coeffs[index(constraint["x_var"])] += 1
            coeffs[index(constraint["y_var"])] -= (
                number(constraint["param"], path + ["param"]) if kind == "xby" else 1
            )
        else:
            raise ModelError("unsupported reference constraint: " + kind)
        operator = constraint["operator"]
        if operator == "GREATER_OR_EQUAL":
            coeffs, limit = [-x for x in coeffs], -limit
        elif operator != "LESS_OR_EQUAL":
            raise ModelError("unknown constraint direction")
        rows.append((tuple(coeffs), limit))
    if objective["type"] == "objvar":
        if not objective["vars"]:
            raise ModelError("reference objective has no annotated variables")
        terms = {name: "1" for name in objective["vars"]}
    elif objective["type"] == "objective":
        if not objective["terms"]:
            raise ModelError("reference objective has no annotated terms")
        terms = objective["terms"]
    else:
        raise ModelError("unknown objective declaration type")
    return LinearReference(
        names,
        tuple(rows),
        tuple(vector(terms, ["obj_declaration", "terms"])),
        direction in maximum,
        tuple(adjustments),
    )


@dataclass(frozen=True)
class IndusCPTask:
    """One runnable IndusCP reference task: pinned model code plus one instance.

    The reference model is the statement's `code` field, the artifact the
    pinned dataset itself publishes per problem; the disk copies under
    cost_data/ are upstream variants that do not all match the shipped JSON
    schema. `extra_args` carries the model-required PyCSP3 variant option
    (induscp_required_variant); it is empty for all other problems.
    """

    problem: str
    instance: str
    model: str
    data_path: Path
    expected: int | None
    extra_args: tuple = ()


def induscp_statements(root):
    path = Path(root) / "data" / "induscp" / "statements.json"
    entries = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(entries, list):
        raise ModelError("IndusCP statements.json is not a list")
    statements = {}
    for entry in entries:
        name, code = entry.get("name"), entry.get("code")
        if not isinstance(name, str) or not isinstance(code, str) or not code:
            raise ModelError("IndusCP statement lacks a name or reference code")
        if name in statements:
            raise ModelError("duplicate IndusCP statement: " + name)
        statements[name] = entry
    return statements


def induscp_required_variant(code):
    """First variant a model's own assertion admits, or None.

    PyCSP3 models that cannot run without an explicit variant say so with
    `assert variant() in (...)`; all other models call variant("default") and
    need no option. The choice is positional (first listed), matching the
    order of each problem README's documented invocations.
    """
    match = re.search(r"assert\s+variant\(\)\s*in\s*[([{]([^)\]}]+)", code)
    if not match:
        return None
    names = re.findall(r"['\"]([^'\"]+)['\"]", match[1])
    if not names:
        raise ModelError("unrecognized variant assertion in IndusCP model")
    return names[0]


def induscp_expected_objective(text):
    """The dataset's published objective value for an instance, if present."""
    if text is None:
        return None
    stripped = text.strip()
    if not re.fullmatch(r"-?\d+", stripped):
        raise ModelError("unsupported IndusCP expected objective: " + repr(text))
    return int(stripped)


def induscp_tasks(root):
    """Enumerate (problem, instance) tasks in deterministic order."""
    root = Path(root)
    statements = induscp_statements(root)
    cost_data = root / "data" / "induscp" / "cost_data"
    orphans = {
        path.name
        for path in cost_data.iterdir()
        if path.is_dir() and path.name not in statements
    }
    if orphans:
        raise ModelError("IndusCP cost_data without a statement: " + repr(sorted(orphans)))
    for name in sorted(statements):
        problem_dir = cost_data / name
        if not problem_dir.is_dir():
            raise ModelError("IndusCP statement has no cost_data directory: " + name)
        instances = []
        for path in problem_dir.iterdir():
            if path.suffix != ".json":
                continue
            if not path.stem.isdigit():
                raise ModelError("non-integer IndusCP instance name: " + path.name)
            instances.append(path)
        if not instances:
            raise ModelError("IndusCP problem has no instances: " + name)
        code = statements[name]["code"]
        variant = induscp_required_variant(code)
        extra_args = ("-variant=" + variant,) if variant else ()
        for path in sorted(instances, key=lambda p: int(p.stem)):
            out_path = path.with_suffix(".out")
            yield IndusCPTask(
                problem=name,
                instance=path.stem,
                model=code,
                data_path=path,
                expected=induscp_expected_objective(
                    out_path.read_text(encoding="utf-8") if out_path.exists() else None
                ),
                extra_args=extra_args,
            )


def normalize_pycsp3_singleton_counts(xml):
    """Normalize PyCSP3 singleton count groups into equivalent intensions.

    XCSP3's published count grammar requires two variables, but PyCSP3 2.6.1
    emits singleton group instances. Four shapes are recognized, all with one
    literal sought value: a "%..." list with a literal comparison bound; a "%0"
    list (the compactor's singleton-row form) with a literal bound; a "%..."
    list whose condition bound is the row's %0 FIRST token; and the pair form,
    a "%0" list with a "%1" condition bound (row: variable then bound).
    Parameter bindings follow the xcsp3 frontend's group expansion
    (substituteFormals binds %0..%k before %... takes the tail). Only rows
    whose singleton is a plain variable reference are rewritten; slices and
    multi-variable rows stay in the group for the frontend. A single leftover
    row would make an invalid group (the frontend requires at least two
    <args>), so it is unwrapped into the direct count the group expands to when
    that substitution is exact for the recognized template; otherwise the whole
    group is left untouched. Every rewrite is logged.
    """
    if re.search(r"<!\s*(DOCTYPE|ENTITY)", xml, re.I):
        raise ModelError("external XML declarations are not supported")
    root = ET.fromstring(xml)
    rewrites = []
    constraints = root.find("constraints")
    if constraints is None:
        return xml, rewrites
    variable_re = r"[A-Za-z_][A-Za-z_0-9]*(?:\[\d+\])*"
    for group in list(constraints):
        template = group.find("count") if group.tag == "group" else None
        if template is None:
            continue
        # Reification, soft constraints and extra child forms have a different
        # contract. Leave them untouched for the frontend to accept or refuse.
        harmless = {"id", "note", "class"}
        if (
            set(group.attrib) - harmless
            or set(template.attrib) - harmless
            or len(group.findall("count")) != 1
            or any(child.tag not in {"count", "args"} for child in group)
            or [child.tag for child in template] != ["list", "values", "condition"]
            or any(child.attrib or len(child) for child in template)
        ):
            continue
        list_text = (template.findtext("list") or "").strip()
        value = (template.findtext("values") or "").strip()
        condition = (template.findtext("condition") or "").strip()
        cond_literal = re.fullmatch(r"\((eq|ne|lt|le|gt|ge),\s*(-?\d+)\)", condition)
        cond_parameter = re.fullmatch(r"\((eq|ne|lt|le|gt|ge),\s*%0\)", condition)
        cond_parameter_1 = re.fullmatch(r"\((eq|ne|lt|le|gt|ge),\s*%1\)", condition)
        if not re.fullmatch(r"-?\d+", value):
            continue
        if list_text == "%..." and cond_literal:
            rule = "singleton-count-to-indicator-v1"
        elif list_text == "%0" and cond_literal:
            rule = "singleton-count-list-parameter-to-indicator-v1"
        elif list_text == "%..." and cond_parameter:
            rule = "singleton-count-condition-parameter-to-indicator-v1"
        elif list_text == "%0" and cond_parameter_1:
            rule = "singleton-count-parameter-pair-to-indicator-v1"
        else:
            continue  # an unrecognized count template shape stays untouched
        cond_any = cond_literal or cond_parameter or cond_parameter_1
        op = cond_any[1]

        def singleton_row(args):
            """(variable, bound) if this args row is a singleton count row."""
            text = (args.text or "").strip()
            if args.attrib or len(args):
                return None
            if cond_literal:
                # With a "%0" list the row is the whole singleton; with "%..."
                # the row text must be exactly one plain variable either way.
                return (text, cond_literal[2]) if re.fullmatch(variable_re, text) else None
            tokens = text.split()
            if len(tokens) != 2:
                return None
            if cond_parameter:
                # The %0 bound is the row's first token, %... takes the tail —
                # the frontend's substituteFormals binding, verified against it.
                variable, bound = tokens[1], tokens[0]
            else:
                # "%0" list and "%1" bound: variable first, bound second.
                variable, bound = tokens
            if re.fullmatch(variable_re, variable) and re.fullmatch(
                r"-?\d+|" + variable_re, bound
            ):
                return variable, bound
            return None

        matched = [
            (args, hit[0], hit[1])
            for args in group.findall("args")
            if (hit := singleton_row(args)) is not None
        ]
        kept = [a for a in group.findall("args") if all(a is not m[0] for m in matched)]
        if not matched:
            continue
        if len(kept) == 1:
            # A leftover of one row would make an invalid group (the frontend
            # requires at least two <args>), so unwrap it into the direct count
            # the group expands to — but only when the substitution is exact
            # for the recognized template. Otherwise leave the group untouched.
            text = (kept[0].text or "").strip()
            tokens = text.split()
            if list_text == "%0" and cond_literal:
                unwrap = len(tokens) == 1  # extra tokens would be silently dropped
                list_value, bound_text = text, condition
            elif list_text == "%0":  # %1 condition: variable first, bound second
                unwrap = len(tokens) == 2
                list_value = tokens[0] if unwrap else ""
                bound_text = f"({op},{tokens[1]})" if unwrap else ""
            elif cond_parameter:
                unwrap = len(tokens) >= 2
                list_value = " ".join(tokens[1:])
                bound_text = f"({op},{tokens[0]})"
            else:
                unwrap, list_value, bound_text = True, text, condition
            if not unwrap or not list_value:
                continue
            count = ET.SubElement(constraints, "count")
            ET.SubElement(count, "list").text = " " + list_value + " "
            ET.SubElement(count, "values").text = " " + value + " "
            ET.SubElement(count, "condition").text = " " + bound_text + " "
            rewrites.append(
                {
                    "rule": "count-group-unwrap-v1",
                    "variable": text,
                    "expression": f"count({list_value}) {bound_text} with values {value}",
                }
            )
            group.remove(kept[0])
        for args, variable, bound in matched:
            expression = f"{op}(if(eq({variable},{value}),1,0),{bound})"
            ET.SubElement(constraints, "intension").text = expression
            group.remove(args)
            rewrites.append(
                {"rule": rule, "variable": variable, "expression": expression}
            )
        if not group.findall("args"):
            constraints.remove(group)
    return ET.tostring(root, encoding="unicode"), rewrites
