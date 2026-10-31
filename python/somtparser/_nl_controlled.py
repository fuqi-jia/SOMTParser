"""A deterministic, bilingual controlled-language proposal backend.

Each nonempty line is one statement. Every unsupported line remains an
unresolved item; it never disappears from a successful translation.
"""
import ast
import re

from ._nl_model import MAX_DEPTH, MAX_TEXT, ModelError, SCHEMA, SEMANTICS


def expression(text, depth=0):
    if depth > MAX_DEPTH:
        raise ModelError("expression nesting limit exceeded")
    text = text.strip()
    for pattern, op in [
        (r"For every\s+(\w+)\s+in\s+(\w+)\s*,\s*(.+)", "forall"),
        (r"There exists\s+(\w+)\s+in\s+(\w+)\s+such that\s+(.+)", "exists"),
        (r"对于每个\s*(\w+)\s*属于\s*(\w+)\s*[，,]\s*(.+)", "forall"),
        (r"存在\s*(\w+)\s*属于\s*(\w+)\s*使得\s*(.+)", "exists"),
    ]:
        match = re.fullmatch(pattern, text, re.I)
        if match:
            return {
                "op": op,
                "var": match[1],
                "domain": match[2],
                "body": expression(match[3], depth + 1),
            }
    match = re.fullmatch(r"If\s+(.+?),?\s+then\s+(.+)", text, re.I)
    if not match:
        match = re.fullmatch(r"如果\s*(.+?)[，,]?\s*那么\s*(.+)", text)
    if match:
        return {
            "op": "implies",
            "args": [expression(match[1], depth + 1), expression(match[2], depth + 1)],
        }
    # Word boundaries keep variables such as 'android' and 'floor' intact.
    replacements = [
        (r"\bis not equal to\b", "!="),
        (r"\bis greater than or equal to\b", ">="),
        (r"\bis less than or equal to\b", "<="),
        (r"\bis at least\b", ">="),
        (r"\bis at most\b", "<="),
        (r"\bis greater than\b", ">"),
        (r"\bis less than\b", "<"),
        (r"\bis equal to\b", "=="),
        (r"\bplus\b", "+"),
        (r"\bminus\b", "-"),
        (r"\btimes\b", "*"),
        (r"\bdivided by\b", "/"),
        (r"\btrue\b", "True"),
        (r"\bfalse\b", "False"),
        (r"不等于", "!="),
        (r"大于等于|至少", ">="),
        (r"小于等于|至多", "<="),
        (r"大于", ">"),
        (r"小于", "<"),
        (r"等于", "=="),
        (r"并且", " and "),
        (r"或者", " or "),
        (r"并非", " not "),
        (r"加上", "+"),
        (r"减去", "-"),
        (r"乘以", "*"),
        (r"除以", "/"),
    ]
    for pattern, replacement in replacements:
        text = re.sub(pattern, replacement, text, flags=re.I)
    text = re.sub(r"(?<![<>=!])=(?!=)", "==", text).strip()
    try:
        tree = ast.parse(text, mode="eval")
    except (SyntaxError, ValueError, RecursionError) as exc:
        raise ModelError(
            "unsupported controlled expression; use explicit symbols and scope"
        ) from exc

    def convert(node, level=0):
        if level > MAX_DEPTH:
            raise ModelError("expression nesting limit exceeded")

        def descend(n):
            return convert(n, level + 1)

        if isinstance(node, ast.Name):
            return {"var": node.id}
        if isinstance(node, ast.Constant):
            if type(node.value) is bool:
                return {"literal": node.value, "sort": "Bool"}
            if type(node.value) is int:
                return {"literal": node.value, "sort": "Int"}
            if type(node.value) is float:
                # Preserve the written decimal, not Python's binary float.
                token = ast.get_source_segment(text, node)
                if not re.fullmatch(r"\d+\.\d+", token):
                    raise ModelError("use exact decimal notation")
                return {"literal": token, "sort": "Real"}
        if isinstance(node, ast.UnaryOp) and isinstance(
            node.op, (ast.Not, ast.USub, ast.UAdd)
        ):
            if isinstance(node.op, ast.UAdd):
                return descend(node.operand)
            return {
                "op": "not" if isinstance(node.op, ast.Not) else "neg",
                "args": [descend(node.operand)],
            }
        if isinstance(node, ast.BinOp) and type(node.op) in [
            ast.Add,
            ast.Sub,
            ast.Mult,
            ast.Div,
        ]:
            return {
                "op": {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.Div: "div"}[
                    type(node.op)
                ],
                "args": [descend(node.left), descend(node.right)],
            }
        if isinstance(node, ast.BoolOp):
            return {
                "op": "and" if isinstance(node.op, ast.And) else "or",
                "args": [descend(n) for n in node.values],
            }
        if isinstance(node, ast.Compare):
            ops = {
                ast.Eq: "eq",
                ast.NotEq: "ne",
                ast.Lt: "lt",
                ast.LtE: "le",
                ast.Gt: "gt",
                ast.GtE: "ge",
            }
            if any(type(op) not in ops for op in node.ops):
                raise ModelError("unsupported comparison")
            operands = [node.left, *node.comparators]
            comparisons = [
                {
                    "op": ops[type(op)],
                    "args": [descend(operands[i]), descend(operands[i + 1])],
                }
                for i, op in enumerate(node.ops)
            ]
            return (
                comparisons[0]
                if len(comparisons) == 1
                else {"op": "and", "args": comparisons}
            )
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and not node.keywords
        ):
            args = [descend(a) for a in node.args]
            if node.func.id in ["tdiv", "ite"]:
                return {"op": node.func.id, "args": args}
            return {"op": "call", "symbol": node.func.id, "args": args}
        raise ModelError(
            "unsupported expression syntax (no attributes, indexing, or executable code)"
        )

    return convert(tree.body)


def propose_controlled(source, *, max_source_chars=MAX_TEXT):
    if (not isinstance(source, str) or not source.strip()
            or (max_source_chars is not None and len(source) > max_source_chars)):
        raise ModelError("expected nonempty text within the configured character limit")
    model = dict(
        schema=SCHEMA,
        semantics=SEMANTICS,
        decision="",
        domains=[],
        symbols=[],
        constraints=[],
        objectives=[],
        objective_order="single",
        goal=None,
        assumptions=[
            "Controlled grammar v1; unbounded exact Int/Real arithmetic; "
            "relational partiality at Boolean predicates; explicit finite domains."
        ],
        unresolved=[],
    )
    offset = 0
    for line_number, raw in enumerate(source.splitlines(keepends=True), 1):
        start = offset
        offset += len(raw)
        text = raw.strip()
        if not text:
            continue
        # A terminal sentence mark is optional; decimals inside a line are untouched.
        text = text[:-1] if text.endswith((".", "。")) else text
        span = [start, start + len(raw.rstrip("\r\n"))]
        try:
            m = re.fullmatch(r"Domain\s+(\w+)\s+consists of\s+(.+)", text, re.I)
            if not m:
                m = re.fullmatch(r"域\s*(\w+?)\s*包含\s*(.+)", text)
            empty = re.fullmatch(
                r"Domain\s+(\w+)\s+is empty", text, re.I
            ) or re.fullmatch(r"域\s*(\w+?)\s*为空", text)
            if m or empty:
                model["domains"].append(
                    dict(
                        name=(m or empty)[1],
                        members=re.split(r"\s*[,、]\s*", m[2]) if m else [],
                        span=span,
                    )
                )
                continue
            m = re.fullmatch(r"Predicate\s+(\w+)\s+has arguments\s+(.+)", text, re.I)
            if not m:
                m = re.fullmatch(r"谓词\s*(\w+?)\s*的参数类型为\s*(.+)", text)
            if m:
                model["symbols"].append(
                    dict(
                        name=m[1],
                        sort="Bool",
                        arguments=re.split(r"\s*[,、]\s*", m[2]),
                        span=span,
                    )
                )
                continue
            m = re.fullmatch(
                r"Let\s+(\w+)\s+be\s+(?:an?\s+)?(integer|real|boolean|\w+)(?:\s+between\s+(.+?)\s+and\s+(.+))?",
                text,
                re.I,
            )
            if not m:
                m = re.fullmatch(
                    r"设\s*(\w+?)\s*为\s*(整数|实数|布尔变量|\w+类型变量)(?:[，,]\s*范围为\s*(.+?)\s*到\s*(.+))?",
                    text,
                )
            if m:
                sorts = {
                    "integer": "Int",
                    "real": "Real",
                    "boolean": "Bool",
                    "整数": "Int",
                    "实数": "Real",
                    "布尔变量": "Bool",
                }
                sort = sorts.get(m[2].lower(), m[2].removesuffix("类型变量"))
                symbol = dict(name=m[1], sort=sort, arguments=[], span=span)
                if m[3] is not None:
                    for key, v in [("lower", m[3]), ("upper", m[4])]:
                        if sort == "Int":
                            if not re.fullmatch(r"[+-]?\d+", v):
                                raise ModelError(
                                    "integer bounds must be exact integer literals"
                                )
                            symbol[key] = int(v)
                        elif sort == "Real":
                            symbol[key] = v
                        else:
                            raise ModelError(
                                "only numeric declarations have interval bounds"
                            )
                model["symbols"].append(symbol)
                continue
            if text.lower() in [
                "find a solution",
                "check satisfiability",
                "求一个解",
                "检查可满足性",
            ]:
                if model["decision"] and model["decision"] != "satisfiability":
                    raise ModelError("conflicting decision requests")
                model["decision"] = "satisfiability"
                continue
            if text.lower() in ["optimize lexicographically", "按字典序优化"]:
                model["objective_order"] = "lexicographic"
                continue
            m = re.fullmatch(r"(?:(Minimize|Maximize)\s+|(最小化|最大化)\s*)(.+)", text, re.I)
            if m:
                if model["decision"] and model["decision"] != "optimization":
                    raise ModelError("conflicting decision requests")
                model["decision"] = "optimization"
                model["objectives"].append(
                    dict(
                        direction="minimize"
                        if (m[1] or m[2]).lower() in ["minimize", "最小化"]
                        else "maximize",
                        expr=expression(m[3]),
                        span=span,
                    )
                )
                continue
            m = re.fullmatch(r"(?:Prove that\s+|证明\s*)(.+)", text, re.I)
            if m:
                if model["goal"] or model["decision"]:
                    raise ModelError(
                        "only one validity goal and decision request is allowed"
                    )
                model["decision"] = "validity"
                model["goal"] = {"expr": expression(m[1]), "span": span}
                continue
            text = re.sub(r"^(?:Require\s+|要求\s*)", "", text, flags=re.I)
            model["constraints"].append({"expr": expression(text), "span": span})
        except (ModelError, ValueError) as exc:
            model["unresolved"].append(f"line {line_number}: {exc}")
    # Chinese operators have no word delimiters. Refuse identifiers containing
    # reserved phrases rather than rewriting part of a declared name as syntax.
    reserved = [
        "不等于",
        "大于",
        "小于",
        "至少",
        "至多",
        "等于",
        "并且",
        "或者",
        "并非",
        "加上",
        "减去",
        "乘以",
        "除以",
        "最小化",
        "最大化",
        "证明",
        "要求",
        "如果",
        "那么",
        "对于每个",
        "存在",
        "属于",
        "使得",
    ]
    pending = [model]
    while pending:
        item = pending.pop()
        if isinstance(item, dict):
            for key, value in item.items():
                names = (
                    value
                    if key == "members"
                    else [value]
                    if key in {"name", "var", "symbol", "domain"}
                    else []
                )
                for identifier in names:
                    if isinstance(identifier, str) and any(
                        word in identifier for word in reserved
                    ):
                        model["unresolved"].append(
                            f"identifier {identifier!r} contains a reserved controlled-language phrase"
                        )
                if isinstance(value, (dict, list)):
                    pending.append(value)
        elif isinstance(item, list):
            pending.extend(value for value in item if isinstance(value, (dict, list)))
    if not model["decision"]:
        model["unresolved"].append(
            "state the decision explicitly: Find a solution / Minimize / Prove that"
        )
    return model
