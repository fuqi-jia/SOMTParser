"""Make scalar PyCSP3 membership compositional without changing the dataset.

PyCSP3 2.6.1 diagnoses scalar ``in`` mixed with ordinary Boolean arguments in
conjunction/disjunction and recommends ``among``/``not_among``. This adapter
rewrites only single membership comparisons with a name/subscript as operand.
The helper dispatches on the actual PyCSP3 integer-variable class; membership
of ordinary Python objects retains Python semantics. Tuple/table membership
and chained comparisons are left unchanged. The caller saves the original
model, transformed model, and returned edit record as separate artifacts.
"""
from dataclasses import dataclass
import ast
import hashlib


@dataclass(frozen=True)
class MembershipRewrite:
    source: str
    original_sha256: str
    transformed_sha256: str
    edits: tuple


def normalize_scalar_membership(source):
    """Return a recorded compatibility transform; never execute the model."""
    tree = ast.parse(source)
    raw = source.encode("utf-8")
    digest = hashlib.sha256(raw).hexdigest()
    offsets = [0]
    for line in raw.splitlines(keepends=True):
        offsets.append(offsets[-1] + len(line))

    def start(node):
        return offsets[node.lineno - 1] + node.col_offset

    def end(node):
        return offsets[node.end_lineno - 1] + node.end_col_offset

    identifiers = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
    identifiers.update(node.arg for node in ast.walk(tree) if isinstance(node, ast.arg))
    identifiers.update(node.name for node in ast.walk(tree)
                       if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)))
    for node in ast.walk(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            identifiers.update(item.asname or item.name.split('.')[0] for item in node.names)
    helper = "_somt_pycsp3_scalar_membership"
    while helper in identifiers:
        helper += "_"

    candidates = [node for node in ast.walk(tree)
                  if isinstance(node, ast.Compare) and len(node.ops) == 1
                  and isinstance(node.ops[0], (ast.In, ast.NotIn))
                  and isinstance(node.left, (ast.Name, ast.Subscript))]
    candidates.sort(key=start)
    # Nested comparisons would require recursive source replacement. Leave
    # overlapping candidates untouched instead of changing operand evaluation.
    selected = [node for node in candidates if not any(
        other is not node and start(node) < end(other) and start(other) < end(node)
        for other in candidates)]
    edits = []
    replacements = []
    for node in selected:
        left = raw[start(node.left):end(node.left)].decode("utf-8")
        right = raw[start(node.comparators[0]):end(node.comparators[0])].decode("utf-8")
        negative = isinstance(node.ops[0], ast.NotIn)
        replacement = f"{helper}(({left}), ({right}), {negative})"
        original = raw[start(node):end(node)].decode("utf-8")
        edits.append({"line": node.lineno, "byte_column": node.col_offset,
                      "original": original, "replacement": replacement,
                      "rule": "scalar-integer-variable-membership-to-among"})
        replacements.append((start(node), end(node), replacement.encode("utf-8")))
    if not edits:
        return MembershipRewrite(source, digest, digest, ())

    insertion = 0
    for index, node in enumerate(tree.body):
        is_docstring = (index == 0 and isinstance(node, ast.Expr)
                        and isinstance(node.value, ast.Constant)
                        and isinstance(node.value.value, str))
        if is_docstring or isinstance(node, ast.ImportFrom) and node.module == "__future__":
            insertion = offsets[node.end_lineno]
        else:
            break
    definition = f'''\n# Compatibility adapter: original and transformed model hashes are recorded.
def {helper}(value, members, negative):
    from pycsp3.classes.main.variables import VariableInteger
    if isinstance(value, VariableInteger):
        return value.not_among(members) if negative else value.among(members)
    return value not in members if negative else value in members
\n'''
    replacements.append((insertion, insertion, definition.encode("utf-8")))
    for begin, finish, replacement in sorted(replacements, reverse=True):
        raw = raw[:begin] + replacement + raw[finish:]
    transformed = raw.decode("utf-8")
    # Parsing checks the generated syntax only; no reference model execution.
    ast.parse(transformed)
    return MembershipRewrite(transformed, digest, hashlib.sha256(raw).hexdigest(), tuple(edits))
