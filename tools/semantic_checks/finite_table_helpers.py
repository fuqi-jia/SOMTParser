"""Exact optional compaction of complete, closed finite binary table helpers.

Decode every literal tuple from the helper itself, independently of the source
oracle. Accept a clique or grouped-row representation only after its complete tuple
set has been reconstructed and compared. Reparse the entire module with nonrecursive
macros so SMT lexical scoping instantiates every original call and cost.
Unsupported definitions leave the entire original module unchanged.
"""
import hashlib
import io
import json
import uuid

import z3

from tools import validate_packed_smt_stream as scanner
from .closed_helpers import _render
from .table_cliques import plan_clique_table


class _Unsupported(ValueError):
    pass


def _flatten(expression, predicate):
    pending = [expression]
    while pending:
        value = pending.pop()
        if predicate(value):
            pending.extend(reversed(value.children()))
        else:
            yield value


def _integer(value):
    if z3.is_int_value(value):
        return value.as_long()
    if z3.is_app_of(value, z3.Z3_OP_UMINUS) and value.num_args() == 1:
        return -_integer(value.arg(0))
    raise _Unsupported('nonliteral table value')


def _intersection(a, b):
    # None is negative infinity in a lower bound and positive in an upper.
    lower = b[0] if a[0] is None else a[0] if b[0] is None else max(a[0], b[0])
    upper = b[1] if a[1] is None else a[1] if b[1] is None else min(a[1], b[1])
    return None if lower is not None and upper is not None and lower > upper else (lower, upper)


def _literal_bound(literal, columns):
    kinds = (z3.Z3_OP_EQ, z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT)
    if not z3.is_app(literal) or literal.decl().kind() not in kinds or literal.num_args() != 2:
        raise _Unsupported('nonliteral table selector')
    a, b = literal.children()
    kind = literal.decl().kind()
    if any(a.eq(c) for c in columns):
        column = next(i for i, c in enumerate(columns) if a.eq(c))
        point = _integer(b)
    elif any(b.eq(c) for c in columns):
        column = next(i for i, c in enumerate(columns) if b.eq(c))
        point = _integer(a)
        kind = {z3.Z3_OP_EQ: z3.Z3_OP_EQ, z3.Z3_OP_LE: z3.Z3_OP_GE,
                z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                z3.Z3_OP_GT: z3.Z3_OP_LT}[kind]
    else:
        raise _Unsupported('selector is not a parameter comparison')
    bounds = {z3.Z3_OP_EQ: (point, point), z3.Z3_OP_LE: (None, point),
              z3.Z3_OP_GE: (point, None), z3.Z3_OP_LT: (None, point - 1),
              z3.Z3_OP_GT: (point + 1, None)}
    return column, bounds[kind]


def _selector(expression, columns):
    """Exact union of literal intervals for a single integer coordinate."""
    column, intervals = None, []
    for clause in _flatten(expression, z3.is_or):
        interval, impossible = (None, None), False
        for literal in _flatten(clause, z3.is_and):
            if z3.is_true(literal):
                continue
            if z3.is_false(literal):
                impossible = True
                continue
            index, bound = _literal_bound(literal, columns)
            if column is not None and column != index:
                raise _Unsupported('selector mixes coordinates')
            column = index
            if interval is not None:
                interval = _intersection(interval, bound)
        if not impossible and interval is not None:
            intervals.append(interval)
    return column, intervals


def _pairs(expression, columns):
    pairs = set()
    for row in _flatten(expression, z3.is_or):
        values = [None, None]
        impossible = False
        for selector in _flatten(row, z3.is_and):
            if z3.is_true(selector):
                continue
            if z3.is_false(selector):
                impossible = True
                continue
            column, intervals = _selector(selector, columns)
            if column is None:
                impossible = impossible or not intervals
            else:
                values[column] = (intervals if values[column] is None else
                                  [intersection for a in values[column] for b in intervals
                                   if (intersection := _intersection(a, b)) is not None])
        if impossible or any(intervals == [] for intervals in values):
            continue
        if (any(intervals is None for intervals in values)
                or any(lo is None or hi is None for intervals in values for lo, hi in intervals)):
            raise _Unsupported('table has an unbounded coordinate')
        # Expand every finite literal interval exactly, including endpoints.
        # No sampled tuples or source-oracle values participate in decoding.
        points = [{n for lo, hi in intervals for n in range(lo, hi + 1)} for intervals in values]
        pairs.update((a, b) for a in points[0] for b in points[1])
    return frozenset(pairs)


def decode_literal_table(tokens):
    """Return all pairs from one complete, isolated binary Int -> Bool body.

    Fresh probe constants cannot accidentally provide a captured global: their
    names are absent from every original token. Parsing the definition as a
    nonrecursive macro rejects recursion, captured names and helper references.
    """
    if (len(tokens) < 16 or tokens[0] != ('paren', b'(')
            or tokens[1] not in (('atom', b'define-fun'), ('atom', b'define-fun-rec'))
            or tokens[2][0] not in ('atom', 'quoted')
            or tokens[3] != ('paren', b'(')):
        raise _Unsupported('not a binary table definition')
    for offset in (4, 8):
        entry = tokens[offset:offset + 4]
        if (len(entry) != 4 or entry[0] != ('paren', b'(')
                or entry[1][0] not in ('atom', 'quoted')
                or entry[2:] != [('atom', b'Int'), ('paren', b')')]):
            raise _Unsupported('table parameter signature')
    if (tokens[12:14] != [('paren', b')'), ('atom', b'Bool')]
            or tokens[5][1] == tokens[9][1]):
        raise _Unsupported('table result or parameter identity')
    used = {value for kind, value in tokens if kind in ('atom', 'quoted')}
    names = []
    for _ in range(2):
        name = ('__somt_literal_probe_' + uuid.uuid4().hex).encode()
        while name in used:
            name += b'_'
        used.add(name)
        names.append(name)
    definition = list(tokens)
    definition[1] = ('atom', b'define-fun')
    call = b'(' + _render([tokens[2]]) + b' ' + b' '.join(names) + b')'
    module = (b'\n'.join(b'(declare-const ' + name + b' Int)' for name in names)
              + b'\n' + _render(definition) + b'\n(assert ' + call + b')')
    context = z3.Context()
    try:
        assertions = z3.parse_smt2_string(module.decode(), ctx=context)
        if len(assertions) != 1:
            raise _Unsupported('table body assertion count')
        columns = [z3.Int(name.decode(), ctx=context) for name in names]
        return _pairs(assertions[0], columns)
    except z3.Z3Exception as error:
        raise _Unsupported('table body is not closed and nonrecursive') from error


def _tuple_sha256(pairs):
    return hashlib.sha256(json.dumps(sorted(pairs), separators=(',', ':')).encode()).hexdigest()


def _integer_text(value):
    return str(value).encode() if value >= 0 else b'(- ' + str(-value).encode() + b')'


def _member_text(column, points):
    ranges = []
    for point in points:
        if ranges and point == ranges[-1][1] + 1:
            ranges[-1] = (ranges[-1][0], point)
        else:
            ranges.append((point, point))
    terms = [(b'(= ' + column + b' ' + _integer_text(lo) + b')') if lo == hi
             else (b'(and (>= ' + column + b' ' + _integer_text(lo) + b') (<= '
                   + column + b' ' + _integer_text(hi) + b'))') for lo, hi in ranges]
    return b'(or ' + b' '.join(terms) + b')'


def render_clique_table(families, columns):
    """The qualified classifier relation, with no generated lexical binders.

    General Z3 sexpr() printing can introduce let names such as a!1 which may
    capture an identically named original formal. Direct Int/Bool output uses
    only the two formal parameter tokens, never auxiliary symbol names.
    """
    terms = []
    for family in families:
        codes = []
        for column in columns:
            parts = [b'(ite ' + _member_text(column, group) + b' ' + str(i).encode() + b' '
                     for i, group in enumerate(family, 1)]
            codes.append(b''.join(parts) + b'0' + b')' * len(parts))
        terms.append(b'(and (not (= ' + codes[0] + b' 0)) (= ' + codes[0] + b' ' + codes[1] + b'))')
    return (b'(and (not (= ' + columns[0] + b' ' + columns[1] + b')) (or '
            + b' '.join(terms) + b'))')



def plan_literal_rows(pairs):
    """Group exactly those first coordinates with identical finite neighbors."""
    neighbors = {}
    for a, b in pairs:
        neighbors.setdefault(a, set()).add(b)
    rows = {}
    for a, values in neighbors.items():
        rows.setdefault(tuple(sorted(values)), []).append(a)
    return tuple(sorted((tuple(sorted(values)), columns)
                        for columns, values in rows.items()))


def render_row_table(groups, columns):
    """A union of finite Cartesian products, with no generated lexical names."""
    return b'(or ' + b' '.join(
        b'(and ' + _member_text(columns[0], rows) + b' '
        + _member_text(columns[1], values) + b')' for rows, values in groups) + b')'


def compact_literal_table_module(module):
    """Return equivalent complete bytes and an auditable all-or-nothing record.

    The caller retains and archives the original complete relation before
    using this optional proof representation. No solver result is implied.
    """
    record = dict(method='exact-closed-literal-table-v1', applied=False,
                  input_sha256=hashlib.sha256(module).hexdigest(), helpers=[])
    try:
        commands = list(scanner.commands(io.BytesIO(module), max_command_bytes=float('inf')))
        rows = [list(scanner.tokens(command.raw)) for command in commands]
        used = {value for row in rows for kind, value in row if kind in ('atom', 'quoted')}
        replacements, names = {}, set()
        for index, (command, tokens) in enumerate(zip(commands, rows)):
            if (len(tokens) < 2 or tokens[1][0] != 'atom'
                    or tokens[1][1] not in {b'define-fun', b'define-fun-rec',
                                          b'declare-const', b'declare-fun', b'assert',
                                          b'minimize', b'maximize', b'set-logic', b'set-info',
                                          b'set-option', b'check-sat', b'get-model',
                                          b'get-objectives', b'exit'}):
                raise _Unsupported('unsupported complete module command')
            if tokens[1] not in (('atom', b'define-fun'), ('atom', b'define-fun-rec')):
                continue
            name = tokens[2][1]
            if name in names:
                raise _Unsupported('duplicate helper identity')
            names.add(name)
            pairs = decode_literal_table(tokens)
            families = plan_clique_table(2, [(((a, a),), ((b, b),)) for a, b in pairs]) if pairs else ()
            row_groups = None
            if families is None:
                row_groups = plan_literal_rows(pairs)
                reconstructed = frozenset((a, b) for rows, values in row_groups
                                          for a in rows for b in values)
            else:
                reconstructed = frozenset((a, b) for family in families for group in family
                                          for a in group for b in group if a != b)
            if reconstructed != pairs:
                raise _Unsupported('complete reconstructed tuple set differs')
            # Rename the two existing formal binders. A legal original formal
            # named |ite| or |not| may otherwise shadow an operator introduced
            # by the classifier representation. The new body is closed over
            # these formals; no original call or module-level name is renamed.
            columns = []
            for column in range(2):
                fresh = ('__somt_literal_column_' + str(column)).encode()
                while fresh in used:
                    fresh += b'_'
                used.add(fresh)
                columns.append(fresh)
            compact = (render_row_table(row_groups, columns) if row_groups is not None else
                       render_clique_table(families, columns) if pairs else b'false')
            # A macro has no persistent function interpretation. The SMT parser
            # substitutes the complete body at every original scoped call.
            header = list(tokens[:14])
            header[1] = ('atom', b'define-fun')
            header[5] = ('atom', columns[0])
            header[9] = ('atom', columns[1])
            replacements[index] = _render(header) + b' ' + compact + b')'
            record['helpers'].append(dict(name=name.decode(), tuples=len(pairs),
                                          tuples_sha256=_tuple_sha256(pairs),
                                          definition_sha256=hashlib.sha256(command.raw).hexdigest(),
                                          representation='row-groups' if row_groups is not None else 'clique',
                                          families=[[list(group) for group in family] for family in (families or ())],
                                          row_groups=[dict(rows=list(rows), columns=list(values))
                                                      for rows, values in (row_groups or ())],
                                          complete_reconstruction_equal=True))
        if not replacements:
            raise _Unsupported('no table helpers')
        result = b'\n'.join(replacements.get(i, command.raw) for i, command in enumerate(commands))
        record.update(applied=True, output_sha256=hashlib.sha256(result).hexdigest())
        return result, record
    except (_Unsupported, z3.Z3Exception, UnicodeError, IndexError, ValueError) as error:
        record.update(helpers=[], fallback_reason=str(error), output_sha256=record['input_sha256'])
        return module, record
