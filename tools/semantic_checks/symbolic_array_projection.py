"""Exact finite-read projection of private arrays with arbitrary Int indices.

An assignment to finitely many reads extends to a total array precisely when
equal indices have equal values. Retaining these congruence conditions removes
existential arrays without restricting their indices to a chosen finite domain.
The complete quantifier-free body, including observation and cost bridges, must
be supplied. Whole-array uses and nested array sorts remain unsupported.
"""
from dataclasses import dataclass

import z3

from .ground_array_projection import UnsupportedArrayProjection


@dataclass(frozen=True)
class SymbolicArrayProjection:
    body: object
    private_variables: tuple
    eliminated_arrays: tuple
    cells: tuple
    consistency_conditions: tuple
    bounded_read_definitions: tuple = ()


def _affine_index_domain(index, bounds):
    """Finite affine-index enclosure from the body's unconditional bounds.

    A row-major subscript often has bounds on its original indices rather than
    on the flattened expression. One varying term has an exact arithmetic
    progression. With several bounded terms, coefficient signs give endpoints
    and their gcd gives a containing progression, possibly with extra points.
    A lookup is used only when every point in that enclosure already has a
    ground cell; no independence or reachability assumption is introduced.
    Nonlinear or partly unbounded expressions require an explicit whole-index
    bound instead.
    """
    memo = {}
    pending = [(index, False)]
    arithmetic = (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS, z3.Z3_OP_MUL)
    while pending:
        term, ready = pending.pop()
        key = term.get_id()
        if key in memo:
            continue
        if z3.is_int_value(term):
            memo[key] = (term, ({}, term.as_long()))
            continue
        kind = term.decl().kind()
        if kind not in arithmetic:
            memo[key] = (term, ({key: 1}, 0))
            continue
        if not ready:
            pending.append((term, True))
            pending.extend((child, False) for child in term.children())
            continue
        children = [memo[child.get_id()][1] for child in term.children()]
        if any(child is None for child in children):
            form = None
        elif kind == z3.Z3_OP_MUL:
            nonconstant = [child for child in children if child[0]]
            if len(nonconstant) > 1:
                form = None
            else:
                factor = 1
                for coefficients, constant in children:
                    if not coefficients:
                        factor *= constant
                coefficients, constant = nonconstant[0] if nonconstant else ({}, 1)
                form = ({symbol: factor*coefficient for symbol, coefficient in coefficients.items()
                         if factor*coefficient}, factor*constant)
        else:
            coefficients, constant = {}, 0
            for number, (child_coefficients, child_constant) in enumerate(children):
                sign = -1 if kind == z3.Z3_OP_UMINUS or (kind == z3.Z3_OP_SUB and number > 0) else 1
                constant += sign*child_constant
                for symbol, coefficient in child_coefficients.items():
                    coefficients[symbol] = coefficients.get(symbol, 0) + sign*coefficient
            form = ({symbol: coefficient for symbol, coefficient in coefficients.items() if coefficient}, constant)
        # An unsupported arithmetic subtree may itself have an explicit domain.
        memo[key] = (term, form if form is not None else ({key: 1}, 0))
    coefficients, offset = memo[index.get_id()][1]
    if not coefficients:
        domain = (offset, offset, 1)
    elif len(coefficients) == 1:
        symbol, scale = next(iter(coefficients.items()))
        bound = bounds.get(symbol)
        if bound is None or bound[1] is None or bound[2] is None or bound[1] > bound[2]:
            domain = None
        else:
            endpoints = [scale*bound[1] + offset, scale*bound[2] + offset]
            domain = (min(endpoints), max(endpoints), abs(scale))
    else:
        from math import gcd

        lower = upper = offset
        stride = 0
        for symbol, scale in coefficients.items():
            bound = bounds.get(symbol)
            if bound is None or bound[1] is None or bound[2] is None or bound[1] > bound[2]:
                domain = None
                break
            endpoints = (scale*bound[1], scale*bound[2])
            lower += min(endpoints)
            upper += max(endpoints)
            stride = gcd(stride, abs(scale))
        else:
            domain = (lower, upper, stride)
    explicit = bounds.get(index.get_id())
    if domain is None:
        if explicit is None or explicit[1] is None or explicit[2] is None:
            return None
        return (explicit[1], explicit[2], 1) if explicit[1] <= explicit[2] else None
    lower, upper, stride = domain
    if explicit is not None:
        first = lower
        if explicit[1] is not None:
            lower = max(lower, explicit[1])
        if explicit[2] is not None:
            upper = min(upper, explicit[2])
        lower += (first - lower) % stride
    return (lower, upper, stride) if lower <= upper else None


def _bounded_read_definitions(body, cells):
    """Use only unconditional bounds and already present ground read cells.

    A total array makes each symbolic witness equal to the ground witness at
    its index. If the body's own bounds cover only existing ground cells,
    that witness has a total finite definition on every feasible state.
    No new bounds are asserted and no unobserved array cells are invented.
    """
    if not any(not z3.is_int_value(index) for _, index, _ in cells):
        return ()
    bounds = {}
    pending, seen = [body], set()
    while pending:
        atom = pending.pop()
        if atom.get_id() in seen:
            continue
        seen.add(atom.get_id())
        if z3.is_and(atom):
            pending.extend(atom.children())
            continue
        if not z3.is_app(atom) or atom.num_args() != 2:
            continue
        kind = atom.decl().kind()
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE,
                        z3.Z3_OP_GT, z3.Z3_OP_EQ):
            continue
        term, constant = atom.children()
        if z3.is_int_value(term):
            term, constant = constant, term
            kind = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT,
                    z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT,
                    z3.Z3_OP_EQ: z3.Z3_OP_EQ}[kind]
        if not z3.is_int(term) or not z3.is_int_value(constant):
            continue
        # Reads use simplified indices; normalize the bounded expression in
        # the same way, retaining the original comparison in the full body.
        term = z3.simplify(term)
        entry = bounds.setdefault(term.get_id(), [term, None, None])
        value = constant.as_long()
        if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ):
            value_lower = value + (kind == z3.Z3_OP_GT)
            entry[1] = value_lower if entry[1] is None else max(entry[1], value_lower)
        if kind in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_EQ):
            value_upper = value - (kind == z3.Z3_OP_LT)
            entry[2] = value_upper if entry[2] is None else min(entry[2], value_upper)
    ground = {}
    for array, index, witness in cells:
        if z3.is_int_value(index):
            ground.setdefault(array.get_id(), {})[index.as_long()] = witness
    pairs = []
    for array, index, witness in cells:
        if z3.is_int_value(index):
            continue
        domain = _affine_index_domain(index, bounds)
        if domain is None:
            continue
        lower, upper, stride = domain
        available = ground.get(array.get_id(), {})
        keys = sorted(key for key in available if lower <= key <= upper and (key - lower) % stride == 0)
        if len(keys) != (upper - lower)//stride + 1:
            continue

        def lookup(begin, end):
            if end - begin == 1:
                return available[keys[begin]]
            middle = (begin + end) // 2
            return z3.If(index < keys[middle], lookup(begin, middle),
                         lookup(middle, end))

        value = lookup(0, len(keys))
        # Cells were created bottom-up. Resolve earlier definitions inside a
        # nested index before recording the next simultaneous substitution.
        if pairs:
            value = z3.substitute(value, *pairs)
        pairs.append((witness, value))
    return tuple(pairs)


def scalarize_symbolic_array_reads(body, private_variables):
    """Preserve ``Exists(private_variables, body)`` by exact read congruence.

    Index expressions may depend on other reads, including reads from the same
    array. A bottom-up DAG rewrite also replaces those dependencies in every
    consistency condition. Equal literal reads share one witness; distinct
    literal indices need no pairwise condition. Reads with complete ground
    coverage under the body's own bounds are replaced before generating pairs.
    Every remaining symbolic read is related to all remaining reads, including
    the ground cells used by bounded definitions. No index bound is invented.
    """
    if not z3.is_bool(body):
        raise UnsupportedArrayProjection('the complete relation must be Boolean')
    private_variables = tuple(private_variables)
    if any(not z3.is_const(v) or v.decl().kind() != z3.Z3_OP_UNINTERPRETED
           for v in private_variables):
        raise UnsupportedArrayProjection('private variables must be constants')
    if any(v.ctx != body.ctx for v in private_variables):
        raise UnsupportedArrayProjection('mixed Z3 contexts')
    if len({v.get_id() for v in private_variables}) != len(private_variables):
        raise UnsupportedArrayProjection('duplicate private variable')
    arrays = {v.get_id(): v for v in private_variables if z3.is_array(v)}
    for array in arrays.values():
        if array.sort().domain().kind() != z3.Z3_INT_SORT:
            raise UnsupportedArrayProjection('private array index is not Int')
        if array.sort().range().kind() == z3.Z3_ARRAY_SORT:
            raise UnsupportedArrayProjection('nested private arrays')
    if not arrays:
        return SymbolicArrayProjection(body, private_variables, (), (), ())

    memo, cells = {}, {}
    pending = [(body, False)]
    while pending:
        term, ready = pending.pop()
        key = term.get_id()
        if key in memo:
            continue
        if z3.is_quantifier(term):
            raise UnsupportedArrayProjection('quantified body requires separate proof')
        if key in arrays:
            raise UnsupportedArrayProjection('private array used beyond a direct read')
        private_read = z3.is_select(term) and term.arg(0).get_id() in arrays
        if private_read:
            if term.num_args() != 2:
                raise UnsupportedArrayProjection('multi-index private array')
            children = [term.arg(1)]
        elif z3.is_app(term):
            children = term.children()
        else:
            raise UnsupportedArrayProjection('unsupported term in quantifier-free body')
        if children and not ready:
            pending.append((term, True))
            pending.extend((child, False) for child in children)
            continue
        rewritten = [memo[child.get_id()][1] for child in children]
        if private_read:
            array = term.arg(0)
            array_id = array.get_id()
            index = z3.simplify(rewritten[0])
            cell_key = (array_id, index.get_id())
            if cell_key not in cells:
                witness = z3.FreshConst(term.sort(), 'array_read')
                cell = (array, index, witness)
                cells[cell_key] = cell
            result = cells[cell_key][2]
        else:
            result = term
            if any(not old.eq(new) for old, new in zip(children, rewritten)):
                result = term.decl()(*rewritten)
        # Retain original ASTs: IDs are meaningful only while their objects live.
        memo[key] = (term, result)

    rewritten_body = memo[body.get_id()][1]
    definitions = _bounded_read_definitions(rewritten_body, tuple(cells.values()))
    eliminated = {variable.get_id() for variable, _ in definitions}
    if definitions:
        rewritten_body = z3.substitute(rewritten_body, *definitions)

    # A bounded read is already a lookup in retained ground cells. Two such
    # lookups agree when their indices agree. Every remaining symbolic read is
    # still compared with every ground cell, so aliases with a bounded lookup
    # are covered too. Generating pairs only now avoids building quadratic
    # obligations that become redundant after substituting those definitions.
    groups, symbolic_groups, conditions = {}, {}, []
    for array, index, witness in cells.values():
        if witness.get_id() in eliminated:
            continue
        if definitions and not z3.is_int_value(index):
            index = z3.simplify(z3.substitute(index, *definitions))
        previous = groups.setdefault(array.get_id(), [])
        symbolic = symbolic_groups.setdefault(array.get_id(), [])
        for _, other_index, other_value in (symbolic if z3.is_int_value(index) else previous):
            same_index = z3.simplify(index == other_index)
            if not z3.is_false(same_index):
                conditions.append(z3.Implies(same_index, witness == other_value))
        cell = (array, index, witness)
        previous.append(cell)
        if not z3.is_int_value(index):
            symbolic.append(cell)
    if conditions:
        rewritten_body = z3.And(rewritten_body, *conditions)
    witnesses = tuple(v for v in private_variables if v.get_id() not in arrays)
    witnesses += tuple(row[2] for row in cells.values() if row[2].get_id() not in eliminated)
    return SymbolicArrayProjection(rewritten_body, witnesses, tuple(arrays.values()),
                                   tuple(cells.values()), tuple(conditions), definitions)
