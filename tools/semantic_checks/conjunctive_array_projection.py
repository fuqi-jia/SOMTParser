"""Prepare positive existential array witnesses for exact finite-read projection.

For inhabited SMT sorts, C & Exists(v, B) is equivalent to Exists(v, C & B)
when v is fresh for C. Only root conjunctions are opened; no binder crosses a
negation, disjunction, implication, universal binder or arbitrary expression.
Fresh constants and substitute_vars preserve nested scopes and spelling
collisions. All conjuncts survive, including observation and signed-cost bridges.

Positive existential conjuncts are opened before finite instantiation, so
private positions are not enumerated as an exponential finite product.
The existing finite-quantifier helper may instantiate a quantifier only
when its own guard proves a finite domain. Its unsupported/budget fallback keeps
the original formula. The existing complete-body read-congruence projector then
removes arrays; residual unsupported quantifiers cause its ordinary refusal.
"""
from dataclasses import dataclass

import z3

from .finite_quantifiers import expand_finite_int_quantifiers
from .symbolic_array_projection import scalarize_symbolic_array_reads


@dataclass(frozen=True)
class ConjunctivePreparation:
    body: object
    private_variables: tuple
    lifted_quantifiers: int
    lifted_variables: tuple
    finite_expansion: object


def _open_conjuncts(body, private_variables):
    private = list(private_variables)
    lifted = []
    quantifiers = 0
    conjuncts = []
    pending = [body]
    while pending:
        term = pending.pop()
        if z3.is_and(term):
            pending.extend(reversed(term.children()))
        elif (z3.is_quantifier(term) and term.is_exists()
              and not term.num_patterns() and not term.num_no_patterns()):
            constants = [z3.FreshConst(term.var_sort(i), 'conjunct_witness')
                         for i in range(term.num_vars())]
            opened = z3.substitute_vars(term.body(), *reversed(constants))
            private.extend(constants)
            lifted.extend(constants)
            quantifiers += 1
            pending.append(opened)
        else:
            conjuncts.append(term)
    result = (z3.And(*conjuncts) if conjuncts
              else z3.BoolVal(True, ctx=body.ctx))
    return result, tuple(private), quantifiers, tuple(lifted)


def prepare_conjunctive_array_body(body, private_variables):
    """Return an exactly equivalent existential closure, without solver queries."""
    if not z3.is_bool(body):
        raise TypeError('the complete relation must be Boolean')
    opened, private, count, lifted = _open_conjuncts(body, private_variables)
    expanded = expand_finite_int_quantifiers(opened)
    result, private, more, extra = _open_conjuncts(expanded.formula, private)
    return ConjunctivePreparation(result, private, count + more,
                                 lifted + extra, expanded.stats)


def project_conjunctive_array_reads(body, private_variables):
    """Use complete-body read congruence after exact conjunction preparation.

    This function never treats an unsupported projection as success. Callers
    must retain their original body/private list if the projector refuses.
    """
    prepared = prepare_conjunctive_array_body(body, private_variables)
    return scalarize_symbolic_array_reads(prepared.body,
                                         prepared.private_variables)
