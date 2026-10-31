"""Sufficient joint-relation bridge between complete typed SMT exports.

All original declared coordinates remain observable. Only additional explicitly
named private witnesses are existentially closed, over the full assertion and
ordered signed-cost tuple. A success transports an independently established
source-to-old-target proof; it does not establish that source proof itself.
"""
import hashlib
import re

import z3

from .boolean_structure import structural_equivalence
from .existential_bijection import prove_existential_bijection
from .public_witness_bijection import prove_public_witness_bijection
from .existential_conjuncts import factor_existential_conjuncts
from .integer_order import normalize_integer_order
from .integer_step_universals import expand_integer_step_universals
from .finite_quantifiers import expand_finite_int_quantifiers
from .qf_conjuncts import prove_qf_conjunctions
from .source_oracles.fzn_json_source import Unsupported
from .source_oracles.target_relation import read_target


def _structure(left, right):
    proof = structural_equivalence(left, right)
    if not proof['equivalent']:
        # Both rewrites preserve the entire formula for every free assignment.
        left = normalize_integer_order(z3.simplify(left)).formula
        right = normalize_integer_order(z3.simplify(right)).formula
        proof = structural_equivalence(left, right)
    return dict(proof, solver_queries=0)


def check(old_bytes, new_bytes, *, solve=False, progress_callback=None,
          complete_relation_callback=None, witness_strategy="ordinal"):
    """Check complete syntax, typed public identity and all ordered objectives.

    By default only structural certificates are attempted. With solve=True,
    complete opened bodies are checked by sufficient conjunction obligations.
    No candidate model, objective bound or caller-supplied symbol map is used.
    Failure to obtain a certificate is inconclusive. The optional archive
    callback receives the original complete joint formulas; its return is ignored.
    public-incidence proposes a typed witness permutation from shared free
    coordinates; the same complete body proof remains mandatory.
    """
    if witness_strategy not in ("ordinal", "public-incidence"):
        raise ValueError("unknown witness correspondence strategy")
    match_witnesses = (prove_public_witness_bijection if witness_strategy == "public-incidence"
                       else prove_existential_bijection)
    receipt = dict(witness_strategy=witness_strategy, old_target_sha256=hashlib.sha256(old_bytes).hexdigest(),
                   new_target_sha256=hashlib.sha256(new_bytes).hexdigest(),
                   full_relation_bridge=False, solver_queries=0,
                   source_correctness_reproved=False)
    def phase(label, **details):
        if progress_callback is not None:
            progress_callback(dict(phase=label, **details))
    try:
        phase('old-complete-typed-parse')
        old_variables, old, old_directions = read_target(old_bytes)
        phase('new-complete-typed-parse')
        new_variables, new, new_directions = read_target(new_bytes)
        if old_directions != new_directions:
            raise Unsupported('ordered objective count or direction changed')
        for name, value in old_variables.items():
            if name not in new_variables or not value.sort().eq(new_variables[name].sort()):
                raise Unsupported('original declared coordinate removed or retyped: ' + name)
        private_names = [name for name in new_variables if name not in old_variables]
        if any(not re.fullmatch(r'!somt_exists_[0-9]+', name) for name in private_names):
            raise Unsupported('new coordinate is not an explicit private witness')
        costs = []
        for left, right in zip(old.objectives(), new.objectives()):
            if not left.sort().eq(right.sort()):
                raise Unsupported('ordered signed-cost sort changed')
            costs.append(z3.FreshConst(left.sort(), 'bridge_cost'))
        left = z3.And(*old.assertions(), *[c == obj for c, obj in zip(costs, old.objectives())])
        right = z3.And(*new.assertions(), *[c == obj for c, obj in zip(costs, new.objectives())])
        if private_names:
            right = z3.Exists([new_variables[name] for name in private_names], right)
        if complete_relation_callback is not None:
            complete_relation_callback(left, right)
        receipt.update(original_declared_coordinates=len(old_variables),
                       private_witnesses=private_names, ordered_directions=old_directions,
                       signed_cost_sorts=[str(c.sort()) for c in costs],
                       old_assertions=len(old.assertions()), new_assertions=len(new.assertions()),
                       complete_old_and_new_streams=True,
                       all_constraints_and_ordered_costs_retained=True)
        if witness_strategy == 'public-incidence':
            phase('complete-public-witness-bijection')
            proof = match_witnesses(left, right, body_checker=_structure)
        else:
            phase('full-structure')
            proof = _structure(left, right)
            if not proof['equivalent']:
                phase('positive-existential-factoring')
                a = factor_existential_conjuncts(left).formula
                b = factor_existential_conjuncts(right).formula
                proof = _structure(a, b)
            if not proof['equivalent']:
                phase('complete-witness-bijection')
                proof = match_witnesses(left, right, body_checker=_structure)
        if proof['equivalent'] is not True and solve:
            phase('complete-conjunction-obligations')
            def body_checker(a, b):
                # Exact finite step expansion covers the complete integer line,
                # including the region before all events and signed heights.
                expansions, finite, normalized = [], [], []
                for side, formula in zip(('old', 'new'), (a, b)):
                    phase('integer-step-expansion', side=side)
                    expansion = expand_integer_step_universals(formula)
                    expansions.append(expansion)
                    phase('integer-step-expansion-complete', side=side,
                          expanded_quantifiers=expansion.expanded_quantifiers,
                          retained_quantifiers=expansion.retained_quantifiers,
                          event_instances=expansion.event_instances)
                for side, expansion in zip(('old', 'new'), expansions):
                    phase('finite-guard-expansion', side=side)
                    item = expand_finite_int_quantifiers(expansion.formula,
                        max_enumerated_tuples=float('inf'), max_emitted_instances=float('inf'),
                        max_ast_nodes=float('inf')) if expansion.retained_quantifiers else None
                    finite.append(item)
                    phase('finite-guard-expansion-complete', side=side,
                          stats=vars(item.stats) if item is not None else None)
                for side, expansion, item in zip(('old', 'new'), expansions, finite):
                    phase('integer-normalization', side=side)
                    normalized.append(normalize_integer_order(z3.simplify(
                        item.formula if item is not None else expansion.formula)).formula)
                    phase('integer-normalization-complete', side=side)
                result = prove_qf_conjunctions(*normalized, progress_callback=progress_callback)
                result['finite_guard_expansion'] = [vars(f.stats) if f is not None else None for f in finite]
                result['integer_step_expansion'] = [dict(
                    expanded_quantifiers=e.expanded_quantifiers,
                    retained_quantifiers=e.retained_quantifiers,
                    event_instances=e.event_instances) for e in expansions]
                return result
            proof = match_witnesses(left, right, body_checker=body_checker)
        receipt.update(full_relation_bridge=proof['equivalent'] is True, proof=proof,
                       solver_queries=proof['solver_queries'])
        if not receipt['full_relation_bridge']:
            receipt['reason'] = 'complete joint structure inconclusive'
    except (Unsupported, UnicodeError, ValueError, z3.Z3Exception, IndexError) as error:
        receipt['reason'] = type(error).__name__ + ': ' + str(error)
    return receipt
