"""Reuse UNSAT only for complete obligations equal under a scalar renaming.

The caller registers only an actual solver UNSAT result. Each later hit needs
an exact whole-formula correspondence, including its original context, domain
conditions and negated conclusion. Similar variable counts are only a lookup
hint. No SAT or unknown result, model assignment or partial clause is reused.
"""
from dataclasses import dataclass
import z3
from .boolean_structure import structural_equivalence


@dataclass(frozen=True)
class RenamedObligation:
    canonical: object
    bucket: tuple
    declaration_map: tuple


class RenamedUnsatCache:
    def __init__(self, ctx):
        self.ctx = ctx
        self.constants = {}
        self.canonical_ids = set()
        self.proved = {}

    def prepare(self, formula, partition=()):
        if formula.ctx != self.ctx or not z3.is_bool(formula):
            raise ValueError('UNSAT reuse requires a Boolean formula in one context')
        core, context = z3.z3core, formula.ctx_ref()
        pending, seen, declarations = [formula.as_ast()], set(), {}
        # The complete formula keeps all raw AST pointers alive. Refuse binders
        # and positive-arity uninterpreted functions rather than guessing maps.
        while pending:
            node = pending.pop()
            identity = core.Z3_get_ast_id(context, node)
            if identity in seen:
                continue
            seen.add(identity)
            kind = core.Z3_get_ast_kind(context, node)
            if kind in (z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST):
                return None
            if kind != z3.Z3_APP_AST:
                continue
            app = core.Z3_to_app(context, node)
            decl = core.Z3_get_app_decl(context, app)
            arity = core.Z3_get_app_num_args(context, app)
            if core.Z3_get_decl_kind(context, decl) == z3.Z3_OP_UNINTERPRETED:
                if arity:
                    return None
                declaration = z3.FuncDeclRef(decl, formula.ctx)
                if declaration.get_id() in self.canonical_ids:
                    return None
                declarations[declaration.get_id()] = declaration
            pending.extend(core.Z3_get_app_arg(context, app, i) for i in range(arity))
        ordered = sorted(declarations.values(), key=lambda d: (d.range().get_id(), d.get_id()))
        sorts = tuple(d.range().get_id() for d in ordered)
        if sorts not in self.constants:
            values = tuple(z3.FreshConst(d.range(), prefix='unsat_renaming') for d in ordered)
            if any(v.decl().get_id() in declarations for v in values):
                return None
            self.constants[sorts] = values
            self.canonical_ids.update(v.decl().get_id() for v in values)
        values = self.constants[sorts]
        pairs = tuple((d(), value) for d, value in zip(ordered, values))
        renamed = z3.substitute(formula, *pairs) if pairs else formula
        mapping = tuple((d.get_id(), value.decl().get_id()) for d, value in zip(ordered, values))
        # Node counts and caller partitions restrict lookup only; every hit
        # still compares the two complete formulas without relying on a hash.
        return RenamedObligation(renamed, (sorts, len(seen), tuple(partition)), mapping)

    def lookup(self, candidate):
        if candidate is None:
            return None
        for previous, number in self.proved.get(candidate.bucket, ()):
            if candidate.canonical.eq(previous.canonical):
                comparison = dict(equivalent=True, method='exact complete renamed AST identity')
            else:
                comparison = structural_equivalence(previous.canonical, candidate.canonical)
            if comparison['equivalent'] is True:
                return dict(source_solver_query=number,
                            source_declaration_map=previous.declaration_map,
                            declaration_map=candidate.declaration_map,
                            complete_obligation_comparison=comparison)
        return None

    def remember_unsat(self, candidate, solver_query):
        if candidate is not None:
            self.proved.setdefault(candidate.bucket, []).append((candidate, solver_query))
