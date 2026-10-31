"""Independent complete-group obligations under shared original context only.

This deliberately refuses unmatched unary groups: it never borrows constraints
from a group awaiting a sibling proof. All remaining groups on either side are
exported, including one-sided and structurally identical groups. UNSAT for every
complete context-and-XOR obligation suffices for equivalence of the full inputs.
The executor is responsible for running the pinned solver on the exact bytes;
the collector checks complete group coverage and binds every solver transcript.
"""
from dataclasses import dataclass
import hashlib
import json
import z3
from .qf_conjuncts import _conjuncts, _signatures


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


@dataclass(frozen=True)
class QfGroupBatch:
    """A locally generated plan; do not reconstruct it from an untrusted manifest."""
    queries: tuple
    manifest_bytes: bytes

    @property
    def manifest(self):
        return json.loads(self.manifest_bytes)

    @property
    def sha256(self):
        return _sha(self.manifest_bytes)


def export_independent_qf_groups(left, right):
    if left.ctx != right.ctx:
        raise ValueError('independent groups require one context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('independent groups require Boolean formulas')
    parts = [tuple(_conjuncts(x)) for x in (left, right)]
    signatures = _signatures((*parts[0], *parts[1]))
    if signatures is None:
        raise ValueError('independent QF groups refuse binders and loose variables')
    sides = [{node.get_id(): node for node in side} for side in parts]
    common = sides[0].keys() & sides[1].keys()
    groups = []
    for side in sides:
        grouped = {}
        for identity, node in side.items():
            if identity not in common:
                grouped.setdefault(signatures[identity], {})[identity] = node
        groups.append(grouped)
    keys = sorted(groups[0].keys() | groups[1].keys(),
                  key=lambda key: (len(key), tuple(sorted(key))))
    if any(len(key) == 1 for key in keys):
        raise ValueError('unmatched unary groups require the general sequential checker')

    def conjunction(nodes):
        return z3.And(*nodes) if nodes else z3.BoolVal(True, ctx=left.ctx)

    queries, records = [], []
    covered = [set(common), set(common)]
    for index, key in enumerate(keys):
        lg, rg = [side.get(key, {}) for side in groups]
        # An actual subset of C shared by BOTH complete inputs, with no learned
        # or assumed facts. Omitting other shared clauses strengthens the query.
        context = {identity: sides[0][identity] for identity in common
                   if signatures[identity].issubset(key)}
        obligation = z3.And(*context.values(),
                            z3.Xor(conjunction(list(lg.values())),
                                   conjunction(list(rg.values()))))
        solver = z3.Solver(ctx=left.ctx)
        solver.add(obligation)
        # Solver construction is only a serializer. No result is inferred here.
        query = ('(set-logic ALL)\n' + solver.sexpr() + '\n(check-sat)\n').encode()
        queries.append(query)
        records.append(dict(index=index, declarations=sorted(key),
                            left_conjunct_ids=sorted(lg), right_conjunct_ids=sorted(rg),
                            shared_original_context_ids=sorted(context),
                            query_sha256=_sha(query), query_bytes=len(query)))
        covered[0].update(lg); covered[1].update(rg)
    assert all(covered[i] == set(sides[i]) for i in (0, 1))
    manifest = dict(schema='independent-complete-QF-groups-v1',
                    all_original_conjuncts_retained=True,
                    learned_or_sibling_context=False,
                    shared_original_conjunct_ids=sorted(common),
                    input_conjunct_counts=[len(side) for side in parts],
                    unique_input_conjunct_ids=[sorted(side) for side in sides],
                    groups=records)
    return QfGroupBatch(tuple(queries), _canonical(manifest))


def accept_independent_qf_results(batch, reports):
    """Accept only a complete set of exact-byte, zero-exit UNSAT transcripts.

    Reports must come from the qualified executor, whose source/runtime and raw
    stdout are preserved by its caller. Missing, duplicate, stale, SAT, unknown,
    and malformed results all remain inconclusive. Export alone proves nothing.
    """
    result = dict(equivalent=None, method='all independent complete QF group queries UNSAT',
                  plan_sha256=batch.sha256, obligations=len(batch.queries),
                  all_original_conjuncts_retained=True)
    manifest = batch.manifest
    records = manifest['groups']
    if len(reports) != len(records):
        return dict(result, reason='incomplete or duplicate group coverage')
    seen, transcripts = set(), []
    for report in reports:
        index = report.get('index')
        if type(index) is not int or not 0 <= index < len(records) or index in seen:
            return dict(result, reason='invalid or duplicate group index')
        seen.add(index)
        query_hash = _sha(batch.queries[index])
        if (report.get('plan_sha256') != batch.sha256
                or report.get('query_sha256') != query_hash
                or records[index]['query_sha256'] != query_hash):
            return dict(result, reason='result does not bind the complete original query')
        stdout = report.get('stdout')
        if (type(report.get('returncode')) is not int or report['returncode'] != 0
                or not isinstance(stdout, str) or stdout.strip() != 'unsat'):
            return dict(result, reason='no complete successful UNSAT transcript')
        transcripts.append(dict(index=index, query_sha256=query_hash,
                                stdout_sha256=_sha(stdout.encode())))
    assert seen == set(range(len(records)))
    return dict(result, equivalent=True, transcripts=sorted(transcripts,key=lambda x:x['index']),
                reason='every original group covered by an exact complete UNSAT query')
