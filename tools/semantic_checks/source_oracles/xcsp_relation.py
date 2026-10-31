"""Complete source relation / signed-cost comparison, never SAT-only matching."""
import io
import z3
from tools import validate_packed_smt_stream as scanner
from ..boolean_structure import structural_equivalence
from ..closed_helpers import retain_closed_helpers
from ..domain_signed_costs import prove_domain_signed_costs
from ..finite_table_helpers import compact_literal_table_module
from ..full_relation_certificate import prove_complete_relation
from ..universal_conjuncts import prove_universal_conjunctions
from .xcsp_source import Unsupported,need

def target_model(data,source,private_scalars=None):
    declared={};helpers=set();directions=[];assertion_count=0;seen_body=False;tail=[];prefix=[]
    for command in scanner.commands(io.BytesIO(data),max_command_bytes=float('inf')):
        head,ts=scanner.command_head(command)
        if tail:
            need(head in ['get-model','get-objectives','exit'] and tail[-1]!='exit' and head not in tail,'invalid query tail')
        if head in ['check-sat','get-model','get-objectives','exit']:
            need(list(ts)==[('paren',b')')],'query arguments')
            need(bool(tail) or head=='check-sat','tail must start with check-sat');tail.append(head);continue
        if head in ['declare-const','declare-fun']:
            tokens=list(ts)
            if head=='declare-fun':need(len(tokens)==5 and tokens[1:3]==[('paren',b'('),('paren',b')')],'non-nullary target declaration');name,sort=tokens[0],tokens[3]
            else:need(len(tokens)==3,'declaration shape');name,sort=tokens[0],tokens[1]
            need(name[0] in ['atom','quoted'] and sort in [('atom',b'Int'),('atom',b'Bool')],'target coordinate sort')
            name=name[1].decode();need(name not in declared,'duplicate target coordinate '+name)
            if name in source.variables:need(sort==('atom',b'Int'),'source coordinate sort changed')
            else:
                need(private_scalars is not None,'target coordinate absent from exact source map: '+name)
                private_scalars.append(z3.Const(name,z3.IntSort() if sort[1]==b'Int' else z3.BoolSort()))
            declared[name]=sort[1].decode()
        elif head in ['define-fun','define-fun-rec']:
            tokens=list(ts);need(bool(tokens) and tokens[0][0] in ['atom','quoted'],'helper name')
            name=tokens[0][1];need(name.decode() not in source.variables and name not in helpers,'helper identity collision');helpers.add(name)
            if head=='define-fun-rec':
                # Some emitters use the recursive declaration form for shared
                # but nonrecursive helpers. Absence of the function identifier
                # from every parameter/sort/body token is a sufficient proof
                # of nonrecursion. Earlier helpers cannot forward-reference it
                # without a declaration, and non-nullary declarations are
                # rejected above. Genuine recursion is never expanded here.
                need(not any(t[0] in ['atom','quoted'] and t[1]==name for t in tokens[1:]),'recursive target helper unsupported')
                # Closed helpers can retain their complete definition once;
                # captured globals still require macro expansion before Exists.
                prefix.append(command.raw);continue
        elif head in ['set-logic','set-info']:need(not seen_body,'late metadata')
        elif head=='set-option':need(list(ts)==[('atom',b':opt.priority'),('atom',b'lex'),('paren',b')')],'unsupported target semantic option')
        elif head=='assert':seen_body=True;assertion_count+=1
        elif head in ['minimize','maximize']:seen_body=True;directions.append(head)
        else:raise Unsupported('target command '+head)
        prefix.append(command.raw)
    need(tail[-1:]==['exit'],'target incomplete tail')
    need(set(source.variables)<=set(declared),'target source-coordinate coverage changed')
    need(directions==[d for d,v in source.objectives],'target objective direction/count changed')
    module,helper_binding=retain_closed_helpers(b'\n'.join(prefix))
    target=z3.Optimize();target.from_string(module.decode())
    target._somt_closed_helper_binding=helper_binding
    # Keep full text only when the existing import found a shared helper.
    # Large helper-free targets must not acquire a second tokenization/copy.
    target._somt_complete_module=module if helper_binding['shared'] else None
    need(len(target.assertions())==assertion_count,'target assertion count changed on parse')
    need(len(target.objectives())==len(directions),'target objective count changed on parse')
    return target

def compare(source,data,*,solve=False,project_private_scalars=False,
            complete_relation_callback=None):
    """Compare full feasible relations and ordered, signed objective values.

    The optional callback observes the original complete joint formulas before
    simplification or certificate projection. Its return value is ignored.
    Only proven complete certificates set equivalent=True; unsuccessful
    sufficient certificates retain the original complete solver fallback.
    """
    # Opt-in projection preserves the exact public source map. Only extra
    # scalar declarations are private, and every original target assertion
    # remains under the same existential binder. The strict default is kept.
    private=[] if project_private_scalars else None
    target=target_model(data,source,private);left=source.relation;body=z3.And(*target.assertions())
    right=z3.Exists(private,body) if private else body
    result=dict(source_variables=len(source.variables),source_constraints=source.constraint_count,
                target_assertions=len(target.assertions()),source_objectives=len(source.objectives),
                relation_equivalent=None,signed_cost_equal=None,solver_queries=0,unsupported=False,
                all_source_constraints_retained=True,all_target_assertions_retained=True,
                joint_ordered_signed_cost_retained=True)
    result['closed_helpers']=target._somt_closed_helper_binding
    if private:
        result['private_scalar_projection']=dict(count=len(private),sorts=[str(v.sort()) for v in private],all_assertions_retained=True)
    if solve or complete_relation_callback is not None or (source.objectives and (private or source.private_variables)):
        signed=[v if direction=='minimize' else -v for direction,v in source.objectives]
        target_costs=list(target.objectives())
        need(len(signed)==len(target_costs),'target objective count changed')
        need(all(a.sort().eq(b.sort()) for a,b in zip(signed,target_costs)),
             'target signed-cost sort changed')
        costs=[z3.FreshConst(v.sort(),prefix='joint_signed_cost') for v in signed]
        source_body=z3.And(*source.constraints,*[c==v for c,v in zip(costs,signed)])
        target_body=z3.And(*target.assertions(),*[c==v for c,v in zip(costs,target_costs)])
        source_private=tuple(source.private_variables)
        complete_left=z3.Exists(source_private,source_body) if source_private else source_body
        complete_right=z3.Exists(private,target_body) if private else target_body
        if complete_relation_callback is not None:
            complete_relation_callback(complete_left,complete_right)
        result['signed_cost_scope']='complete joint feasible relation and ordered signed-cost values'
        if solve:
            # Decode complete literal tables before either proof path. A cost
            # identity can otherwise send an opaque recursive helper into the
            # feasibility solver before the existing table compaction runs.
            # The original complete query was already archived by the callback.
            proof_target=target
            compact_module=None
            table_binding=dict(method='exact-closed-literal-table-v1',applied=False,
                               fallback_reason='no retained closed helpers')
            if target._somt_complete_module is not None:
                compact_module,table_binding=compact_literal_table_module(target._somt_complete_module)
            result['literal_table_helpers']=table_binding
            if table_binding['applied']:
                try:
                    compact_target=z3.Optimize();compact_target.from_string(compact_module.decode())
                    need(len(compact_target.assertions())==len(target.assertions()),'compact target assertion count')
                    need(len(compact_target.objectives())==len(target.objectives()),'compact target objective count')
                    proof_target=compact_target
                except (z3.Z3Exception,ValueError) as error:
                    table_binding.update(applied=False,fallback_reason='complete compact module parse: '+str(error),
                                         attempted_output_sha256=table_binding['output_sha256'],
                                         output_sha256=table_binding['input_sha256'])
            # Preserve the original complete query above, then compose two
            # sufficient obligations before expanding a large joint cost DAG.
            # Cost identities use every original source domain; accepting the
            # instance ALSO requires full feasible-relation equivalence.
            if signed and not private and not source_private:
                domains=z3.And(*source.constraints[:len(source.variables)])
                domain_cost=prove_domain_signed_costs(domains,signed,list(proof_target.objectives()))
                result['domain_cost_certificate']=domain_cost
                if domain_cost['equivalent'] is True:
                    feasibility=prove_complete_relation(z3.simplify(left),
                                                        z3.simplify(z3.And(*proof_target.assertions())))
                    result['composed_feasibility_certificate']=feasibility
                    result['solver_queries']+=feasibility['solver_queries']
                    if feasibility['equivalent'] is True:
                        result['structural']=dict(executed=False,equivalent=None,
                                                  reason='complete feasibility certificate already proved')
                        result.update(relation_equivalent=True,signed_cost_equal=True,equivalent=True,
                                      signed_cost_scope='ordered signed-cost equality on all source-domain assignments',
                                      method='complete feasible-relation certificate composed with ordered source-domain signed-cost identities')
                        return result
            compact_body=z3.And(*proof_target.assertions(),
                                *[c==v for c,v in zip(costs,proof_target.objectives())])
            proof_right=z3.Exists(private,compact_body) if private else compact_body
            reduced=[z3.simplify(value) for value in (complete_left,proof_right)]
            proof=prove_complete_relation(*reduced)
            result['conjunction_certificate']=proof
            result['solver_queries']+=proof['solver_queries']
            proved=proof['equivalent'] is True
            if not proved:
                universal=prove_universal_conjunctions(*reduced)
                result['universal_certificate']=universal
                result['solver_queries']+=universal['solver_queries']
                proved=universal['equivalent'] is True
            if proved:
                # A complete joint certificate already covers feasibility.
                # Do not traverse both full DAGs again merely for diagnostics.
                # This records no independent structural check as performed.
                result['structural']=dict(executed=False,equivalent=None,
                                          reason='complete joint relation certificate already proved')
                result['relation_equivalent']=True
                if not source.objectives or private or source.private_variables:
                    result.update(signed_cost_equal=True,equivalent=True,
                                  method='complete joint feasible relation and ordered signed-cost certificate')
                    return result
                # The scalar API additionally requires objective equality on
                # every source-domain point, including infeasible points.
                # A joint feasible certificate cannot discharge that stronger
                # contract; retain the independent cost check below.
    if result['relation_equivalent'] is not True:
        reduced_left=z3.simplify(left);reduced_right=z3.simplify(right)
        structure=structural_equivalence(reduced_left,reduced_right)
        result['structural']=structure
        if structure['equivalent']:result['relation_equivalent']=True
        elif z3.is_false(z3.simplify(z3.Xor(left,right))):result['relation_equivalent']=True
        elif result['relation_equivalent'] is None and solve:
            solver=z3.Solver();solver.add(z3.Xor(left,right));answer=solver.check();result['solver_queries']+=1;result['relation_answer']=str(answer)
            if answer==z3.unsat:result['relation_equivalent']=True
            elif answer==z3.sat:result['relation_equivalent']=False;result['relation_counterexample']=str(solver.model())
            else:result['relation_unknown_reason']=solver.reason_unknown()
    if private:result['private_scalar_projection']=dict(count=len(private),sorts=[str(v.sort()) for v in private],all_assertions_retained=True)
    if not source.objectives:result['signed_cost_equal']=True
    elif private or source.private_variables:
        # Cost may itself mention witnesses. Bind the ordered signed-cost
        # observations inside that same existential relation, rather than
        # comparing expressions with accidentally free auxiliary constants.
        source_cost,target_cost=complete_left,complete_right
        proof=structural_equivalence(z3.simplify(source_cost),z3.simplify(target_cost))
        result['signed_cost_scope']='complete joint feasible relation and ordered signed-cost values'
        result['signed_cost_structural']=[proof]
        if proof['equivalent'] or z3.is_false(z3.simplify(z3.Xor(source_cost,target_cost))):result['signed_cost_equal']=True
        elif solve:
            solver=z3.Solver();solver.add(z3.Xor(source_cost,target_cost));answer=solver.check();result['solver_queries']+=1;result['cost_answer']=str(answer)
            if answer==z3.unsat:result['signed_cost_equal']=True
            elif answer==z3.sat:result['signed_cost_equal']=False;result['cost_counterexample']=str(solver.model())
            else:result['cost_unknown_reason']=solver.reason_unknown()
    else:
        # Optimize.objectives() uses minimization sign for maximize. Preserve
        # every offset and direction, and compare values on source domains,
        # independently of the feasibility constraints of the model.
        result['signed_cost_scope']='ordered signed-cost equality on all source-domain assignments'
        signed=[v if d=='minimize' else -v for d,v in source.objectives]
        equal=z3.And(*[a==b for a,b in zip(signed,target.objectives())])
        if z3.is_true(z3.simplify(equal)):result['signed_cost_equal']=True
        else:
            # A fresh cost coordinate turns exact arithmetic identity into a
            # Boolean formula accepted by the already-qualified structural
            # checker. Addition remains a multiset, and offsets/directions
            # remain present. This proves identity independently of domains
            # and feasible constraints; a mismatch stays inconclusive.
            proofs=[]
            for a,b in zip(signed,target.objectives()):
                coordinate=z3.FreshConst(a.sort(),prefix='signed_cost_observation')
                proofs.append(structural_equivalence(coordinate==z3.simplify(a),coordinate==z3.simplify(b)))
            result['signed_cost_structural']=proofs
            if all(p['equivalent'] for p in proofs):result['signed_cost_equal']=True
        if result['signed_cost_equal'] is None and solve:
            domains=z3.And(*source.constraints[:len(source.variables)])
            solver=z3.Solver();solver.add(domains,z3.Not(equal));answer=solver.check();result['solver_queries']+=1;result['cost_answer']=str(answer)
            if answer==z3.unsat:result['signed_cost_equal']=True
            elif answer==z3.sat:result['signed_cost_equal']=False;result['cost_counterexample']=str(solver.model())
            else:result['cost_unknown_reason']=solver.reason_unknown()
    result['equivalent']=result['relation_equivalent'] is True and result['signed_cost_equal'] is True
    result['method']='complete projected relation XOR and joint ordered signed-cost relation; structural sufficient proof first' if private or source.private_variables else 'complete source Boolean relation XOR and ordered signed-cost equality; structural sufficient proof first'
    return result
