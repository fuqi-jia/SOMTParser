"""Exact joint feasible-relation/signed-cost projection against an SMT target.

This compares every explicit source observation, existentially closing all
remaining flat/target variables. It does not compare optimum values or assert
that equality only at optimum implies model equivalence.
"""
import io
from ..phase_events import timed_phase
import z3
from tools import validate_packed_smt_stream as scanner
from ..boolean_structure import structural_equivalence
from ..existential_definitions import eliminate_existential_definitions
from ..integer_order import normalize_integer_order
from ..full_relation_certificate import prove_complete_relation as prove_qf_conjunctions
from ..nonrecursive_helpers import normalize as normalize_nonrecursive_helpers
from .fzn_json_source import Unsupported,need,finite_set
from tools.semantic_checks.ground_array_projection import UnsupportedArrayProjection
from ..conjunctive_array_projection import project_conjunctive_array_reads
from ..circuit_rank_witness import normalize_root_circuit_ranks
from ..observed_constants import project_observed_constants
from ..finite_scalar_tables import normalize_finite_scalar_tables
from ..common_public_terms import abstract_common_public_products

def read_target(data):
    variables={};directions=[];prefix=[];assertions=0;tail=[];body=False;recursive_helpers=False
    def sort(tokens,index):
        need(index<len(tokens),'truncated target sort');token=tokens[index]
        if token==('atom',b'Int'):return z3.IntSort(),index+1
        if token==('atom',b'Real'):return z3.RealSort(),index+1
        if token==('atom',b'Bool'):return z3.BoolSort(),index+1
        need(tokens[index:index+2]==[('paren',b'('),('atom',b'Array')],'unsupported target sort')
        domain,i=sort(tokens,index+2);value,i=sort(tokens,i);need(tokens[i]==('paren',b')'),'array sort delimiter');return z3.ArraySort(domain,value),i+1
    for command in scanner.commands(io.BytesIO(data),max_command_bytes=float('inf')):
        head,stream=scanner.command_head(command)
        if tail:need(head in ['get-model','get-objectives','exit'] and tail[-1]!='exit' and head not in tail,'target query tail')
        if head in ['check-sat','get-model','get-objectives','exit']:
            need(list(stream)==[('paren',b')')],'target query arguments');need(bool(tail) or head=='check-sat','target query order');tail.append(head);continue
        if head in ['declare-const','declare-fun']:
            tokens=list(stream);need(bool(tokens),'missing target declaration');name=tokens[0];need(name[0] in ['atom','quoted'],'target symbol token')
            index=1
            if head=='declare-fun':need(tokens[1:3]==[('paren',b'('),('paren',b')')],'non-nullary target function');index=3
            typ,index=sort(tokens,index);need(tokens[index:]==[('paren',b')')],'target declaration suffix');name=name[1].decode();need(name not in variables,'duplicate target symbol');variables[name]=z3.Const(name,typ)
        elif head in ['define-fun','define-fun-rec']:
            recursive_helpers=recursive_helpers or head=='define-fun-rec'
        elif head in ['set-info','set-logic']:need(not body,'late target metadata')
        elif head=='set-option':need(list(stream)==[('atom',b':opt.priority'),('atom',b'lex'),('paren',b')')],'target semantic option')
        elif head=='assert':body=True;assertions+=1
        elif head in ['minimize','maximize']:body=True;directions.append(head)
        else:raise Unsupported('target command '+head)
        prefix.append(command.raw)
    need(tail[-1:]==['exit'],'target EOF/query coverage')
    # Declarations/helpers may follow assertions or objectives. Preserve every
    # command in its original position: Z3 validates scope and rejects forward
    # references instead of making them legal by hoisting declarations.
    module=b'\n'.join(prefix)
    if recursive_helpers:
        # Recursive declarations are registered in their Z3 context. Validate
        # in a disposable context so repeated imports cannot collide by name.
        validation=z3.Optimize(ctx=z3.Context())
        validation.from_string(module.decode())
        need(len(validation.assertions())==assertions and len(validation.objectives())==len(directions),'original target parse count mismatch')
        # A nonrecursive RecFunction can capture globals outside the later
        # existential closure; macro expansion exposes those dependencies.
        try:module,_=normalize_nonrecursive_helpers(module)
        except ValueError as error:raise Unsupported(str(error)) from error
    target=z3.Optimize();target.from_string(module.decode())
    need(len(target.assertions())==assertions and len(target.objectives())==len(directions),'target parse count mismatch')
    return variables,target,directions

def compare(flat,observations,data,*,flatten_multidimensional_arrays=False,solve=False,
            complete_relation_callback=None, progress_callback=None):
    """Compare complete relations; optionally archive them before normalization.

    The callback receives the complete joint formulas, including signed cost,
    and its return value is ignored. It does not perform a solver query.
    progress_callback optionally receives phase timing events; its return value
    is also ignored and cannot establish equivalence.
    """
    with timed_phase(progress_callback, 'target-parse'):
        variables,target,directions=read_target(data)
    with timed_phase(progress_callback, 'observation-map'):
        expected=[] if flat.method=='satisfy' else [flat.method]
        need(directions==expected,'ordered objective direction/count differs')
        source_bindings=[];target_equalities=[];public=[]
        names={row['name'] for row in observations}
        # The native frontend's declared source-array convention is independently
        # supplied by its pinned frontend report. No suffix or index-base guessing.
        for row in observations:
            name=row['name'];need(name in variables,'public source declaration absent from exact target map '+name)
            left=row['value']
            if isinstance(left,frozenset):left=finite_set([(i,i) for i in sorted(left)])
            if type(left)is int:left=z3.IntVal(left)
            value=variables[name];indices=row['indices'];dims=row['dimensions']
            if indices is not None:
                need(z3.is_array(value),'public source array is not target Array')
                if len(indices)==1:index=indices[0]
                else:
                    need(flatten_multidimensional_arrays,'multidimensional native array layout not explicitly authorized');index=0
                    for d,i in zip(dims,indices):need(i in d,'observation outside source extent');index=index*len(d)+d.index(i)
                value=z3.Select(value,index)
            need(left.sort().eq(value.sort()),'source/target public sort mismatch')
            coordinate=z3.FreshConst(left.sort(),'public');public.append(coordinate);source_bindings.append((coordinate,left));target_equalities.append(coordinate==value)
        cost=None
        if expected:
            cost=z3.FreshConst(flat.objective.sort(),'signed_cost');need(cost.sort().eq(target.objectives()[0].sort()),'signed-cost sort mismatch');target_equalities.append(cost==target.objectives()[0])
    with timed_phase(progress_callback, 'source-projection'):
        reference=flat.projected(source_bindings,signed_cost=cost)
    target_body=z3.And(*target.assertions(),*target_equalities)
    private=list(variables.values())
    with timed_phase(progress_callback, 'complete-query-archive'):
        if complete_relation_callback is not None:
            original_target=z3.Exists(private,target_body) if private else target_body
            complete_relation_callback(reference,original_target)
    rank_normalization=dict(source=0,target=0)
    with timed_phase(progress_callback, 'source-array-projection'):
        source_array_projection=dict(applied=False,arrays=0,cells=0)
        try:
            normalized=normalize_root_circuit_ranks(reference)
            projected=project_conjunctive_array_reads(normalized.formula,[])
            reference=(z3.Exists(projected.private_variables,projected.body)
                       if projected.private_variables else projected.body)
            source_array_projection=dict(applied=bool(projected.eliminated_arrays),arrays=len(projected.eliminated_arrays),cells=len(projected.cells))
            rank_normalization['source']=normalized.normalized_circuits
        except UnsupportedArrayProjection as error:
            # The original complete relation remains available on refusal.
            source_array_projection['reason']=str(error)
    with timed_phase(progress_callback, 'target-array-projection'):
        array_projection=dict(applied=False,arrays=0,cells=0)
        try:
            normalized=normalize_root_circuit_ranks(target_body)
            projected=project_conjunctive_array_reads(normalized.formula,private)
            target_body=projected.body;private=list(projected.private_variables)
            rank_normalization['target']=normalized.normalized_circuits
            array_projection=dict(applied=bool(projected.eliminated_arrays),arrays=len(projected.eliminated_arrays),cells=len(projected.cells))
            if projected.consistency_conditions:array_projection['consistency_conditions']=len(projected.consistency_conditions)
        except UnsupportedArrayProjection as error:
            array_projection['reason']=str(error)
        observed=project_observed_constants(target_body,private,public)
        target_body=observed.body;private=list(observed.private_variables)
        # Closed literal tables are exact scalar expressions; rewriting before
        # Exists avoids carrying array theory into the quantified scalar relation.
        table_normalization=normalize_finite_scalar_tables(target_body)
        target_body=table_normalization.formula
        candidate=z3.Exists(private,target_body) if private else target_body
    # qe-light only performs equivalence-preserving rewriting; residual
    # quantifiers remain part of the complete formula and can be inconclusive.
    def reduce(expr):
        goal=z3.Goal();goal.add(expr);return z3.Then('simplify','qe-light','simplify')(goal).as_expr()
    # Eliminate witnessed definitions before qe-light: on large compiler
    # outputs the generic tactic otherwise repeatedly scans the same chains.
    # Each elimination retains the complete substituted body and signed cost.
    with timed_phase(progress_callback, 'source-definition-elimination-initial'):
        early_source_definitions=eliminate_existential_definitions(reference)
    with timed_phase(progress_callback, 'target-definition-elimination-initial'):
        early_target_definitions=eliminate_existential_definitions(candidate)
    with timed_phase(progress_callback, 'qe-light-initial'):
        a,b=reduce(early_source_definitions.formula),reduce(early_target_definitions.formula)
    with timed_phase(progress_callback, 'definition-elimination-secondary'):
        source_definitions=eliminate_existential_definitions(a)
        target_definitions=eliminate_existential_definitions(b)
    with timed_phase(progress_callback, 'qe-light-secondary'):
        a,b=reduce(source_definitions.formula),reduce(target_definitions.formula)
    with timed_phase(progress_callback, 'integer-order-normalization'):
        source_order,target_order=normalize_integer_order(a),normalize_integer_order(b)
        a,b=source_order.formula,target_order.formula
    with timed_phase(progress_callback, 'structural-correspondence'):
        structure=structural_equivalence(a,b);equivalent=structure['equivalent'];answer=None;counterexample=None;queries=0;public_term_proof=None
        if not equivalent and z3.is_false(z3.simplify(z3.Xor(a,b))):equivalent=True
    conjunction_proof=None
    if not equivalent and solve:
        with timed_phase(progress_callback, 'complete-relation-certificate'):
            conjunction_proof=prove_qf_conjunctions(a,b)
        queries+=conjunction_proof['solver_queries']
        if conjunction_proof['equivalent'] is True:equivalent=True
    if not equivalent and solve:
        with timed_phase(progress_callback, 'public-product-abstraction'):
            abstraction=abstract_common_public_products(a,b,public)
        if abstraction.substitutions:
            with timed_phase(progress_callback, 'abstract-relation-solver'):
                probe=z3.Solver();probe.add(z3.Xor(abstraction.left,abstraction.right));abstract_answer=probe.check();queries+=1
            public_term_proof=dict(method='common public product abstraction; only UNSAT transfers to the original relations',solver_answer=str(abstract_answer),terms=[dict(original=term.sexpr(),coordinate=value.sexpr(),sort=str(term.sort())) for term,value in abstraction.substitutions],original_formulas_required_on_non_unsat=True)
            if abstract_answer==z3.unsat:equivalent=True;answer=z3.unsat
            elif abstract_answer==z3.unknown:public_term_proof['solver_reason_unknown']=probe.reason_unknown()
    if not equivalent and solve:
        with timed_phase(progress_callback, 'complete-relation-solver'):
            solver=z3.Solver();solver.add(z3.Xor(a,b));answer=solver.check()
        queries+=1
        if answer==z3.unsat:equivalent=True
        elif answer==z3.sat:counterexample=str(solver.model())
    result=dict(array_projection=array_projection,equivalent=equivalent,source_observable_cells=len(public),source_observable_names=sorted(names),all_source_constraints_retained=True,all_target_assertions_retained=True,target_assertions=len(target.assertions()),source_flat_variables=len(flat.variables),target_variables=len(variables),objectives=len(expected),method='full existential observation projection with joint feasible signed-cost coordinate',domain_independent_cost_identity_claimed=False,structural=structure,solver_queries=queries,solver_answer=str(answer) if answer is not None else None,counterexample=counterexample)
    result['source_array_projection']=source_array_projection
    result['circuit_rank_normalization']=rank_normalization
    result['integer_order_normalization']=dict(source_comparisons=source_order.eligible_comparisons,target_comparisons=target_order.eligible_comparisons)
    result['existential_definitions']={label:dict(direct=early.direct_definitions+late.direct_definitions,conditional=early.conditional_definitions+late.conditional_definitions,scalarized_arrays=early.scalarized_arrays+late.scalarized_arrays,indicator_products=early.indicator_products+late.indicator_products,before_reduction=dict(direct=early.direct_definitions,conditional=early.conditional_definitions,scalarized_arrays=early.scalarized_arrays,indicator_products=early.indicator_products)) for label,early,late in [('source',early_source_definitions,source_definitions),('target',early_target_definitions,target_definitions)]}
    result['finite_scalar_tables']=dict(completed=table_normalization.completed,table_rewrites=table_normalization.table_rewrites,canonical_reorders=table_normalization.canonical_reorders)
    if conjunction_proof is not None:result['conjunction_certificate']=conjunction_proof
    if public_term_proof is not None:result['public_term_abstraction']=public_term_proof
    if answer is not None and answer == z3.unknown:
        result['solver_reason_unknown']=solver.reason_unknown()
    return result
