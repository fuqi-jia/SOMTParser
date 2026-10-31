"""Noninteractive, no-solver translation for HIR, direct SMT and hybrid models."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

from smt_bridge import read_json, request_for
from candidate_protocol import resolve_source_spans, schema_with_source_anchors, schema_diagnostics

HYBRID_SCHEMA = "somt-nl-hybrid-v1"
TOKEN = re.compile(r'\s+|;[^\n]*|"(?:[^"]|"")*"|\|[^|\\]*\||[()]|[^\s();"|]+')
QUERY = {"check-sat", "get-model", "get-objectives", "get-unsat-core", "exit"}


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def expressions(text):
    """Parse S-expression structure, preserving quoted tokens, not semantics."""
    tokens, position = [], 0
    while position < len(text):
        match = TOKEN.match(text, position)
        if not match:
            raise ValueError("malformed SMT token at offset " + str(position))
        token = match.group()
        position = match.end()
        if not token.isspace() and not token.startswith(";"):
            tokens.append(token)
    root, stack = [], []
    current = root
    for token in tokens:
        if token == "(":
            node = []
            current.append(node)
            stack.append(current)
            current = node
        elif token == ")":
            if not stack:
                raise ValueError("unbalanced SMT closing parenthesis")
            current = stack.pop()
        else:
            current.append(token)
    if stack:
        raise ValueError("unbalanced SMT opening parenthesis")
    return root


def sexpr(node):
    """Write nested SMT terms without consuming the Python call stack."""
    if not isinstance(node, list):
        return node
    pieces = ["("]
    frames = [(node, 0)]
    active = {id(node)}
    while frames:
        items, index = frames[-1]
        if index == len(items):
            pieces.append(")")
            frames.pop()
            active.remove(id(items))
            continue
        frames[-1] = (items, index + 1)
        if index:
            pieces.append(" ")
        child = items[index]
        if isinstance(child, list):
            if id(child) in active:
                raise ValueError("cyclic SMT expression")
            pieces.append("(")
            active.add(id(child))
            frames.append((child, 0))
        else:
            pieces.append(child)
    return "".join(pieces)


def exact_fields(value, required, optional=()):
    if not isinstance(value, dict) or not set(required) <= set(value) or set(value) - set(required) - set(optional):
        raise ValueError("unexpected model fields; required: " + ", ".join(required))


def expand_macros(value):
    """Small compositional conveniences; native HIR owns all primitive semantics."""
    if isinstance(value, list):
        return [expand_macros(item) for item in value]
    if not isinstance(value, dict):
        return value
    if "macro" not in value:
        return {key:expand_macros(item) for key,item in value.items()}
    exact_fields(value, ("macro", "args"))
    name, args = value["macro"], expand_macros(value["args"])
    if not isinstance(args, list):
        raise ValueError("macro args must be a list")
    op = lambda name,*xs: {"op":name,"args":list(xs)}
    if name == "makespan":
        if not args or any(not isinstance(pair,list) or len(pair)!=2 for pair in args):
            raise ValueError("makespan requires nonempty [start,duration] pairs")
        ends = [op("add", *pair) for pair in args]
        # Exact maximum, including when it occurs outside a minimization goal.
        def maximum(items):
            if len(items) == 1:
                return items[0]
            middle = len(items) // 2
            left, right = maximum(items[:middle]), maximum(items[middle:])
            return op("ite", op("ge",left,right), left,right)
        # Balanced construction avoids exponential JSON duplication from a
        # left fold whose accumulator occurs twice at every step.
        return maximum(ends)
    if name == "distance_to" and len(args) == 2:
        return op("abs", op("sub",*args))
    if name == "weighted_sum":
        if any(not isinstance(pair,list) or len(pair)!=2 for pair in args):
            raise ValueError("weighted_sum requires [weight,expression] pairs")
        return op("add", *[op("mul",*pair) for pair in args])
    if name == "in_range" and len(args) == 3:
        x,lo,hi = args
        return op("and",op("ge",x,lo),op("le",x,hi))
    if name in ("exactly", "at_most", "at_least") and len(args) == 2 and isinstance(args[1], list):
        count = {"cp":"count_true", "items":args[1]}
        return op({"exactly":"eq","at_most":"le","at_least":"ge"}[name],count,args[0])
    raise ValueError("unsupported macro or arity: " + str(name))


def get_macro_catalog():
    return {"schema":"somt-hir-macros-v1", "names":[
        "makespan","distance_to","weighted_sum","in_range","exactly","at_most","at_least"]}


def expand_hir_macros(model):
    """Expand expression positions only; data may legally have a key 'macro'."""
    result = copy.deepcopy(model)
    if not isinstance(result,dict):
        return result
    for field in ("constraints","soft_constraints","objectives"):
        entries = result.get(field, [])
        if isinstance(entries,list):
            for entry in entries:
                if isinstance(entry,dict) and "expr" in entry:
                    entry["expr"] = expand_macros(entry["expr"])
    goal = result.get("goal")
    if isinstance(goal,dict) and "expr" in goal:
        goal["expr"] = expand_macros(goal["expr"])
    functions = result.get("functions",[])
    if isinstance(functions,list):
        for function in functions:
            if isinstance(function,dict) and "body" in function:
                function["body"] = expand_macros(function["body"])
    return result


def present_request(request, profile):
    if profile not in ("full","compact"):
        raise ValueError("unknown request profile")
    request["request_profile"] = profile
    request["schema"] = schema_with_source_anchors(request["schema"],request["language"])
    request["source_length"] = len(request["source"])
    request["source_anchor_extension"] = {
        "schema":"somt-source-anchor-v1", "span_example":{"quote":"exact source substring"},
        "instruction":"A permitted span may be [start,end] or {quote:exact source text,occurrence:optional zero-based index}. "
                      "The generator resolves quotations deterministically. Repeated quotes require occurrence. "
                      "Do not add spans in fields where the schema does not allow them."}
    if profile == "full":
        return request
    schema = request["schema"]
    hir_schema = schema["properties"]["hir"] if request["language"]=="hybrid" else schema
    omitted = {}
    if "constructor_api" in hir_schema:
        omitted["constructor_api_sha256"] = sha(canonical(hir_schema.pop("constructor_api")))
    for name in ("instruction","hir_instruction"):
        if name in request:
            omitted[name+"_sha256"] = sha(request.pop(name))
    request["omitted_documentation"] = omitted
    request["instruction"] = (
        "Return exactly one complete JSON candidate matching this schema and the selected route. "
        "Preserve every source clause, domain, unit, strict inequality and objective. Context belongs "
        "to the caller; apply it but do not return a context field. All required root fields are "
        "required even when empty or null. Link constraints/objectives to the unchanged source. "
        "Use unresolved for genuinely competing interpretations not settled by source/context, "
        "not unknown values to solve for. Do not add unstated bounds or constraints. "
        "HIR constraints are Boolean expressions, variables use {var:name}, and source spans "
        "belong only to schema-supported fields. In hybrid the hir field owns declarations and "
        "objectives; smt_constraints contains single Boolean terms, never commands. "
        "Direct SMT links must quote actual program fragments; do not emit includes or set-option. "
        "The full native validation schema is retained; only redundant API documentation was "
        "omitted. A full request can be obtained with request_profile=full.")
    return request


def get_request(source, context, route, request_profile="full", dialect="z3"):
    if dialect not in ("z3", "optimathsat", "smtlib-pure"):
        raise ValueError("unknown target dialect")
    if route != "hybrid":
        result = request_for(source, context, route)
        result["dialect"] = dialect
        result["macro_extension"] = get_macro_catalog() if route == "hir" else None
        return present_request(result,request_profile)
    base = request_for(source, context, "hir")
    base["dialect"] = dialect
    base["language"] = "hybrid"
    base["macro_extension"] = get_macro_catalog()
    hir_schema = base["schema"]
    definitions = hir_schema.pop("$defs", None)
    base["schema"] = dict(type="object", additionalProperties=False,
        required=["schema","hir","smt_constraints"], properties={
            "schema":{"const":HYBRID_SCHEMA}, "hir":hir_schema,
            "smt_constraints":{"type":"array", "items":{
                "type":"object", "additionalProperties":False,
                "required":["span","term"], "properties":{
                    "span":{"type":"array","items":{"type":"integer"},"minItems":2,"maxItems":2},
                    "term":{"type":"string","minLength":1}}}}})
    # HIR's local JSON pointers resolve from the document root, even when its
    # schema is nested. Preserve their scope in the combined schema.
    if definitions is not None:
        base["schema"]["$defs"] = definitions
    base["hir_instruction"] = base.pop("instruction")
    base["instruction"] = (
        "Return a hybrid envelope matching schema. hir_instruction applies only to the nested hir field. "
        "HIR owns all declarations, domains and objectives; "
        "smt_constraints adds only Boolean SMT terms over that same symbol interface. "
        "No SMT commands, declarations, includes, options or objectives in extensions. "
        "Put genuine ambiguities in hir.unresolved; never weaken a requirement to fit HIR.")
    return present_request(base,request_profile)


def render(source, model, *, route="hir", dialect="z3", context=None):
    import somtparser as sp
    dialects = {"z3":sp.OmtDialect.Z3, "optimathsat":sp.OmtDialect.OptiMathSAT,
                "smtlib-pure":sp.OmtDialect.NONE}
    if route not in ("hir","smtlib2","hybrid") or dialect not in dialects:
        raise ValueError("unknown route or dialect")
    original = copy.deepcopy(model)
    model, source_anchors = resolve_source_spans(model,source,route)
    if route == "hybrid":
        exact_fields(model,("schema","hir","smt_constraints"))
        if model["schema"] != HYBRID_SCHEMA or not isinstance(model["smt_constraints"],list):
            raise ValueError("invalid hybrid model")
        selected = expand_hir_macros(model["hir"])
    else:
        selected = expand_hir_macros(model) if route == "hir" else copy.deepcopy(model)
    if route == "smtlib2" and isinstance(selected,dict) and isinstance(selected.get("program"),str):
        # The final template has one query. Do not collapse an incremental
        # transcript or discard assumptions used by an original query.
        seen_query = False
        for node in expressions(selected["program"]):
            if not isinstance(node,list) or not node or not isinstance(node[0],str):
                raise ValueError("expected SMT commands")
            command = node[0]
            if command in ("push","pop","reset","reset-assertions","check-sat-assuming"):
                raise ValueError("single-state translation does not accept " + command)
            if command == "check-sat":
                if seen_query or len(node) != 1:
                    raise ValueError("expected at most one plain check-sat query")
                seen_query = True
            elif seen_query and command not in QUERY:
                raise ValueError("model construction after a query is not supported")
            elif command == "exit":
                raise ValueError("omit exit; the caller owns the solver session")
    language = "smtlib2" if route == "smtlib2" else "hir"
    candidate = sp.propose_nl(source, provider=lambda request:selected,
                              language=language, context={} if context is None else context)
    result = sp.compile_candidate(candidate, accept_digest=candidate.digest, dialect=dialects[dialect])
    if not result.ok:
        diagnostic_model = dict(model,hir=selected) if route=="hybrid" else selected
        details = schema_diagnostics(diagnostic_model,get_request(source,context,route)["schema"])
        return dict(status="translation-error", ir=original, code=None,
                    assumptions=selected.get("assumptions",[]), ambiguities=selected.get("unresolved",[]),
                    diagnostics=list(result.diagnostics),diagnostic_details=details,
                    meta=dict(route=route,dialect=dialect,solver_executed=False,
                              source_sha256=sha(source),candidate_digest=candidate.digest))
    code = result.to_smt2()
    if route == "hybrid":
        nodes = expressions(code)
        allowed = {"set-logic","set-option","declare-sort","declare-datatype","declare-datatypes",
                   "declare-fun","declare-const","define-fun","assert","assert-soft","minimize","maximize"}
        body = []
        for node in nodes:
            if not isinstance(node,list) or not node or not isinstance(node[0],str):
                raise ValueError("unexpected backend command")
            if node[0] in QUERY:
                continue
            if node[0] not in allowed:
                raise ValueError("unsupported hybrid backend command: " + node[0])
            body.append(sexpr(node))
        for extension in model["smt_constraints"]:
            exact_fields(extension,("span","term"))
            span = extension["span"]
            if (not isinstance(span,list) or len(span)!=2 or any(type(x) is not int for x in span)
                    or not 0 <= span[0] < span[1] <= len(source)):
                raise ValueError("invalid hybrid source span")
            if not isinstance(extension["term"],str):
                raise ValueError("hybrid term must be SMT text")
            terms = expressions(extension["term"])
            if len(terms)!=1:
                raise ValueError("hybrid extension must contain exactly one term")
            term = terms[0]
            if isinstance(term,list) and term and isinstance(term[0],str) and term[0] in allowed | QUERY:
                raise ValueError("hybrid extension cannot contain commands")
            body.append("(assert " + sexpr(term) + ")")
        joined = "\n".join(body) + "\n(check-sat)\n"
        # Type/symbol checking and final export, never solver execution.
        translated = sp.translate(source=joined, language="smtlib2", dialect=dialects[dialect])
        if not translated.ok:
            return dict(status="translation-error",ir=original,code=None,
                        assumptions=selected.get("assumptions",[]),ambiguities=selected.get("unresolved",[]),
                        diagnostics=[d.message for d in translated.diagnostic_items],
                        meta=dict(route=route,dialect=dialect,solver_executed=False,source_sha256=sha(source)))
        code = translated.to_smt2(dialect=dialects[dialect])
    # Query responses are state-dependent. Emit check-sat only; the caller can
    # request a model/core after observing the returned result.
    nodes = expressions(code)
    commands = [n for n in nodes if isinstance(n,list) and n and n[0] not in QUERY]
    code = "; SOMTParser translation | route=" + route + " | dialect=" + dialect + "\n"
    code += "\n".join(sexpr(n) for n in commands) + "\n; query\n(check-sat)\n"
    objectives = sum(n[0] in ("minimize","maximize") for n in commands)
    soft = sum(n[0] == "assert-soft" for n in commands)
    logic = next((n[1] for n in commands if n[0]=="set-logic"),None)
    interface = [sexpr(n) for n in commands if n[0] in
                 ("declare-sort","declare-datatype","declare-datatypes","declare-const","declare-fun")]
    return dict(status="translated",ir=original,code=code,
                assumptions=selected.get("assumptions",[]),ambiguities=selected.get("unresolved",[]),
                diagnostics=[],meta=dict(route=route,dialect=dialect,logic=logic,
                    task=selected.get("decision"),objectives=objectives,soft=soft,
                    solver_executed=False,intent_preservation="not-proved",degraded=False,
                    source_sha256=sha(source),ir_sha256=sha(canonical(original)),
                    candidate_digest=candidate.digest,code_sha256=sha(code),
                    candidate_digest_scope="hir-base" if route=="hybrid" else "candidate",
                    smt_symbol_interface=interface,
                    hybrid_extensions=len(model["smt_constraints"]) if route=="hybrid" else 0,
                    source_anchor_resolutions=source_anchors,
                    verdict_polarity=result.report()["verdict_polarity"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("model",type=Path,nargs="?")
    parser.add_argument("--source",type=Path,required=True)
    parser.add_argument("--route",choices=["hir","smtlib2","hybrid"],default="hir")
    parser.add_argument("--dialect",choices=["z3","optimathsat","smtlib-pure"],default="z3")
    parser.add_argument("--mode",choices=["full","code","ir"],default="full")
    parser.add_argument("--context",type=Path)
    parser.add_argument("--request",action="store_true")
    parser.add_argument("--request-profile",choices=["full","compact"],default="full")
    args = parser.parse_args()
    source = args.source.read_text(encoding="utf-8")
    context = read_json(args.context) if args.context else {}
    if args.request:
        print(canonical(get_request(source,context,args.route,args.request_profile,args.dialect)))
        return 0
    if args.model is None:
        parser.error("model is required unless --request is selected")
    result = render(source,read_json(args.model),route=args.route,dialect=args.dialect,context=context)
    if result["status"] != "translated":
        print(canonical(result),file=sys.stderr if args.mode=="code" else sys.stdout)
        return 2
    print(result["code"] if args.mode=="code" else canonical(result["ir"] if args.mode=="ir" else result),end="\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError,ValueError,TypeError,KeyError,RecursionError) as exc:
        print(canonical(dict(status="translation-error",code=None,diagnostics=[str(exc)],
                             meta={"solver_executed":False})),file=sys.stderr)
        raise SystemExit(2)
