"""Complete weighted-clause certificate, including exact hard AMO expansion.

Independent source clauses define public Booleans, feasibility, and every soft
weight. Target hard conjunctions/AMOs expand to precisely their implied clauses;
soft costs retain multiplicities and exact decimal bytes. No solver is invoked.
"""
from collections import Counter
from itertools import combinations
from .wcnf_stream_equivalence import SourceClauses, TargetTokens, VerificationError, _natural, _target_variable


def key(literals):
    values=set(literals)
    return None if any(-x in values for x in values) else tuple(sorted(values))


def expression(tokens, first):
    if first != b'(':
        if first is None or first == b')':raise VerificationError('missing expression')
        return first
    stack=[[]]
    while stack:
        token=next(tokens,None)
        if token is None:raise VerificationError('unterminated expression')
        if token==b'(':stack.append([])
        elif token==b')':
            node=stack.pop()
            if not stack:return node
            stack[-1].append(node)
        else:stack[-1].append(token)


def literal(node, declared):
    negative=isinstance(node,list) and len(node)==2 and node[0]==b'not'
    atom=node[1] if negative else node
    if not isinstance(atom,bytes):raise VerificationError('expected Boolean literal')
    number=_target_variable(atom)
    if number>declared:raise VerificationError('undeclared literal')
    return -number if negative else number


def clause(node, declared):
    values=[];pending=[node];tautology=False
    while pending:
        part=pending.pop()
        if isinstance(part,list) and part and part[0]==b'or':
            if len(part)==1:raise VerificationError('zero-arity or is not SMT syntax')
            pending.extend(part[1:])
        elif part==b'true':tautology=True
        elif part==b'false':pass
        else:values.append(literal(part,declared))
    return None if tautology else key(values)


def hard_clauses(node,declared):
    pending=[node]
    while pending:
        part=pending.pop()
        if isinstance(part,list) and part and part[0]==b'and':
            if len(part)==1:raise VerificationError('zero-arity and is not SMT syntax')
            pending.extend(part[1:]);continue
        if isinstance(part,list) and len(part)==3 and part[0]==b'<=' and part[2]==b'1':
            terms=part[1][1:] if isinstance(part[1],list) and part[1] and part[1][0]==b'+' else [part[1]]
            indicators=[]
            for term in terms:
                if term==b'0':continue
                if not isinstance(term,list) or len(term)!=4 or term[0]!=b'ite' or term[2:]!=[b'1',b'0']:
                    raise VerificationError('unsupported AMO indicator')
                indicators.append(literal(term[1],declared))
            # Sum of Boolean indicators <=1 iff every pair is not both true.
            # Preserve duplicate occurrences: [p,p] implies the unit clause !p.
            for a,b in combinations(indicators,2):yield key([-a,-b])
        else:yield clause(part,declared)


def verify_streams(source_stream,target_stream):
    source=SourceClauses(source_stream);hard=set();soft=Counter()
    for entry in source:
        k=key(entry.literals)
        if k is None:continue
        if entry.weight is None:hard.add(k)
        else:soft[(k,entry.weight)]+=1
    assert source.complete
    target=TargetTokens(target_stream);tokens=target.iterator
    declared=0;seen_hard=set();seen_soft=Counter();assertions=0;phase='metadata';logic=False;queried=False;exited=False;amo=0
    while True:
        first=next(tokens,None)
        if first is None:break
        if exited or first!=b'(':raise VerificationError('content outside command/after exit')
        cmd=expression(tokens,first)
        if not cmd or not isinstance(cmd[0],bytes):raise VerificationError('invalid command')
        head=cmd[0]
        if head==b'set-logic':
            if phase!='metadata' or logic or cmd!=[b'set-logic',b'ALL']:raise VerificationError('invalid/late logic')
            logic=True
        elif head in (b'declare-const',b'declare-fun'):
            if phase not in ('metadata','declarations'):raise VerificationError('late declaration')
            phase='declarations';declared+=1
            wanted=[head,cmd[1],b'Bool'] if head==b'declare-const' and len(cmd)>=2 else [head,cmd[1],[],b'Bool'] if len(cmd)>=2 else []
            if cmd!=wanted or _target_variable(cmd[1])!=declared:raise VerificationError('nonconsecutive/non-Boolean/nullary declaration')
        elif head in (b'assert',b'assert-soft'):
            if phase=='queries':raise VerificationError('assertion after query')
            phase='assertions';assertions+=1
            if head==b'assert':
                if len(cmd)!=2:raise VerificationError('assert arity')
                for k in hard_clauses(cmd[1],declared):
                    if k is None:continue
                    if k not in hard:raise VerificationError('extra/changed target hard clause')
                    seen_hard.add(k)
            else:
                if len(cmd)!=4 or cmd[2]!=b':weight':raise VerificationError('soft attributes/arity')
                weight=_natural(cmd[3],positive=True);k=clause(cmd[1],declared)
                if k is not None:
                    seen_soft[(k,weight)]+=1
                    if seen_soft[(k,weight)]>soft[(k,weight)]:raise VerificationError('extra/changed soft clause or exact weight')
        elif head in (b'check-sat',b'exit'):
            if len(cmd)!=1:raise VerificationError('query arity')
            phase='queries'
            if head==b'check-sat':
                if queried:raise VerificationError('duplicate query')
                queried=True
            else:exited=True
        else:raise VerificationError('unsupported command '+repr(head))
    expected=source.largest if source.declared_variables is None else source.declared_variables
    if declared!=expected or seen_hard!=hard or seen_soft!=soft:raise VerificationError('missing source variables/hard clauses/soft costs')
    return dict(status='verified',feasibility_equivalent=True,pointwise_violation_cost_equal=True,
        variables=declared,source_clauses=source.clauses,source_hard=source.hard,source_soft=source.soft,
        unique_hard_clauses=len(hard),soft_clause_occurrences=sum(soft.values()),target_assertions=assertions,
        source_sha256=source.digest.hexdigest(),target_sha256=target.digest.hexdigest(),solver_queries=0,
        method='complete canonical hard-clause set and exact weighted soft multiset; exact AMO expansion')
