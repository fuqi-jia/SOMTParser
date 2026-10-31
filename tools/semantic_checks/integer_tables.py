"""Exact decision DAGs for integer tables in independent source interpreters.

Plans contain literal interval unions and column numbers only. Each use binds
its own scope; no target formula or frontend-private identity is consulted.
"""
import z3


def _member(value, ranges):
    return z3.Or(*[value == lo if lo == hi else z3.And(value >= lo, value <= hi)
                   for lo, hi in ranges])


def plan_integer_table(width,rows):
    """Exact column decision DAG, independent of variables and target output.

    A branch label is an integer interval union, or None for a wildcard.
    Overlapping labels remain disjunctive; no partition/disjointness assumption
    is made. Only labels with the *same complete suffix* can be unioned.
    """
    if type(width) is not int or width < 0:
        raise ValueError('table width must be a nonnegative integer')
    for row in rows:
        if len(row) != width:
            raise ValueError('table tuple width')
    if width>64:
        # Keep the previous flat encoding for wide tuples, rather than making
        # later Z3 consumers traverse a new conjunction chain of that width.
        return ('flat',tuple(rows))
    trie={}
    for row in rows:
        if any(label==() for label in row):continue
        branch=trie
        for label in row:branch=branch.setdefault(label,{})
    if width==0:return ('constant',bool(rows))
    if not trie:return ('constant',False)
    nodes=[None,None];interned={};finished={};stack=[(trie,0,False)]
    while stack:
        branch,column,ready=stack.pop()
        if column==width:finished[id(branch)]=1;continue
        if not ready:
            stack.append((branch,column,True))
            stack.extend((child,column+1,False) for child in branch.values())
            continue
        by_suffix={}
        for label,child in branch.items():
            by_suffix.setdefault(finished[id(child)],[]).append(label)
        branches=[]
        for suffix,labels in sorted(by_suffix.items()):
            if None in labels:union=None
            else:
                merged=[]
                for lo,hi in sorted(interval for label in labels for interval in label):
                    if merged and lo<=merged[-1][1]+1:merged[-1]=(merged[-1][0],max(hi,merged[-1][1]))
                    else:merged.append((lo,hi))
                union=tuple(merged)
            branches.append((union,suffix))
        # Python dict hashes are only an index: complete immutable tuple
        # equality includes column, every interval endpoint and child identity.
        key=(column,tuple(branches))
        if len(branches)==1 and branches[0][0] is None:
            node=branches[0][1]
        elif key in interned:node=interned[key]
        else:
            node=len(nodes);nodes.append(key);interned[key]=node
        finished[id(branch)]=node
    return ('dag',tuple(nodes),finished[id(trie)])

def integer_table_relation(xs,plan):
    """Instantiate a closed table plan with this occurrence's full scope."""
    if plan[0]=='constant':return z3.BoolVal(plan[1])
    if plan[0]=='flat':
        return z3.Or(*[z3.And(*[_member(x,label) for x,label in zip(xs,row) if label is not None]) for row in plan[1]])
    values=[z3.BoolVal(False),z3.BoolVal(True)]
    for column,branches in plan[1][2:]:
        alternatives=[]
        for label,suffix in branches:
            if label is None:alternative=values[suffix]
            else:
                predicate=_member(xs[column],label)
                alternative=predicate if suffix==1 else z3.And(predicate,values[suffix])
            alternatives.append(alternative)
        values.append(alternatives[0] if len(alternatives)==1 else z3.Or(*alternatives))
    return values[plan[2]]
