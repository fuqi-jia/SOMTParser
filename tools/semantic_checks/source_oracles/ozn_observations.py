"""Read exact public-coordinate bindings from official MiniZinc OZN output.

Only expressions needed by explicitly annotated source decisions are evaluated.
Unknown syntax is rejected, never replaced by an invented coordinate or value.
OZN is an output program, not an additional feasibility constraint.
"""
from dataclasses import dataclass
from itertools import product
import re
import z3
from .fzn_json_source import Unsupported,need

TOKEN=re.compile(r'''\s+|%[^\n]*|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|[A-Za-z_][A-Za-z_0-9]*|[0-9]+(?:\.(?!\.)[0-9]+)?(?:[eE][+-]?[0-9]+)?|\.\.|::|<=|>=|!=|==|/\\|\\/|\+\+|[^\s]''')
def lex(text):
    return [m.group() for m in TOKEN.finditer(text) if not m.group().isspace() and not m.group().startswith('%')]
def split(tokens,delimiter):
    result=[];start=0;depth=0
    for i,t in enumerate(tokens):
        if t in ['(','[','{']:depth+=1
        elif t in [')',']','}']:depth-=1
        elif depth==0 and t==delimiter:result.append(tokens[start:i]);start=i+1
        need(depth>=0,'unbalanced OZN delimiter')
    need(depth==0,'unbalanced OZN delimiter');result.append(tokens[start:]);return result
def const_int(v):
    if type(v) is int:return v
    if z3.is_int(v):v=z3.simplify(v)
    if z3.is_int_value(v):return v.as_long()
    raise Unsupported('nonconstant OZN index')
# Absence is produced only by an exact, constant out-of-range read. It may
# be consumed by an explicit OZN default; it is never a guessed value.
ABSENT=object()

@dataclass
class Array:
    dimensions:tuple
    items:list
    def __post_init__(self):
        count=1
        for d in self.dimensions:count*=len(d)
        need(count==len(self.items),'OZN array extent mismatch')
    def at(self,indices,bounds=None):
        need(len(indices)==len(self.dimensions),'OZN array index rank');choices=[]
        for d,i in zip(self.dimensions,indices):
            try:
                value=const_int(i)
                if value not in d:return ABSENT
                choices.append((value,));continue
            except Unsupported:
                interval=bounds(i) if bounds is not None else None
            need(interval is not None,'nonconstant OZN index has no proved source domain')
            lo,hi=interval;values=tuple(v for v in d if lo<=v<=hi)
            need(hi>=lo and len(values)==hi-lo+1,'OZN dynamic index not proved inside explicit extent')
            choices.append(values)
        values=[]
        for coordinates in product(*choices):
            offset=0
            for d,i in zip(self.dimensions,coordinates):offset=offset*len(d)+d.index(i)
            values.append((coordinates,self.items[offset]))
        need(bool(values),'empty OZN dynamic lookup')
        result=values[-1][1]
        # The source domains prove that one enumerated coordinate is selected.
        # The final branch is therefore exhaustive, not a new default value.
        for coordinates,value in reversed(values[:-1]):
            conditions=[i==v for i,v in zip(indices,coordinates)]
            need(isinstance(value,z3.ExprRef) and isinstance(result,z3.ExprRef) and value.sort().eq(result.sort()),'OZN dynamic lookup value sort')
            result=z3.If(z3.And(*conditions),value,result)
        return result

class Record:
    """Evaluate only fields used by an explicitly requested observation.

    As with top-level output declarations, unused display fields and their
    expressions do not contribute to the public-coordinate relation.
    """
    def __init__(self,fields,env):
        self.fields=fields;self.env=dict(env);self.kinds=None;self.cache={};self.active=set()
    def field(self,name,program):
        need(name in self.fields,'unknown OZN record field '+name)
        if name in self.cache:return self.cache[name]
        need(name not in self.active,'cyclic OZN record field '+name);self.active.add(name)
        try:
            value=program.expression(self.fields[name],self.env)
            if self.kinds is not None:program.check_kind(value,self.kinds[name])
            self.cache[name]=value;return value
        finally:self.active.remove(name)

def record_fields(tokens,*,declaration=False):
    fields={}
    for entry in split(tokens,','):
        parts=split(entry,':');need(len(parts)==2,'OZN record field declaration')
        name_tokens,value=(parts[1],parts[0]) if declaration else parts
        need(len(name_tokens)==1 and re.fullmatch(r'[A-Za-z_]\w*',name_tokens[0]) is not None,'OZN record field name')
        name=name_tokens[0];need(name not in fields and bool(value),'duplicate or empty OZN record field '+name)
        fields[name]=value
    return fields

class Program:
    def __init__(self,text,flat):
        self.flat=flat;self._index_domain_constraints=None;self.declarations={};self.cache={};self.active=set();self.functions={};self.active_functions=set()
        for statement in split(lex(text),';'):
            if not statement:continue
            if statement[0]=='function':
                # Store unused display/string overloads without interpreting
                # them. A called function must have one supported definition.
                colon=statement.index(':');name=statement[colon+1]
                self.functions.setdefault(name,[]).append(statement)
                continue
            if statement[0] in ['output','predicate','annotation','include']:continue
            chunks=split(statement,':')
            need(len(chunks)==2,'unsupported OZN declaration')
            head,tail=chunks;need(bool(tail),'OZN declaration name');name=tail[0]
            need(name not in self.declarations,'duplicate OZN declaration')
            rest=tail[1:];rhs=None
            if rest:
                need(rest[0]=='=','OZN declaration annotation unsupported');rhs=rest[1:]
            self.declarations[name]=(head,rhs)
    def expression(self,tokens,env=None):
        parser=Expression(self,tokens,env or {});value=parser.parse();need(parser.i==len(tokens),'unsupported OZN expression tail '+repr(tokens[parser.i:parser.i+8]));return value
    def source_index_domains(self):
        """Intersect unconditional original Int bounds; never inspect a branch.

        Compiler element constraints can narrow an index beyond its declared
        domain. Their explicit guards already belong to the full flat relation,
        which is retained when the observations are projected. A bound under OR,
        implication, reification or a binder is not an unconditional premise.
        """
        if self._index_domain_constraints is not None:
            return self._index_domain_constraints
        bounds={};todo=list(getattr(self.flat,'constraints',()))
        reverse={z3.Z3_OP_LE:z3.Z3_OP_GE,z3.Z3_OP_LT:z3.Z3_OP_GT,
                 z3.Z3_OP_GE:z3.Z3_OP_LE,z3.Z3_OP_GT:z3.Z3_OP_LT,
                 z3.Z3_OP_EQ:z3.Z3_OP_EQ}
        while todo:
            atom=todo.pop()
            if z3.is_and(atom) or (z3.is_or(atom) and atom.num_args()==1):
                todo.extend(atom.children());continue
            if not z3.is_app(atom) or atom.decl().kind() not in reverse or atom.num_args()!=2:
                continue
            left,right=atom.children();kind=atom.decl().kind()
            if not z3.is_int(left) or not z3.is_int(right):continue
            left,right=z3.simplify(left),z3.simplify(right)
            if z3.is_int_value(left):left,right=right,left;kind=reverse[kind]
            if not (z3.is_const(left) and left.decl().kind()==z3.Z3_OP_UNINTERPRETED
                    and z3.is_int_value(right)):continue
            number=right.as_long();lo,hi=bounds.get(left.get_id(),(None,None))
            lower=number+(kind==z3.Z3_OP_GT) if kind in (z3.Z3_OP_GE,z3.Z3_OP_GT,z3.Z3_OP_EQ) else None
            upper=number-(kind==z3.Z3_OP_LT) if kind in (z3.Z3_OP_LE,z3.Z3_OP_LT,z3.Z3_OP_EQ) else None
            if lower is not None:lo=lower if lo is None else max(lo,lower)
            if upper is not None:hi=upper if hi is None else min(hi,upper)
            bounds[left.get_id()]=(lo,hi)
        self._index_domain_constraints=bounds
        return bounds
    def index_bounds(self,value):
        """Sound interval from original flat domains and unconditional guards."""
        if type(value)is int:return (value,value)
        if not z3.is_int(value):return None
        value=z3.simplify(value)
        if z3.is_int_value(value):return (value.as_long(),value.as_long())
        domain=getattr(self.flat,'integer_domains',{}).get(value.get_id())
        lo,hi=(min(a for a,b in domain),max(b for a,b in domain)) if domain else (None,None)
        guard_lo,guard_hi=self.source_index_domains().get(value.get_id(),(None,None))
        if guard_lo is not None:lo=guard_lo if lo is None else max(lo,guard_lo)
        if guard_hi is not None:hi=guard_hi if hi is None else min(hi,guard_hi)
        if lo is not None and hi is not None:return lo,hi
        if not z3.is_app(value):return None
        if value.decl().kind()==z3.Z3_OP_ITE:
            yes,no=[self.index_bounds(value.arg(i)) for i in (1,2)]
            return None if yes is None or no is None else (min(yes[0],no[0]),max(yes[1],no[1]))
        children=[self.index_bounds(x) for x in value.children()]
        if any(x is None for x in children):return None
        kind=value.decl().kind()
        if kind==z3.Z3_OP_ADD:return sum(x[0] for x in children),sum(x[1] for x in children)
        if kind==z3.Z3_OP_UMINUS and len(children)==1:return -children[0][1],-children[0][0]
        if kind==z3.Z3_OP_SUB and len(children)==2:return children[0][0]-children[1][1],children[0][1]-children[1][0]
        if kind==z3.Z3_OP_MUL:
            lo,hi=1,1
            for a,b in children:lo,hi=min(lo*a,lo*b,hi*a,hi*b),max(lo*a,lo*b,hi*a,hi*b)
            return lo,hi
        return None
    def name(self,name,env):
        if name in env:return z3.IntVal(env[name]) if type(env[name]) is int else env[name]
        if name=='true':return z3.BoolVal(True)
        if name=='false':return z3.BoolVal(False)
        if name in self.cache:return self.cache[name]
        need(name in self.declarations,'OZN name lacks explicit declaration '+name)
        need(name not in self.active,'cyclic OZN output alias');self.active.add(name)
        try:
            head,rhs=self.declarations[name]
            if head[0]=='array':
                need(head[1]=='[', 'OZN array declaration');end=head.index(']');need(head[end+1]=='of','OZN array element declaration')
                kind=head[end+2:];dimension_tokens=split(head[2:end],',')
                value=self.expression(rhs,{}) if rhs is not None else self.flat.arrays.get(name)
                need(value is not None,'uninitialized OZN array absent from exact flat map '+name)
                values=value.items if isinstance(value,Array) else value
                need(isinstance(values,list),'OZN array initializer')
                dimensions=[]
                for i,t in enumerate(dimension_tokens):
                    if t==['int']:
                        need(len(dimension_tokens)==1,'unresolved multidimensional extent');d=tuple(range(1,len(values)+1))
                    else:d=tuple(sorted(self.constant_set(self.expression(t,{}))))
                    dimensions.append(d)
                if isinstance(value,Array) and all(t!=['int'] for t in dimension_tokens):need(value.dimensions==tuple(dimensions),'OZN reshape declared extent mismatch')
                value=Array(tuple(dimensions),values)
                for v in values:self.check_kind(v,kind)
            else:
                value=self.expression(rhs,{}) if rhs is not None else self.flat.variables.get(name)
                need(value is not None,'uninitialized OZN scalar absent from exact flat map '+name);self.check_kind(value,head)
            self.cache[name]=value;return value
        finally:self.active.remove(name)
    @staticmethod
    def constant_set(value):
        need(isinstance(value,frozenset),'OZN index set is not a constant integer set');return value
    def check_kind(self,value,kind):
        need(value is not ABSENT,'OZN index outside explicit extent without default')
        if kind==['int']:need(z3.is_int(value) or type(value)is int,'OZN Int sort')
        elif kind==['float']:need(z3.is_real(value),'OZN Real sort')
        elif kind==['bool']:need(z3.is_bool(value),'OZN Bool sort')
        elif kind==['set','of','int']:need(isinstance(value,frozenset) or isinstance(value,z3.ExprRef) and value.sort().eq(z3.SetSort(z3.IntSort())),'OZN Set sort')
        elif kind[:2]==['record','('] and kind[-1:]==[')']:
            need(isinstance(value,Record),'OZN Record sort');kinds=record_fields(kind[2:-1],declaration=True)
            need(set(kinds)==set(value.fields),'OZN record fields differ from declaration')
            need(value.kinds is None or value.kinds==kinds,'conflicting OZN record field types')
            value.kinds=kinds
            for name,cached in value.cache.items():self.check_kind(cached,kinds[name])
        elif len(kind)==1 and kind[0] in self.declarations:
            # Named integer subtypes occur in function results as well as
            # parameters. Establish membership from existing source bounds;
            # never add an assumption to make an output expression typecheck.
            need(z3.is_int(value) or type(value)is int,'OZN named domain Int sort')
            domain=self.constant_set(self.name(kind[0],{}));interval=self.index_bounds(value)
            need(interval is not None and len([i for i in domain if interval[0]<=i<=interval[1]])==interval[1]-interval[0]+1,'OZN named domain not established')
        else:raise Unsupported('OZN type '+repr(kind))
    def observations(self,names):
        need(len(names)==len(set(names)),'duplicate source observation name');out=[]
        for name in names:
            value=self.name(name,{})
            if isinstance(value,Array):
                for coords,v in zip(product(*value.dimensions),value.items):out.append(dict(name=name,indices=coords,value=v,dimensions=value.dimensions))
            else:out.append(dict(name=name,indices=None,value=value,dimensions=None))
        return out

class Expression:
    PRECEDENCE={'\\/':10,'/\\':20,'<':30,'<=':30,'>':30,'>=':30,'=':40,'==':40,'!=':40,'in':50,'..':80,'+':90,'-':90,'*':100,'div':100,'mod':100,'++':120,'default':130}
    def __init__(self,program,tokens,env):self.p=program;self.t=tokens;self.i=0;self.env=env
    def take(self,expected=None):
        need(self.i<len(self.t),'truncated OZN expression');v=self.t[self.i];self.i+=1
        if expected is not None:need(v==expected,'expected OZN token '+expected)
        return v
    def section(self,closing):
        start=self.i;depth=0
        while self.i<len(self.t):
            t=self.t[self.i]
            if depth==0 and t==closing:out=self.t[start:self.i];self.i+=1;return out
            if t in ['(','[','{']:depth+=1
            elif t in [')',']','}']:depth-=1
            self.i+=1
        raise Unsupported('unterminated OZN grouping')
    def parse(self,minimum=0):
        t=self.take()
        if t=='-':
            operand=self.parse(105);v=ABSENT if operand is ABSENT else -operand
        elif t=='+':v=self.parse(105)
        elif t=='not':
            operand=self.parse(105);need(z3.is_bool(operand),'OZN not operand sort');v=z3.Not(operand)
        elif t=='if':v=self.conditional()
        elif t=='(':
            body=self.section(')')
            v=Record(record_fields(body),self.env) if len(split(body,':'))>1 else self.p.expression(body,self.env)
        elif t=='[':
            body=self.section(']');chunks=split(body,'|')
            if len(chunks)>=3 and not chunks[0] and not chunks[-1]:
                rows=[[self.p.expression(x,self.env) for x in split(row,',')] for row in chunks[1:-1]]
                need(rows and rows[0] and all(len(row)==len(rows[0]) for row in rows),'OZN matrix literal row widths')
                v=Array((tuple(range(1,len(rows)+1)),tuple(range(1,len(rows[0])+1))),[x for row in rows for x in row])
            else:
                if len(chunks)==1:values=[] if not body else [self.p.expression(x,self.env) for x in split(body,',')]
                else:
                    need(len(chunks)==2,'OZN comprehension shape');values=self.comprehension(*chunks)
                v=values if isinstance(values,Array) else Array((tuple(range(1,len(values)+1)),),values)
        elif t=='{':
            body=self.section('}');v=frozenset() if not body else frozenset(const_int(self.p.expression(x,self.env)) for x in split(body,','))
        elif re.fullmatch(r'[0-9]+',t):v=z3.IntVal(t)
        elif re.fullmatch(r'[0-9]+(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?',t):v=z3.RealVal(t)
        elif self.i<len(self.t) and self.t[self.i]=='(':
            self.i+=1;body=self.section(')');args=[] if not body else [self.p.expression(x,self.env) for x in split(body,',')];v=self.call(t,args)
        else:v=self.p.name(t,self.env)
        while self.i<len(self.t):
            op=self.t[self.i]
            if op=='.':
                self.i+=1;field=self.take();need(v is ABSENT or isinstance(v,Record),'OZN field selection on nonrecord')
                v=ABSENT if v is ABSENT else v.field(field,self.p);continue
            if op=='[':
                self.i+=1;indices=[self.p.expression(x,self.env) for x in split(self.section(']'),',')];need(v is ABSENT or isinstance(v,Array),'OZN index on nonarray');v=ABSENT if v is ABSENT else v.at(indices,self.p.index_bounds);continue
            precedence=self.PRECEDENCE.get(op,-1)
            if precedence<minimum:break
            self.i+=1;rhs=self.parse(precedence if op=='++' else precedence+1)
            if op=='default':v=rhs if v is ABSENT else v
            elif v is ABSENT or rhs is ABSENT:v=ABSENT
            elif op=='in':
                need(z3.is_int(v),'OZN membership value sort')
                if isinstance(rhs,frozenset):v=z3.Or(*[v==i for i in sorted(rhs)])
                else:
                    need(isinstance(rhs,z3.ExprRef) and rhs.sort().eq(z3.SetSort(z3.IntSort())),'OZN membership set sort');v=z3.IsMember(v,rhs)
            elif op=='..':v=frozenset(range(const_int(v),const_int(rhs)+1))
            elif op=='++':need(isinstance(v,Array) and isinstance(rhs,Array),'OZN concat sort');values=v.items+rhs.items;v=Array((tuple(range(1,len(values)+1)),),values)
            elif op in ['div','mod']:
                need(z3.is_int(v) and z3.is_int(rhs),'OZN integer division sort');divisor=const_int(rhs)
                need(divisor!=0,'OZN division by zero')
                q=z3.If(v>=0,v/abs(divisor),-((-v)/abs(divisor)))
                if divisor<0:q=-q
                v=q if op=='div' else v-q*divisor
            else:v={'+':lambda:v+rhs,'-':lambda:v-rhs,'*':lambda:v*rhs,'=':lambda:v==rhs,'==':lambda:v==rhs,'!=':lambda:v!=rhs,'<':lambda:v<rhs,'<=':lambda:v<=rhs,'>':lambda:v>rhs,'>=':lambda:v>=rhs,'/\\':lambda:z3.And(v,rhs),'\\/':lambda:z3.Or(v,rhs)}[op]()
        return v
    def conditional(self):
        condition=self.parse();need(z3.is_bool(condition),'OZN if condition sort');self.take('then');yes=self.parse()
        if self.i<len(self.t) and self.t[self.i]=='elseif':
            self.i+=1;no=self.conditional()
        else:
            self.take('else');no=self.parse();self.take('endif')
        constant=z3.simplify(condition)
        if z3.is_true(constant):return yes
        if z3.is_false(constant):return no
        need(yes is not ABSENT and no is not ABSENT,'OZN conditional partial read needs a proved guard')
        need(isinstance(yes,z3.ExprRef) and isinstance(no,z3.ExprRef) and yes.sort().eq(no.sort()),'OZN if branch sort')
        return z3.If(condition,yes,no)
    def comprehension(self,body,generators):
        parts=split(generators,'where');need(len(parts)<=2,'multiple OZN where clauses');clauses=split(parts[0],',');groups=[];names=[]
        for clause in clauses:
            if 'in' not in clause:names.extend(clause);continue
            index=clause.index('in');names.extend(clause[:index]);need(all(re.fullmatch(r'[A-Za-z_]\w*',n) for n in names),'OZN binder name');groups.append((names,clause[index+1:]));names=[]
        need(not names,'OZN binder lacks domain');values=[];indexed=split(body,':');need(len(indexed)<=2,'OZN indexed comprehension body')
        coordinates=[]
        def walk(i,env):
            if i==len(groups):
                if len(parts)==2:
                    condition=z3.simplify(self.p.expression(parts[1],env));need(z3.is_true(condition) or z3.is_false(condition),'nonconstant OZN filter')
                    if z3.is_false(condition):return
                if len(indexed)==2:
                    index_tokens=indexed[0]
                    if index_tokens[:1]==['('] and index_tokens[-1:]==[')']:index_tokens=index_tokens[1:-1]
                    coordinates.append(tuple(const_int(self.p.expression(t,env)) for t in split(index_tokens,',')))
                    values.append(self.p.expression(indexed[1],env))
                else:values.append(self.p.expression(body,env))
                return
            names,domain=groups[i];domain=self.p.expression(domain,env)
            entries=domain.items if isinstance(domain,Array) else sorted(self.p.constant_set(domain))
            for tuple_values in product(entries,repeat=len(names)):walk(i+1,dict(env,**dict(zip(names,tuple_values))))
        walk(0,self.env)
        if len(indexed)==2:
            need(coordinates and coordinates[0] and len({len(x) for x in coordinates})==1,'OZN indexed comprehension rank')
            need(len(set(coordinates))==len(coordinates),'duplicate OZN indexed comprehension coordinate')
            dimensions=tuple(tuple(sorted({c[i] for c in coordinates})) for i in range(len(coordinates[0])))
            mapping=dict(zip(coordinates,values));ordered=list(product(*dimensions));need(set(ordered)==set(coordinates),'incomplete Cartesian OZN indexed comprehension')
            return Array(dimensions,[mapping[c] for c in ordered])
        return values
    def call(self,name,args):
        if name in self.p.functions:
            definitions=self.p.functions[name];need(len(definitions)==1,'overloaded OZN function '+name)
            need(name not in self.p.active_functions,'recursive OZN function '+name)
            tokens=definitions[0];colon=tokens.index(':');need(tokens[colon+2]=='(','OZN function parameter list')
            depth=0;end=None
            for i in range(colon+2,len(tokens)):
                if tokens[i]=='(':depth+=1
                elif tokens[i]==')':
                    depth-=1
                    if depth==0:end=i;break
            need(end is not None and tokens[end+1:end+2]==['='],'OZN function body')
            parameters=split(tokens[colon+3:end],',') if tokens[colon+3:end] else []
            need(len(parameters)==len(args),'OZN function arity');bindings={}
            for parameter,value in zip(parameters,args):
                fields=split(parameter,':');need(len(fields)==2 and len(fields[1])==1,'OZN scalar parameter declaration');kind,identifier=fields[0],fields[1][0]
                need(identifier not in bindings,'duplicate OZN function parameter')
                if len(kind)==1 and kind[0] in self.p.declarations:
                    domain=self.p.constant_set(self.p.name(kind[0],{}));interval=self.p.index_bounds(value)
                    need(interval is not None and len([i for i in domain if interval[0]<=i<=interval[1]])==interval[1]-interval[0]+1,'OZN function argument domain not established')
                else:self.p.check_kind(value,kind)
                bindings[identifier]=value
            self.p.active_functions.add(name)
            try:
                value=self.p.expression(tokens[end+2:],bindings);self.p.check_kind(value,tokens[1:colon]);return value
            finally:self.p.active_functions.remove(name)
        if re.fullmatch(r'array[1-6]d',name):
            n=int(name[5]);need(len(args)==n+1 and isinstance(args[-1],Array),'OZN arrayNd arguments');dims=tuple(tuple(sorted(self.p.constant_set(v))) for v in args[:-1]);return Array(dims,args[-1].items)
        if name=='index_set':need(len(args)==1 and isinstance(args[0],Array) and len(args[0].dimensions)==1,'OZN index_set rank');return frozenset(args[0].dimensions[0])
        match=re.fullmatch(r'index_set_([1-6])of([1-6])',name)
        if match:
            i,n=map(int,match.groups());need(len(args)==1 and isinstance(args[0],Array) and len(args[0].dimensions)==n and i<=n,'OZN index_set dimension');return frozenset(args[0].dimensions[i-1])
        if name in ['sum','min','max']:
            if name in ['min','max'] and len(args)==2:
                a,b=args;need(z3.is_arith(a) and z3.is_arith(b) and a.sort().eq(b.sort()),'OZN scalar extremum sort');return z3.If(a<=b if name=='min' else a>=b,a,b)
            if name in ['min','max'] and len(args)==1 and isinstance(args[0],frozenset):
                values=args[0];need(bool(values),'empty OZN extremum')
                need(all(type(v)is int for v in values),'OZN set extremum sort')
                return z3.IntVal(min(values) if name=='min' else max(values))
            need(len(args)==1 and isinstance(args[0],Array),'OZN aggregate');values=args[0].items
            if name=='sum':return z3.Sum(*values)
            need(bool(values),'empty OZN extremum');v=values[0]
            for x in values[1:]:v=z3.If(v<=x if name=='min' else v>=x,v,x)
            return v
        if name=='enum2int':
            need(len(args)==1,'OZN enum2int arity');value=args[0]
            # FlatZinc/OZN already carries the enum's integer representation.
            # This coercion preserves it, including array extents and set
            # membership. Original enum domains stay in the flat relation;
            # no new positivity, contiguity or default-value assumption is made.
            values=value.items if isinstance(value,Array) else [value];kinds=set()
            for item in values:
                if type(item)is int or z3.is_int(item):kinds.add('int')
                elif isinstance(item,frozenset) and all(type(v)is int for v in item):kinds.add('set')
                elif isinstance(item,z3.ExprRef) and item.sort().eq(z3.SetSort(z3.IntSort())):kinds.add('set')
                else:raise Unsupported('OZN enum2int requires present integer or integer-set representation')
            need(len(kinds)<=1,'OZN enum2int heterogeneous array');return value
        if name=='bool2int':need(len(args)==1 and z3.is_bool(args[0]),'OZN bool2int');return z3.If(args[0],1,0)
        if name=='abs':need(len(args)==1 and z3.is_arith(args[0]),'OZN abs');return z3.If(args[0]>=0,args[0],-args[0])
        if name=='arg_max':
            need(len(args)==1 and isinstance(args[0],Array) and len(args[0].dimensions)==1 and args[0].items,'OZN arg_max array')
            xs=args[0].items;need(all(z3.is_arith(x) for x in xs),'OZN arg_max numeric values');indices=args[0].dimensions[0]
            index=z3.IntVal(indices[0]);best=xs[0]
            for i,value in zip(indices[1:],xs[1:]):index=z3.If(value>best,i,index);best=z3.If(value>best,value,best)
            return index
        if name=='to_enum':
            need(len(args)==2,'OZN to_enum arity');domain=self.p.constant_set(args[0]);interval=self.p.index_bounds(args[1])
            need(interval is not None and len([i for i in domain if interval[0]<=i<=interval[1]])==interval[1]-interval[0]+1,'OZN enum value domain not established');return args[1]
        if name=='card':
            need(len(args)==1,'OZN card arity');value=args[0]
            if isinstance(value,frozenset):return z3.IntVal(len(value))
            need(value.sort().eq(z3.SetSort(z3.IntSort())),'OZN card type');return z3.Sum(*[z3.If(z3.IsMember(z3.IntVal(i),value),1,0) for i in self.p.flat.universe])
        raise Unsupported('OZN function '+name)
