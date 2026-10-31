"""Independent FlatZinc JSON semantics for the official MiniZinc compiler.

This reader does not infer source coordinates from introduced names. A caller
must provide an explicit, separately justified observation map. Domains and
all defining constraints remain in the projected relation; annotations are
implementation hints, never permissions to drop a constraint.
"""
from dataclasses import dataclass,field
from decimal import Decimal
import json
import z3
from ..integer_tables import plan_integer_table, integer_table_relation
from ..functional_integer_tables import functional_integer_table_relation
from ..observed_constants import project_observed_constants
from ..finite_scalar_tables import normalize_finite_scalar_tables

class Unsupported(ValueError):pass

def need(value,message):
    if not value:raise Unsupported(message)

def fields(obj,allowed):need(isinstance(obj,dict) and set(obj)<=set(allowed),'unknown JSON semantic field')
def is_int(v):return type(v) is int

def ranges(raw,integer=True):
    need(isinstance(raw,list),'domain must be ranges');out=[]
    for row in raw:
        need(isinstance(row,list) and len(row)==2,'domain interval shape')
        a,b=row;need((is_int(a) and is_int(b)) if integer else type(a) in [int,Decimal] and type(b) in [int,Decimal],'domain endpoint sort');need(a<=b,'reversed domain');out.append((a,b))
    return out

def in_ranges(x,domain):return z3.Or(*[x==a if a==b else z3.And(x>=a,x<=b) for a,b in domain])
def finite_set(domain):
    out=z3.EmptySet(z3.IntSort())
    for a,b in domain:
        for i in range(a,b+1):out=z3.SetAdd(out,z3.IntVal(i))
    return out

def real(value):return z3.RealVal(str(value))

@dataclass
class Source:
    variables:dict
    arrays:dict
    constraints:list
    objective:object
    method:str
    universe:tuple
    integer_domains:dict=field(default_factory=dict)
    finite_set_domains:dict=field(default_factory=dict)
    @property
    def relation(self):return z3.And(*self.constraints)
    def projected(self,observations,*,signed_cost=None):
        """Existentially close all flat variables, retaining complete relation.

        observations is an explicit [(public term, flat term)] mapping. It can
        include source aliases and scalar coordinates of arrays. No statement
        about completeness of source-coordinate coverage is inferred here.
        """
        equalities=[]
        public=[]
        # Z3 interns ASTs within a context. Keep the variables/public terms
        # alive and compare their exact context-local IDs instead of scanning
        # every private variable for every public coordinate.
        identity=lambda term:(term.ctx_ref().value,term.get_id())
        private=list(self.variables.values())
        private_identities={identity(term) for term in private}
        public_identities=set()
        observed_sets={}
        for left,right in observations:
            need(z3.is_const(left) and left.num_args()==0,'public observation must be scalar constant')
            need(left.sort().eq(right.sort()),'observation sort mismatch')
            key=identity(left);need(key not in public_identities,'duplicate public observation')
            public_identities.add(key);public.append(left);equalities.append(left==right)
            if (identity(right) in private_identities
                    and self.finite_set_domains.get(right.get_id()) is not None):
                observed_sets.setdefault(identity(right),left)
        if signed_cost is not None:
            need(z3.is_const(signed_cost) and identity(signed_cost) not in private_identities and identity(signed_cost) not in public_identities,'cost coordinate must be fresh')
            need(self.method in ['minimize','maximize'],'satisfaction has no cost')
            need(signed_cost.sort().eq(self.objective.sort()),'cost coordinate sort')
            equalities.append(signed_cost==(self.objective if self.method=='minimize' else -self.objective))
        need(not public_identities.intersection(private_identities),'public and private identities overlap')
        body=z3.And(self.relation,*equalities)
        replacements=[]
        replaced_identities=set()
        member_variables=[]
        observed_carriers=[]
        for variable in self.variables.values():
            carrier=self.finite_set_domains.get(variable.get_id())
            if carrier is None:continue
            observed=observed_sets.get(identity(variable))
            if observed is not None:
                # The unconditional observation equality already identifies
                # this entire set with a public coordinate. Substitute that
                # coordinate directly instead of introducing Boolean witnesses
                # merely to reconstruct the same set. Every original carrier,
                # alias, relation, and objective constraint remains in body.
                replacements.append((variable,observed))
                replaced_identities.add(identity(variable))
                domain=z3.EmptySet(z3.IntSort(ctx=variable.ctx))
                for element in carrier:
                    domain=z3.SetAdd(domain,z3.IntVal(element,ctx=variable.ctx))
                # Source can also be constructed directly, with the complete
                # carrier supplied only as metadata. The old Boolean witness
                # parameterization enforces that carrier even in that case.
                observed_carriers.append(z3.IsSubset(observed,domain))
                continue
            # Every original set is constrained to this explicit finite carrier.
            # A Boolean per member parameterizes exactly all its subsets. Retain
            # every original constraint and observation after substitution,
            # including the carrier constraint; never infer a smaller carrier
            # from a current solution, objective, or a partial observation map.
            value=z3.EmptySet(z3.IntSort(ctx=variable.ctx))
            members=[]
            for element in carrier:
                member=z3.FreshConst(z3.BoolSort(ctx=variable.ctx),'fzn_set_member')
                members.append(member)
                value=z3.Store(value,z3.IntVal(element,ctx=variable.ctx),member)
            replacements.append((variable,value))
            replaced_identities.add(identity(variable))
            member_variables.extend(members)
        if replacements:
            # Remove all finite-set witnesses in one pass. Rebuilding this
            # list after each set also rescanned every previously added member.
            # Keep original remaining order, followed by members in set/carrier
            # order, exactly as the successive removals and appends did.
            private=[term for term in private
                     if identity(term) not in replaced_identities]+member_variables
            body=z3.substitute(body,*replacements)
            if observed_carriers:body=z3.And(body,*observed_carriers)
        projected=project_observed_constants(body,private,public)
        # Normalize literal lookup tables before adding this existential binder.
        # The normalizer preserves every integer index, including the default
        # outside stored keys, and deliberately leaves existing binders intact.
        body=normalize_finite_scalar_tables(projected.body).formula
        return z3.Exists(projected.private_variables,body) if projected.private_variables else body

def element_relation(index, offset, values, result):
    """Complete finite element relation, with an explicit index guard."""
    if not values:
        return z3.BoolVal(False, ctx=index.ctx)

    def lookup(begin, end):
        if end - begin == 1:
            return values[begin]
        middle = (begin + end) // 2
        return z3.If(index < offset + middle, lookup(begin, middle),
                     lookup(middle, end))

    return z3.And(index >= offset, index < offset + len(values),
                  result == lookup(0, len(values)))


class Reader:
    def __init__(self, *, table_encoding='auto'):
        need(table_encoding in ['auto','decision-dag'],'unknown integer table encoding')
        self.table_encoding=table_encoding
        self.variables={};self.arrays={};self.constraints=[];self.universe=set();self.int_domains={};self.integer_literals={};self.set_domains={}
        self.index_intervals={}
    def value(self,item):
        if type(item) is bool:return z3.BoolVal(item)
        if type(item) is int:
            # Large literal tables repeat the same exact integers many times.
            # Reuse immutable Z3 numerals within this reader; keep bool/real
            # dispatch separate so Python's equal numeric keys cannot mix sorts.
            value=self.integer_literals.get(item)
            if value is None:
                value=z3.IntVal(item);self.integer_literals[item]=value
            return value
        if isinstance(item,Decimal):return real(item)
        if isinstance(item,list):return [self.value(v) for v in item]
        if isinstance(item,str):
            need(item in self.variables or item in self.arrays,'unknown FlatZinc identifier '+item)
            return self.variables[item] if item in self.variables else self.arrays[item]
        if isinstance(item,dict) and set(item)=={'set'}:
            domain=ranges(item['set']);self.universe.update(i for a,b in domain for i in range(a,b+1));return finite_set(domain)
        raise Unsupported('unsupported FlatZinc literal '+repr(item)[:80])
    @staticmethod
    def arity(args,n):need(len(args)==n,'constraint arity')
    @staticmethod
    def arithmetic(v):need(z3.is_arith(v),'expected numeric operand');return v
    @staticmethod
    def integer(v):need(z3.is_int(v),'expected Int operand');return v
    @staticmethod
    def boolean(v):need(z3.is_bool(v),'expected Bool operand');return v
    @staticmethod
    def array(v):need(isinstance(v,list),'expected array argument');return v
    def index_interval(self,value):
        """Read an entire literal MiniZinc index set, never just its bounds."""
        need(z3.is_array(value) and value.sort().domain().kind()==z3.Z3_INT_SORT
             and value.sort().range().kind()==z3.Z3_BOOL_SORT,'element2d Int index set')
        key=(value.ctx_ref().value,value.get_id())
        cached=self.index_intervals.get(key)
        if cached is not None:return cached[1]
        original=value;members={}
        while z3.is_store(value):
            index,present=value.arg(1),value.arg(2)
            need(z3.is_int_value(index) and (z3.is_true(present) or z3.is_false(present)),
                 'element2d literal index set')
            members.setdefault(index.as_long(),z3.is_true(present));value=value.arg(0)
        need(z3.is_const_array(value) and z3.is_false(value.arg(0)),
             'element2d finite literal index set')
        indices=sorted(i for i,present in members.items() if present)
        need(not indices or indices[-1]-indices[0]+1==len(indices),
             'element2d index sets must be contiguous')
        interval=(indices[0],len(indices)) if indices else (0,0)
        # Retain the source AST while its context-local identity is a cache key.
        self.index_intervals[key]=(original,interval)
        return interval
    def nonnegative(self,value):
        value=self.integer(value)
        if z3.is_int_value(value):return value.as_long()>=0
        domain=self.int_domains.get(value.get_id())
        return domain is not None and all(a>=0 for a,b in domain)
    def set_card(self,s):
        need(s.sort().eq(z3.SetSort(z3.IntSort())),'expected Int set')
        return z3.Sum(*[z3.If(z3.IsMember(z3.IntVal(i),s),1,0) for i in sorted(self.universe)])
    def predicate(self,name,a):
        if name.endswith('_reif'):
            need(bool(a),'reification arity');return self.predicate(name[:-5],a[:-1])==self.boolean(a[-1])
        if name.endswith('_imp'):
            need(bool(a),'implication arity');return z3.Implies(self.boolean(a[-1]),self.predicate(name[:-4],a[:-1]))
        if name in ['int_eq','int_ne','int_le','int_lt','float_eq','float_ne','float_le','float_lt','bool_eq','bool_ne','bool_le','bool_lt']:
            self.arity(a,2)
            if name.startswith('int_'):a=[self.integer(x) for x in a]
            elif name.startswith('float_'):a=[self.arithmetic(x) for x in a]
            else:a=[z3.If(self.boolean(x),1,0) for x in a]
            x,y=a;op=name.rsplit('_',1)[1];return {'eq':lambda:x==y,'ne':lambda:x!=y,'le':lambda:x<=y,'lt':lambda:x<y}[op]()
        if name.startswith(('int_lin_','float_lin_')):
            self.arity(a,3);cs,xs,rhs=a;self.array(cs);self.array(xs);need(len(cs)==len(xs),'linear coefficient arity')
            if name.startswith('int_'):cs=[self.integer(x) for x in cs];xs=[self.integer(x) for x in xs];rhs=self.integer(rhs)
            else:cs=[self.arithmetic(x) for x in cs];xs=[self.arithmetic(x) for x in xs];rhs=self.arithmetic(rhs)
            need(all(z3.is_int_value(x) or z3.is_rational_value(x) for x in cs),'nonconstant linear coefficient')
            lhs=z3.Sum(*[c*x for c,x in zip(cs,xs)]);op=name.rsplit('_',1)[1];need(op in ['eq','ne','le','lt'],'linear operator')
            return {'eq':lambda:lhs==rhs,'ne':lambda:lhs!=rhs,'le':lambda:lhs<=rhs,'lt':lambda:lhs<rhs}[op]()
        if name in ['int_plus','int_minus','int_times','int_min','int_max','float_plus','float_minus','float_times','float_min','float_max']:
            self.arity(a,3);a=[self.integer(x) if name.startswith('int_') else self.arithmetic(x) for x in a];x,y,r=a
            op=name.rsplit('_',1)[1];v={'plus':lambda:x+y,'minus':lambda:x-y,'times':lambda:x*y,'min':lambda:z3.If(x<=y,x,y),'max':lambda:z3.If(x>=y,x,y)}[op]();return r==v
        if name in ['int_abs','float_abs','int_negate','float_negate']:
            self.arity(a,2);x,r=a;x=self.integer(x) if name.startswith('int_') else self.arithmetic(x);return r==(-x if name.endswith('negate') else z3.If(x>=0,x,-x))
        if name in ['bool_and','bool_or','bool_xor']:
            self.arity(a,3);x,y,r=[self.boolean(x) for x in a];return r=={'bool_and':z3.And,'bool_or':z3.Or,'bool_xor':z3.Xor}[name](x,y)
        if name=='bool_not':self.arity(a,2);return self.boolean(a[1])==z3.Not(self.boolean(a[0]))
        if name=='array_bool_xor':
            self.arity(a,1);v=z3.BoolVal(False)
            for x in self.array(a[0]):v=z3.Xor(v,self.boolean(x))
            return v
        if name in ['array_bool_and','array_bool_or']:
            self.arity(a,2);xs=[self.boolean(x) for x in self.array(a[0])];r=self.boolean(a[1])
            if name=='array_bool_and':v=z3.And(*xs)
            elif name=='array_bool_or':v=z3.Or(*xs)
            else:
                v=z3.BoolVal(False)
                for x in xs:v=z3.Xor(v,x)
            return r==v
        if name=='bool_clause':
            self.arity(a,2);return z3.Or(*[self.boolean(x) for x in self.array(a[0])],*[z3.Not(self.boolean(x)) for x in self.array(a[1])])
        if name=='bool2int':self.arity(a,2);return self.integer(a[1])==z3.If(self.boolean(a[0]),1,0)
        if name=='int2float':self.arity(a,2);return self.arithmetic(a[1])==z3.ToReal(self.integer(a[0]))
        if name=='gecode_regular':
            self.arity(a,6);xs=[self.integer(x) for x in self.array(a[0])]
            q,s,initial=[self.integer(a[i]) for i in (1,2,4)]
            need(all(z3.is_int_value(x) for x in (q,s,initial)),'regular constant shape/start')
            q,s,initial=[x.as_long() for x in (q,s,initial)]
            transitions=[self.integer(x) for x in self.array(a[3])]
            need(q>0 and s>0 and 1<=initial<=q and len(transitions)==q*s,'regular transition dimensions/start')
            need(all(z3.is_int_value(x) and 0<=x.as_long()<=q for x in transitions),'regular transition destination')
            # Read the complete literal accepting set, including deletions in
            # a store chain. Unknown/nonconstant sets are never approximated.
            final=a[5];members={}
            while z3.is_store(final):
                index,value=final.arg(1),z3.simplify(final.arg(2))
                need(z3.is_int_value(index) and (z3.is_true(value) or z3.is_false(value)),'regular constant accepting set')
                members.setdefault(index.as_long(),z3.is_true(value));final=final.arg(0)
            need(z3.is_const_array(final) and z3.is_false(z3.simplify(final.arg(0))),'regular finite accepting set')
            accepting=sorted(i for i,present in members.items() if present)
            need(all(1<=i<=q for i in accepting),'regular accepting state outside domain')
            # The official transition table is row-major (state, symbol).
            # State zero is absorbing failure. Sharing the prior state AST
            # keeps the deterministic recurrence exact without path expansion.
            state=z3.IntVal(initial);parts=[]
            for value in xs:
                parts.append(z3.And(value>=1,value<=s));next_state=z3.IntVal(0)
                for row in range(q-1,-1,-1):
                    for column in range(s-1,-1,-1):
                        destination=transitions[row*s+column]
                        if destination.as_long()!=0:next_state=z3.If(z3.And(state==row+1,value==column+1),destination,next_state)
                state=next_state
            parts.append(z3.Or(*[state==i for i in accepting]))
            return z3.And(*parts)
        if name=='gecode_nooverlap':
            # gecode/fzn_diffn swaps the public (x,y,dx,dy) argument order.
            # Strict diffn keeps zero-width rectangles in every separation.
            self.arity(a,4);x,w,y,h=[[self.integer(v) for v in self.array(xs)] for xs in a]
            need(len(x)==len(y)==len(w)==len(h),'nooverlap array lengths')
            need(all(self.nonnegative(v) for v in w+h),'nooverlap nonnegative sizes not established')
            return z3.And(*[z3.Or(x[i]+w[i]<=x[j],x[j]+w[j]<=x[i],y[i]+h[i]<=y[j],y[j]+h[j]<=y[i]) for i in range(len(x)) for j in range(i+1,len(x))])
        if name=='inverse_offsets':
            self.arity(a,4);f=[self.integer(v) for v in self.array(a[0])];foff=self.integer(a[1]);inv=[self.integer(v) for v in self.array(a[2])];ioff=self.integer(a[3])
            need(z3.is_int_value(foff) and z3.is_int_value(ioff),'inverse offsets must be constants')
            # foff is the value/index origin of invf, not the origin of f.
            parts=[z3.And(v>=foff,v<foff+len(inv)) for v in f]+[z3.And(v>=ioff,v<ioff+len(f)) for v in inv]
            parts.extend((fv==foff+j)==(iv==ioff+i) for i,fv in enumerate(f) for j,iv in enumerate(inv))
            return z3.And(*parts)
        if name in ['gecode_maximum_arg_int_offset','gecode_maximum_arg_bool_offset']:
            self.arity(a,3);xs=self.array(a[0]);offset=self.integer(a[1]);index=self.integer(a[2])
            need(z3.is_int_value(offset),'argmax offset must be constant')
            xs=[z3.If(self.boolean(x),1,0) if name.endswith('bool_offset') else self.integer(x) for x in xs]
            # Least source index wins ties, as required by std/arg_max.mzn.
            return z3.Or(*[z3.And(index==offset+i,*[x>v if j<i else x>=v for j,v in enumerate(xs)]) for i,x in enumerate(xs)])
        if name=='gecode_cumulatives':
            # The four-argument cumulative overload has nonnegative usage.
            # Signed resources in the six-argument multi-machine overload
            # require separate covered-event semantics and remain unsupported.
            need(len(a)==4,'multi-machine cumulative overload not supported')
            starts,durations,uses=[[self.integer(v) for v in self.array(xs)] for xs in a[:3]];capacity=self.integer(a[3])
            need(len(starts)==len(durations)==len(uses),'cumulative array lengths')
            need(all(self.nonnegative(v) for v in durations+uses),'cumulative nonnegative durations/resources not established')
            if not starts:return z3.BoolVal(True)
            # Between starts the nonnegative load cannot increase. Include
            # baseline zero even if all durations/usages are zero.
            return z3.And(capacity>=0,*[z3.Sum(*[z3.If(z3.And(s<=at,at<s+d),r,0) for s,d,r in zip(starts,durations,uses)])<=capacity for at in starts])
        if name=='gecode_circuit':
            self.arity(a,2);offset=self.integer(a[0]);xs=[self.integer(v) for v in self.array(a[1])];n=len(xs)
            need(z3.is_int_value(offset),'circuit offset must be constant')
            need(n>=2,'degenerate circuit requires explicit backend profile')
            # Exact std/fzn_circuit order witness. The finite lookup remains
            # shared through stores; no inferred bound on source variables.
            order=[z3.FreshInt('circuit_order') for _ in xs];lookup=z3.K(z3.IntSort(),z3.IntVal(0))
            for i,v in enumerate(order):lookup=z3.Store(lookup,offset+i,v)
            parts=[z3.Distinct(*xs),z3.Distinct(*order),order[0]==1]
            parts.extend(z3.And(v>=1,v<=n) for v in order)
            parts.extend(z3.And(x>=offset,x<offset+n,x!=offset+i,z3.Select(lookup,x)==z3.If(order[i]==n,1,order[i]+1)) for i,x in enumerate(xs))
            return z3.Exists(order,z3.And(*parts))
        if name in ['gecode_int_element2d','gecode_bool_element2d']:
            # Official gecode/redefinitions-2.5.2.mzn supplies both complete
            # index sets and row-major array1d(x). Guard each coordinate:
            # an out-of-range column can otherwise alias the following row.
            self.arity(a,6);row=self.integer(a[0]);column=self.integer(a[1])
            start_row,nrows=self.index_interval(a[3]);start_column,ncols=self.index_interval(a[4])
            check=self.integer if name=='gecode_int_element2d' else self.boolean
            xs=[check(v) for v in self.array(a[2])];value=check(a[5])
            need(len(xs)==nrows*ncols,'element2d array dimensions')
            index=(row-start_row)*ncols+(column-start_column)
            return z3.And(row>=start_row,row<start_row+nrows,
                          column>=start_column,column<start_column+ncols,
                          element_relation(index,0,xs,value))
        if name in ['gecode_int_element','gecode_bool_element']:
            # Official gecode/redefinitions-2.0.2.mzn passes the minimum
            # source index explicitly. It need not be zero or one.
            self.arity(a,4);index=self.integer(a[0]);offset=self.integer(a[1]);xs=self.array(a[2]);value=a[3]
            need(z3.is_int_value(offset),'element offset must be constant')
            check=self.integer if name=='gecode_int_element' else self.boolean
            value=check(value);xs=[check(x) for x in xs]
            return element_relation(index,offset.as_long(),xs,value)
        if name=='gecode_table_int':
            # Gecode's fzn_table_int maps array2d rows to array1d in row order.
            self.arity(a,2);xs=[self.integer(x) for x in self.array(a[0])];table=self.array(a[1])
            need(xs and len(table)%len(xs)==0,'table width')
            # The table holds every wrapper alive for this call. Validate and
            # decode each shared immutable numeral once, without assuming that
            # other callers of predicate() used this reader's literal cache.
            decoded={};values=[]
            for value in table:
                key=id(value)
                if key not in decoded:
                    self.integer(value)
                    need(z3.is_int_value(value),'table entries must be constants')
                    decoded[key]=value.as_long()
                values.append(decoded[key])
            if self.table_encoding=='auto':
                functional=functional_integer_table_relation(xs,values)
                if functional is not None:return functional
            # Share complete literal suffixes before building SMT expressions;
            # factoring preserves the full relation over unbounded integers.
            rows=[tuple(((v,v),) for v in values[i:i+len(xs)])
                  for i in range(0,len(values),len(xs))]
            return integer_table_relation(xs,plan_integer_table(len(xs),rows))
        if name=='gecode_bin_packing_load':
            # Gecode preserves the original first load index explicitly.
            # Every item, including zero-weight items, must name a real bin.
            self.arity(a,4)
            loads,bins,weights=[[self.integer(x) for x in self.array(xs)] for xs in a[:3]]
            offset=self.integer(a[3])
            need(z3.is_int_value(offset),'bin packing offset must be constant')
            need(len(bins)==len(weights),'bin packing item/weight lengths')
            need(all(z3.is_int_value(w) and w.as_long()>=0 for w in weights),
                 'bin packing weights must be nonnegative constants')
            weights=[w.as_long() for w in weights];first=offset.as_long()
            parts=[z3.And(b>=first,b<first+len(loads)) for b in bins]
            parts.append(z3.Sum(*loads)==sum(weights))
            for index,load in enumerate(loads,first):
                terms=[z3.If(b==index,w,0) for b,w in zip(bins,weights) if w]
                parts.append(load==(z3.Sum(*terms) if terms else 0))
            return z3.And(*parts)
        if name=='fzn_nvalue':
            self.arity(a,2);count=self.integer(a[0]);xs=[self.integer(x) for x in self.array(a[1])]
            # A value contributes exactly once, at its first occurrence. The
            # shared prefix array keeps the DAG linear without restricting
            # integers to a guessed or enumerated value domain.
            seen=z3.K(z3.IntSort(ctx=count.ctx),z3.BoolVal(False,ctx=count.ctx))
            parts=[]
            for value in xs:
                parts.append(z3.If(z3.Select(seen,value),0,1))
                seen=z3.Store(seen,value,z3.BoolVal(True,ctx=count.ctx))
            return count==(z3.Sum(*parts) if parts else z3.IntVal(0,ctx=count.ctx))
        if name in ['fzn_count_eq','fzn_count_eq_par']:
            self.arity(a,3);xs=[self.integer(x) for x in self.array(a[0])];value=self.integer(a[1]);count=self.integer(a[2])
            return count==z3.Sum(*[z3.If(x==value,1,0) for x in xs])
        if name in ['gecode_global_cardinality','gecode_global_cardinality_closed','fzn_global_cardinality_low_up','fzn_global_cardinality_low_up_closed']:
            low_up=name.startswith('fzn_');self.arity(a,4 if low_up else 3)
            xs=[self.integer(x) for x in self.array(a[0])];cover=[self.integer(x) for x in self.array(a[1])]
            need(all(z3.is_int_value(v) for v in cover),'cardinality cover must be constants')
            counts=[z3.Sum(*[z3.If(x==v,1,0) for x in xs]) for v in cover];parts=[]
            if low_up:
                lower=[self.integer(x) for x in self.array(a[2])];upper=[self.integer(x) for x in self.array(a[3])]
                need(len(cover)==len(lower)==len(upper),'cardinality bound lengths')
                need(all(z3.is_int_value(x) for x in lower+upper),'cardinality bounds must be constants')
                parts.extend(z3.And(n>=lo,n<=hi) for n,lo,hi in zip(counts,lower,upper))
            else:
                expected=[self.integer(x) for x in self.array(a[2])];need(len(cover)==len(expected),'cardinality count lengths')
                parts.extend(n==v for n,v in zip(counts,expected))
            if name.endswith('_closed'):parts.extend(z3.Or(*[x==v for v in cover]) for x in xs)
            return z3.And(*parts)
        if name in ['array_int_lq','array_int_lt','gecode_array_int_lq',
                    'gecode_array_int_lt','fzn_lex_lesseq_int','fzn_lex_less_int']:
            self.arity(a,2)
            left,right=[[self.integer(x) for x in self.array(values)] for values in a]
            strict=name.endswith('_lt') or name=='fzn_lex_less_int'
            # Gecode's array_int_lq/lt are lexicographic relations. The first
            # unequal entry decides; an equal prefix is ordered by length.
            # Build a shared suffix recurrence, with no quadratic prefix list.
            value=z3.BoolVal(len(left)<len(right) if strict else len(left)<=len(right))
            for x,y in reversed(list(zip(left,right))):
                value=z3.Or(x<y,z3.And(x==y,value))
            return value
        if name=='fzn_increasing_int':
            self.arity(a,1);xs=[self.integer(x) for x in self.array(a[0])]
            return z3.And(*[x<=y for x,y in zip(xs,xs[1:])])
        if name in ['array_int_element','array_var_int_element','array_bool_element','array_var_bool_element','array_float_element','array_var_float_element','array_set_element','array_var_set_element']:
            self.arity(a,3);index=self.integer(a[0]);xs=self.array(a[1]);value=a[2]
            return element_relation(index,1,xs,value)
        if name in ['array_int_minimum','array_int_maximum','array_float_minimum','array_float_maximum']:
            self.arity(a,2);value,xs=a;xs=self.array(xs);need(bool(xs),'empty extremum');m=xs[0]
            for x in xs[1:]:m=z3.If(m<=x if name.endswith('minimum') else m>=x,m,x)
            return value==m
        if name in ['fzn_all_different_int','all_different_int','fzn_all_different_except_0']:
            self.arity(a,1);xs=[self.integer(x) for x in self.array(a[0])]
            if name.endswith('except_0'):return z3.And(*[z3.Or(x==0,y==0,x!=y) for i,x in enumerate(xs) for y in xs[i+1:]])
            return z3.Distinct(*xs) if len(xs)>=2 else z3.BoolVal(True)
        if name in ['set_eq','set_ne','set_subset','set_superset']:
            self.arity(a,2);x,y=a;need(x.sort().eq(z3.SetSort(z3.IntSort())) and y.sort().eq(x.sort()),'set operand sort')
            return {'set_eq':lambda:x==y,'set_ne':lambda:x!=y,'set_subset':lambda:z3.IsSubset(x,y),'set_superset':lambda:z3.IsSubset(y,x)}[name]()
        if name=='set_in':self.arity(a,2);return z3.IsMember(self.integer(a[0]),a[1])
        if name=='set_card':self.arity(a,2);return self.integer(a[1])==self.set_card(a[0])
        if name in ['set_union','set_intersect','set_diff','set_symdiff']:
            self.arity(a,3);x,y,r=a
            v={'set_union':lambda:z3.SetUnion(x,y),'set_intersect':lambda:z3.SetIntersect(x,y),'set_diff':lambda:z3.SetDifference(x,y),'set_symdiff':lambda:z3.SetUnion(z3.SetDifference(x,y),z3.SetDifference(y,x))}[name]();return r==v
        raise Unsupported('FlatZinc constraint '+name)
    def read(self,doc):
        fields(doc,['variables','arrays','constraints','output','solve','version']);need(doc.get('version')=='1.0','FlatZinc JSON version')
        need(all(k in doc for k in ['variables','arrays','constraints','output','solve']),'missing FlatZinc component')
        for name,spec in doc['variables'].items():
            fields(spec,['type','domain','rhs','introduced','defined','ann']);kind=spec['type'];need(kind in ['int','float','bool','set of int'],'FlatZinc sort')
            sort={'int':z3.IntSort,'float':z3.RealSort,'bool':z3.BoolSort,'set of int':lambda:z3.SetSort(z3.IntSort())}[kind]()
            v=z3.FreshConst(sort,prefix='fzn_'+name);self.variables[name]=v
            if 'domain' in spec:
                domain=ranges(spec['domain'],kind!='float')
                if kind=='int':self.int_domains[v.get_id()]=domain
                if kind=='set of int':
                    carrier=tuple(sorted({i for a,b in domain for i in range(a,b+1)}))
                    self.universe.update(carrier);self.set_domains[v.get_id()]=carrier
                    self.constraints.append(z3.IsSubset(v,finite_set(domain)))
                elif kind=='bool':raise Unsupported('Boolean domain attribute')
                else:self.constraints.append(in_ranges(v,[(real(a),real(b)) for a,b in domain]) if kind=='float' else in_ranges(v,domain))
            elif kind=='set of int':raise Unsupported('set variable without finite carrier')
        # A shared finite universe suffices for cardinality because every set
        # variable is bounded above. Literal sets are included before building
        # any constraint, so declaration/constraint order cannot shrink it.
        def collect(v):
            if isinstance(v,dict):
                if set(v)=={'set'}:
                    self.universe.update(i for a,b in ranges(v['set']) for i in range(a,b+1))
                else:
                    for x in v.values():collect(x)
            elif isinstance(v,list):
                for x in v:collect(x)
        collect(doc)
        pending=dict(doc['arrays'])
        while pending:
            progress=False
            for name,spec in list(pending.items()):
                need(name not in self.variables,'array/scalar identity collision');fields(spec,['a','ann','introduced','defined'])
                try:value=self.value(spec['a'])
                except Unsupported as e:
                    if 'unknown FlatZinc identifier' in str(e):continue
                    raise
                self.array(value);self.arrays[name]=value;del pending[name];progress=True
            need(progress or not pending,'cyclic/unknown array reference')
        for name,spec in doc['variables'].items():
            if 'rhs' in spec:
                value=self.value(spec['rhs']);need(self.variables[name].sort().eq(value.sort()),'rhs sort');self.constraints.append(self.variables[name]==value)
        for row in doc['constraints']:
            fields(row,['id','args','ann','defines','defined']);need('id' in row and 'args' in row,'constraint shape')
            if 'defined' in row:need(type(row['defined']) is bool,'definition annotation must be Boolean')
            if 'defines' in row:need(row['defines'] in self.variables,'unknown definition metadata')
            self.constraints.append(self.predicate(row['id'],[self.value(x) for x in row['args']]))
        for name in doc['output']:need(name in self.variables or name in self.arrays,'unknown output identity')
        solve=doc['solve'];fields(solve,['method','objective','ann']);method=solve.get('method');need(method in ['satisfy','minimize','maximize'],'solve method')
        need(('objective' in solve)==(method!='satisfy'),'objective arity')
        objective=self.value(solve['objective']) if method!='satisfy' else None
        if objective is not None:self.arithmetic(objective)
        return Source(self.variables,self.arrays,self.constraints,objective,method,tuple(sorted(self.universe)),dict(self.int_domains),dict(self.set_domains))

def read_source(data, *, table_encoding='auto'):
    return Reader(table_encoding=table_encoding).read(json.loads(data,parse_float=Decimal) if isinstance(data,(str,bytes)) else data)
