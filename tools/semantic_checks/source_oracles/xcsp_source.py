"""Independent XCSP3 integer source relation, using the published XML semantics.

Unsupported syntax aborts the whole source model. No SOMTParser node, target
formula, solution, objective optimum, or compiler-private value builds this
reference. Every declared scalar coordinate and source constraint is retained.
"""
from dataclasses import dataclass
from itertools import product,combinations
import copy,re,xml.etree.ElementTree as ET
import z3
from ..table_cliques import plan_clique_table, CliqueTable
from ..integer_tables import (plan_integer_table as _extension_plan,
                              integer_table_relation as _extension_relation)

class Unsupported(ValueError):pass

def need(ok,message):
    if not ok:raise Unsupported(message)

def fields(text,separator=None):
    """Split list expressions, retaining functional terms and finite sets."""
    out=[];start=0;depth=0
    for i,c in enumerate(text):
        if c in '({[':depth+=1
        elif c in ')}]':depth-=1;need(depth>=0,'unbalanced list')
        elif depth==0 and (c==separator if separator else c.isspace()):
            if text[start:i].strip():out.append(text[start:i].strip())
            start=i+1
    need(depth==0,'unbalanced list')
    if text[start:].strip():out.append(text[start:].strip())
    return out

def integer(text):
    need(re.fullmatch(r'[+-]?\d+',text) is not None,'expected integer: '+text)
    return int(text)

def intervals(text):
    out=[]
    for word in fields(text):
        if '..' in word:
            pair=word.split('..');need(len(pair)==2,'bad interval');lo,hi=map(integer,pair);need(lo<=hi,'reversed interval')
        else:lo=hi=integer(word)
        out.append((lo,hi))
    # Closed integer intervals admit exact union normalization: adjacency is
    # mergeable for Int only. Holes and the empty domain remain unchanged.
    merged=[]
    for lo,hi in sorted(out):
        if merged and lo<=merged[-1][1]+1:merged[-1]=(merged[-1][0],max(hi,merged[-1][1]))
        else:merged.append((lo,hi))
    return tuple(merged)

def member(value,ranges):return z3.Or(*[value==a if a==b else z3.And(value>=a,value<=b) for a,b in ranges])

def arithmetic(value):
    if z3.is_bool(value):return z3.If(value,1,0)
    need(z3.is_int(value),'expected integer expression');return value

def expr_text(e):return ''.join(e.itertext()).strip()
def attrs(e,extra=()):need(set(e.attrib)<=set(extra)|{'id','class','note'},'unsupported attributes on '+e.tag+': '+str(e.attrib))
def children(e,allowed):need(all(c.tag in allowed for c in e),'unsupported child in '+e.tag)
def one(e,name,required=True):
    values=e.findall(name);need(len(values)<=1,'duplicate '+name)
    if required:need(bool(values),'missing '+name)
    return values[0] if values else None

def text_of(e,name,default=None):
    child=one(e,name,default is None)
    return expr_text(child) if child is not None else default

@dataclass
class Source:
    variables:dict
    domains:dict
    constraints:list
    objectives:list
    constraint_count:int
    source_type:str
    reference_profile:object=None
    private_variables:tuple=()
    @property
    def relation(self):
        body=z3.And(*self.constraints)
        return z3.Exists(self.private_variables,body) if self.private_variables else body

class Reader:
    def __init__(self,*,reference_profile=None,circuit_witness='successor-walk',cumulative_encoding='event-points'):
        need(reference_profile in [None,'official-java-cpp-open-default','website-closed-default'],'unknown reference parser profile')
        self.reference_profile=reference_profile
        need(circuit_witness in ['successor-walk','cyclic-order'],'unknown circuit witness encoding')
        self.circuit_witness=circuit_witness
        need(cumulative_encoding in ['event-points','integer-time'],'unknown cumulative encoding')
        self.cumulative_encoding=cumulative_encoding
        self.variables={};self.domains={};self.arrays={};self.uniform_array_domains={};self.constraints=[];self.objectives=[];self.constraint_count=0
        self.private_variables=[]
        self.extension_plans={}
        self.extension_templates={}
        self.extension_cliques={}
    def declare(self,name,domain):
        need(name not in self.variables and name not in self.arrays,'duplicate source identity '+name)
        self.variables[name]=z3.Int(name);self.domains[name]=domain;self.constraints.append(member(self.variables[name],domain))
    def selectors(self,token,declared=True):
        match=re.fullmatch(r'([^\[\]\s]+)((?:\[[^\[\]]*\])+)',token)
        need(match is not None and match[1] in self.arrays,'unknown array selector '+token)
        bounds=self.arrays[match[1]];parts=re.findall(r'\[([^\]]*)\]',match[2]);need(len(parts)==len(bounds),'array rank '+token)
        ranges=[]
        for part,(start,size) in zip(parts,bounds):
            if not part:a,b=start,start+size-1
            elif '..' in part:a,b=map(integer,part.split('..'))
            else:a=b=integer(part)
            need(start<=a<=b<start+size,'array index '+token);ranges.append(range(a,b+1))
        names=[match[1]+''.join('['+str(v)+']' for v in row) for row in product(*ranges)]
        if declared:
            # Unassigned cells of a mixed-domain array are absent, not free Ints.
            names=[n for n in names if n in self.variables]
            if all(p and '..' not in p for p in parts):need(len(names)==1,'undeclared source array cell '+token)
        return names
    def expanded_tokens(self,text):
        out=[]
        for token in fields(text):
            if token in self.variables:out.append(token)
            elif '[' in token and '(' not in token:out.extend(self.selectors(token))
            else:
                repeated=re.fullmatch(r'([+-]?\d+)x(\d+)',token)
                if repeated:out.extend([repeated[1]]*int(repeated[2]))
                else:out.append(token)
        return out
    def expressions(self,text):return [self.expression(t) for t in self.expanded_tokens(text)]
    def boolean(self,value):
        if z3.is_bool(value):return value
        if z3.is_int_value(value):need(value.as_long() in [0,1],'non-Boolean literal');return value==1
        if z3.is_const(value) and str(value.decl().name()) in self.domains:
            need(all(0<=a<=b<=1 for a,b in self.domains[str(value.decl().name())]),'Boolean variable has non-Boolean domain')
            return value==1
        raise Unsupported('arithmetic term in Boolean position without Boolean range proof')
    def expression(self,text):
        text=text.strip()
        if text in self.variables:return self.variables[text]
        if re.fullmatch(r'[+-]?\d+',text):return z3.IntVal(int(text))
        if text in ['true','false']:return z3.BoolVal(text=='true')
        m=re.fullmatch(r'([A-Za-z][A-Za-z0-9_]*)\((.*)\)',text,re.S);need(m is not None,'unknown source expression '+text[:120])
        op=m[1];tokens=fields(m[2],',')
        if op=='set':return intervals(' '.join(tokens))
        if op in ['in','notin']:
            need(len(tokens)==2,'membership arity');v=arithmetic(self.expression(tokens[0]));domain=self.expression(tokens[1]);need(isinstance(domain,tuple),'literal set required');f=member(v,domain);return f if op=='in' else z3.Not(f)
        args=[self.expression(t) for t in tokens]
        if op in ['and','or','xor','iff','imp','not']:
            bs=[self.boolean(x) for x in args]
            if op=='not':need(len(bs)==1,'not arity');return z3.Not(bs[0])
            if op=='imp':need(len(bs)==2,'imp arity');return z3.Implies(*bs)
            need(len(bs)>=2,'logical arity')
            if op=='and':return z3.And(*bs)
            if op=='or':return z3.Or(*bs)
            if op=='iff':return z3.And(*[bs[0]==x for x in bs[1:]])
            result=bs[0]
            for b in bs[1:]:result=z3.Xor(result,b)
            return result
        if op=='if':need(len(args)==3,'if arity');return z3.If(self.boolean(args[0]),arithmetic(args[1]),arithmetic(args[2]))
        aa=[arithmetic(x) for x in args]
        if op in ['div','mod']:
            need(len(aa)==2,'partial arithmetic arity');a,b=aa;b=z3.simplify(b)
            nonzero=z3.is_int_value(b) and b.as_long()!=0
            if z3.is_const(b) and str(b) in self.domains:
                nonzero=all(not lo<=0<=hi for lo,hi in self.domains[str(b)])
            # Official Java TreeEvaluator uses / and % (truncate toward zero).
            # Only total-on-declared-domain expressions are covered here;
            # guarded partial expressions remain explicitly unsupported.
            need(nonzero,'source operator '+op+' requires a provably nonzero divisor')
            q=z3.If(a>=0,a,-a)/z3.If(b>=0,b,-b)
            q=z3.If((a>=0)==(b>=0),q,-q)
            return q if op=='div' else a-q*b
        if op in ['eq','ne','lt','le','gt','ge']:
            need(len(aa)>=2 if op=='eq' else len(aa)==2,'comparison arity')
            if op=='eq':return z3.And(*[aa[0]==x for x in aa[1:]])
            a,b=aa;return {'ne':lambda:a!=b,'lt':lambda:a<b,'le':lambda:a<=b,'gt':lambda:a>b,'ge':lambda:a>=b}[op]()
        if op in ['neg','abs','sqr']:need(len(aa)==1,'unary arity');a=aa[0];return -a if op=='neg' else z3.If(a>=0,a,-a) if op=='abs' else a*a
        if op in ['sub','dist']:need(len(aa)==2,'binary arity');a,b=aa;return a-b if op=='sub' else z3.If(a>=b,a-b,b-a)
        if op=='add':need(len(aa)>=2,'add arity');return z3.Sum(*aa)
        if op=='mul':
            need(len(aa)>=2,'mul arity');result=z3.IntVal(1)
            for a in aa:result=result*a
            return result
        if op in ['min','max']:
            need(len(aa)>=2,'min/max arity');result=aa[0]
            for a in aa[1:]:result=z3.If(result<=a if op=='min' else result>=a,result,a)
            return result
        if op=='pow':
            need(len(aa)==2 and z3.is_int_value(aa[1]) and aa[1].as_long()>=0,'constant nonnegative exponent required')
            result=z3.IntVal(1);base=aa[0];n=aa[1].as_long()
            while n:
                if n&1:result=result*base
                n//=2
                if n:base=base*base
            return result
        raise Unsupported('source operator '+op)
    def variables_xml(self,parent):
        attrs(parent)
        for e in parent:
            attrs(e,{'type','as','size','startIndex'});need(e.tag in ['var','array'],'source declaration '+e.tag);need(e.get('type','integer')=='integer','non-integer source variable')
            name=e.get('id');need(bool(name),'missing variable id')
            if e.tag=='var':
                need(not list(e),'nested scalar domain')
                if e.get('as'):
                    need(e.get('as') in self.domains and not expr_text(e),'unknown/nonempty variable alias');domain=self.domains[e.get('as')]
                else:domain=intervals(expr_text(e))
                self.declare(name,domain);continue
            need(name not in self.arrays and name not in self.variables,'duplicate array id')
            shape=e.get('size','');need(re.fullmatch(r'(?:\[\d+\])+',shape) is not None,'invalid array size')
            sizes=[int(x) for x in re.findall(r'\d+',shape)];need(all(x>0 for x in sizes),'nonpositive array dimension')
            start=integer(e.get('startIndex','0'));self.arrays[name]=tuple((start,n) for n in sizes)
            cells=self.selectors(name+'[]'*len(sizes),False);assigned={}
            if e.get('as'):
                # XCSP's `as` copies the referenced domain, not variable values
                # or extents. Uniform domains therefore also permit a new size.
                # Mixed-domain templates need selector remapping and stay explicit.
                need(not list(e) and not expr_text(e),'nonempty array domain alias')
                alias=e.get('as')
                need(alias in self.uniform_array_domains,'unknown/nonuniform array domain alias')
                domain=self.uniform_array_domains[alias];self.uniform_array_domains[name]=domain
                assigned={n:domain for n in cells}
            elif not list(e):
                domain=intervals(expr_text(e));self.uniform_array_domains[name]=domain
                assigned={n:domain for n in cells}
            else:
                children(e,{'domain'});need(not (e.text or '').strip(),'mixed array direct domain');others=False
                for d in e:
                    attrs(d,{'for','as'});need(not d.get('as'),'domain alias unsupported');need(not others,'others domain must be last')
                    selector=d.get('for','');need(bool(selector),'missing domain selector')
                    if selector=='others':names=[n for n in cells if n not in assigned];others=True
                    else:names=[n for t in fields(selector) for n in self.selectors(t,False)]
                    domain=intervals(expr_text(d))
                    for n in names:need(n in cells and n not in assigned,'duplicate/foreign domain cell');assigned[n]=domain
            for n,d in assigned.items():self.declare(n,d)
    def condition(self,value,text):
        need(text.startswith('(') and text.endswith(')'),'condition syntax');parts=fields(text[1:-1],',');need(len(parts)==2,'condition arity');op,rhs=parts
        if op in ['in','notin']:
            domain=intervals(rhs[1:-1].replace(',',' ')) if rhs.startswith('{') and rhs.endswith('}') else intervals(rhs)
            f=member(value,domain);return f if op=='in' else z3.Not(f)
        b=arithmetic(self.expression(rhs));need(op in ['eq','ne','lt','le','gt','ge'],'condition operator')
        return {'eq':lambda:value==b,'ne':lambda:value!=b,'lt':lambda:value<b,'le':lambda:value<=b,'gt':lambda:value>b,'ge':lambda:value>=b}[op]()
    def terms(self,e):attrs(e,{'startIndex','rank'});need(not list(e),'unexpected nested list');return [arithmetic(v) for v in self.expressions(expr_text(e))]
    def matrix(self,e):
        attrs(e,{'startRowIndex','startColIndex'});need(not list(e),'nested matrix XML')
        text=expr_text(e);rows=[]
        if text.startswith('('):
            depth=0;start=None;last=0
            for i,c in enumerate(text):
                if c=='(':
                    if depth==0:need(not text[last:i].strip(),'matrix text outside rows');start=i+1
                    depth+=1
                elif c==')':
                    depth-=1;need(depth>=0,'unbalanced matrix')
                    if depth==0:
                        rows.append([arithmetic(self.expression(t)) for t in fields(text[start:i],',')]);last=i+1
            need(depth==0 and not text[last:].strip(),'truncated/trailing matrix')
        else:
            match=re.fullmatch(r'([^\[\]\s]+)\[([^\]]*)\]\[([^\]]*)\]',text)
            need(match is not None and match[1] in self.arrays and len(self.arrays[match[1]])==2,'compact matrix requires rank two')
            ranges=[]
            for part,(start,size) in zip(match.groups()[1:],self.arrays[match[1]]):
                if not part:lo,hi=start,start+size-1
                elif '..' in part:lo,hi=map(integer,part.split('..'))
                else:lo=hi=integer(part)
                need(start<=lo<=hi<start+size,'compact matrix index');ranges.append(range(lo,hi+1))
            for i in ranges[0]:
                row=[]
                for j in ranges[1]:
                    name=f'{match[1]}[{i}][{j}]';need(name in self.variables,'absent compact matrix cell '+name);row.append(self.variables[name])
                rows.append(row)
        need(bool(rows) and len(rows[0])>0 and len({len(row) for row in rows})==1,'ragged/empty matrix')
        return rows
    def template(self,e,args):
        raw=ET.tostring(e,encoding='unicode');used=[int(x) for x in re.findall(r'%(\d+)',raw)];tail=max(used,default=-1)+1
        need(not used or max(used)<len(args),'template missing argument')
        def substitute(m):return ' '.join(args[tail:]) if m[1]=='...' else args[int(m[1])]
        out=copy.deepcopy(e)
        for n in out.iter():
            if n.text:n.text=re.sub(r'%(\.\.\.|\d+)',substitute,n.text)
            for k,v in list(n.attrib.items()):n.attrib[k]=re.sub(r'%(\.\.\.|\d+)',substitute,v)
        return out
    def constraint(self,e):
        attrs(e,{'zeroIgnored'} if e.tag=='noOverlap' else ())
        if e.tag in ['constraints','block']:
            for child in e:self.constraint(child)
            return
        if e.tag=='group':
            need(len(e)>=2 and all(x.tag=='args' for x in list(e)[1:]),'group shape')
            for arg in list(e)[1:]:attrs(arg);self.constraint(self.template(e[0],self.expanded_tokens(expr_text(arg))))
            return
        f=None
        if e.tag=='intension':
            children(e,{'function'});f=self.boolean(self.expression(expr_text(e)))
        elif e.tag=='sum':
            children(e,{'list','coeffs','condition'});xs=self.terms(one(e,'list'));cs=one(e,'coeffs',False);coeff=self.terms(cs) if cs is not None else [z3.IntVal(1)]*len(xs);need(len(xs)==len(coeff),'sum arity');f=self.condition(z3.Sum(*[a*b for a,b in zip(xs,coeff)]),text_of(e,'condition'))
        elif e.tag=='count':
            children(e,{'list','values','condition'});xs=self.terms(one(e,'list'));vs=self.terms(one(e,'values'));f=self.condition(z3.Sum(*[z3.If(z3.Or(*[a==b for b in vs]),1,0) for a in xs]),text_of(e,'condition'))
        elif e.tag=='nValues':
            children(e,{'list','except','condition'});xs=self.terms(one(e,'list'));need(len(xs)>=2,'nValues list arity')
            excluded=one(e,'except',False)
            if excluded is None:values=[]
            else:
                attrs(excluded);need(not list(excluded),'nested nValues except');values=[integer(t) for t in fields(expr_text(excluded))];need(bool(values),'empty nValues except')
            # Count exactly the first occurrence of each non-excluded value.
            # Repeated variables and arbitrary integer expression values are retained.
            terms=[z3.If(z3.And(*[x!=value for value in values],*[x!=previous for previous in xs[:i]]),1,0) for i,x in enumerate(xs)]
            f=self.condition(z3.Sum(*terms),text_of(e,'condition'))
        elif e.tag=='cardinality':
            children(e,{'list','values','occurs'});xs=self.terms(one(e,'list'));values=one(e,'values');occurs=one(e,'occurs');attrs(values,{'closed'});attrs(occurs)
            vs=[arithmetic(v) for v in self.expressions(expr_text(values))];os=fields(expr_text(occurs));need(len(xs)>=2 and vs and len(vs)==len(os),'cardinality arity')
            constants=all(z3.is_int_value(v) for v in vs);variables=all(z3.is_const(v) and v.num_args()==0 and str(v) in self.variables for v in vs)
            need(constants or variables,'cardinality values must be uniformly constants or variables')
            parts=[]
            for value,occurrence in zip(vs,os):
                count=z3.Sum(*[z3.If(x==value,1,0) for x in xs])
                parts.append(member(count,intervals(occurrence)) if '..' in occurrence else count==arithmetic(self.expression(occurrence)))
            if variables:parts.append(z3.Distinct(*vs) if len(vs)>1 else z3.BoolVal(True))
            closed=values.get('closed')
            if closed is None:
                # Published prose and the official reference parsers disagree.
                # Never select an interpretation from the candidate's result.
                need(self.reference_profile is not None,'omitted cardinality closed requires explicit reference-parser profile')
                closed='false' if self.reference_profile=='official-java-cpp-open-default' else 'true'
            need(closed in ['true','false'],'cardinality closed Boolean')
            if closed=='true':parts.extend(z3.Or(*[x==v for v in vs]) for x in xs)
            f=z3.And(*parts)
        elif e.tag=='allDifferent':
            children(e,{'list','except'});ls=e.findall('list');exc=one(e,'except',False)
            if len(ls)>1:
                tuples=[self.terms(row) for row in ls]
                width=len(tuples[0]);need(width>=2 and all(len(row)==width for row in tuples),'tuple allDifferent arity')
                exceptions=[]
                if exc is not None:
                    attrs(exc);need(not list(exc),'nested tuple exception')
                    text=expr_text(exc)
                    need(re.fullmatch(r'(?:\s*\([^()]*\))*\s*',text) is not None,'tuple exception syntax')
                    parts=re.findall(r'\([^()]*\)',text)
                    # Exception tuples are constants; no wildcards, variables,
                    # intervals or unparsed text may disappear from the model.
                    for part in parts:
                        need(part.startswith('(') and part.endswith(')'),'tuple exception syntax')
                        row=[integer(value) for value in fields(part[1:-1],',')]
                        need(len(row)==width,'tuple exception arity');exceptions.append(row)
                def excepted(row):return z3.Or(*[z3.And(*[v==k for v,k in zip(row,values)]) for values in exceptions])
                f=z3.And(*[z3.Or(*[a!=b for a,b in zip(left,right)],excepted(left),excepted(right)) for left,right in combinations(tuples,2)])
            else:
                xs=self.terms(ls[0]) if ls else self.terms(e)
                if exc is None:f=z3.Distinct(*xs) if len(xs)>=2 else z3.BoolVal(True)
                else:
                    domain=intervals(expr_text(exc));f=z3.And(*[z3.Or(a!=b,member(a,domain),member(b,domain)) for a,b in combinations(xs,2)])
        elif e.tag=='noOverlap':
            children(e,{'origins','lengths'})
            origins=one(e,'origins');lengths=one(e,'lengths');attrs(origins);attrs(lengths)
            if expr_text(origins).startswith('('):
                starts=self.matrix(origins);durations=self.matrix(lengths)
            else:
                starts=[[x] for x in self.terms(origins)];durations=[[x] for x in self.terms(lengths)]
            need(len(starts)>=2 and len(starts)==len(durations),'noOverlap task arity')
            width=len(starts[0]);need(width>0 and all(len(x)==width for x in starts+durations),'noOverlap dimensions')
            ignored=e.get('zeroIgnored','true');need(ignored in ['true','false'],'noOverlap zeroIgnored Boolean')
            parts=[]
            for i,j in combinations(range(len(starts)),2):
                alternatives=[]
                if ignored=='true':alternatives.extend(d==0 for d in durations[i]+durations[j])
                for a,la,b,lb in zip(starts[i],durations[i],starts[j],durations[j]):alternatives.extend([a+la<=b,b+lb<=a])
                parts.append(z3.Or(*alternatives))
            f=z3.And(*parts)
        elif e.tag=='cumulative':
            # The machine-indexed variant has different quantification and is
            # intentionally unsupported; none of its children may be dropped.
            children(e,{'origins','lengths','ends','heights','condition'})
            nodes=[one(e,name) for name in ('origins','lengths','heights')]
            for node in nodes:attrs(node)
            starts,durations,heights=[self.terms(node) for node in nodes]
            need(len(starts)>=2 and len(starts)==len(durations)==len(heights),'cumulative task arity')
            condition=one(e,'condition');attrs(condition);need(not list(condition),'nested cumulative condition')
            condition_text=expr_text(condition)
            ends=[a+l for a,l in zip(starts,durations)]
            parts=[];end_node=one(e,'ends',False)
            if end_node is not None:
                attrs(end_node);explicit_ends=self.terms(end_node);need(len(explicit_ends)==len(starts),'cumulative ends arity')
                parts.extend(a==b for a,b in zip(ends,explicit_ends))
            # For each assignment the load is constant between successive
            # integer start/end events and zero outside their finite envelope.
            # Checking zero plus every event therefore checks *all* Int times,
            # including negative times. End events are necessary for negative
            # heights/non-monotone conditions. No domain or horizon is added.
            if self.cumulative_encoding=='integer-time':
                # Equivalent linear-size spelling of that same full relation:
                # no horizon or sign assumption is added. The event spelling
                # uses O(n^2) task terms; this binder uses O(n), which lets the
                # independent source remain comparable to quantified targets.
                time=z3.FreshInt('source_cumulative_time')
                load=z3.Sum(*[z3.If(z3.And(a<=time,time<b),h,0) for a,b,h in zip(starts,ends,heights)])
                parts.append(z3.ForAll([time],self.condition(load,condition_text)))
            else:
                parts.append(self.condition(z3.IntVal(0),condition_text))
                for time in starts+ends:
                    load=z3.Sum(*[z3.If(z3.And(a<=time,time<b),h,0) for a,b,h in zip(starts,ends,heights)])
                    parts.append(self.condition(load,condition_text))
            f=z3.And(*parts)
        elif e.tag=='flow':
            children(e,{'list','balance','arcs','capacities','weights','condition'})
            need(not (e.text or '').strip(),'flow text outside fields')
            nodes={name:one(e,name,name in ['list','balance','arcs']) for name in ('list','balance','arcs','capacities','weights','condition')}
            for node in nodes.values():
                if node is not None:
                    attrs(node);need(not list(node) and not (node.tail or '').strip(),'nested/trailing flow field')
            def atomic_terms(node):
                values=self.terms(node)
                need(all(z3.is_int_value(v) or (z3.is_const(v) and str(v.decl().name()) in self.variables) for v in values),'flow integer literal or source variable required')
                return values
            xs=atomic_terms(nodes['list']);balances=atomic_terms(nodes['balance'])
            need(len(xs)>=2 and all(z3.is_const(v) and str(v.decl().name()) in self.variables for v in xs),'flow arc variables required')
            text=expr_text(nodes['arcs']);arcs=[];last=0
            for match in re.finditer(r'\(\s*([+-]?\d+)\s*,\s*([+-]?\d+)\s*\)',text):
                need(not text[last:match.start()].strip(),'flow arc grammar');last=match.end()
                arcs.append((integer(match[1]),integer(match[2])))
            need(not text[last:].strip() and len(arcs)==len(xs),'flow arc/list arity')
            labels=sorted({v for arc in arcs for v in arc})
            need(len(labels)>=2 and len(labels)==len(balances),'flow balance/node arity')
            # The reference checker indexes balance by node - minimum node.
            # Do not invent a different map for ambiguous sparse identifiers.
            need(all(b==a+1 for a,b in zip(labels,labels[1:])),'flow consecutive node identifiers required')
            contributions={node:[] for node in labels}
            for value,(tail,head) in zip(xs,arcs):
                contributions[tail].append(value);contributions[head].append(-value)
            # Semantics 45 uses outgoing minus incoming. The sum retains each
            # arc occurrence, including repeated coordinates and self loops.
            parts=[z3.Sum(*contributions[node])==balance for node,balance in zip(labels,balances)]
            capacities=nodes['capacities']
            if capacities is not None:
                bounds=[]
                for token in fields(expr_text(capacities)):
                    match=re.fullmatch(r'([+-]?\d+)\.\.([+-]?\d+)(?:x(\d+))?',token)
                    need(match is not None,'flow capacity interval required')
                    lo,hi=integer(match[1]),integer(match[2]);count=int(match[3] or '1')
                    need(lo<=hi and 0<count<=len(xs)-len(bounds),'flow capacity bounds/repetition')
                    bounds.extend([(lo,hi)]*count)
                need(len(bounds)==len(xs),'flow capacity/arc arity')
                parts.extend(z3.And(v>=lo,v<=hi) for v,(lo,hi) in zip(xs,bounds))
            weights,condition=nodes['weights'],nodes['condition']
            need((weights is None)==(condition is None),'flow weights and condition must occur together')
            if weights is not None:
                ws=atomic_terms(weights);need(len(ws)==len(xs),'flow weight/arc arity')
                parts.append(self.condition(z3.Sum(*[v*w for v,w in zip(xs,ws)]),expr_text(condition)))
            # No positivity or conservation-derived domain restriction is
            # added beyond the declared domains and explicit capacities.
            f=z3.And(*parts)
        elif e.tag=='circuit':
            children(e,{'list','size'})
            scope=one(e,'list',False)
            need(scope is not None or not list(e),'circuit size requires list')
            if scope is not None:attrs(scope,{'startIndex'})
            xs=self.terms(scope if scope is not None else e);n=len(xs)
            need(n>=2 and all(z3.is_const(x) and str(x.decl().name()) in self.variables for x in xs),'circuit requires successor variables')
            start=integer(scope.get('startIndex','0')) if scope is not None else 0
            labels=list(range(start,start+n));active=[x!=label for x,label in zip(xs,labels)]
            count=z3.Sum(*[z3.If(a,1,0) for a in active])
            parts=[z3.Distinct(*xs),count>1,*[z3.And(start<=x,x<start+n) for x in xs]]
            size=one(e,'size',False);required=None
            if size is not None:
                attrs(size);need(not list(size),'nested circuit size')
                required=arithmetic(self.expression(expr_text(size)))
                need(z3.is_int_value(required) or (z3.is_const(required) and str(required.decl().name()) in self.variables),'circuit size must be an integer or source variable')
                parts.append(count==required)
            if self.circuit_witness=='cyclic-order':
                from .circuit_order import cyclic_order_witness
                f,witnesses=cyclic_order_witness(xs,start=start,size=required)
                self.private_variables.extend(witnesses)
            else:
                # Follow the successor permutation from its first non-self node.
                # Exactly count distinct visited nodes and a final return to the
                # anchor witness one cycle containing all active nodes. These are
                # source-side walk values, not the target's inverse positions.
                # The linear-size witness avoids an n-by-n reachability matrix.
                anchor=z3.IntVal(start)
                for enabled,label in reversed(list(zip(active,labels))):anchor=z3.If(enabled,label,anchor)
                table=z3.K(z3.IntSort(),z3.IntVal(start))
                for label,value in zip(labels,xs):table=z3.Store(table,label,value)
                walk=[z3.FreshInt('source_circuit_walk') for _ in range(n)]
                self.private_variables.extend(walk)
                parts.append(walk[0]==anchor)
                for i in range(1,n):parts.append(z3.Implies(i<count,walk[i]==z3.Select(table,walk[i-1])))
                # Tags outside the label range exclude unused suffix entries from
                # Distinct without identifying or constraining any source node.
                parts.append(z3.Distinct(*[z3.If(i<count,node,start-1-i) for i,node in enumerate(walk)]))
                walk_table=z3.K(z3.IntSort(),anchor)
                for i,node in enumerate(walk):walk_table=z3.Store(walk_table,i,node)
                parts.append(z3.Select(table,z3.Select(walk_table,count-1))==anchor)
                f=z3.And(*parts)
        elif e.tag=='regular':
            children(e,{'list','transitions','start','final'})
            scope=one(e,'list');attrs(scope);xs=self.terms(scope);need(bool(xs),'regular nonempty word required')
            need(all(z3.is_const(x) and str(x.decl().name()) in self.variables for x in xs),'regular list requires source variables')
            nodes=[one(e,name) for name in ('transitions','start','final')]
            for node in nodes:attrs(node);need(not list(node),'nested regular field')
            text=expr_text(nodes[0]);edges=[];last=0
            pattern=r'\(\s*([^(),\s]+)\s*,\s*([+-]?\d+)\s*,\s*([^(),\s]+)\s*\)'
            for match in re.finditer(pattern,text):
                need(not text[last:match.start()].strip(),'regular transition grammar');last=match.end()
                edges.append((match[1],integer(match[2]),match[3]))
            need(edges and not text[last:].strip(),'regular constant-label transitions required')
            starts=fields(expr_text(nodes[1]));finals=fields(expr_text(nodes[2]))
            states={a for a,_,b in edges}|{b for a,_,b in edges}
            need(len(starts)==1 and starts[0] in states and finals and set(finals)<=states,'regular start/final state identity')
            # Independent finite-word NFA semantics: a state is reachable after
            # the next letter iff some matching incoming edge was reachable.
            # Cycles consume a letter; nondeterministic/duplicate edges remain
            # disjunctive, and repeated source coordinates are not renamed.
            incoming={state:[] for state in states}
            for a,value,b in edges:incoming[b].append((a,value))
            reach={state:z3.BoolVal(state==starts[0]) for state in states}
            for x in xs:
                reach={state:z3.Or(*[z3.And(reach[a],x==value) for a,value in incoming[state]]) for state in states}
            f=z3.Or(*[reach[state] for state in finals])
        elif e.tag=='binPacking':
            children(e,{'list','sizes','condition','limits','loads'})
            scope=one(e,'list');sizes_node=one(e,'sizes');attrs(scope);attrs(sizes_node)
            xs=self.terms(scope);sizes=self.terms(sizes_node)
            need(len(xs)>=2 and len(xs)==len(sizes),'binPacking item/size arity')
            need(all(z3.is_int_value(v) for v in sizes),'binPacking constant sizes required')
            forms=[one(e,name,False) for name in ('condition','limits','loads')]
            need(sum(node is not None for node in forms)==1,'binPacking needs exactly one condition/limits/loads')
            def load(bin_value):return z3.Sum(*[z3.If(x==bin_value,size,0) for x,size in zip(xs,sizes)])
            condition,limits,loads=forms
            if condition is not None:
                attrs(condition);need(not list(condition),'nested binPacking condition')
                # Each used bin is the value of at least one list entry;
                # repeated entries still contribute their own exact sizes.
                f=z3.And(*[self.condition(load(x),expr_text(condition)) for x in xs])
            else:
                node=limits if limits is not None else loads;attrs(node);values=self.terms(node)
                need(bool(values),'empty binPacking bin values')
                # The official finite-bin checker checks every specified bin,
                # including empty bins. Out-of-range items have divergent
                # interpretations; only accept source domains that already
                # prove valid indices, never add a guessed bound here.
                for x in xs:
                    name=str(x.decl().name()) if z3.is_const(x) else None
                    need(name in self.variables and x.eq(self.variables[name]),'binPacking variable partition required')
                    need(all(0<=lo<=hi<len(values) for lo,hi in self.domains[name]),'binPacking finite-bin source domain must establish valid indices')
                f=z3.And(*[load(z3.IntVal(i))<=v if limits is not None else load(z3.IntVal(i))==v for i,v in enumerate(values)])
        elif e.tag=='instantiation':
            children(e,{'list','values'});xs=self.terms(one(e,'list'));vs=self.terms(one(e,'values'));need(len(xs)==len(vs),'instantiation arity');f=z3.And(*[a==b for a,b in zip(xs,vs)])
        elif e.tag=='ordered':
            children(e,{'list','lengths','operator'});xs=self.terms(one(e,'list'));lens=one(e,'lengths',False);lengths=self.terms(lens) if lens is not None else [z3.IntVal(0)]*(len(xs)-1);need(len(lengths) in [len(xs),len(xs)-1],'ordered lengths arity');op=text_of(e,'operator');need(op in ['lt','le','gt','ge'],'ordered operator')
            pairs=[(a+c,b) for a,b,c in zip(xs,xs[1:],lengths)];f=z3.And(*[{'lt':lambda:a<b,'le':lambda:a<=b,'gt':lambda:a>b,'ge':lambda:a>=b}[op]() for a,b in pairs])
        elif e.tag=='lex':
            children(e,{'list','matrix','operator'});matrix=one(e,'matrix',False)
            if matrix is None:
                ls=[self.terms(x) for x in e.findall('list')];need(len(ls)>=2 and len({len(x) for x in ls})==1,'lex list arity');pairs=list(zip(ls,ls[1:]))
            else:
                need(not e.findall('list'),'mixed lex matrix/list');attrs(matrix);ls=self.matrix(matrix);cols=list(zip(*ls));pairs=list(zip(ls,ls[1:]))+list(zip(cols,cols[1:]))
            op=text_of(e,'operator');need(op in ['lt','le','gt','ge'],'lex operator');parts=[]
            for left,right in pairs:
                tail=z3.BoolVal(op in ['le','ge'])
                for a,b in reversed(list(zip(left,right))):tail=z3.Or(a<b if op in ['lt','le'] else a>b,z3.And(a==b,tail))
                parts.append(tail)
            f=z3.And(*parts)
        elif e.tag=='element' and one(e,'matrix',False) is not None:
            children(e,{'matrix','index','value','condition'});matrix=one(e,'matrix');rows=self.matrix(matrix);ix=one(e,'index');attrs(ix);indices=self.terms(ix);need(len(indices)==2,'matrix element index arity')
            value=one(e,'value',False);condition=one(e,'condition',False);need((value is None)!=(condition is None),'matrix element result shape')
            rhs=arithmetic(self.expression(expr_text(value))) if value is not None else None
            row_start=integer(matrix.get('startRowIndex','0'));col_start=integer(matrix.get('startColIndex','0'))
            # Exhaustive finite source matrix selection also excludes invalid indices.
            f=z3.Or(*[z3.And(indices[0]==row_start+i,indices[1]==col_start+j,x==rhs if rhs is not None else self.condition(x,expr_text(condition))) for i,row in enumerate(rows) for j,x in enumerate(row)])
        elif e.tag=='element':
            children(e,{'list','index','value','condition'});ls=one(e,'list');xs=self.terms(ls);ix=one(e,'index',False);value=one(e,'value',False);condition=one(e,'condition',False);need((value is None)!=(condition is None),'element result shape')
            rhs=arithmetic(self.expression(expr_text(value))) if value is not None else None
            relations=[x==rhs if rhs is not None else self.condition(x,expr_text(condition)) for x in xs]
            if ix is None:f=z3.Or(*relations)
            else:
                attrs(ix,{'rank'});index=arithmetic(self.expression(expr_text(ix)));start=integer(ls.get('startIndex','0'));rank=ix.get('rank','any');need(rank in ['any','first','last'],'element rank')
                terms=[]
                for i,relation in enumerate(relations):
                    extra=relations[:i] if rank=='first' else relations[i+1:] if rank=='last' else []
                    terms.append(z3.And(index==start+i,relation,*[z3.Not(x) for x in extra]))
                f=z3.Or(*terms)
        elif e.tag=='extension':
            children(e,{'list','supports','conflicts'});xs=self.terms(one(e,'list'));table=one(e,'supports',False);negative=table is None
            if negative:table=one(e,'conflicts')
            else:need(one(e,'conflicts',False) is None,'two table polarities')
            attrs(table);text=expr_text(table)
            if len(xs)==1:f=member(xs[0],intervals(text))
            else:
                key=(len(xs),text)
                if key not in self.extension_plans:
                    rows=[];pos=0
                    for m in re.finditer(r'\(([^()]*)\)',text):
                        need(not text[pos:m.start()].strip(),'table text outside tuple');pos=m.end();tokens=fields(m[1],',');need(len(tokens)==len(xs),'table tuple width');row=[]
                        for t in tokens:
                            if t=='*':row.append(None)
                            elif t.startswith('{') and t.endswith('}'):row.append(intervals(t[1:-1].replace(',',' ')))
                            else:row.append(intervals(t))
                        rows.append(tuple(row))
                    need(not text[pos:].strip(),'table trailing text')
                    self.extension_plans[key]=_extension_plan(len(xs),rows)
                    cliques=plan_clique_table(len(xs),rows)
                    self.extension_cliques[key]=CliqueTable(cliques) if cliques is not None else None
                if self.extension_cliques[key] is not None:
                    f=self.extension_cliques[key].relation(xs)
                else:
                    f=self.extension_generic(key,xs)
            if negative:f=z3.Not(f)
        else:raise Unsupported('constraint '+e.tag)
        self.constraints.append(f);self.constraint_count+=1
    def extension_generic(self,key,xs):
        if key not in self.extension_templates:
            columns=tuple(z3.FreshInt('source_table_column') for _ in xs)
            self.extension_templates[key]=(columns,_extension_relation(columns,self.extension_plans[key]))
        columns,template=self.extension_templates[key]
        # Simultaneous substitution preserves repeated and reordered scopes.
        return z3.substitute(template,*zip(columns,xs))
    def objectives_xml(self,e):
        attrs(e,{'combination'});need(e.get('combination','lexico')=='lexico','non-lex objective combination');need(len(e)<=1,'multiple objectives not yet supported')
        for objective in e:
            attrs(objective,{'type'});need(objective.tag in ['minimize','maximize'],'objective kind');kind=objective.get('type','expression')
            if kind=='expression':need(not list(objective),'nested expression objective');value=arithmetic(self.expression(expr_text(objective)))
            else:
                children(objective,{'list','coeffs'});ls=one(objective,'list',False);xs=self.terms(ls) if ls is not None else [arithmetic(x) for x in self.expressions((objective.text or '').strip())];cs=one(objective,'coeffs',False)
                if cs is not None:
                    coeff=self.terms(cs);need(len(coeff)==len(xs),'objective coefficient arity');xs=[a*b for a,b in zip(xs,coeff)]
                if kind=='sum':value=z3.Sum(*xs)
                elif kind=='product':
                    value=z3.IntVal(1)
                    for x in xs:value=value*x
                elif kind in ['minimum','maximum']:
                    need(bool(xs),'empty minimum/maximum objective');value=xs[0]
                    for x in xs[1:]:value=z3.If(value<=x if kind=='minimum' else value>=x,value,x)
                else:raise Unsupported('objective type '+kind)
            self.objectives.append((objective.tag,value))
    def read(self,xml):
        root=ET.fromstring(xml);attrs(root,{'format','type'});need(root.tag=='instance' and root.get('format')=='XCSP3' and root.get('type') in ['CSP','COP'],'XCSP3 CSP/COP required');children(root,{'variables','constraints','objectives','annotations'})
        self.variables_xml(one(root,'variables'));constraints=one(root,'constraints',False)
        if constraints is not None:self.constraint(constraints)
        objectives=one(root,'objectives',False)
        if objectives is not None:self.objectives_xml(objectives)
        need((root.get('type')=='CSP')==(not bool(self.objectives)),'framework/objective mismatch')
        return Source(self.variables,self.domains,self.constraints,self.objectives,self.constraint_count,root.get('type'),self.reference_profile,tuple(self.private_variables))

def read_source(xml,*,reference_profile=None,circuit_witness='successor-walk',cumulative_encoding='event-points'):return Reader(reference_profile=reference_profile,circuit_witness=circuit_witness,cumulative_encoding=cumulative_encoding).read(xml)
