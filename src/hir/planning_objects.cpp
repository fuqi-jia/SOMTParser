#include "somtparser/hir/planning_objects.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <unordered_set>

namespace SOMTParser::Uir::Hir::Planning {
namespace {
bool fail(Diagnostics& d, const std::string& s) { d.error(ErrorCode::E_TYPE, "planning objects: " + s); return false; }
ExprPtr all(std::vector<ExprPtr> a) { return a.empty() ? mkBool(true) : a.size()==1 ? a[0] : mkOp(Op::AND,std::move(a)); }
ExprPtr any(std::vector<ExprPtr> a) { return a.empty() ? mkBool(false) : a.size()==1 ? a[0] : mkOp(Op::OR,std::move(a)); }
ExprPtr eq(ExprPtr a, ExprPtr b) { return mkOp(Op::EQ,{std::move(a),std::move(b)}); }
ExprPtr neg(ExprPtr a) { return mkOp(Op::NOT,{std::move(a)}); }
ExprPtr imp(ExprPtr a, ExprPtr b) { return mkOp(Op::IMPLIES,{std::move(a),std::move(b)}); }
ExprPtr code(std::size_t i) { return mkInt(std::to_string(i+1)); }
bool sorted(const ExprPtr& p, SortKind s) { return p && p->sort.kind==s; }
void append(std::vector<ExprPtr>& a, const std::vector<ExprPtr>& b) { a.insert(a.end(),b.begin(),b.end()); }
void append(std::vector<ObjectReadAccess>& a, const std::vector<ObjectReadAccess>& b, ExprPtr guard=mkBool(true)) {
    for (const auto& r:b) { a.push_back({r.cell,all({guard,r.when})}); }
}
using Parents=std::map<std::string,std::vector<std::string>>;
Parents parents(const ObjectUniverse& u) {
    Parents p{{"object",{}}};
    for (const auto& t:u.types) { p.emplace(t.name,t.parents.empty()?std::vector<std::string>{"object"}:t.parents); }
    return p;
}
bool sub(const Parents& p,const std::string& a,const std::string& b) {
    std::vector<std::string> todo{a}; std::set<std::string> seen;
    while (!todo.empty()) { auto n=todo.back();todo.pop_back(); if(n==b)return true;
        if(seen.insert(n).second) { auto it=p.find(n);if(it!=p.end())todo.insert(todo.end(),it->second.begin(),it->second.end()); }
    } return false;
}
bool type(const ObjectUniverse& u,const ObjectType& t,Diagnostics& d) {
    auto p=parents(u);std::set<std::string> seen;
    if(t.alternatives.empty())return fail(d,"empty type union");
    for(const auto& a:t.alternatives)if(!p.count(a)||!seen.insert(a).second)return fail(d,"unknown or repeated type union member");
    return true;
}
bool shape(const ObjectUniverse& u,const ObjectValue& v,Diagnostics& d) {
    if(!sorted(v.value,SortKind::INT)||!sorted(v.defined,SortKind::BOOL)||!type(u,v.type,d))return fail(d,"object value requires Int code, Bool definedness and a known type");
    for(const auto& r:v.reads)if(!sorted(r.when,SortKind::BOOL))return fail(d,"read guard must be Bool");
    for(const auto& c:v.constraints)if(!sorted(c,SortKind::BOOL))return fail(d,"object obligation must be Bool");
    return true;
}
ExprPtr membership(const ObjectUniverse& u,ExprPtr value,const ObjectType& t) {
    auto p=parents(u);std::vector<ExprPtr> m;
    for(std::size_t i=0;i<u.objects.size();++i)for(const auto& a:t.alternatives)if(sub(p,u.objects[i].type,a)){m.push_back(eq(value,code(i)));break;}
    return any(std::move(m));
}
void obligations(const ObjectUniverse& u,const ObjectValue& v,std::vector<ExprPtr>& out) {
    append(out,v.constraints);
    out.push_back(imp(v.defined,membership(u,v.value,v.type)));
    out.push_back(imp(neg(v.defined),eq(v.value,mkInt(0))));
}
bool typed(const ConstraintModel& context,const std::vector<ExprPtr>& terms,Diagnostics& d) {
    std::vector<LocatedExpr> located; for(const auto& t:terms)located.push_back({t,{}});
    return typeCheckTerms(context,located,d);
}
void valueTerms(const ObjectValue& v,std::vector<ExprPtr>& ts) {
    ts.push_back(v.value);ts.push_back(v.defined);append(ts,v.constraints);
    for(const auto& r:v.reads)ts.push_back(r.when);
}
bool conditionShape(const ObjectCondition& c,Diagnostics& d) {
    if(!sorted(c.value,SortKind::BOOL)||!sorted(c.defined,SortKind::BOOL))return fail(d,"condition requires Bool value and definedness");
    for(const auto& r:c.reads)if(!sorted(r.when,SortKind::BOOL))return fail(d,"condition read guard must be Bool");
    for(const auto& x:c.constraints)if(!sorted(x,SortKind::BOOL))return fail(d,"condition obligation must be Bool");
    return true;
}
bool policy(ObjectUndefinedPolicy p,Diagnostics& d) {
    return p==ObjectUndefinedPolicy::STRICT||p==ObjectUndefinedPolicy::ATOMIC_FALSE||fail(d,"invalid undefined policy");
}
ObjectCondition totalize(ObjectCondition c,ObjectUndefinedPolicy p) {
    if(p==ObjectUndefinedPolicy::ATOMIC_FALSE){c.value=all({c.defined,c.value});c.defined=mkBool(true);}return c;
}
bool cellShape(const ObjectUniverse& u,const ObjectStateCell& c,Diagnostics& d) {
    return shape(u,{c.value,c.defined,c.type,{},{}},d)
        && ((c.value->kind==ExprKind::IDENT&&c.defined->kind==ExprKind::IDENT)||fail(d,"state cell must use identifiers"));
}
bool stateShapes(const ConstraintModel& context,const ObjectUniverse& u,const std::vector<ObjectStateCell>& cells,Diagnostics& d) {
    std::vector<ExprPtr> terms; std::set<std::string> names;
    for(const auto& c:cells){if(!cellShape(u,c,d))return false;
        for(const auto& t:{c.value,c.defined}){if(!names.insert(t->name).second)return fail(d,"aliased state identifiers");terms.push_back(t);}}
    return typed(context,terms,d);
}
} // namespace

bool validateObjectUniverse(const ObjectUniverse& u,Diagnostics& d) {
    std::set<std::string> names{"object"};
    for(const auto& t:u.types)if(t.name.empty()||t.name=="number"||!names.insert(t.name).second)return fail(d,"invalid or duplicate type");
    const auto p=parents(u);
    for(const auto& t:u.types){std::set<std::string> seen;for(const auto& a:t.parents)
        if(!p.count(a)||!seen.insert(a).second)return fail(d,"unknown or duplicate supertype");}
    std::map<std::string,int> color;
    struct Frame { std::string name; std::size_t next = 0; };
    for(const auto& t:p) {
        if(color[t.first]==2) continue;
        std::vector<Frame> pending{{t.first}};
        color[t.first]=1;
        while(!pending.empty()) {
            auto& frame=pending.back();
            const auto& ancestors=p.at(frame.name);
            if(frame.next==ancestors.size()) {
                color[frame.name]=2;
                pending.pop_back();
                continue;
            }
            const auto& ancestor=ancestors[frame.next++];
            if(color[ancestor]==1) return fail(d,"cyclic type hierarchy");
            if(color[ancestor]==2) continue;
            color[ancestor]=1;
            pending.push_back({ancestor});
        }
    }
    names.clear();for(const auto& o:u.objects)
        if(o.name.empty()||o.name=="undefined"||!names.insert(o.name).second||!p.count(o.type))return fail(d,"invalid, duplicate or untyped object");
    return true;
}
std::optional<bool> objectSubtype(const ObjectUniverse& u,const ObjectType& a,const ObjectType& b,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||!type(u,a,d)||!type(u,b,d))return std::nullopt;
    const auto p=parents(u);for(const auto& x:a.alternatives){bool found=false;for(const auto& y:b.alternatives)found=found||sub(p,x,y);if(!found)return false;}return true;
}
std::optional<std::vector<std::size_t>> objectCarrier(const ObjectUniverse& u,const ObjectType& t,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||!type(u,t,d))return std::nullopt;
    const auto p=parents(u);std::vector<std::size_t> out;
    for(std::size_t i=0;i<u.objects.size();++i) {
        for(const auto& a:t.alternatives) {
            if(sub(p,u.objects[i].type,a)){out.push_back(i);break;}
        }
    }
    return out;
}
std::optional<ObjectValue> objectConstant(const ObjectUniverse& u,const std::string& name,Diagnostics& d) {
    if(!validateObjectUniverse(u,d))return std::nullopt;
    for(std::size_t i=0;i<u.objects.size();++i)if(u.objects[i].name==name)return ObjectValue{code(i),mkBool(true),{{u.objects[i].type}},{},{}};
    fail(d,"unknown object constant (undefined is not a term)");return std::nullopt;
}
std::optional<ObjectValue> objectRead(const ObjectUniverse& u,const ObjectStateCell& c,std::size_t i,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||!cellShape(u,c,d))return std::nullopt;
    ObjectValue v{c.value,c.defined,c.type,{{i,mkBool(true)}},{}};
    std::vector<ExprPtr> constraints;obligations(u,v,constraints);v.constraints=std::move(constraints);return v;
}
std::optional<ObjectCondition> objectEqual(const ObjectUniverse& u,const ObjectValue& a,const ObjectValue& b,ObjectUndefinedPolicy p,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||!shape(u,a,d)||!shape(u,b,d)||!policy(p,d))return std::nullopt;
    ObjectCondition c{eq(a.value,b.value),all({a.defined,b.defined}),{}, {}};
    append(c.reads,a.reads);append(c.reads,b.reads);obligations(u,a,c.constraints);obligations(u,b,c.constraints);
    return totalize(std::move(c),p);
}
std::optional<ObjectCondition> objectLogical(Op op,const std::vector<ObjectCondition>& args,Diagnostics& d) {
    if((op!=Op::AND&&op!=Op::OR&&op!=Op::NOT&&op!=Op::IMPLIES)||(op==Op::NOT&&args.size()!=1)||(op==Op::IMPLIES&&args.size()!=2)){fail(d,"bad logical operator/arity");return std::nullopt;}
    std::vector<ExprPtr> vs,ds;ObjectCondition out;
    for(const auto& a:args){if(!conditionShape(a,d))return std::nullopt;vs.push_back(a.value);ds.push_back(a.defined);append(out.reads,a.reads);append(out.constraints,a.constraints);}
    out.value=op==Op::AND?all(std::move(vs)):op==Op::OR?any(std::move(vs)):mkOp(op,std::move(vs));out.defined=all(std::move(ds));return out;
}
ExprPtr objectSatisfied(const ObjectCondition& c) { return all({c.defined,c.value}); }

std::optional<ObjectDispatch> objectDispatch(const ConstraintModel& context,const ObjectUniverse& u,
    const ObjectTable& table,const std::vector<ObjectValue>& args,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||table.parameters.size()!=args.size()){fail(d,"table argument arity mismatch");return std::nullopt;}
    std::vector<std::vector<std::size_t>> carriers;std::vector<ExprPtr> terms,defined;
    ObjectDispatch out;
    for(std::size_t i=0;i<args.size();++i){auto c=objectCarrier(u,table.parameters[i],d);auto s=objectSubtype(u,args[i].type,table.parameters[i],d);
        if(!c||!s||!*s||!shape(u,args[i],d)){fail(d,"ill-typed table argument");return std::nullopt;}
        carriers.push_back(*c);defined.push_back(args[i].defined);append(out.reads,args[i].reads);obligations(u,args[i],out.constraints);valueTerms(args[i],terms);}
    std::set<std::vector<std::size_t>> rows;
    for(const auto& row:table.rows){if(row.size()!=args.size()||!rows.insert(row).second){fail(d,"duplicate or wrong-arity table row");return std::nullopt;}
        for(std::size_t i=0;i<row.size();++i)if(std::find(carriers[i].begin(),carriers[i].end(),row[i])==carriers[i].end()){fail(d,"table row outside parameter carrier");return std::nullopt;}}
    std::vector<std::size_t> tuple;bool complete=true;
    std::function<void(std::size_t)> visit=[&](std::size_t at){if(!complete)return;if(at==carriers.size()){complete=rows.count(tuple)!=0;return;}
        for(auto i:carriers[at]){tuple.push_back(i);visit(at+1);tuple.pop_back();}};visit(0);
    if(!complete){fail(d,"incomplete finite table");return std::nullopt;}
    if(!typed(context,terms,d))return std::nullopt;
    out.defined=all(std::move(defined));
    for(const auto& row:table.rows){std::vector<ExprPtr> matches{out.defined};for(std::size_t i=0;i<row.size();++i)matches.push_back(eq(args[i].value,code(row[i])));out.matches.push_back(all(std::move(matches)));}
    return out;
}
std::optional<ObjectValue> objectLookup(const ConstraintModel& context,const ObjectUniverse& u,
    const ObjectTable& table,const std::vector<ObjectValue>& args,const std::vector<ObjectValue>& values,
    const ObjectType& result_type,Diagnostics& d) {
    auto dispatch=objectDispatch(context,u,table,args,d);if(!dispatch)return std::nullopt;
    if(values.size()!=table.rows.size()||!type(u,result_type,d)){fail(d,"object table result count/type mismatch");return std::nullopt;}
    ObjectValue out{mkInt(0),mkBool(false),result_type,dispatch->reads,dispatch->constraints};std::vector<ExprPtr> defs,terms;
    for(std::size_t i=0;i<values.size();++i){const auto& v=values[i];auto s=objectSubtype(u,v.type,result_type,d);
        if(!s||!*s||!shape(u,v,d)){fail(d,"object table result type mismatch");return std::nullopt;}
        const auto chosen=all({dispatch->matches[i],v.defined});defs.push_back(chosen);out.value=mkOp(Op::ITE,{chosen,v.value,out.value});
        append(out.reads,v.reads,dispatch->matches[i]);obligations(u,v,out.constraints);valueTerms(v,terms);}
    if(!typed(context,terms,d))return std::nullopt;
    out.defined=any(std::move(defs));return out;
}
std::optional<ObjectCondition> objectPredicate(const ConstraintModel& context,const ObjectUniverse& u,
    const ObjectTable& table,const std::vector<ObjectValue>& args,const std::vector<ExprPtr>& values,
    ObjectUndefinedPolicy p,Diagnostics& d) {
    auto dispatch=objectDispatch(context,u,table,args,d);if(!dispatch||!policy(p,d))return std::nullopt;
    if(values.size()!=table.rows.size()){fail(d,"predicate table result count mismatch");return std::nullopt;}
    std::vector<ExprPtr> ts;for(std::size_t i=0;i<values.size();++i){if(!sorted(values[i],SortKind::BOOL)){fail(d,"predicate row must be Bool");return std::nullopt;}ts.push_back(all({dispatch->matches[i],values[i]}));}
    if(!typed(context,values,d))return std::nullopt;
    return totalize({any(std::move(ts)),dispatch->defined,dispatch->reads,dispatch->constraints},p);
}
std::optional<ObjectNumericValue> objectNumericLookup(const ConstraintModel& context,const ObjectUniverse& u,
    const ObjectTable& table,const std::vector<ObjectValue>& args,const std::vector<NumericValue>& values,Diagnostics& d) {
    auto dispatch=objectDispatch(context,u,table,args,d);if(!dispatch)return std::nullopt;
    if(values.size()!=table.rows.size()){fail(d,"numeric table result count mismatch");return std::nullopt;}
    ObjectNumericValue out{{mkReal("0"),mkBool(false),{}},dispatch->reads,{},dispatch->constraints};std::vector<ExprPtr> defs,terms;
    for(std::size_t i=0;i<values.size();++i){const auto& v=values[i];if(!sorted(v.value,SortKind::REAL)||!sorted(v.defined,SortKind::BOOL)){fail(d,"numeric row must have Real/Bool fields");return std::nullopt;}
        const auto chosen=all({dispatch->matches[i],v.defined});defs.push_back(chosen);out.numeric.value=mkOp(Op::ITE,{chosen,v.value,out.numeric.value});
        out.numeric.reads.insert(out.numeric.reads.end(),v.reads.begin(),v.reads.end());
        for(const auto index:v.reads) { out.numeric_reads.push_back({index,dispatch->matches[i]}); }
        terms.push_back(v.value);terms.push_back(v.defined);}
    if(!typed(context,terms,d))return std::nullopt;
    out.numeric.defined=any(std::move(defs));
    std::sort(out.numeric.reads.begin(),out.numeric.reads.end());out.numeric.reads.erase(std::unique(out.numeric.reads.begin(),out.numeric.reads.end()),out.numeric.reads.end());return out;
}
std::optional<ObjectAddress> objectAddress(const ConstraintModel& context,const ObjectUniverse& u,
    const ObjectTable& table,const std::vector<ObjectValue>& args,const std::vector<std::size_t>& cells,Diagnostics& d) {
    auto dispatch=objectDispatch(context,u,table,args,d);if(!dispatch)return std::nullopt;
    if(cells.size()!=table.rows.size()||std::set<std::size_t>(cells.begin(),cells.end()).size()!=cells.size()){fail(d,"object address table must map each tuple to a distinct cell");return std::nullopt;}
    return ObjectAddress{dispatch->defined,cells,dispatch->matches,dispatch->reads,dispatch->constraints};
}

std::optional<ObjectTransition> initialObjectState(const ConstraintModel& context,const ObjectUniverse& u,
    const std::vector<ObjectStateCell>& cells,const std::vector<std::pair<std::size_t,std::size_t>>& values,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||!stateShapes(context,u,cells,d))return std::nullopt;
    std::map<std::size_t,std::size_t> init;
    for(const auto& x:values){if(x.first>=cells.size()||x.second>=u.objects.size()||!init.emplace(x).second){fail(d,"invalid or repeated initialization");return std::nullopt;}
        auto s=objectSubtype(u,{{u.objects[x.second].type}},cells[x.first].type,d);if(!s||!*s){fail(d,"initial object has incompatible type");return std::nullopt;}}
    ObjectTransition out;
    for(std::size_t i=0;i<cells.size();++i){const auto& c=cells[i];const auto found=init.find(i);const bool defined=found!=init.end();
        out.constraints.push_back(eq(c.defined,mkBool(defined)));out.constraints.push_back(eq(c.value,defined?code(found->second):mkInt(0)));}
    return out;
}
std::optional<ObjectTransition> buildObjectTransition(const ConstraintModel& context,const ObjectUniverse& u,
    const std::vector<ObjectStateCell>& before,const std::vector<ObjectStateCell>& after,
    const std::vector<ObjectUpdate>& updates,ObjectAssignmentPolicy policy,Diagnostics& d) {
    if(!validateObjectUniverse(u,d)||before.size()!=after.size()){fail(d,"different state sizes");return std::nullopt;}
    if(policy!=ObjectAssignmentPolicy::SINGLE_WRITER&&policy!=ObjectAssignmentPolicy::AGREEING_WRITERS){fail(d,"invalid assignment policy");return std::nullopt;}
    std::vector<ObjectStateCell> combined=before;combined.insert(combined.end(),after.begin(),after.end());
    if(!stateShapes(context,u,combined,d))return std::nullopt;
    std::set<std::string> future;std::vector<ExprPtr> terms,pending;ObjectTransition out;
    struct Write { ExprPtr guard,value,defined; };std::vector<std::vector<Write>> writes(before.size());
    for(std::size_t i=0;i<before.size();++i){auto a=objectSubtype(u,before[i].type,after[i].type,d),b=objectSubtype(u,after[i].type,before[i].type,d);
        if(!a||!b||!*a||!*b){fail(d,"before/after cell types differ");return std::nullopt;}
        future.insert(after[i].value->name);future.insert(after[i].defined->name);
        obligations(u,{before[i].value,before[i].defined,before[i].type,{},{}},out.constraints);
        obligations(u,{after[i].value,after[i].defined,after[i].type,{},{}},out.constraints);}
    for(const auto& update:updates){const auto& target=update.target;
        if(!sorted(update.guard,SortKind::BOOL)||!sorted(target.defined,SortKind::BOOL)||target.cells.size()!=target.matches.size()) {fail(d,"malformed update/address");return std::nullopt;}
        terms.push_back(update.guard);terms.push_back(target.defined);append(terms,target.constraints);append(out.constraints,target.constraints);
        for(const auto& c:target.constraints)if(!sorted(c,SortKind::BOOL)){fail(d,"address obligation must be Bool");return std::nullopt;}
        for(const auto& r:target.reads){if(r.cell>=before.size()||!sorted(r.when,SortKind::BOOL)){fail(d,"invalid address read metadata");return std::nullopt;}terms.push_back(r.when);}
        if(update.rhs){if(!shape(u,*update.rhs,d))return std::nullopt;valueTerms(*update.rhs,terms);obligations(u,*update.rhs,out.constraints);
            for(const auto& r:update.rhs->reads)if(r.cell>=before.size()){fail(d,"invalid RHS read metadata");return std::nullopt;}}
        out.constraints.push_back(imp(update.guard,target.defined));
        // Validate even manually assembled addresses: exactly one selected cell
        // iff defined. A malformed address cannot make a firing effect vanish.
        out.constraints.push_back(eq(target.defined,any(target.matches)));
        for(std::size_t j=0;j<target.cells.size();++j){const auto i=target.cells[j];
            if(i>=before.size()||!sorted(target.matches[j],SortKind::BOOL)){fail(d,"invalid selected object cell");return std::nullopt;}
            terms.push_back(target.matches[j]);
            for(std::size_t k=0;k<j;++k)out.constraints.push_back(neg(all({target.matches[j],target.matches[k]})));
            if(update.rhs){auto sub=objectSubtype(u,update.rhs->type,before[i].type,d);if(!sub||!*sub){fail(d,"assigned object has incompatible type");return std::nullopt;}}
            const auto firing=all({update.guard,target.matches[j]});
            if(update.rhs)out.constraints.push_back(imp(firing,update.rhs->defined));
            writes[i].push_back({firing,update.rhs?update.rhs->value:mkInt(0),mkBool(bool(update.rhs))});}}
    if(!typed(context,terms,d))return std::nullopt;
    std::map<std::string,ExprPtr> bodies;for(const auto& f:context.funs)if(f.body)bodies.emplace(f.name,f.body);
    std::map<std::string,std::size_t> old_names;
    for(std::size_t i=0;i<before.size();++i){old_names.emplace(before[i].value->name,i);old_names.emplace(before[i].defined->name,i);}
    const auto checkReads=[&](std::vector<ExprPtr> queue,const std::vector<ObjectReadAccess>& reads){
        std::set<std::size_t> actual,declared;
        for(const auto& r:reads)declared.insert(r.cell);
        std::unordered_set<const Expr*> visited;
        while(!queue.empty()){auto t=queue.back();queue.pop_back();if(!visited.insert(t.get()).second)continue;
            if(t->kind==ExprKind::IDENT){const auto found=old_names.find(t->name);if(found!=old_names.end())actual.insert(found->second);}
            queue.insert(queue.end(),t->args.begin(),t->args.end());
            if(t->kind==ExprKind::APPLY){const auto f=bodies.find(t->name);if(f!=bodies.end())queue.push_back(f->second);}}
        return actual==declared||fail(d,"read metadata does not match old-state dependencies");
    };
    for(const auto& update:updates){
        std::vector<ExprPtr> address_terms{update.target.defined};append(address_terms,update.target.matches);append(address_terms,update.target.constraints);
        if(!checkReads(address_terms,update.target.reads))return std::nullopt;
        if(update.rhs){std::vector<ExprPtr> rhs_terms{update.rhs->value,update.rhs->defined};append(rhs_terms,update.rhs->constraints);
            if(!checkReads(rhs_terms,update.rhs->reads))return std::nullopt;}}
    pending=terms;std::unordered_set<const Expr*> seen;
    while(!pending.empty()){const auto t=pending.back();pending.pop_back();if(!seen.insert(t.get()).second)continue;
        if(t->kind==ExprKind::IDENT&&future.count(t->name)){fail(d,"simultaneous assignment reads successor state");return std::nullopt;}
        pending.insert(pending.end(),t->args.begin(),t->args.end());if(t->kind==ExprKind::APPLY){const auto f=bodies.find(t->name);if(f!=bodies.end())pending.push_back(f->second);}}
    for(std::size_t i=0;i<before.size();++i){ExprPtr value=before[i].value,defined=before[i].defined;
        for(std::size_t j=0;j<writes[i].size();++j){const auto& w=writes[i][j];for(std::size_t k=0;k<j;++k){const auto& v=writes[i][k];const auto both=all({w.guard,v.guard});
            out.constraints.push_back(policy==ObjectAssignmentPolicy::SINGLE_WRITER?neg(both):imp(both,all({eq(w.defined,v.defined),eq(w.value,v.value)})));}
            value=mkOp(Op::ITE,{w.guard,w.value,value});defined=mkOp(Op::ITE,{w.guard,w.defined,defined});}
        out.constraints.push_back(eq(after[i].defined,defined));out.constraints.push_back(eq(after[i].value,value));}
    return out;
}
} // namespace SOMTParser::Uir::Hir::Planning
