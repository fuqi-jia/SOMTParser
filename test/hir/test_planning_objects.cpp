#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/planning_objects.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
namespace U = SOMTParser::Uir;
using Policy = P::ObjectAssignmentPolicy;
using Undefined = P::ObjectUndefinedPolicy;

struct Fixture {
    P::ObjectUniverse universe{{{"node", {}}, {"place", {}}, {"empty", {}}},
                              {{"a", "node"}, {"b", "node"}, {"p", "place"}}};
    P::ObjectType node{{"node"}};
    H::ConstraintModel model;
    U::Diagnostics diagnostics;
    std::vector<P::ObjectStateCell> before, after;
    H::ExprPtr a, b, observed, observed_defined, observed_int, observed_real;
    Fixture() {
        const auto var = [&](const std::string& name, H::Sort sort) {
            model.decls.push_back({name, sort, {}, {}, {}});
            return H::mkIdent(name, sort);
        };
        for (const auto* name : {"x", "y", "z"}) {
            const auto cell = [&](const std::string& prefix) {
                const std::string value = prefix + name;
                return P::ObjectStateCell{var(value, H::Sort::integer()),
                    var(value + "d", H::Sort::boolean()), node};
            };
            before.push_back(cell("")); after.push_back(cell("n"));
        }
        a = var("a", H::Sort::boolean()); b = var("b", H::Sort::boolean());
        observed = var("observed", H::Sort::boolean());
        observed_defined = var("observed_defined", H::Sort::boolean());
        observed_int = var("observed_int", H::Sort::integer());
        observed_real = var("observed_real", H::Sort::real());
    }
    void add(const H::ExprPtr& e) { H::Constraint c; c.formula=e; model.constraints.push_back(c); }
    void add(const std::vector<H::ExprPtr>& es) { for (const auto& e:es) add(e); }
    void equal(const H::ExprPtr& a,const H::ExprPtr& b) { add(H::mkOp(H::Op::EQ,{a,b})); }
    P::ObjectValue read(std::size_t i) {
        auto r=P::objectRead(universe,before[i],i,diagnostics);VERIFY(r);return *r;
    }
    P::ObjectValue constant(const std::string& name) {
        auto r=P::objectConstant(universe,name,diagnostics);VERIFY(r);return *r;
    }
    P::ObjectTable table() const { return {{node}, {{0},{1}}}; }
    P::ObjectAddress address(std::size_t i) {
        auto r=P::objectAddress(model,universe,{{},{{}}},{},{i},diagnostics);VERIFY(r);return *r;
    }
    P::ObjectAddress dynamic(const P::ObjectValue& v) {
        auto r=P::objectAddress(model,universe,table(),{v},{0,1},diagnostics);VERIFY(r);return *r;
    }
    P::ObjectValue lookup(const P::ObjectValue& v) {
        auto r=P::objectLookup(model,universe,table(),{v},{read(0),read(1)},node,diagnostics);VERIFY(r);return *r;
    }
    void transition(const std::vector<P::ObjectUpdate>& us,Policy policy=Policy::SINGLE_WRITER) {
        auto r=P::buildObjectTransition(model,universe,before,after,us,policy,diagnostics);VERIFY(r);add(r->constraints);
    }
    void observe(const P::ObjectValue& v) { add(v.constraints);equal(observed_int,v.value);equal(observed_defined,v.defined); }
    void observe(const P::ObjectCondition& c) { add(c.constraints);equal(observed,c.value);equal(observed_defined,c.defined); }
    void emit(const std::filesystem::path& dir,const std::string& name) {
        VERIFY(H::typeCheck(model,diagnostics));auto parser=SOMTParser::newParser();
        SOMTParser::Lower::HirToParser lower(parser);U::TranslationReport report;
        VERIFY(lower.lower(model,report,diagnostics));auto smt=parser->dumpSMT2();VERIFY(!smt.empty());
        if(!dir.empty())std::ofstream(dir/(name+".smt2"))<<smt;
    }
};

int main(int argc,char** argv) {
    {
        P::ObjectUniverse universe;
        constexpr std::size_t depth=20000;
        for(std::size_t i=0;i<depth;++i) {
            universe.types.push_back({"type"+std::to_string(i),
                {i+1==depth ? "object" : "type"+std::to_string(i+1)}});
        }
        // Multiple children sharing a completed ancestor are not a cycle.
        universe.types.push_back({"diamond", {"type0", "type1"}});
        U::Diagnostics diagnostics;
        VERIFY(P::validateObjectUniverse(universe,diagnostics));
        universe.types[depth-1].parents={"type0"};
        VERIFY(!P::validateObjectUniverse(universe,diagnostics));
    }
    const std::filesystem::path dir=argc==2?argv[1]:"";
    if(!dir.empty())std::filesystem::create_directories(dir);
    std::vector<std::string> refusals;
    const auto refused=[&](bool r,const std::string& name){VERIFY(r);refusals.push_back(name);};
    {
        Fixture f;auto r=P::initialObjectState(f.model,f.universe,f.before,{{1,1}},f.diagnostics);VERIFY(r);
        f.add(r->constraints);f.transition({});f.emit(dir,"initial");
    }
    { Fixture f;f.transition({});f.emit(dir,"frame"); }
    { Fixture f;f.transition({{f.address(0),f.constant("b"),f.a}});f.emit(dir,"constant"); }
    { Fixture f;f.transition({{f.address(0),std::nullopt,f.a}});f.emit(dir,"undefined"); }
    { Fixture f;f.transition({{f.address(0),f.read(1),f.a},{f.address(1),f.read(0),f.a}});f.emit(dir,"swap"); }
    { Fixture f;f.transition({{f.address(2),f.lookup(f.lookup(f.read(2))),f.a}});f.emit(dir,"nested"); }
    { Fixture f;f.transition({{f.dynamic(f.read(2)),f.constant("b"),f.a}});f.emit(dir,"dynamic_address"); }
    { Fixture f;f.transition({{f.dynamic(f.read(2)),f.constant("a"),f.a},{f.address(2),f.constant("b"),f.a}});f.emit(dir,"old_address"); }
    { Fixture f;f.transition({{f.dynamic(f.read(2)),f.constant("a"),f.a},{f.dynamic(f.read(1)),f.constant("a"),f.b}});f.emit(dir,"alias_conflict"); }
    { Fixture f;f.transition({{f.dynamic(f.read(2)),f.constant("a"),f.a},{f.dynamic(f.read(1)),f.constant("a"),f.b}},Policy::AGREEING_WRITERS);f.emit(dir,"alias_agree"); }
    { Fixture f;f.transition({{f.address(0),f.constant("a"),f.a},{f.address(0),f.constant("b"),f.b}},Policy::AGREEING_WRITERS);f.emit(dir,"value_conflict"); }
    { Fixture f;f.transition({{f.address(0),std::nullopt,f.a},{f.address(0),std::nullopt,f.b}},Policy::AGREEING_WRITERS);f.emit(dir,"undefined_agree"); }
    { Fixture f;f.transition({{f.address(0),std::nullopt,f.a},{f.address(0),f.constant("a"),f.b}},Policy::AGREEING_WRITERS);f.emit(dir,"undefined_conflict"); }
    for (const auto p:{Undefined::STRICT,Undefined::ATOMIC_FALSE}) {
        const std::string suffix=p==Undefined::STRICT?"strict":"atomic_false";
        {
            Fixture f;auto c=P::objectEqual(f.universe,f.read(2),f.constant("a"),p,f.diagnostics);VERIFY(c);
            auto n=P::objectLogical(H::Op::NOT,{*c},f.diagnostics);VERIFY(n);f.observe(*n);f.transition({});f.emit(dir,"not_"+suffix);
        }
        {
            Fixture f;auto c=P::objectEqual(f.universe,f.read(2),f.constant("a"),p,f.diagnostics);VERIFY(c);
            auto o=P::objectLogical(H::Op::OR,{{H::mkBool(true),H::mkBool(true),{},{}},*c},f.diagnostics);VERIFY(o);
            f.observe(*o);f.transition({});f.emit(dir,"or_"+suffix);
        }
        {
            Fixture f;auto c=P::objectPredicate(f.model,f.universe,f.table(),{f.lookup(f.read(2))},
                {H::mkBool(false),H::mkBool(true)},p,f.diagnostics);VERIFY(c);
            f.observe(*c);f.transition({});f.emit(dir,"predicate_"+suffix);
        }
    }
    {
        Fixture f;auto n=P::objectNumericLookup(f.model,f.universe,f.table(),{f.lookup(f.read(2))},
            {{H::mkReal("1/3"),H::mkBool(true),{}},{H::mkReal("2/3"),H::mkBool(true),{}}},f.diagnostics);VERIFY(n);
        f.add(n->constraints);f.equal(f.observed_real,n->numeric.value);f.equal(f.observed_defined,n->numeric.defined);
        f.transition({});f.emit(dir,"numeric_arguments");
    }
    {
        Fixture f;auto n=P::objectNumericLookup(f.model,f.universe,f.table(),{f.read(2)},
            {{H::mkReal("1/3"),H::mkBool(true),{}},{H::mkReal("0"),H::mkBool(false),{}}},f.diagnostics);VERIFY(n);
        f.add(n->constraints);f.equal(f.observed_real,n->numeric.value);f.equal(f.observed_defined,n->numeric.defined);
        f.transition({});f.emit(dir,"numeric_undefined");
    }
    {
        Fixture f;f.before[2].type=f.after[2].type={{"node","place"}};
        f.transition({{f.address(2),f.constant("p"),f.a}});f.emit(dir,"union_assignment");
    }
    {
        Fixture f;f.before[2].type=f.after[2].type={{"empty"}};
        auto v=P::objectLookup(f.model,f.universe,P::ObjectTable{{P::ObjectType{{"empty"}}},{}},{f.read(2)},{},f.node,f.diagnostics);VERIFY(v);
        f.observe(*v);f.transition({});f.emit(dir,"empty_carrier");
    }
    {
        Fixture f;auto v=P::objectLookup(f.model,f.universe,{{},{{}}},{},{f.read(1)},f.node,f.diagnostics);VERIFY(v);
        f.observe(*v);f.transition({});f.emit(dir,"nullary");
    }
    {
        Fixture f;f.universe.types.push_back({"special",{"node"}});f.universe.objects.push_back({"s","special"});
        auto carrier=P::objectCarrier(f.universe,{{"node","place"}},f.diagnostics);VERIFY(carrier&&*carrier==std::vector<std::size_t>({0,1,2,3}));
        auto sub=P::objectSubtype(f.universe,{{"special","place"}},{{"node","place"}},f.diagnostics);VERIFY(sub&&*sub);
        auto wrong=P::objectSubtype(f.universe,{{"empty"}},{{"node"}},f.diagnostics);VERIFY(wrong&&!*wrong);
    }
    {
        Fixture f;refused(!P::objectConstant(f.universe,"undefined",f.diagnostics),"undefined_is_not_a_term");
    }
    {
        Fixture f;auto u=f.universe;u.types.push_back({"cycle",{"cycle"}});
        refused(!P::validateObjectUniverse(u,f.diagnostics),"type_cycle");
    }
    {
        Fixture f;auto u=f.universe;u.objects.push_back({"a","node"});
        refused(!P::validateObjectUniverse(u,f.diagnostics),"duplicate_object");
    }
    {
        Fixture f;refused(!P::objectCarrier(f.universe,{{"missing"}},f.diagnostics),"unknown_union_member");
    }
    {
        Fixture f;refused(!P::objectDispatch(f.model,f.universe,{{f.node},{{0}}},{f.read(2)},f.diagnostics),"missing_table_row");
    }
    {
        Fixture f;refused(!P::objectDispatch(f.model,f.universe,{{f.node},{{0},{1},{1}}},{f.read(2)},f.diagnostics),"duplicate_table_row");
    }
    {
        Fixture f;refused(!P::objectDispatch(f.model,f.universe,{{f.node},{{0},{2}}},{f.read(2)},f.diagnostics),"wrong_type_table_row");
    }
    {
        Fixture f;refused(!P::objectDispatch(f.model,f.universe,f.table(),{f.constant("p")},f.diagnostics),"wrong_argument_type");
    }
    {
        Fixture f;refused(!P::objectLookup(f.model,f.universe,f.table(),{f.read(2)},
            {f.constant("a"),f.constant("p")},f.node,f.diagnostics),"wrong_return_type");
    }
    {
        Fixture f;refused(!P::objectAddress(f.model,f.universe,f.table(),{f.read(2)},{0,0},f.diagnostics),"aliased_ground_cells");
    }
    {
        Fixture f;refused(!P::initialObjectState(f.model,f.universe,f.before,{{0,0},{0,0}},f.diagnostics),"duplicate_initialization");
    }
    {
        Fixture f;refused(!P::initialObjectState(f.model,f.universe,f.before,{{0,2}},f.diagnostics),"wrong_initial_type");
    }
    {
        Fixture f;refused(!P::buildObjectTransition(f.model,f.universe,f.before,f.after,
            {{f.address(0),f.constant("p"),H::mkBool(false)}},Policy::SINGLE_WRITER,f.diagnostics),"inactive_wrong_assignment_type");
    }
    {
        Fixture f;auto bad=f.constant("a");bad.value=H::mkReal("1");
        refused(!P::buildObjectTransition(f.model,f.universe,f.before,f.after,
            {{f.address(0),bad,H::mkBool(false)}},Policy::SINGLE_WRITER,f.diagnostics),"inactive_wrong_sort");
    }
    {
        Fixture f;auto bad=f.read(1);bad.reads.clear();
        refused(!P::buildObjectTransition(f.model,f.universe,f.before,f.after,
            {{f.address(0),bad,f.a}},Policy::SINGLE_WRITER,f.diagnostics),"missing_read_metadata");
    }
    for(const bool active:{false,true}) {
        Fixture f;H::FunDecl hidden{"hidden",{},H::Sort::integer(),{}};hidden.body=f.after[0].value;
        f.model.funs.push_back(hidden);auto bad=f.constant("a");bad.value=H::mkApply("hidden",H::Sort::integer(),{});
        refused(!P::buildObjectTransition(f.model,f.universe,f.before,f.after,
            {{f.address(0),bad,H::mkBool(active)}},Policy::SINGLE_WRITER,f.diagnostics),
            active?"future_hidden_active":"future_hidden_inactive");
    }
    {
        Fixture f;auto bad=f.address(0);bad.cells[0]=7;
        refused(!P::buildObjectTransition(f.model,f.universe,f.before,f.after,
            {{bad,f.constant("a"),f.a}},Policy::SINGLE_WRITER,f.diagnostics),"invalid_target_cell");
    }
    {
        Fixture f;auto bad=f.read(0);bad.value=H::mkIdent("not_declared",H::Sort::integer());
        refused(!P::objectDispatch(f.model,f.universe,f.table(),{bad},f.diagnostics),"unbound_table_argument");
    }
    {
        Fixture f;auto bad=f.read(0);bad.value=H::mkBoundVar("unbound",H::Sort::integer());
        refused(!P::objectDispatch(f.model,f.universe,f.table(),{bad},f.diagnostics),"free_bound_variable");
    }
    if(!dir.empty()) {
        std::ofstream out(dir/"object-refusals.json");out<<"{\"passed\":true,\"cases\":[";
        for(std::size_t i=0;i<refusals.size();++i){if(i)out<<',';out<<'"'<<refusals[i]<<'"';}out<<"]}\n";
    }
    std::cout<<"planning object API constructions and "<<refusals.size()<<" refusals passed\n";
    return 0;
}
