#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/planning_trajectory.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iostream>

namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
namespace U = SOMTParser::Uir;
using K = P::TrajectoryOperator;

struct Fixture {
    H::ConstraintModel model;
    U::Diagnostics diagnostics;
    H::ExprPtr declare(const std::string& name, H::Sort sort = H::Sort::boolean()) {
        model.decls.push_back({name, sort, {}, {}, {}}); return H::mkIdent(name,sort);
    }
    void assert_(H::ExprPtr term) { H::Constraint row;row.formula=term;model.constraints.push_back(row); }
    void encoded(const P::TrajectoryEncoding& encoding) {
        for (const auto& term:encoding.domain_constraints) {assert_(term);}
        assert_(H::mkOp(H::Op::EQ,{declare("result"),encoding.satisfied}));
    }
    void emit(const std::filesystem::path& directory,const std::string& name) {
        VERIFY(H::typeCheck(model,diagnostics));
        auto parser=SOMTParser::newParser();SOMTParser::Lower::HirToParser lower(parser);
        U::TranslationReport report;VERIFY(lower.lower(model,report,diagnostics));
        const auto target=parser->dumpSMT2();VERIFY(!target.empty());
        if (!directory.empty()) {std::ofstream(directory/(name+".smt2"))<<target;}
    }
};
H::ExprPtr binary(H::Op op,H::ExprPtr a,H::ExprPtr b) {return H::mkOp(op,{a,b});}
bool pair(K op) {return op==K::SOMETIME_BEFORE || op==K::SOMETIME_AFTER || op==K::ALWAYS_WITHIN;}
H::ExprPtr bound(K op) {
    return op==K::WITHIN || op==K::ALWAYS_WITHIN || op==K::HOLD_AFTER || op==K::HOLD_DURING ? H::mkReal("3") : nullptr;
}
const std::vector<std::pair<K,std::string>> operations{
    {K::AT_END,"end"},{K::ALWAYS,"always"},{K::SOMETIME,"sometime"},{K::WITHIN,"within"},
    {K::AT_MOST_ONCE,"once"},{K::SOMETIME_BEFORE,"before"},{K::SOMETIME_AFTER,"after"},
    {K::ALWAYS_WITHIN,"always_within"},{K::HOLD_DURING,"during"},{K::HOLD_AFTER,"hold_after"}};

int main(int argc,char**argv) {
    const std::filesystem::path directory=argc==2?argv[1]:"";
    if (!directory.empty()) {std::filesystem::create_directories(directory);}
    // Both implementations retain symbolic truth/definedness and prefix length.
    // The independent oracle checks their ENTIRE relation, not one satisfying plan.
    for (const auto& item:operations) {
        for (bool observed:{false,true}) {
            Fixture f;std::vector<P::TrajectorySample> samples;
            for (int i=0;i<4;++i) {
                const auto suffix=std::to_string(i);
                auto active=i?f.declare("a"+suffix):H::mkBool(true);
                P::TrajectorySample sample{active,H::mkReal(std::vector<std::string>{"0","2","5","9"}[i]),
                    {f.declare("p"+suffix),f.declare("d"+suffix),{}},std::nullopt};
                if (pair(item.first)) {sample.second=P::NumericCondition{f.declare("q"+suffix),f.declare("e"+suffix),{}};}
                samples.push_back(sample);
            }
            if (!observed) {
                auto result=P::encodeFiniteTrajectory(f.model,item.first,samples,bound(item.first),
                    item.first==K::HOLD_DURING?H::mkReal("8"):nullptr,f.diagnostics);
                VERIFY(result);f.encoded(*result);
            } else {
                auto t=H::mkBoundVar("time",H::Sort::real()),phase=H::mkBoundVar("phase",H::Sort::integer());
                std::vector<H::ExprPtr> members;auto last=H::mkReal("0");
                auto pv=H::mkBool(false),pd=H::mkBool(false),qv=H::mkBool(false),qd=H::mkBool(false);
                for (std::size_t i=0;i<samples.size();++i) {
                    const auto& sample=samples[i];auto here=binary(H::Op::EQ,t,sample.time);
                    members.push_back(H::mkOp(H::Op::AND,{sample.active,here,binary(H::Op::EQ,phase,H::mkInt(0))}));
                    pv=H::mkOp(H::Op::ITE,{here,sample.first.value,pv});pd=H::mkOp(H::Op::ITE,{here,sample.first.defined,pd});
                    if (sample.second) {qv=H::mkOp(H::Op::ITE,{here,sample.second->value,qv});qd=H::mkOp(H::Op::ITE,{here,sample.second->defined,qd});}
                    last=H::mkOp(H::Op::ITE,{sample.active,sample.time,last});
                    if (i) {f.assert_(binary(H::Op::IMPLIES,sample.active,samples[i-1].active));}
                }
                P::TrajectoryObservationDomain domain{"time","phase",H::mkOp(H::Op::OR,members),
                    {H::mkReal("0"),H::mkInt(0)},{last,H::mkInt(0)}};
                std::optional<P::NumericCondition> secondary;
                if (pair(item.first)) {secondary=P::NumericCondition{qv,qd,{}};}
                auto result=P::encodeObservedTrajectory(f.model,domain,item.first,{pv,pd,{}},secondary,
                    bound(item.first),item.first==K::HOLD_DURING?H::mkReal("8"):nullptr,f.diagnostics);
                VERIFY(result);f.encoded(*result);
            }
            f.emit(directory,(observed?"observed_":"finite_")+item.second);
        }
    }
    // Dense time witnesses cannot be recovered from endpoint sampling.
    for (const auto& name:{"dense_always","dense_sometime","dense_within","dense_once_gap","dense_once_interval",
                          "dense_undefined_tail","dense_during","dense_hold_after_strict","dense_hold_after_witness",
                          "dense_hold_after_fallback","dense_before_strict","dense_after_same","scope_shadow"}) {
        Fixture f;auto t=H::mkBoundVar("time",H::Sort::real()),phase=H::mkBoundVar("phase",H::Sort::integer());
        auto truth=H::mkBool(true);auto member=H::mkOp(H::Op::AND,{binary(H::Op::LE,H::mkReal("0"),t),
            binary(H::Op::LE,t,H::mkReal("2")),binary(H::Op::EQ,phase,H::mkInt(0))});
        P::TrajectoryObservationDomain domain{"time","phase",member,{H::mkReal("0"),H::mkInt(0)},{H::mkReal("2"),H::mkInt(0)}};
        auto at_one=binary(H::Op::EQ,t,H::mkReal("1"));auto not_one=H::mkOp(H::Op::NOT,{at_one});
        K op=K::ALWAYS;P::NumericCondition condition{not_one,truth,{}};
        std::optional<P::NumericCondition> second;H::ExprPtr lo,hi;std::string id=name;
        if (id=="dense_sometime") {op=K::SOMETIME;condition.value=at_one;}
        if (id=="dense_within") {op=K::WITHIN;condition.value=at_one;lo=H::mkReal("1");}
        if (id=="dense_once_gap") {op=K::AT_MOST_ONCE;}
        if (id=="dense_once_interval") {op=K::AT_MOST_ONCE;condition.value=binary(H::Op::LT,t,H::mkReal("1"));}
        if (id=="dense_undefined_tail") {op=K::AT_MOST_ONCE;condition.value=binary(H::Op::LT,t,H::mkReal("1"));condition.defined=not_one;}
        if (id=="dense_during") {op=K::HOLD_DURING;lo=H::mkReal("1/2");hi=H::mkReal("1");}
        if (id=="dense_hold_after_strict") {op=K::HOLD_AFTER;lo=H::mkReal("1");condition.value=at_one;}
        if (id=="dense_hold_after_witness") {op=K::HOLD_AFTER;lo=H::mkReal("1");condition.value=binary(H::Op::EQ,t,H::mkReal("3/2"));}
        if (id=="dense_hold_after_fallback") {op=K::HOLD_AFTER;lo=H::mkReal("3");condition.value=binary(H::Op::EQ,t,H::mkReal("2"));}
        if (id=="dense_before_strict" || id=="dense_after_same") {
            op=id=="dense_before_strict"?K::SOMETIME_BEFORE:K::SOMETIME_AFTER;
            condition.value=at_one;second=condition;
        }
        if (id=="scope_shadow") {
            f.declare("__trajectory_bound_0",H::Sort::real());
            condition.value=H::mkForall({{"time",H::Sort::real()}},binary(H::Op::EQ,t,t));
        }
        auto result=P::encodeObservedTrajectory(f.model,domain,op,condition,second,lo,hi,f.diagnostics);
        VERIFY(result);f.encoded(*result);f.emit(directory,id);
    }
    // Same time, explicitly ordered pre/post observations remain distinct.
    {
        Fixture f;auto t=H::mkBoundVar("t",H::Sort::real()),p=H::mkBoundVar("p",H::Sort::integer());
        auto at0=binary(H::Op::EQ,t,H::mkReal("0")),at1=binary(H::Op::EQ,t,H::mkReal("1"));
        auto pre=binary(H::Op::EQ,p,H::mkInt(-1)),post=binary(H::Op::EQ,p,H::mkInt(1));
        auto member=H::mkOp(H::Op::OR,{H::mkOp(H::Op::AND,{at0,binary(H::Op::EQ,p,H::mkInt(0))}),
            H::mkOp(H::Op::AND,{at1,H::mkOp(H::Op::OR,{pre,post})})});
        P::TrajectoryObservationDomain domain{"t","p",member,{H::mkReal("0"),H::mkInt(0)},{H::mkReal("1"),H::mkInt(1)}};
        auto result=P::encodeObservedTrajectory(f.model,domain,K::SOMETIME_BEFORE,{post,H::mkBool(true),{}},
            P::NumericCondition{pre,H::mkBool(true),{}},nullptr,nullptr,f.diagnostics);
        VERIFY(result);f.encoded(*result);f.emit(directory,"phase_order");
    }
    {
        Fixture f;auto a=f.declare("a"),b=f.declare("b"),on=f.declare("on");
        P::NumericCondition partial{a,b,{}};
        std::vector<P::PreferenceInstance> instances{
            {"outer-forall","outer",H::mkBool(true),H::mkOp(H::Op::AND,{a,b})},
            {"x=1","inner",H::mkBool(true),a},{"x=2","inner",H::mkBool(true),b},
            {"occurrence-1","pre",on,P::numericSatisfied(partial)},
            {"occurrence-2","pre",on,P::numericSatisfied(partial)},
            {"occurrence-3","pre",on,P::numericSatisfied(partial)},
            {"anonymous-1","",H::mkBool(true),a},{"anonymous-2","",on,b}};
        auto result=P::encodePreferences(f.model,instances,f.diagnostics);VERIFY(result);
        for (const auto& group:result->named_violations) {f.assert_(binary(H::Op::EQ,f.declare(group.first,H::Sort::integer()),group.second));}
        f.assert_(binary(H::Op::EQ,f.declare("anonymous",H::Sort::integer()),result->anonymous_violations));
        auto min=P::preferenceMetric(f.model,H::mkReal("3/2"),*result,true,f.diagnostics);
        auto max=P::preferenceMetric(f.model,H::mkInt(7),*result,false,f.diagnostics);VERIFY(min&&max);
        f.assert_(binary(H::Op::EQ,f.declare("min",H::Sort::real()),*min));
        f.assert_(binary(H::Op::EQ,f.declare("max",H::Sort::integer()),*max));f.emit(directory,"preferences");
        instances.push_back(instances.front());VERIFY(!P::encodePreferences(f.model,instances,f.diagnostics));
    }
    {
        Fixture f;auto empty=P::encodePreferences(f.model,{},f.diagnostics,{"empty_grounding"});VERIFY(empty);
        f.assert_(binary(H::Op::EQ,f.declare("zero",H::Sort::integer()),empty->anonymous_violations));
        f.assert_(binary(H::Op::EQ,f.declare("empty_group",H::Sort::integer()),empty->named_violations.at("empty_grounding")));
        f.emit(directory,"preferences_empty");
    }
    // Structural/type/scope refusals must not depend on an active branch.
    {
        Fixture f;auto t=H::mkBool(true);P::TrajectorySample s{t,H::mkReal("0"),{t,t,{}},std::nullopt};
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{},nullptr,nullptr,f.diagnostics));
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::WITHIN,{s},nullptr,nullptr,f.diagnostics));
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{s},H::mkReal("1"),nullptr,f.diagnostics));
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::SOMETIME_AFTER,{s},nullptr,nullptr,f.diagnostics));
        VERIFY(!P::encodeFiniteTrajectory(f.model,static_cast<K>(99),{s},nullptr,nullptr,f.diagnostics));
        s.second=s.first;VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{s},nullptr,nullptr,f.diagnostics));s.second.reset();
        s.active=H::mkBool(false);s.first.value=H::mkIdent("missing",H::Sort::boolean());
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{s},nullptr,nullptr,f.diagnostics));
        s.first.value=H::mkInt(1);VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{s},nullptr,nullptr,f.diagnostics));
        s.first.value=H::mkBoundVar("free",H::Sort::boolean());
        VERIFY(!P::encodeFiniteTrajectory(f.model,K::ALWAYS,{s},nullptr,nullptr,f.diagnostics));
    }
    {
        Fixture f;auto t=H::mkBoundVar("time",H::Sort::real());
        P::TrajectoryObservationDomain domain{"time","phase",H::mkBool(true),
            {H::mkReal("0"),H::mkInt(0)},{H::mkReal("1"),H::mkInt(0)}};
        // A helper body is outside the observation-template lexical scope.
        H::FunDecl hidden{"hidden",{},H::Sort::boolean(),{}};
        hidden.body=binary(H::Op::GT,t,H::mkReal("0"));f.model.funs.push_back(hidden);
        VERIFY(!P::encodeObservedTrajectory(f.model,domain,K::ALWAYS,
            {H::mkApply("hidden",H::Sort::boolean(),{}),H::mkBool(true),{}},std::nullopt,nullptr,nullptr,f.diagnostics));
    }
    std::cout<<"PDDL3 trajectory/preference constructions and refusals passed\n";
    return 0;
}
