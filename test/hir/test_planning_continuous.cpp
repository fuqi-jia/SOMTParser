#include "somtparser/hir/planning_continuous.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iostream>

namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
namespace U = SOMTParser::Uir;

namespace {
H::ExprPtr real(const char* value) { return H::mkReal(value); }
H::ExprPtr binary(H::Op op, H::ExprPtr a, H::ExprPtr b) { return H::mkOp(op,{a,b}); }
struct Fixture {
    H::ConstraintModel model;
    P::ContinuousSegment segment;
    U::Diagnostics diagnostics;
    H::ExprPtr x0,x1,d0,d1,enabled,active,guard,t,x;
    Fixture() {
        const auto declare=[&](const char* name,H::Sort sort) {
            model.decls.push_back({name,sort,{},{},{}});return H::mkIdent(name,sort);
        };
        x0=declare("x0",H::Sort::real());x1=declare("x1",H::Sort::real());
        d0=declare("d0",H::Sort::boolean());d1=declare("d1",H::Sort::boolean());
        enabled=declare("enabled",H::Sort::boolean());active=declare("active",H::Sort::boolean());
        guard=declare("guard",H::Sort::boolean());
        // Deliberate potential generated-name collision; must remain global.
        declare("__flow_bound_0",H::Sort::real());
        t=H::mkBoundVar("t",H::Sort::real());x=H::mkBoundVar("x",H::Sort::real());
        segment.enabled=H::mkBool(true);segment.start=real("0");segment.end=real("1");
        segment.time_variable="t";segment.derivative_domain=P::FlowDerivativeDomain::INTERIOR;
        segment.coordinates.push_back({"curve_x","x",{x0,d0},{x1,d1},H::mkBool(true),
                                       {real("2"),H::mkBool(true),{}}});
    }
    void rate(H::ExprPtr value,H::ExprPtr defined=H::mkBool(true)) {
        segment.coordinates[0].rate={value,defined,{}};
    }
    void invariant(H::ExprPtr condition,bool left=false,bool right=false,
                   H::ExprPtr defined=H::mkBool(true),H::ExprPtr activation=H::mkBool(true)) {
        segment.invariants.push_back({activation,{condition,defined,{}},left,right});
    }
    void emit(const std::filesystem::path& directory,const std::string& name,
              const std::optional<std::vector<std::vector<H::ExprPtr>>>& coefficients=std::nullopt) {
        const auto declaration_count=model.decls.size(),constraint_count=model.constraints.size(),function_count=model.funs.size();
        auto answer=coefficients?P::encodePolynomialFlowWitness(model,segment,*coefficients,diagnostics)
                                :P::encodeContinuousSegment(model,segment,diagnostics);
        if (!answer) { for (const auto& message:diagnostics.all()) {std::cerr<<name<<": "<<message.message<<'\n';} }
        VERIFY(answer);
        VERIFY(model.decls.size()==declaration_count && model.constraints.size()==constraint_count && model.funs.size()==function_count);
        VERIFY(answer->polynomial_witness==coefficients.has_value());
        VERIFY(answer->requires_trajectory_source_observations!=coefficients.has_value());
        for (const auto& function:answer->trajectories) {
            VERIFY(function.auxiliary==coefficients.has_value());
            VERIFY(static_cast<bool>(function.body)==coefficients.has_value());
        }
        auto complete=model;
        complete.funs.insert(complete.funs.end(),answer->trajectories.begin(),answer->trajectories.end());
        for (const auto& expression:answer->constraints) {H::Constraint row;row.formula=expression;complete.constraints.push_back(row);}
        VERIFY(H::typeCheck(complete,diagnostics));
        auto parser=SOMTParser::newParser();SOMTParser::Lower::HirToParser lower(parser);U::TranslationReport report;
        VERIFY(lower.lower(complete,report,diagnostics));
        const auto text=parser->dumpSMT2();VERIFY(!text.empty());
        if (!directory.empty()) {std::ofstream(directory/(name+".smt2"))<<text;}
    }
    void polynomial(const std::filesystem::path& directory,const std::string& name,
                    std::vector<H::ExprPtr> coefficients) {
        emit(directory,name,std::vector<std::vector<H::ExprPtr>>{std::move(coefficients)});
    }
};
} // namespace

int main(int argc,char**argv) {
    const std::filesystem::path directory=argc==2?argv[1]:"";
    if (!directory.empty()) {std::filesystem::create_directories(directory);}
    {
        Fixture f;f.segment.enabled=f.enabled;f.segment.coordinates[0].active=f.active;
        f.emit(directory,"general_interior");
        f.polynomial(directory,"linear_guarded",{f.x0,H::mkOp(H::Op::ITE,{f.active,real("2"),real("0")})});
    }
    {
        Fixture f;f.segment.derivative_domain=P::FlowDerivativeDomain::CLOSED_ONE_SIDED;
        f.segment.enabled=f.enabled;f.segment.coordinates[0].active=f.active;
        f.emit(directory,"general_closed");
    }
    {
        Fixture f;f.rate(binary(H::Op::MUL,f.x,f.x));
        f.invariant(binary(H::Op::LE,f.x,real("2")),true,true);
        f.emit(directory,"general_nonlinear");
    }
    {
        Fixture f;f.rate(f.x);
        f.polynomial(directory,"nonlinear_witness",{f.x0,f.x0});
    }
    for (const auto bound:{"1","1/2"}) {
        Fixture f;f.rate(binary(H::Op::SUB,real("4"),binary(H::Op::MUL,real("8"),f.t)));
        f.invariant(binary(H::Op::LE,f.x,real(bound)),true,true);
        f.polynomial(directory,std::string("parabola_")+(std::string(bound)=="1"?"safe":"interior_violation"),{real("0"),real("4"),real("-4")});
    }
    for (const auto closed:{false,true}) {
        Fixture f;f.rate(real("1"));
        f.invariant(H::mkOp(H::Op::AND,{binary(H::Op::GT,f.x,real("0")),binary(H::Op::LT,f.x,real("1"))}),closed,closed);
        f.polynomial(directory,closed?"closed_invariant":"open_invariant",{real("0"),real("1")});
    }
    for (const auto closed:{false,true}) {
        Fixture f;
        f.segment.derivative_domain=closed?P::FlowDerivativeDomain::CLOSED_ONE_SIDED:P::FlowDerivativeDomain::INTERIOR;
        f.rate(binary(H::Op::DIV_REAL,binary(H::Op::MUL,real("2"),binary(H::Op::MUL,f.t,f.t)),f.t),
               H::mkOp(H::Op::NOT,{binary(H::Op::EQ,f.t,real("0"))}));
        f.polynomial(directory,closed?"closed_rhs_domain":"interior_rhs_domain",{real("0"),real("0"),real("1")});
    }
    {
        Fixture f;f.segment.coordinates[0].active=H::mkBool(false);f.rate(real("9"),H::mkBool(false));
        f.polynomial(directory,"inactive_undefined_frame",{});
    }
    {
        Fixture f;f.rate(real("0"));f.invariant(H::mkBool(true),true,true,H::mkBool(false),f.guard);
        f.polynomial(directory,"guarded_undefined_invariant",{});
    }
    {
        Fixture f;f.rate(real("0"));
        // Inner t shadows the template clock. Substitution must retain this
        // tautological quantified condition, not replace its body with point.
        auto local=H::mkBoundVar("t",H::Sort::real());
        f.invariant(H::mkForall({{"t",H::Sort::real()}},binary(H::Op::IMPLIES,
            binary(H::Op::GT,local,real("0")),binary(H::Op::GE,local,real("0")))));
        f.polynomial(directory,"lexical_shadow",{});
    }
    {
        Fixture f;f.segment.coordinates[0].variable="x0";
        f.rate(H::mkBoundVar("x0",H::Sort::real()));
        f.polynomial(directory,"bound_vs_ident",{f.x0});
    }
    {
        Fixture f;f.rate(real("3"));f.polynomial(directory,"wrong_derivative",{real("0"),real("2")});
    }
    {
        Fixture f;f.segment.derivative_domain.reset();
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
        VERIFY(f.model.funs.empty() && f.model.constraints.empty());
    }
    {
        Fixture f;f.rate(H::mkInt(2));
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;f.segment.coordinates[0].trajectory_name="x0";
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;f.segment.coordinates[0].terminal.value=f.x0;
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;auto alias=f.segment.coordinates[0];alias.variable="y";alias.trajectory_name="curve_y";
        f.segment.coordinates.push_back(alias);
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;f.segment.coordinates[0].terminal.defined=H::mkIdent("x0",H::Sort::boolean());
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;f.segment.coordinates[0].active=binary(H::Op::GT,f.t,real("0"));
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    {
        Fixture f;VERIFY(!P::encodePolynomialFlowWitness(f.model,f.segment,{{f.t}},f.diagnostics));
    }
    {
        Fixture f;VERIFY(!P::encodePolynomialFlowWitness(f.model,f.segment,{{H::mkInt(2)}},f.diagnostics));
    }
    {
        Fixture f;VERIFY(!P::encodePolynomialFlowWitness(f.model,f.segment,{},f.diagnostics));
    }
    {
        Fixture f;auto malformed=std::make_shared<H::Expr>();malformed->kind=H::ExprKind::OP;
        malformed->op=H::Op::ADD;malformed->sort=H::Sort::real();malformed->args={nullptr,real("2")};f.rate(malformed);
        VERIFY(!P::encodeContinuousSegment(f.model,f.segment,f.diagnostics));
    }
    std::cout<<"continuous HIR models and strict constructor refusals passed\n";
    return 0;
}
