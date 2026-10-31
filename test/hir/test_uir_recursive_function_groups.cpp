// Explicit HIR recursion is an equation group, not an implicit relaxation of
// the default acyclic helper contract. Native qualification is run remotely.
#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <string>
#include <vector>

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort NAT = H::Sort::datatype("Nat");
const H::Sort BOOL = H::Sort::boolean();

H::ConstraintModel parityModel() {
    H::ConstraintModel model;
    H::DatatypeDecl nat;
    nat.name = "Nat";
    nat.constructors.push_back(H::DtConstructor{"zero", {}});
    nat.constructors.push_back(H::DtConstructor{
        "succ", {H::DtSelector{"pred", NAT}}});
    model.datatypes.push_back(std::move(nat));

    // Deliberately shadows a same-sorted free global. BOUND_VAR and IDENT
    // must remain distinct when the group is lowered and then re-read.
    H::VarDecl global;
    global.name = "n";
    global.sort = NAT;
    model.decls.push_back(std::move(global));

    H::FunDecl even;
    even.name = "even";
    even.params = {NAT};
    even.result = BOOL;
    even.binders = {{"n", NAT}};
    even.recursive_group = "nat-parity";
    const auto even_n = H::mkBoundVar("n", NAT);
    even.body = H::mkOp(H::Op::OR, {
        H::mkDtTester("zero", even_n),
        // Same spelling and sort as the formal, but this IDENT denotes the
        // free global and must survive parameter alpha-renaming.
        H::mkDtTester("zero", H::mkIdent("n", NAT)),
        H::mkApply("odd", BOOL, {
            H::mkDtSelector("pred", NAT, H::mkBoundVar("n", NAT))})});

    H::FunDecl odd;
    odd.name = "odd";
    odd.params = {NAT};
    odd.result = BOOL;
    odd.binders = {{"n", NAT}};
    odd.recursive_group = "nat-parity";
    odd.body = H::mkOp(H::Op::AND, {
        H::mkDtTester("succ", H::mkBoundVar("n", NAT)),
        H::mkApply("even", BOOL, {
            H::mkDtSelector("pred", NAT, H::mkBoundVar("n", NAT))})});
    model.funs.push_back(std::move(even));
    model.funs.push_back(std::move(odd));

    H::Constraint constraint;
    constraint.formula = H::mkApply("even", BOOL, {
        H::mkDtConstructor("zero", NAT, {})});
    model.constraints.push_back(std::move(constraint));
    return model;
}

bool typechecks(const H::ConstraintModel& model) {
    SOMTParser::Uir::Diagnostics diagnostics;
    const bool ok = H::typeCheck(model, diagnostics);
    VERIFY(ok == !diagnostics.hasErrors());
    return ok;
}

H::ConstraintModel recursiveArrayReaders(bool mutual) {
    H::ConstraintModel model;
    const auto integer = H::Sort::integer();
    const auto array = H::Sort::array(integer, integer);
    for (unsigned member = 0; member < (mutual ? 2u : 1u); ++member) {
        H::FunDecl function;
        function.name = member == 0 ? "read_f" : "read_g";
        function.params = {array, integer};
        function.result = integer;
        function.binders = {{"a", array}, {"n", integer}};
        function.recursive_group = "array-readers";
        const auto a = H::mkBoundVar("a", array);
        const auto n = H::mkBoundVar("n", integer);
        std::vector<H::ExprPtr> terms;
        for (unsigned index = 0; index < 200; ++index) {
            terms.push_back(H::mkOp(H::Op::ITE, {
                H::mkOp(H::Op::EQ, {
                    H::mkOp(H::Op::SELECT, {a, H::mkInt(index)}), n}),
                H::mkInt(1), H::mkInt(0)}));
        }
        // The same finite-read shape as an eligible leaf, but with a real
        // self/mutual recursive edge and an explicitly opted-in SCC.
        const std::string called = mutual && member == 0 ? "read_g" : "read_f";
        function.body = H::mkOp(H::Op::ITE, {
            H::mkOp(H::Op::LE, {n, H::mkInt(0)}),
            H::mkOp(H::Op::ADD, std::move(terms)),
            H::mkApply(called, integer, {
                a, H::mkOp(H::Op::SUB, {n, H::mkInt(1)})})});
        model.funs.push_back(std::move(function));
    }
    return model;
}

} // namespace

int main() {
    H::ConstraintModel model = parityModel();
    VERIFY(typechecks(model));
    SOMTParser::ParserPtr parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser lowerer(parser);
    SOMTParser::Uir::TranslationReport report;
    SOMTParser::Uir::Diagnostics diagnostics;
    VERIFY(lowerer.lower(model, report, diagnostics));
    VERIFY(!diagnostics.hasErrors());
    const std::string smt = parser->dumpSMT2();
    VERIFY(smt.find("(define-funs-rec ((even ") != std::string::npos);
    VERIFY(smt.find("(odd ") != std::string::npos);
    VERIFY(smt.find("(declare-fun n () Nat)") != std::string::npos);
    VERIFY(smt.find("__somt_hir_param_") != std::string::npos);
    VERIFY(smt.find("((_ is zero) n)") != std::string::npos);
    VERIFY(smt.find("((_ is zero) __somt_hir_param_") != std::string::npos);
    SOMTParser::ParserPtr reader = SOMTParser::newParser();
    VERIFY(reader->parseStr(smt));
    const auto* reparsed_group = reader->getSymbolManager()->getRecFunGroup("even");
    VERIFY(reparsed_group != nullptr);
    VERIFY(reparsed_group->size() == 2);

    // A cycle with no opt-in label remains rejected.
    {
        auto bad = parityModel();
        bad.funs[0].recursive_group.clear();
        bad.funs[1].recursive_group.clear();
        VERIFY(!typechecks(bad));
    }

    // Partial/mismatched group labels cannot cause separate components to be
    // dumped together or just one edge of a recursive SCC to be enabled.
    {
        auto bad = parityModel();
        bad.funs[1].recursive_group = "other-group";
        VERIFY(!typechecks(bad));
    }

    // Body and declared signature must agree before a recursion group is
    // admitted. This intentionally changes odd's result but leaves its body
    // Bool and its call sites expecting Bool.
    {
        auto bad = parityModel();
        bad.funs[1].result = H::Sort::integer();
        VERIFY(!typechecks(bad));
    }
    {
        auto bad = parityModel();
        bad.funs[1].params[0] = H::Sort::integer();
        VERIFY(!typechecks(bad));
    }

    // A same-labeled but acyclic definition is not a recursive group.
    {
        H::ConstraintModel bad;
        H::FunDecl constant;
        constant.name = "constant_true";
        constant.result = BOOL;
        constant.body = H::mkBool(true);
        constant.recursive_group = "not-recursive";
        bad.funs.push_back(std::move(constant));
        VERIFY(!typechecks(bad));
    }

    // The bounded finite-array macro choice must not change self-recursive
    // or mutually recursive equations into ordinary, forward-invalid macros.
    for (const bool mutual : {false, true}) {
        auto recursive = recursiveArrayReaders(mutual);
        VERIFY(typechecks(recursive));
        auto target = SOMTParser::newParser();
        SOMTParser::Lower::HirToParser recursive_lowerer(target);
        SOMTParser::Uir::TranslationReport recursive_report;
        SOMTParser::Uir::Diagnostics recursive_diagnostics;
        VERIFY(recursive_lowerer.lower(recursive, recursive_report, recursive_diagnostics));
        const auto script = target->dumpSMT2();
        VERIFY(script.find("(define-fun read_f ") == std::string::npos);
        VERIFY(script.find("(define-fun read_g ") == std::string::npos);
        VERIFY(script.find("(define-funs-rec ((read_f ") != std::string::npos);
        auto reparsed = SOMTParser::newParser();
        VERIFY(reparsed->parseStr(script));
        const auto* group = reparsed->getSymbolManager()->getRecFunGroup("read_f");
        VERIFY(group != nullptr);
        VERIFY(group->size() == (mutual ? 2u : 1u));
    }
}
