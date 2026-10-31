#include "somtparser/lowering/hir_to_parser.h"
#include "test_helpers.h"

#include <ctime>
#include <iostream>
#include <string>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

struct Result {
    double seconds;
    std::string target;
};

static Result lower(H::ConstraintModel model, bool consume) {
    auto parser = SOMTParser::newParser();
    L::HirToParser lowering(parser);
    U::TranslationReport report;
    U::Diagnostics diagnostics;
    const auto start = std::clock();
    const bool ok = consume ? lowering.lowerConsuming(model, report, diagnostics)
                            : lowering.lower(model, report, diagnostics);
    const double seconds = double(std::clock() - start) / CLOCKS_PER_SEC;
    VERIFY(ok && !diagnostics.hasErrors());
    if (consume) { VERIFY(!model.constraints[0].formula); }
    return {seconds, parser->dumpSMT2()};
}

int main() {
    // Repeated use of one immutable, deep term is common in finite array and
    // scheduling encodings. Consuming an AND must not turn its shared DAG
    // back into a tree, even though each completed child is released.
    H::ConstraintModel model;
    model.decls.push_back({"x", H::Sort::integer(), {}, {}, {}});
    model.decls.push_back({"y", H::Sort::integer(), {}, {}, {}});
    auto x = H::mkIdent("x", H::Sort::integer());
    auto term = H::mkIdent("y", H::Sort::integer());
    for (int i = 0; i < 512; ++i) {
        term = H::mkOp(H::Op::SUB, {x, term});
    }
    std::vector<H::ExprPtr> children;
    for (int i = 0; i < 512; ++i) {
        children.push_back(H::mkOp(H::Op::GT, {term, H::mkInt(i)}));
    }
    model.constraints.push_back({H::mkOp(H::Op::AND, std::move(children))});
    double plain_cpu = 0, consuming_cpu = 0;
    for (int repetition = 0; repetition < 3; ++repetition) {
        const auto plain = lower(model, false);
        const auto consumed = lower(model, true);
        VERIFY(plain.target == consumed.target);
        plain_cpu += plain.seconds;
        consuming_cpu += consumed.seconds;
    }
    std::cout << "shared_conjunction_cpu plain=" << plain_cpu
              << " consuming=" << consuming_cpu
              << " ratio=" << consuming_cpu / plain_cpu << std::endl;
    // CPU time excludes scheduling delays. Both modes lower exactly the same
    // DAG; a generous ratio still rejects re-lowering it for all 512 children.
    VERIFY(plain_cpu > 0 && consuming_cpu < plain_cpu * 10);

    // A shared body appears under two different binders between shared free
    // terms. Memoization within the AND must still respect quantifier scopes.
    const auto bound = H::mkBoundVar("n", H::Sort::integer());
    const auto body = H::mkOp(H::Op::GT, {bound, x});
    model.constraints[0].formula = H::mkOp(H::Op::AND, {
        H::mkOp(H::Op::GT, {term, H::mkInt(0)}),
        H::mkExists({{"n", H::Sort::integer()}}, body),
        H::mkForall({{"n", H::Sort::integer()}}, body),
        H::mkOp(H::Op::GT, {term, H::mkInt(1)})});
    VERIFY(lower(model, false).target == lower(model, true).target);
    return 0;
}
