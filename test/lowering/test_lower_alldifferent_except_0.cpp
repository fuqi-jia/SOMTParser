#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/lowering/decompose_globals_pass.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/hir/typecheck.h"

#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {
namespace H = SOMTParser::Uir::Hir;

bool contains(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

H::ConstraintModel withConstraint(H::ExprPtr formula) {
    H::ConstraintModel model;
    H::Constraint constraint;
    constraint.formula = std::move(formula);
    model.constraints.push_back(std::move(constraint));
    return model;
}

H::ExprPtr global(std::vector<H::ExprPtr> args) {
    return H::mkGlobal("alldifferent_except_0", std::move(args));
}

bool encode(const char* profile_id, H::ConstraintModel model, std::string& output,
            Diagnostics& diagnostics) {
    Lower::registerBuiltinPasses(PassRegistry::instance());
    const auto profile = EncodingProfile::builtin(profile_id);
    VERIFY(profile != nullptr);
    TranslationReport report;
    if (!PassManager::run(model, *profile, PassRegistry::instance(), report,
                          diagnostics)) {
        return false;
    }
    VERIFY(H::typeCheck(model, diagnostics));
    ParserPtr parser = newParser();
    Lower::HirToParser lowering(parser);
    if (!lowering.lower(model, report, diagnostics)) { return false; }
    output = parser->dumpSMT2();
    return true;
}

bool rejects(H::ExprPtr formula, const std::string& name = "a",
             H::Sort sort = H::Sort::integer()) {
    auto model = withConstraint(std::move(formula));
    H::VarDecl declaration;
    declaration.name = name;
    declaration.sort = std::move(sort);
    model.decls.push_back(std::move(declaration));
    Diagnostics diagnostics;
    return !H::typeCheck(model, diagnostics) && diagnostics.hasErrors();
}
} // namespace

int main() {
    const auto int_sort = H::Sort::integer();
    const auto array_sort = H::Sort::array(int_sort, int_sort);

    // The list form lowers to one native distinct, with one injective mapped
    // term per input. The mapping gives every zero a private negative tag and
    // sends positive/negative nonzero values to disjoint positive ranges.
    {
        H::ConstraintModel model;
        for (const auto* name : {"x", "y"}) {
            H::VarDecl declaration;
            declaration.name = name;
            declaration.sort = H::Sort::integer();
            model.decls.push_back(std::move(declaration));
        }
        std::vector<H::ExprPtr> terms{H::mkInt(0), H::mkInt(0), H::mkInt(-9),
                                     H::mkIdent("x", int_sort),
                                     H::mkIdent("y", int_sort)};
        model.constraints.push_back({global(std::move(terms))});
        std::string smt;
        Diagnostics diagnostics;
        VERIFY(encode("ground", std::move(model), smt, diagnostics));
        VERIFY(!diagnostics.hasErrors());
        VERIFY(smt.find("(distinct ") != std::string::npos);
        VERIFY(smt.find("alldifferent_except_0") == std::string::npos);
    }

    // Empty and singleton lists are true, but only after checking every
    // supplied operand's exact Int sort.
    {
        std::string empty_smt;
        Diagnostics diagnostics;
        VERIFY(encode("ground", withConstraint(global({})), empty_smt,
                      diagnostics));
        VERIFY(!empty_smt.empty());

        std::string singleton_smt;
        Diagnostics one_diagnostics;
        VERIFY(encode("ground", withConstraint(global({H::mkInt(-4)})),
                      singleton_smt, one_diagnostics));
        VERIFY(!singleton_smt.empty());
        VERIFY(rejects(global({H::mkBool(true)})));
        VERIFY(rejects(global({H::mkReal("1.0")})));
    }

    // Indexed form uses exactly [lo, hi), including the empty-range identity.
    {
        H::VarDecl array;
        array.name = "a";
        array.sort = array_sort;
        H::ConstraintModel model;
        model.decls.push_back(array);
        model.constraints.push_back({global({H::mkIdent("a", array_sort),
                                              H::mkInt(2), H::mkInt(5)})});
        std::string smt;
        Diagnostics diagnostics;
        VERIFY(encode("ground", std::move(model), smt, diagnostics));
        VERIFY(!smt.empty());
        VERIFY(contains(smt, "(select a 2)"));
        VERIFY(contains(smt, "(select a 4)"));
        VERIFY(!contains(smt, "(select a 1)"));
        VERIFY(!contains(smt, "(select a 5)"));

        H::ConstraintModel empty;
        empty.decls.push_back(array);
        empty.constraints.push_back({global({H::mkIdent("a", array_sort),
                                             H::mkInt(2), H::mkInt(2)})});
        VERIFY(encode("ground", std::move(empty), smt, diagnostics));
        VERIFY(!smt.empty());
    }

    // Quantified array encoding remains exact for symbolic bounds and avoids
    // collisions with names already bound in the source formula.
    {
        H::VarDecl array;
        array.name = "a";
        array.sort = array_sort;
        H::VarDecl lo{"lo", int_sort};
        H::VarDecl hi{"hi", int_sort};
        H::ConstraintModel model;
        model.decls = {array, lo, hi};
        const auto indexed = global({H::mkIdent("a", array_sort),
                                     H::mkIdent("lo", int_sort),
                                     H::mkIdent("hi", int_sort)});
        const H::Binder outer{"!except0_i0", H::Sort::integer()};
        model.constraints.push_back({H::mkForall({outer}, indexed)});
        std::string smt;
        Diagnostics diagnostics;
        VERIFY(encode("quantified", std::move(model), smt, diagnostics));
        VERIFY(contains(smt, "!except0_i0_1"));
        VERIFY(contains(smt, "!except0_j0"));
        VERIFY(!contains(smt, "alldifferent_except_0"));
    }

    // The compact list lowering grows linearly: one distinct node for each
    // arity, rather than a pairwise expansion of the original relation.
    {
        auto output_size = [&](std::size_t n) {
            std::vector<H::ExprPtr> terms;
            for (std::size_t i = 1; i <= n; ++i) {
                terms.push_back(H::mkIdent("x" + std::to_string(i), int_sort));
            }
            H::ConstraintModel model = withConstraint(global(std::move(terms)));
            for (std::size_t i = 1; i <= n; ++i) {
                H::VarDecl d;
                d.name = "x" + std::to_string(i);
                d.sort = int_sort;
                model.decls.push_back(std::move(d));
            }
            std::string smt;
            Diagnostics diagnostics;
            VERIFY(encode("ground", std::move(model), smt, diagnostics));
            VERIFY(!smt.empty());
            VERIFY(contains(smt, "(distinct "));
            return smt.size();
        };
        const auto n8 = output_size(8);
        const auto n16 = output_size(16);
        VERIFY(n16 > n8);
        VERIFY(n16 < n8 * 2.5);
    }

    // Exact Int validation applies to indexed arrays and bounds too.
    {
        const auto bool_array = H::Sort::array(int_sort, H::Sort::boolean());
        VERIFY(rejects(global({H::mkIdent("a", bool_array),
                               H::mkInt(0), H::mkInt(1)}), "a", bool_array));
        const auto real_index_array = H::Sort::array(H::Sort::real(), int_sort);
        VERIFY(rejects(global({H::mkIdent("a", real_index_array),
                               H::mkInt(0), H::mkInt(1)}), "a", real_index_array));
        VERIFY(rejects(global({H::mkIdent("a", array_sort),
                               H::mkBool(false), H::mkInt(1)}), "a", array_sort));
    }
    return 0;
}
