// Focused structural tests for the isolated polymorphic type-code encoding.
// Backend SAT/UNSAT qualification must run against the shared qualified tree.
#include "../../languages/tptp/src/strong_henkin_encoding.h"

#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Lang::ThfPrototype;
namespace H = SOMTParser::Uir::Hir;

namespace {
ThfFile parseFile(const std::string& source, FunctionHirBuilder& builder) {
    ThfFileParser parser(source, "strong-henkin-test.p", builder);
    return parser.parse();
}

void writeSmt(const H::ConstraintModel& model, const char* path) {
    ParserPtr parser = newParser();
    Lower::HirToParser lowerer(parser);
    Uir::TranslationReport report;
    Uir::Diagnostics diagnostics;
    VERIFY(lowerer.lower(model, report, diagnostics));
    std::ofstream out(path, std::ios::binary | std::ios::trunc);
    VERIFY(static_cast<bool>(out));
    out << parser->dumpSMT2();
    out << "(check-sat)\n(exit)\n";
    out.flush();
    VERIFY(static_cast<bool>(out));
}
}

int main(int argc, char** argv) {
    // Mandatory Henkin counterexample: for every predicate there is a witness
    // where it is true. The FOL model must include lambda x.$false, obtained
    // from the generic K combinator, so this source assertion is UNSAT.
    {
        FunctionHirBuilder builder;
        const ThfFile file = parseFile(
            "thf(ty_u,type,(u:$tType)).\n"
            "thf(ty_p,type,(predicate:u > $o)).\n"
            "thf(counterexample,axiom, ! [F:u > $o] : ? [X:u] : (F @ X)).\n",
            builder);
        H::ConstraintModel model;
        StrongHenkinEncoding encoding(model);
        encoding.encode(file);
        Uir::Diagnostics diagnostics;
        const bool typechecked = H::typeCheck(model, diagnostics);
        for (const auto& diagnostic : diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
        VERIFY(typechecked);
        VERIFY(model.datatypes.size() == 1);
        const auto& type_codes = model.datatypes.front();
        VERIFY(type_codes.name == encoding.typeCodeSort().name);
        VERIFY(type_codes.constructors.size() == 3); // Bool, u, and Arrow.
        bool has_generic_k = false;
        bool has_generic_s = false;
        bool has_generic_choice = false;
        for (const auto& function : model.funs) {
            has_generic_k = has_generic_k || function.name.rfind("__thf_K_", 0) == 0;
            has_generic_s = has_generic_s || function.name.rfind("__thf_S_", 0) == 0;
            has_generic_choice = has_generic_choice
                || function.name.rfind("__thf_choice_", 0) == 0;
        }
        VERIFY(has_generic_k && has_generic_s && has_generic_choice);
        bool has_generic_not = false;
        bool has_generic_and = false;
        bool has_generic_or = false;
        bool has_generic_implies = false;
        for (const auto& declaration : model.decls) {
            has_generic_not = has_generic_not || declaration.name.rfind("__thf_not_", 0) == 0;
            has_generic_and = has_generic_and || declaration.name.rfind("__thf_and_", 0) == 0;
            has_generic_or = has_generic_or || declaration.name.rfind("__thf_or_", 0) == 0;
            has_generic_implies = has_generic_implies
                || declaration.name.rfind("__thf_implies_", 0) == 0;
        }
        bool has_generic_equality = false;
        bool has_generic_forall = false;
        bool has_generic_exists = false;
        for (const auto& function : model.funs) {
            has_generic_equality = has_generic_equality
                || function.name.rfind("__thf_equal_", 0) == 0;
            has_generic_forall = has_generic_forall
                || function.name.rfind("__thf_forall_", 0) == 0;
            has_generic_exists = has_generic_exists
                || function.name.rfind("__thf_exists_", 0) == 0;
        }
        VERIFY(has_generic_not && has_generic_and && has_generic_or && has_generic_implies);
        VERIFY(has_generic_equality && has_generic_forall && has_generic_exists);
        // The global K axiom is a single quantified schema over TypeCode,
        // not a selected list of concrete function-sort instances.
        bool found_universal_type_schema = false;
        for (const auto& constraint : model.constraints) {
            if (constraint.formula->kind == H::ExprKind::FORALL
                && constraint.formula->binders.size() == 2
                && constraint.formula->binders.front().sort.kind == H::SortKind::DATATYPE
                && constraint.formula->binders.front().sort.name == type_codes.name) {
                found_universal_type_schema = true;
            }
        }
        VERIFY(found_universal_type_schema);

        // Optional independent-backend qualification: lower the actual
        // generated HIR and preserve its SMT-LIB, rather than validating only
        // hand-written encodings of the same counterexample.
        if (argc > 1) {
            writeSmt(model, argv[1]);
        }
    }

    // No explicit lambda occurs in this input. The generic negation object
    // must nevertheless belong to Bool->Bool; it refutes monotonicity on the
    // two Boolean values, making this axiom UNSAT in the full Henkin model.
    // This specifically catches an encoding that has K/S but omits closure
    // under logical constants.
    {
        FunctionHirBuilder builder;
        const ThfFile file = parseFile(
            "thf(monotone,axiom, ! [F:$o > $o] : "
            "((F @ $false) => (F @ $true))).\n", builder);
        H::ConstraintModel model;
        StrongHenkinEncoding encoding(model);
        encoding.encode(file);
        Uir::Diagnostics diagnostics;
        for (const auto& diagnostic : diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
        VERIFY(H::typeCheck(model, diagnostics));
        if (argc > 2) { writeSmt(model, argv[2]); }
    }

    // The real source shape captures an outer predicate in a lambda passed to
    // a higher-order helper. The lifted helper must take that capture as an
    // explicit target parameter and constrain the lambda for every typed
    // capture/argument pair.
    {
        FunctionHirBuilder builder;
        const ThfFile file = parseFile(
            "thf(ty_u,type,(u:$tType)).\n"
            "thf(ty_p,type,(predicate:u > $o)).\n"
            "thf(ty_collect,type,(collect:(u > $o) > (u > $o))).\n"
            "thf(captured,axiom, ! [A:u > $o] : "
            "((collect @ ^ [X:u] : (predicate @ X & A @ X)) = A)).\n",
            builder);
        H::ConstraintModel model;
        StrongHenkinEncoding encoding(model);
        encoding.encode(file);
        Uir::Diagnostics diagnostics;
        VERIFY(H::typeCheck(model, diagnostics));
        bool found_captured_lambda_helper = false;
        for (const auto& function : model.funs) {
            if (function.name.rfind("__thf_lambda_", 0) == 0
                && function.params.size() == 1
                && H::sameSort(function.params.front(), encoding.objectSort())) {
                found_captured_lambda_helper = true;
            }
        }
        VERIFY(found_captured_lambda_helper);
    }

    // This prototype does not reinterpret TPTP's arithmetic base types as
    // arbitrary objects. Reject before mutating the target model.
    {
        ThfFile unsupported;
        unsupported.signature.emplace("n", Type::integer());
        H::ConstraintModel model;
        StrongHenkinEncoding encoding(model);
        bool rejected = false;
        try { encoding.encode(unsupported); }
        catch (const std::invalid_argument&) { rejected = true; }
        VERIFY(rejected);
        VERIFY(model.decls.empty() && model.funs.empty() && model.constraints.empty());
    }
}
