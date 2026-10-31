#include "somtparser/hir/packed_clause_io.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <sstream>
#include <string>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static std::size_t count(const std::string& text, const std::string& token) {
    std::size_t result = 0, position = 0;
    while ((position = text.find(token, position)) != std::string::npos) {
        ++result;
        position += token.size();
    }
    return result;
}

static H::ConstraintModel fixture() {
    H::ConstraintModel model;
    H::BoolVarRange range;
    range.prefix = "x";
    range.count = 2;
    model.bool_var_ranges.push_back(range);
    H::PackedBoolClauseBatch batch;
    batch.variable_range = 0;
    batch.clause_offsets = {0, 1, 2, 2};
    batch.literals = {1, -2};
    batch.weight_offsets = {0, 0, 1, 17};
    batch.weight_bytes = "79007199254740993";
    batch.source_lines = {1, 2, 3};
    model.packed_bool_clauses.push_back(batch);
    return model;
}

int main() {
    const auto model = fixture();
    {
        U::Diagnostics diagnostics;
        std::ostringstream output;
        VERIFY(H::writePackedBoolClausesSmt2(model, output, diagnostics));
        VERIFY(output.str() ==
            "(declare-const x1 Bool)\n(declare-const x2 Bool)\n"
            "(assert (or x1))\n"
            "(assert-soft (or (not x2)) :weight 7)\n"
            "(assert-soft false :weight 9007199254740993)\n");
    }
    {
        U::Diagnostics diagnostics;
        std::ostringstream output;
        VERIFY(H::writePackedBoolClausesSmt2(model, output, diagnostics, "|cost with spaces|"));
        VERIFY(count(output.str(), ":objective |cost with spaces|") == 2);
        VERIFY(output.str().find("(assert (or x1))") != std::string::npos);
        VERIFY(output.str().find(":weight 9007199254740993 :objective") != std::string::npos);
        VERIFY(output.str().find("define-maxsmt-objective") == std::string::npos);
        VERIFY(output.str().find("check-sat") == std::string::npos);
    }
    for (const auto& invalid : {"bad) (assert false", "x1", "|x2|"}) {
        U::Diagnostics diagnostics;
        std::ostringstream output;
        VERIFY(!H::writePackedBoolClausesSmt2(model, output, diagnostics, invalid));
        VERIFY(diagnostics.hasErrors());
        VERIFY(output.str().empty());
    }
    for (const auto dialect : {L::OmtDialect::Z3, L::OmtDialect::OptiMathSAT, L::OmtDialect::Gomt}) {
        SOMTParser::TranslateOptions options;
        options.omt_dialect = dialect;
        const auto translated = SOMTParser::translate(model, options);
        VERIFY(translated.ok());
        VERIFY(translated.usesPackedSmtStream() && !translated.hasParser());
        VERIFY(translated.objectiveCount() == 1);
        const auto text = translated.toSmt2(dialect);
        VERIFY(count(text, "(assert-soft ") == 2);
        VERIFY(text.find(":weight 9007199254740993") != std::string::npos);
        if (dialect == L::OmtDialect::Gomt) {
            VERIFY(count(text, "(define-maxsmt-objective ") == 1);
            VERIFY(count(text, "(optimize-sat ") == 1);
            VERIFY(count(text, ":objective ") == 2);
            VERIFY(count(text, "(check-sat)") == 0);
            VERIFY(text.find("(set-option :enable-omt true)") < text.find("(define-maxsmt-objective "));
            VERIFY(text.find("(define-maxsmt-objective ") < text.find("(assert-soft "));
            VERIFY(text.rfind("(assert-soft ") < text.find("(optimize-sat "));
            const auto name_begin = text.find("(define-maxsmt-objective ") + std::string("(define-maxsmt-objective ").size();
            const auto name = text.substr(name_begin, text.find(')', name_begin) - name_begin);
            VERIFY(count(text, ":objective " + name) == 2);
            VERIFY(text.find("(optimize-sat " + name + ")") != std::string::npos);
        } else {
            VERIFY(count(text, "(check-sat)") == 1);
            VERIFY(text.find("optimize-sat") == std::string::npos);
            VERIFY(count(text, "(minimize I)") == (dialect == L::OmtDialect::OptiMathSAT ? 1 : 0));
            if (dialect == L::OmtDialect::OptiMathSAT) {
                VERIFY(text.rfind("(assert-soft ") < text.find("(minimize I)"));
                VERIFY(text.find("(minimize I)") < text.find("(check-sat)"));
            }
        }
        // A pure SAT packed input still has exactly one ordinary query in all
        // three dialects, even though no optimization API is needed.
        auto hard = model;
        hard.packed_bool_clauses[0].weight_bytes.clear();
        hard.packed_bool_clauses[0].weight_offsets = {0, 0, 0, 0};
        const auto sat = SOMTParser::translate(hard, options);
        VERIFY(sat.ok());
        const auto hard_text = sat.toSmt2(dialect);
        VERIFY(count(hard_text, "(check-sat)") == 1);
        VERIFY(hard_text.find("optimize-sat") == std::string::npos);
        VERIFY(hard_text.find("define-maxsmt-objective") == std::string::npos);
    }
    return 0;
}
