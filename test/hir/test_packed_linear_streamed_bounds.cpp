#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <fstream>
#include <limits>
#include <sstream>
#include <streambuf>

namespace H = SOMTParser::Uir::Hir;
using SOMTParser::Uir::Diagnostics;
using SOMTParser::Lower::OmtDialect;

namespace {

class FailedBuffer : public std::streambuf {
protected:
    int_type overflow(int_type) override { return traits_type::eof(); }
};

H::ConstraintModel makeModel() {
    H::ConstraintModel model;
    const auto add = [&](std::string name, H::Sort sort, H::ExprPtr lo, H::ExprPtr hi) {
        H::VarDecl declaration;
        declaration.name = std::move(name);
        declaration.sort = std::move(sort);
        declaration.lower_bound = std::move(lo);
        declaration.upper_bound = std::move(hi);
        model.decls.push_back(std::move(declaration));
    };
    // Real endpoints on Int declarations must retain comparison promotion,
    // including fractional bounds. A reserved symbol also collides with a
    // real source column named like the lowerer's first replacement.
    add("true", H::Sort::integer(), H::mkReal("0"), H::mkReal("1"));
    add("true!0", H::Sort::integer(), H::mkInt(0), H::mkInt(2));
    add("fractional", H::Sort::integer(), H::mkReal("-1.5"), H::mkReal("2.25"));
    add("real", H::Sort::real(), H::mkInt(-2), H::mkInt(4));
    add("big", H::Sort::integer(), H::mkInt("900719925474099312345"),
        H::mkInt("900719925474099312347"));
    add("x y", H::Sort::real(), H::mkReal("-1/3"), H::mkReal("7/3"));
    add("rational_int", H::Sort::integer(), H::mkReal("1/3"), H::mkReal("7/3"));
    add("mixed", H::Sort::integer(), H::mkInt(1),
        H::mkOp(H::Op::ADD, {H::mkInt(3), H::mkInt(4)}));
    add("format", H::Sort::real(), H::mkReal("0.0"), H::mkReal("2.0"));
    auto unnamed = std::make_shared<H::Expr>();
    unnamed->kind = H::ExprKind::LIT_INT;
    unnamed->sort = H::Sort::integer();
    unnamed->int_value = std::numeric_limits<long long>::min();
    add("empty", H::Sort::integer(), unnamed, H::mkInt(-1));
    add("unused", H::Sort::real(), H::mkReal("-3.25"), H::mkReal("6.75"));
    add("free", H::Sort::real(), {}, {});
    H::Objective objective;
    objective.kind = H::ObjKind::MINIMIZE;
    objective.name = "cost";
    objective.term = H::mkOp(H::Op::ADD,
        {H::mkIdent("true", H::Sort::integer()),
         H::mkIdent("fractional", H::Sort::integer()),
         H::mkIdent("real", H::Sort::real()), H::mkReal("1/3")});
    model.objectives.push_back(std::move(objective));
    model.packed_linear_rows = std::make_shared<H::PackedLinearRows>();
    return model;
}

std::size_t assertions(const std::string& script) {
    std::size_t count = 0, offset = 0;
    while ((offset = script.find("(assert ", offset)) != std::string::npos) {
        ++count;
        offset += 8;
    }
    return count;
}

} // namespace

int main(int argc, char** argv) {
    auto model = makeModel();
    SOMTParser::TranslateOptions options;
    options.profile_id = "feasibility";
    options.omt_dialect = OmtDialect::Z3;
    const auto actual = SOMTParser::translate(model, options);
    if (!actual.ok()) {
        for (const auto& d : actual.diagnostics().all()) std::cerr << d.message << '\n';
    }
    VERIFY(actual.ok());
    VERIFY(actual.usesPackedSmtStream());
    auto ordinary = model;
    ordinary.packed_linear_rows.reset();
    const auto expected = SOMTParser::translate(ordinary, options);
    VERIFY(expected.ok());
    const auto packed_script = actual.toSmt2(OmtDialect::Z3);
    VERIFY(assertions(packed_script) == 22);

    // Existing direct callers retain all bounds in their preamble. Only the
    // explicit mode defers literals, and the complementary writer emits each
    // deferred endpoint exactly once using the actual renamed symbol map.
    SOMTParser::Uir::TranslationReport report;
    Diagnostics diags;
    const auto parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser lowerer(parser);
    VERIFY(lowerer.lowerPackedLinearPreamble(model, report, diags, true));
    std::ostringstream preamble;
    parser->writeSMT2Module(preamble);
    VERIFY(assertions(preamble.str()) == 7); // rational, expression, noncanonical decimal
    std::vector<std::string> symbols;
    for (const auto& declaration : model.decls) {
        symbols.push_back(SOMTParser::smtSymbol(lowerer.varMap().at(declaration.name)->getName()));
    }
    std::ostringstream streamed;
    VERIFY(H::writePackedLinearBoundsSmt2(model, symbols, streamed, diags));
    VERIFY(assertions(streamed.str()) == 15);
    VERIFY(streamed.str().find("900719925474099312345") != std::string::npos);
    VERIFY(streamed.str().find("(- 9223372036854775808)") != std::string::npos);
    VERIFY(streamed.str().find("(- 1.5)") != std::string::npos);
    VERIFY(streamed.str().find("2.25") != std::string::npos);
    const auto original_parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser original(original_parser);
    VERIFY(original.lowerPackedLinearPreamble(model, report, diags));
    std::ostringstream original_script;
    original_parser->writeSMT2Module(original_script);
    VERIFY(assertions(original_script.str()) == 22);

    // Translation must still reject an incorrectly tagged endpoint before
    // either the streamed or ordinary part of the relation is emitted.
    auto malformed = model;
    auto wrong_sort = std::make_shared<H::Expr>();
    wrong_sort->kind = H::ExprKind::LIT_REAL;
    wrong_sort->sort = H::Sort::integer();
    wrong_sort->name = "0";
    VERIFY(!H::isPackedLinearBoundLiteral(model.decls.front(), wrong_sort));
    malformed.decls.front().lower_bound = wrong_sort;
    VERIFY(!SOMTParser::translate(malformed, options).ok());
    auto with_arguments = std::make_shared<H::Expr>();
    with_arguments->kind = H::ExprKind::LIT_INT;
    with_arguments->sort = H::Sort::integer();
    with_arguments->name = "0";
    with_arguments->args.push_back(H::mkInt(1));
    VERIFY(!H::isPackedLinearBoundLiteral(model.decls.front(), with_arguments));

    Diagnostics bad_map;
    std::ostringstream untouched;
    auto short_symbols = symbols;
    short_symbols.pop_back();
    VERIFY(!H::writePackedLinearBoundsSmt2(model, short_symbols, untouched, bad_map));
    VERIFY(untouched.str().empty());
    symbols.back().clear();
    VERIFY(!H::writePackedLinearBoundsSmt2(model, symbols, untouched, bad_map));
    VERIFY(untouched.str().empty());
    symbols.back() = "free";
    FailedBuffer failed_buffer;
    std::ostream failed(&failed_buffer);
    Diagnostics io_diags;
    VERIFY(!H::writePackedLinearBoundsSmt2(model, symbols, failed, io_diags));
    VERIFY(io_diags.hasErrors());

    // A large binary column population contributes no bound assertions to
    // the parser in streaming mode. Declarations remain visible and bounded
    // in the complete exported relation, even when unused by the matrix.
    H::ConstraintModel binary;
    binary.packed_linear_rows = std::make_shared<H::PackedLinearRows>();
    for (std::size_t i = 0; i < 2048; ++i) {
        H::VarDecl declaration;
        declaration.name = "b" + std::to_string(i);
        declaration.sort = H::Sort::integer();
        declaration.lower_bound = H::mkReal("0");
        declaration.upper_bound = H::mkReal("1");
        binary.decls.push_back(std::move(declaration));
    }
    const auto binary_parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser binary_lowerer(binary_parser);
    VERIFY(binary_lowerer.lowerPackedLinearPreamble(binary, report, diags, true));
    std::ostringstream binary_preamble;
    binary_parser->writeSMT2Module(binary_preamble);
    VERIFY(assertions(binary_preamble.str()) == 0);
    VERIFY(binary_lowerer.varMap().size() == 2048);

    if (argc == 2) {
        std::ofstream packed(std::string(argv[1]) + "/packed.smt2");
        std::ofstream expanded(std::string(argv[1]) + "/expanded.smt2");
        packed << packed_script;
        expanded << expected.toSmt2(OmtDialect::Z3);
        VERIFY(packed.good() && expanded.good());
    }
    return 0;
}
