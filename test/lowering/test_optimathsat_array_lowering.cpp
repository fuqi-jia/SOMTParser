#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/optimathsat_array_lowering.h"
#include "somtparser/lowering/omt_emitter.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;

static void nestedArraysAndScopes() {
    const std::string source =
        "(set-logic QF_AUFLIA)"
        "(declare-const a (Array Bool (Array Int Bool)))"
        "(declare-const p Bool)"
        "(define-fun f ((v (Array Int Bool)) (i Int)) Bool (select v i))"
        "(assert (let ((a (select a p)) (q (select (select a p) 0)))"
        "(let ((a (store a 0 q))) (f a 0))))"
        "(assert (= a ((as const (Array Bool (Array Int Bool)))"
        "((as const (Array Int Bool)) true))))(check-sat)"
        "(get-value ((select (select a p) 0)))";
    const auto output = Lower::lowerBooleanArraysForOptiMathSat(source);
    VERIFY(output.find("(set-logic ALL)") == 0);
    VERIFY(output.find("(Array (_ BitVec 1) (Array Int (_ BitVec 1)))") != std::string::npos);
    VERIFY(output.find("(ite p #b1 #b0)") != std::string::npos);
    VERIFY(output.find("(ite __somt_oms_bound_") != std::string::npos);
    VERIFY(output.find("(= (select __somt_oms_bound_") != std::string::npos);
    VERIFY(output.find("(get-value ((= (select (select a (ite p #b1 #b0)) 0) #b1)))") != std::string::npos);
    Parser reader;
    VERIFY(reader.parseStr(output));
}

static void nativeDumpAndObjectives() {
    Parser parser;
    VERIFY(parser.parseStr(
        "(declare-const a (Array Bool Bool))"
        "(assert (select a true))(minimize (ite (select a false) 4 2))"
        "(check-sat)(get-objectives)"));
    VERIFY(Lower::needsOptiMathSatArrayLowering(parser));
    const auto output = parser.dumpSMT2(Lower::OmtDialect::OptiMathSAT);
    VERIFY(output.find("(Array (_ BitVec 1) (_ BitVec 1))") != std::string::npos);
    VERIFY(output.find("(minimize ") != std::string::npos);
    VERIFY(output.find("(get-objectives)") != std::string::npos);
    Parser reader;
    VERIFY(reader.parseStr(output));
    VERIFY(reader.getObjectives().size() == 1);
    VERIFY(!Lower::needsOptiMathSatArrayLowering(reader));
    const std::string scalar = "(declare-const p Bool)(assert p)(check-sat)";
    VERIFY(Lower::lowerBooleanArraysForOptiMathSat(scalar) == scalar);
}

static void deepStoresAndSharedLetScopes() {
    constexpr std::size_t depth = 20000;
    std::string source = "(declare-const a (Array Bool Bool))(assert (select ";
    for (std::size_t i = 0; i < depth; ++i) source += "(store ";
    source += "a";
    for (std::size_t i = 0; i < depth; ++i) source += " true false)";
    source += " false))(check-sat)";
    const auto lowered = Lower::lowerBooleanArraysForOptiMathSat(source);
    VERIFY(lowered.find("(Array (_ BitVec 1) (_ BitVec 1))") != std::string::npos);
    VERIFY(lowered.size() < source.size() * 5);

    source = "(declare-const a (Array Bool Bool))(assert ";
    for (std::size_t i = 0; i < depth; ++i)
        source += "(let ((a (ite (select a true) a (store a false true)))) ";
    source += "(or (select a true) (select a false))";
    source.append(depth, ')');
    source += ")(check-sat)";
    const auto shared = Lower::lowerBooleanArraysForOptiMathSat(source);
    VERIFY(shared.find("(ite (= (select a #b1) #b1) a") != std::string::npos);
    VERIFY(shared.size() < source.size() * 5);
}

static void deepArraySortsAndQuotedSymbols() {
    constexpr std::size_t depth = 20000;
    std::string source = "(declare-const nested ";
    for (std::size_t i = 0; i < depth; ++i) source += "(Array Int ";
    source += "Bool";
    source.append(depth, ')');
    source += ")(check-sat)";
    const auto lowered = Lower::lowerBooleanArraysForOptiMathSat(source);
    VERIFY(lowered.find("Bool") == std::string::npos);
    VERIFY(lowered.size() < source.size() + 20);
    const auto quoted = Lower::lowerBooleanArraysForOptiMathSat(
        "(declare-const |a| (Array Int Bool))(declare-fun |select| (Int) Bool)"
        "(assert (and (select a 0) (|select| 0)))(check-sat)");
    VERIFY(quoted.find("(and (= (select a 0) #b1) (|select| 0))") != std::string::npos);
}

int main() {
    nestedArraysAndScopes();
    nativeDumpAndObjectives();
    deepStoresAndSharedLetScopes();
    deepArraySortsAndQuotedSymbols();
    return 0;
}
