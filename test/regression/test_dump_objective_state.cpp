#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <initializer_list>
#include <sstream>
#include <string>

using namespace SOMTParser;

static size_t count(const std::string& text, const std::string& token) {
    size_t result = 0;
    size_t at = 0;
    while ((at = text.find(token, at)) != std::string::npos) {
        ++result;
        at += token.size();
    }
    return result;
}

static void verifyOrder(const std::string& text,
                        std::initializer_list<std::string> tokens) {
    size_t after = 0;
    for (const auto& token : tokens) {
        const size_t position = text.find(token, after);
        VERIFY(position != std::string::npos);
        after = position + token.size();
    }
}

static std::string roundTrip(Parser& parser) {
    const std::string text = parser.dumpSMT2();
    std::ostringstream stream;
    parser.writeSMT2(stream);
    VERIFY(stream.str() == text);
    Parser reader;
    VERIFY(reader.parseStr(text));
    const auto before = parser.getObjectives();
    const auto after = reader.getObjectives();
    VERIFY(before.size() == after.size());
    for (size_t i = 0; i < before.size(); ++i) {
        VERIFY(before[i]->getObjectiveKind() == after[i]->getObjectiveKind());
        VERIFY(before[i]->getObjectiveTerm()->getName() == after[i]->getObjectiveTerm()->getName());
    }
    VERIFY(parser.getSoftAssertions().size() == reader.getSoftAssertions().size());
    VERIFY(parser.getGroupedSoftAssertions() == reader.getGroupedSoftAssertions());
    const auto old_weights = parser.getSoftWeights();
    const auto new_weights = reader.getSoftWeights();
    VERIFY(old_weights.size() == new_weights.size());
    for (size_t i = 0; i < old_weights.size(); ++i) {
        VERIFY(old_weights[i]->getName() == new_weights[i]->getName());
    }
    VERIFY(reader.dumpSMT2() == text);
    return text;
}

static void testDirectionsAndResponse() {
    Parser parser;
    VERIFY(parser.parseStr(
        "(declare-const x Int)(declare-const y Int)"
        "(minimize x)(maximize y)(check-sat)(get-objectives)"));
    VERIFY(parser.getObjectives().size() == 2);
    VERIFY(parser.getObjectives()[0]->isMinimize());
    VERIFY(parser.getObjectives()[1]->isMaximize());
    const std::string text = roundTrip(parser);
    verifyOrder(text, {"(minimize x", "(maximize y", "(check-sat)", "(get-objectives)", "(exit)"});
    VERIFY(count(text, "(get-objectives)") == 1);
}

static void testPriorityAndSoftOrder() {
    for (const char* priority : {"lex", "pareto", "box"}) {
        Parser parser;
        parser.setOption("opt.priority", priority);
        VERIFY(parser.parseStr(
            "(declare-const x Int)(declare-const y Int)"
            "(declare-const p Bool)(declare-const q Bool)"
            "(assert-soft p :weight 9007199254740993 :id first)"
            "(minimize x)"
            "(assert-soft q :weight 3.5 :id second)"
            "(maximize y)"
            "(assert-soft (not q) :weight 2 :id first)"
            "(check-sat)(get-objectives)"));
        const std::string text = roundTrip(parser);
        const std::string option = std::string("(set-option :opt.priority ") + priority + ")";
        VERIFY(count(text, option) == 1);
        verifyOrder(text, {option,
            "(assert-soft p", "(minimize x", "(assert-soft q",
            "(maximize y", "(assert-soft (not q)", "(get-objectives)"});
        VERIFY(text.find(":weight 9007199254740993") != std::string::npos);
        VERIFY(text.find(":weight 3.5") != std::string::npos);
        Parser reader;
        VERIFY(reader.parseStr(text));
        VERIFY(reader.getOptions()->options.at("opt.priority") == priority);
    }
}

static void testApiSoftOrder() {
    Parser parser;
    auto p = parser.mkVarBool("p");
    parser.assertSoft(p, parser.mkConstInt(7), "first");
    VERIFY(parser.parseStr("(declare-const x Int)(minimize x)"));
    parser.assertSoft(parser.mkNot(p), nullptr, "second");
    VERIFY(parser.parseStr("(maximize x)"));
    const std::string text = roundTrip(parser);
    verifyOrder(text, {"(assert-soft p", "(minimize x", "(assert-soft (not p)", "(maximize x"});
    VERIFY(text.find(":weight 1 :id second") != std::string::npos);
}

static void testPopAndLastResponse() {
    Parser parser;
    VERIFY(parser.parseStr(
        "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
        "(declare-const p Bool)(declare-const q Bool)"
        "(assert-soft p :id base)(minimize x)(check-sat)(get-objectives)"
        "(push 1)(maximize y)(assert-soft (not p) :id discarded)"
        "(check-sat)(get-objectives)(pop 1)"
        "(maximize z)(assert-soft q :id last)(check-sat)(get-objectives)"));
    const std::string text = roundTrip(parser);
    VERIFY(parser.getObjectives().size() == 2);
    VERIFY(parser.getSoftAssertions().size() == 2);
    VERIFY(text.find("(maximize y") == std::string::npos);
    VERIFY(text.find("discarded") == std::string::npos);
    VERIFY(text.find("(push ") == std::string::npos);
    VERIFY(text.find("(pop ") == std::string::npos);
    VERIFY(count(text, "(check-sat)") == 1);
    VERIFY(count(text, "(get-objectives)") == 1);
    verifyOrder(text, {"(assert-soft p", "(minimize x", "(maximize z", "(assert-soft q", "(get-objectives)"});
}

static void testResetAssertions() {
    Parser parser;
    VERIFY(parser.parseStr(
        "(set-option :global-declarations true)"
        "(declare-const x Int)(declare-const p Bool)"
        "(minimize x)(assert-soft p :id discarded_base)"
        "(push 1)(maximize x)(assert-soft (not p) :id discarded_inner)"
        "(reset-assertions)(maximize x)(assert-soft p :id retained)"
        "(check-sat)(get-objectives)"));
    VERIFY(parser.getScopeDepth() == 0);
    const std::string text = roundTrip(parser);
    VERIFY(parser.getObjectives().size() == 1);
    VERIFY(parser.getSoftAssertions().size() == 1);
    VERIFY(text.find("(minimize ") == std::string::npos);
    VERIFY(text.find("discarded_") == std::string::npos);
    verifyOrder(text, {"(maximize x", "(assert-soft p", "(get-objectives)"});
}

static void testExactDecimalWeights() {
    for (const char* weight : {"0.125", "3.5", "9007199254740993.125"}) {
        Parser parser;
        VERIFY(parser.parseStr(std::string("(declare-const p Bool)(assert-soft p :id cost :weight ")
                               + weight + ")(check-sat)"));
        const auto original = parser.getSoftWeights()[0]->getValue()->getNumberValue();
        const auto output = parser.dumpSMT2();
        VERIFY(output.find(std::string(":weight ") + weight) != std::string::npos);
        Parser reader;
        VERIFY(reader.parseStr(output));
        VERIFY(reader.getSoftWeights().size() == 1);
        VERIFY(reader.getSoftWeights()[0]->getValue()->getNumberValue() == original);
        VERIFY(reader.dumpSMT2() == output);
        const auto module = parser.dumpSMT2Module();
        VERIFY(module.find(std::string(":weight ") + weight) != std::string::npos);
        Parser module_reader;
        VERIFY(module_reader.parseStr(module));
        VERIFY(module_reader.getSoftWeights()[0]->getValue()->getNumberValue() == original);
    }
    Parser nondecimal;
    auto p = nondecimal.mkVarBool("p");
    nondecimal.assertSoft(p, nondecimal.mkConstReal(std::string("1/3")), "cost");
    bool rejected = false;
    try {
        (void)nondecimal.dumpSMT2();
    } catch (const std::runtime_error& error) {
        rejected = std::string(error.what()).find("no exact finite decimal") != std::string::npos;
    }
    VERIFY(rejected);
}

int main() {
    testDirectionsAndResponse();
    testPriorityAndSoftOrder();
    testApiSoftOrder();
    testPopAndLastResponse();
    testResetAssertions();
    testExactDecimalWeights();
    return 0;
}
