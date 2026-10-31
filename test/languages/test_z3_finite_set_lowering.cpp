// Native integration regressions for the finite-set helper and exporter.
#include "somtparser/lowering/z3_finite_set_lowering.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iterator>
#include <stdexcept>
#include <string>

using namespace SOMTParser;

namespace {

std::string lower(const std::string& source) {
    return Lower::lowerFiniteSetsForZ3(source);
}

Translation parseSmt(const std::string& source) {
    Lang::SourceUnit unit;
    unit.main_path = "finite-set-export.smt2";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "smtlib2";
    options.omt_dialect = Lower::OmtDialect::SmtLib2025;
    return translate(unit, options);
}

void testQuotedBinderIdentityIsConsistent() {
    // In SMT-LIB, |u| and u are the same symbol. Both spellings must be
    // accepted in the quantified membership binder and in its occurrence.
    const std::string quoted_binder = R"SMT((set-logic ALL)
(declare-const S (Set Int))
(assert (forall ((|u| Int)) (=> (set.member u S) (and (<= u 2) (>= u 0)))))
(assert (= (set.card S) 1))
(check-sat)
)SMT";
    const std::string lowered = lower(quoted_binder);
    VERIFY(lowered.find("set.card") == std::string::npos);
    VERIFY(lowered.find("(Array Int Bool)") != std::string::npos);

    const std::string plain_binder_quoted_use = R"SMT((set-logic ALL)
(declare-const S (Set Int))
(assert (forall ((u Int)) (=> (set.member |u| S) (and (<= u 2) (>= u 0)))))
(assert (= (set.card S) 1))
(check-sat)
)SMT";
    const std::string reverse = lower(plain_binder_quoted_use);
    VERIFY(reverse.find("set.card") == std::string::npos);
}

void testLoweredLogicCoversAddedArraysAndQuantifiers() {
    // The source logic may be Set-capable but the rewritten formula is also
    // quantified linear arithmetic over arrays. QF_LIA cannot type-check it.
    const std::string qf_lia = R"SMT((set-logic QF_LIA)
(declare-const S (Set Int))
(assert (forall ((u Int)) (=> (set.member u S) (and (<= u 2) (>= u 0)))))
(assert (= (set.card S) 1))
(check-sat)
)SMT";
    const std::string rewritten = lower(qf_lia);
    VERIFY(rewritten.find("(set-logic ALL)") == 0);
    VERIFY(rewritten.find("(Array Int Bool)") != std::string::npos);
    VERIFY(rewritten.find("(forall ") != std::string::npos);
}

void testUnsupportedZ3ExportDoesNotTruncateFile() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    const auto translated = parseSmt(R"SMT((set-logic ALL)
(declare-const S (Set Int))
(assert (forall ((x Int)) (set.member x S)))
(assert (= (set.card S) 1))
(check-sat)
)SMT");
    // Translation/type validation can succeed while this requested backend
    // export is unsupported; callers must observe that refusal at export time.
    VERIFY(translated.ok());

    const auto path = std::filesystem::temp_directory_path() /
        "somtparser-z3-set-export-atomic.smt2";
    const std::string sentinel = "preserve-on-refusal\n";
    { std::ofstream out(path, std::ios::binary | std::ios::trunc); out << sentinel; }
    bool refused = false;
    try {
        translated.writeSmt2(path.string(), Lower::OmtDialect::Z3);
    } catch (const std::runtime_error&) {
        refused = true;
    }
    VERIFY(refused);
    std::ifstream in(path, std::ios::binary);
    const std::string contents((std::istreambuf_iterator<char>(in)), {});
    VERIFY(contents == sentinel);
    std::filesystem::remove(path);
}

void testRecursiveSetEquationsRequireFiniteSupport() {
    // These equations require an infinite set even without explicit forall.
    // The second example reaches membership through a nonrecursive helper.
    for (const std::string source : {
        "(define-fun-rec F ((n Int)) (Set Int) (set.insert n (F (+ n 1))))"
        "(assert (= (F 0) (F 1))) (check-sat)",
        "(declare-const S (Set Int))"
        "(define-fun member ((n Int)) Bool (set.member n S))"
        "(define-fun-rec all ((n Int)) Bool (and (member n) (all (+ n 1))))"
        "(assert (all 0)) (check-sat)"
    }) {
        bool refused = false;
        try { lower(source); }
        catch (const std::runtime_error& error) {
            refused = std::string(error.what()).find("unbounded carriers") != std::string::npos;
        }
        VERIFY(refused);
    }
}

void testCommandNamesAndQuotedKeywordsRemainTerms() {
    for (const std::string name : {
        "set-logic", "declare-const", "declare-fun", "define-fun",
        "define-fun-rec", "define-funs-rec", "define-sort",
        "declare-datatype", "declare-datatypes", "declare-codatatypes",
        "forall", "exists", "lambda", "let", "as", "match"
    }) {
        const std::string application = "(|" + name + "| 1)";
        const std::string source =
            "(set-logic ALL)(declare-fun |" + name + "| (Int) Bool)"
            "(declare-const S (Set Int))"
            "(assert (= S (set.singleton 0)))"
            "(assert " + application + ")(check-sat)";
        const std::string lowered = lower(source);
        VERIFY(lowered.find("(assert " + application + ")") != std::string::npos);
        VERIFY(lowered.find("set.singleton") == std::string::npos);
        VERIFY(lowered.find("(set-logic ALL)") == 0);
    }
    // Command-like names need not be quoted in term position, either.
    const auto plain = lower(
        "(declare-fun set-logic (Int) Bool)(assert (set-logic 1))");
    VERIFY(plain.find("(assert (set-logic 1))") != std::string::npos);
}

void testNativeReplayKeepsSetsAndObjectives() {
    // No finite carrier is supplied. Native replay must preserve this model
    // and its objective even though exact Z3 export cannot count this Set.
    const std::string source =
        "(set-logic ALL)(declare-const S (Set Int))"
        "(assert (>= (set.card S) 3))(minimize (set.card S))(check-sat)";
    const auto translated = parseSmt(source);
    VERIFY(translated.ok());
    VERIFY(translated.objectiveCount() == 1);
    const std::string replay = translated.toParserSmt2();
    VERIFY(replay.find("set.card") != std::string::npos);
    VERIFY(replay.find("minimize") != std::string::npos);
    ParserPtr reader = newParser();
    VERIFY(reader->parseStr(replay));
    VERIFY(reader->getObjectives().size() == 1);

    Lang::SourceUnit unit;
    unit.main_path = "native-set-replay.smt2";
    unit.inline_source = source;
    ParserPtr destination = newParser();
    VERIFY(destination->parseAny(unit));
    VERIFY(destination->getObjectives().size() == 1);
}

void testBoundedDynamicSetArrayReadThroughUniqueLetAlias() {
    const std::string prefix =
        "(set-logic ALL)(declare-const x (Array Int (Set Int)))(declare-const j Int)"
        "(assert (<= j 1))(assert (>= j 0))"
        "(assert (forall ((u Int)) (=> (set.member u (select x 0)) (and (<= u 2) (>= u 0)))))"
        "(assert (forall ((v Int)) (=> (set.member v (select x 1)) (and (<= v 2) (>= v 0)))))";
    const auto lowered = lower(prefix +
        "(assert (let ((a j)) (= (set.card (select x a)) 0)))(check-sat)");
    VERIFY(lowered.find("set.card") == std::string::npos);
    VERIFY(lowered.find("(Array Int (Array Int Bool))") != std::string::npos);

    // These variants must stay refused: sibling RHSs in SMT let are
    // simultaneous, duplicate names are lexically shadowed, a conditional or
    // quantified index has no proven interval, and index 2 has no set-cell
    // carrier proof.
    for(const std::string body : {
        "(assert (let ((j 0) (a j)) (= (set.card (select x a)) 0)))",
        "(assert (let ((a 0)) (let ((a 1)) (= (set.card (select x a)) 0))))",
        "(declare-const b Bool)(assert (let ((a (ite b 0 1))) (= (set.card (select x a)) 0)))",
        "(assert (forall ((a Int)) (= (set.card (select x a)) 0)))",
        "(assert (forall ((j Int)) (let ((a j)) (= (set.card (select x a)) 0))))",
        "(define-funs-rec ((f ((j Int)) Int)) ((let ((a j)) (set.card (select x a)))))",
        "(declare-datatype T ((A) (B (val Int))))(declare-const t T)"
        "(assert (= (match t (((A) 0) ((B j) (let ((a j)) (set.card (select x a))))) 0)))",
        "(assert (let ((a (+ j 1))) (= (set.card (select x a)) 0)))"
    }) {
        bool refused = false;
        try { lower(prefix + body + "(check-sat)"); }
        catch(const std::runtime_error& error) {
            refused = std::string(error.what()).find("unbounded carriers") != std::string::npos;
        }
        VERIFY(refused);
    }
}

void testLetSupportIsCapturedBeforeSimultaneousShadowing() {
    const auto text = lower(
        "(declare-const x Int)(assert (= x 0))"
        "(assert (let ((x 9) (S (set.singleton x))) (= (set.card S) 1)))");
    VERIFY(text.find("set.card") == std::string::npos);
    VERIFY(text.find("(__somt_z3_set_support_0 x)") != std::string::npos);
    VERIFY(text.find("(select S __somt_z3_set_support_0)") != std::string::npos);
}

} // namespace

int main() {
    testQuotedBinderIdentityIsConsistent();
    testLoweredLogicCoversAddedArraysAndQuantifiers();
    testUnsupportedZ3ExportDoesNotTruncateFile();
    testRecursiveSetEquationsRequireFiniteSupport();
    testCommandNamesAndQuotedKeywordsRemainTerms();
    testNativeReplayKeepsSetsAndObjectives();
    testLetSupportIsCapturedBeforeSimultaneousShadowing();
    testBoundedDynamicSetArrayReadThroughUniqueLetAlias();
    return 0;
}
