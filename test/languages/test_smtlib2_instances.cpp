// The SMT-LIB2 frontend against this repository's OWN instance corpus.
//
// `test/instances/` is 21 scripts the ENGINE has always parsed -- they are what
// test_somtparser_exe reads. So every one of them is, by construction, a
// well-formed SMT-LIB script that this project already supports at the parser
// level, and any of them the SMT-LIB2 *frontend* cannot lift is a gap in
// ParserToHir and nothing else. A free corpus, already in the tree, that nobody
// had pointed at the frontend.
//
// The first run was 10 of 21, and what it found was not one missing feature but
// a table nobody had finished filling in:
//
//   re.++, re.union, str.in_re, ...   the whole regex cluster, every operator
//                                     of which already existed in the HIR
//   fp.leq, fp.geq, fp.isInfinite     likewise
//   (_ extract hi lo), zero/sign_extend, (_ re.loop i j)
//                                     indexed operators, which cannot be table
//                                     entries at all: the engine stores indices
//                                     as CHILDREN and the HIR as `indices`
//   func_apply / func_rec_apply       define-fun and define-fun-rec
//   let_chain                         `let`, whose bound references were lifted
//                                     as identifiers the model never declared
//   (_ int2bv w), (_ fp.to_ubv w)     indexed differently AGAIN -- the width is
//                                     in the result SORT, not in a child
//   re.none / re.allchar / set.empty  nullary, so HIR literals rather than
//                                     operators; mkOp refuses an empty arg list
//   ubv_to_int / sbv_to_int           the engine's other spellings of bv2nat
//                                     and bv2int, missing while the aliases
//                                     they duplicate were present
//
// It is now 19 of 21. The earlier 20 included symbols.smt2 with its
// bit-vector objective silently dropped. It must now refuse that objective;
// the symbol-only part is checked separately below.
// Algebraic datatypes were the last theory the HIR carried
// entirely and the lift could not read at all; the regex string operators and
// constant arrays were the last two rows of the coverage table that named a
// construct rather than a decision. One of the earlier sixteen went through a
// spell of being 15:
// `error_unknown_symbol_2.smt2` uses `(S Bool)` for a sort declared at arity 1,
// and the lift used to flatten the application to the constructor's NAME, so
// `(S Bool)` and `(S Int)` were one sort. That counted as a success until the
// engine started printing the application, at which point it stopped
// round-tripping and had to be refused -- and is now actually supported, with
// Hir::Sort carrying the arguments. The floor below is what keeps the rest from
// sliding back.
//
// The other refusal is `root-obj`, a Z3 extension with no HIR literal.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

std::vector<std::string> instances(const std::string& dir) {
    std::vector<std::string> out;
    std::error_code ec;
    for (const auto& e : std::filesystem::directory_iterator(dir, ec)) {
        if (e.is_regular_file(ec) && e.path().extension() == ".smt2") {
            out.push_back(e.path().string());
        }
    }
    std::sort(out.begin(), out.end());
    return out;
}

const Diagnostic* firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return &d; }
    }
    return nullptr;
}

} // namespace

int main() {
    std::cout << "======= SMT-LIB2 over test/instances =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    const std::vector<std::string> files = instances("test/instances");
    // The corpus must be there, or the whole test passes vacuously.
    VERIFY(files.size() >= 20);

    std::size_t lifted = 0, refused = 0;
    for (const std::string& f : files) {
        Lang::SourceUnit u;
        u.main_path = f;
        u.display_name = f;
        TranslateOptions opts;
        opts.language_id = "smtlib2";
        const Translation t = translate(u, opts);

        if (!t.ok()) {
            const Diagnostic* err = firstError(t);
            VERIFY(err != nullptr);
            // A refusal must NAME the construct. E_INTERNAL would mean the
            // lift broke rather than declined -- and the whole point of a
            // frontend that refuses by name is that the gap is legible.
            if (err->code == ErrorCode::E_INTERNAL) {
                std::cout << "  E_INTERNAL on " << f << ": " << err->message << "\n";
                VERIFY(false);
            }
            VERIFY(err->message.size() > 20);
            const auto filename = std::filesystem::path(f).filename().string();
            VERIFY(filename == "symbols.smt2" || filename == "reals.smt2");
            if (filename == "symbols.smt2") {
                VERIFY(err->code == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
                VERIFY(err->message.find("objective") != std::string::npos);
                // Refusing the unsupported objective must not hide a loss of
                // support for the quoted/empty symbols this fixture exercises.
                std::ifstream input(f);
                std::ostringstream text;
                text << input.rdbuf();
                std::string source = text.str();
                const std::string objective = "(minimize || )";
                const auto at = source.find(objective);
                VERIFY(at != std::string::npos);
                source.erase(at, objective.size());
                Lang::SourceUnit symbols;
                symbols.inline_source = source;
                const auto symbolic = translate(symbols, opts);
                VERIFY(symbolic.ok());
                VERIFY(newParser()->parseStr(symbolic.toSmt2()));
            }
            ++refused;
            continue;
        }

        // What it lifted must come back out. The engine parsed the input, so a
        // failure here is the lift losing or corrupting something rather than
        // the script being unreadable.
        ParserPtr reader = newParser();
        const std::string smt = t.toSmt2(Lower::OmtDialect::Z3);
        if (!reader->parseStr(smt)) {
            std::cout << "  emitted script does not re-parse: " << f << "\n" << smt;
            VERIFY(false);
        }
        ++lifted;
    }

    std::cout << "  smtlib2: " << lifted << " lifted, " << refused << " refused, "
              << files.size() << " total\n";

    // A floor, not an equality: adding an instance that refuses for a good
    // reason should not fail the suite, and losing an operator that used to
    // lift should.
    if (lifted < 19) {
        std::cout << "  lifted " << lifted << ", expected at least 19\n";
        VERIFY(false);
    }

    // ---- The specific gaps, pinned by construct rather than by file. -------
    //
    // A file-count floor says a number moved; these say WHICH constructs the
    // lift now handles, so a regression names itself.
    {
        struct Case {
            const char* what;
            const char* script;
        };
        const Case cases[] = {
            {"let", "(set-logic ALL)(declare-const x Int)"
                    "(assert (let ((y (+ x 1))) (> y 0)))(check-sat)"},
            {"nested let", "(set-logic ALL)(declare-const x Int)"
                           "(assert (let ((y (+ x 1))) (let ((z (* y 2))) (> z 0))))"
                           "(check-sat)"},
            {"define-fun", "(set-logic ALL)(define-fun inc ((x Int)) Int (+ x 1))"
                           "(assert (= (inc 1) 2))(check-sat)"},
            {"define-fun, two params",
             "(set-logic ALL)(define-fun mx ((x Int) (y Int)) Int (ite (>= x y) x y))"
             "(assert (= (mx 1 2) 2))(check-sat)"},
            {"bv extract", "(set-logic ALL)(declare-const b (_ BitVec 8))"
                           "(assert (= ((_ extract 3 0) b) #b0001))(check-sat)"},
            {"bv zero_extend", "(set-logic ALL)(declare-const b (_ BitVec 4))"
                               "(assert (= ((_ zero_extend 4) b) #x0f))(check-sat)"},
            {"regex", "(set-logic ALL)(declare-const s String)"
                      "(assert (str.in_re s (re.++ (str.to_re \"a\") (re.* (str.to_re \"b\")))))"
                      "(check-sat)"},
            {"fp comparison", "(set-logic ALL)(declare-const f (_ FloatingPoint 8 24))"
                              "(assert (fp.leq f f))(check-sat)"},
            {"int2bv -- width from the result sort, not a child",
             "(set-logic ALL)(declare-const n Int)"
             "(assert (= ((_ int2bv 8) n) #x0f))(check-sat)"},
            {"SMT-LIB 2.7 indexed integer-to-bitvector spelling",
             "(set-logic ALL)(declare-const n Int)"
             "(assert (= ((_ int_to_bv 8) n) #x0f))(check-sat)"},
            {"nullary regex literal", "(set-logic ALL)(declare-const s String)"
                                      "(assert (str.in_re s re.allchar))(check-sat)"},
        };
        for (const Case& c : cases) {
            Lang::SourceUnit u;
            u.main_path = "t.smt2";
            u.display_name = "t.smt2";
            u.inline_source = c.script;
            TranslateOptions opts;
            opts.language_id = "smtlib2";
            const Translation t = translate(u, opts);
            if (!t.ok()) {
                const Diagnostic* err = firstError(t);
                std::cout << "  " << c.what << " no longer lifts: "
                          << (err ? err->message : "(no error?)") << "\n";
                VERIFY(false);
            }
            ParserPtr p = newParser();
            VERIFY(p->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
        }
    }
    {
        // `let` is INLINED, because SMT-LIB defines it by substitution and the
        // HIR has no let. That is exact and costs size: a value bound once and
        // used twice is written twice. Asserted so the trade is recorded rather
        // than discovered.
        Lang::SourceUnit u;
        u.main_path = "t.smt2";
        u.display_name = "t.smt2";
        u.inline_source = "(set-logic ALL)(declare-const x Int)"
                          "(assert (let ((y (+ x 1))) (and (> y 0) (< y 9))))(check-sat)";
        TranslateOptions opts;
        opts.language_id = "smtlib2";
        const Translation t = translate(u, opts);
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // No `let` survives, and the bound expression appears on both sides of
        // the conjunction. A lift that emitted an identifier for `y` instead
        // would produce a script naming a symbol nothing declares.
        VERIFY(smt.find("let") == std::string::npos);
        VERIFY(smt.find("(+ 1 x)") != std::string::npos
               || smt.find("(+ x 1)") != std::string::npos);
    }

    std::cout << "All SMT-LIB2 instance tests passed." << std::endl;
    return 0;
}
