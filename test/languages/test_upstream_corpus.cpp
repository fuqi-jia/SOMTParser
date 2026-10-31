// The upstream corpora, run as a property rather than as cases.
//
// Every fixture under a language's `ok/` was written by whoever wrote the
// frontend, so it can only contain a construct that person thought of. The
// files under `instances/upstream/` were written by the people who defined the
// formats, and every corpus added here has found something no hand-written
// fixture exercised:
//
//   btor2     the `implies` operator and the indexed `slice`
//   minizinc  `/* */` comments -- 16 of 16 failed at line 1, column 1 --
//             and behind that, parameters, `->` and `include`
//   xcsp3     `<var as="...">`, misreported as "a variable has an empty domain"
//   boogie    `const`, `function`, quantifiers, grouped names -- and that
//             DECLARATIONS ARE NOT ORDERED, so a legal program was rejected
//   tptp      a problem whose function symbol is called `not`, which reached
//             the engine's reserved-name check and escaped as E_INTERNAL
//             (the fixture for that one is authored, not vendored -- see
//             languages/tptp/instances/ok/reserved_names.p)
//
// So this test supplies the CORPUS and asserts a property over all of it, the
// same way test_dump_roundtrip_instances does for the printer. Adding a file
// extends the check for free.
//
// The property, for each instance:
//
//   1. it translates, or refuses with a reason that names the construct;
//   2. what it produces re-parses -- a script this engine cannot read back is
//      the defect class this project keeps finding;
//   3. where the language is a transition system, the unrolling records its
//      bound, in the under-approximating direction.
//
// A refusal is a legitimate outcome and is counted, not ignored: `empty.aag` is
// a well-formed AIGER file with no property at all, and translating it would
// produce a trivially satisfiable script; seven FlatZinc compiler tests refer
// to external relations whose implementations are absent. An E_INTERNAL means
// the frontend broke rather than declined; that check holds at every level,
// including inputs with no available semantic task.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <algorithm>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

std::vector<std::string> instances(const std::string& dir, const std::string& ext) {
    std::vector<std::string> out;
    std::error_code ec;
    for (const auto& e : std::filesystem::directory_iterator(dir, ec)) {
        if (e.is_regular_file(ec) && e.path().extension() == ext) {
            out.push_back(e.path().string());
        }
    }
    std::sort(out.begin(), out.end());
    return out;
}

/** A transition system is unrolled to a depth and the bound must say so; every
 *  other language has no such bound and must not invent one.
 *
 *  A PLANNING instance is two files: a domain is a schema and the
 *  problem supplies the objects that make it a concrete transition system, so
 *  running the domain alone measures nothing. The pairing is by filename --
 *  `<case>_domain.pddl` beside `<case>_<problem>.pddl` -- which is a property of
 *  how they were vendored rather than of the format. */
enum class Shape { TRANSITION_SYSTEM, SINGLE_QUERY, PLANNING, HIERARCHICAL };

std::string hddlCompanion(const std::string& path) {
    const std::string stem = std::filesystem::path(path).replace_extension().string();
    std::vector<std::string> candidates{stem + "-problem.hddl"};
    for (const std::string suffix : {"-domain", "-d"}) {
        if (stem.size() >= suffix.size()
            && stem.compare(stem.size() - suffix.size(), suffix.size(), suffix) == 0) {
            candidates.push_back(stem.substr(0, stem.size() - suffix.size())
                                 + (suffix == "-d" ? "-p.hddl" : "-problem.hddl"));
        }
    }
    for (const auto& candidate : candidates) {
        if (candidate != path && std::filesystem::is_regular_file(candidate)) {
            return candidate;
        }
    }
    return {};
}

/** The selectors a MoXI multi-question refusal names, or empty.
 *
 *  A MoXI file may ask several questions and a ConstraintModel answers one, so
 *  the frontend refuses to choose and offers `query=` / `check_index=`.
 *  Answering one of two is a smaller problem, not this one, so a file counts
 *  here exactly when EVERY question it asks translates.
 *
 *  Read out of the refusal, which names them for this purpose. It is the same
 *  source `scripts/sweep-corpora.sh` and `scripts/solve-corpora.py` read: three
 *  instruments measuring the same corpus must not disagree about what they
 *  asked it, because in the output a difference in invocation is
 *  indistinguishable from a difference in coverage. */
std::vector<std::pair<std::string, std::string>> moxiQuestions(const std::string& why) {
    std::vector<std::pair<std::string, std::string>> out;
    const std::string qmark = "(queries: ";
    std::size_t at = why.find(qmark);
    if (at != std::string::npos) {
        const std::size_t end = why.find(')', at);
        if (end == std::string::npos) { return out; }
        std::string list = why.substr(at + qmark.size(), end - at - qmark.size());
        std::size_t i = 0;
        while (i <= list.size()) {
            const std::size_t comma = list.find(',', i);
            std::string one = list.substr(i, comma == std::string::npos
                                                 ? std::string::npos : comma - i);
            const std::size_t b = one.find_first_not_of(" \t");
            const std::size_t e = one.find_last_not_of(" \t");
            if (b != std::string::npos) { out.emplace_back("query", one.substr(b, e - b + 1)); }
            if (comma == std::string::npos) { break; }
            i = comma + 1;
        }
        return out;
    }
    const std::string cmark = "check_index range: 0..";
    at = why.find(cmark);
    if (at == std::string::npos) { return out; }
    const int hi = std::atoi(why.c_str() + at + cmark.size());
    for (int k = 0; k <= hi; ++k) { out.emplace_back("check_index", std::to_string(k)); }
    return out;
}

/** Run one QUESTION. Returns true when it translated; otherwise `why` is the
 *  first ERROR's message. */
bool checkOne(const std::string& lang, const std::string& path, Shape shape, int depth,
              const std::vector<std::pair<std::string, std::string>>& extra,
              std::string& why) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = lang;
    if (lang == "smtlib2") {
        opts.parse.options["cvc5_sets"] = "1";
    }
    if (lang == "pddl") {
        opts.parse.options["fond_policy"] = "strong-cyclic";
        opts.parse.options["policy_size"] = std::to_string(depth);
    }
    for (const auto& kv : extra) { opts.parse.options[kv.first] = kv.second; }
    // The companion DATA file, where the language has one. A model swept
    // without its data is not a smaller problem, it is an unanswerable one:
    // every domain bound and quantifier range is expanded against the
    // parameters, so the file refuses for a missing value and the refusal gets
    // counted as missing coverage.
    //
    // `scripts/sweep-corpora.sh` has always supplied these and this test never
    // did, so the two instruments were measuring different questions and
    // reporting one number each. Mirrors that script's `companion_for`; the
    // three must not disagree.
    if (lang == "essence" || lang == "minizinc") {
        const std::string ext = lang == "essence" ? ".eprime" : ".mzn";
        const std::string data = lang == "essence" ? ".param" : ".dzn";
        if (path.size() > ext.size()
            && path.compare(path.size() - ext.size(), ext.size(), ext) == 0) {
            const std::string cand = path.substr(0, path.size() - ext.size()) + data;
            std::error_code ec;
            if (std::filesystem::exists(cand, ec)) { u.data_paths.push_back(cand); }
        }
    }
    if (shape == Shape::PLANNING) {
        const std::string suffix = "_domain.pddl";
        const std::string base = path.substr(0, path.size() - suffix.size());
        // The one problem file vendored beside this domain.
        std::error_code pec;
        for (const auto& e : std::filesystem::directory_iterator(
                 std::filesystem::path(path).parent_path(), pec)) {
            const std::string p = e.path().string();
            if (p.rfind(base + "_", 0) == 0 && p != path) {
                u.data_paths.push_back(p);
                break;
            }
        }
        opts.profile_id = "bmc";
        opts.parse.options["plan_horizon"] = std::to_string(depth);
    }
    if (shape == Shape::HIERARCHICAL) {
        const auto companion = hddlCompanion(path);
        VERIFY(!companion.empty());
        u.data_paths.push_back(companion);
        opts.profile_id = "bmc";
        opts.parse.options["plan_horizon"] = std::to_string(depth);
        opts.parse.options["decomposition_depth"] = "3";
        opts.parse.options["lenient_requirements"] = "1";
    }
    if (shape == Shape::TRANSITION_SYSTEM) {
        opts.profile_id = "bmc";
        opts.parse.options["bmc_depth"] = std::to_string(depth);
    }
    const Translation t = translate(u, opts);

    if (!t.ok()) {
        // A refusal is a legitimate outcome; a crash is not. E_INTERNAL is the
        // bucket reserved for a broken invariant, so a frontend that reaches it
        // on well-formed upstream input has a defect rather than a gap. This is
        // the check that caught TPTP's reserved-name escape.
        VERIFY(!t.diagnostics().all().empty());
        // The first ERROR, not the first diagnostic: a frontend may emit notes
        // and warnings before it gives up -- MiniZinc's annotation note is one --
        // and checking all()[0] would grade the wrong message.
        const Diagnostic* err = nullptr;
        for (const Diagnostic& d : t.diagnostics().all()) {
            if (d.severity == Severity::ERROR) { err = &d; break; }
        }
        VERIFY(err != nullptr);
        if (err->code == ErrorCode::E_INTERNAL) {
            std::cout << "  E_INTERNAL on " << path << ": " << err->message << "\n";
            VERIFY(false);
        }
        // ...and it must say something. An empty message, or one that names a
        // token rather than a construct, is a refusal nobody can act on.
        if (err->message.size() <= 20) {
            std::cout << "  refusal too terse on " << path << ": " << err->message << "\n";
            VERIFY(false);
        }
        why = err->message;
        return false;
    }

    // What it produced must be readable by this engine.
    //
    // Asked of the **Z3 dialect** rather than of toSmt2()'s default, and the
    // difference is deliberate on both sides. The default is
    // `smtlib-omt-2025`, the SMT-LIB OMT *proposal* syntax
    // (`(define-objective o (OBJECTIVE_MIN ...))` / `(optimize-sat o)`), which
    // this parser does not implement -- it recognises `define-objective` with
    // this project's own, different grammar and does not know `optimize-sat`
    // at all (base_parser.cpp:3919 says so, and is why the internal
    // Parser-to-Parser move uses Z3 too). So a re-parse of the default dialect
    // would fail for every model with an objective, which is a fact about the
    // dialect and not a defect in the translation.
    //
    // halfreif.mzn is what made this concrete: it is the first corpus instance
    // with a `solve minimize`, and it started failing here the moment MiniZinc
    // learned bool-to-int coercion and the file began translating at all.
    // This checks the native parser round trip, including finite Set Bool,
    // Set Real and unbounded set.card. Those are valid native theory terms
    // even when the external Z3 backend cannot encode them. Keep the same
    // minimize/maximize grammar above without invoking backend lowering.
    const std::string smt = t.toParserSmt2();
    ParserPtr reader = newParser();
    if (!reader->parseStr(smt)) {
        std::cout << "  emitted script does not re-parse: " << path << "\n" << smt;
        VERIFY(false);
    }

    if (shape == Shape::TRANSITION_SYSTEM) {
        // The bound is recorded, and in the under-approximating direction: a
        // trace found within k is real, "none within k" is not "safe".
        bool found = false;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "transition-system") {
                found = true;
                VERIFY(e.fidelity.sound);
                VERIFY(!e.fidelity.complete);
                VERIFY(e.fidelity.bounds.size() == 1);
                VERIFY(e.fidelity.bounds[0].kind == Fidelity::Bound::BMC_DEPTH);
                VERIFY(e.fidelity.bounds[0].value == depth);
            }
        }
        VERIFY(found);
    } else {
        // A single-query language must NOT claim a BMC depth. The `bmc` profile
        // is not even selected here, so a bound of that kind appearing would
        // mean a frontend wrote one nobody asked for.
        for (const EncodingChoice& e : t.report().choices()) {
            for (const Fidelity::Bound& b : e.fidelity.bounds) {
                VERIFY(b.kind != Fidelity::Bound::BMC_DEPTH);
            }
        }
    }
    return true;
}

/** Run one instance: every question it asks. Returns true when all translated. */
bool check(const std::string& lang, const std::string& path, Shape shape, int depth,
           std::size_t& refused) {
    std::string why;
    if (checkOne(lang, path, shape, depth, {}, why)) { return true; }
    // A MoXI file asking several questions is asked each of them, and counts
    // only if every one translates -- see moxiQuestions(). Four upstream files
    // were counted as coverage failures until 2026-09-22 for a refusal that
    // says, in its own text, exactly which question to ask instead.
    if (lang == "moxi") {
        const auto asks = moxiQuestions(why);
        if (!asks.empty()) {
            bool all = true;
            for (const auto& kv : asks) {
                std::string ignored;
                if (!checkOne(lang, path, shape, depth, {kv}, ignored)) {
                    all = false;
                    break;
                }
            }
            if (all) { return true; }
        }
    }
    ++refused;
    return false;
}

} // namespace

int main() {
    std::cout << "======= upstream corpora =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    struct Corpus {
        const char* lang;
        const char* dir;
        const char* ext;
        Shape       shape;
        // A floor rather than an equality: adding an instance that refuses for
        // a good reason should not fail the suite, and a coverage regression
        // that stops translating what used to work should. Floors match the
        // verified source-task counts; E_INTERNAL and message-quality checks
        // still bind on every input, including legitimate refusals.
        std::size_t min_translated;
    };
    const std::vector<Corpus> corpora = {
        {"btor2",    "languages/btor2/instances/upstream",    ".btor2",
         Shape::TRANSITION_SYSTEM, 6},
        {"aiger",    "languages/aiger/instances/upstream",    ".aag",
         Shape::TRANSITION_SYSTEM, 14},
        {"dimacs",   "languages/dimacs/instances/upstream",   ".cnf",
         Shape::SINGLE_QUERY, 12},
        // 16 of 16 since 2026-09-22 -- from 8 at the start of 2026-09-21. The
        // three battleships instances needed `array2d(…)` and `_`; the two
        // blocksworld ones needed named-set element types, a set comprehension
        // in expression position, `union` between set terms, and a `var`
        // parameter typed by a named set -- four separate gaps behind one
        // another in the same file, which is why a corpus finds what a fixture
        // cannot.
        //
        // The last three were the three tenpenki instances, and they took the
        // frontend's B9-f in three steps: a predicate body RE-PARSED per call
        // rather than parsed once and substituted into, array-valued par
        // parameters carrying the caller's index set, and `let`. See
        // docs/languages/minizinc.md §4.8.
        {"minizinc", "languages/minizinc/instances/upstream", ".mzn",
         Shape::SINGLE_QUERY, 16},
        {"xcsp3",    "languages/xcsp3/instances/upstream",    ".xml",
         Shape::SINGLE_QUERY, 0},
        {"boogie",   "languages/boogie/instances/upstream",   ".bpl",
         Shape::SINGLE_QUERY, 6},
        // Vendored 2026-08-17. 22 of 43 on the first run, and the floor is set
        // one below that: the number is a regression guard, not a target, and
        // the twenty-one refusals are almost all unimplemented builtins from an
        // open catalogue, which is the honest shape of this format's coverage.
        {"flatzinc", "languages/flatzinc/instances/upstream", ".fzn",
         Shape::SINGLE_QUERY, 36},
        // Vendored 2026-08-17. 16 of 24 as of 2026-09-21, from 2 when the
        // corpus landed. These are Conjure's OUTPUT -- deeply nested
        // comprehensions over mangled representation names, which is the hard
        // end of the format -- and what moved it was never one big feature.
        // Fifteen of the twenty-four once stopped on `branching`, one token;
        // the last three stopped on a comprehension GUARD (`| q1 : int(1..2),
        // q1 < q2`), on `catchUndef`, and on a matrix literal, each of which
        // is a construct the language defines and none of which is a semantic
        // gap. The guard is the one with correctness content: it is evaluated
        // before the body, because a guard exists to exclude tuples and the
        // body need not be meaningful for the ones it excludes.
        //
        // 18 of 24 here (20 of 24 when the sweep supplies the three `.param`
        // files this test does not). Six of those came from splitting the
        // comprehension expansion from the FOLD: once a bracketed list could
        // be handed to something other than `and`/`or`/`sum`,
        // `alldifferent_except`, a lowered `<lex`, `flatten`, `allDiff` over
        // an explicit list and `min`/`max` were each a few lines on top of it
        // rather than a parser of their own. `/` and `%` came with them.
        //
        // 23 of 24, now that this test supplies the `.param` files the sweep
        // always did. It read 20 of 24 before that, and the three-file
        // difference was the harness rather than the frontend.
        //
        // The multi-dimensional non-constant subscript closed on 2026-09-22 by
        // BUILDING the flattened offset instead of folding it -- the same
        // Horner recurrence `Matrix::offsetOf` uses, written once as a term --
        // and the matrix-domain generator the same day, by expanding the
        // function space it quantifies over.
        //
        // All 24 translate after adopting the manual's relational partiality:
        // an undefined numeric expression makes its nearest Boolean expression
        // false. The old claim that Savile Row was inconsistent was wrong;
        // negating that Boolean can deliberately make the result true.
        {"essence",  "languages/essence/instances/upstream",  ".eprime",
         Shape::SINGLE_QUERY, 24},
        // Vendored 2026-08-17. All 17 now translate after the frontend adopted
        // the reference implementation's typed atoms, safety conditions,
        // carry/borrow, split/shift, range-expression and vpc rules. Keep the
        // exact floor: these are compact instruction-level reference examples,
        // and a refusal here is now a semantic regression rather than an
        // intentionally unsupported full-program feature such as `cut`.
        {"cryptoline", "languages/cryptoline/instances/upstream", ".cl",
         Shape::SINGLE_QUERY, 17},
        // Vendored 2026-08-17, GPL-3.0 -- see its PROVENANCE.md, which is the
        // only copyleft corpus here. 17 of 30 translate since 2026-09-19:
        // subsystem flattening, enums, rigid declare-const/define-fun and
        // parametric declare-datatype(s) all landed. Every refusal left is a
        // named one: eight files ask no query (including LossyIntChannelX).
        // Selected fairness is now encoded with a bounded lasso.
        //
        // 22 of 30 with fair lassos. The earlier four gains were never a
        // translation gap: they ask SEVERAL questions, this harness asked one,
        // and the refusal was counted as missing coverage. They are now asked
        // all of their questions and translate every one -- see
        // moxiQuestions() above for why that, and not "one of them worked", is
        // the bar.
        {"moxi",     "languages/moxi/instances/upstream",     ".moxi",
         Shape::TRANSITION_SYSTEM, 22},
        // HiGHS's reader corpus mixes dialect variants and negative tests.
        // 25/30 under the strict reader after Gurobi-verified inline comments;
        // an explicit HiGHS recovery option also reads warnings.mps. Keep that
        // secondary interpretation separate from this default-reader floor.
        {"mps",      "languages/mps/instances/upstream",      ".mps",
         Shape::SINGLE_QUERY, 25},
        // Vendored 2026-09-21, the two competition formats this tree had no
        // corpus for until now (D29: their archives live off GitHub, so the
        // gap was availability, not scope).
        //
        // OPB: 25 of 25, from QPLIB-PB (CC-BY-4.0). Every file translated at
        // the first attempt, which is why the floor is now the full 25 --
        // there is no refusal here to leave room for. They are OPTIMIZATION
        // instances, so they reach the objective path and OmtEmitter, not only
        // the constraint path a satisfaction corpus exercises.
        {"opb",      "languages/opb/instances/upstream",      ".opb",
         Shape::SINGLE_QUERY, 25},
        // WCNF: 25 of 25, from maxsat-core-bench (MIT), MaxSAT Evaluation 2012
        // and 2024 instances. Ten were refused on arrival, and the refusal was
        // this reader's defect rather than the files': a DIMACS-family comment
        // is a line whose first CHARACTER is `c`, and the evaluation's own
        // standardised header writes `c{` with no space, which a
        // first-token comparison does not match. `languages/dimacs` had the
        // same defect and neither was reachable from any fixture in the tree.
        {"wcnf",     "languages/wcnf/instances/upstream",     ".wcnf",
         Shape::SINGLE_QUERY, 25},
        {"lp",       "languages/lp/instances/upstream",       ".lp",
         Shape::SINGLE_QUERY, 15},
        // Vendored 2026-08-17 from cvc5's regressions, sampled across six
        // theories rather than by size, because this frontend's surface is the
        // whole of SMT-LIB and one directory would report on one theory.
        // 47 of 48 with explicit cvc5_sets compatibility and native
        // coinductive declarations. nullable_checks is a negative parser test;
        // accepting that script is not required to raise the floor.
        {"smtlib2",  "languages/smtlib2/instances/upstream",  ".smt2",
         Shape::SINGLE_QUERY, 47},
        // Vendored 2026-08-17 from AI-Planning/pddl's IPC fixtures, as
        // domain+problem PAIRS -- a domain alone is a schema and measures
        // nothing. Five pairs are FOND: use explicitly fair strong-cyclic
        // policy semantics and a policy-state bound. Childsnack remains a
        // classical bounded plan. Both produce replayable source witnesses.
        {"pddl",     "languages/pddl/instances/upstream",     ".pddl",
         Shape::PLANNING, 6},
        // Eight paired tasks from pandaPIparser; the remaining domain file is
        // unpaired. Like the CLI/Python sweeps, supply both files and explicit
        // plan/decomposition bounds, with recorded requirement lenience.
        // Previously all seventeen files were tried alone, so even supported
        // pairs were refused for missing companions and a zero floor hid it.
        // All eight now translate, including method events and bounded costs.
        {"hddl",     "languages/hddl/instances/upstream",     ".hddl",
         Shape::HIERARCHICAL, 8},
        // Three files, and the smallness is the honest part -- the TPTP Problem
        // Library is distributed from tptp.org and its licence terms are
        // recorded as unconfirmed (languages-scoping.md §1.2, §1.7). All three
        // translate, which is a weaker result than a failure; what it says is
        // that the CNF fragment was not built against a shape only its author
        // would write. See its PROVENANCE.md.
        {"tptp",     "languages/tptp/instances/upstream",     ".p",
         Shape::SINGLE_QUERY, 3},
    };

    std::size_t files_seen = 0;
    for (const Corpus& c : corpora) {
        std::vector<std::string> files = instances(c.dir, c.ext);
        if (c.shape == Shape::PLANNING) {
            // A planning corpus holds domains AND problems, and only the domain
            // is an entry point -- check() finds its problem beside it. Running
            // a problem file on its own would measure a schema-less fragment.
            std::vector<std::string> domains;
            for (const std::string& f : files) {
                if (f.size() > 12 && f.compare(f.size() - 12, 12, "_domain.pddl") == 0) {
                    domains.push_back(f);
                }
            }
            files.swap(domains);
        }
        if (c.shape == Shape::HIERARCHICAL) {
            files.erase(std::remove_if(files.begin(), files.end(),
                [](const std::string& path) { return hddlCompanion(path).empty(); }),
                files.end());
            VERIFY(files.size() == 8);
        }
        // The corpus must actually be there. Without this the whole test passes
        // vacuously if the directory is renamed or the files are not checked
        // in -- which is how a corpus-driven test goes quietly dead.
        if (files.empty()) {
            std::cout << "  no instances under " << c.dir << "\n";
            VERIFY(false);
        }
        files_seen += files.size();

        std::size_t translated = 0, refused = 0;
        for (const std::string& f : files) {
            // Depth 2 for a plan horizon: an IPC instance unrolled to 3 is
            // large enough to make this test slow for no extra property.
            const int depth = (c.shape == Shape::PLANNING
                               || c.shape == Shape::HIERARCHICAL) ? 2 : 3;
            if (check(c.lang, f, c.shape, depth, refused)) { ++translated; }
        }
        std::cout << "  " << c.lang << ": " << translated << " translated, "
                  << refused << " refused, " << files.size() << " total\n";

        if (translated < c.min_translated) {
            std::cout << "  translated " << translated << ", expected at least "
                      << c.min_translated << "\n";
            VERIFY(false);
        }
    }

    // A second floor on the corpus itself, independent of translation success.
    // Deleting negative tests must not leave the suite vacuously green.
    VERIFY(files_seen >= 334);

    // ---- Depth really varies over the corpus, not just on one fixture. -----
    {
        // The same instance at two depths must give different scripts. Run over
        // the corpus rather than a chosen file, so it holds for every shape
        // upstream ships rather than the one that was convenient.
        for (const std::string& f : instances("languages/btor2/instances/upstream",
                                              ".btor2")) {
            Lang::SourceUnit u;
            u.main_path = f;
            u.display_name = f;
            TranslateOptions a;
            a.language_id = "btor2";
            a.profile_id = "bmc";
            a.parse.options["bmc_depth"] = "1";
            TranslateOptions b = a;
            b.parse.options["bmc_depth"] = "4";
            const Translation t1 = translate(u, a);
            const Translation t2 = translate(u, b);
            if (t1.ok() && t2.ok()) { VERIFY(t1.toSmt2() != t2.toSmt2()); }
        }
    }

    std::cout << "All upstream-corpus tests passed." << std::endl;
    return 0;
}
