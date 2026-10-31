// The AIGER frontend, and the obligations docs/languages/aiger.md wrote down.
//
// AIGER is BTOR2 with one-bit words, so the unrolling obligations are the same
// and test_btor2.cpp holds them. What is AIGER's own is the LITERAL ENCODING,
// and it is the format's most likely first bug:
//
//   * a literal is `2*v` for the positive occurrence of variable `v` and
//     `2*v + 1` for its negation -- **the low bit is a negation flag, not part
//     of the index**. A reader that treats literals as indices silently reads a
//     circuit in which every negated occurrence refers to the wrong variable: a
//     different circuit that parses, unrolls and answers;
//   * literal 0 is constant FALSE and literal 1 is constant TRUE. Variable
//     index 0 does not exist, so reading them as variable 0 invents one.
//
// A latch with no reset column takes AIGER's specified default 0. That default
// is recorded, but it is neither a version inference nor an approximation.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation runFile(const std::string& path, int depth) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "aiger";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

Translation run(const std::string& src, int depth) {
    Lang::SourceUnit u;
    u.main_path = "t.aag";
    u.display_name = "t.aag";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "aiger";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

const EncodingChoice* choiceFor(const Translation& t, const std::string& op) {
    for (const EncodingChoice& c : t.report().choices()) {
        if (c.unified_op == op) { return &c; }
    }
    return nullptr;
}

} // namespace

int main() {
    std::cout << "======= AIGER frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* a = Lang::LanguageRegistry::instance().byId("aiger");
    assert(a != nullptr);

    // ---- The literal encoding: the low bit is a negation flag. -------------
    {
        // A latch driven by literal 3, which is variable 1 NEGATED -- so the
        // latch toggles. Read as an index, 3 would be variable 3, which does
        // not exist in a file whose header says M = 1.
        const Translation t = runFile("languages/aiger/instances/ok/toggle.aag", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= (not v1@0) v1@1)"));
        assert(has(smt, "(= (not v1@1) v1@2)"));
        // Exactly one variable exists, so the shift is not producing extras.
        assert(!has(smt, "v3@"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The mechanical half: literals 2 and 3 must give DIFFERENT circuits.
        // Read as indices they would give different circuits too, so this
        // pairs with the assertion above rather than standing alone.
        const Translation neg = run("aag 1 0 1 1 0\n2 3 0\n2\n", 1);
        const Translation pos = run("aag 1 0 1 1 0\n2 2 0\n2\n", 1);
        assert(neg.ok() && pos.ok());
        assert(neg.toSmt2() != pos.toSmt2());
        // The positive one holds its value; the negated one flips.
        assert(has(pos.toSmt2(), "(= v1@0 v1@1)"));
        assert(has(neg.toSmt2(), "(= (not v1@0) v1@1)"));
    }
    {
        // Literals 0 and 1 are the CONSTANTS. A latch driven by 0 is false
        // forever; read as "variable 0", it would be a variable the format says
        // does not exist.
        const Translation t = run("aag 1 0 1 1 0\n2 0 1\n2\n", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "v0@"));
    }

    // ---- AND gates. --------------------------------------------------------
    {
        const Translation t = runFile("languages/aiger/instances/ok/and.aag", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Two inputs, fresh at every step, and the gate is their conjunction.
        assert(has(smt, "v1@0") && has(smt, "v2@0"));
        assert(has(smt, "v1@2") && has(smt, "v2@2"));
        assert(has(smt, "and v1@0 v2@0") || has(smt, "and v2@0 v1@0"));
    }

    // ---- The reset column, and what its absence means. ---------------------
    {
        // reset == the latch's own literal: UNINITIALISED under 1.9, so step 0
        // is unconstrained. Adding a value would remove initial states.
        const Translation t = runFile("languages/aiger/instances/ok/uninit.aag", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun v1@0"));
        assert(!has(smt, "(assert (not v1@0))"));
        assert(!has(smt, "(assert v1@0)"));
        // ...and no assumption was recorded, because none was made.
        assert(choiceFor(t, "latch-reset") == nullptr);
    }
    {
        // No reset column: AIGER's exact language-defined default is 0. Its
        // application is recorded without inferring that the file is old.
        const Translation t = runFile("languages/aiger/instances/ok/old.aag", 2);
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert (not v1@0))"));
        const EncodingChoice* c = choiceFor(t, "latch-reset");
        assert(c != nullptr);
        assert(c->strategy == "specified-default-zero");
        assert(has(c->rationale, "exact default"));
    }
    {
        // An explicit `0` reset is READ, not assumed, so it records nothing --
        // otherwise every file would carry the assumption.
        const Translation t = run("aag 1 0 1 1 0\n2 3 0\n2\n", 1);
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert (not v1@0))"));
        assert(choiceFor(t, "latch-reset") == nullptr);
    }

    // ---- The bound is on the record, in the right direction. --------------
    {
        const Translation t = runFile("languages/aiger/instances/ok/toggle.aag", 3);
        const EncodingChoice* c = choiceFor(t, "transition-system");
        assert(c != nullptr);
        assert(c->fidelity.sound && !c->fidelity.complete);
        assert(c->fidelity.bounds.size() == 1);
        assert(c->fidelity.bounds[0].kind == Fidelity::Bound::BMC_DEPTH);
        assert(c->fidelity.bounds[0].value == 3);
        assert(has(c->rationale, "must not be reported as safe"));
    }
    {
        // A 1.0 file has no `bad` section, so its OUTPUTS are the properties.
        // That is a convention, so it is recorded rather than silently applied.
        const Translation t = runFile("languages/aiger/instances/ok/toggle.aag", 1);
        const EncodingChoice* c = choiceFor(t, "transition-system");
        assert(c != nullptr);
        assert(has(c->rationale, "OUTPUTS"));
    }
    {
        // AIGER 1.9 constraints need hold only through the bad-state step. The
        // latch is initially false, so both the constraint and bad literal 3
        // hold at step 0; it becomes true at step 1, making the constraint
        // false. Requiring the constraint through the end of a depth-1
        // unrolling would incorrectly erase the valid step-0 witness.
        const Translation t = run(
            "aag 1 0 1 0 0 1 1\n"
            "2 1 0\n"
            "3\n"
            "3\n",
            1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Reset, one transition, and one prefix-guarded reachability formula.
        // The two environment literals are inside that formula, not emitted as
        // two additional global constraints.
        assert(t.report().stats().num_constraints == 3);
        assert(has(smt, "(not v1@0)"));
        // There is no global assertion of the step-1 constraint.
        assert(!has(smt, "(assert (not v1@1))"));
    }

    // ---- Refusals. ---------------------------------------------------------
    {
        // An explicit B=0 selects the 1.9 property sections. A normal output
        // is not silently reinterpreted as a bad-state property.
        const Translation t = run("aag 0 0 0 1 0 0\n1\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "outputs are not safety properties"));
    }
    {
        // Header counts are obligations, not hints. Silently accepting a short
        // bad section shifts all following sections.
        const Translation t = run("aag 0 0 0 0 0 1\n", 1);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "bad properties"));
    }
    {
        // Undefined literals used to become fresh SMT variables, adding models
        // that no source AIGER circuit has.
        const Translation t = run("aag 1 0 1 1 0\n2 4\n2\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "undefined literal 4"));
    }
    {
        const Translation t = run("aag 1 0 1 1 0\n2 2 7\n2\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "reset must be 0, 1"));
    }
    {
        const Translation t = run("aag 1 0 1 1 0\n2 2 trailing\n2\n", 1);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        Lang::SourceUnit u;
        u.main_path = "languages/aiger/instances/ok/toggle.aag";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "aiger";
        opts.profile_id = "bmc";
        opts.parse.options["bmc_depth"] = "not-a-depth";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    // ---- The binary `aig` encoding. ------------------------------------------
    {
        // Two encodings, one circuit: the binary toggle and and_desc must
        // produce BYTE-IDENTICAL output to their ASCII counterparts, because
        // nothing but the encoding differs. A delta-decoding bug shows up here
        // as a different circuit, which is exactly the failure §2.4 warns about.
        const Translation asc = runFile("languages/aiger/instances/ok/toggle.aag", 2);
        const Translation bin = runFile("languages/aiger/instances/ok/toggle.aig", 2);
        assert(asc.ok() && bin.ok());
        assert(asc.toSmt2() == bin.toSmt2());

        const Translation ascA = runFile("languages/aiger/instances/ok/and_desc.aag", 2);
        const Translation binA = runFile("languages/aiger/instances/ok/and_desc.aig", 2);
        assert(ascA.ok() && binA.ok());
        assert(ascA.toSmt2() == binA.toSmt2());
        assert(has(binA.toSmt2(), "and v1@0 v2@0") || has(binA.toSmt2(), "and v2@0 v1@0"));
    }
    {
        // A delta of 252 spans two bytes in the variable-length encoding
        // (0xFC 0x01); a single-byte reader decodes a different circuit.
        // I = 127 makes the gate's lhs 2*(127+0+1) = 256, so a rhs0 of
        // literal 4 costs a 252 delta.
        std::string src = "aig 128 127 0 1 1\n256\n";
        src += '\xFC';                // delta0 = 252 -> rhs0 = 4
        src += '\x01';
        src += '\x02';                // delta1 = 2   -> rhs1 = 2
        const Translation t = run(src, 0);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The gate is the conjunction of inputs 2 and 1 at step 0.
        assert(has(smt, "v1@0") && has(smt, "v2@0"));
        assert(has(smt, "and v2@0 v1@0") || has(smt, "and v1@0 v2@0"));
        // 127 inputs, and no variable past them was invented by the decode.
        assert(!has(smt, "v128@"));
    }
    {
        // Deltas that do not decrease are corrupt, not a circuit: the encoding
        // is unambiguous exactly because lhs > rhs0 >= rhs1.
        const Translation t = runFile("languages/aiger/instances/reject/deltas_increasing.aig", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "decrease"));
    }
    {
        // One delta where the header promises two gates' worth of bytes.
        const Translation t = runFile("languages/aiger/instances/reject/truncated.aig", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "binary AND gates"));
    }
    {
        // Liveness asks about infinite behaviour, which a bounded unrolling
        // cannot express -- refused identically under both encodings.
        const Translation t = run("aag 1 0 1 0 0 0 0 1\n2 3 0\n", 2);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "infinite behaviour"));
        const Translation b = run("aig 1 0 1 0 0 0 0 1\n3 0\n", 2);
        assert(!b.ok());
        assert(has(b.diagnostics().all()[0].message, "infinite behaviour"));
    }
    {
        // No property at all: an unrolling with nothing asserted is trivially
        // satisfiable, so translating it would report a counterexample for
        // every circuit.
        const Translation t = run("aag 1 0 1 0 0\n2 3 0\n", 2);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "trivially satisfiable"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "languages/aiger/instances/ok/toggle.aag";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "aiger";
        opts.profile_id = "bmc";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "no default"));
    }
    {
        const Translation t = runFile("languages/aiger/instances/nosuch.aag", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = a->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All AIGER tests passed." << std::endl;
    return 0;
}
