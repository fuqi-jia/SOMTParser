// The report is the paper's core artifact: fidelity must be the meet over all
// per-site encoding choices, and provenance must always be present.
#include "somtparser/translation/report.h"
#include <cassert>
#include <iostream>
#include <stdexcept>
#include <string>

using namespace SOMTParser::Uir;

static bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

// Structural well-formedness check: no adjacent `,}` or `,]`, balanced braces/brackets.
// Skips escaped quotes correctly by tracking backslash state.
static void assertJsonWellFormed(const std::string& json) {
    // Check for adjacent `,}`, `,]`, `{,`, `[,`
    assert(json.find(",}") == std::string::npos && "found adjacent ,}");
    assert(json.find(",]") == std::string::npos && "found adjacent ,]");
    assert(json.find("{,") == std::string::npos && "found adjacent {,");
    assert(json.find("[,") == std::string::npos && "found adjacent [,");

    // Check balanced braces and brackets, accounting for strings
    int depth = 0;
    bool inString = false;
    bool escaped = false;
    for (const char c : json) {
        if (escaped) {
            escaped = false;
            continue;
        }
        if (c == '\\') {
            escaped = true;
            continue;
        }
        if (c == '"') {
            inString = !inString;
            continue;
        }
        if (inString) {
            continue;
        }
        if (c == '{' || c == '[') { depth++; }
        else if (c == '}' || c == ']') { depth--; }
        assert(depth >= 0 && "unbalanced braces/brackets");
    }
    assert(depth == 0 && "unbalanced braces/brackets at end");
}

int main() {
    TranslationReport r;

    // A fresh report has no count evidence, even though nothing has been
    // shown to lose models.
    assert(r.fidelity().count_status == CountStatus::UNASSESSED);
    assert(r.choices().empty());

    // A legacy exact() choice keeps count unassessed.
    EncodingChoice native;
    native.site = "c1";
    native.unified_op = "alldifferent";
    native.strategy = "native-distinct";
    native.fidelity = Fidelity::exact();
    native.rationale = "SMT-LIB distinct applies directly";
    r.addChoice(native);
    assert(r.choices().size() == 1);
    assert(r.choices()[0].site == "c1");
    assert(r.choices()[0].unified_op == "alldifferent");
    assert(r.choices()[0].strategy == "native-distinct");
    assert(!r.choices()[0].fidelity.isExact());
    assert(r.fidelity().count_status == CountStatus::UNASSESSED);

    // A local positive count claim without evidence is rejected.
    bool rejected_unproven_count = false;
    try {
        EncodingChoice unproven;
        unproven.fidelity = Fidelity::exact();
        unproven.fidelity.count_status = CountStatus::PRESERVED;
        r.addChoice(unproven);
    } catch (const std::runtime_error&) {
        rejected_unproven_count = true;
    }
    assert(rejected_unproven_count);

    TranslationReport evidenced;
    EncodingChoice measured;
    measured.fidelity = Fidelity::exact();
    measured.fidelity.count_status = CountStatus::PRESERVED;
    measured.count_evidence = CountEvidence{
        EvidenceKind::BY_CONSTRUCTION,
        "the test fixture models an identity map on one declared Boolean, so each source assignment is exactly one target assignment",
        {"test/translation/test_uir_report.cpp::identity-count-control"}};
    evidenced.addChoice(measured);
    assert(evidenced.fidelity().preservesCount());

    // One bounded choice drags the aggregate down, and the bound is retained.
    EncodingChoice bv;
    bv.site = "x";
    bv.unified_op = "int-var";
    bv.strategy = "int-as-bv32";
    bv.fidelity = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 32, "x"});
    r.addChoice(bv);
    assert(!r.fidelity().isExact());
    assert(r.fidelity().sound);
    assert(!r.fidelity().complete);
    assert(r.fidelity().bounds.size() == 1);
    assert(r.fidelity().bounds[0].value == 32);

    // Adding an over-approximation loses the other direction too.
    EncodingChoice relax;
    relax.site = "c9";
    relax.unified_op = "cumulative";
    relax.strategy = "relaxed";
    // overApprox() takes no site: an over-approximation stores no Bound, so
    // there is nowhere in the Fidelity for one to go. relax.site above is
    // where it is recorded, and the assertion below reads it back from there.
    relax.fidelity = Fidelity::overApprox();
    r.addChoice(relax);
    assert(!r.fidelity().sound);
    assert(!r.fidelity().complete);
    // Choices are kept in insertion order and none is dropped or rewritten:
    // the paper reads this list to say which encoding produced which result.
    assert(r.choices().size() == 3);
    assert(r.choices()[0].strategy == "native-distinct");
    assert(r.choices()[1].strategy == "int-as-bv32");
    assert(r.choices()[1].unified_op == "int-var");
    assert(r.choices()[2].strategy == "relaxed");
    assert(r.choices()[2].unified_op == "cumulative");
    assert(r.choices()[2].site == "c9");

    r.mutableProvenance().somtparser_version = "1.0.0";
    r.mutableProvenance().language_id = "minizinc";
    r.mutableProvenance().profile_id = "bv32";
    r.mutableProvenance().profile_content_hash = "abc123";
    r.mutableProvenance().target_dialect = "z3";
    r.mutableFeatureCounts()["int-var"] = 4;
    r.mutableFeatureCounts()["global-constraint"] = 2;
    r.mutableTheoryUsage()["QF_BV"] = 1;
    r.mutableStats().num_vars = 4;
    r.mutableStats().num_constraints = 9;
    r.addWarning(Diagnostic{Severity::WARNING, ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "circuit dropped", SourceLoc{"m.mzn", 3, 1}});
    assert(r.warnings().size() == 1);
    assert(r.warnings()[0].code == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    assert(r.warnings()[0].severity == Severity::WARNING);
    assert(r.warnings()[0].message == "circuit dropped");
    assert(r.warnings()[0].loc.line == 3);
    assert(r.warnings()[0].loc.file == "m.mzn");

    // JSON is what goes into the evaluation database, so the fields the
    // analysis groups by must all be present.
    const std::string j = r.toJson();
    assert(contains(j, "\"sound\""));
    assert(contains(j, "\"complete\""));
    assert(contains(j, "\"count_status\":\"no_guarantee\""));
    assert(contains(j, "\"preserves_count\":false"));
    assert(contains(j, "\"bounds\""));
    assert(contains(j, "\"minizinc\""));
    assert(contains(j, "\"bv32\""));
    assert(contains(j, "\"abc123\""));
    assert(contains(j, "\"target_dialect\":\"z3\""));
    assert(contains(j, "\"int-as-bv32\""));
    assert(contains(j, "\"global-constraint\""));
    assert(contains(j, "\"QF_BV\""));
    assert(contains(j, "\"num_constraints\""));
    assert(contains(j, "E_UNSUPPORTED_CONSTRUCT"));
    assert(contains(j, "\"severity\"") && contains(j, "\"WARNING\""));
    assertJsonWellFormed(j);

    // Empty report: all arrays and objects must be empty, not missing.
    TranslationReport empty;
    const std::string je = empty.toJson();
    assert(contains(je, "\"choices\":[]"));
    assert(contains(je, "\"warnings\":[]"));
    assert(contains(je, "\"bounds\":[]"));
    // Empty feature counts and theory usage are empty objects
    assert(contains(je, "\"hir_feature_counts\":{}"));
    assert(contains(je, "\"smt_theory_usage\":{}"));
    assertJsonWellFormed(je);

    // Exercise escaping: quote, backslash, newline, tab in rationale and message.
    TranslationReport esc;
    EncodingChoice escaped;
    escaped.site = "s1";
    escaped.unified_op = "op";
    escaped.strategy = "strat";
    escaped.fidelity = Fidelity::exact();
    escaped.rationale = "has \"quotes\" \\ newline\nand\ttab";
    esc.addChoice(escaped);
    esc.addWarning(Diagnostic{Severity::ERROR, ErrorCode::E_INTERNAL,
                              "msg with \" backslash \\ newline\nand tab\t",
                              SourceLoc{"f.txt", 1, 1}});
    const std::string jesc = esc.toJson();
    // Assert escaped forms are present: \" \\ \n \t
    assert(contains(jesc, "\\\""));
    assert(contains(jesc, "\\\\"));
    assert(contains(jesc, "\\n"));
    assert(contains(jesc, "\\t"));
    // Raw characters must not appear in JSON strings
    // (rough check: the rationale/message strings should be quoted and escaped)
    assertJsonWellFormed(jesc);

    const std::string jevidenced = evidenced.toJson();
    assert(contains(jevidenced, "\"count_status\":\"preserved\""));
    assert(contains(jevidenced, "\"count_evidence\""));
    assert(contains(jevidenced, "test/translation/test_uir_report.cpp::identity-count-control"));
    assertJsonWellFormed(jevidenced);

    // Bound deduplication: adding two choices with identical bounds should fold into one.
    TranslationReport dedup;
    EncodingChoice c1, c2;
    c1.site = "x1";
    c1.unified_op = "op1";
    c1.strategy = "strat1";
    c1.fidelity = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 64, "myvar"});
    c1.rationale = "r1";
    dedup.addChoice(c1);

    c2.site = "x2";
    c2.unified_op = "op2";
    c2.strategy = "strat2";
    // Same bound as c1: kind=BV_WIDTH, value=64, site="myvar"
    c2.fidelity = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 64, "myvar"});
    c2.rationale = "r2";
    dedup.addChoice(c2);

    // Aggregate should have exactly one bound, not two, because meet deduplicates
    assert(dedup.fidelity().bounds.size() == 1);
    assert(dedup.fidelity().bounds[0].kind == Fidelity::Bound::BV_WIDTH);
    assert(dedup.fidelity().bounds[0].value == 64);
    assert(dedup.fidelity().bounds[0].site == "myvar");

    // ---- mergeFrontend: what a frontend may and may not write. -------------
    //
    // A frontend owns its choices and warnings. Provenance, stats, feature
    // counts and theory usage are filled by translate() AFTER parsing, so a
    // frontend writing one would have it overwritten without a word -- and a
    // provenance in the experiment database that is not the configuration that
    // ran is worse than a missing one, because it looks answerable.
    {
        TranslationReport host, fe;
        EncodingChoice c;
        c.site = "f.mzn:3";
        c.unified_op = "predicate";
        c.strategy = "inline-at-call-site";
        c.fidelity = Fidelity::exact();
        c.rationale = "why";
        fe.addChoice(c);
        Diagnostic w;
        w.severity = Severity::WARNING;
        w.code = ErrorCode::E_PARSE;
        w.message = "a frontend warning";
        fe.addWarning(w);

        host.mergeFrontend(fe);
        assert(host.choices().size() == 1);
        assert(host.choices()[0].strategy == "inline-at-call-site");
        assert(host.warnings().size() == 1);
    }
    {
        // The aggregate MEETS rather than being copied: a frontend
        // approximation has to downgrade the whole instance exactly as a pass
        // approximation does. A merge that assigned instead of folding would
        // pass every assertion above.
        TranslationReport host, fe;
        EncodingChoice pass_choice;
        pass_choice.fidelity = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 32, "v"});
        host.addChoice(pass_choice);

        EncodingChoice fe_choice;
        fe_choice.fidelity = Fidelity::overApprox();
        fe.addChoice(fe_choice);

        host.mergeFrontend(fe);
        assert(!host.fidelity().sound);       // from the frontend's overApprox
        assert(!host.fidelity().complete);    // from the pass's underApprox
        assert(host.fidelity().bounds.size() == 1);
    }
    {
        // Each translate()-owned field is refused on its own, so a merge that
        // checked only the first one would not pass this.
        const auto refuses = [](const TranslationReport& bad) {
            TranslationReport host;
            try {
                host.mergeFrontend(bad);
            } catch (const std::runtime_error&) {
                return true;
            }
            return false;
        };

        TranslationReport prov;
        prov.mutableProvenance().language_id = "minizinc";
        assert(refuses(prov));

        TranslationReport dialect;
        dialect.mutableProvenance().target_dialect = "z3";
        assert(refuses(dialect));

        TranslationReport stats;
        stats.mutableStats().num_vars = 1;
        assert(refuses(stats));

        TranslationReport feats;
        feats.mutableFeatureCounts()["alldifferent"] = 1;
        assert(refuses(feats));

        TranslationReport theory;
        theory.mutableTheoryUsage()["LIA"] = 1;
        assert(refuses(theory));

        // And a report carrying only choices is accepted, so the check is not
        // simply refusing everything.
        TranslationReport clean;
        assert(!refuses(clean));
    }

    std::cout << "All TranslationReport tests passed." << std::endl;
    return 0;
}
