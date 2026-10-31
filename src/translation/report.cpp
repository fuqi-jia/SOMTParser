/* -*- Source -*-
 * TranslationReport serialisation.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/report.h"

#include "somtparser/core/asserting.h"

#include <sstream>
#include <utility>

namespace SOMTParser::Uir {

namespace {

std::string quote(const std::string& s) {
    std::ostringstream o;
    o << '"';
    for (const char c : s) {
        switch (c) {
        case '"':  o << "\\\""; break;
        case '\\': o << "\\\\"; break;
        case '\n': o << "\\n";  break;
        case '\r': o << "\\r";  break;
        case '\t': o << "\\t";  break;
        default:
            if (static_cast<unsigned char>(c) < 0x20) {
                o << "\\u00"
                  << "0123456789abcdef"[(c >> 4) & 0xF]
                  << "0123456789abcdef"[c & 0xF];
            } else {
                o << c;
            }
        }
    }
    o << '"';
    return o.str();
}

const char* severityName(Severity s) {
    switch (s) {
    case Severity::NOTE:    return "NOTE";
    case Severity::WARNING: return "WARNING";
    case Severity::ERROR:   return "ERROR";
    }
    condAssert(false, "severityName: unhandled Severity");
    return "";   // unreachable; condAssert always throws
}

const char* boundKindName(Fidelity::Bound::Kind k) {
    switch (k) {
    case Fidelity::Bound::BMC_DEPTH:   return "BMC_DEPTH";
    case Fidelity::Bound::BV_WIDTH:    return "BV_WIDTH";
    case Fidelity::Bound::DOMAIN_CUT:  return "DOMAIN_CUT";
    case Fidelity::Bound::HORN_UNROLL: return "HORN_UNROLL";
    case Fidelity::Bound::PLAN_HORIZON: return "PLAN_HORIZON";
    case Fidelity::Bound::DECOMPOSITION_DEPTH: return "DECOMPOSITION_DEPTH";
    case Fidelity::Bound::GRAMMAR_RESTRICTION: return "GRAMMAR_RESTRICTION";
    case Fidelity::Bound::STRATEGY_SIZE: return "STRATEGY_SIZE";
    }
    // No fallback value. A new Bound::Kind must fail here rather than be
    // silently reported as DOMAIN_CUT, which would put a wrong bound kind into
    // the experiment database and misdescribe why a result is only conditionally
    // valid. -Wswitch catches it at compile time; this catches it at run time.
    condAssert(false, "boundKindName: unhandled Fidelity::Bound::Kind");
    return "";   // unreachable; condAssert always throws
}

void writeFidelity(std::ostringstream& o, const Fidelity& f) {
    o << "{\"sound\":" << (f.sound ? "true" : "false")
      << ",\"complete\":" << (f.complete ? "true" : "false")
      << ",\"preserves_optimum\":" << (f.preserves_optimum ? "true" : "false")
      << ",\"count_status\":" << quote(countStatusName(f.count_status))
      << ",\"preserves_count\":" << (f.preservesCount() ? "true" : "false")
      << ",\"bounds\":[";
    for (std::size_t i = 0; i < f.bounds.size(); ++i) {
        const auto& b = f.bounds[i];
        if (i != 0) { o << ','; }
        o << "{\"kind\":" << quote(boundKindName(b.kind))
          << ",\"value\":" << b.value
          << ",\"site\":" << quote(b.site) << '}';
    }
    o << "]}";
}

void writeCountMap(std::ostringstream& o, const std::map<std::string, std::size_t>& m) {
    o << '{';
    bool first = true;
    for (const auto& kv : m) {
        if (!first) { o << ','; }
        first = false;
        o << quote(kv.first) << ':' << kv.second;
    }
    o << '}';
}

/** The fields translate() owns. A frontend must leave them as constructed;
 *  see TranslationReport::mergeFrontend for why this is an error and not a
 *  merge rule. */
bool isPristine(const Provenance& p) {
    return p.somtparser_version.empty() && p.language_id.empty()
        && p.language_version.empty() && p.ops_schema_version.empty()
        && p.ops_content_hash.empty() && p.profile_id.empty()
        && p.profile_content_hash.empty() && p.target_dialect.empty();
}

bool isPristine(const Stats& s) {
    return s.num_vars == 0 && s.num_constraints == 0 && s.num_objectives == 0
        && s.num_smt_nodes == 0 && s.max_quantifier_alternations == 0
        && s.translate_ms == 0.0 && s.parse_ms == 0.0
        && s.typecheck_ms == 0.0 && s.passes_ms == 0.0 && s.lower_ms == 0.0
        && s.semantics_ms == 0.0;
}

} // namespace

void TranslationReport::addChoice(EncodingChoice c) {
    condAssert(c.fidelity.count_status != CountStatus::PRESERVED
                   || (c.count_evidence && c.count_evidence->recorded()),
               "an EncodingChoice that claims model-count preservation needs concrete count evidence");
    if (!has_choice_) {
        fidelity_ = c.fidelity;
        has_choice_ = true;
    } else {
        fidelity_ = Fidelity::meet(fidelity_, c.fidelity);
    }
    if (phase_active_) {
        phase_fidelity_ = phase_has_choice_ ? Fidelity::meet(phase_fidelity_, c.fidelity) : c.fidelity;
        phase_has_choice_ = true;
    }
    if (details_enabled_) { choices_.push_back(std::move(c)); }
}

void TranslationReport::mergeFrontend(const TranslationReport& frontend) {
    condAssert(isPristine(frontend.provenance_),
               "a frontend wrote TranslationReport::provenance, which translate() "
               "fills after parsing and would overwrite");
    condAssert(isPristine(frontend.stats_),
               "a frontend wrote TranslationReport::stats, which translate() fills "
               "from the lowered model and would overwrite");
    condAssert(frontend.feature_counts_.empty(),
               "a frontend wrote TranslationReport::featureCounts, which translate() "
               "derives from the model's own features and would overwrite");
    condAssert(frontend.theory_usage_.empty(),
               "a frontend wrote TranslationReport::theoryUsage, which lowering fills "
               "and would overwrite");

    for (const EncodingChoice& c : frontend.choices_) {
        addChoice(c);
    }
    if (details_enabled_) {
        warnings_.insert(warnings_.end(), frontend.warnings_.begin(), frontend.warnings_.end());
    }
}

std::string TranslationReport::toJson() const {
    std::ostringstream o;
    o << "{\"fidelity\":";
    writeFidelity(o, fidelity_);

    o << ",\"provenance\":{"
      << "\"somtparser_version\":" << quote(provenance_.somtparser_version)
      << ",\"language_id\":" << quote(provenance_.language_id)
      << ",\"language_version\":" << quote(provenance_.language_version)
      << ",\"ops_schema_version\":" << quote(provenance_.ops_schema_version)
      << ",\"ops_content_hash\":" << quote(provenance_.ops_content_hash)
      << ",\"profile_id\":" << quote(provenance_.profile_id)
      << ",\"profile_content_hash\":" << quote(provenance_.profile_content_hash)
      << ",\"target_dialect\":" << quote(provenance_.target_dialect)
      << '}';

    o << ",\"stats\":{"
      << "\"num_vars\":" << stats_.num_vars
      << ",\"num_constraints\":" << stats_.num_constraints
      << ",\"num_objectives\":" << stats_.num_objectives
      << ",\"num_smt_nodes\":" << stats_.num_smt_nodes
      << ",\"max_quantifier_alternations\":" << stats_.max_quantifier_alternations
      << ",\"translate_ms\":" << stats_.translate_ms
      << ",\"parse_ms\":" << stats_.parse_ms
      << ",\"typecheck_ms\":" << stats_.typecheck_ms
      << ",\"passes_ms\":" << stats_.passes_ms
      << ",\"lower_ms\":" << stats_.lower_ms
      << ",\"semantics_ms\":" << stats_.semantics_ms
      << '}';

    o << ",\"hir_feature_counts\":";
    writeCountMap(o, feature_counts_);
    o << ",\"smt_theory_usage\":";
    writeCountMap(o, theory_usage_);

    o << ",\"choices\":[";
    for (std::size_t i = 0; i < choices_.size(); ++i) {
        const auto& c = choices_[i];
        if (i != 0) { o << ','; }
        o << "{\"site\":" << quote(c.site)
          << ",\"unified_op\":" << quote(c.unified_op)
          << ",\"strategy\":" << quote(c.strategy)
          << ",\"rationale\":" << quote(c.rationale)
          << ",\"fidelity\":";
        writeFidelity(o, c.fidelity);
        if (c.count_evidence) {
            o << ",\"count_evidence\":{\"kind\":"
              << quote(evidenceKindName(c.count_evidence->kind))
              << ",\"rationale\":" << quote(c.count_evidence->rationale)
              << ",\"references\":[";
            for (std::size_t ref = 0; ref < c.count_evidence->references.size(); ++ref) {
                if (ref != 0) { o << ','; }
                o << quote(c.count_evidence->references[ref]);
            }
            o << "]}";
        }
        o << '}';
    }
    o << ']';

    o << ",\"warnings\":[";
    for (std::size_t i = 0; i < warnings_.size(); ++i) {
        const auto& w = warnings_[i];
        if (i != 0) { o << ','; }
        o << "{\"severity\":" << quote(severityName(w.severity))
          << ",\"code\":" << quote(errorCodeName(w.code))
          << ",\"message\":" << quote(w.message)
          << ",\"file\":" << quote(w.loc.file)
          << ",\"line\":" << w.loc.line
          << ",\"column\":" << w.loc.column << '}';
    }
    o << "]}";
    return o.str();
}

} // namespace SOMTParser::Uir
