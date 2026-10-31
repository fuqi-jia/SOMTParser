/* -*- Header -*-
 *
 * Diagnostics — errors as return values.
 *
 * Error reporting never throws: recording, merging and inspecting diagnostics
 * are value-based, because translating tens of thousands of benchmarks means
 * one malformed input must degrade to a recorded failure, never an escaped
 * exception that ends the run.
 *
 * Invariant violations do throw, via condAssert. A value outside ErrorCode
 * cannot arise from any input, only from a bad cast, so it is a broken
 * invariant rather than a runtime condition, and it fails loudly instead of
 * being reported as a stand-in name that would corrupt the evaluation's
 * failure statistics.
 *
 * ErrorCode is deliberately a closed, stable enum: it is the denominator of the
 * evaluation's failure-cause breakdown. E_UNSUPPORTED_CONSTRUCT dominating means
 * our coverage is thin (an engineering problem); E_NO_ENCODING dominating means
 * the encoding library is thin (a research problem). Those must not blur.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_DIAGNOSTIC_HEADER
#define SOMTPARSER_TRANSLATION_DIAGNOSTIC_HEADER

#include "somtparser/core/asserting.h"

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

namespace SOMTParser::Uir {

struct SourceLoc {
    std::string file;
    int         line = 0;
    int         column = 0;
};

enum class Severity { NOTE, WARNING, ERROR };

enum class ErrorCode {
    OK = 0,
    E_IO,
    E_LEX,
    E_PARSE,
    E_TYPE,
    E_UNSUPPORTED_CONSTRUCT,  // the language construct is not implemented
    E_NO_ENCODING,            // no encoding available for this op under the profile
    E_FIDELITY_REJECTED,      // below the profile's min_fidelity
    E_PASS_PIPELINE,          // the profile's pass order is not valid
    E_RESOURCE,               // timeout or memory limit
    E_INTERNAL,
};

/** Stable name for @p c, used as the key the evaluation groups failures by.
 *  Never returns a stand-in name for an unrecognized value: a newly added
 *  enumerator that reaches here without a case means this switch is out of
 *  sync with ErrorCode, and silently bucketing it under a fallback name
 *  (e.g. "E_INTERNAL") would quietly corrupt the failure statistics instead
 *  of surfacing the bug. */
inline const char* errorCodeName(ErrorCode c) {
    switch (c) {
    case ErrorCode::OK:                      return "OK";
    case ErrorCode::E_IO:                    return "E_IO";
    case ErrorCode::E_LEX:                   return "E_LEX";
    case ErrorCode::E_PARSE:                 return "E_PARSE";
    case ErrorCode::E_TYPE:                  return "E_TYPE";
    case ErrorCode::E_UNSUPPORTED_CONSTRUCT: return "E_UNSUPPORTED_CONSTRUCT";
    case ErrorCode::E_NO_ENCODING:           return "E_NO_ENCODING";
    case ErrorCode::E_FIDELITY_REJECTED:     return "E_FIDELITY_REJECTED";
    case ErrorCode::E_PASS_PIPELINE:         return "E_PASS_PIPELINE";
    case ErrorCode::E_RESOURCE:              return "E_RESOURCE";
    case ErrorCode::E_INTERNAL:              return "E_INTERNAL";
    }
    condAssert(false, "errorCodeName: value outside ErrorCode");
    return ""; // unreachable; satisfies compilers that don't see condAssert as noreturn
}

struct Diagnostic {
    Severity    severity = Severity::ERROR;
    ErrorCode   code = ErrorCode::E_INTERNAL;
    std::string message;
    SourceLoc   loc;
};

class Diagnostics {
public:
    /** @p code must name an actual failure. Reporting an error under
     *  ErrorCode::OK is a programming mistake, not a runtime condition: the
     *  evaluation buckets failures by code, so an error filed under "no error"
     *  would be counted as a success cause. Fail loudly instead. */
    void error(ErrorCode code, std::string message, SourceLoc loc = {}) {
        condAssert(code != ErrorCode::OK,
                   "Diagnostics::error: an error cannot carry ErrorCode::OK");
        add(Severity::ERROR, code, std::move(message), std::move(loc));
    }
    void warn(ErrorCode code, std::string message, SourceLoc loc = {}) {
        add(Severity::WARNING, code, std::move(message), std::move(loc));
    }
    void note(ErrorCode code, std::string message, SourceLoc loc = {}) {
        add(Severity::NOTE, code, std::move(message), std::move(loc));
    }

    /** Append @p other's entries, preserving order and error state. */
    void merge(const Diagnostics& other) {
        for (const auto& d : other.items_) {
            items_.push_back(d);
            if (d.severity == Severity::ERROR) {
                has_errors_ = true;
                if (first_error_ == ErrorCode::OK) {
                    first_error_ = d.code;
                }
            }
        }
    }

    /** Whether any ERROR-severity entry was recorded. Deliberately tracked
     *  independently of first_error_: deriving it from the code would make
     *  hasErrors() disagree with what was actually recorded for any error
     *  whose code happens to be OK, and this predicate gates translate()'s
     *  failure paths. */
    bool hasErrors() const noexcept { return has_errors_; }
    /** The first error's code, or OK when there was none. */
    ErrorCode firstErrorCode() const noexcept { return first_error_; }
    const std::vector<Diagnostic>& all() const noexcept { return items_; }
    std::size_t size() const noexcept { return items_.size(); }

private:
    void add(Severity sev, ErrorCode code, std::string message, SourceLoc loc) {
        items_.push_back(Diagnostic{sev, code, std::move(message), std::move(loc)});
        if (sev == Severity::ERROR) {
            has_errors_ = true;
            if (first_error_ == ErrorCode::OK) {
                first_error_ = code;
            }
        }
    }

    std::vector<Diagnostic> items_;
    ErrorCode               first_error_ = ErrorCode::OK;
    bool                    has_errors_ = false;
};

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_TRANSLATION_DIAGNOSTIC_HEADER */
