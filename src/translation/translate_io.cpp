#include "translate_internal.h"
#include "somtparser/translation/module.h"

#include <fstream>
#include <iostream>
#include <new>
#include <sstream>

namespace SOMTParser {
namespace {
std::string joined(const std::vector<std::string>& items) {
    std::string out;
    for (const auto& item : items) { if (!out.empty()) out += ", "; out += item; }
    return out;
}
bool parseDialect(const std::string& name, Lower::OmtDialect& out) {
    if (name == "gomt" || name == "smtlib-omt-2025") out = Lower::OmtDialect::Gomt;
    else if (name == "z3") out = Lower::OmtDialect::Z3;
    else if (name == "optimathsat") out = Lower::OmtDialect::OptiMathSAT;
    else if (name == "none") out = Lower::OmtDialect::None;
    else return false;
    return true;
}
const char* severityName(Uir::Severity severity) {
    switch (severity) {
    case Uir::Severity::NOTE: return "note";
    case Uir::Severity::WARNING: return "warning";
    case Uir::Severity::ERROR: return "error";
    }
    return "error";
}
}

// All file/HIR entry points finish through this same output/report policy.
struct TranslationAccess {
    static void releaseDetails(Translation& t, const TranslateOptions& opts) {
        t.details_ = opts.details;
        if (opts.details) return;
        t.parser_.reset();
        t.packed_base_parser_.reset();
        t.lowered_.reset();
        t.model_.reset();
        t.semantics_ = {};
        t.report_ = {};
        std::string().swap(t.module_smt2_);
        std::string().swap(t.module_interface_json_);
        std::vector<std::string>().swap(t.packed_linear_symbols_);
    }

    static Translation failure(int code, std::string text, Uir::ErrorCode error,
                               const TranslateOptions& opts, std::ostream* diagnostics) {
        Translation t;
        t.exit_code_ = code;
        t.diagnostics_.error(error, text.substr(0, text.size() - 1));
        if (diagnostics) { *diagnostics << text; diagnostics->flush(); }
        else t.diagnostic_text_ = std::move(text);
        if (diagnostics && !*diagnostics) t.exit_code_ = 3;
        releaseDetails(t, opts);
        return t;
    }

    static Translation finish(Translation t, const TranslateOptions& opts,
                              std::ostream* output, std::ostream* diagnostics) {
        std::ostringstream captured_output, captured_diagnostics;
        std::ostream& out = output ? *output : captured_output;
        std::ostream& err = diagnostics ? *diagnostics : captured_diagnostics;
        t.captured_output_ = !output;
        t.exit_code_ = t.ok_ ? 0 : 1;
        for (const auto& d : t.diagnostics_.all()) {
            err << severityName(d.severity) << ": ";
            if (!t.module_mode_ && !d.loc.file.empty()) {
                err << d.loc.file << ':' << d.loc.line << ':' << d.loc.column << ": ";
            }
            err << Uir::errorCodeName(d.code) << ": " << d.message << '\n';
        }
        if (!opts.report_path.empty()) {
            // Module interfaces are written only after a successful export;
            // ordinary reports also describe failed translations.
            if (!t.module_mode_ || t.ok_) {
                std::ofstream report(opts.report_path);
                if (report) {
                    report << (t.module_mode_ ? t.module_interface_json_ : t.report_.toJson()) << '\n';
                    report.close();
                }
                if (!report) {
                    err << (t.module_mode_ ? "cannot write module interface\n"
                        : "error: cannot write report to '" + opts.report_path + "'\n");
                    t.exit_code_ = 3;
                }
            }
        }
        if (t.ok_ && t.exit_code_ == 0) {
            try {
                t.writeSmt2(out, opts.omt_dialect);
                out.flush();
                if (!out) {
                    err << "error: cannot write SMT-LIB output\n";
                    t.exit_code_ = 3;
                }
            } catch (const std::bad_alloc&) {
                if (!out) { err << "error: cannot write SMT-LIB output\n"; t.exit_code_ = 3; }
                else {
                    err << "error: E_RESOURCE: memory allocation failed during SMT-LIB output\n";
                    t.diagnostics_.error(Uir::ErrorCode::E_RESOURCE, "memory allocation failed during SMT-LIB output");
                    t.exit_code_ = 1;
                }
            } catch (const std::exception& e) {
                if (!out) { err << "error: cannot write SMT-LIB output\n"; t.exit_code_ = 3; }
                else {
                    err << "error: E_INTERNAL: " << e.what() << '\n';
                    t.diagnostics_.error(Uir::ErrorCode::E_INTERNAL, e.what());
                    t.exit_code_ = 1;
                }
            }
        }
        err.flush();
        if (!err) t.exit_code_ = 3;
        if (t.exit_code_ == 3) {
            t.diagnostics_.error(Uir::ErrorCode::E_IO, "translation report/output stream I/O failed");
        }
        t.completed_smt2_ = captured_output.str();
        t.diagnostic_text_ = captured_diagnostics.str();
        releaseDetails(t, opts);
        return t;
    }

    static Translation module(const Lang::SourceUnit& unit, const TranslateOptions& opts) {
        Translation t;
        t.module_mode_ = true;
        t.dialect_ = opts.omt_dialect;
        const auto imported = Lang::importModule(unit, opts.language_id, opts.parse);
        t.diagnostics_.merge(imported.diagnostics);
        if (!imported.ok()) return t;
        const auto exported = Lang::exportModule(*imported.module);
        t.diagnostics_.merge(exported.diagnostics);
        if (!exported.ok()) return t;
        t.module_smt2_ = exported.smt2;
        t.module_interface_json_ = exported.interface_json;
        if (opts.details) {
            t.report_.mutableProvenance().language_id = imported.module->language;
            t.report_.mutableProvenance().profile_id = "module";
        }
        t.ok_ = true;
        return t;
    }
};

Translation translate(const Lang::SourceUnit& source, const TranslateOptions& options,
                      std::istream* input, std::ostream* output, std::ostream* diagnostics) {
    Lang::SourceUnit unit = source;
    TranslateOptions opts = options;
    auto fail = [&](int code, const std::string& message, Uir::ErrorCode error) {
        return TranslationAccess::failure(code, message, error, opts, diagnostics);
    };
    if (opts.dialect_name && !parseDialect(*opts.dialect_name, opts.omt_dialect)) {
        return fail(2, "unknown dialect '" + *opts.dialect_name + "'\n", Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    if (unit.main_path.empty() && unit.inline_source.empty()) {
        return fail(2, "an input path or source is required\n", Uir::ErrorCode::E_IO);
    }
    if (unit.display_name == "<memory>" && !unit.main_path.empty()) unit.display_name = unit.main_path;
    if (!opts.language_id.empty() && !Lang::LanguageRegistry::instance().byId(opts.language_id)) {
        std::vector<std::string> ids;
        for (const auto* language : Lang::LanguageRegistry::instance().all()) ids.push_back(language->id());
        return fail(2, "unknown language '" + opts.language_id + "'; known: " + joined(ids) + '\n',
                    Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    if (!Uir::EncodingProfile::builtin(opts.profile_id)) {
        return fail(2, "unknown profile '" + opts.profile_id + "'; known: "
                    + joined(Uir::EncodingProfile::builtinIds()) + '\n', Uir::ErrorCode::E_PASS_PIPELINE);
    }
    if (unit.main_path == "-" && unit.inline_source.empty()) {
        if (opts.language_id.empty()) {
            return fail(2, "reading from stdin needs --from: there is no file name to detect the language from\n", Uir::ErrorCode::E_IO);
        }
        std::istream& in = input ? *input : std::cin;
        std::ostringstream buffer;
        char chunk[8192];
        while (in.read(chunk, sizeof(chunk)) || in.gcount() != 0) buffer.write(chunk, in.gcount());
        if (in.bad() || (in.fail() && !in.eof()) || !buffer) {
            return fail(3, "error: cannot read stdin\n", Uir::ErrorCode::E_IO);
        }
        unit.inline_source = buffer.str();
        unit.display_name = "<stdin>";
        if (unit.inline_source.empty()) return fail(1, "error: E_IO: stdin is empty\n", Uir::ErrorCode::E_IO);
    }
    if (opts.module && (opts.profile_explicit || opts.dialect_explicit || opts.dialect_name
                       || opts.profile_id != "default" || opts.omt_dialect != Lower::OmtDialect::Gomt)) {
        return fail(2, "--module cannot be combined with --profile or --dialect\n", Uir::ErrorCode::E_PASS_PIPELINE);
    }
    return TranslationAccess::finish(opts.module ? TranslationAccess::module(unit, opts)
        : translateImpl(unit, opts, nullptr, {}), opts, output, diagnostics);
}

Translation translate(const Uir::Hir::ConstraintModel& model, const TranslateOptions& opts) {
    return translate(model, opts, std::vector<Uir::Hir::LocatedExpr>{});
}
Translation translate(const Uir::Hir::ConstraintModel& model, const TranslateOptions& options,
                      const std::vector<Uir::Hir::LocatedExpr>& source_terms) {
    TranslateOptions opts = options;
    if (!Uir::EncodingProfile::builtin(opts.profile_id)) {
        return TranslationAccess::failure(2, "unknown profile '" + opts.profile_id + "'; known: "
            + joined(Uir::EncodingProfile::builtinIds()) + '\n', Uir::ErrorCode::E_PASS_PIPELINE, opts, nullptr);
    }
    if (opts.module) {
        return TranslationAccess::failure(2, "module export requires a source file or text\n",
                                          Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT, opts, nullptr);
    }
    if (opts.dialect_name && !parseDialect(*opts.dialect_name, opts.omt_dialect)) {
        return TranslationAccess::failure(2, "unknown dialect '" + *opts.dialect_name + "'\n",
                                          Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT, opts, nullptr);
    }
    return TranslationAccess::finish(translateImpl({}, opts,
        std::make_shared<Uir::Hir::ConstraintModel>(model), source_terms), opts, nullptr, nullptr);
}
} // namespace SOMTParser
