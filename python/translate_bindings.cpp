#include "translate_bindings.h"
#include <pybind11/stl.h>

#include "somtparser/translation/translate.h"
#include "somtparser/lowering/omt_emitter.h"

#include <array>
#include <memory>
#include <sstream>
#include <streambuf>

namespace py = pybind11;

namespace {

// Per-call streams: never redirect process-wide cout/cerr or assemble a full
// script when the caller supplies an output sink. Decode incrementally because
// a UTF-8 character may cross a buffer boundary.
class PythonOutputBuffer : public std::streambuf {
public:
    explicit PythonOutputBuffer(const py::object& stream)
        : write_(stream.attr("write")), flush_(stream.attr("flush")),
          decoder_(py::module_::import("codecs").attr("getincrementaldecoder")("utf-8")()) {
        setp(buffer_.data(), buffer_.data() + buffer_.size());
    }

protected:
    int sync() override {
        if (failed_) { return -1; }
        try {
            const auto size = pptr() - pbase();
            const py::object text = decoder_.attr("decode")(py::bytes(pbase(), size));
            setp(buffer_.data(), buffer_.data() + buffer_.size());
            if (py::len(text)) {
                const py::object written = write_(text);
                if (!written.is_none() && written.cast<py::ssize_t>()
                        != static_cast<py::ssize_t>(py::len(text))) {
                    failed_ = true;
                    return -1;
                }
            }
            flush_();
            return 0;
        } catch (const py::error_already_set&) {
            failed_ = true;
            return -1;
        }
    }

    int_type overflow(int_type ch) override {
        if (sync() != 0) { return traits_type::eof(); }
        if (!traits_type::eq_int_type(ch, traits_type::eof())) {
            *pptr() = traits_type::to_char_type(ch);
            pbump(1);
        }
        return traits_type::not_eof(ch);
    }

private:
    std::array<char, 8192> buffer_;
    py::object write_, flush_, decoder_;
    bool failed_ = false;
};

class PythonInputBuffer : public std::streambuf {
public:
    explicit PythonInputBuffer(py::object stream) : stream_(std::move(stream)) {}

protected:
    int_type underflow() override {
        if (gptr() && gptr() < egptr()) { return traits_type::to_int_type(*gptr()); }
        buffer_ = stream_.attr("read")(8192).cast<std::string>();
        if (buffer_.empty()) { return traits_type::eof(); }
        setg(buffer_.data(), buffer_.data(), buffer_.data() + buffer_.size());
        return traits_type::to_int_type(*gptr());
    }

private:
    py::object stream_;
    std::string buffer_;
};

std::optional<std::string> dialectName(const py::object& dialect) {
    if (dialect.is_none()) { return std::nullopt; }
    if (py::isinstance<py::str>(dialect)) { return dialect.cast<std::string>(); }
    if (!py::isinstance<SOMTParser::Lower::OmtDialect>(dialect)) {
        throw py::type_error("dialect must be a string, OmtDialect, or None");
    }
    switch (dialect.cast<SOMTParser::Lower::OmtDialect>()) {
    case SOMTParser::Lower::OmtDialect::Gomt: return "gomt";
    case SOMTParser::Lower::OmtDialect::Z3: return "z3";
    case SOMTParser::Lower::OmtDialect::OptiMathSAT: return "optimathsat";
    case SOMTParser::Lower::OmtDialect::None: return "none";
    }
    throw py::value_error("unknown OmtDialect");
}

} // namespace

namespace SomtPythonTranslate {

void bind(py::module_& m) {
    using namespace SOMTParser;
    m.def("translate", [](const std::string& path, const std::string& source,
                        const std::string& language, const std::optional<std::string>& profile,
                        const py::object& dialect, const std::vector<std::string>& data,
                        const Uir::ParamMap& options,
                        const std::string& report, bool module, bool details, py::object input,
                        const py::object& output, const py::object& diagnostics) {
        Lang::SourceUnit unit;
        unit.main_path = path;
        unit.inline_source = source;
        unit.data_paths = data;
        if (!path.empty()) { unit.display_name = path; }
        TranslateOptions opts;
        opts.language_id = language;
        opts.profile_id = profile.value_or("default");
        opts.profile_explicit = profile.has_value();
        opts.dialect_name = dialectName(dialect);
        opts.dialect_explicit = !dialect.is_none();
        opts.parse.options = options;
        opts.report_path = report;
        opts.module = module;
        opts.details = details;

        if (input.is_none()) { input = py::module_::import("sys").attr("stdin"); }
        PythonInputBuffer input_buffer(std::move(input));
        std::istream in(&input_buffer);
        std::unique_ptr<PythonOutputBuffer> output_buffer, diagnostic_buffer;
        std::unique_ptr<std::ostream> out, err;
        if (!output.is_none()) {
            output_buffer = std::make_unique<PythonOutputBuffer>(output);
            out = std::make_unique<std::ostream>(output_buffer.get());
        }
        if (!diagnostics.is_none()) {
            diagnostic_buffer = std::make_unique<PythonOutputBuffer>(diagnostics);
            err = std::make_unique<std::ostream>(diagnostic_buffer.get());
        }
        return translate(unit, opts, &in, out.get(), err.get());
    }, py::arg("path") = "", py::kw_only(), py::arg("source") = "",
       py::arg("language") = "", py::arg("profile") = py::none(),
       py::arg("dialect") = py::none(), py::arg("data") = std::vector<std::string>{},
       py::arg("options") = Uir::ParamMap{},
       py::arg("report") = "", py::arg("module") = false, py::arg("details") = true,
       py::arg("stdin") = py::none(), py::arg("output") = py::none(),
       py::arg("diagnostics") = py::none(),
       "Translate a model; capture output by default or write to caller-owned text streams.");
}

} // namespace SomtPythonTranslate
