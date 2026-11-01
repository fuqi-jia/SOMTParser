#include <algorithm>
#include <new>
#include <ostream>
#include <stdexcept>
#include <string>
#include <streambuf>
#include <sstream>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {

class FailingBuffer final : public std::streambuf {
public:
    explicit FailingBuffer(std::size_t byte_limit) : byte_limit_(byte_limit) {}

    const std::string& accepted() const { return accepted_; }

protected:
    std::streamsize xsputn(const char* source, std::streamsize count) override {
        if (count <= 0) return 0;
        const std::size_t room = byte_limit_ > accepted_.size()
            ? byte_limit_ - accepted_.size() : 0;
        const std::size_t copied = std::min(room, static_cast<std::size_t>(count));
        accepted_.append(source, copied);
        return static_cast<std::streamsize>(copied);
    }

    int_type overflow(int_type value) override {
        if (traits_type::eq_int_type(value, traits_type::eof())) {
            return traits_type::not_eof(value);
        }
        if (accepted_.size() >= byte_limit_) return traits_type::eof();
        accepted_.push_back(traits_type::to_char_type(value));
        return value;
    }

private:
    std::size_t byte_limit_;
    std::string accepted_;
};

class AllocationFailureBuffer final : public std::streambuf {
protected:
    std::streamsize xsputn(const char*, std::streamsize) override {
        throw std::bad_alloc();
    }
    int_type overflow(int_type) override { throw std::bad_alloc(); }
};

template <typename Writer>
void verify_rejects_failed_sink(Writer&& writer) {
    FailingBuffer buffer(2);
    std::ostream output(&buffer);
    bool rejected_partial = false;
    try {
        writer(output);
    } catch (const std::runtime_error& error) {
        rejected_partial = std::string(error.what()).find("failed while writing")
            != std::string::npos;
    }
    VERIFY(rejected_partial);
    VERIFY(!buffer.accepted().empty());
    VERIFY(output.bad());
}

} // namespace

int main() {
    auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic ALL)\n(declare-const x Int)\n"));
    const auto variable = parser->mkExpr("x");
    VERIFY(variable != nullptr);

    std::ostringstream streamed;
    dumpSMTLIB2(variable, streamed);
    VERIFY(streamed.str() == "x");
    VERIFY(dumpSMTLIB2(variable) == streamed.str());

    const auto expression = parser->mkExpr("(+ x 1)");
    VERIFY(expression != nullptr);
    std::ostringstream expression_stream;
    dumpSMTLIB2(expression, expression_stream);
    VERIFY(dumpSMTLIB2(expression) == expression_stream.str());
    VERIFY(expression_stream.str().find("x") != std::string::npos);

    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpSMTLIB2(expression, output);
    });
    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpSMTLIB2Shared(expression, output);
    });

    // Ordinary ostream insertion catches streambuf allocation errors and sets
    // badbit. The serializer must notice that state instead of returning a
    // successfully serialized prefix to a caller using the default mask.
    AllocationFailureBuffer allocation_failure;
    std::ostream allocation_stream(&allocation_failure);
    bool rejected_allocation_failure = false;
    try {
        dumpSMTLIB2(expression, allocation_stream);
    } catch (const std::runtime_error&) {
        rejected_allocation_failure = true;
    }
    VERIFY(rejected_allocation_failure);
    VERIFY(allocation_stream.bad());

    const auto int_sort = parser->mkIntSort();
    const auto zero = parser->mkConstInt(0);
    const auto parameter = parser->mkFunParamVar(int_sort, "x");
    const auto definition = parser->mkFuncDef("constant", {parameter}, int_sort, zero);
    VERIFY(definition != nullptr);
    std::ostringstream definition_stream;
    dumpFuncDef(definition, definition_stream);
    VERIFY(definition_stream.str() == "(define-fun constant ((x Int)) Int 0)");
    VERIFY(dumpFuncDef(definition) == definition_stream.str());
    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpFuncDef(definition, output);
    });

    const auto recursive_parameter = parser->mkFunParamVar(int_sort, "n");
    const auto recursive = parser->mkFuncRec("recursive", {recursive_parameter},
                                               int_sort, zero);
    VERIFY(recursive != nullptr);
    std::ostringstream recursive_stream;
    dumpFuncRec(recursive, recursive_stream);
    VERIFY(recursive_stream.str() == "(define-fun-rec recursive ((n Int)) Int 0)");
    VERIFY(dumpFuncRec(recursive) == recursive_stream.str());
    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpFuncRec(recursive, output);
    });

    const auto group_parameter_f = parser->mkFunParamVar(int_sort, "a");
    const auto group_parameter_g = parser->mkFunParamVar(int_sort, "b");
    const auto recursive_f = parser->mkFuncRec("recursive_f", {group_parameter_f},
                                                int_sort, zero);
    const auto one = parser->mkConstInt(1);
    const auto recursive_g = parser->mkFuncRec("recursive_g", {group_parameter_g},
                                                int_sort, one);
    const std::vector<std::shared_ptr<DAGNode>> group{recursive_f, recursive_g};
    std::ostringstream group_stream;
    dumpFuncsRec(group, group_stream);
    VERIFY(group_stream.str() ==
           "(define-funs-rec ((recursive_f ((a Int)) Int) "
           "(recursive_g ((b Int)) Int)) (0 1))");
    VERIFY(dumpFuncsRec(group) == group_stream.str());
    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpFuncsRec(group, output);
    });

    const auto declaration = parser->mkFuncDec("declared", {int_sort},
                                                parser->mkBoolSort());
    VERIFY(declaration != nullptr);
    std::ostringstream declaration_stream;
    dumpFuncDec(declaration, declaration_stream);
    VERIFY(declaration_stream.str() == "(declare-fun declared (Int) Bool)");
    VERIFY(dumpFuncDec(declaration) == declaration_stream.str());
    verify_rejects_failed_sink([&](std::ostream& output) {
        dumpFuncDec(declaration, output);
    });

    // An unshared SELECT needs no let prefix. The fallback must have emitted
    // nothing before the ordinary printer writes the body once.
    const auto array_sort = parser->mkArraySort(int_sort, int_sort);
    const auto array_parameter = parser->mkFunParamVar(array_sort, "items");
    const auto index_parameter = parser->mkFunParamVar(int_sort, "index");
    const auto select_body = parser->mkSelect(array_parameter, index_parameter);
    const auto fallback_definition = parser->mkFuncDef(
        "lookup", {array_parameter, index_parameter}, int_sort, select_body);
    std::ostringstream fallback_stream;
    dumpFuncDef(fallback_definition, fallback_stream);
    VERIFY(fallback_stream.str() ==
           "(define-fun lookup ((items (Array Int Int)) (index Int)) Int "
           "(select items index))");
}
