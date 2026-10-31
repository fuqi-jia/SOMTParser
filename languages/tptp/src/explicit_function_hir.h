#pragma once

#include "henkin_encoding.h"

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>

namespace SOMTParser::Lang::ThfPrototype {

/** Lexically scoped, first-class function HIR node proposal (never an Array). */
struct FunctionTerm;
using FunctionTermPtr = std::shared_ptr<const FunctionTerm>;

struct SourceSpan {
    std::string file;
    std::uint32_t line = 0;
    std::uint32_t column = 0;
};

/** A lexical binder has identity independent of its source spelling. */
struct FunctionBinder {
    std::uint64_t id = 0;
    std::string name;
    Type type;
    SourceSpan source;
};

struct FunctionTerm {
    enum class Kind {
        HIR_VALUE, BOUND, APPLY, LAMBDA, FORALL, EXISTS, EQUAL,
        NOT, AND, OR, IMPLIES
    } kind;
    Type type;
    SourceSpan source;
    std::uint64_t binder_id = 0;
    std::string hint;
    Uir::Hir::ExprPtr hir_value;
    std::shared_ptr<const FunctionBinder> binder;
    FunctionTermPtr function;
    FunctionTermPtr argument;
    FunctionTermPtr body;
    FunctionTermPtr left;
    FunctionTermPtr right;
};

class FunctionHirBuilder {
public:
    FunctionBinder binder(std::string hint, Type type);
    FunctionBinder binder(std::string hint, Type type, SourceSpan source);
    FunctionTermPtr value(Uir::Hir::ExprPtr value);
    FunctionTermPtr bound(const FunctionBinder& binder);
    FunctionTermPtr apply(FunctionTermPtr function, FunctionTermPtr argument);
    FunctionTermPtr lambda(const FunctionBinder& binder, FunctionTermPtr body);
    FunctionTermPtr quantify(bool universal, const FunctionBinder& binder,
                             FunctionTermPtr boolean_body);
    FunctionTermPtr equal(FunctionTermPtr left, FunctionTermPtr right);
    FunctionTermPtr logicalNot(FunctionTermPtr value);
    FunctionTermPtr logicalBinary(FunctionTerm::Kind kind, FunctionTermPtr left,
                                  FunctionTermPtr right);
    FunctionTermPtr withSource(FunctionTermPtr term, SourceSpan source) const;

    /** Check lexical binder identity and all nodes' local type invariants. */
    bool wellScoped(const FunctionTermPtr& term) const;

private:
    bool check(const FunctionTermPtr& term, std::unordered_map<std::uint64_t, Type>& scope) const;
    std::uint64_t next_binder_ = 1;
};

} // namespace SOMTParser::Lang::ThfPrototype
