#include "explicit_function_hir.h"

#include <stdexcept>
#include <utility>

namespace SOMTParser::Lang::ThfPrototype {
namespace H = SOMTParser::Uir::Hir;

namespace {
bool sameType(const Type& a, const Type& b) {
    if (a.kind != b.kind || a.name != b.name) { return false; }
    if (a.kind != Type::Kind::ARROW) { return true; }
    return a.domain && b.domain && a.codomain && b.codomain
        && sameType(*a.domain, *b.domain) && sameType(*a.codomain, *b.codomain);
}
FunctionTermPtr node(FunctionTerm::Kind k, Type t) {
    auto out = std::make_shared<FunctionTerm>();
    out->kind = k;
    out->type = std::move(t);
    return out;
}
Type typeFromSort(const H::Sort& sort) {
    switch (sort.kind) {
    case H::SortKind::BOOL: return Type::boolean();
    case H::SortKind::INT: return Type::integer();
    case H::SortKind::REAL: return Type::real();
    case H::SortKind::UNINTERPRETED: return Type::individual(sort.name);
    case H::SortKind::ARRAY:
        if (!sort.index || !sort.elem) {
            throw std::invalid_argument("malformed array sort in THF value import");
        }
        return Type::arrow(typeFromSort(*sort.index), typeFromSort(*sort.elem));
    default:
        throw std::invalid_argument("HIR value sort has no THF simple-type mapping");
    }
}
}

FunctionBinder FunctionHirBuilder::binder(std::string hint, Type type) {
    return binder(std::move(hint), std::move(type), {});
}

FunctionBinder FunctionHirBuilder::binder(std::string hint, Type type, SourceSpan source) {
    if (hint.empty()) { throw std::invalid_argument("THF binder needs a name"); }
    return FunctionBinder{next_binder_++, std::move(hint), std::move(type),
                          std::move(source)};
}

FunctionTermPtr FunctionHirBuilder::value(H::ExprPtr value) {
    if (!value) { throw std::invalid_argument("null HIR value"); }
    Type t = typeFromSort(value->sort);
    auto out = std::const_pointer_cast<FunctionTerm>(node(FunctionTerm::Kind::HIR_VALUE, t));
    out->hir_value = std::move(value);
    return out;
}

FunctionTermPtr FunctionHirBuilder::bound(const FunctionBinder& binder_value) {
    if (binder_value.id == 0 || binder_value.name.empty()) {
        throw std::invalid_argument("THF bound variable needs a valid lexical binder");
    }
    auto out = std::make_shared<FunctionTerm>();
    out->kind = FunctionTerm::Kind::BOUND;
    out->type = binder_value.type;
    out->binder_id = binder_value.id;
    out->hint = binder_value.name;
    return out;
}

FunctionTermPtr FunctionHirBuilder::apply(FunctionTermPtr fn, FunctionTermPtr arg) {
    if (!fn || !arg || !fn->type.isArrow() || !fn->type.domain || !fn->type.codomain
        || !sameType(*fn->type.domain, arg->type)) {
        throw std::invalid_argument("ill-typed THF @ application");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(FunctionTerm::Kind::APPLY,
                                                           *fn->type.codomain));
    out->function = std::move(fn);
    out->argument = std::move(arg);
    return out;
}

FunctionTermPtr FunctionHirBuilder::lambda(const FunctionBinder& b, FunctionTermPtr body) {
    if (!body) { throw std::invalid_argument("null THF lambda body"); }
    if (b.id == 0 || b.name.empty()) {
        throw std::invalid_argument("THF lambda needs a valid lexical binder");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(
        FunctionTerm::Kind::LAMBDA, Type::arrow(b.type, body->type)));
    out->binder = std::make_shared<const FunctionBinder>(b);
    out->binder_id = b.id;
    out->hint = b.name;
    out->body = std::move(body);
    // The body must already refer to the same lexical identity. `bound()` is
    // exposed for constructing that node; names alone never bind occurrences.
    return out;
}

FunctionTermPtr FunctionHirBuilder::quantify(bool universal, const FunctionBinder& b,
                                              FunctionTermPtr body) {
    if (b.id == 0 || b.name.empty() || !body || body->type.kind != Type::Kind::BOOL) {
        throw std::invalid_argument("THF quantifier body must be Bool");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(
        universal ? FunctionTerm::Kind::FORALL : FunctionTerm::Kind::EXISTS,
        Type::boolean()));
    out->binder = std::make_shared<const FunctionBinder>(b);
    out->binder_id = b.id;
    out->hint = b.name;
    out->body = std::move(body);
    return out;
}

FunctionTermPtr FunctionHirBuilder::equal(FunctionTermPtr left, FunctionTermPtr right) {
    if (!left || !right || !sameType(left->type, right->type)) {
        throw std::invalid_argument("THF equality operands must have identical types");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(FunctionTerm::Kind::EQUAL,
                                                           Type::boolean()));
    out->left = std::move(left);
    out->right = std::move(right);
    return out;
}

FunctionTermPtr FunctionHirBuilder::logicalNot(FunctionTermPtr value) {
    if (!value || value->type.kind != Type::Kind::BOOL) {
        throw std::invalid_argument("THF negation operand must be Bool");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(FunctionTerm::Kind::NOT,
                                                           Type::boolean()));
    out->body = std::move(value);
    return out;
}

FunctionTermPtr FunctionHirBuilder::logicalBinary(FunctionTerm::Kind kind,
                                                  FunctionTermPtr left,
                                                  FunctionTermPtr right) {
    if (kind != FunctionTerm::Kind::AND && kind != FunctionTerm::Kind::OR
        && kind != FunctionTerm::Kind::IMPLIES) {
        throw std::invalid_argument("invalid THF binary connective kind");
    }
    if (!left || !right || left->type.kind != Type::Kind::BOOL
        || right->type.kind != Type::Kind::BOOL) {
        throw std::invalid_argument("THF connective operands must be Bool");
    }
    auto out = std::const_pointer_cast<FunctionTerm>(node(kind, Type::boolean()));
    out->left = std::move(left);
    out->right = std::move(right);
    return out;
}

FunctionTermPtr FunctionHirBuilder::withSource(FunctionTermPtr term,
                                                SourceSpan source) const {
    if (!term) { throw std::invalid_argument("cannot locate a null THF term"); }
    auto copy = std::make_shared<FunctionTerm>(*term);
    copy->source = std::move(source);
    return copy;
}

bool FunctionHirBuilder::check(const FunctionTermPtr& term,
                               std::unordered_map<std::uint64_t, Type>& scope) const {
    if (!term) { return false; }
    switch (term->kind) {
    case FunctionTerm::Kind::HIR_VALUE: return term->hir_value != nullptr;
    case FunctionTerm::Kind::BOUND: {
        const auto found = scope.find(term->binder_id);
        return term->binder_id != 0 && found != scope.end()
            && sameType(term->type, found->second);
    }
    case FunctionTerm::Kind::APPLY:
        return term->function && term->argument && check(term->function, scope)
            && check(term->argument, scope) && term->function->type.isArrow()
            && term->function->type.domain
            && term->function->type.codomain
            && sameType(*term->function->type.domain, term->argument->type)
            && sameType(term->type, *term->function->type.codomain);
    case FunctionTerm::Kind::LAMBDA:
    case FunctionTerm::Kind::FORALL:
    case FunctionTerm::Kind::EXISTS: {
        if (!term->binder || term->binder_id == 0 || term->binder->id != term->binder_id) {
            return false;
        }
        if (term->kind == FunctionTerm::Kind::LAMBDA
            && (!term->type.isArrow() || !term->type.domain || !term->type.codomain
                || !sameType(*term->type.domain, term->binder->type))) { return false; }
        if ((term->kind == FunctionTerm::Kind::FORALL || term->kind == FunctionTerm::Kind::EXISTS)
            && term->type.kind != Type::Kind::BOOL) { return false; }
        const bool inserted = scope.emplace(term->binder_id, term->binder->type).second;
        if (!inserted) { return false; }
        const bool ok = check(term->body, scope);
        scope.erase(term->binder_id);
        if (!ok) { return false; }
        return term->kind != FunctionTerm::Kind::LAMBDA
            || sameType(*term->type.codomain, term->body->type);
    }
    case FunctionTerm::Kind::EQUAL:
        return term->left && term->right && check(term->left, scope)
            && check(term->right, scope) && sameType(term->left->type, term->right->type)
            && term->type.kind == Type::Kind::BOOL;
    case FunctionTerm::Kind::NOT:
        return term->body && check(term->body, scope)
            && term->body->type.kind == Type::Kind::BOOL
            && term->type.kind == Type::Kind::BOOL;
    case FunctionTerm::Kind::AND:
    case FunctionTerm::Kind::OR:
    case FunctionTerm::Kind::IMPLIES:
        return term->left && term->right && check(term->left, scope)
            && check(term->right, scope) && term->left->type.kind == Type::Kind::BOOL
            && term->right->type.kind == Type::Kind::BOOL
            && term->type.kind == Type::Kind::BOOL;
    }
    return false;
}

bool FunctionHirBuilder::wellScoped(const FunctionTermPtr& term) const {
    std::unordered_map<std::uint64_t, Type> scope;
    return check(term, scope);
}

} // namespace SOMTParser::Lang::ThfPrototype
