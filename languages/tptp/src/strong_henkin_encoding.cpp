#include "strong_henkin_encoding.h"

#include <algorithm>
#include <functional>
#include <stdexcept>
#include <utility>

namespace SOMTParser::Lang::ThfPrototype {
namespace H = SOMTParser::Uir::Hir;

namespace {
using ExprPtr = H::ExprPtr;

std::string typeKey(const Type& type) {
    switch (type.kind) {
    case Type::Kind::BOOL: return "o";
    case Type::Kind::INT: return "$int";
    case Type::Kind::REAL: return "$real";
    case Type::Kind::INDIVIDUAL: return "i:" + type.name;
    case Type::Kind::ARROW:
        if (!type.domain || !type.codomain) {
            throw std::invalid_argument("malformed THF arrow type");
        }
        return "(" + typeKey(*type.domain) + ">" + typeKey(*type.codomain) + ")";
    }
    throw std::invalid_argument("unknown THF type kind");
}

ExprPtr eq(ExprPtr left, ExprPtr right) {
    return H::mkOp(H::Op::EQ, {std::move(left), std::move(right)});
}
ExprPtr logicalNot(ExprPtr value) {
    return H::mkOp(H::Op::NOT, {std::move(value)});
}
ExprPtr conjunction(std::vector<ExprPtr> values) {
    if (values.empty()) { return H::mkBool(true); }
    if (values.size() == 1) { return values.front(); }
    return H::mkOp(H::Op::AND, std::move(values));
}
ExprPtr disjunction(std::vector<ExprPtr> values) {
    if (values.empty()) { return H::mkBool(false); }
    if (values.size() == 1) { return values.front(); }
    return H::mkOp(H::Op::OR, std::move(values));
}
ExprPtr implication(ExprPtr left, ExprPtr right) {
    return H::mkOp(H::Op::IMPLIES, {std::move(left), std::move(right)});
}
ExprPtr iff(ExprPtr left, ExprPtr right) {
    return disjunction({conjunction({left, right}),
                        conjunction({logicalNot(left), logicalNot(right)})});
}

void visit(const FunctionTermPtr& term,
           const std::function<void(const FunctionTermPtr&)>& f) {
    if (!term) { return; }
    f(term);
    switch (term->kind) {
    case FunctionTerm::Kind::HIR_VALUE:
    case FunctionTerm::Kind::BOUND: break;
    case FunctionTerm::Kind::APPLY:
        visit(term->function, f); visit(term->argument, f); break;
    case FunctionTerm::Kind::LAMBDA:
    case FunctionTerm::Kind::FORALL:
    case FunctionTerm::Kind::EXISTS:
    case FunctionTerm::Kind::NOT:
        visit(term->body, f); break;
    case FunctionTerm::Kind::EQUAL:
    case FunctionTerm::Kind::AND:
    case FunctionTerm::Kind::OR:
    case FunctionTerm::Kind::IMPLIES:
        visit(term->left, f); visit(term->right, f); break;
    }
}

void collectFreeBinders(const FunctionTermPtr& term,
                        std::unordered_set<std::uint64_t>& bound,
                        std::unordered_set<std::uint64_t>& free) {
    if (!term) { return; }
    if (term->kind == FunctionTerm::Kind::BOUND) {
        if (bound.count(term->binder_id) == 0) { free.insert(term->binder_id); }
        return;
    }
    if (term->kind == FunctionTerm::Kind::LAMBDA
        || term->kind == FunctionTerm::Kind::FORALL
        || term->kind == FunctionTerm::Kind::EXISTS) {
        const bool inserted = bound.insert(term->binder_id).second;
        collectFreeBinders(term->body, bound, free);
        if (inserted) { bound.erase(term->binder_id); }
        return;
    }
    switch (term->kind) {
    case FunctionTerm::Kind::HIR_VALUE:
    case FunctionTerm::Kind::BOUND:
    case FunctionTerm::Kind::LAMBDA:
    case FunctionTerm::Kind::FORALL:
    case FunctionTerm::Kind::EXISTS: break;
    case FunctionTerm::Kind::APPLY:
        collectFreeBinders(term->function, bound, free);
        collectFreeBinders(term->argument, bound, free);
        break;
    case FunctionTerm::Kind::NOT: collectFreeBinders(term->body, bound, free); break;
    case FunctionTerm::Kind::EQUAL:
    case FunctionTerm::Kind::AND:
    case FunctionTerm::Kind::OR:
    case FunctionTerm::Kind::IMPLIES:
        collectFreeBinders(term->left, bound, free);
        collectFreeBinders(term->right, bound, free);
        break;
    }
}
}

StrongHenkinEncoding::StrongHenkinEncoding(H::ConstraintModel& model) : model_(model) {}

H::Sort StrongHenkinEncoding::objectSort() const { return object_sort_; }
H::Sort StrongHenkinEncoding::typeCodeSort() const { return type_code_sort_; }

std::string StrongHenkinEncoding::encodedName(const char* prefix,
                                             const std::string& source) const {
    static const char* hex = "0123456789abcdef";
    std::string out(prefix);
    out.push_back('_');
    out.reserve(out.size() + source.size() * 2);
    for (unsigned char c : source) {
        out.push_back(hex[c >> 4]);
        out.push_back(hex[c & 15]);
    }
    return out;
}

std::string StrongHenkinEncoding::freshName(const char* prefix) {
    auto exists = [&](const std::string& name) {
        if (std::any_of(model_.decls.begin(), model_.decls.end(),
                [&](const H::VarDecl& d) { return d.name == name; })) { return true; }
        if (std::any_of(model_.funs.begin(), model_.funs.end(),
                [&](const H::FunDecl& f) { return f.name == name; })) { return true; }
        if (std::any_of(model_.uninterpreted_sorts.begin(), model_.uninterpreted_sorts.end(),
                [&](const H::UninterpretedSortDecl& d) { return d.name == name; })) { return true; }
        return std::any_of(model_.datatypes.begin(), model_.datatypes.end(),
                [&](const H::DatatypeDecl& d) {
                    if (d.name == name) { return true; }
                    return std::any_of(d.constructors.begin(), d.constructors.end(),
                        [&](const H::DtConstructor& c) {
                            return c.name == name || std::any_of(c.selectors.begin(),
                                c.selectors.end(), [&](const H::DtSelector& s) {
                                    return s.name == name;
                                });
                        });
                });
    };
    std::string candidate;
    do { candidate = std::string(prefix) + "_" + std::to_string(fresh_++); }
    while (exists(candidate));
    return candidate;
}

void StrongHenkinEncoding::collectType(const Type& type) {
    if (type.kind == Type::Kind::INT || type.kind == Type::Kind::REAL) {
        throw std::invalid_argument(
            "THF $int/$real require their interpreted arithmetic semantics");
    }
    if (type.kind == Type::Kind::BOOL || type.kind == Type::Kind::INDIVIDUAL) {
        if (type.kind == Type::Kind::INDIVIDUAL && type.name.empty()) {
            throw std::invalid_argument("empty THF base type name");
        }
        base_type_names_.insert(typeKey(type));
    } else if (type.kind == Type::Kind::ARROW) {
        if (!type.domain || !type.codomain) {
            throw std::invalid_argument("malformed THF arrow type");
        }
        collectType(*type.domain);
        collectType(*type.codomain);
    }
}

void StrongHenkinEncoding::collectTermTypes(const FunctionTermPtr& term) {
    visit(term, [&](const FunctionTermPtr& node) {
        collectType(node->type);
        if (node->binder) {
            collectType(node->binder->type);
            binder_types_.emplace(node->binder->id, node->binder->type);
        }
    });
}

H::ExprPtr StrongHenkinEncoding::typeCode(const Type& type) const {
    if (!prepared_) { throw std::logic_error("THF type codes requested before encode()"); }
    if (type.kind == Type::Kind::ARROW) {
        if (!type.domain || !type.codomain) {
            throw std::invalid_argument("malformed THF arrow type");
        }
        return H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
            {typeCode(*type.domain), typeCode(*type.codomain)});
    }
    const auto found = base_constructors_.find(typeKey(type));
    if (found == base_constructors_.end()) {
        throw std::invalid_argument("THF base type was not registered");
    }
    return H::mkDtConstructor(found->second, type_code_sort_, {});
}

void StrongHenkinEncoding::addConstraint(ExprPtr formula, const char* label,
                                         Uir::SourceLoc source) {
    (void)label;
    model_.constraints.push_back(H::Constraint{std::move(formula), false, 1.0, {}, {},
                                               std::move(source)});
}

ExprPtr StrongHenkinEncoding::hasType(ExprPtr value, const Type& type) const {
    return H::mkApply(has_type_name_, H::Sort::boolean(),
                      {std::move(value), typeCode(type)});
}

ExprPtr StrongHenkinEncoding::app(ExprPtr function, ExprPtr argument) const {
    return H::mkApply(app_name_, object_sort_,
                      {std::move(function), std::move(argument)});
}

ExprPtr StrongHenkinEncoding::objectBoolean(ExprPtr formula) const {
    return H::mkOp(H::Op::ITE, {std::move(formula),
        H::mkIdent(true_object_name_, object_sort_),
        H::mkIdent(false_object_name_, object_sort_)});
}

ExprPtr StrongHenkinEncoding::freshBound(const char* stem) {
    return H::mkBoundVar(freshName(stem), object_sort_);
}

void StrongHenkinEncoding::declareEncodingSymbols() {
    type_code_sort_name_ = freshName("__thf_TypeCode");
    type_code_sort_ = H::Sort::datatype(type_code_sort_name_);
    object_sort_ = H::Sort::uninterpreted(freshName("__thf_Object"));
    model_.uninterpreted_sorts.push_back(
        H::UninterpretedSortDecl{object_sort_.name, 0, {}});

    std::vector<std::string> type_keys(base_type_names_.begin(), base_type_names_.end());
    std::sort(type_keys.begin(), type_keys.end());
    H::DatatypeDecl type_codes;
    type_codes.name = type_code_sort_name_;
    for (const std::string& key : type_keys) {
        const std::string ctor = freshName("__thf_tc_base");
        base_constructors_.emplace(key, ctor);
        type_codes.constructors.push_back(H::DtConstructor{ctor, {}});
    }
    arrow_constructor_name_ = freshName("__thf_tc_arrow");
    const std::string domain_selector = freshName("__thf_tc_domain");
    const std::string codomain_selector = freshName("__thf_tc_codomain");
    type_codes.constructors.push_back(H::DtConstructor{arrow_constructor_name_, {
        H::DtSelector{domain_selector, type_code_sort_},
        H::DtSelector{codomain_selector, type_code_sort_}}});
    model_.datatypes.push_back(std::move(type_codes));

    has_type_name_ = freshName("__thf_has_type");
    app_name_ = freshName("__thf_apply");
    is_true_name_ = freshName("__thf_is_true");
    not_name_ = freshName("__thf_not");
    and_name_ = freshName("__thf_and");
    or_name_ = freshName("__thf_or");
    implies_name_ = freshName("__thf_implies");
    equality_name_ = freshName("__thf_equal");
    forall_name_ = freshName("__thf_forall");
    exists_name_ = freshName("__thf_exists");
    identity_name_ = freshName("__thf_I");
    k_name_ = freshName("__thf_K");
    s_name_ = freshName("__thf_S");
    choice_name_ = freshName("__thf_choice");
    true_object_name_ = freshName("__thf_true");
    false_object_name_ = freshName("__thf_false");

    model_.funs.push_back(H::FunDecl{has_type_name_,
        {object_sort_, type_code_sort_}, H::Sort::boolean(), {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{app_name_,
        {object_sort_, object_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{is_true_name_,
        {object_sort_}, H::Sort::boolean(), {}, {}, {}, false});
    model_.decls.push_back(H::VarDecl{not_name_, object_sort_, {}, {}, {}, false});
    model_.decls.push_back(H::VarDecl{and_name_, object_sort_, {}, {}, {}, false});
    model_.decls.push_back(H::VarDecl{or_name_, object_sort_, {}, {}, {}, false});
    model_.decls.push_back(H::VarDecl{implies_name_, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{equality_name_,
        {type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{forall_name_,
        {type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{exists_name_,
        {type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{identity_name_,
        {type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{k_name_,
        {type_code_sort_, type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{s_name_,
        {type_code_sort_, type_code_sort_, type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.funs.push_back(H::FunDecl{choice_name_,
        {type_code_sort_}, object_sort_, {}, {}, {}, false});
    model_.decls.push_back(H::VarDecl{true_object_name_, object_sort_, {}, {}, {}, true});
    model_.decls.push_back(H::VarDecl{false_object_name_, object_sort_, {}, {}, {}, true});
}

void StrongHenkinEncoding::addCoreAxioms() {
    const Type boolean = Type::boolean();
    const ExprPtr truth = H::mkIdent(true_object_name_, object_sort_);
    const ExprPtr falsity = H::mkIdent(false_object_name_, object_sort_);
    const ExprPtr bool_code = typeCode(boolean);
    const ExprPtr bool_membership_t = hasType(truth, boolean);
    const ExprPtr bool_membership_f = hasType(falsity, boolean);
    addConstraint(conjunction({logicalNot(eq(truth, falsity)), bool_membership_t,
                               bool_membership_f,
                               H::mkApply(is_true_name_, H::Sort::boolean(), {truth}),
                               logicalNot(H::mkApply(is_true_name_, H::Sort::boolean(),
                                                     {falsity}))}),
                  "THF Boolean objects and truth interpretation");

    ExprPtr x = freshBound("__thf_bool_obj");
    ExprPtr typed_bool = H::mkApply(has_type_name_, H::Sort::boolean(), {x, bool_code});
    ExprPtr bool_cases = disjunction({eq(x, truth), eq(x, falsity)});
    addConstraint(H::mkForall({H::Binder{x->name, object_sort_}},
                              implication(typed_bool, bool_cases)),
                  "THF truth type has exactly two values");

    auto arrow = [&](ExprPtr domain, ExprPtr codomain) {
        return H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
                                  {std::move(domain), std::move(codomain)});
    };
    auto boolTypeCode = [&]() { return typeCode(boolean); };
    auto isTrue = [&](ExprPtr value) {
        return H::mkApply(is_true_name_, H::Sort::boolean(), {std::move(value)});
    };
    auto typedObject = [&](ExprPtr value, const ExprPtr& code) {
        return H::mkApply(has_type_name_, H::Sort::boolean(), {std::move(value), code});
    };

    // Logical constants are values in the source Henkin model, not only
    // target-level syntax. Give each its generic type and characteristic
    // equation so that function quantification ranges over a domain closed
    // under these constants even when they are never mentioned explicitly.
    const ExprPtr bool_code_for_ops = boolTypeCode();
    const ExprPtr not_type = arrow(bool_code_for_ops, bool_code_for_ops);
    const ExprPtr and_type = arrow(bool_code_for_ops,
        arrow(bool_code_for_ops, bool_code_for_ops));
    ExprPtr not_value = H::mkIdent(not_name_, object_sort_);
    ExprPtr and_value = H::mkIdent(and_name_, object_sort_);
    ExprPtr or_value = H::mkIdent(or_name_, object_sort_);
    ExprPtr implies_value = H::mkIdent(implies_name_, object_sort_);
    addConstraint(typedObject(not_value, not_type), "typed THF negation");
    addConstraint(typedObject(and_value, and_type), "typed THF conjunction");
    addConstraint(typedObject(or_value, and_type), "typed THF disjunction");
    addConstraint(typedObject(implies_value, and_type), "typed THF implication");

    ExprPtr logical_x = freshBound("__thf_logic_x");
    ExprPtr logical_y = freshBound("__thf_logic_y");
    ExprPtr logical_not_result = app(not_value, logical_x);
    ExprPtr logical_not_axiom = implication(typedObject(logical_x, bool_code_for_ops),
        conjunction({typedObject(logical_not_result, bool_code_for_ops),
            iff(isTrue(logical_not_result), logicalNot(isTrue(logical_x)))}));
    addConstraint(H::mkForall({H::Binder{logical_x->name, object_sort_}},
        std::move(logical_not_axiom)), "THF negation semantics");

    auto addBinaryLogical = [&](const std::string& name, ExprPtr value,
                                const char* label, const std::function<ExprPtr(ExprPtr, ExprPtr)>& op) {
        (void)name;
        ExprPtr result = app(app(value, logical_x), logical_y);
        ExprPtr semantics = implication(conjunction({
            typedObject(logical_x, bool_code_for_ops),
            typedObject(logical_y, bool_code_for_ops)}),
            conjunction({typedObject(result, bool_code_for_ops),
                iff(isTrue(result), op(isTrue(logical_x), isTrue(logical_y)))}));
        addConstraint(H::mkForall({H::Binder{logical_x->name, object_sort_},
                                   H::Binder{logical_y->name, object_sort_}},
                                  std::move(semantics)), label);
    };
    addBinaryLogical(and_name_, and_value, "THF conjunction semantics",
        [](ExprPtr p, ExprPtr q) { return conjunction({std::move(p), std::move(q)}); });
    addBinaryLogical(or_name_, or_value, "THF disjunction semantics",
        [](ExprPtr p, ExprPtr q) { return disjunction({std::move(p), std::move(q)}); });
    addBinaryLogical(implies_name_, implies_value, "THF implication semantics",
        [](ExprPtr p, ExprPtr q) { return implication(std::move(p), std::move(q)); });

    // Equality and quantifiers are polymorphic families indexed by TypeCode.
    ExprPtr eq_a = H::mkBoundVar(freshName("__thf_eq_type"), type_code_sort_);
    ExprPtr eq_value = H::mkApply(equality_name_, object_sort_, {eq_a});
    ExprPtr eq_type = arrow(eq_a, arrow(eq_a, bool_code_for_ops));
    ExprPtr eq_x = freshBound("__thf_eq_x");
    ExprPtr eq_y = freshBound("__thf_eq_y");
    ExprPtr eq_result = app(app(eq_value, eq_x), eq_y);
    ExprPtr eq_semantics = conjunction({typedObject(eq_value, eq_type),
        H::mkForall({H::Binder{eq_x->name, object_sort_},
                     H::Binder{eq_y->name, object_sort_}},
            implication(conjunction({typedObject(eq_x, eq_a), typedObject(eq_y, eq_a)}),
                conjunction({typedObject(eq_result, bool_code_for_ops),
                             iff(isTrue(eq_result), eq(eq_x, eq_y))}))) });
    addConstraint(H::mkForall({H::Binder{eq_a->name, type_code_sort_}},
        std::move(eq_semantics)), "THF polymorphic equality");

    auto addQuantifierFamily = [&](const std::string& symbol, bool universal) {
        ExprPtr quantified_type = H::mkBoundVar(freshName("__thf_quantifier_type"),
                                                type_code_sort_);
        ExprPtr predicate_type = arrow(quantified_type, bool_code_for_ops);
        ExprPtr quantifier_type = arrow(predicate_type, bool_code_for_ops);
        ExprPtr quantifier = H::mkApply(symbol, object_sort_, {quantified_type});
        ExprPtr predicate = freshBound("__thf_quantifier_predicate");
        ExprPtr value = freshBound("__thf_quantifier_value");
        ExprPtr application = app(predicate, value);
        ExprPtr pointwise = universal
            ? implication(typedObject(value, quantified_type), isTrue(application))
            : conjunction({typedObject(value, quantified_type), isTrue(application)});
        ExprPtr aggregate = universal
            ? H::mkForall({H::Binder{value->name, object_sort_}}, std::move(pointwise))
            : H::mkExists({H::Binder{value->name, object_sort_}}, std::move(pointwise));
        ExprPtr result = app(quantifier, predicate);
        ExprPtr body = conjunction({typedObject(quantifier, quantifier_type),
            H::mkForall({H::Binder{predicate->name, object_sort_}},
                implication(typedObject(predicate, predicate_type),
                    conjunction({typedObject(result, bool_code_for_ops),
                                 iff(isTrue(result), std::move(aggregate))}))) });
        addConstraint(H::mkForall({H::Binder{quantified_type->name, type_code_sort_}},
            std::move(body)), universal ? "THF polymorphic universal quantifier"
                                        : "THF polymorphic existential quantifier");
    };
    addQuantifierFamily(forall_name_, true);
    addQuantifierFamily(exists_name_, false);

    // Typed carriers are disjoint and nonempty. The recursive datatype gives
    // precisely the well-founded simple type codes; quantifying these schemas
    // over it is the polymorphic instance required by the strong axiom.
    ExprPtr value = freshBound("__thf_value");
    ExprPtr a = H::mkBoundVar(freshName("__thf_type_a"), type_code_sort_);
    ExprPtr b = H::mkBoundVar(freshName("__thf_type_b"), type_code_sort_);
    ExprPtr typed_a = H::mkApply(has_type_name_, H::Sort::boolean(), {value, a});
    ExprPtr typed_b = H::mkApply(has_type_name_, H::Sort::boolean(), {value, b});
    addConstraint(H::mkForall({H::Binder{value->name, object_sort_},
                                H::Binder{a->name, type_code_sort_},
                                H::Binder{b->name, type_code_sort_}},
        implication(conjunction({typed_a, typed_b}), eq(a, b))),
        "THF type domains are disjoint");

    ExprPtr t = H::mkBoundVar(freshName("__thf_type"), type_code_sort_);
    ExprPtr any_value = freshBound("__thf_nonempty_value");
    ExprPtr nonempty = H::mkExists({H::Binder{any_value->name, object_sort_}},
        H::mkApply(has_type_name_, H::Sort::boolean(), {any_value, t}));
    addConstraint(H::mkForall({H::Binder{t->name, type_code_sort_}}, nonempty),
                  "every simple type has a nonempty carrier");

    ExprPtr f = freshBound("__thf_app_f");
    ExprPtr y = freshBound("__thf_app_x");
    ExprPtr domain = H::mkBoundVar(freshName("__thf_app_domain"), type_code_sort_);
    ExprPtr codomain = H::mkBoundVar(freshName("__thf_app_codomain"), type_code_sort_);
    ExprPtr function_code = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
                                               {domain, codomain});
    ExprPtr apply_typed = implication(conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {f, function_code}),
        H::mkApply(has_type_name_, H::Sort::boolean(), {y, domain})}),
        H::mkApply(has_type_name_, H::Sort::boolean(), {app(f, y), codomain}));
    addConstraint(H::mkForall({H::Binder{f->name, object_sort_},
        H::Binder{y->name, object_sort_},
        H::Binder{domain->name, type_code_sort_},
        H::Binder{codomain->name, type_code_sort_}}, std::move(apply_typed)),
        "THF application preserves typing");

    // Extensionality states that target object equality reflects THF
    // functional equality on the entire source domain.
    ExprPtr left = freshBound("__thf_ext_left");
    ExprPtr right = freshBound("__thf_ext_right");
    ExprPtr arg_type = H::mkBoundVar(freshName("__thf_ext_domain"), type_code_sort_);
    ExprPtr result_type = H::mkBoundVar(freshName("__thf_ext_codomain"), type_code_sort_);
    ExprPtr ext_fn_type = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
                                             {arg_type, result_type});
    ExprPtr ext_arg = freshBound("__thf_ext_arg");
    ExprPtr ext_pointwise = H::mkForall({H::Binder{ext_arg->name, object_sort_}},
        implication(H::mkApply(has_type_name_, H::Sort::boolean(), {ext_arg, arg_type}),
            eq(app(left, ext_arg), app(right, ext_arg))));
    ExprPtr extensionality = implication(conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {left, ext_fn_type}),
        H::mkApply(has_type_name_, H::Sort::boolean(), {right, ext_fn_type}),
        ext_pointwise}), eq(left, right));
    addConstraint(H::mkForall({H::Binder{left->name, object_sort_},
        H::Binder{right->name, object_sort_},
        H::Binder{arg_type->name, type_code_sort_},
        H::Binder{result_type->name, type_code_sort_}}, std::move(extensionality)),
        "THF function extensionality");

    // Polymorphic identity combinator.
    ExprPtr ia = H::mkBoundVar(freshName("__thf_i_type"), type_code_sort_);
    ExprPtr iv = H::mkApply(identity_name_, object_sort_, {ia});
    ExprPtr i_type = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {ia, ia});
    ExprPtr ix = freshBound("__thf_i_x");
    ExprPtr i_axiom = conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {iv, i_type}),
        H::mkForall({H::Binder{ix->name, object_sort_}},
            implication(H::mkApply(has_type_name_, H::Sort::boolean(), {ix, ia}),
                        eq(app(iv, ix), ix)))});
    addConstraint(H::mkForall({H::Binder{ia->name, type_code_sort_}}, std::move(i_axiom)),
                  "THF polymorphic identity combinator");

    // Polymorphic K combinator: K x y = x.
    ExprPtr ka = H::mkBoundVar(freshName("__thf_k_a"), type_code_sort_);
    ExprPtr kb = H::mkBoundVar(freshName("__thf_k_b"), type_code_sort_);
    ExprPtr kv = H::mkApply(k_name_, object_sort_, {ka, kb});
    ExprPtr kb_to_a = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {kb, ka});
    ExprPtr k_type = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {ka, kb_to_a});
    ExprPtr kx = freshBound("__thf_k_x");
    ExprPtr ky = freshBound("__thf_k_y");
    ExprPtr k_axiom = conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {kv, k_type}),
        H::mkForall({H::Binder{kx->name, object_sort_}, H::Binder{ky->name, object_sort_}},
            implication(conjunction({
                H::mkApply(has_type_name_, H::Sort::boolean(), {kx, ka}),
                H::mkApply(has_type_name_, H::Sort::boolean(), {ky, kb})}),
                eq(app(app(kv, kx), ky), kx)))});
    addConstraint(H::mkForall({H::Binder{ka->name, type_code_sort_},
        H::Binder{kb->name, type_code_sort_}}, std::move(k_axiom)),
        "THF polymorphic K combinator");

    // Polymorphic S combinator: S f g x = f x (g x).
    ExprPtr sa = H::mkBoundVar(freshName("__thf_s_a"), type_code_sort_);
    ExprPtr sb = H::mkBoundVar(freshName("__thf_s_b"), type_code_sort_);
    ExprPtr sc = H::mkBoundVar(freshName("__thf_s_c"), type_code_sort_);
    ExprPtr b_to_c = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {sb, sc});
    ExprPtr a_to_b_to_c = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
        {sa, b_to_c});
    ExprPtr a_to_b = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {sa, sb});
    ExprPtr a_to_c = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_, {sa, sc});
    ExprPtr a_to_b_to_a_to_c = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
        {a_to_b, a_to_c});
    ExprPtr s_type = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
        {a_to_b_to_c, a_to_b_to_a_to_c});
    ExprPtr sv = H::mkApply(s_name_, object_sort_, {sa, sb, sc});
    ExprPtr sf = freshBound("__thf_s_f");
    ExprPtr sg = freshBound("__thf_s_g");
    ExprPtr sx = freshBound("__thf_s_x");
    ExprPtr s_axiom = conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {sv, s_type}),
        H::mkForall({H::Binder{sf->name, object_sort_}, H::Binder{sg->name, object_sort_},
                     H::Binder{sx->name, object_sort_}},
            implication(conjunction({
                H::mkApply(has_type_name_, H::Sort::boolean(), {sf, a_to_b_to_c}),
                H::mkApply(has_type_name_, H::Sort::boolean(), {sg, a_to_b}),
                H::mkApply(has_type_name_, H::Sort::boolean(), {sx, sa})}),
                eq(app(app(app(sv, sf), sg), sx),
                   app(app(sf, sx), app(sg, sx)))))});
    addConstraint(H::mkForall({H::Binder{sa->name, type_code_sort_},
        H::Binder{sb->name, type_code_sort_}, H::Binder{sc->name, type_code_sort_}},
        std::move(s_axiom)), "THF polymorphic S combinator");

    // Polymorphic choice: if a typed predicate has a witness, its selected
    // value satisfies the predicate. This is the source TH0 choice obligation.
    ExprPtr ca = H::mkBoundVar(freshName("__thf_choice_type"), type_code_sort_);
    ExprPtr bool_code_for_choice = typeCode(boolean);
    ExprPtr pred_type = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
                                           {ca, bool_code_for_choice});
    ExprPtr pred_to_a = H::mkDtConstructor(arrow_constructor_name_, type_code_sort_,
                                            {pred_type, ca});
    ExprPtr choice = H::mkApply(choice_name_, object_sort_, {ca});
    ExprPtr cp = freshBound("__thf_choice_pred");
    ExprPtr cx = freshBound("__thf_choice_witness");
    ExprPtr chosen = app(choice, cp);
    ExprPtr has_witness = H::mkExists({H::Binder{cx->name, object_sort_}},
        conjunction({H::mkApply(has_type_name_, H::Sort::boolean(), {cx, ca}),
                     H::mkApply(is_true_name_, H::Sort::boolean(), {app(cp, cx)})}));
    ExprPtr choice_axiom = conjunction({
        H::mkApply(has_type_name_, H::Sort::boolean(), {choice, pred_to_a}),
        H::mkForall({H::Binder{cp->name, object_sort_}}, implication(
            conjunction({H::mkApply(has_type_name_, H::Sort::boolean(), {cp, pred_type}),
                         has_witness}),
            H::mkApply(is_true_name_, H::Sort::boolean(), {app(cp, chosen)})))});
    addConstraint(H::mkForall({H::Binder{ca->name, type_code_sort_}},
                              std::move(choice_axiom)),
                  "THF polymorphic choice");
}

void StrongHenkinEncoding::encode(const ThfFile& file) {
    if (prepared_) { throw std::logic_error("StrongHenkinEncoding::encode is one-shot"); }
    static const std::unordered_set<std::string> supported_roles = {
        "axiom", "hypothesis", "definition", "assumption", "lemma",
        "theorem", "corollary", "conjecture", "negated_conjecture"};
    for (const auto& formula : file.formulas) {
        if (supported_roles.count(formula.role) == 0) {
            throw std::invalid_argument("THF formula role '" + formula.role
                + "' has no supported input-problem semantics");
        }
    }
    collectType(Type::boolean());
    for (const auto& declaration : file.type_declarations) { collectType(declaration.type); }
    for (const auto& entry : file.signature) { collectType(entry.second); }
    for (const auto& formula : file.formulas) { collectTermTypes(formula.term); }
    declareEncodingSymbols();
    prepared_ = true;
    addCoreAxioms();

    std::vector<std::string> source_names;
    source_names.reserve(file.signature.size());
    for (const auto& entry : file.signature) { source_names.push_back(entry.first); }
    std::sort(source_names.begin(), source_names.end());
    for (const std::string& source_name : source_names) {
        const std::string target_name = freshName(
            encodedName("__thf_source", source_name).c_str());
        Uir::SourceLoc loc;
        for (const auto& declaration : file.type_declarations) {
            if (!declaration.declares_type_symbol && declaration.name == source_name) {
                loc = Uir::SourceLoc{declaration.source.file,
                    static_cast<int>(declaration.source.line),
                    static_cast<int>(declaration.source.column)};
                break;
            }
        }
        model_.decls.push_back(H::VarDecl{target_name, object_sort_, {}, {},
                                           loc, false});
        ExprPtr value = H::mkIdent(target_name, object_sort_);
        source_symbols_.emplace(source_name, value);
        addConstraint(hasType(value, file.signature.at(source_name)),
                      "typed THF source constant", std::move(loc));
    }

    std::vector<ExprPtr> negated_conjectures;
    Uir::SourceLoc conjecture_source;
    for (const auto& formula : file.formulas) {
        std::unordered_map<std::uint64_t, ExprPtr> scope;
        ExprPtr lowered = lowerFormula(formula.term, scope);
        const Uir::SourceLoc source{formula.source.file,
            static_cast<int>(formula.source.line),
            static_cast<int>(formula.source.column)};
        if (formula.role == "conjecture") {
            if (negated_conjectures.empty()) { conjecture_source = source; }
            negated_conjectures.push_back(logicalNot(std::move(lowered)));
        } else {
            // In particular, a TPTP `negated_conjecture` is already a
            // satisfiability assertion and must remain conjoined as written.
            addConstraint(std::move(lowered), formula.name.c_str(), source);
        }
    }
    if (!negated_conjectures.empty()) {
        // A TPTP theorem succeeds only if every positive conjecture follows.
        // A countermodel therefore satisfies Axioms and NOT(C1 AND ... AND Cn),
        // equivalently the disjunction of all negated positive conjectures.
        addConstraint(disjunction(std::move(negated_conjectures)),
            "TPTP positive-conjecture refutation",
            std::move(conjecture_source));
    }
}

ExprPtr StrongHenkinEncoding::lowerObject(const FunctionTermPtr& term,
    std::unordered_map<std::uint64_t, ExprPtr>& scope) {
    if (!term) { throw std::invalid_argument("null THF term during lowering"); }
    switch (term->kind) {
    case FunctionTerm::Kind::HIR_VALUE: {
        if (!term->hir_value) { throw std::invalid_argument("empty THF HIR value"); }
        if (term->hir_value->kind == H::ExprKind::LIT_BOOL) {
            return H::mkIdent(term->hir_value->bool_value ? true_object_name_ : false_object_name_,
                              object_sort_);
        }
        const auto found = source_symbols_.find(term->hir_value->name);
        if (found == source_symbols_.end()) {
            throw std::invalid_argument("undeclared THF source value: "
                                        + term->hir_value->name);
        }
        return found->second;
    }
    case FunctionTerm::Kind::BOUND: {
        const auto found = scope.find(term->binder_id);
        if (found == scope.end()) {
            throw std::invalid_argument("unbound THF value during lowering: " + term->hint);
        }
        return found->second;
    }
    case FunctionTerm::Kind::APPLY:
        return app(lowerObject(term->function, scope), lowerObject(term->argument, scope));
    case FunctionTerm::Kind::LAMBDA: return lowerLambda(term, scope);
    case FunctionTerm::Kind::FORALL:
    case FunctionTerm::Kind::EXISTS:
    case FunctionTerm::Kind::EQUAL:
    case FunctionTerm::Kind::NOT:
    case FunctionTerm::Kind::AND:
    case FunctionTerm::Kind::OR:
    case FunctionTerm::Kind::IMPLIES:
        return objectBoolean(lowerFormula(term, scope));
    }
    throw std::invalid_argument("unknown THF expression kind");
}

ExprPtr StrongHenkinEncoding::lowerFormula(const FunctionTermPtr& term,
    std::unordered_map<std::uint64_t, ExprPtr>& scope) {
    if (!term || term->type.kind != Type::Kind::BOOL) {
        throw std::invalid_argument("THF formula lowering requires a Bool term");
    }
    switch (term->kind) {
    case FunctionTerm::Kind::HIR_VALUE:
    case FunctionTerm::Kind::BOUND:
        return H::mkApply(is_true_name_, H::Sort::boolean(), {lowerObject(term, scope)});
    case FunctionTerm::Kind::APPLY:
        return H::mkApply(is_true_name_, H::Sort::boolean(), {lowerObject(term, scope)});
    case FunctionTerm::Kind::FORALL:
    case FunctionTerm::Kind::EXISTS: {
        if (!term->binder) { throw std::invalid_argument("THF quantifier lacks binder"); }
        ExprPtr variable = H::mkBoundVar(freshName("__thf_quantified"), object_sort_);
        auto prior = scope.find(term->binder_id);
        if (prior != scope.end()) { throw std::invalid_argument("duplicate active binder id"); }
        if (binder_types_.count(term->binder_id) == 0) {
            throw std::invalid_argument("THF quantifier binder type was not registered");
        }
        scope.emplace(term->binder_id, variable);
        ExprPtr body = lowerFormula(term->body, scope);
        scope.erase(term->binder_id);
        ExprPtr member = hasType(variable, term->binder->type);
        ExprPtr guarded = term->kind == FunctionTerm::Kind::FORALL
            ? implication(std::move(member), std::move(body))
            : conjunction({std::move(member), std::move(body)});
        return term->kind == FunctionTerm::Kind::FORALL
            ? H::mkForall({H::Binder{variable->name, object_sort_}}, std::move(guarded))
            : H::mkExists({H::Binder{variable->name, object_sort_}}, std::move(guarded));
    }
    case FunctionTerm::Kind::EQUAL:
        if (term->left->type.kind == Type::Kind::BOOL) {
            return iff(lowerFormula(term->left, scope), lowerFormula(term->right, scope));
        }
        return eq(lowerObject(term->left, scope), lowerObject(term->right, scope));
    case FunctionTerm::Kind::NOT:
        return logicalNot(lowerFormula(term->body, scope));
    case FunctionTerm::Kind::AND:
        return H::mkOp(H::Op::AND, {lowerFormula(term->left, scope),
                                    lowerFormula(term->right, scope)});
    case FunctionTerm::Kind::OR:
        return H::mkOp(H::Op::OR, {lowerFormula(term->left, scope),
                                   lowerFormula(term->right, scope)});
    case FunctionTerm::Kind::IMPLIES:
        return H::mkOp(H::Op::IMPLIES, {lowerFormula(term->left, scope),
                                        lowerFormula(term->right, scope)});
    case FunctionTerm::Kind::LAMBDA:
        return H::mkApply(is_true_name_, H::Sort::boolean(), {lowerObject(term, scope)});
    }
    throw std::invalid_argument("unknown THF formula kind");
}

ExprPtr StrongHenkinEncoding::lowerLambda(const FunctionTermPtr& term,
    std::unordered_map<std::uint64_t, ExprPtr>& scope) {
    if (!term->binder || !term->type.isArrow()) {
        throw std::invalid_argument("malformed THF lambda node");
    }
    std::unordered_set<std::uint64_t> local_bound{term->binder_id};
    std::unordered_set<std::uint64_t> free_ids;
    collectFreeBinders(term->body, local_bound, free_ids);
    std::vector<std::uint64_t> captures(free_ids.begin(), free_ids.end());
    std::sort(captures.begin(), captures.end());

    std::vector<ExprPtr> capture_actuals;
    std::vector<Sort> parameter_sorts;
    std::vector<H::Binder> quantified;
    std::unordered_map<std::uint64_t, ExprPtr> body_scope;
    std::vector<ExprPtr> capture_bounds;
    for (std::uint64_t id : captures) {
        const auto outer = scope.find(id);
        const auto type = binder_types_.find(id);
        if (outer == scope.end() || type == binder_types_.end()) {
            throw std::invalid_argument("THF lambda capture is outside its lexical scope");
        }
        capture_actuals.push_back(outer->second);
        ExprPtr bound = H::mkBoundVar(freshName("__thf_capture"), object_sort_);
        quantified.push_back(H::Binder{bound->name, object_sort_});
        parameter_sorts.push_back(object_sort_);
        capture_bounds.push_back(bound);
        body_scope.emplace(id, bound);
    }

    const std::string helper_name = freshName("__thf_lambda");
    ExprPtr lambda_value;
    if (captures.empty()) {
        model_.decls.push_back(H::VarDecl{helper_name, object_sort_, {}, {}, {}, true});
        lambda_value = H::mkIdent(helper_name, object_sort_);
    } else {
        model_.funs.push_back(H::FunDecl{helper_name, parameter_sorts, object_sort_,
                                         {}, {}, {}, false});
        lambda_value = H::mkApply(helper_name, object_sort_, capture_actuals);
    }

    ExprPtr argument = H::mkBoundVar(freshName("__thf_lambda_arg"), object_sort_);
    quantified.push_back(H::Binder{argument->name, object_sort_});
    body_scope.emplace(term->binder_id, argument);
    ExprPtr body_value = lowerObject(term->body, body_scope);

    std::vector<ExprPtr> guards;
    for (std::size_t i = 0; i < captures.size(); ++i) {
        guards.push_back(hasType(capture_bounds[i], binder_types_.at(captures[i])));
    }
    guards.push_back(hasType(argument, term->binder->type));
    ExprPtr lambda_at = captures.empty()
        ? lambda_value
        : H::mkApply(helper_name, object_sort_, capture_bounds);
    ExprPtr equation = eq(app(lambda_at, argument), std::move(body_value));
    ExprPtr member = hasType(lambda_at, term->type);
    ExprPtr definition = implication(conjunction(std::move(guards)),
                                     conjunction({std::move(member), std::move(equation)}));
    addConstraint(H::mkForall(std::move(quantified), std::move(definition)),
                  "closure-lifted THF lambda definition",
                  Uir::SourceLoc{term->source.file,
                      static_cast<int>(term->source.line),
                      static_cast<int>(term->source.column)});
    return lambda_value;
}

} // namespace SOMTParser::Lang::ThfPrototype
