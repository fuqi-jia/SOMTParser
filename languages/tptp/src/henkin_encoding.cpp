#include "henkin_encoding.h"

#include <algorithm>
#include <stdexcept>
#include <utility>

namespace SOMTParser::Lang::ThfPrototype {
namespace H = SOMTParser::Uir::Hir;

namespace {
H::ExprPtr conjunction(std::vector<H::ExprPtr> xs) {
    if (xs.empty()) { return H::mkBool(true); }
    if (xs.size() == 1) { return xs.front(); }
    return H::mkOp(H::Op::AND, std::move(xs));
}
H::ExprPtr implication(H::ExprPtr a, H::ExprPtr b) {
    return H::mkOp(H::Op::IMPLIES, {std::move(a), std::move(b)});
}
H::ExprPtr eq(H::ExprPtr a, H::ExprPtr b) {
    return H::mkOp(H::Op::EQ, {std::move(a), std::move(b)});
}
H::ExprPtr selected(H::ExprPtr f, H::ExprPtr x) {
    return H::mkOp(H::Op::SELECT, {std::move(f), std::move(x)});
}
}

Type Type::boolean() { return Type{Kind::BOOL}; }
Type Type::integer() { return Type{Kind::INT}; }
Type Type::real() { return Type{Kind::REAL}; }
Type Type::individual(std::string n) {
    Type t{Kind::INDIVIDUAL}; t.name = std::move(n); return t;
}
Type Type::arrow(Type a, Type b) {
    Type t{Kind::ARROW};
    t.domain = std::make_shared<const Type>(std::move(a));
    t.codomain = std::make_shared<const Type>(std::move(b));
    return t;
}

HenkinEncoding::HenkinEncoding(H::ConstraintModel& model) : model_(model) {}

void HenkinEncoding::reserveSourceNames(const std::vector<std::string>& names) {
    if (!domain_names_.empty()) {
        throw std::logic_error("THF source names must be reserved before type lowering");
    }
    for (const std::string& name : names) {
        if (!name.empty()) { reserved_names_.insert(name); }
    }
}

std::string HenkinEncoding::key(const Type& t) const {
    switch (t.kind) {
    case Type::Kind::BOOL: return "o";
    case Type::Kind::INT: return "int";
    case Type::Kind::REAL: return "real";
    case Type::Kind::INDIVIDUAL: return "i:" + t.name;
    case Type::Kind::ARROW:
        if (!t.domain || !t.codomain) { throw std::invalid_argument("malformed arrow type"); }
        return "(" + key(*t.domain) + ">" + key(*t.codomain) + ")";
    }
    throw std::invalid_argument("unknown THF type");
}

bool HenkinEncoding::hasFullFiniteDomain(const Type& t) const {
    switch (t.kind) {
    case Type::Kind::BOOL: return true;
    case Type::Kind::ARROW:
        return t.domain && t.codomain
            && hasFullFiniteDomain(*t.domain) && hasFullFiniteDomain(*t.codomain);
    case Type::Kind::INT:
    case Type::Kind::REAL:
    case Type::Kind::INDIVIDUAL:
        return false;
    }
    return false;
}

std::string HenkinEncoding::domainName(const Type& t) {
    const auto k = key(t);
    auto found = domain_names_.find(k);
    if (found != domain_names_.end()) { return found->second; }
    // Hex-encode the structural key so generated identifiers are deterministic
    // and cannot collide due to punctuation or source symbol spelling.
    static const char* hex = "0123456789abcdef";
    std::string suffix;
    suffix.reserve(k.size() * 2);
    for (unsigned char c : k) { suffix.push_back(hex[c >> 4]); suffix.push_back(hex[c & 15]); }
    std::string name = "__thf_domain_" + suffix;
    auto collides = [&](const std::string& candidate) {
        return std::any_of(model_.funs.begin(), model_.funs.end(), [&](const H::FunDecl& f) {
                   return f.name == candidate;
               }) || std::any_of(model_.decls.begin(), model_.decls.end(), [&](const H::VarDecl& d) {
                   return d.name == candidate;
               }) || reserved_names_.count(candidate) != 0;
    };
    const std::string base = name;
    for (std::size_t n = 1; collides(name); ++n) {
        name = base + "_" + std::to_string(n);
    }
    domain_names_.emplace(k, name);
    return name;
}

H::Sort HenkinEncoding::sortOf(const Type& t) {
    switch (t.kind) {
    case Type::Kind::BOOL: return H::Sort::boolean();
    case Type::Kind::INT: return H::Sort::integer();
    case Type::Kind::REAL: return H::Sort::real();
    case Type::Kind::INDIVIDUAL: return H::Sort::uninterpreted(t.name);
    case Type::Kind::ARROW:
        if (!t.domain || !t.codomain) { throw std::invalid_argument("malformed arrow type"); }
        ensureType(t);
        return H::Sort::array(sortOf(*t.domain), sortOf(*t.codomain));
    }
    throw std::invalid_argument("unknown THF type");
}

H::ExprPtr HenkinEncoding::declareValue(std::string name, const Type& t, bool auxiliary) {
    if (name.empty()) { throw std::invalid_argument("THF value needs a name"); }
    if (std::any_of(model_.decls.begin(), model_.decls.end(), [&](const H::VarDecl& d) {
            return d.name == name;
        }) || std::any_of(model_.funs.begin(), model_.funs.end(), [&](const H::FunDecl& f) {
            return f.name == name;
        })) {
        throw std::invalid_argument("THF value name is already declared");
    }
    const H::Sort s = sortOf(t);
    model_.decls.push_back(H::VarDecl{name, s, {}, {}, {}, auxiliary});
    H::ExprPtr value = H::mkIdent(name, s);
    if (t.isArrow() && !hasFullFiniteDomain(t)) {
        addConstraint(member(t, value), "THF function constant belongs to its type domain");
    }
    return value;
}

H::ExprPtr HenkinEncoding::rawMember(const Type& t, H::ExprPtr value) {
    if (!t.isArrow() || hasFullFiniteDomain(t)) { return H::mkBool(true); }
    return H::mkApply(domainName(t), H::Sort::boolean(), {std::move(value)});
}

H::ExprPtr HenkinEncoding::member(const Type& t, H::ExprPtr value) {
    (void)sortOf(t);
    if (!value || !H::sameSort(value->sort, sortOf(t))) {
        throw std::invalid_argument("THF membership value has the wrong sort");
    }
    return rawMember(t, std::move(value));
}

H::ExprPtr HenkinEncoding::apply(const Type& ft, H::ExprPtr f, H::ExprPtr x) {
    if (!ft.isArrow() || !ft.domain || !ft.codomain) {
        throw std::invalid_argument("THF application requires an arrow type");
    }
    const auto fs = sortOf(ft);
    const auto xs = sortOf(*ft.domain);
    if (!f || !x || !H::sameSort(f->sort, fs) || !H::sameSort(x->sort, xs)) {
        throw std::invalid_argument("THF application argument or function has the wrong sort");
    }
    return selected(std::move(f), std::move(x));
}

H::ExprPtr HenkinEncoding::equal(const Type& t, H::ExprPtr a, H::ExprPtr b) {
    if (!a || !b || !H::sameSort(a->sort, sortOf(t)) || !H::sameSort(b->sort, sortOf(t))) {
        throw std::invalid_argument("THF equality operands have different types");
    }
    if (!t.isArrow()) { return eq(std::move(a), std::move(b)); }
    const std::string n = "__thf_ext_x_" + std::to_string(fresh_++);
    H::ExprPtr x = H::mkBoundVar(n, sortOf(*t.domain));
    H::ExprPtr pointwise = equal(*t.codomain,
        apply(t, a, x), apply(t, b, x));
    H::ExprPtr guarded = implication(member(*t.domain, x), pointwise);
    return H::mkForall({H::Binder{n, sortOf(*t.domain)}}, std::move(guarded));
}

void HenkinEncoding::ensureBooleanConstantLambdas(const Type& domain) {
    (void)sortOf(domain);
    const std::string type_key = key(domain);
    if (boolean_constant_closures_.count(type_key) != 0) { return; }

    auto fresh_name = [&](const char* stem) {
        std::string candidate;
        do {
            candidate = std::string("__thf_") + stem + "_" + std::to_string(fresh_++);
        } while (reserved_names_.count(candidate) != 0
                 || std::any_of(model_.decls.begin(), model_.decls.end(),
                     [&](const H::VarDecl& d) { return d.name == candidate; })
                 || std::any_of(model_.funs.begin(), model_.funs.end(),
                     [&](const H::FunDecl& f) { return f.name == candidate; }));
        return candidate;
    };

    const std::string false_name = fresh_name("logical_false");
    const std::string true_name = fresh_name("logical_true");
    const std::string arg_name = fresh_name("logical_arg");
    const TypedBinder argument{arg_name, domain};
    (void)lambda(false_name, argument, Type::boolean(), H::mkBool(false));
    (void)lambda(true_name, argument, Type::boolean(), H::mkBool(true));
    boolean_constant_closures_.insert(type_key);
}

H::ExprPtr HenkinEncoding::quantify(bool universal, const TypedBinder& b,
                                    H::ExprPtr body) {
    if (b.type.isArrow() && !hasFullFiniteDomain(b.type)) {
        throw std::invalid_argument(
            "THF function quantification requires complete Henkin lambda closure; unsupported");
    }
    if (!body || !H::sameSort(body->sort, H::Sort::boolean())) {
        throw std::invalid_argument("THF quantified body must be Bool");
    }
    const auto s = sortOf(b.type);
    H::ExprPtr v = H::mkBoundVar(b.name, s);
    H::ExprPtr guarded = std::move(body);
    return universal ? H::mkForall({H::Binder{b.name, s}}, std::move(guarded))
                     : H::mkExists({H::Binder{b.name, s}}, std::move(guarded));
}

void HenkinEncoding::addConstraint(H::ExprPtr f, const std::string& label) {
    (void)label;
    model_.constraints.push_back(H::Constraint{std::move(f), false, 1.0, {}, {}, {}});
}

void HenkinEncoding::ensureType(const Type& t) {
    const std::string k = key(t);
    if (emitted_.count(k)) { return; }
    // Mark before descent: simple types are acyclic, but this also makes a
    // malformed self-referential client input fail deterministically below.
    emitted_.emplace(k, true);
    if (t.kind == Type::Kind::INDIVIDUAL) {
        if (t.name.empty()) { throw std::invalid_argument("THF individual sort needs a name"); }
        if (std::none_of(model_.uninterpreted_sorts.begin(), model_.uninterpreted_sorts.end(),
                [&](const H::UninterpretedSortDecl& d) { return d.name == t.name && d.arity == 0; })) {
            model_.uninterpreted_sorts.push_back(H::UninterpretedSortDecl{t.name, 0, {}});
        }
    } else if (t.kind == Type::Kind::ARROW) {
        if (!t.domain || !t.codomain) { throw std::invalid_argument("malformed arrow type"); }
        ensureType(*t.domain);
        ensureType(*t.codomain);
        if (!hasFullFiniteDomain(t)) { addArrowAxioms(t); }
    }
}

void HenkinEncoding::addArrowAxioms(const Type& t) {
    const H::Sort fs = H::Sort::array(sortOf(*t.domain), sortOf(*t.codomain));
    const std::string dname = domainName(t);
    if (std::none_of(model_.funs.begin(), model_.funs.end(), [&](const H::FunDecl& f) {
            return f.name == dname;
        })) {
        model_.funs.push_back(H::FunDecl{dname, {fs}, H::Sort::boolean(), {}, {}, {}, true});
    }

    const std::string fn = "__thf_f_" + std::to_string(fresh_++);
    const std::string xn = "__thf_x_" + std::to_string(fresh_++);
    H::ExprPtr f = H::mkBoundVar(fn, fs);
    H::ExprPtr x = H::mkBoundVar(xn, sortOf(*t.domain));
    H::ExprPtr fx = apply(t, f, x);
    H::ExprPtr closure = implication(
        conjunction({rawMember(t, f), rawMember(*t.domain, x)}),
        rawMember(*t.codomain, fx));
    addConstraint(H::mkForall({H::Binder{fn, fs}, H::Binder{xn, sortOf(*t.domain)}},
                              std::move(closure)), "THF function application closure");

    H::ExprPtr nonempty = H::mkExists({H::Binder{fn, fs}}, rawMember(t, f));
    addConstraint(std::move(nonempty), "THF function domain is nonempty");

    const std::string gn = "__thf_g_" + std::to_string(fresh_++);
    H::ExprPtr g = H::mkBoundVar(gn, fs);
    H::ExprPtr pointwise = equal(*t.codomain, apply(t, f, x), apply(t, g, x));
    H::ExprPtr all_points = H::mkForall({H::Binder{xn, sortOf(*t.domain)},
        }, implication(rawMember(*t.domain, x), std::move(pointwise)));
    H::ExprPtr same_rep = implication(
        conjunction({rawMember(t, f), rawMember(t, g), std::move(all_points)}),
        eq(f, g));
    addConstraint(H::mkForall({H::Binder{fn, fs}, H::Binder{gn, fs}},
                              std::move(same_rep)), "THF extensional representative uniqueness");
}

H::ExprPtr HenkinEncoding::lambda(std::string name, const TypedBinder& arg,
                                  const Type& result, H::ExprPtr body) {
    return lambda(std::move(name), {}, {}, arg, result, std::move(body));
}

H::ExprPtr HenkinEncoding::lambda(std::string name,
                                  const std::vector<TypedBinder>& captures,
                                  const std::vector<H::ExprPtr>& capture_values,
                                  const TypedBinder& arg,
                                  const Type& result, H::ExprPtr body) {
    if (name.empty() || !body || !H::sameSort(body->sort, sortOf(result))) {
        throw std::invalid_argument("THF lambda body has the wrong type");
    }
    if (captures.size() != capture_values.size()) {
        throw std::invalid_argument("THF lambda capture arity mismatch");
    }
    Type ft = Type::arrow(arg.type, result);
    const H::Sort fs = sortOf(ft);
    if (std::any_of(model_.decls.begin(), model_.decls.end(), [&](const H::VarDecl& d) {
            return d.name == name;
        }) || std::any_of(model_.funs.begin(), model_.funs.end(), [&](const H::FunDecl& f) {
            return f.name == name;
        }) || reserved_names_.count(name) != 0) {
        throw std::invalid_argument("THF lambda target name is already declared");
    }
    std::vector<H::Sort> parameter_sorts;
    std::vector<H::Binder> binders;
    std::vector<H::ExprPtr> helper_arguments;
    std::vector<H::ExprPtr> guards;
    std::unordered_map<std::string, bool> capture_names;
    for (std::size_t i = 0; i < captures.size(); ++i) {
        if (captures[i].name.empty() || captures[i].name == arg.name
            || !capture_names.emplace(captures[i].name, true).second) {
            throw std::invalid_argument("THF lambda capture binders must have distinct names");
        }
        const auto s = sortOf(captures[i].type);
        if (!capture_values[i] || !H::sameSort(capture_values[i]->sort, s)) {
            throw std::invalid_argument("THF lambda capture has the wrong sort");
        }
        parameter_sorts.push_back(s);
        binders.push_back(H::Binder{captures[i].name, s});
        H::ExprPtr v = H::mkBoundVar(captures[i].name, s);
        helper_arguments.push_back(v);
        if (captures[i].type.isArrow() && !hasFullFiniteDomain(captures[i].type)) {
            guards.push_back(member(captures[i].type, v));
        }
    }
    H::ExprPtr array;
    if (captures.empty()) {
        model_.decls.push_back(H::VarDecl{name, fs, {}, {}, {}, true});
        array = H::mkIdent(name, fs);
    } else {
        model_.funs.push_back(H::FunDecl{name, parameter_sorts, fs, {}, {}, {}, true});
        array = H::mkApply(name, fs, capture_values);
    }
    H::ExprPtr bound_array = captures.empty() ? array : H::mkApply(name, fs, helper_arguments);
    const std::string arg_name = arg.name;
    if (arg_name.empty()) { throw std::invalid_argument("THF lambda argument needs a name"); }
    const H::Sort arg_sort = sortOf(arg.type);
    binders.push_back(H::Binder{arg_name, arg_sort});
    H::ExprPtr x = H::mkBoundVar(arg_name, arg_sort);
    H::ExprPtr pointwise = equal(result, apply(ft, bound_array, x), body);
    guards.push_back(member(arg.type, x));
    H::ExprPtr definition = implication(conjunction(std::move(guards)), std::move(pointwise));
    addConstraint(H::mkForall(std::move(binders), std::move(definition)), "THF lambda definition");
    H::ExprPtr lambda_member = member(ft, bound_array);
    if (captures.empty()) {
        addConstraint(std::move(lambda_member), "THF lambda belongs to its function domain");
    } else {
        std::vector<H::Binder> capture_binders;
        std::vector<H::ExprPtr> capture_guards;
        std::vector<H::ExprPtr> quantified_captures;
        for (std::size_t i = 0; i < captures.size(); ++i) {
            const auto s = sortOf(captures[i].type);
            capture_binders.push_back(H::Binder{captures[i].name, s});
            H::ExprPtr v = H::mkBoundVar(captures[i].name, s);
            quantified_captures.push_back(v);
            if (captures[i].type.isArrow() && !hasFullFiniteDomain(captures[i].type)) {
                capture_guards.push_back(member(captures[i].type, v));
            }
        }
        H::ExprPtr value = H::mkApply(name, fs, quantified_captures);
        H::ExprPtr is_member = member(ft, value);
        if (!capture_guards.empty()) {
            is_member = implication(conjunction(std::move(capture_guards)), std::move(is_member));
        }
        addConstraint(H::mkForall(std::move(capture_binders), std::move(is_member)),
                      "THF lambda belongs to its function domain");
    }
    return array;
}

} // namespace SOMTParser::Lang::ThfPrototype
