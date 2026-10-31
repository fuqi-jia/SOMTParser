// Parses representative captured-lambda/application shapes from official
// SLH/SLH0285^1.p and checks THF's unitary lambda-scope boundary.
#include "../../languages/tptp/src/thf_expression_parser.h"

#include "test_helpers.h"

#include <string>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
bool evalBoolean(const SOMTParser::Lang::ThfPrototype::FunctionTermPtr& term,
                 const std::unordered_map<std::uint64_t, bool>& values) {
    using Kind = SOMTParser::Lang::ThfPrototype::FunctionTerm::Kind;
    switch (term->kind) {
    case Kind::BOUND: return values.at(term->binder_id);
    case Kind::NOT: return !evalBoolean(term->body, values);
    case Kind::AND:
        return evalBoolean(term->left, values) && evalBoolean(term->right, values);
    case Kind::OR:
        return evalBoolean(term->left, values) || evalBoolean(term->right, values);
    case Kind::IMPLIES:
        return !evalBoolean(term->left, values) || evalBoolean(term->right, values);
    default: throw std::runtime_error("expected Boolean connective AST");
    }
}
}

using namespace SOMTParser::Lang::ThfPrototype;

int main() {
    const Type a = Type::individual("a");
    const Type set_a = Type::arrow(a, Type::boolean());
    ThfSignature signature;
    signature.emplace("member_a", Type::arrow(a, Type::arrow(set_a, Type::boolean())));
    signature.emplace("collect_a", Type::arrow(set_a, set_a));

    // This is the source structure around the official line-3131 fragment:
    // A is an enclosing function-typed variable, and X3 is captured neither
    // by spelling nor by global substitution; the lambda body closes over A.
    // Exact formula fragment from fixture lines 8-9; its comment anchors the
    // expression shape to the unmodified official source at line 3131.
    const std::string source =
        "    ! [A:a > $o] :\n"
        "      ( ( collect_a @ ( ^ [X3:a] : ( member_a @ X3 @ A ) ) ) = A )";
    FunctionHirBuilder builder;
    ThfExpressionParser parser(source, "SLH0285-set-comprehension.p", 8, 1,
                               signature, builder);
    FunctionTermPtr root = parser.parse();

    VERIFY(root->kind == FunctionTerm::Kind::FORALL);
    VERIFY(root->binder->name == "A");
    VERIFY(root->binder->type.isArrow());
    VERIFY(root->body->kind == FunctionTerm::Kind::EQUAL);
    const FunctionTermPtr& lhs = root->body->left;
    VERIFY(lhs->kind == FunctionTerm::Kind::APPLY);
    VERIFY(lhs->function->hir_value->name == "collect_a");
    VERIFY(lhs->argument->kind == FunctionTerm::Kind::LAMBDA);
    const FunctionTermPtr& lambda = lhs->argument;
    VERIFY(lambda->binder->name == "X3");
    VERIFY(lambda->source.file == "SLH0285-set-comprehension.p");
    VERIFY(lambda->source.line == 9);
    const std::size_t newline = source.find('\n');
    VERIFY(lambda->source.column == source.find('^') - newline);
    VERIFY(lambda->body->kind == FunctionTerm::Kind::APPLY);
    VERIFY(lambda->body->function->kind == FunctionTerm::Kind::APPLY);
    VERIFY(lambda->body->function->function->hir_value->name == "member_a");
    VERIFY(lambda->body->function->argument->hint == "X3");
    VERIFY(lambda->body->argument->kind == FunctionTerm::Kind::BOUND);
    VERIFY(lambda->body->argument->binder_id == root->binder_id);
    VERIFY(root->body->right->kind == FunctionTerm::Kind::BOUND);
    VERIFY(root->body->right->binder_id == root->binder_id);
    VERIFY(builder.wellScoped(root));

    // TPTP THF specifies that application is left-associative and lambda is
    // right-associative: an unparenthesized @ after the lambda's unitary body
    // is outside its scope. This must parse as (^[X].X) @ g, not ^[X].(X @ g).
    ThfSignature scope_signature;
    scope_signature.emplace("g", a);
    FunctionHirBuilder scope_builder;
    ThfExpressionParser scope_parser("^ [X:a] : X @ g", "scope.p", 1, 1,
                                     scope_signature, scope_builder);
    FunctionTermPtr scope_root = scope_parser.parse();
    VERIFY(scope_root->kind == FunctionTerm::Kind::APPLY);
    VERIFY(scope_root->function->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(scope_root->function->body->kind == FunctionTerm::Kind::BOUND);
    VERIFY(scope_root->function->body->binder_id == scope_root->function->binder_id);
    VERIFY(scope_root->argument->hir_value->name == "g");
    VERIFY(scope_builder.wellScoped(scope_root));

    // The official THF grammar makes prefix unary formulas valid unit
    // formulas, including both sides of @ and Boolean equality. Keep a
    // parenthesized application inside the lambda's negation, while the final
    // unparenthesized @ applies the filtered list outside that lambda.
    const Type list_a = Type::individual("list_a");
    const Type predicate_a = Type::arrow(a, Type::boolean());
    ThfSignature unary_signature;
    unary_signature.emplace("filter_a", Type::arrow(
        predicate_a, Type::arrow(list_a, list_a)));
    FunctionHirBuilder unary_builder;
    const std::string unary_application =
        "! [P:a > $o,Xs:list_a] : "
        "(filter_a @ ^ [X:a] : ~ (P @ X) @ Xs = Xs)";
    ThfExpressionParser unary_parser(unary_application, "unit-formula.p", 1, 1,
                                     unary_signature, unary_builder);
    FunctionTermPtr unary_root = unary_parser.parse();
    VERIFY(unary_root->kind == FunctionTerm::Kind::FORALL);
    VERIFY(unary_root->body->kind == FunctionTerm::Kind::FORALL);
    const FunctionTermPtr& filtered_formula = unary_root->body->body;
    VERIFY(filtered_formula->kind == FunctionTerm::Kind::EQUAL);
    const FunctionTermPtr& filtered = filtered_formula->left;
    VERIFY(filtered->kind == FunctionTerm::Kind::APPLY);
    VERIFY(filtered->function->kind == FunctionTerm::Kind::APPLY);
    VERIFY(filtered->function->function->hir_value->name == "filter_a");
    const FunctionTermPtr& predicate = filtered->function->argument;
    VERIFY(predicate->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(predicate->body->kind == FunctionTerm::Kind::NOT);
    VERIFY(predicate->body->body->kind == FunctionTerm::Kind::APPLY);
    VERIFY(filtered->argument->kind == FunctionTerm::Kind::BOUND);
    VERIFY(filtered->argument->binder_id == unary_root->body->binder_id);
    VERIFY(filtered_formula->right->kind == FunctionTerm::Kind::BOUND);
    VERIFY(filtered_formula->right->binder_id == unary_root->body->binder_id);
    VERIFY(unary_builder.wellScoped(unary_root));

    // An explicitly quantified formula is also a THF unit formula and can
    // occur directly as an @ argument (the shape at official SLH0256^1.p).
    ThfSignature quantified_argument_signature;
    quantified_argument_signature.emplace("predicate_i", Type::arrow(
        Type::individual("i"), Type::boolean()));
    quantified_argument_signature.emplace("bool_id", Type::arrow(
        Type::boolean(), Type::boolean()));
    FunctionHirBuilder quantified_argument_builder;
    ThfExpressionParser quantified_argument_parser(
        "bool_id @ ! [I:i] : (predicate_i @ I)", "quantified-argument.p",
        1, 1, quantified_argument_signature, quantified_argument_builder);
    FunctionTermPtr quantified_argument = quantified_argument_parser.parse();
    VERIFY(quantified_argument->kind == FunctionTerm::Kind::APPLY);
    VERIFY(quantified_argument->function->hir_value->name == "bool_id");
    VERIFY(quantified_argument->argument->kind == FunctionTerm::Kind::FORALL);
    VERIFY(quantified_argument->argument->body->kind == FunctionTerm::Kind::APPLY);
    VERIFY(quantified_argument_builder.wellScoped(quantified_argument));

    // `= ~ P` occurs in the official SLH/SLH0059^1.p and SLH/SLH0112^1.p
    // theorem corpus. It is Boolean equality, not a malformed term.
    ThfSignature equality_signature;
    equality_signature.emplace("zero_n2687167440665602831ol_nat", Type::arrow(
        Type::boolean(), Type::individual("nat")));
    equality_signature.emplace("zero_zero_nat", Type::individual("nat"));
    FunctionHirBuilder equality_builder;
    ThfExpressionParser equality_parser(
        "! [P:$o] : ((zero_n2687167440665602831ol_nat @ P = zero_zero_nat) = ~ P)",
        "bool-equality.p", 1, 1, equality_signature, equality_builder);
    FunctionTermPtr equality_root = equality_parser.parse();
    VERIFY(equality_root->kind == FunctionTerm::Kind::FORALL);
    VERIFY(equality_root->body->kind == FunctionTerm::Kind::EQUAL);
    VERIFY(equality_root->body->right->kind == FunctionTerm::Kind::NOT);
    VERIFY(equality_root->body->right->body->kind == FunctionTerm::Kind::BOUND);
    VERIFY(equality_builder.wellScoped(equality_root));

    // Defined logical connectives are first-class THF terms with their
    // ordinary curried Boolean types. Their lambda bodies use the same
    // logical HIR nodes as infix formula syntax.
    FunctionHirBuilder connective_builder;
    ThfExpressionParser connective_parser("(=>)", "connective-value.p", 1, 1,
                                           {}, connective_builder);
    FunctionTermPtr implication = connective_parser.parse();
    VERIFY(implication->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(implication->type.isArrow());
    VERIFY(implication->type.domain->kind == Type::Kind::BOOL);
    VERIFY(implication->type.codomain->isArrow());
    VERIFY(implication->type.codomain->domain->kind == Type::Kind::BOOL);
    VERIFY(implication->type.codomain->codomain->kind == Type::Kind::BOOL);
    VERIFY(implication->body->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(implication->body->body->kind == FunctionTerm::Kind::IMPLIES);
    VERIFY(implication->body->body->left->binder_id == implication->binder_id);
    VERIFY(implication->body->body->right->binder_id == implication->body->binder_id);
    VERIFY(connective_builder.wellScoped(implication));
    for (bool p : {false, true}) {
        for (bool q : {false, true}) {
            const std::unordered_map<std::uint64_t, bool> values = {
                {implication->binder_id, p}, {implication->body->binder_id, q}
            };
            VERIFY(evalBoolean(implication->body->body, values) == (!p || q));
        }
    }

    FunctionHirBuilder applied_connective_builder;
    ThfExpressionParser applied_connective_parser(
        "((=>) @ $true @ $false)", "connective-apply.p", 1, 1, {},
        applied_connective_builder);
    FunctionTermPtr applied_implication = applied_connective_parser.parse();
    VERIFY(applied_implication->kind == FunctionTerm::Kind::APPLY);
    VERIFY(applied_implication->type.kind == Type::Kind::BOOL);
    VERIFY(applied_implication->function->kind == FunctionTerm::Kind::APPLY);
    VERIFY(applied_implication->function->function->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(applied_connective_builder.wellScoped(applied_implication));

    // The connective's declared domain is Bool. A same-shaped application
    // with an individual argument must fail in the typed @ builder.
    bool connective_type_rejected = false;
    try {
        ThfSignature bad_connective_signature;
        bad_connective_signature.emplace("individual_value", Type::individual("i"));
        FunctionHirBuilder bad_connective_builder;
        ThfExpressionParser bad_connective_parser(
            "((=>) @ individual_value @ $false)", "connective-type.p", 1, 1,
            bad_connective_signature, bad_connective_builder);
        (void)bad_connective_parser.parse();
    } catch (const ThfParseError& error) {
        connective_type_rejected = std::string(error.what()).find(
            "ill-typed THF @ application") != std::string::npos;
    }
    VERIFY(connective_type_rejected);

    const std::vector<std::pair<std::string, FunctionTerm::Kind>> connective_terms = {
        {"(~)", FunctionTerm::Kind::LAMBDA}, {"(&)", FunctionTerm::Kind::LAMBDA},
        {"(|)", FunctionTerm::Kind::LAMBDA}, {"(<=)", FunctionTerm::Kind::LAMBDA},
        {"(<=>)", FunctionTerm::Kind::LAMBDA}, {"(<~>)", FunctionTerm::Kind::LAMBDA},
        {"(~&)", FunctionTerm::Kind::LAMBDA}, {"(~|)", FunctionTerm::Kind::LAMBDA}
    };
    for (const auto& entry : connective_terms) {
        FunctionHirBuilder each_builder;
        ThfExpressionParser each_parser(entry.first, "connective-forms.p", 1, 1,
                                        {}, each_builder);
        FunctionTermPtr value = each_parser.parse();
        VERIFY(value->kind == entry.second);
        VERIFY(each_builder.wellScoped(value));
        const std::string spelling = entry.first.substr(1, entry.first.size() - 2);
        if (spelling == "~") {
            VERIFY(value->body->kind == FunctionTerm::Kind::NOT);
            for (bool p : {false, true}) {
                VERIFY(evalBoolean(value->body, {{value->binder_id, p}}) == !p);
            }
        } else if (spelling == "&") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::AND);
        } else if (spelling == "|") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::OR);
        } else if (spelling == "~&" || spelling == "~|") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::NOT);
        } else if (spelling == "<=>") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::AND);
            VERIFY(value->body->body->left->kind == FunctionTerm::Kind::IMPLIES);
            VERIFY(value->body->body->right->kind == FunctionTerm::Kind::IMPLIES);
        } else if (spelling == "<~>") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::NOT);
            VERIFY(value->body->body->body->kind == FunctionTerm::Kind::AND);
        } else if (spelling == "<=") {
            VERIFY(value->body->body->kind == FunctionTerm::Kind::IMPLIES);
            VERIFY(value->body->body->left->binder_id == value->body->binder_id);
            VERIFY(value->body->body->right->binder_id == value->binder_id);
        }
        if (spelling != "~") {
            const FunctionTermPtr& body = value->body->body;
            for (bool p : {false, true}) {
                for (bool q : {false, true}) {
                    const bool expected = spelling == "&" ? (p && q)
                        : spelling == "|" ? (p || q)
                        : spelling == "~&" ? !(p && q)
                        : spelling == "~|" ? !(p || q)
                        : spelling == "=>" ? (!p || q)
                        : spelling == "<=" ? (!q || p)
                        : spelling == "<=>" ? (p == q)
                        : (p != q);
                    VERIFY(evalBoolean(body, {{value->binder_id, p},
                                              {value->body->binder_id, q}}) == expected);
                }
            }
        }
    }

    for (const auto& entry : std::vector<std::pair<std::string, FunctionTerm::Kind>>{
             {"! [P:$o,Q:$o] : (P ~& Q)", FunctionTerm::Kind::AND},
             {"! [P:$o,Q:$o] : (P ~| Q)", FunctionTerm::Kind::OR}}) {
        FunctionHirBuilder negated_binary_builder;
        ThfExpressionParser negated_binary_parser(entry.first, "negated-binary.p",
            1, 1, {}, negated_binary_builder);
        FunctionTermPtr parsed = negated_binary_parser.parse();
        VERIFY(parsed->kind == FunctionTerm::Kind::FORALL);
        VERIFY(parsed->body->kind == FunctionTerm::Kind::FORALL);
        VERIFY(parsed->body->body->kind == FunctionTerm::Kind::NOT);
        VERIFY(parsed->body->body->body->kind == entry.second);
        VERIFY(negated_binary_builder.wellScoped(parsed));
    }

    bool unbound_rejected = false;
    try {
        FunctionHirBuilder bad_builder;
        ThfExpressionParser bad("(member_a @ X3)", "bad.p", 4, 3,
                                signature, bad_builder);
        (void)bad.parse();
    } catch (const ThfParseError& e) {
        unbound_rejected = e.source().file == "bad.p" && e.source().line == 4
            && e.source().column == 15;
    }
    VERIFY(unbound_rejected);
}
