#include "../../languages/tptp/src/thf_expression_parser.h"

#include "test_helpers.h"

#include <string>
#include <vector>

using namespace SOMTParser::Lang::ThfPrototype;
namespace H = SOMTParser::Uir::Hir;

namespace {
void globals(const FunctionTermPtr& term, const std::string& name,
             std::vector<FunctionTermPtr>& found) {
    if (!term) { return; }
    if (term->kind == FunctionTerm::Kind::HIR_VALUE && term->hir_value->name == name) {
        found.push_back(term);
    }
    for (const auto& child : {term->function, term->argument, term->body,
                              term->left, term->right}) {
        globals(child, name, found);
    }
}
}

int main() {
    const std::string first_line = "thf(first,axiom,h @ f).";
    const std::string second_line = "thf(second,axiom,(h @ f) => (h @ f)).";
    const std::string source =
        "thf(h_type,type,h:($o > $o) > $o).\n"
        "thf(f_type,type,f:$o > $o).\n" + first_line + "\n" + second_line + "\n"
        "thf(scoped,axiom, ! [X:$o] : ((h @ (^ [X:$o] : X)) => X)).\n";
    FunctionHirBuilder builder;
    ThfFileParser parser(source, "shared-symbols.p", builder);
    const auto file = parser.parse();
    VERIFY(file.formulas.size() == 3);
    std::vector<FunctionTermPtr> h_values;
    for (const auto& formula : file.formulas) {
        VERIFY(builder.wellScoped(formula.term));
        globals(formula.term, "h", h_values);
    }
    VERIFY(h_values.size() == 4);
    const auto& first = h_values[0];
    VERIFY(first->type.kind == Type::Kind::ARROW);
    VERIFY(first->type.domain->kind == Type::Kind::ARROW);
    VERIFY(first->hir_value->sort.kind == H::SortKind::ARRAY);
    VERIFY(first->hir_value->sort.index->kind == H::SortKind::ARRAY);
    for (std::size_t i = 1; i < h_values.size(); ++i) {
        const auto& occurrence = h_values[i];
        // Readers are reconstructed for each formula. These values must
        // nevertheless share both recursive type trees and the HIR leaf.
        VERIFY(occurrence.get() != first.get());
        VERIFY(occurrence->hir_value.get() == first->hir_value.get());
        VERIFY(occurrence->type.domain.get() == first->type.domain.get());
        VERIFY(occurrence->type.codomain.get() == first->type.codomain.get());
        VERIFY(occurrence->type.domain->domain.get() == first->type.domain->domain.get());
        VERIFY(occurrence->hir_value->sort.index.get() == first->hir_value->sort.index.get());
        VERIFY(occurrence->hir_value->sort.index->index.get()
               == first->hir_value->sort.index->index.get());
        VERIFY(occurrence->source.file == "shared-symbols.p");
    }
    VERIFY(first->source.line == 3);
    VERIFY(first->source.column == first_line.find("h @ f") + 1);
    VERIFY(h_values[1]->source.line == 4);
    VERIFY(h_values[1]->source.column == second_line.find("h @ f") + 1);
    VERIFY(h_values[2]->source.line == 4);
    VERIFY(h_values[2]->source.column == second_line.rfind("h @ f") + 1);
    VERIFY(h_values[1]->source.column != h_values[2]->source.column);
    VERIFY(h_values[3]->source.line == 5);

    const auto& quantified = file.formulas[2].term;
    const auto& implication = quantified->body;
    const auto& lambda = implication->left->argument;
    VERIFY(quantified->kind == FunctionTerm::Kind::FORALL);
    VERIFY(implication->kind == FunctionTerm::Kind::IMPLIES);
    VERIFY(lambda->kind == FunctionTerm::Kind::LAMBDA);
    VERIFY(lambda->binder_id != quantified->binder_id);
    VERIFY(lambda->body->kind == FunctionTerm::Kind::BOUND);
    VERIFY(lambda->body->binder_id == lambda->binder_id);
    VERIFY(implication->right->kind == FunctionTerm::Kind::BOUND);
    VERIFY(implication->right->binder_id == quantified->binder_id);
    VERIFY(lambda->binder->name == quantified->binder->name);

    // A local binder is resolved before consulting any global symbol table,
    // even if a programmatic signature has an entry with the same spelling.
    ThfExpressionParser shadow("! [X:$o] : X", "shadow.p", 1, 1,
        ThfSignature{{"X", Type::arrow(Type::boolean(), Type::boolean())}}, builder);
    const auto shadowed = shadow.parse();
    VERIFY(shadowed->body->kind == FunctionTerm::Kind::BOUND);
    VERIFY(shadowed->body->binder_id == shadowed->binder_id);
    VERIFY(shadowed->body->type.kind == Type::Kind::BOOL);
    VERIFY(builder.wellScoped(shadowed));

    // The builder can outlive several input files. Their signatures must not
    // share a cache keyed only by symbol spelling, even at identical positions.
    ThfFileParser other("thf(h_type,type,h:$o).\nthf(next,axiom,h).\n",
                        "shared-symbols.p", builder);
    const auto other_file = other.parse();
    const auto& other_h = other_file.formulas[0].term;
    VERIFY(other_h->type.kind == Type::Kind::BOOL);
    VERIFY(other_h->hir_value->sort.kind == H::SortKind::BOOL);
    VERIFY(other_h->hir_value.get() != first->hir_value.get());
    VERIFY(first->type.kind == Type::Kind::ARROW);
    VERIFY(first->source.line == 3);
    VERIFY(first->source.column == first_line.find("h @ f") + 1);
    const auto repeated_file = parser.parse();
    std::vector<FunctionTermPtr> repeated_h;
    globals(repeated_file.formulas[0].term, "h", repeated_h);
    VERIFY(repeated_h.size() == 1);
    VERIFY(repeated_h[0]->hir_value.get() != first->hir_value.get());
    VERIFY(repeated_h[0]->type.kind == Type::Kind::ARROW);

    bool undeclared = false;
    try {
        ThfFileParser missing("thf(no_declaration,axiom,h).", "missing.p", builder);
        (void)missing.parse();
    } catch (const ThfParseError& error) {
        undeclared = std::string(error.what()).find("no declared type") != std::string::npos
            && error.source().file == "missing.p" && error.source().line == 1;
    }
    VERIFY(undeclared);

    bool missing_signature = false;
    try {
        ThfExpressionParser invalid("$true", "null-signature.p", 1, 1, builder, nullptr);
        (void)invalid.parse();
    } catch (const std::invalid_argument&) {
        missing_signature = true;
    }
    VERIFY(missing_signature);
}
