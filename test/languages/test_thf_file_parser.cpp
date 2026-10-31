// Reads the pinned CASC 2025 SLH0285^1.p file and checks full annotated-file
// parsing/type analysis. CTest uses the bundled fixture; argv[1] may override it.
#include "../../languages/tptp/src/thf_expression_parser.h"

#include "test_helpers.h"

#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <unordered_map>
#include <vector>

using namespace SOMTParser::Lang::ThfPrototype;

int main(int argc, char** argv) {
    VERIFY(argc == 1 || argc == 2);
    const std::string path = argc == 2
        ? argv[1]
        : "languages/tptp/instances/ok/SLH0285-original.p";
    std::ifstream input(path, std::ios::binary);
    VERIFY(input.good());
    const std::string source((std::istreambuf_iterator<char>(input)),
                              std::istreambuf_iterator<char>());
    FunctionHirBuilder builder;
    ThfFileParser parser(source, path, builder);
    ThfFile file;
    try {
        file = parser.parse();
    } catch (const ThfParseError& error) {
        std::cerr << error.what() << " at " << error.source().line << ':'
                  << error.source().column << '\n';
        throw;
    }

    VERIFY(file.type_declarations.size() == 929);
    VERIFY(file.signature.size() == 685);
    VERIFY(file.formulas.size() == 1277);
    std::unordered_map<std::string, std::size_t> roles;
    std::size_t user_types = 0;
    for (const auto& declaration : file.type_declarations) {
        if (declaration.declares_type_symbol) { ++user_types; }
    }
    for (const auto& formula : file.formulas) {
        ++roles[formula.role];
        VERIFY(formula.term->type.kind == Type::Kind::BOOL);
        VERIFY(builder.wellScoped(formula.term));
    }
    VERIFY(user_types == 244);
    VERIFY(roles["axiom"] == 1276);
    VERIFY(roles["conjecture"] == 1);
    VERIFY(file.formulas.back().role == "conjecture");
    VERIFY(file.formulas.back().source.line > 0);
    VERIFY(file.formulas.back().term->source.file == path);

    bool found_captured_set_lambda = false;
    std::vector<FunctionTermPtr> pending;
    for (const auto& formula : file.formulas) { pending.push_back(formula.term); }
    while (!pending.empty()) {
        FunctionTermPtr term = pending.back();
        pending.pop_back();
        if (term->kind == FunctionTerm::Kind::LAMBDA
            && term->source.line == 3131 && term->binder->name == "X3") {
            found_captured_set_lambda = true;
        }
        switch (term->kind) {
        case FunctionTerm::Kind::HIR_VALUE:
        case FunctionTerm::Kind::BOUND: break;
        case FunctionTerm::Kind::APPLY:
            pending.push_back(term->function);
            pending.push_back(term->argument);
            break;
        case FunctionTerm::Kind::LAMBDA:
        case FunctionTerm::Kind::FORALL:
        case FunctionTerm::Kind::EXISTS:
        case FunctionTerm::Kind::NOT: pending.push_back(term->body); break;
        case FunctionTerm::Kind::EQUAL:
        case FunctionTerm::Kind::AND:
        case FunctionTerm::Kind::OR:
        case FunctionTerm::Kind::IMPLIES:
            pending.push_back(term->left);
            pending.push_back(term->right);
            break;
        }
    }
    VERIFY(found_captured_set_lambda);

    bool include_rejected = false;
    try {
        FunctionHirBuilder include_builder;
        ThfFileParser with_include("include('other.p').\n", "include.p", include_builder);
        (void)with_include.parse();
    } catch (const ThfParseError& error) {
        include_rejected = error.source().file == "include.p";
    }
    VERIFY(include_rejected);

    const std::string include_root = "languages/tptp/instances/ok/thf-includes.p";
    FunctionHirBuilder selected_builder;
    ThfFileParser selected(
        "include('support/thf-include-mid.ax',[type_p,positive]).\n",
        include_root, selected_builder);
    VERIFY(selected.hasThfStatements());
    const auto selected_file = selected.parse();
    VERIFY(selected_file.signature.size() == 1);
    VERIFY(selected_file.formulas.size() == 1);
    VERIFY(selected_file.formulas[0].name == "positive");
    VERIFY(selected_file.formulas[0].source.file ==
           "languages/tptp/instances/ok/support/thf-include-leaf.ax");
    VERIFY(selected_file.formulas[0].source.line == 3);
    VERIFY(selected_file.formulas[0].term->source.file == selected_file.formulas[0].source.file);

    for (const std::string& selection : {"[missing]", "[positive,positive]"}) {
        bool rejected = false;
        try {
            FunctionHirBuilder selected_builder;
            ThfFileParser invalid("include('support/thf-include-mid.ax'," + selection + ").",
                                  include_root, selected_builder);
            (void)invalid.parse();
        } catch (const ThfParseError& error) {
            rejected = error.source().file == include_root;
        }
        VERIFY(rejected);
    }
    bool cycle_rejected = false;
    try {
        FunctionHirBuilder cycle_builder;
        ThfFileParser cycle("include('support/thf-include-cycle.ax').",
                           "languages/tptp/instances/reject/cycle.p", cycle_builder);
        (void)cycle.parse();
    } catch (const ThfParseError& error) {
        cycle_rejected = std::string(error.what()).find("include nesting") != std::string::npos;
    }
    VERIFY(cycle_rejected);

    // Shared include dependencies can repeat the same declaration. Compare
    // parsed types, so redundant parentheses do not create a false conflict.
    FunctionHirBuilder repeated_builder;
    ThfFileParser repeated(
        "thf(sort_a,type,a:$tType).\n"
        "thf(sort_a_again,type,a:$tType).\n"
        "thf(f_type,type,f:a > a > $o).\n"
        "thf(f_type_again,type,f:(a > (a > $o))).\n"
        "thf(goal,conjecture, ! [X:a] : (f @ X @ X)).\n",
        "repeated-types.p", repeated_builder);
    const auto repeated_file = repeated.parse();
    VERIFY(repeated_file.signature.size() == 1);
    VERIFY(repeated_file.type_declarations.size() == 2);
    VERIFY(repeated_file.type_declarations[1].source.line == 3);
    VERIFY(repeated_file.formulas.size() == 1);

    FunctionHirBuilder overlapping_builder;
    ThfFileParser overlapping(
        "include('support/thf-include-leaf.ax',[type_p]).\n"
        "include('support/thf-include-mid.ax',[type_p,positive]).\n",
        include_root, overlapping_builder);
    const auto overlapping_file = overlapping.parse();
    VERIFY(overlapping_file.signature.size() == 1);
    VERIFY(overlapping_file.type_declarations.size() == 1);
    VERIFY(overlapping_file.formulas.size() == 1);

    for (const std::string& source : {
            "thf(one,type,f:$i > $o).\nthf(two,type,f:$o > $i).",
            "thf(one,type,f:$i > $i > $o).\nthf(two,type,f:($i > $i) > $o).",
            "thf(one,type,a:$tType).\nthf(two,type,a:$i).",
            "thf(one,type,a:$i).\nthf(two,type,a:$tType)."}) {
        bool conflict_rejected = false;
        try {
            FunctionHirBuilder conflict_builder;
            ThfFileParser conflict(source, "conflicting-types.p", conflict_builder);
            (void)conflict.parse();
        } catch (const ThfParseError& error) {
            conflict_rejected = std::string(error.what()).find("conflicting THF type")
                != std::string::npos && error.source().line == 2;
        }
        VERIFY(conflict_rejected);
    }

    // All formula readers share a completed declaration table. A shadowed
    // local name must neither escape into the next formula nor mutate it.
    // Comment removal, CRLF and same-line statements retain source locations.
    FunctionHirBuilder multi_builder;
    ThfFileParser multi(
        "% heading\r\n"
        "thf(p_type,type,p:$o). /* inline\nblock */\n"
        "thf(a,axiom, ! [P:$o] : (P => p)). thf(b,axiom,p).\n",
        "shared-signature.p", multi_builder);
    const auto multi_file = multi.parse();
    VERIFY(multi_file.signature.size() == 1);
    VERIFY(multi_file.signature.at("p").kind == Type::Kind::BOOL);
    VERIFY(multi_file.formulas.size() == 2);
    const auto& quantified = multi_file.formulas[0].term;
    VERIFY(quantified->kind == FunctionTerm::Kind::FORALL);
    VERIFY(quantified->body->kind == FunctionTerm::Kind::IMPLIES);
    VERIFY(quantified->body->left->kind == FunctionTerm::Kind::BOUND);
    VERIFY(quantified->body->left->binder_id == quantified->binder_id);
    VERIFY(quantified->body->right->kind == FunctionTerm::Kind::HIR_VALUE);
    VERIFY(quantified->body->right->hir_value->name == "p");
    VERIFY(multi_file.formulas[1].term->kind == FunctionTerm::Kind::HIR_VALUE);
    VERIFY(multi_file.formulas[1].term->hir_value->name == "p");
    VERIFY(multi_file.formulas[0].source.line == 4);
    VERIFY(multi_file.formulas[0].source.column == 13);
    VERIFY(quantified->source.line == 4);
    VERIFY(quantified->source.column == 14);
    VERIFY(multi_file.formulas[1].source.line == 4);
    VERIFY(multi_file.formulas[1].source.column == 48);
    VERIFY(builder.wellScoped(quantified));
    // The parser remains reusable even though construction transfers the map
    // through a shared owner during the expression pass.
    const auto multi_again = multi.parse();
    VERIFY(multi_again.signature.size() == 1);
    VERIFY(multi_again.formulas.size() == 2);


    // A shared expression parser owns its immutable signature even if the
    // caller releases that owner before parse(), including lambda scopes.
    auto owned_signature = std::make_shared<const ThfSignature>(
        ThfSignature{{"p", Type::boolean()}});
    FunctionHirBuilder owned_builder;
    ThfExpressionParser owned_parser("! [P:$o] : (P => p)", "owned.p", 1, 1,
                                     owned_builder, owned_signature);
    owned_signature.reset();
    const auto owned_term = owned_parser.parse();
    VERIFY(owned_builder.wellScoped(owned_term));
    VERIFY(owned_term->body->left->binder_id == owned_term->binder_id);
    VERIFY(owned_term->body->right->hir_value->name == "p");

}
