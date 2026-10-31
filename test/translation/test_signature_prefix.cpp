#include "somtparser/translation/semantics.h"
#include "test_helpers.h"

#include <stdexcept>
#include <utility>
#include <vector>

using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

static H::ConstraintModel example(bool auxiliary_first = false) {
    H::ConstraintModel model;
    H::VarDecl x{"x", H::Sort::integer(), H::mkInt(-2), H::mkInt(4), {}};
    H::VarDecl y{"y", H::Sort::real(), H::mkReal("0.5"), {}, {}};
    H::VarDecl auxiliary{"aux", H::Sort::real(), {}, {}, {}};
    auxiliary.auxiliary = true;
    if (auxiliary_first) { model.decls.push_back(auxiliary); }
    model.decls.push_back(x);
    model.decls.push_back(y);
    if (!auxiliary_first) { model.decls.push_back(auxiliary); }
    model.packed_linear_rows = std::make_shared<H::PackedLinearRows>();
    return model;
}

int main() {
    const auto model = example();
    const auto source = S::directLanguageToRelationalContract(model, "mps", Fidelity::exact());
    VERIFY(source.source_signature.symbols.size() == 2);
    VERIFY(source.target_signature.symbols.size() == 3);
    VERIFY(source.source_signature.symbols.data() == source.target_signature.symbols.data());
    VERIFY(!source.source_signature.sharesStorageWith(source.target_signature));
    VERIFY(source.source_signature.symbols.back().name == "y");
    VERIFY(source.source_signature.symbols.end() - source.source_signature.symbols.begin() == 2);
    VERIFY(!S::signatureMatchesModel(source.source_signature, model));
    auto without_auxiliary = model;
    without_auxiliary.decls.pop_back();
    VERIFY(S::signatureMatchesModel(source.source_signature, without_auxiliary));
    Diagnostics diagnostics;
    VERIFY(source.validate(diagnostics));
    const auto target = S::relationalToSmtContract(model, false, source.projection,
        source.target_axioms, &source.target_signature);
    VERIFY(target.source_signature.symbols.size() == 3);
    VERIFY(target.source_signature.sharesStorageWith(source.target_signature));
    S::TranslationPipeline pipeline;
    pipeline.add(source);
    pipeline.add(target);
    VERIFY(pipeline.validate(diagnostics));
    S::Assignment observed;
    VERIFY(source.projection.project({{"x", "1"}, {"y", "0.5"}, {"aux", "7"}},
                                      observed, diagnostics));
    VERIFY(observed.size() == 2 && observed.count("aux") == 0);

    // Indexing, materialization, and the legacy const-vector conversion all
    // respect the visible prefix. Neither conversion can expose the auxiliary.
    auto prefix = source.target_signature.symbolPrefix(2);
    const auto shared_prefix = prefix;
    const std::vector<S::Symbol>& vector = prefix.symbols;
    const std::vector<S::Symbol>& shared_vector = shared_prefix.symbols;
    VERIFY(vector.size() == 2 && vector.back().name == "y");
    VERIFY(&vector == &shared_vector);
    auto independent = prefix.materialize();
    independent.symbols.front().name = "changed";
    VERIFY(prefix.symbols.front().name == "x");
    VERIFY(source.target_signature.symbols.front().name == "x");
    bool rejected = false;
    try { (void)prefix.symbols.at(2); }
    catch (const std::out_of_range&) { rejected = true; }
    VERIFY(rejected);
    rejected = false;
    try { (void)prefix.symbolPrefix(3); }
    catch (const std::out_of_range&) { rejected = true; }
    VERIFY(rejected);
    const auto shorter = prefix.symbolPrefix(1);
    VERIFY(shorter.symbols.size() == 1 && shorter.symbols.back().name == "x");
    VERIFY(shorter.symbols.data() == source.target_signature.symbols.data());
    const auto empty = prefix.symbolPrefix(0);
    VERIFY(empty.symbols.empty() && empty.symbols.begin() == empty.symbols.end());
    const std::vector<S::Symbol>& empty_vector = empty.symbols;
    VERIFY(empty_vector.empty());

    auto moved = std::move(prefix.symbols);
    VERIFY(prefix.symbols.empty());
    VERIFY(!prefix.sharesStorageWith(shared_prefix));
    prefix = S::SignatureSnapshot{};
    VERIFY(moved.size() == 2 && moved.back().name == "y");
    VERIFY(shared_prefix.symbols.back().name == "y");
    S::SignatureSnapshot retained;
    {
        S::Signature temporary;
        temporary.symbols.push_back({"retained", S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
        temporary.symbols.push_back({"private", S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
        temporary.sort_constructors.push_back({"Carrier", 0});
        temporary.symbol_ranges.push_back({"r", 1, 4, S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
        retained = S::SignatureSnapshot(std::move(temporary)).symbolPrefix(1);
    }
    VERIFY(retained.symbols.front().name == "retained");
    VERIFY(retained.sort_constructors.size() == 1);
    VERIFY(retained.symbol_ranges.size() == 1 && retained.symbolCount() == 5);

    // An interspersed auxiliary is not a prefix. The existing filtered copy
    // must still exclude it while retaining every later source declaration.
    const auto mixed = S::directLanguageToRelationalContract(example(true), "mps", Fidelity::exact());
    VERIFY(mixed.source_signature.symbols.size() == 2);
    VERIFY(mixed.source_signature.symbols.front().name == "x");
    VERIFY(mixed.source_signature.symbols.back().name == "y");
    VERIFY(mixed.source_signature.symbols.data() != mixed.target_signature.symbols.data());
    VERIFY(mixed.validate(diagnostics));
    VERIFY(!diagnostics.hasErrors());
    return 0;
}
