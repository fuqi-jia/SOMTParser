// A source language may call a symbol `not`. SMT-LIB may not.
//
// TPTP's LCL domain encodes a LOGIC, so its connectives are ordinary
// uninterpreted function symbols. `is_a_theorem(implies(not(X),X))` is a
// perfectly legal problem, and passing `not` through to `declare-fun` made the
// ENGINE reject it as a reserved built-in -- with the rejection escaping the
// frontend as **E_INTERNAL**, the bucket reserved for a broken invariant,
// reported for a legal input.
//
// The fix is in the LOWERING rather than in the TPTP frontend, because the
// hazard is not TPTP's: Boogie, CHC-COMP, Essence and SMT-LIB2 all admit
// arbitrary identifiers, and putting the guard in one frontend would leave the
// same defect in five others.
//
// Renaming is safe in a way most rewrites are not: the symbols are
// uninterpreted, so consistently renaming one is an alpha-conversion and
// changes no model. What it must not do is COLLIDE, or be silent -- both are
// tested below.

#include "somtparser/translation/translate.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <fstream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** Lower a model directly, so the test exercises the lowering and not one
 *  frontend's route into it. */
std::string lower(const H::ConstraintModel& m, Diagnostics& diags) {
    ParserPtr p = newParser();
    TranslationReport report;
    Lower::HirToParser low(p);
    VERIFY(low.lower(m, report, diags));
    return p->dumpSMT2();
}

H::FunDecl fun(const std::string& name, std::vector<H::Sort> params, H::Sort result) {
    H::FunDecl f;
    f.name = name;
    f.params = std::move(params);
    f.result = result;
    return f;
}

} // namespace

int main(int argc, char** argv) {
    std::cout << "======= reserved symbol names =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- The bare case: a function called `not`. ---------------------------
    {
        H::ConstraintModel m;
        m.funs.push_back(fun("not", {H::Sort::integer()}, H::Sort::integer()));
        H::VarDecl x;
        x.name = "x";
        x.sort = H::Sort::integer();
        m.decls.push_back(x);
        H::Constraint c;
        c.formula = H::mkOp(H::Op::EQ,
                            {H::mkApply("not", H::Sort::integer(),
                                        {H::mkIdent("x", H::Sort::integer())}),
                             H::mkInt(0)});
        m.constraints.push_back(c);

        Diagnostics diags;
        const std::string smt = lower(m, diags);

        // It no longer throws, and what comes out re-parses -- which is the
        // whole point, since the engine is what rejected the name.
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));

        // The renaming is CONSISTENT: declaration and use agree. A rename
        // applied at one site and not the other would produce a script that
        // re-parses and asserts something about an undeclared symbol.
        VERIFY(!has(smt, "(declare-fun not "));
        VERIFY(has(smt, "not!0"));

        // And it is RECORDED. The emitted script says `not!0` where the source
        // said `not`, and anyone comparing the two has to be told why.
        bool warned = false;
        for (const auto& d : diags.all()) {
            if (has(d.message, "reserved SMT-LIB name") && has(d.message, "not!0")) {
                warned = true;
            }
        }
        VERIFY(warned);
    }

    // ---- The replacement must not collide. ---------------------------------
    {
        // A model that already contains `not!0`. The generated replacement has
        // to step over it, or two distinct symbols become one and the model
        // changes -- which is exactly what renaming was supposed to avoid.
        H::ConstraintModel m;
        m.funs.push_back(fun("not", {H::Sort::integer()}, H::Sort::boolean()));
        m.funs.push_back(fun("not!0", {H::Sort::integer()}, H::Sort::boolean()));
        H::VarDecl x;
        x.name = "x";
        x.sort = H::Sort::integer();
        m.decls.push_back(x);
        H::Constraint c;
        c.formula = H::mkOp(H::Op::AND,
                            {H::mkApply("not", H::Sort::boolean(),
                                        {H::mkIdent("x", H::Sort::integer())}),
                             H::mkApply("not!0", H::Sort::boolean(),
                                        {H::mkIdent("x", H::Sort::integer())})});
        m.constraints.push_back(c);

        Diagnostics diags;
        const std::string smt = lower(m, diags);
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
        // Both survive as DISTINCT symbols. The source `not!0` keeps its name --
        // it is not reserved -- and the source `not` steps over it to `not!1`.
        // Had the replacement collided, the two would be one declaration and
        // the second mkFuncDec would have failed as a redeclaration.
        VERIFY(has(smt, "not!0"));
        VERIFY(has(smt, "not!1"));
        VERIFY(!has(smt, "(declare-fun not "));
        // Three declarations: x, and the two renamed-or-not functions.
        std::size_t decls = 0;
        for (std::size_t i = smt.find("(declare-fun "); i != std::string::npos;
             i = smt.find("(declare-fun ", i + 1)) {
            ++decls;
        }
        VERIFY(decls == 3);
    }

    // ---- An ordinary name is untouched. ------------------------------------
    {
        // The guard must be narrow. Renaming every symbol, or any symbol that
        // merely contains a reserved word, would make every emitted script
        // unreadable against its source for no reason.
        H::ConstraintModel m;
        m.funs.push_back(fun("notable", {H::Sort::integer()}, H::Sort::boolean()));
        H::Constraint c;
        c.formula = H::mkApply("notable", H::Sort::boolean(), {H::mkInt(1)});
        m.constraints.push_back(c);

        Diagnostics diags;
        const std::string smt = lower(m, diags);
        VERIFY(has(smt, "notable"));
        VERIFY(!has(smt, "notable!"));
        for (const auto& d : diags.all()) {
            VERIFY(!has(d.message, "reserved SMT-LIB name"));
        }
    }

    // ---- End to end, through the frontend that found it. -------------------
    {
        Lang::SourceUnit u;
        u.main_path = "languages/tptp/instances/ok/reserved_names.p";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "tptp";
        const Translation t = translate(u, opts);
        VERIFY(t.ok());

        const std::string smt = t.toSmt2();
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));

        // The distinction the fixture exists to show: the OBJECT logic's `not`
        // is renamed, while the META logic's `not` -- the one this frontend
        // emits for `~` -- is the built-in and stays.
        // The frontend now encodes unsafe names before generic lowering.
        // Follow its recorded source identity, rather than depending on the
        // lowering layer's former fresh-name suffix.
        VERIFY(!t.semantics().stages().empty());
        const auto& source_map = t.semantics().stages().front().symbol_map;
        const auto target = [&](const std::string& source) {
            std::string name;
            for (const auto& mapping : source_map) {
                if (mapping.source == source) {
                    VERIFY(name.empty());
                    name = mapping.target;
                }
            }
            VERIFY(!name.empty());
            VERIFY(has(smt, "(declare-fun " + name + " "));
            VERIFY(has(smt, "(" + name + " "));
            return name;
        };
        const std::string object_not = target("tptp:6e6f74/1");
        const std::string object_and = target("tptp:616e64/2");
        const std::string object_or = target("tptp:6f72/2");
        VERIFY(object_not != object_and && object_not != object_or);
        VERIFY(object_and != object_or);
        VERIFY(has(smt, "(not "));       // the built-in, from `~`
        VERIFY(!has(smt, "(declare-fun not "));
        VERIFY(!has(smt, "(declare-fun and "));
        VERIFY(!has(smt, "(declare-fun or "));
    }

    // Constants are kept in a different builtin table from operators. A
    // quoted spelling denotes the same SMT symbol and needs the same guard.
    // Existing bare and quoted collision names must retain their identities.
    std::size_t fixture = 0;
    std::ofstream manifest;
    if (argc == 2) { manifest.open(std::string(argv[1]) + "/symbols.tsv"); }
    for (const std::string base : {"true", "false", "pi", "e", "nan", "epsilon",
                                   "+epsilon", "-epsilon", "+oo", "-oo", "inf", "not"}) {
        for (const bool quoted : {false, true}) {
            const std::string source = quoted ? '|' + base + '|' : base;
            const std::string collision0 = base + "!0";
            const std::string collision1 = '|' + base + "!1|";
            const std::string renamed = base + "!2";
            H::ConstraintModel model;
            const std::vector<std::string> names{source, collision0, collision1};
            for (std::size_t i = 0; i < names.size(); ++i) {
                H::VarDecl declaration;
                declaration.name = names[i];
                declaration.sort = H::Sort::integer();
                declaration.lower_bound = H::mkInt(2 * i);
                declaration.upper_bound = H::mkInt(2 * i + 1);
                model.decls.push_back(std::move(declaration));
            }
            const auto x = H::mkIdent(source, H::Sort::integer());
            const auto y = H::mkIdent(collision0, H::Sort::integer());
            const auto z = H::mkIdent(collision1, H::Sort::integer());
            H::Constraint relation;
            relation.formula = H::mkOp(H::Op::EQ,
                {H::mkOp(H::Op::ADD, {x, y, z}), H::mkInt(7)});
            model.constraints.push_back(std::move(relation));
            H::Objective objective;
            objective.name = "cost";
            objective.kind = H::ObjKind::MINIMIZE;
            objective.term = H::mkOp(H::Op::ADD,
                {H::mkOp(H::Op::MUL, {H::mkInt(100), x}),
                 H::mkOp(H::Op::MUL, {H::mkInt(10), y}), z});
            model.objectives.push_back(std::move(objective));
            TranslateOptions options;
            options.profile_id = "feasibility";
            options.omt_dialect = Lower::OmtDialect::Z3;
            for (const bool packed : {false, true}) {
                if (packed) { model.packed_linear_rows = std::make_shared<H::PackedLinearRows>(); }
                const auto translated = translate(model, options);
                for (const auto& d : translated.diagnostics().all()) {
                    if (d.severity == Severity::ERROR) { std::cerr << d.message << '\n'; }
                }
                VERIFY(translated.ok());
                VERIFY(translated.usesPackedSmtStream() == packed);
                Diagnostics diags;
                VERIFY(translated.semantics().validate(diags));
                const auto& contract = translated.semantics().stages().back();
                VERIFY(contract.source_signature.symbols.front().name == source);
                VERIFY(contract.target_signature.symbols.front().name == renamed);
                VERIFY(!contract.source_signature.sharesStorageWith(contract.target_signature));
                VERIFY(model.decls.front().name == source);
                Sem::Assignment projected;
                VERIFY(translated.semantics().project(
                    {{renamed, "1"}, {collision0, "2"}, {collision1, "4"}}, projected, diags));
                VERIFY(projected.at(source) == "1" && projected.at(collision0) == "2"
                       && projected.at(collision1) == "4");
                if (packed) {
                    VERIFY(contract.target_declaration_bounds.size() == 3);
                    VERIFY(contract.target_declaration_bounds.front().target_name == renamed);
                    VERIFY(contract.target_declaration_bounds.front().materialize(contract.target_signature));
                }
                const auto& maps = contract.symbol_map;
                bool found = false;
                for (const auto& mapping : maps) {
                    if (mapping.source == source) {
                        VERIFY(!found && mapping.target == renamed);
                        found = true;
                    }
                }
                VERIFY(found);
                const std::string script = translated.toSmt2(Lower::OmtDialect::Z3);
                VERIFY(has(script, "(declare-fun " + renamed + " () Int)"));
                VERIFY(!has(script, "(declare-fun " + source + " () Int)"));
                if (argc == 2) {
                    std::ofstream output(std::string(argv[1]) + "/" + std::to_string(fixture)
                        + (packed ? "-packed.smt2" : "-ordinary.smt2"));
                    output << script;
                    VERIFY(output.good());
                }
            }
            if (argc == 2) { manifest << fixture << '\t' << base << '\n'; }
            ++fixture;
        }
    }
    if (argc == 2) { VERIFY(manifest.good()); }

    // Contract axioms distinguish free names from bound variables, operators,
    // and string values. Updating the emitted target must not mutate the
    // source model or the signature snapshot shared with an earlier stage.
    {
        H::ConstraintModel model;
        H::VarDecl x;
        x.name = "true";
        x.sort = H::Sort::integer();
        x.lower_bound = H::mkInt(0);
        x.upper_bound = H::mkInt(1);
        model.decls.push_back(x);
        model.funs.push_back(fun("not", {H::Sort::integer()}, H::Sort::integer()));
        const auto bound = H::mkBoundVar("false", H::Sort::integer());
        const auto quantified = H::mkForall({{"false", H::Sort::integer()}},
            H::mkOp(H::Op::EQ, {bound, bound}));
        const auto text = H::mkString("true");
        const auto condition = H::mkOp(H::Op::AND,
            {quantified, H::mkOp(H::Op::EQ, {text, text})});
        const auto application = H::mkApply("not", H::Sort::integer(),
            {H::mkIdent("true", H::Sort::integer())});
        const auto lower_bound = H::mkOp(H::Op::ITE, {condition, application, H::mkInt(0)});
        H::VarDecl y;
        y.name = "y";
        y.sort = H::Sort::integer();
        y.lower_bound = lower_bound;
        y.upper_bound = H::mkInt(6);
        model.decls.push_back(y);
        TranslateOptions options;
        options.profile_id = "feasibility";
        options.omt_dialect = Lower::OmtDialect::Z3;
        for (const bool packed : {false, true}) {
            if (packed) { model.packed_linear_rows = std::make_shared<H::PackedLinearRows>(); }
            const auto translated = translate(model, options);
            VERIFY(translated.ok());
            const auto& contract = translated.semantics().stages().back();
            bool free_found = false, function_found = false, binder_found = false, text_found = false;
            std::vector<H::ExprPtr> pending(contract.target_axioms);
            while (!pending.empty()) {
                const auto expression = pending.back(); pending.pop_back();
                if (!expression) { continue; }
                if (expression->kind == H::ExprKind::IDENT) {
                    VERIFY(expression->name != "true");
                    free_found = free_found || expression->name == "true!0";
                } else if (expression->kind == H::ExprKind::APPLY) {
                    VERIFY(expression->name == "not!0");
                    function_found = true;
                } else if (expression->kind == H::ExprKind::BOUND_VAR) {
                    VERIFY(expression->name == "false");
                    binder_found = true;
                } else if (expression->kind == H::ExprKind::LIT_STRING) {
                    VERIFY(expression->name == "true");
                    text_found = true;
                }
                if (expression->kind == H::ExprKind::FORALL) {
                    VERIFY(expression->binders.front().name == "false");
                }
                pending.insert(pending.end(), expression->args.begin(), expression->args.end());
            }
            VERIFY(free_found && function_found && binder_found && text_found);
            VERIFY(model.decls[1].lower_bound == lower_bound);
            VERIFY(application->name == "not" && application->args.front()->name == "true");
            if (argc == 2) {
                std::ofstream output(std::string(argv[1])
                    + (packed ? "/scope-packed.smt2" : "/scope-ordinary.smt2"));
                output << translated.toSmt2(Lower::OmtDialect::Z3);
                VERIFY(output.good());
            }
        }
    }
    {
        H::ConstraintModel ordinary;
        H::VarDecl x;
        x.name = "ordinary";
        x.sort = H::Sort::integer();
        ordinary.decls.push_back(x);
        const auto translated = translate(ordinary);
        VERIFY(translated.ok());
        const auto& contract = translated.semantics().stages().back();
        VERIFY(contract.source_signature.sharesStorageWith(contract.target_signature));
    }

    std::cout << "All reserved-symbol-name tests passed." << std::endl;
    return 0;
}
