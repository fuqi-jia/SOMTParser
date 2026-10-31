// The proposed SMT-LIB OMT syntax is what standardised benchmarks must use,
// but no solver accepts it yet, so running experiments needs the vendor
// dialects too. One translation, several emissions.
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

static bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

int main() {
    // Sort and Objective are ambiguous unqualified: SOMTParser::Sort and
    // SOMTParser::Objective (frontend/objective.h) collide with their
    // SOMTParser::Uir::Hir counterparts once all the using-directives above
    // are in scope, so these need the Hir:: qualifier -- they are the same
    // concept at a different layer, so qualification rather than renaming is
    // the right fix. Model used to collide with SOMTParser::Model
    // (model/model.h) the same way, but that pair meant genuinely different
    // things -- a problem specification versus a solver's satisfying
    // assignment -- so it was renamed to ConstraintModel instead of merely
    // qualified.
    Hir::ConstraintModel m;
    VarDecl d;
    d.name = "x";
    d.sort = Hir::Sort::integer();
    m.decls.push_back(d);

    Hir::Objective o;
    o.kind = ObjKind::MINIMIZE;
    o.term = mkIdent("x", Hir::Sort::integer());
    o.name = "obj0";
    m.objectives.push_back(o);

    ParserPtr p = newParser();
    Lower::HirToParser lowerer(p);
    TranslationReport report;
    Diagnostics diags;
    assert(lowerer.lower(m, report, diags));

    // The proposed standard: named objective plus an explicit optimise call.
    {
        Diagnostics d2;
        const std::string s =
            Lower::emitObjectives(m, Lower::OmtDialect::SmtLib2025, lowerer, d2);
        assert(!d2.hasErrors());
        assert(contains(s, "(define-objective obj0 OBJECTIVE_MIN"));
        assert(contains(s, "(optimize-sat obj0)"));
        assert(!contains(s, "(minimize"));
    }

    // Z3 accepts (minimize t) and needs no objective name.
    {
        Diagnostics d2;
        const std::string s = Lower::emitObjectives(m, Lower::OmtDialect::Z3, lowerer, d2);
        assert(!d2.hasErrors());
        assert(contains(s, "(minimize "));
        assert(!contains(s, "define-objective"));
        assert(!contains(s, "optimize-sat"));
    }

    // OptiMathSAT also uses (minimize t) but requires the OMT option first.
    {
        Diagnostics d2;
        const std::string s =
            Lower::emitObjectives(m, Lower::OmtDialect::OptiMathSAT, lowerer, d2);
        assert(!d2.hasErrors());
        assert(contains(s, "(set-option :produce-models true)"));
        assert(contains(s, "(minimize "));
    }

    // None drops the objective entirely: the pure-SMT comparison arm.
    {
        Diagnostics d2;
        const std::string s = Lower::emitObjectives(m, Lower::OmtDialect::None, lowerer, d2);
        assert(!d2.hasErrors());
        assert(!contains(s, "minimize"));
        assert(!contains(s, "define-objective"));
    }

    // MAXIMIZE maps to the right keyword in each dialect.
    {
        Hir::ConstraintModel mx = m;
        mx.objectives[0].kind = ObjKind::MAXIMIZE;
        Diagnostics d2;
        const std::string a =
            Lower::emitObjectives(mx, Lower::OmtDialect::SmtLib2025, lowerer, d2);
        assert(contains(a, "OBJECTIVE_MAX"));
        const std::string b = Lower::emitObjectives(mx, Lower::OmtDialect::Z3, lowerer, d2);
        assert(contains(b, "(maximize "));
    }

    // An unnamed objective still gets a stable generated name, because the
    // proposed syntax requires one and results are keyed by it.
    //
    // Checked at index 1, not index 0. The objective in `m` is at index 0 and
    // is already called "obj0", which is exactly what objectiveName() generates
    // for index 0 -- so clearing its name and asserting "obj0" appears passed
    // whether or not the fallback existed. Deleting the fallback would not have
    // failed that test. A second objective makes the generated name ("obj1")
    // one that appears nowhere else in the model.
    {
        Hir::ConstraintModel mu = m;
        Hir::Objective second;
        second.kind = ObjKind::MAXIMIZE;
        second.term = mkIdent("x", Hir::Sort::integer());
        second.name.clear();                       // the objective under test
        mu.objectives.push_back(second);
        mu.objective_combination = Hir::ObjectiveCombination::BOX;

        Diagnostics d2;
        const std::string s =
            Lower::emitObjectives(mu, Lower::OmtDialect::SmtLib2025, lowerer, d2);
        assert(!d2.hasErrors());
        assert(contains(s, "(define-objective obj1 OBJECTIVE_MAX"));
        assert(contains(s, "(define-multi-objective multi OBJECTIVE_BOX obj0 obj1)"));
        assert(contains(s, "(optimize-sat multi)"));
        // The named one is untouched, so the generated name really did come
        // from the fallback and not from some model-wide renaming.
        assert(contains(s, "(define-objective obj0 OBJECTIVE_MIN"));
    }

    // Renderability is checked without a dialect, so that OmtDialect::None --
    // which emits nothing -- does not also validate nothing. translate() calls
    // this to justify toSmt2()'s assert; when it went through emitObjectives()
    // with the caller's dialect, `--dialect none` proved nothing and the
    // documented re-emit path (translate as None, then toSmt2(Z3)) hit that
    // assert at runtime.
    {
        Diagnostics d2;
        assert(Lower::validateObjectives(m, lowerer, d2));
        assert(!d2.hasErrors());

        Hir::ConstraintModel bad = m;
        // A term the emitter cannot render: it only handles a variable or an
        // integer literal, and this variable is not in the lowered model.
        bad.objectives[0].term = mkIdent("never_declared", Hir::Sort::integer());
        Diagnostics d3;
        assert(!Lower::validateObjectives(bad, lowerer, d3));
        assert(d3.hasErrors());
        // And emitObjectives() under None still emits nothing, so the two are
        // genuinely independent questions.
        Diagnostics d4;
        assert(Lower::emitObjectives(bad, Lower::OmtDialect::None, lowerer, d4).empty());
        assert(!d4.hasErrors());
    }

    // Names are stable strings the evaluation groups by.
    assert(std::string(Lower::omtDialectName(Lower::OmtDialect::SmtLib2025)) == "smtlib-omt-2025");
    assert(std::string(Lower::omtDialectName(Lower::OmtDialect::Z3)) == "z3");
    assert(std::string(Lower::omtDialectName(Lower::OmtDialect::None)) == "none");

    // Several objectives carry their combination into the emitted script.
    //
    // Without this, the emitter produced several (minimize t) commands and Z3's
    // documented default for those is lexicographic -- so the pipeline was not
    // dropping the combination, it was choosing one. Verified against Z3's
    // optimization documentation: (set-option :opt.priority lex|pareto|box).
    {
        Hir::ConstraintModel mm = m;
        Hir::Objective second;
        second.kind = ObjKind::MINIMIZE;
        second.term = mkIdent("x", Hir::Sort::integer());
        second.name = "obj1";
        mm.objectives.push_back(second);

        struct Case { Hir::ObjectiveCombination c; const char* expect; };
        for (const auto& tc : {
                 Case{Hir::ObjectiveCombination::LEXICOGRAPHIC, "(set-option :opt.priority lex)"},
                 Case{Hir::ObjectiveCombination::PARETO,        "(set-option :opt.priority pareto)"},
                 Case{Hir::ObjectiveCombination::BOX,           "(set-option :opt.priority box)"}}) {
            mm.objective_combination = tc.c;
            Diagnostics d2;
            const std::string s = Lower::emitObjectives(mm, Lower::OmtDialect::Z3, lowerer, d2);
            assert(!d2.hasErrors());
            assert(contains(s, tc.expect));
            // The objectives themselves are still emitted, before which the
            // option would be pointless and after which Z3 would not see it.
            assert(contains(s, "(minimize "));
            assert(s.find(tc.expect) < s.find("(minimize "));
        }

        // minmax and maxmin are this engine's own commands with no Z3
        // counterpart. Emitting the objectives without them would silently mean
        // lexicographic, so they are refused rather than approximated.
        for (auto c : {Hir::ObjectiveCombination::MINMAX,
                       Hir::ObjectiveCombination::MAXMIN}) {
            mm.objective_combination = c;
            Diagnostics d3;
            assert(Lower::emitObjectives(mm, Lower::OmtDialect::Z3, lowerer, d3).empty());
            assert(d3.hasErrors());
            assert(d3.firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        }

        // Official OptiMathSAT >= 1.7.0 syntax uses these same priority tokens.
        for (const auto& tc : {
                 Case{Hir::ObjectiveCombination::LEXICOGRAPHIC, "(set-option :opt.priority lex)"},
                 Case{Hir::ObjectiveCombination::PARETO, "(set-option :opt.priority pareto)"},
                 Case{Hir::ObjectiveCombination::BOX, "(set-option :opt.priority box)"}}) {
            mm.objective_combination = tc.c;
            Diagnostics d4;
            const auto text = Lower::emitObjectives(mm, Lower::OmtDialect::OptiMathSAT, lowerer, d4);
            assert(!d4.hasErrors());
            assert(contains(text, tc.expect));
            assert(contains(text, "(minimize x)"));
        }

        // SmtLib2025 renders all five kinds, per Fig. 1:
        //   ( define-multi-objective <symbol> <m-objective-kind> <symbol>+ )
        // The declaration names its members, so it can only come AFTER them --
        // which is why this dialect cannot use the prefix Z3 uses, and why the
        // ordering below is asserted rather than just the presence of the text.
        {
            struct MCase { Hir::ObjectiveCombination c; const char* kind; };
            for (auto tc : {MCase{Hir::ObjectiveCombination::LEXICOGRAPHIC, "OBJECTIVE_LEX"},
                            MCase{Hir::ObjectiveCombination::PARETO,        "OBJECTIVE_PARETO"},
                            MCase{Hir::ObjectiveCombination::BOX,           "OBJECTIVE_BOX"},
                            MCase{Hir::ObjectiveCombination::MINMAX,        "OBJECTIVE_MINMAX"},
                            MCase{Hir::ObjectiveCombination::MAXMIN,        "OBJECTIVE_MAXMIN"}}) {
                mm.objective_combination = tc.c;
                Diagnostics dm;
                const std::string s2 =
                    Lower::emitObjectives(mm, Lower::OmtDialect::SmtLib2025, lowerer, dm);
                assert(!dm.hasErrors());
                assert(contains(s2, std::string("(define-multi-objective multi ")
                                        + tc.kind + " obj0 obj1)"));
                // Exactly one optimize-sat, and it names the MULTI-objective.
                // One per member would ask for several independent
                // optimisations -- which is OBJECTIVE_BOX, a different problem
                // and silently so.
                assert(contains(s2, "(optimize-sat multi)"));
                assert(!contains(s2, "(optimize-sat obj0)"));
                assert(!contains(s2, "(optimize-sat obj1)"));
                // Members are declared before the multi-objective that names
                // them; a solver reading this top-to-bottom needs that order.
                assert(s2.find("(define-objective obj0") < s2.find("(define-multi-objective"));
                assert(s2.find("(define-objective obj1") < s2.find("(define-multi-objective"));
                assert(s2.find("(define-multi-objective") < s2.find("(optimize-sat multi)"));
            }
        }

        // MINMAX and MAXMIN are the asymmetry worth pinning: Z3 refuses them
        // (above) and the 2025 proposal covers them. The dialect nobody
        // implements yet is the more expressive one, which is the argument for
        // emitting it at all.
        {
            mm.objective_combination = Hir::ObjectiveCombination::MINMAX;
            Diagnostics dz, ds;
            assert(Lower::emitObjectives(mm, Lower::OmtDialect::Z3, lowerer, dz).empty());
            assert(dz.hasErrors());
            assert(!Lower::emitObjectives(mm, Lower::OmtDialect::SmtLib2025,
                                          lowerer, ds).empty());
            assert(!ds.hasErrors());
        }

        // A single objective is unaffected: no option, no refusal, any dialect.
        {
            Diagnostics d5;
            const std::string s = Lower::emitObjectives(m, Lower::OmtDialect::Z3, lowerer, d5);
            assert(!d5.hasErrors());
            assert(!contains(s, "opt.priority"));
        }

        // validateObjectives stays dialect-free and must NOT reject a
        // combination it cannot render, or translate() would refuse a model
        // toSmt2(Z3) emits perfectly well.
        {
            mm.objective_combination = Hir::ObjectiveCombination::MAXMIN;
            Diagnostics d6;
            assert(Lower::validateObjectives(mm, lowerer, d6));
            assert(!d6.hasErrors());
        }
    }

    // The low-level rendered event interface is also used by native snapshots.
    // Vendor and proposal soft syntax differ, but first-occurrence cost order
    // must not depend on the caller or on whether later clauses join a group.
    {
        using Kind = Lower::RenderedObjectiveKind;
        const auto event = [](Kind kind, const std::string& term,
                              const std::string& group = "", const std::string& weight = "1") {
            Lower::RenderedObjective value;
            value.kind = kind; value.term = term; value.group = group; value.weight = weight;
            return value;
        };
        const auto occurrences = [](const std::string& text, const std::string& token) {
            std::size_t count = 0, position = 0;
            while ((position = text.find(token, position)) != std::string::npos) {
                ++count; position += token.size();
            }
            return count;
        };
        const std::vector<Lower::RenderedObjective> events = {
            event(Kind::Minimize, "x"), event(Kind::Soft, "p", "g", "2"),
            event(Kind::Maximize, "y"), event(Kind::Soft, "q", "|g|", "7")};
        for (const auto dialect : {Lower::OmtDialect::Z3, Lower::OmtDialect::OptiMathSAT}) {
            Diagnostics dd;
            const auto rendered = Lower::emitRenderedObjectives(events,
                Hir::ObjectiveCombination::LEXICOGRAPHIC, dialect, dd);
            assert(!dd.hasErrors());
            assert(contains(rendered.preamble, ":opt.priority lex"));
            assert(rendered.query == "(check-sat)\n");
            assert(rendered.commands.find("(minimize x)") < rendered.commands.find("(assert-soft p"));
            assert(rendered.commands.find("(assert-soft p") < rendered.commands.find("(maximize y)"));
            assert(rendered.commands.find("(maximize y)") < rendered.commands.find("(assert-soft q"));
            assert(contains(rendered.commands, ":weight 2"));
            assert(contains(rendered.commands, ":weight 7"));
            assert(occurrences(rendered.commands, "(minimize g)") ==
                   (dialect == Lower::OmtDialect::OptiMathSAT ? 1 : 0));
        }
        {
            Diagnostics dd;
            const auto rendered = Lower::emitRenderedObjectives(events,
                Hir::ObjectiveCombination::LEXICOGRAPHIC, Lower::OmtDialect::Gomt, dd);
            assert(!dd.hasErrors());
            assert(contains(rendered.preamble, "(set-option :enable-omt true)"));
            assert(rendered.objective_names.size() == 3);
            assert(occurrences(rendered.commands, "(define-maxsmt-objective ") == 1);
            assert(occurrences(rendered.commands, ":objective ") == 2);
            assert(!contains(rendered.commands, ":id "));
            assert(contains(rendered.commands, "OBJECTIVE_LEX"));
            assert(occurrences(rendered.query, "(optimize-sat ") == 1);
            assert(!contains(rendered.query, "check-sat"));
            assert(!contains(rendered.commands, "optimize-sat"));
        }
        {
            // Generated proposal labels cannot shadow terms or one another.
            auto collision = event(Kind::Minimize, "obj0");
            collision.name = "obj0";
            Diagnostics dd;
            const auto rendered = Lower::emitRenderedObjectives({collision},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::Gomt, dd, {"obj0"});
            assert(!dd.hasErrors());
            assert(rendered.objective_names == std::vector<std::string>{"obj0_"});
            assert(contains(rendered.commands, "(define-objective obj0_ OBJECTIVE_MIN obj0)"));
            assert(rendered.query == "(optimize-sat obj0_)\n");
        }
        {
            // An unnamed group is distinct from explicit I in Z3/GOMT. For
            // OptiMathSAT-owned emission, name it freshly instead of merging.
            Diagnostics dd;
            const auto rendered = Lower::emitRenderedObjectives(
                {event(Kind::Soft, "p"), event(Kind::Soft, "q", "I")},
                Hir::ObjectiveCombination::LEXICOGRAPHIC, Lower::OmtDialect::OptiMathSAT, dd);
            assert(!dd.hasErrors());
            assert(contains(rendered.commands, "(minimize __somt_soft_default)"));
            assert(contains(rendered.commands, "(minimize I)"));
        }
        {
            // Existing module soft records need vendor activation, and cannot
            // masquerade as proposal :objective syntax.
            auto legacy = event(Kind::Soft, "", "g");
            legacy.already_emitted = true;
            Diagnostics dom, dg;
            const auto vendor = Lower::emitRenderedObjectives({legacy},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::OptiMathSAT, dom);
            assert(!dom.hasErrors());
            assert(vendor.commands == "(minimize g)\n");
            const auto proposal = Lower::emitRenderedObjectives({legacy},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::Gomt, dg);
            assert(dg.hasErrors());
            assert(proposal.commands.empty() && proposal.query.empty());
        }
        {
            Diagnostics first, second;
            const auto renamed = Lower::emitRenderedObjectives({event(Kind::Soft, "p", "g")},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::OptiMathSAT, first, {"g"});
            assert(!first.hasErrors());
            assert(contains(renamed.commands, ":id g_)"));
            assert(contains(renamed.commands, "(minimize g_)"));
            const auto stable = Lower::emitRenderedObjectives({event(Kind::Soft, "p", "g_")},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::OptiMathSAT, second, {"g"});
            assert(!second.hasErrors());
            assert(renamed.commands == stable.commands);
        }
        {
            Diagnostics first, second;
            const auto original = Lower::emitRenderedObjectives({event(Kind::Soft, "p", "g")},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::Gomt, first);
            assert(!first.hasErrors());
            assert(original.objective_names == std::vector<std::string>{"g"});
            const auto reread = Lower::emitRenderedObjectives(
                {event(Kind::Soft, "p", original.objective_names[0])},
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::Gomt, second);
            assert(!second.hasErrors());
            assert(original.commands == reread.commands && original.query == reread.query);
        }
        {
            Diagnostics dd;
            const auto bad = Lower::emitRenderedObjectives(events,
                Hir::ObjectiveCombination::SINGLE, Lower::OmtDialect::Z3, dd);
            assert(dd.hasErrors());
            assert(bad.preamble.empty() && bad.commands.empty() && bad.query.empty());
        }
        for (const auto dialect : {Lower::OmtDialect::Z3, Lower::OmtDialect::OptiMathSAT,
                                    Lower::OmtDialect::Gomt}) {
            Diagnostics dd;
            const auto empty = Lower::emitRenderedObjectives({},
                Hir::ObjectiveCombination::SINGLE, dialect, dd);
            assert(!dd.hasErrors());
            assert(empty.preamble.empty() && empty.commands.empty());
            assert(empty.query == "(check-sat)\n");
        }
        for (const auto combination : {Hir::ObjectiveCombination::MINMAX, Hir::ObjectiveCombination::MAXMIN}) {
            const auto kind = combination == Hir::ObjectiveCombination::MINMAX ? Kind::Minimize : Kind::Maximize;
            Diagnostics dd;
            const auto rendered = Lower::emitRenderedObjectives({event(kind, "x"), event(kind, "y")},
                combination, Lower::OmtDialect::OptiMathSAT, dd);
            assert(!dd.hasErrors());
            assert(rendered.commands == (kind == Kind::Minimize ? "(minmax x y)\n" : "(maxmin x y)\n"));
            Diagnostics bad;
            assert(Lower::emitRenderedObjectives({event(Kind::Minimize, "x"), event(Kind::Maximize, "y")},
                combination, Lower::OmtDialect::OptiMathSAT, bad).commands.empty());
            assert(bad.hasErrors());
        }
    }

    {
        // HIR GOMT output reconstructs real soft clauses from the retained
        // parser; its caller writes a hard-only module, not vendor :id clauses.
        auto soft_model = m;
        soft_model.objective_combination = Hir::ObjectiveCombination::LEXICOGRAPHIC;
        Hir::Constraint first;
        first.formula = Hir::mkBool(true);
        first.soft = true;
        first.weight_text = "9007199254740993";
        first.group = "|group cost|";
        auto second = first;
        second.formula = Hir::mkBool(false);
        second.weight_text = "7";
        soft_model.constraints = {first, second};
        const auto soft_parser = newParser();
        Lower::HirToParser soft_lowerer(soft_parser);
        TranslationReport soft_report;
        Diagnostics lowering;
        assert(soft_lowerer.lower(soft_model, soft_report, lowering));
        assert(!lowering.hasErrors());
        Diagnostics initial;
        std::vector<std::string> names;
        const auto text = Lower::emitObjectives(soft_model, Lower::OmtDialect::Gomt,
                                                soft_lowerer, initial, 1, &names);
        assert(!initial.hasErrors());
        assert(names.size() == 2);
        assert(contains(text, "(define-maxsmt-objective "));
        assert(contains(text, "(assert-soft true :weight 9007199254740993 :objective "));
        assert(contains(text, "(assert-soft false :weight 7 :objective "));
        assert(!contains(text, ":id "));
        assert(contains(text, "OBJECTIVE_LEX"));
        assert(contains(text, "(optimize-sat "));
        // Releasing the HIR records must not lose exact weights/group identity.
        soft_model.constraints.clear();
        Diagnostics consumed;
        const auto again = Lower::emitObjectives(soft_model, Lower::OmtDialect::Gomt,
                                                 soft_lowerer, consumed, 1);
        assert(!consumed.hasErrors());
        assert(text == again);
    }

    static_assert(Lower::OmtDialect::Gomt == Lower::OmtDialect::SmtLib2025);
    std::cout << "All OMT dialect tests passed." << std::endl;
    return 0;
}
