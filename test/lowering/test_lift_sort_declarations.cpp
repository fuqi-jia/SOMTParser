// Explicit free sort constructors are part of the HIR signature even when no
// declaration or assertion uses them. These are also the constructors the
// counting boundary must see after Translation lowers back to Parser.

#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/translation/semantics.h"
#include "somtparser/translation/translate.h"
#include "somtparser/hir/typecheck.h"

#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace Sem = SOMTParser::Uir::Sem;

int main() {
    {
        ParserPtr input = newParser();
        VERIFY(input->parseStr(
            "(set-logic ALL)\n"
            "(declare-sort U 0)\n"
            "(declare-sort Box 1)\n"
            "(define-sort Alias () Int)\n"
            "(define-sort AliasU () U)\n"
            "(define-sort AliasBox () (Box Int))\n"
            "(declare-datatype D ((d)))\n"
            "(define-sort AliasD () D)\n"
            "(declare-fun U () Bool)\n"));

        H::ConstraintModel model;
        Diagnostics diagnostics;
        Lower::ParserToHir up(input);
        VERIFY(up.lift(model, diagnostics));
        VERIFY(model.uninterpreted_sorts.size() == 2);
        VERIFY(model.uninterpreted_sorts[0].name == "U");
        VERIFY(model.uninterpreted_sorts[0].arity == 0);
        VERIFY(model.uninterpreted_sorts[1].name == "Box");
        VERIFY(model.uninterpreted_sorts[1].arity == 1);
        VERIFY(model.datatypes.size() == 1);
        const auto signature = Sem::signatureOf(model);
        VERIFY(signature.sort_constructors.size() == 2);
        VERIFY(signature.sort_constructors[0].name == "U");
        VERIFY(signature.sort_constructors[0].arity == 0);
        VERIFY(signature.sort_constructors[1].name == "Box");
        VERIFY(signature.sort_constructors[1].arity == 1);
        VERIFY(H::typeCheck(model, diagnostics));

        // Exercise the public translation facade used by Parser.cnf(), not
        // only the lowerer directly. Unused constructors must still reach the
        // translated Parser where the conservative counting guard inspects it.
        Translation translated = translate(model);
        VERIFY(translated.ok());
        VERIFY(translated.parser()->getSymbolManager()->hasSort("U"));
        const auto box = translated.parser()->getSymbolManager()->resolveSort("Box");
        VERIFY(box != nullptr);
        VERIFY(box->arity == 1);

        ParserPtr output = newParser();
        Lower::HirToParser down(output);
        TranslationReport report;
        VERIFY(down.lower(model, report, diagnostics));
        const std::string text = output->dumpSMT2();
        VERIFY(text.find("(declare-sort U 0)") != std::string::npos);
        VERIFY(text.find("(declare-sort Box 1)") != std::string::npos);
        ParserPtr reparsed = newParser();
        VERIFY(reparsed->parseStr(text));
    }

    {
        H::ConstraintModel model;
        model.uninterpreted_sorts.push_back({"Box", 1, {}});
        H::VarDecl value;
        value.name = "x";
        value.sort = H::Sort::sortApp("Box", {H::Sort::integer(),
                                               H::Sort::boolean()});
        model.decls.push_back(value);
        Diagnostics diagnostics;
        VERIFY(!H::typeCheck(model, diagnostics));
    }

    {
        H::ConstraintModel model;
        model.uninterpreted_sorts.push_back({"U", 0, {}});
        model.uninterpreted_sorts.push_back({"U", 0, {}});
        Diagnostics diagnostics;
        VERIFY(!H::typeCheck(model, diagnostics));
    }

    {
        H::ConstraintModel model;
        model.uninterpreted_sorts.push_back({"SameName", 0, {}});
        H::FunDecl function;
        function.name = "SameName";  // SMT-LIB sort and term namespaces differ.
        function.result = H::Sort::boolean();
        model.funs.push_back(function);
        Diagnostics diagnostics;
        VERIFY(H::typeCheck(model, diagnostics));
    }

    {
        H::ConstraintModel model;
        model.uninterpreted_sorts.push_back({"Clash", 0, {}});
        H::DatatypeDecl datatype;
        datatype.name = "Clash";
        datatype.constructors.push_back({"clash-value", {}});
        model.datatypes.push_back(datatype);
        Diagnostics diagnostics;
        VERIFY(!H::typeCheck(model, diagnostics));
    }

    {
        // A datatype's local parameter must shadow and then restore an
        // already declared global constructor with the same spelling.
        ParserPtr input = newParser();
        VERIFY(input->parseStr(
            "(set-logic ALL)\n"
            "(declare-sort U 1)\n"
            "(declare-datatype D (par (U) ((d (value U)))))\n"
            "(declare-const x (U Int))\n"));
        H::ConstraintModel model;
        Diagnostics diagnostics;
        Lower::ParserToHir up(input);
        VERIFY(up.lift(model, diagnostics));
        VERIFY(model.uninterpreted_sorts.size() == 1);
        VERIFY(model.uninterpreted_sorts[0].name == "U");
        VERIFY(model.uninterpreted_sorts[0].arity == 1);
        VERIFY(model.datatypes.size() == 1);
        VERIFY(model.decls.size() == 1);
        VERIFY(model.decls[0].sort.args.size() == 1);
        VERIFY(H::typeCheck(model, diagnostics));
    }

    {
        // A parameter's historical order entry must not hide or duplicate a
        // later top-level declaration with the same spelling.
        ParserPtr input = newParser();
        VERIFY(input->parseStr(
            "(set-logic ALL)\n"
            "(declare-datatype D (par (U) ((d (value U)))))\n"
            "(declare-sort U 0)\n"));
        H::ConstraintModel model;
        Diagnostics diagnostics;
        Lower::ParserToHir up(input);
        VERIFY(up.lift(model, diagnostics));
        VERIFY(model.uninterpreted_sorts.size() == 1);
        VERIFY(model.uninterpreted_sorts[0].name == "U");
    }

    {
        // Each member of a mutually declared datatype group gets a local
        // parameter scope; both must restore the same outer free constructor.
        ParserPtr input = newParser();
        VERIFY(input->parseStr(
            "(set-logic ALL)\n"
            "(declare-sort U 1)\n"
            "(declare-datatypes ((D 1) (E 1)) "
            "((par (U) ((d (dvalue U)))) (par (U) ((e (evalue U))))))\n"
            "(declare-const x (U Int))\n"));
        H::ConstraintModel model;
        Diagnostics diagnostics;
        Lower::ParserToHir up(input);
        VERIFY(up.lift(model, diagnostics));
        VERIFY(model.uninterpreted_sorts.size() == 1);
        VERIFY(model.uninterpreted_sorts[0].arity == 1);
        VERIFY(model.datatypes.size() == 2);
        VERIFY(H::typeCheck(model, diagnostics));
    }

    {
        // A temporary datatype parameter must not be recorded as a pushed
        // declaration or remove an outer sort when that parser scope is popped.
        ParserPtr input = newParser();
        VERIFY(input->parseStr(
            "(set-logic ALL)\n"
            "(declare-sort U 1)\n"
            "(push 1)\n"
            "(declare-datatype D (par (U) ((d (value U)))))\n"
            "(pop 1)\n"
            "(declare-const x (U Int))\n"));
        H::ConstraintModel model;
        Diagnostics diagnostics;
        Lower::ParserToHir up(input);
        VERIFY(up.lift(model, diagnostics));
        VERIFY(model.uninterpreted_sorts.size() == 1);
        VERIFY(model.uninterpreted_sorts[0].arity == 1);
        VERIFY(model.decls.size() == 1);
        VERIFY(model.decls[0].name == "x");
        VERIFY(model.decls[0].sort.args.size() == 1);
    }
}
