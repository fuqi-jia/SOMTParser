#include "somtparser/translation/module.h"
#include "somtparser/languages/register_all.h"
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    Lang::SourceUnit unit;
    unit.inline_source = "aag 0 0 0 0 0\n";
    auto empty = Lang::importModule(unit, "aiger");
    VERIFY(empty.ok());
    VERIFY(empty.module->systems.size() == 1);
    VERIFY(empty.module->systems[0].variables.empty());
    VERIFY(empty.module->systems[0].bad.empty());
    const auto circuit_export = Lang::exportModule(*empty.module);
    VERIFY(circuit_export.ok());
    VERIFY(circuit_export.smt2.find("(define-fun ") != std::string::npos);
    VERIFY(circuit_export.smt2.find("(check-sat)") == std::string::npos);
    unit.data_paths = {"ignored.aag"};
    VERIFY(!Lang::importModule(unit, "aiger").ok());
    unit.data_paths.clear();
    VERIFY(!Lang::importModule(unit, "missing-language").ok());
    unit.inline_source = "predicate p(var int: x); var 1..2: x; constraint p(x); solve satisfy;";
    auto open = Lang::importModule(unit, "flatzinc");
    VERIFY(open.ok());
    VERIFY(open.module->unresolved.size() == 1);
    VERIFY(open.module->known.decls.size() == 1);
    VERIFY(open.module->unresolved[0].arguments[0].values.size() == 1);
    const auto open_export = Lang::exportModule(*open.module);
    VERIFY(open_export.ok());
    VERIFY(open_export.interface_json.find("\"predicate\":\"p\"") != std::string::npos);
    VERIFY(open_export.smt2.find("(assert (somt.module.external.0 x))") != std::string::npos);
    unit.inline_source = "(define-system S :output ((x Int)))";
    const auto integer_system = Lang::importModule(unit, "moxi");
    VERIFY(integer_system.ok());
    auto bounded = *integer_system.module;
    bounded.systems[0].context.decls[0].lower_bound = Uir::Hir::mkInt("0");
    const auto invalid_export = Lang::exportModule(bounded);
    VERIFY(!invalid_export.ok());
    VERIFY(invalid_export.smt2.empty());
    unit.inline_source = "(define-system S :init missing)";
    auto invalid = Lang::importModule(unit, "moxi");
    VERIFY(!invalid.ok());
    VERIFY(invalid.diagnostics.firstErrorCode() != Uir::ErrorCode::E_INTERNAL);
    unit.inline_source = "(declare-datatype E (par (T) (none) (some (value T))))"
                         "(define-system S :input ((x (E Int))) :inv (= x none))";
    VERIFY(!Lang::importModule(unit, "moxi").ok());
    Lang::ParseOptions reader;
    reader.options["flat_datatype_constructors"] = "true";
    const auto compatible = Lang::importModule(unit, "moxi", reader);
    VERIFY(compatible.ok());
    VERIFY(compatible.module->source_rewrites.size() == 1);
    VERIFY(Lang::exportModule(*compatible.module).ok());
    reader.strict = true;
    VERIFY(!Lang::importModule(unit, "moxi", reader).ok());
    reader.strict = false;
    reader.options["unknown"] = "true";
    VERIFY(!Lang::importModule(unit, "moxi", reader).ok());
    unit.inline_source = "aag 0 0 0 0 0\n";
    VERIFY(!Lang::importModule(unit, "aiger", reader).ok());
    return 0;
}
