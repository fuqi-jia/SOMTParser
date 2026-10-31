// Deep XML and expression input must use explicit stacks, including failure
// unwinding. The expected HIR is checked directly, without a recursive printer.
#include "somtparser/languages/xcsp3.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {
Lang::ParseOutcome parse(std::string text) {
    Lang::SourceUnit unit;
    unit.display_name = "deep.xml";
    unit.inline_source = std::move(text);
    return Lang::mkXcsp3Language()->parse(unit, {});
}
std::string repeat(const std::string& text, std::size_t count) {
    std::string result;
    result.reserve(text.size() * count);
    while (count--) { result += text; }
    return result;
}
std::string instance(const std::string& constraints, const std::string& objectives = "") {
    return "<instance format=\"XCSP3\" type=\"" + std::string(objectives.empty() ? "CSP" : "COP")
        + "\"><variables><var id=\"x\">-2..2</var><var id=\"y\">-2..2</var>"
          "</variables><constraints>" + constraints + "</constraints>" + objectives + "</instance>";
}
bool diagnostic(const Lang::ParseOutcome& parsed, const std::string& text) {
    for (const auto& entry : parsed.diagnostics.all()) {
        if (entry.message.find(text) != std::string::npos) { return true; }
    }
    return false;
}
}

int main() {
    constexpr std::size_t depth = 12000;
    {
        auto parsed = parse(instance(repeat("<block>", depth)
            + "<intension>eq(x,1)</intension>" + repeat("</block>", depth)
            + "<intension>eq(y,2)</intension>"));
        VERIFY(parsed.ok());
        VERIFY(parsed.model->constraints.size() == 2);
        const auto& first = parsed.model->constraints[0].formula;
        const auto& second = parsed.model->constraints[1].formula;
        VERIFY(first->op == H::Op::EQ && first->args[0]->name == "x");
        VERIFY(first->args[1]->name == "1");
        VERIFY(second->op == H::Op::EQ && second->args[0]->name == "y");
        VERIFY(second->args[1]->name == "2");
    }
    {
        // A deep group template exercises iterative Elem copying and formal
        // substitution as well as the suspended per-row lowering continuation.
        auto parsed = parse(instance("<group>" + repeat("<block>", depth)
            + "<intension>eq(%0,1)</intension>" + repeat("</block>", depth)
            + "<args>x</args><args>y</args></group>"));
        VERIFY(parsed.ok());
        VERIFY(parsed.model->constraints.size() == 2);
        VERIFY(parsed.model->constraints[0].formula->args[0]->name == "x");
        VERIFY(parsed.model->constraints[1].formula->args[0]->name == "y");
    }
    {
        // Deep retained XML is destroyed even though annotations add no formula.
        auto parsed = parse("<instance format=\"XCSP3\" type=\"CSP\"><annotations>"
            + repeat("<note>", depth * 2) + "text&amp;more"
            + repeat("</note>", depth * 2) + "</annotations></instance>");
        VERIFY(parsed.ok() && parsed.model->constraints.empty());
        auto malformed = parse(instance(repeat("<block>", depth) + "</wrong>"));
        VERIFY(!malformed.ok() && diagnostic(malformed, "closed by"));
    }
    {
        constexpr std::size_t expression_depth = 4096;
        const std::string expression = repeat("neg(", expression_depth) + "x"
            + repeat(")", expression_depth);
        auto parsed = parse(instance("<intension>eq(" + expression + ",1)</intension>",
            "<objectives combination=\"lexico\"><minimize>" + expression
            + "</minimize><maximize>y</maximize></objectives>"));
        VERIFY(parsed.ok());
        VERIFY(parsed.model->objectives.size() == 2);
        auto cursor = parsed.model->constraints[0].formula->args[0];
        for (std::size_t i = 0; i < expression_depth; ++i) {
            VERIFY(cursor->op == H::Op::SUB && cursor->args.size() == 2);
            VERIFY(cursor->args[0]->name == "0");
            cursor = cursor->args[1];
        }
        VERIFY(cursor->kind == H::ExprKind::IDENT && cursor->name == "x");
        auto invalid = parse(instance("<intension>eq(" + repeat("neg(", expression_depth)
            + "x y" + repeat(")", expression_depth) + ",1)</intension>"));
        VERIFY(!invalid.ok() && diagnostic(invalid, "expected ',' or ')'"));
    }
    {
        // Repeated syntactic subexpressions still share the actual typed DAG.
        const auto subtree = repeat("neg(", 512) + "x" + repeat(")", 512);
        auto parsed = parse(instance("<intension>eq(add(" + subtree + "," + subtree
            + "),y)</intension>"));
        VERIFY(parsed.ok());
        const auto sum = parsed.model->constraints[0].formula->args[0];
        VERIFY(sum->op == H::Op::ADD && sum->args.size() == 2);
        VERIFY(sum->args[0] == sum->args[1]);
    }
    {
        // The mixed-radix prefix walk is independent of array rank. Only two
        // rows are created, and the complete 65536-cell domain is retained.
        const std::string prefix = "a" + repeat("[3]", 4096);
        auto parsed = parse("<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"a\" startIndex=\"3\" size=\"" + repeat("[1]", 4096)
            + "[2][32768]\">-2..2</array></variables></instance>");
        VERIFY(parsed.ok());
        VERIFY(parsed.model->scalar_var_ranges.size() == 2);
        for (std::size_t i = 0; i < 2; ++i) {
            const auto& range = parsed.model->scalar_var_ranges[i];
            VERIFY(range.prefix == prefix + "[" + std::to_string(3 + i) + "][");
            VERIFY(range.first == 3 && range.count == 32768);
            VERIFY(range.lower_bound->name == "-2" && range.upper_bound->name == "2");
        }
    }
    {
        constexpr std::size_t width = 2048;
        const std::string scope = repeat("%0 ", width);
        const std::string suffix = repeat(",0", width - 1);
        auto parsed = parse(instance("<group><extension><list>" + scope
            + "</list><supports>(0" + suffix + ")(1" + suffix
            + ")</supports></extension><args>x</args><args>y</args><args>x</args></group>"));
        VERIFY(parsed.ok());
        VERIFY(parsed.model->funs.size() == 1);
        const auto& helper = parsed.model->funs.front();
        VERIFY(helper.binders.size() == 1);
        std::unordered_set<const H::Expr*> visited;
        std::vector<const H::Expr*> pending{helper.body.get()};
        std::size_t bound_nodes = 0;
        while (!pending.empty()) {
            const auto* expression = pending.back(); pending.pop_back();
            if (!visited.insert(expression).second) { continue; }
            VERIFY(expression->kind != H::ExprKind::IDENT);
            if (expression->kind == H::ExprKind::BOUND_VAR) {
                ++bound_nodes;
                VERIFY(expression->name == helper.binders[0].name);
            }
            for (const auto& child : expression->args) { pending.push_back(child.get()); }
        }
        VERIFY(bound_nodes == 1); // repeated columns retain DAG sharing
        VERIFY(parsed.model->constraints.size() == 3);
        VERIFY(parsed.model->constraints[0].formula->args[0]->name == "x");
        VERIFY(parsed.model->constraints[1].formula->args[0]->name == "y");
        VERIFY(parsed.model->constraints[2].formula->args[0]->name == "x");
    }
    {
        // A long directed cycle with one root and one terminal reaches the
        // graph-cycle check (rather than an earlier root-count refusal).
        std::string transitions = "(root,0,sink)(root,0,q0)";
        for (std::size_t i = 0; i < depth; ++i) {
            transitions += "(q" + std::to_string(i) + ",0,q"
                + std::to_string((i + 1) % depth) + ")";
        }
        auto parsed = parse(instance("<mdd><list>x y</list><transitions>"
            + transitions + "</transitions></mdd>"));
        VERIFY(!parsed.ok() && diagnostic(parsed, "directed cycle"));
    }
    return 0;
}
