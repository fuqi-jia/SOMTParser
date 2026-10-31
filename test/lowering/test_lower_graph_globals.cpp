#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/lowering/decompose_globals_pass.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"

#include <string>
#include <utility>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {
namespace H = SOMTParser::Uir::Hir;

bool contains(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}

H::ExprPtr graph(const char* name, std::size_t n, std::vector<long long> from,
                 std::vector<long long> to, std::vector<H::ExprPtr> nodes,
                 std::vector<H::ExprPtr> edges) {
    std::vector<H::ExprPtr> args{H::mkInt(static_cast<long long>(n)),
                                 H::mkInt(static_cast<long long>(from.size()))};
    for (const auto value : from) { args.push_back(H::mkInt(value)); }
    for (const auto value : to) { args.push_back(H::mkInt(value)); }
    args.insert(args.end(), nodes.begin(), nodes.end());
    args.insert(args.end(), edges.begin(), edges.end());
    return H::mkGlobal(name, std::move(args));
}

H::ConstraintModel modelWith(H::ExprPtr expr) {
    H::ConstraintModel model;
    for (const char* name : {"n0", "n1", "n2", "e0", "e1"}) {
        H::VarDecl d;
        d.name = name;
        d.sort = H::Sort::boolean();
        model.decls.push_back(std::move(d));
    }
    H::Constraint c;
    c.formula = std::move(expr);
    model.constraints.push_back(std::move(c));
    return model;
}

bool encode(H::ConstraintModel model, std::string& smt, Diagnostics& diagnostics) {
    Lower::registerBuiltinPasses(PassRegistry::instance());
    const auto profile = EncodingProfile::builtin("ground");
    VERIFY(profile != nullptr);
    TranslationReport report;
    if (!PassManager::run(model, *profile, PassRegistry::instance(), report,
                          diagnostics)) {
        return false;
    }
    VERIFY(H::typeCheck(model, diagnostics));
    ParserPtr parser = newParser();
    Lower::HirToParser lower(parser);
    if (!lower.lower(model, report, diagnostics)) { return false; }
    smt = parser->dumpSMT2();
    return true;
}
} // namespace

int main() {
    const auto nodes = std::vector<H::ExprPtr>{H::mkIdent("n0", H::Sort::boolean()),
                                               H::mkIdent("n1", H::Sort::boolean())};
    const auto edges = std::vector<H::ExprPtr>{H::mkIdent("e0", H::Sort::boolean())};

    // The graph witness is local to the formula, so no target declaration is
    // introduced and the same relation can safely occur under NOT.
    {
        std::string directed, undirected;
        Diagnostics d;
        VERIFY(encode(modelWith(graph("dconnected", 2, {0}, {1}, nodes, edges)),
                      directed, d));
        VERIFY(encode(modelWith(graph("connected", 2, {0}, {1}, nodes, edges)),
                      undirected, d));
        VERIFY(contains(directed, "exists"));
        VERIFY(contains(undirected, "exists"));
        VERIFY(directed != undirected);
        VERIFY(directed.find("dconnected") == std::string::npos);
        VERIFY(undirected.find("connected") == std::string::npos);
    }

    // Generated witness names must not capture an enclosing source binder.
    // These are the exact first root/rank spellings chosen by the lowering;
    // the pass must freshen both names rather than relying on a user-facing
    // identifier restriction.
    {
        for (const auto& item : std::vector<std::pair<const char*, const char*>>{
                 {"connected", "!conn_root0"},
                 {"dconnected", "!dconn_root0"}}) {
            H::ConstraintModel scoped = modelWith(
                graph(item.first, 2, {0}, {1}, nodes, edges));
            scoped.constraints.front().formula = H::mkForall(
                {{item.second, H::Sort::integer()},
                 {item.first == std::string("connected") ? "!conn_rank1"
                                                          : "!dconn_rank1",
                  H::Sort::integer()}},
                scoped.constraints.front().formula);
            std::string smt;
            Diagnostics d;
            VERIFY(encode(std::move(scoped), smt, d));
            VERIFY(contains(smt, item.first == std::string("connected")
                                     ? "!conn_root0_1"
                                     : "!dconn_root0_1"));
            VERIFY(contains(smt, item.first == std::string("connected")
                                     ? "!conn_rank1_1"
                                     : "!dconn_rank1_1"));
        }
    }

    // An empty universe has no possible selected root, so the exact relation
    // is false. This is distinct from a selected isolated singleton.
    {
        H::ConstraintModel empty;
        H::Constraint c;
        c.formula = graph("connected", 0, {}, {}, {}, {});
        empty.constraints.push_back(std::move(c));
        std::string smt;
        Diagnostics d;
        VERIFY(encode(std::move(empty), smt, d));
        VERIFY(!smt.empty());
    }

    // The native checker owns the canonical layout and rejects malformed
    // counts, endpoint indices, and selector sorts before decomposition.
    {
        Diagnostics d;
        auto bad_endpoint = modelWith(graph("connected", 2, {2}, {1}, nodes, edges));
        VERIFY(!H::typeCheck(bad_endpoint, d));
        VERIFY(d.hasErrors());

        d = Diagnostics{};
        auto bad_nodes = nodes;
        bad_nodes[1] = H::mkInt(1);
        auto bad_sort = modelWith(graph("dconnected", 2, {0}, {1}, bad_nodes, edges));
        VERIFY(!H::typeCheck(bad_sort, d));
        VERIFY(d.hasErrors());
    }
    return 0;
}
