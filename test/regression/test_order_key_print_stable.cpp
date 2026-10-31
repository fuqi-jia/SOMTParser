// The key that canonicalises commutative operand order must depend only on how
// an operand prints.
//
// It used to be DAGNode::hashCode(), which also mixes in the sort string and
// the internal name/child layout. Historically a Real literal printed as `0`
// and read back as IntOrReal; the exporter now preserves `0.0`. An fp literal built by
// ((_ to_fp 11 53) RNE 1.0) is a childless node whose name is the whole
// literal, while the same text read back as (fp #b0 ...) is a three-child node
// named "(fp_bit_representation)". Ordering by hashCode() therefore gave one
// script two different operand orders on consecutive parses, and dumpSMT2()
// never reached a fixed point.
//
// test_dump_roundtrip_instances.cpp catches that end to end, but only for terms
// the corpus happens to contain, and only as an opaque "line N differs". This
// file pins the underlying invariant directly, on the two representation splits
// that actually caused it: nodes that print alike must key alike, whatever they
// look like inside.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <cstdint>
#include <memory>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

// Parses `script` and returns the operand of the single top-level assertion's
// binary root that prints as `wanted`.
std::shared_ptr<DAGNode> operandPrintingAs(const std::string& script, const std::string& wanted) {
    auto parser = std::make_shared<Parser>();
    VERIFY(parser->parseStr(script));
    const auto assertions = parser->getAssertions();
    VERIFY(assertions.size() == 1);
    for (const auto& child : assertions[0]->getChildren()) {
        if (dumpSMTLIB2(child) == wanted) return child;
    }
    std::cerr << "  no operand printed as " << wanted << "; assertion was "
              << dumpSMTLIB2(assertions[0]) << "\n";
    VERIFY(false);
    return nullptr;
}

void check(const char* what, const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b) {
    // Guard the premise: if these ever stop printing alike the test below would
    // pass for the wrong reason.
    VERIFY(dumpSMTLIB2(a) == dumpSMTLIB2(b));
    std::cout << "  " << what << ": both print as " << dumpSMTLIB2(a) << "\n";
    if (a->orderKey() != b->orderKey()) {
        std::cerr << "  order keys differ: " << a->orderKey() << " vs " << b->orderKey() << "\n";
        VERIFY(false);
    }
    std::cout << "    same order key, despite sort " << a->getSort()->toString() << " vs "
              << b->getSort()->toString() << " and " << a->getChildrenSize() << " vs "
              << b->getChildrenSize() << " children\n";
}

}  // namespace

int main() {
    std::cout << "======= commutative order key depends only on printed form =======\n";

    // The first request for a shared DAG's key must equal the hash of its
    // fully expanded canonical text. Caching descendants changes the work
    // performed, never the operand ordering or the byte sequence it denotes.
    {
        auto parser = newParser();
        auto maximum = parser->mkVarInt("first");
        for (unsigned i = 0; i < 7; ++i) {
            const auto item = parser->mkVarInt("item" + std::to_string(i));
            maximum = parser->mkIte(parser->mkGe(maximum, item), maximum, item);
        }
        std::uint64_t expected = 0;
        for (const unsigned char byte : dumpSMTLIB2(maximum)) {
            expected = expected * 1099511628211ull + byte;
        }
        VERIFY(maximum->orderKey() == static_cast<std::size_t>(expected));
        VERIFY(maximum->orderKey() == static_cast<std::size_t>(expected));
    }

    // Integral Real literals retain their sort and order key on export/reparse.
    {
        const std::string decl = "(set-logic ALL)(declare-const zero2 Real)";
        auto written = operandPrintingAs(decl + "(assert (= zero2 0.00000))", "0.0");
        auto reread = operandPrintingAs(decl + "(assert (= zero2 0.0))", "0.0");
        VERIFY(written->getSort()->isReal() && reread->getSort()->isReal());
        check("real zero", written, reread);
    }

    // An fp literal built by to_fp, and the same text read back as (fp ...).
    {
        const std::string decl = "(set-logic ALL)(declare-const x (_ FloatingPoint 11 53))";
        const std::string triple =
            "(fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)";
        auto folded = operandPrintingAs(decl + "(assert (fp.eq x ((_ to_fp 11 53) RNE 1.0)))", triple);
        auto reread = operandPrintingAs(decl + "(assert (fp.eq x " + triple + "))", triple);
        VERIFY(folded->getChildrenSize() != reread->getChildrenSize());
        check("fp one", folded, reread);
    }

    // The checks above pin orderKey() itself. This one pins that the operand
    // ordering actually uses it: a commutative operator over operands that
    // print alike must lay them out the same way in both scripts. Reverting
    // sortParams to hashCode() leaves every check above passing and fails here.
    {
        const std::string decl = "(set-logic ALL)(declare-const x (_ FloatingPoint 11 53))";
        auto folded = std::make_shared<Parser>();
        VERIFY(folded->parseStr(decl + "(assert (fp.eq x ((_ to_fp 11 53) RNE 1.0)))"));
        const std::string a = dumpSMTLIB2(folded->getAssertions()[0]);
        auto reread = std::make_shared<Parser>();
        VERIFY(reread->parseStr(decl + "(assert " + a + ")"));
        const std::string b = dumpSMTLIB2(reread->getAssertions()[0]);
        if (a != b) {
            std::cerr << "  commutative order not stable across representations:\n"
                      << "    " << a << "\n    " << b << "\n";
            VERIFY(false);
        }
        std::cout << "  equal-printing operands order alike: " << a << "\n";
    }

    // Sanity: the key is not simply constant, or everything above would pass
    // no matter what the key did.
    {
        const std::string decl = "(set-logic ALL)(declare-const p Int)(declare-const q Int)";
        auto p = operandPrintingAs(decl + "(assert (= p q))", "p");
        auto q = operandPrintingAs(decl + "(assert (= p q))", "q");
        VERIFY(p->orderKey() != q->orderKey());
        std::cout << "  distinct terms still key apart\n";
    }

    std::cout << "Order key depends only on the printed form.\n";
    return 0;
}
