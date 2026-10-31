#include "somtparser/hir/planning_temporal.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <gmpxx.h>
#include <iostream>
#include <stdexcept>

using namespace SOMTParser::Uir;
namespace H = Hir;
namespace P = Hir::Planning;

namespace {
struct Value {
    bool boolean = false;
    bool truth = false;
    mpq_class number = 0;
};

Value boolean(bool value) { return {true, value, 0}; }
Value number(mpq_class value) { return {false, false, std::move(value)}; }

// Independent exact evaluation of emitted ground HIR, not an implementation
// of temporal semantics. The source oracle below reasons directly about
// positions, samples and interval membership.
Value evaluate(const H::ExprPtr& expression) {
    VERIFY(expression);
    if (expression->kind == H::ExprKind::LIT_BOOL) { return boolean(expression->bool_value); }
    if (expression->kind == H::ExprKind::LIT_REAL || expression->kind == H::ExprKind::LIT_INT) {
        mpq_class value(expression->name);
        value.canonicalize();
        return number(value);
    }
    VERIFY(expression->kind == H::ExprKind::OP);
    std::vector<Value> args;
    for (const auto& child : expression->args) { args.push_back(evaluate(child)); }
    switch (expression->op) {
    case H::Op::AND:
        for (const auto& arg : args) { VERIFY(arg.boolean); if (!arg.truth) { return boolean(false); } }
        return boolean(true);
    case H::Op::OR:
        for (const auto& arg : args) { VERIFY(arg.boolean); if (arg.truth) { return boolean(true); } }
        return boolean(false);
    case H::Op::NOT: VERIFY(args.size() == 1 && args[0].boolean); return boolean(!args[0].truth);
    case H::Op::IMPLIES:
        VERIFY(args.size() == 2 && args[0].boolean && args[1].boolean);
        return boolean(!args[0].truth || args[1].truth);
    case H::Op::EQ:
        VERIFY(args.size() == 2 && args[0].boolean == args[1].boolean);
        return boolean(args[0].boolean ? args[0].truth == args[1].truth : args[0].number == args[1].number);
    case H::Op::LT: return boolean(args[0].number < args[1].number);
    case H::Op::LE: return boolean(args[0].number <= args[1].number);
    case H::Op::GT: return boolean(args[0].number > args[1].number);
    case H::Op::GE: return boolean(args[0].number >= args[1].number);
    case H::Op::SUB: return number(args[0].number - args[1].number);
    case H::Op::MUL: return number(args[0].number * args[1].number);
    case H::Op::TO_REAL: return number(args[0].number);
    default: throw std::runtime_error("unexpected operator in temporal test relation");
    }
}

bool truth(const H::ExprPtr& expression) {
    const auto value = evaluate(expression);
    VERIFY(value.boolean);
    return value.truth;
}

bool satisfy(const std::vector<H::ExprPtr>& constraints) {
    for (const auto& constraint : constraints) { if (!truth(constraint)) { return false; } }
    return true;
}

bool bit(unsigned mask, unsigned index) { return (mask & (1U << index)) != 0; }

std::vector<P::TemporalHappening> grid(unsigned mask = 7) {
    std::vector<P::TemporalHappening> result;
    for (unsigned i = 0; i < 3; ++i) {
        result.push_back({H::mkBool(bit(mask, i)), H::mkReal(std::to_string(i + 1))});
    }
    return result;
}

P::TemporalConditionSamples samples(unsigned start, unsigned end, unsigned interval) {
    P::TemporalConditionSamples result;
    for (unsigned i = 0; i < 3; ++i) {
        result.atStart.push_back(H::mkBool(bit(start, i)));
        result.atEnd.push_back(H::mkBool(bit(end, i)));
        if (i < 2) { result.overAll.push_back(H::mkBool(bit(interval, i))); }
    }
    return result;
}
}

int main() {
    // Exact rational coordinates use unbounded integer witnesses. This
    // includes nondecimal fractions and imposes no denominator precision.
    for (int numerator = -7; numerator <= 7; ++numerator) {
        for (int denominator = -3; denominator <= 7; ++denominator) {
            for (bool active : {false, true}) {
                Diagnostics diagnostics;
                const mpq_class value = denominator == 0 ? mpq_class(0)
                    : mpq_class(numerator) / denominator;
                const P::RationalTimeCoordinate coordinate{H::mkReal(value.get_str()),
                    H::mkInt(numerator), H::mkInt(denominator)};
                const auto result = P::encodeRationalTime(coordinate, H::mkBool(active), diagnostics);
                VERIFY(result && satisfy(*result) == (!active || denominator > 0));
            }
        }
    }
    {
        Diagnostics diagnostics;
        P::RationalTimeCoordinate coordinate{H::mkReal("1/1000000007"), H::mkInt(1), H::mkInt(1000000007)};
        const auto exact = P::encodeRationalTime(coordinate, H::mkBool(true), diagnostics);
        VERIFY(exact && satisfy(*exact));
        coordinate.numerator = H::mkReal("1");
        VERIFY(!P::encodeRationalTime(coordinate, H::mkBool(true), diagnostics));
    }
    std::size_t relation_cases = 0;
    for (unsigned active = 0; active < 8; ++active) {
        const bool prefix = active == 0 || active == 1 || active == 3 || active == 7;
        auto happenings = grid(active);
        Diagnostics diagnostics;
        const auto order = P::encodeHappeningOrder(happenings, diagnostics);
        VERIFY(order && satisfy(*order) == prefix);
        for (unsigned start = 0; start < 3; ++start) {
            for (unsigned end = 0; end < 3; ++end) {
                P::DurativeOccurrence occurrence{H::mkBool(true),
                    H::mkReal(std::to_string(start + 1)), H::mkReal(std::to_string(end + 1))};
                for (unsigned start_mask = 0; start_mask < 8; ++start_mask) {
                    for (unsigned end_mask = 0; end_mask < 8; ++end_mask) {
                        for (unsigned interval_mask = 0; interval_mask < 4; ++interval_mask) {
                            auto conditions = samples(start_mask, end_mask, interval_mask);
                            const auto built = P::encodeDurativeOccurrence(happenings, occurrence, conditions, diagnostics);
                            VERIFY(built);
                            bool source = prefix && bit(active, start) && bit(active, end)
                                && end >= start && bit(start_mask, start) && bit(end_mask, end);
                            for (unsigned interval = start; interval < end; ++interval) {
                                source = source && bit(interval_mask, interval);
                            }
                            VERIFY((satisfy(*order) && satisfy(built->constraints)) == source);
                            // A false conditional guard suppresses its effect;
                            // it must not remove an otherwise valid occurrence.
                            const auto bare = P::encodeDurativeOccurrence(happenings, occurrence, {}, diagnostics);
                            const auto effect = P::temporalEffectGuard(happenings, occurrence, conditions,
                                P::TemporalEffectEndpoint::END, diagnostics);
                            VERIFY(bare && effect);
                            if (satisfy(*order) && satisfy(bare->constraints)) { VERIFY(truth(effect) == source); }
                            ++relation_cases;
                        }
                    }
                }
            }
        }
    }
    // The guard must remember the state at the selected start, not the state
    // at the end. Two overlapping occurrences of one action have independent
    // histories even when they finish at the same happening.
    {
        auto happenings = grid();
        auto conditions = samples(1, 7, 3);
        Diagnostics diagnostics;
        P::DurativeOccurrence first{H::mkBool(true), H::mkReal("1"), H::mkReal("3")};
        P::DurativeOccurrence second{H::mkBool(true), H::mkReal("2"), H::mkReal("3")};
        VERIFY(truth(P::temporalEffectGuard(happenings, first, conditions,
            P::TemporalEffectEndpoint::END, diagnostics)));
        VERIFY(!truth(P::temporalEffectGuard(happenings, second, conditions,
            P::TemporalEffectEndpoint::END, diagnostics)));
        VERIFY(!P::temporalEffectGuard(happenings, first, conditions,
            P::TemporalEffectEndpoint::START, diagnostics));
    }
    // Endpoint times are exact Real values; no discretization or positive
    // epsilon changes which intervals can be represented.
    {
        Diagnostics diagnostics;
        std::vector<P::TemporalHappening> happenings{{H::mkBool(true), H::mkReal("1/7")},
                                                   {H::mkBool(true), H::mkReal("2/7")}};
        P::DurativeOccurrence occurrence{H::mkBool(true), happenings[0].time, happenings[1].time};
        auto result = P::encodeDurativeOccurrence(happenings, occurrence, {}, diagnostics);
        VERIFY(result && satisfy(result->constraints));
        VERIFY(evaluate(result->duration).number == mpq_class(1, 7));
        VERIFY(satisfy(*P::encodeHappeningOrder(happenings, diagnostics)));
        happenings[0].time = H::mkReal("0");
        VERIFY(!satisfy(*P::encodeHappeningOrder(happenings, diagnostics)));
    }
    // With no happenings, only an inactive occurrence is permitted.
    {
        Diagnostics diagnostics;
        P::DurativeOccurrence occurrence{H::mkBool(false), H::mkReal("0"), H::mkReal("0")};
        VERIFY(satisfy(P::encodeDurativeOccurrence({}, occurrence, {}, diagnostics)->constraints));
        occurrence.active = H::mkBool(true);
        VERIFY(!satisfy(P::encodeDurativeOccurrence({}, occurrence, {}, diagnostics)->constraints));
    }
    // Source cases for endpoint interference. The implicit old accumulator
    // of an additive update is excluded, but an explicit RHS read is included.
    std::size_t interference_cases = 0;
    for (unsigned kind = 0; kind < 10; ++kind) {
        for (bool together : {false, true}) {
            for (unsigned mask = 0; mask < 4; ++mask) {
                P::TemporalEndpointAccess a, b;
                a.active = H::mkBool(bit(mask, 0)); b.active = H::mkBool(bit(mask, 1));
                a.time = H::mkReal("1"); b.time = H::mkReal(together ? "1" : "2");
                bool source_conflict = true;
                switch (kind) {
                case 0: a.propositionReads = {"p"}; b.propositionAdds = {"p"}; break;
                case 1: a.propositionReads = {"p"}; b.propositionDeletes = {"p"}; break;
                case 2: a.propositionAdds = {"p"}; b.propositionDeletes = {"p"}; break;
                case 3: a.propositionAdds = {"p"}; b.propositionAdds = {"p"}; source_conflict = false; break;
                case 4: a.numericWrites = {"x"}; b.numericWrites = {"x"}; break;
                case 5: a.numericWrites = a.additiveWrites = {"x"}; b.numericWrites = {"x"}; break;
                case 6:
                    a.numericWrites = a.additiveWrites = {"x"};
                    b.numericWrites = b.additiveWrites = {"x"}; source_conflict = false; break;
                case 7: a.numericReads = {"x"}; b.numericWrites = b.additiveWrites = {"x"}; break;
                case 8: a.numericReads = {"y"}; b.numericWrites = {"x"}; source_conflict = false; break;
                case 9: b.propositionReads = {"p"}; a.propositionDeletes = {"p"}; break;
                }
                Diagnostics diagnostics;
                auto result = P::encodeTemporalInterference({a, b}, diagnostics);
                VERIFY(result);
                VERIFY(satisfy(*result) == !(source_conflict && together && mask == 3));
                ++interference_cases;
            }
        }
    }
    // Reject shape/type errors before returning any incomplete encoding.
    {
        Diagnostics diagnostics;
        P::TemporalEndpointAccess reader, writer;
        reader.active = writer.active = H::mkBool(true);
        reader.time = writer.time = H::mkReal("1");
        reader.propositionReads = {"p"}; writer.propositionAdds = {"p"};
        reader.owner_id = writer.owner_id = "same-ground-occurrence-start";
        auto same = P::encodeTemporalInterference({reader, writer}, diagnostics);
        VERIFY(same && satisfy(*same));
        writer.owner_id = "different-ground-occurrence-start";
        auto different = P::encodeTemporalInterference({reader, writer}, diagnostics);
        VERIFY(different && !satisfy(*different));
        P::DurativeOccurrence occurrence{H::mkBool(true), H::mkReal("1"), H::mkReal("2")};
        VERIFY(!P::temporalEffectGuard(grid(), occurrence, {},
            static_cast<P::TemporalEffectEndpoint>(99), diagnostics));
    }
    {
        Diagnostics diagnostics;
        P::DurativeOccurrence occurrence{H::mkBool(true), H::mkReal("1"), H::mkReal("2")};
        auto wrong_samples = samples(7, 7, 3); wrong_samples.atStart.pop_back();
        VERIFY(!P::encodeDurativeOccurrence(grid(), occurrence, wrong_samples, diagnostics));
        auto wrong_grid = grid(); wrong_grid[0].time = H::mkInt(1);
        VERIFY(!P::encodeHappeningOrder(wrong_grid, diagnostics));
        P::TemporalEndpointAccess wrong;
        wrong.active = H::mkBool(true); wrong.time = H::mkReal("1"); wrong.additiveWrites = {"x"};
        VERIFY(!P::encodeTemporalInterference({wrong}, diagnostics));
    }
    // The public shared type checker accepts the composed ordinary HIR.
    {
        Diagnostics diagnostics;
        H::ConstraintModel model;
        auto happenings = grid();
        P::DurativeOccurrence occurrence{H::mkBool(true), H::mkReal("1"), H::mkReal("3")};
        auto order = P::encodeHappeningOrder(happenings, diagnostics);
        auto built = P::encodeDurativeOccurrence(happenings, occurrence, samples(7, 7, 3), diagnostics);
        for (const auto& expression : *order) { H::Constraint row; row.formula = expression; model.constraints.push_back(row); }
        for (const auto& expression : built->constraints) { H::Constraint row; row.formula = expression; model.constraints.push_back(row); }
        VERIFY(H::typeCheck(model, diagnostics));
    }
    std::cout << "{\"relation_cases\":" << relation_cases
              << ",\"interference_cases\":" << interference_cases
              << ",\"passed\":true}\n";
    return 0;
}
