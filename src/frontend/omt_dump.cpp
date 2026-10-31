#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/omt_emitter.h"

#include <sstream>
#include <stdexcept>
#include <unordered_set>

namespace SOMTParser {

std::string softWeightToken(const std::shared_ptr<DAGNode>& weight) {
    condAssert(weight && weight->isNumeral() && weight->getValue(),
               "dumpSMT2: soft weight must be an exact numeric constant");
    mpq_class value = weight->getValue()->getNumberValue().toRationalExact().getMPQ();
    value.canonicalize();
    mpz_class numerator = value.get_num();
    const mpz_class denominator = value.get_den();
    mpz_class factors = denominator;
    while (mpz_divisible_ui_p(factors.get_mpz_t(), 2)) factors /= 2;
    while (mpz_divisible_ui_p(factors.get_mpz_t(), 5)) factors /= 5;
    condAssert(factors == 1,
               "dumpSMT2: soft weight has no exact finite decimal representation");
    const bool negative = numerator < 0;
    if (negative) numerator = -numerator;
    const mpz_class whole = numerator / denominator;
    mpz_class remainder = numerator % denominator;
    std::string token = negative ? "-" : "";
    token += whole.get_str();
    if (remainder != 0) token += '.';
    while (remainder != 0) {
        remainder *= 10;
        const mpz_class digit = remainder / denominator;
        token += static_cast<char>('0' + digit.get_ui());
        remainder %= denominator;
    }
    return token;
}

Lower::RenderedOmt Parser::renderSMT2Objectives(Lower::OmtDialect dialect) {
    namespace H = Uir::Hir;
    using Lower::RenderedObjective;
    using Lower::RenderedObjectiveKind;
    const bool selected_gomt = static_cast<bool>(getObjectiveManager()->getSelectedGomtObjective());
    std::vector<MetaObjectivePtr> objectives;
    for (const auto& objective : getObjectives()) objectives.push_back(objective);
    H::ObjectiveCombination combination = H::ObjectiveCombination::LEXICOGRAPHIC;
    const auto priority = getOptions()->options.find("opt.priority");
    if (priority != getOptions()->options.end()) {
        if (priority->second == "pareto") combination = H::ObjectiveCombination::PARETO;
        else if (priority->second == "box") combination = H::ObjectiveCombination::BOX;
        else if (priority->second != "lex") {
            throw std::runtime_error("dumpSMT2: unsupported opt.priority " + priority->second);
        }
    }
    // The legacy native grammar keeps named member definitions in the active
    // list. A terminal compound objective selects their order and combination.
    if (!objectives.empty() && objectives.back() && objectives.back()->isMultiObjective()) {
        const auto compound = objectives.back();
        condAssert(selected_gomt || context_.soft_assertions.empty(),
                   "dumpSMT2: native compound objectives cannot implicitly select soft groups");
        std::vector<MetaObjectivePtr> members;
        std::unordered_set<const MetaObjective*> selected;
        for (size_t i = 0; i < compound->getObjectiveSize(); ++i) {
            const auto& member = compound->getObjective(i);
            condAssert(member && member->isSingleObjective(),
                       "dumpSMT2: nested compound objective is not supported by this dialect adapter");
            members.push_back(member);
            selected.insert(member.get());
        }
        for (size_t i = 0; i + 1 < objectives.size(); ++i) {
            condAssert(selected.count(objectives[i].get()) != 0,
                       "dumpSMT2: independent and compound objectives need an explicit combination");
        }
        switch (compound->getObjectiveKind()) {
        case OPT_KIND::OPT_LEX_OPTIMIZE: combination = H::ObjectiveCombination::LEXICOGRAPHIC; break;
        case OPT_KIND::OPT_PARETO_OPTIMIZE: combination = H::ObjectiveCombination::PARETO; break;
        case OPT_KIND::OPT_BOX_OPTIMIZE: combination = H::ObjectiveCombination::BOX; break;
        case OPT_KIND::OPT_MINMAX: combination = H::ObjectiveCombination::MINMAX; break;
        case OPT_KIND::OPT_MAXMIN: combination = H::ObjectiveCombination::MAXMIN; break;
        default: throw std::runtime_error("dumpSMT2: invalid compound objective");
        }
        objectives = std::move(members);
    }
    const auto text = [](const std::shared_ptr<DAGNode>& term) {
        condAssert(term && !term->isNull(), "dumpSMT2: missing objective term");
        std::ostringstream out;
        dumpSMTLIB2Shared(term, out);
        return out.str();
    };
    std::vector<RenderedObjective> events;
    std::vector<std::string> soft_groups(context_.soft_assertions.size());
    for (const auto& group : context_.soft_assertion_groups) {
        for (const size_t index : group.second) {
            condAssert(index < soft_groups.size(), "dumpSMT2: soft group index out of range");
            soft_groups[index] = group.first;
        }
    }
    std::unordered_set<std::string> explicitly_activated;
    if (!selected_gomt) {
        for (const auto& objective : objectives) {
            if (objective && objective->isMaxSAT()) explicitly_activated.insert(objective->getGroupID());
        }
    }
    const auto append_objective = [&](const MetaObjectivePtr& objective) {
        if (selected_gomt && objective && objective->isMaxSAT()) {
            const auto& soft = getObjectiveManager()->getGomtSoftAssertions(objective->getGroupID());
            for (const auto& constraint : soft) {
                RenderedObjective event;
                event.kind = RenderedObjectiveKind::Soft;
                event.term = text(constraint.node);
                event.weight = softWeightToken(constraint.weight);
                event.group = objective->getGroupID();
                events.push_back(std::move(event));
            }
            if (soft.empty()) {
                RenderedObjective event;
                event.kind = RenderedObjectiveKind::Minimize;
                event.term = "0";
                event.name = objective->getGroupID();
                events.push_back(std::move(event));
            }
            return;
        }
        if (objective && objective->isMaxSAT()) {
            for (size_t i = 0; i < soft_groups.size(); ++i) {
                if (soft_groups[i] != objective->getGroupID()) continue;
                RenderedObjective event;
                event.kind = RenderedObjectiveKind::Soft;
                event.term = text(context_.soft_assertions[i]);
                event.weight = softWeightToken(context_.soft_weights[i]);
                event.group = soft_groups[i];
                events.push_back(std::move(event));
            }
            return;
        }
        condAssert(objective && (objective->isMinimize() || objective->isMaximize()),
                   "dumpSMT2: objective is not an arithmetic minimize/maximize goal");
        const auto& term = objective->getObjectiveTerm();
        condAssert(term && !term->isNull(), "dumpSMT2: missing objective term");
        // Keep the default-order export domain aligned with the GOMT reader.
        if (dialect == Lower::OmtDialect::Gomt) {
            const auto& sort = term->getSort();
            condAssert(sort && (sort->isInt() || sort->isReal() || sort->isBv() || sort->isFp()),
                       "dumpSMT2: GOMT export currently supports only Int/Real/BV/FP objective terms");
        }
        condAssert(objective->getEpsilon() == NodeManager::NULL_NODE
                   && objective->getM() == NodeManager::NULL_NODE,
                   "dumpSMT2: explicit epsilon/M objectives need a generalized order encoding");
        const auto comparison = objective->getCompareOperator();
        condAssert(comparison == getDefaultCompareOperator(getOptions()->logic, objective->getObjectiveKind())
                   || comparison == getCompareOperatorForObjectiveTerm(term, objective->getObjectiveKind()),
                   "dumpSMT2: non-default objective comparison needs an explicit order encoding");
        RenderedObjective event;
        event.kind = objective->isMinimize() ? RenderedObjectiveKind::Minimize
                                            : RenderedObjectiveKind::Maximize;
        event.term = text(term);
        if (selected_gomt) event.name = objective->getGroupID();
        events.push_back(std::move(event));
    };
    size_t next = 0;
    for (size_t i = 0; !selected_gomt && i < context_.soft_assertions.size(); ++i) {
        condAssert(i < context_.soft_objective_positions.size(),
                   "dumpSMT2: soft assertion lacks objective order metadata");
        const size_t position = context_.soft_objective_positions[i];
        condAssert(position >= next && position <= objectives.size(),
                   "dumpSMT2: invalid soft/objective order metadata");
        while (next < position) append_objective(objectives[next++]);
        if (explicitly_activated.count(soft_groups[i])) continue;
        RenderedObjective event;
        event.kind = RenderedObjectiveKind::Soft;
        event.term = text(context_.soft_assertions[i]);
        if (i < context_.soft_weights.size() && context_.soft_weights[i]) {
            // Node names canonicalize 3.5 to 7/2; vendor :weight needs a
            // numeral/decimal token, with no rounding through binary floats.
            event.weight = softWeightToken(context_.soft_weights[i]);
        }
        event.group = soft_groups[i];
        events.push_back(std::move(event));
    }
    while (next < objectives.size()) append_objective(objectives[next++]);
    if (events.size() <= 1 && priority == getOptions()->options.end()
        && combination == H::ObjectiveCombination::LEXICOGRAPHIC) {
        combination = H::ObjectiveCombination::SINGLE;
    }
    // None is a deliberate feasibility abstraction on Translation, not a
    // lossless dump of a parser's optimization state.
    condAssert(dialect != Lower::OmtDialect::None || events.empty(),
               "dumpSMT2: a feasibility-only dialect would discard optimization goals");
    std::vector<std::string> reserved;
    if (dialect == Lower::OmtDialect::SmtLib2025 || dialect == Lower::OmtDialect::OptiMathSAT) {
        for (const auto& var : getVariables()) reserved.push_back(var->getName());
        for (const auto& fun : getFunctions()) reserved.push_back(fun->getName());
    }
    Uir::Diagnostics diagnostics;
    auto result = Lower::emitRenderedObjectives(events, combination, dialect, diagnostics, reserved);
    if (diagnostics.hasErrors()) {
        throw std::runtime_error("dumpSMT2: " + diagnostics.all().front().message);
    }
    return result;
}

} // namespace SOMTParser
