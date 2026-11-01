/* -*- Source -*-
 *
 * An SMT/OMT Parser (Evaluation part)
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include "somtparser/frontend/parser.h"
#include "somtparser/frontend/eval_dispatch.h"
#include <stack>
#include <unordered_map>

namespace SOMTParser{

    namespace {
    using EvalNode = std::shared_ptr<DAGNode>;
    struct EvaluatedNode { EvalNode value; bool changed; };
    struct EvaluationSession {
        const Parser* parser;
        const Model* model;
        std::unordered_map<EvalNode, EvaluatedNode> completed;
    };
    thread_local EvaluationSession* active_evaluation = nullptr;
    struct EvaluationScope {
        EvaluationSession* previous;
        explicit EvaluationScope(EvaluationSession& session) : previous(active_evaluation) {
            active_evaluation = &session;
        }
        ~EvaluationScope() { active_evaluation = previous; }
    };

    // Operator handlers are local rules, not traversal entry points. Dynamic
    // dependencies (function bodies, matches, lets) belong to explicit frames.
    bool evaluatedOperand(const Parser* parser, const EvalNode& node,
                          const std::shared_ptr<Model>& model, EvalNode& result) {
        condAssert(active_evaluation && active_evaluation->parser == parser
                   && active_evaluation->model == model.get(), "evaluation scope mismatch");
        const auto found = active_evaluation->completed.find(node);
        condAssert(found != active_evaluation->completed.end(), "evaluation operand missing from worklist");
        result = found->second.value;
        return found->second.changed;
    }

    std::string sanitizedUfKey(const std::string& value) {
        std::string out;
        for(char c : value) {
            if(c == '(') out += "LP";
            else if(c == ')') out += "RP";
            else if(c == ' ') out += '_';
            else if(c == '|') out += "PIPE";
            else if(c == ':') out += "COLON";
            else if(c == '"') out += "QUOTE";
            else if(c == '\\') out += "BSLASH";
            else out += c;
        }
        return out;
    }
    }


    void not_implemented_warning(const std::string& op){
        std::cerr << "Not implemented warning: " << op << " is not implemented" << std::endl;
    }
    std::shared_ptr<DAGNode> Parser::evaluate(std::shared_ptr<DAGNode> expr, const Model &model){
        std::shared_ptr<DAGNode> result = NodeManager::NULL_NODE;
        std::shared_ptr<Model> model_ptr = std::make_shared<Model>(model);
        try {
            evaluate(expr, model_ptr, result);
        } catch (const std::exception&) {
            return expr;   // evaluation failed; return unevaluated expression
        }
        return result;
    }

    std::shared_ptr<DAGNode> Parser::evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model){
        std::shared_ptr<DAGNode> result = NodeManager::NULL_NODE;
        try {
            evaluate(expr, model, result);
        } catch (const std::exception&) {
            return expr;   // evaluation failed; return unevaluated expression
        }
        return result;
    }
    bool Parser::evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model, std::shared_ptr<DAGNode> &result){
        EvaluationSession session{this, model.get(), {}};
        EvaluationScope scope(session);
        struct Frame {
            EvalNode node;
            size_t next = 0;
            size_t end = 0;
            bool entered = false;
            bool dynamic_ready = false;
            bool arguments_changed = false;
            EvalNode dynamic{};
            std::unordered_set<EvalNode> distinct_constants{};
            std::vector<EvalNode> distinct_datatypes{};
        };
        std::vector<Frame> pending{{expr}};
        std::unordered_set<const DAGNode*> active{expr.get()};
        const auto push = [&](const EvalNode& child) {
            if(session.completed.count(child)) return false;
            condAssert(child && active.insert(child.get()).second,
                       "cyclic or null expression in evaluation");
            pending.push_back({child});
            return true;
        };
        const auto finish = [&](const EvalNode& value, bool changed) {
            const auto node = pending.back().node;
            session.completed.emplace(node, EvaluatedNode{value, changed});
            active.erase(node.get());
            pending.pop_back();
        };
        while(!pending.empty()) {
            auto& frame = pending.back();
            const auto node = frame.node;
            if(!frame.entered) {
                frame.entered = true;
                frame.end = node->getChildrenSize();
                if(model->isEmpty() && !node->isEq() && !node->isDistinct()
                   && !node->isConstructorApp() && !node->isSelectorApp()
                   && !node->isTesterApp() && !node->isMatchApp()
                   && !node->isFuncApplication()) {
                    finish(node, false); continue;
                }
                if(node->isUnknown() || node->isErr()) {
                    finish(NodeManager::NULL_NODE, false); continue;
                }
                if(node->isConst()) { finish(node, false); continue; }
                if(node->isVar()) {
                    auto value = model->get(node);
                    const bool changed = !value->isUnknown();
                    finish(changed ? value : node, changed); continue;
                }
                if(!getEvalDispatcher().has(node->getKind())
                   || node->getKind() == NODE_KIND::NT_STR_SPLIT) {
                    EvalNode value = NodeManager::NULL_NODE;
                    EvalContext ctx(this, model, &value);
                    const bool changed = getEvalDispatcher().dispatch(node, ctx);
                    finish(value, changed); continue;
                }
                if(node->isUFApplication()) {
                    // The symbolic model entry takes precedence over evaluating
                    // arguments, including partial or otherwise undefined ones.
                    std::string key = "uf@@" + node->getName();
                    for(const auto& child : node->getChildren())
                        key += "@@" + sanitizedUfKey(dumpSMTLIB2(child));
                    const auto value = model->get(key);
                    if(value && !value->isUnknown()) { finish(value, true); continue; }
                }
                if(node->isFuncApplication()) {
                    if(node->getChildrenSize() < 1 || !node->getChild(0)
                       || !node->getChild(0)->isFuncDef()) { finish(node, false); continue; }
                    frame.next = 1; // A function declaration is not an operand.
                }
                // Indexed parameters and the fixed rounding modes used by
                // these existing handlers are metadata, not evaluated terms.
                switch(node->getKind()) {
                case NODE_KIND::NT_BV_EXTRACT:
                case NODE_KIND::NT_BV_REPEAT:
                case NODE_KIND::NT_BV_ZERO_EXT:
                case NODE_KIND::NT_BV_SIGN_EXT:
                case NODE_KIND::NT_BV_ROTATE_LEFT:
                case NODE_KIND::NT_BV_ROTATE_RIGHT:
                    frame.end = std::min<size_t>(1, frame.end); break;
                case NODE_KIND::NT_FP_ADD:
                case NODE_KIND::NT_FP_SUB:
                case NODE_KIND::NT_FP_MUL:
                case NODE_KIND::NT_FP_DIV:
                case NODE_KIND::NT_FP_FMA:
                    frame.next = 1; break;
                case NODE_KIND::NT_FP_TO_UBV:
                case NODE_KIND::NT_FP_TO_SBV:
                    frame.next = 1; frame.end = std::min<size_t>(2, frame.end); break;
                case NODE_KIND::NT_FP_TO_FP:
                    if(frame.end == 3 || frame.end == 4) frame.next = frame.end - 1;
                    break;
                case NODE_KIND::NT_FP_TO_FP_UNSIGNED:
                    if(frame.end == 4) frame.next = 3;
                    else frame.end = 0;
                    break;
                default: break;
                }
            }

            const bool implication = node->isImplies() && node->getChildrenSize() > 2;
            const bool let = node->isLet() || node->isLetChain();
            const bool match = node->isMatchApp();
            const bool function = node->isFuncApplication();
            if(match && node->getChildrenSize() < 3) { finish(node, false); continue; }

            // Select only the scrutinee before a match. For ordinary operators
            // preserve source child order and short-circuit AND/OR/distinct.
            const size_t count = let || implication ? 0 : match ? 1 : frame.end;
            bool suspended = false, decided = false;
            while(frame.next < count) {
                const auto child = node->getChild(frame.next);
                if(push(child)) { suspended = true; break; }
                const auto& evaluated = session.completed.at(child);
                const auto& value = evaluated.value;
                frame.arguments_changed |= evaluated.changed;
                ++frame.next;
                if((node->isAnd() && value->isFalse()) || (node->isOr() && value->isTrue())) {
                    finish(value, true); decided = true; break;
                }
                if(node->isDistinct()) {
                    const auto distinct_value = evaluated.changed ? value : child;
                    bool duplicate = false;
                    if(distinct_value->isDtGroundValue()) {
                        for(const auto& prior : frame.distinct_datatypes)
                            if(areDtValuesEqual(distinct_value, prior)) { duplicate = true; break; }
                        frame.distinct_datatypes.push_back(distinct_value);
                    } else if(distinct_value->isConst()) {
                        duplicate = !frame.distinct_constants.insert(distinct_value).second;
                    }
                    if(duplicate) { finish(mkFalse(), true); decided = true; break; }
                }
            }
            if(suspended || decided) continue;

            if(let || implication || match || function) {
                if(!frame.dynamic_ready) {
                    frame.dynamic_ready = true;
                    if(let) {
                        frame.dynamic = expandLet(node);
                    } else if(implication) {
                        std::vector<EvalNode> disjuncts;
                        for(size_t i = 0; i + 1 < node->getChildrenSize(); ++i)
                            disjuncts.push_back(mkNot(node->getChild(i)));
                        disjuncts.push_back(node->getChild(node->getChildrenSize() - 1));
                        frame.dynamic = mkOr(disjuncts);
                    } else if(function) {
                        std::vector<EvalNode> arguments;
                        for(size_t i = 1; i < node->getChildrenSize(); ++i)
                            arguments.push_back(session.completed.at(node->getChild(i)).value);
                        struct ExpandScope {
                            std::shared_ptr<GlobalOptions> options;
                            bool previous;
                            explicit ExpandScope(std::shared_ptr<GlobalOptions> value)
                                : options(value), previous(value->getExpandFunctions()) {
                                options->setExpandFunctions(true);
                            }
                            ~ExpandScope() { options->setExpandFunctions(previous); }
                        } expand_scope(getOptions());
                        frame.dynamic = applyFun(node->getChild(0), arguments);
                        if(!frame.dynamic) { finish(node, frame.arguments_changed); continue; }
                        if(frame.dynamic->isErr()) { finish(frame.dynamic, true); continue; }
                    } else {
                        const auto scrutinee = session.completed.at(node->getChild(0)).value;
                        for(size_t i = 1; i + 1 < node->getChildrenSize(); i += 2) {
                            auto pattern = node->getChild(i);
                            std::unordered_map<std::string, EvalNode> bindings;
                            if(pattern->isConstructorApp()) {
                                if(!scrutinee->isConstructorApp() || scrutinee->getName() != pattern->getName()) continue;
                                for(size_t j = 0; j < pattern->getChildrenSize() && j < scrutinee->getChildrenSize(); ++j)
                                    bindings[pattern->getChild(j)->getName()] = scrutinee->getChild(j);
                            } else {
                                bindings[pattern->getName()] = scrutinee;
                            }
                            frame.dynamic = substitute(node->getChild(i + 1), bindings);
                            break;
                        }
                        if(!frame.dynamic) { finish(node, false); continue; }
                    }
                }
                if(push(frame.dynamic)) continue;
                const auto completed = session.completed.at(frame.dynamic);
                const bool changed = completed.changed || (function && frame.arguments_changed);
                finish(implication && !changed ? node : completed.value, changed);
                continue;
            }
            EvalNode value = NodeManager::NULL_NODE;
            EvalContext ctx(this, model, &value);
            const bool changed = getEvalDispatcher().dispatch(node, ctx);
            finish(value, changed);
        }
        const auto completed = session.completed.at(expr);
        result = completed.value;
        return completed.changed;
    }

    bool Parser::evaluateSimpleOp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result, NODE_KIND op){
        bool changed = false;
        switch(op){
            // unary operations
            case NODE_KIND::NT_NOT:
            case NODE_KIND::NT_NEG:
            case NODE_KIND::NT_ABS:
            case NODE_KIND::NT_SQRT:
            case NODE_KIND::NT_SAFESQRT:
            case NODE_KIND::NT_CEIL:
            case NODE_KIND::NT_FLOOR:
            case NODE_KIND::NT_ROUND:
            case NODE_KIND::NT_EXP:
            case NODE_KIND::NT_POW2:
            case NODE_KIND::NT_LN:
            case NODE_KIND::NT_LG:
            case NODE_KIND::NT_LB:
            case NODE_KIND::NT_SIN:
            case NODE_KIND::NT_COS:
            case NODE_KIND::NT_TAN:
            case NODE_KIND::NT_COT:
            case NODE_KIND::NT_CSC:
            case NODE_KIND::NT_SEC:
            case NODE_KIND::NT_ASIN:
            case NODE_KIND::NT_ACOS:
            case NODE_KIND::NT_ATAN:
            case NODE_KIND::NT_ASEC:
            case NODE_KIND::NT_ACSC:
            case NODE_KIND::NT_ACOT:
            case NODE_KIND::NT_SINH:
            case NODE_KIND::NT_COSH:
            case NODE_KIND::NT_TANH:
            case NODE_KIND::NT_SECH:
            case NODE_KIND::NT_CSCH:
            case NODE_KIND::NT_COTH:
            case NODE_KIND::NT_ASINH:
            case NODE_KIND::NT_ACOSH:
            case NODE_KIND::NT_ATANH:
            case NODE_KIND::NT_ACOTH:
            case NODE_KIND::NT_ASECH:
            case NODE_KIND::NT_ACSCH:
            case NODE_KIND::NT_TO_REAL:
            case NODE_KIND::NT_TO_INT:
            case NODE_KIND::NT_IS_INT:
            case NODE_KIND::NT_IS_DIVISIBLE:
            case NODE_KIND::NT_IS_PRIME:
            case NODE_KIND::NT_IS_EVEN:
            case NODE_KIND::NT_IS_ODD:
            case NODE_KIND::NT_FACT:
            case NODE_KIND::NT_BV_NOT:
            case NODE_KIND::NT_BV_NEG:
            case NODE_KIND::NT_BV_TO_NAT:
            case NODE_KIND::NT_BV_TO_INT:
            case NODE_KIND::NT_STR_LEN:
            case NODE_KIND::NT_STR_TO_LOWER:
            case NODE_KIND::NT_STR_TO_UPPER:
            case NODE_KIND::NT_STR_REV:
            case NODE_KIND::NT_STR_IS_DIGIT:
            case NODE_KIND::NT_STR_FROM_INT:
            case NODE_KIND::NT_STR_TO_INT:
            case NODE_KIND::NT_STR_TO_REG:
            case NODE_KIND::NT_STR_TO_CODE:
            case NODE_KIND::NT_STR_FROM_CODE:
            case NODE_KIND::NT_REG_STAR:
            case NODE_KIND::NT_REG_PLUS:
            case NODE_KIND::NT_REG_OPT:
            case NODE_KIND::NT_REG_COMPLEMENT:
            {
                std::shared_ptr<DAGNode> child = NodeManager::NULL_NODE;
                changed |= evaluatedOperand(this, expr->getChildren()[0], model, child);
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                result = mkOper(expr->getSort(), op, child);
                return true;
            }
            // binary operations
            case NODE_KIND::NT_IMPLIES:
            case NODE_KIND::NT_MOD:
            case NODE_KIND::NT_LOG:
            case NODE_KIND::NT_POW:
            case NODE_KIND::NT_ATAN2:
            case NODE_KIND::NT_LE:
            case NODE_KIND::NT_LT:
            case NODE_KIND::NT_GE:
            case NODE_KIND::NT_GT:
            case NODE_KIND::NT_GCD:
            case NODE_KIND::NT_LCM:
            case NODE_KIND::NT_BV_COMP:
            case NODE_KIND::NT_BV_UREM:
            case NODE_KIND::NT_BV_SREM:
            case NODE_KIND::NT_BV_UMOD:
            case NODE_KIND::NT_BV_SMOD:
            case NODE_KIND::NT_BV_SHL:
            case NODE_KIND::NT_BV_LSHR:
            case NODE_KIND::NT_BV_ASHR:
            case NODE_KIND::NT_BV_ULT:
            case NODE_KIND::NT_BV_ULE:
            case NODE_KIND::NT_BV_UGT:
            case NODE_KIND::NT_BV_UGE:
            case NODE_KIND::NT_BV_SLT:
            case NODE_KIND::NT_BV_SGT:
            case NODE_KIND::NT_BV_SLE:
            case NODE_KIND::NT_BV_SGE:
            case NODE_KIND::NT_NAT_TO_BV:
            case NODE_KIND::NT_INT_TO_BV:
            case NODE_KIND::NT_STR_PREFIXOF:
            case NODE_KIND::NT_STR_SUFFIXOF:
            case NODE_KIND::NT_STR_CONTAINS:
            case NODE_KIND::NT_STR_CHARAT:
            // The string orderings are binary nodes here on purpose: the
            // :chainable n-ary form is expanded to a conjunction of adjacent
            // pairs at parse time (op_parser.cpp, mkStrLt(vector) &c.), so an
            // NT_STR_LT/LE/GT/GE node always has exactly two children.
            case NODE_KIND::NT_STR_LT:
            case NODE_KIND::NT_STR_LE:
            case NODE_KIND::NT_STR_GT:
            case NODE_KIND::NT_STR_GE:
            case NODE_KIND::NT_STR_IN_REG:
            case NODE_KIND::NT_STR_INDEXOF_REG:
            case NODE_KIND::NT_REG_RANGE:
            case NODE_KIND::NT_REG_REPEAT:
            {
                std::shared_ptr<DAGNode> l = NodeManager::NULL_NODE;
                std::shared_ptr<DAGNode> r = NodeManager::NULL_NODE;
                changed |= evaluatedOperand(this, expr->getChildren()[0], model, l);
                changed |= evaluatedOperand(this, expr->getChildren()[1], model, r);
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                result = mkOper(expr->getSort(), op, l, r);
                return true;
            }
            // triple operations
            case NODE_KIND::NT_STR_SUBSTR:
            case NODE_KIND::NT_STR_INDEXOF:
            case NODE_KIND::NT_STR_UPDATE:
            case NODE_KIND::NT_STR_REPLACE:
            case NODE_KIND::NT_STR_REPLACE_ALL:
            case NODE_KIND::NT_STR_REPLACE_REG:
            case NODE_KIND::NT_STR_REPLACE_REG_ALL:
            case NODE_KIND::NT_REG_LOOP:
            {
                bool changed = false;
                std::shared_ptr<DAGNode> l = NodeManager::NULL_NODE;
                std::shared_ptr<DAGNode> r = NodeManager::NULL_NODE;
                std::shared_ptr<DAGNode> s = NodeManager::NULL_NODE;
                changed |= evaluatedOperand(this, expr->getChildren()[0], model, l);
                changed |= evaluatedOperand(this, expr->getChildren()[1], model, r);
                changed |= evaluatedOperand(this, expr->getChildren()[2], model, s);
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                result = mkOper(expr->getSort(), op, {l, r, s});
                return true;
            }
            // simplify using binary operations
            case NODE_KIND::NT_IAND:
            case NODE_KIND::NT_ADD:
            case NODE_KIND::NT_MUL:
            case NODE_KIND::NT_BV_AND:
            case NODE_KIND::NT_BV_OR:
            case NODE_KIND::NT_BV_XOR:
            case NODE_KIND::NT_BV_NAND:
            case NODE_KIND::NT_BV_NOR:
            case NODE_KIND::NT_BV_XNOR:
            case NODE_KIND::NT_BV_ADD:
            case NODE_KIND::NT_BV_MUL:
            case NODE_KIND::NT_MAX:
            case NODE_KIND::NT_MIN:
            {
                changed = false;
                std::vector<std::shared_ptr<DAGNode>> children;
                for(auto child : expr->getChildren()){
                    std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
                    changed |= evaluatedOperand(this, child, model, eval);
                    children.emplace_back(eval);
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                condAssert(!children.empty(), "evaluateSimpleOp: children is empty");
                // compute the sum of the children that are constant
                std::vector<std::shared_ptr<DAGNode>> const_children;
                std::vector<std::shared_ptr<DAGNode>> non_const_children;
                for(auto child : children){
                    if(child->isConst()){
                        const_children.emplace_back(child);
                    }
                    else{
                        non_const_children.emplace_back(child);
                    }
                }
                if(const_children.empty()){
                    if(non_const_children.size() == 1){
                        result = non_const_children[0];
                    }
                    else{
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                }
                else{
                    // compute the and of the constant children
                    result = const_children[0];
                    for(size_t i = 1; i < const_children.size(); ++i){
                        result = mkOper(expr->getSort(), op, result, const_children[i]);
                    }
                    non_const_children.emplace_back(result);
                    if(non_const_children.size() == 1){
                        result = non_const_children[0];
                    }
                    else{
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                }
                return true; 
            }
            // simplify using binary operations but the first child is special
            case NODE_KIND::NT_SUB:
            case NODE_KIND::NT_DIV_REAL:
            case NODE_KIND::NT_BV_SUB:
            case NODE_KIND::NT_BV_UDIV:
            case NODE_KIND::NT_BV_SDIV:
            case NODE_KIND::NT_FP_SUB:
            {
                changed = false;
                std::vector<std::shared_ptr<DAGNode>> children;
                for(auto child : expr->getChildren()){
                    std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
                    changed |= evaluatedOperand(this, child, model, eval);
                    children.emplace_back(eval);
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                condAssert(!children.empty(), "evaluateSimpleOp: children is empty");
                // compute the difference of the children that are constant
                bool first_child_is_const = children[0]->isConst();
                std::vector<std::shared_ptr<DAGNode>> const_children;
                std::vector<std::shared_ptr<DAGNode>> non_const_children;
                for(auto child : children){
                    if(child->isConst()){
                        const_children.emplace_back(child);
                    }
                    else{
                        non_const_children.emplace_back(child);
                    }
                }
                if(const_children.empty()){
                    if(non_const_children.size() == 1){
                        result = non_const_children[0];
                    }
                    else{
                        result = mkOper(expr->getSort(), op, non_const_children);
                    }
                }
                else{
                    if(first_child_is_const){
                        result = const_children[0];
                        for(size_t i = 1; i < const_children.size(); ++i){
                            result = mkOper(expr->getSort(), op, result, const_children[i]);
                        }
                        non_const_children.insert(non_const_children.begin(), result);
                        if(non_const_children.size() == 1){
                            result = non_const_children[0];
                        }
                        else{
                            result = mkOper(expr->getSort(), op, non_const_children);
                        }
                    }
                    else{
                        auto opposite_op = getFlipKind(op);
                        result = const_children[0];
                        for(size_t i = 1; i < const_children.size(); ++i){
                            result = mkOper(expr->getSort(), opposite_op, result, const_children[i]);
                        }
                        non_const_children.emplace_back(result);
                        if(non_const_children.size() == 1){
                            result = non_const_children[0];
                        }
                        else{
                            result = mkOper(expr->getSort(), op, non_const_children);
                        }
                    }
                }
                return true;
            }
            // concat
            case NODE_KIND::NT_BV_CONCAT:
            case NODE_KIND::NT_STR_CONCAT:
            {
                changed = false;
                // sequential evaluation
                std::vector<std::shared_ptr<DAGNode>> children;
                size_t i = 0;
                while(i < expr->getChildren().size()){
                    // concat until the last constant child
                    std::shared_ptr<DAGNode> child = NodeManager::NULL_NODE;
                    changed |= evaluatedOperand(this, expr->getChildren()[i], model, child);
                    if(child->isConst()){
                        // go on until the child is not constant
                        std::shared_ptr<DAGNode> child_ = NodeManager::NULL_NODE;
                        i++; // skip the already-evaluated first constant
                        while(i < expr->getChildren().size()){
                            changed |= evaluatedOperand(this, expr->getChildren()[i], model, child_);
                            if(!child_->isConst()) break;
                            child = mkOper(expr->getSort(), op, child, child_);
                            i++;
                        }
                        if(i == expr->getChildren().size()){
                            // all remaining children are constant
                            children.emplace_back(child);
                            break;
                        }
                        else if(child_->isNull()){
                            // child_ is null -> only child is constant
                            children.emplace_back(child);
                        }
                        else{
                            // child is the constant prefix; child_ is the non-constant child
                            children.emplace_back(child);
                            children.emplace_back(child_);
                        }
                    }
                    else{
                        children.emplace_back(child);
                    }
                    i++;
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                condAssert(changed, "evaluateSimpleOp: changed is false");
                condAssert(!children.empty(), "evaluateSimpleOp: children is empty");
                if(children.size() == 1){
                    result = children.back();
                    return true;
                }
                else{
                    result = mkOper(expr->getSort(), op, children);
                }
                return true;
            }
            // n-ary regex operations (no constant folding, just recurse into children)
            case NODE_KIND::NT_REG_CONCAT:
            case NODE_KIND::NT_REG_UNION:
            case NODE_KIND::NT_REG_INTER:
            case NODE_KIND::NT_REG_DIFF:
            {
                changed = false;
                std::vector<std::shared_ptr<DAGNode>> children;
                for(const auto& child : expr->getChildren()){
                    std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
                    changed |= evaluatedOperand(this, child, model, eval);
                    children.emplace_back(eval);
                }
                if(!changed){
                    result = expr;
                    return false;
                }
                result = mkOper(expr->getSort(), op, children);
                return true;
            }
            default:
                condAssert(false, "evaluateSimpleOp: no implementation for this kind");
                result = expr;
                return false;
        }

        return changed;
    }
    bool Parser::evaluateAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        std::vector<std::shared_ptr<DAGNode>> children;
        bool changed = false;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, child, model, eval);
            if(eval->isConst()){
                if(eval->isFalse()){
                    result = eval;
                    return true; // result has been changed
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        condAssert(changed, "evaluateAnd: changed is false");
        if(children.empty()){
            result = mkTrue();
        }
        else if(children.size() == 1){
            result = children[0];
        }
        else{
            result = mkAnd(children);
        }
        return true;
    }
    bool Parser::evaluateOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        std::vector<std::shared_ptr<DAGNode>> children;
        bool changed = false;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, child, model, eval);
            if(eval->isConst()){
                if(eval->isTrue()){
                    result = eval;
                    return true;
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        condAssert(changed, "evaluateOr: changed is false");
        if(children.empty()){
            result = mkFalse();
        }
        else if(children.size() == 1){
            result = children[0];
        }
        else{
            result = mkOr(children);
        }
        return true;
    }
    bool Parser::evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NOT);
    }
    bool Parser::evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // `=>` is :right-assoc in SMT-LIB, so `(=> a b c)` is `(=> a (=> b c))`,
        // which is the disjunction `(or (not a) (not b) c)`. evaluateSimpleOp
        // classifies NT_IMPLIES as binary and rebuilds it from the first two
        // children only, so every argument past the second was dropped and
        // `(=> a b c)` evaluated as `a => b` -- silently, and to the wrong
        // answer whenever the two differ.
        //
        // Rewriting to the disjunction rather than repairing the binary path
        // reuses the OR evaluator, which already handles a partial model
        // correctly (one false antecedent decides the whole formula without
        // needing the rest).
        const size_t arity = expr->getChildrenSize();
        if (arity <= 2) {
            return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IMPLIES);
        }
        std::vector<std::shared_ptr<DAGNode>> disjuncts;
        disjuncts.reserve(arity);
        for (size_t i = 0; i + 1 < arity; i++) {
            disjuncts.emplace_back(mkNot(expr->getChild(i)));
        }
        disjuncts.emplace_back(expr->getChild(arity - 1));
        std::shared_ptr<DAGNode> rewritten = mkOr(disjuncts);
        std::shared_ptr<DAGNode> evaluated = NodeManager::NULL_NODE;
        const bool changed = evaluatedOperand(this, rewritten, model, evaluated);
        if (!changed) {
            // Report the node the caller handed us, not the rewriting.
            result = expr;
            return false;
        }
        result = evaluated;
        return true;
    }
    bool Parser::evaluateXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        // count true
        size_t trueCount = 0;
        // save unevaluated children
        std::vector<std::shared_ptr<DAGNode>> remainingChildren;
        
        // traverse all children
        for (auto child : expr->getChildren()) {
            std::shared_ptr<DAGNode> evaluatedChild = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, child, model, evaluatedChild);
            
            // evaluated as constant
            if (evaluatedChild->isConst()) {
                if (evaluatedChild->isTrue()) {
                    trueCount++;
                }
                // ignore false
            } else {
                // save unevaluated children
                remainingChildren.emplace_back(evaluatedChild);
            }
        }
        if(!changed){
            result = expr;
            return false;
        }
        condAssert(changed, "evaluateXor: changed is false");
        // all children are constants
        if (remainingChildren.empty()) {
            // result depends on true count is odd or even
            result = (trueCount % 2 == 1) ? mkTrue() : mkFalse();
            return true;
        }
        
        // only one unevaluated child
        if (remainingChildren.size() == 1) {
            // if true count is even, result is the child
            // if true count is odd, result is the negation of the child
            result = (trueCount % 2 == 0) ? 
                remainingChildren[0] : 
                mkNot(remainingChildren[0]);
            return true;
        }
        
        // multiple unevaluated children
        // decide return XOR or its negation based on true count
        result = (trueCount % 2 == 0) ? 
                mkXor(remainingChildren) : 
                mkNot(mkXor(remainingChildren));
        return true;
    }
    bool Parser::evaluateEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        std::vector<std::shared_ptr<DAGNode>> const_vals;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            bool c = evaluatedOperand(this, child, model, eval);
            if(!c) eval = child;
            changed |= c;
            if((eval->isConst() && (!eval->isCFP() || fpNodeToValue(eval))) || eval->isDtGroundValue()){
                const_vals.emplace_back(eval);
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed && const_vals.empty()){
            result = expr;
            return false;
        }
        if(const_vals.empty()){
            result = mkEq(children);
            return true;
        }
        auto const_val = const_vals[0];
        for(size_t i = 1; i < const_vals.size(); ++i){
            if(const_val->isCInt() && const_vals[i]->isCInt()){
                if(toInt(const_val) != toInt(const_vals[i])){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isCReal() && const_vals[i]->isCReal()){
                if(toReal(const_val) != toReal(const_vals[i])){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isCBool() && const_vals[i]->isCBool()){
                if(const_val->isTrue() != const_vals[i]->isTrue()){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isCStr() && const_vals[i]->isCStr()){
                if(const_val->toString() != const_vals[i]->toString()){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isCBV() && const_vals[i]->isCBV()){
                if(const_val->toString() != const_vals[i]->toString()){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isCFP() && const_vals[i]->isCFP()){
                auto va = FloatingPointUtils::fpNodeToValue(const_val);
                auto vb = FloatingPointUtils::fpNodeToValue(const_vals[i]);
                bool differ = false;
                if(va && vb){
                    differ = !FloatingPointUtils::fpValueIdentical(*va, *vb);
                } else{
                    differ = (const_val->toString() != const_vals[i]->toString());
                }
                if(differ){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isArray() && const_vals[i]->isArray()){
                // Use canonical form to check array equality
                if(!areArraysEqual(const_val, const_vals[i])){
                    result = mkFalse();
                    return true;
                }
            }
            else if(const_val->isDtGroundValue() && const_vals[i]->isDtGroundValue()){
                if(!areDtValuesEqual(const_val, const_vals[i])){
                    result = mkFalse();
                    return true;
                }
            }
            else{
                condAssert(false, "evaluateEq: const_val is not a constant");
            }
        }
        if(children.size() == 0){
            result = mkTrue();
            return true;
        }
        else if(children.size() == 1){
            children.emplace_back(const_val);
            result = mkEq(children);
        }
        else{
            if(const_val->isNull()){
                result = mkEq(children);
            }
            else{
                children.emplace_back(const_val);
                result = mkEq(children);
            }
        }
        return true;
    }
    bool Parser::evaluateDistinct(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        std::unordered_set<std::shared_ptr<DAGNode>> const_vals;
        std::vector<std::shared_ptr<DAGNode>> dt_vals;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            bool c = evaluatedOperand(this, child, model, eval);
            if(!c) eval = child;
            changed |= c;
            if(eval->isDtGroundValue()){
                for(auto& prev : dt_vals){
                    if(areDtValuesEqual(eval, prev)){
                        result = mkFalse();
                        return true;
                    }
                }
                dt_vals.push_back(eval);
            }
            else if(eval->isConst() && (!eval->isCFP() || fpNodeToValue(eval))){
                if(const_vals.empty()){
                    const_vals.insert(eval);
                }
                else if(const_vals.find(eval) == const_vals.end()){
                    const_vals.insert(eval);
                }
                else{
                    result = mkFalse();
                    return true;
                }
            }
            else{
                children.emplace_back(eval);
            }
        }
        if(!changed && const_vals.empty() && dt_vals.empty()){
            result = expr;
            return false;
        }
        if(const_vals.empty() && dt_vals.empty()){
            result = mkDistinct(children);
            return true;
        }
        if(children.empty()){
            result = mkTrue();
        }
        else{
            children.insert(children.end(), const_vals.begin(), const_vals.end());
            children.insert(children.end(), dt_vals.begin(), dt_vals.end());
            if(children.size() <= 1){
                result = mkTrue();
            }
            else{
                result = mkDistinct(children);
            }
        }
        return true;
    }
    bool Parser::evaluateIte(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        bool changed = false;
        std::shared_ptr<DAGNode> cond = NodeManager::NULL_NODE;
        std::shared_ptr<DAGNode> then_child = NodeManager::NULL_NODE;
        std::shared_ptr<DAGNode> else_child = NodeManager::NULL_NODE;
        changed |= evaluatedOperand(this, expr->getChild(0), model, cond);
        changed |= evaluatedOperand(this, expr->getChild(1), model, then_child);
        changed |= evaluatedOperand(this, expr->getChild(2), model, else_child);
        if(!changed){
            result = expr;
            return false;
        }
        condAssert(changed, "evaluateIte: changed is false");
        if(cond->isConst()){
            result = cond->isTrue() ? then_child : else_child;
        }
        else{
            result = mkIte(cond, then_child, else_child);
        }
        return true;
    }
    bool Parser::evaluateAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ADD);
    }
    bool Parser::evaluateNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NEG);
    }
    bool Parser::evaluateSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SUB);
    }
    bool Parser::evaluateMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MUL);
    }
    bool Parser::evaluateDivInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> children;
        for(auto child : expr->getChildren()){
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, child, model, eval);
            children.emplace_back(eval);
        }
        if(!changed) {
            result = expr;
            return false;
        }
        condAssert(children.size() >= 2, "evaluateDivInt: missing division operand");
        // Constant grouping or operand reordering changes Euclidean division,
        // especially with negative divisors and partially assigned models.
        result = children[0];
        for(size_t i = 1; i < children.size(); ++i) result = mkDivInt(result, children[i]);
        return true;
    }
    bool Parser::evaluateDivReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_DIV_REAL);
    }   
    bool Parser::evaluateMod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MOD);
    }
    bool Parser::evaluatePow(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_POW);
    }
    bool Parser::evaluatePow2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_POW2);
    }
    bool Parser::evaluateIand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IAND);
    }
    bool Parser::evaluateAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ABS);
    }
    bool Parser::evaluateSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SQRT);
    }
    bool Parser::evaluateSafeSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SAFESQRT);
    }
    bool Parser::evaluateCeil(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_CEIL);
    }
    bool Parser::evaluateFloor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_FLOOR);
    }
    bool Parser::evaluateRound(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ROUND);
    }
    bool Parser::evaluateExp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_EXP);
    }
    bool Parser::evaluateLn(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LN);
    }
    bool Parser::evaluateLg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LG);
    }
    bool Parser::evaluateLog(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LOG);
    }
    bool Parser::evaluateLb(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LB);
    }
    bool Parser::evaluateSin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SIN);
    }
    bool Parser::evaluateCos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COS);
    }
    bool Parser::evaluateTan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TAN);
    }
    bool Parser::evaluateCot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COT);
    }
    bool Parser::evaluateCsc(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_CSC);
    }
    bool Parser::evaluateSec(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SEC);
    }
    
    bool Parser::evaluateAsin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASIN);
    }
    bool Parser::evaluateAcos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOS);
    }
    bool Parser::evaluateAtan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATAN);
    }
    bool Parser::evaluateAsec(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASEC);
    }
    bool Parser::evaluateAcsc(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACSC);
    }
    bool Parser::evaluateAcot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOT);
    }
    
    bool Parser::evaluateSinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SINH);
    }
    bool Parser::evaluateCosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COSH);
    }
    bool Parser::evaluateTanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TANH);
    }
    bool Parser::evaluateSech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_SECH);
    }
    bool Parser::evaluateCsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_CSCH);
    }
    bool Parser::evaluateCoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_COTH);
    }

    bool Parser::evaluateAsinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASINH);
    }
    bool Parser::evaluateAcosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOSH);
    }
    bool Parser::evaluateAtanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATANH);
    }
    bool Parser::evaluateAsech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ASECH);
    }
    bool Parser::evaluateAcsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACSCH);
    }
    bool Parser::evaluateAcoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ACOTH);
    }

    bool Parser::evaluateAtan2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_ATAN2);
    }
    bool Parser::evaluateLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LE);
    }
    bool Parser::evaluateLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LT);
    }
    bool Parser::evaluateGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GE);
    }
    bool Parser::evaluateGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GT);
    }
    bool Parser::evaluateToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TO_REAL);
    }
    bool Parser::evaluateToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_TO_INT);
    }
    bool Parser::evaluateIsInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_INT);
    }
    bool Parser::evaluateIsDivisible(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_DIVISIBLE);
    }
    bool Parser::evaluateIsPrime(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_PRIME);
    }
    bool Parser::evaluateIsEven(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_EVEN);
    }
    bool Parser::evaluateIsOdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_IS_ODD);
    }
    bool Parser::evaluateGcd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_GCD);
    }
    bool Parser::evaluateLcm(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_LCM);
    }
    bool Parser::evaluateFact(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_FACT);
    }
    bool Parser::evaluateBvNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NOT);
    }
    bool Parser::evaluateBvNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NEG);
    }
    bool Parser::evaluateBvAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_AND);
    }
    bool Parser::evaluateBvOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_OR);
    }
    bool Parser::evaluateBvXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_XOR);
    }
    bool Parser::evaluateBvNand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NAND);
    }
    bool Parser::evaluateBvNor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_NOR);
    }
    bool Parser::evaluateBvXnor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_XNOR);
    }
    bool Parser::evaluateBvComp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_COMP);
    }
    bool Parser::evaluateBvAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ADD);
    }
    bool Parser::evaluateBvSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SUB);
    }
    bool Parser::evaluateBvMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_MUL);
    }
    bool Parser::evaluateBvUdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UDIV);
    }
    bool Parser::evaluateBvUrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UREM);
    }
    bool Parser::evaluateBvSdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SDIV);
    }
    bool Parser::evaluateBvSrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SREM);
    }
    bool Parser::evaluateBvSmod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SMOD);
    }
    bool Parser::evaluateBvShl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SHL);
    }
    bool Parser::evaluateBvLshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_LSHR);
    }
    bool Parser::evaluateBvAshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ASHR);
    }
    bool Parser::evaluateBvUlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ULT);
    }
    bool Parser::evaluateBvUle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_ULE);
    }
    bool Parser::evaluateBvUgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UGT);
    }
    bool Parser::evaluateBvUge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_UGE);
    }
    bool Parser::evaluateBvSlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SLT);
    }
    bool Parser::evaluateBvSle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SLE);
    }
    bool Parser::evaluateBvSgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SGT);
    }
    bool Parser::evaluateBvSge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_SGE);
    }
    bool Parser::evaluateBvConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_CONCAT);
    }
    bool Parser::evaluateBvToNat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_TO_NAT);
    }
    bool Parser::evaluateBvNatToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NAT_TO_BV);
    }
    bool Parser::evaluateBvIntToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_BV_TO_INT);
    }
    bool Parser::evaluateBvToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_NAT_TO_BV);
    }
    bool Parser::evaluateBvExtract(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> hi = expr->getChildren()[1];
        std::shared_ptr<DAGNode> lo = expr->getChildren()[2];
        if(bv->isCBV()){
            Integer hi_val = toInt(hi);
            Integer lo_val = toInt(lo);
            size_t width = (hi_val - lo_val + 1).toULong();
            result = mkConstBv(BitVectorUtils::bvExtract(bv->toString(), hi_val, lo_val), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_EXTRACT, bv, hi, lo);
        }
        return true;
    }
    bool Parser::evaluateBvRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> cnt = expr->getChildren()[1];
        if(bv->isCBV() && cnt->isCInt()){
            Integer n = toInt(cnt);
            size_t width = bv->getSort()->getBitWidth() * n.toULong();
            result = mkConstBv(BitVectorUtils::bvRepeat(bv->toString(), n), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_REPEAT, bv, cnt);
        }
        return true;
    }
    bool Parser::evaluateBvZeroExt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> ext = expr->getChildren()[1];
        if(bv->isCBV() && ext->isCInt()){
            Integer n = toInt(ext);
            size_t width = bv->getSort()->getBitWidth() + n.toULong();
            result = mkConstBv(BitVectorUtils::bvZeroExtend(bv->toString(), n), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_ZERO_EXT, bv, ext);
        }
        return true;
    }
    bool Parser::evaluateBvSignExt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> ext = expr->getChildren()[1];
        if(bv->isCBV() && ext->isCInt()){
            Integer n = toInt(ext);
            size_t width = bv->getSort()->getBitWidth() + n.toULong();
            result = mkConstBv(BitVectorUtils::bvSignExtend(bv->toString(), n), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_SIGN_EXT, bv, ext);
        }
        return true;
    }
    bool Parser::evaluateBvRotLeft(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> amt = expr->getChildren()[1];
        if(bv->isCBV() && amt->isCInt()){
            size_t width = bv->getSort()->getBitWidth();
            result = mkConstBv(BitVectorUtils::bvRotateLeft(bv->toString(), toInt(amt)), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_ROTATE_LEFT, bv, amt);
        }
        return true;
    }
    bool Parser::evaluateBvRotRight(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, bv);
        if(!changed){ result = expr; return false; }
        std::shared_ptr<DAGNode> amt = expr->getChildren()[1];
        if(bv->isCBV() && amt->isCInt()){
            size_t width = bv->getSort()->getBitWidth();
            result = mkConstBv(BitVectorUtils::bvRotateRight(bv->toString(), toInt(amt)), width);
        } else {
            result = mkOper(expr->getSort(), NODE_KIND::NT_BV_ROTATE_RIGHT, bv, amt);
        }
        return true;
    }
    bool Parser::evaluateFpAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        auto sort = fp1->getSort();
        if(fp1->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto v = fpNodeToValue(fp1);
            if(v){ result = mkConstFp(v->abs().toSMTFP(), e, s); return true; }
        }
        result = mkOper(fp1->getSort(), NODE_KIND::NT_FP_ABS, fp1);
        return true;
    }
    bool Parser::evaluateFpNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        auto sort = fp1->getSort();
        if(fp1->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto v = fpNodeToValue(fp1);
            if(v){ result = mkConstFp(v->neg().toSMTFP(), e, s); return true; }
        }
        result = mkOper(fp1->getSort(), NODE_KIND::NT_FP_NEG, fp1);
        return true;
    }
    bool Parser::evaluateFpAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren(); // [rm, fp1, fp2]
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE, fp2 = NodeManager::NULL_NODE;
        bool c1 = evaluatedOperand(this, ch[1], model, fp1), c2 = evaluatedOperand(this, ch[2], model, fp2);
        if(!c1) fp1 = ch[1];
        if(!c2) fp2 = ch[2];
        auto rm = ch[0]; auto rnd = getFPRoundingModeMpfr(rm);
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpBinaryOp(*va, *vb, e, s, rnd, mpfr_add);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_ADD, {rm, fp1, fp2});
        return true;
    }
    bool Parser::evaluateFpSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren(); // [rm, fp1, fp2]
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE, fp2 = NodeManager::NULL_NODE;
        bool c1 = evaluatedOperand(this, ch[1], model, fp1), c2 = evaluatedOperand(this, ch[2], model, fp2);
        if(!c1) fp1 = ch[1];
        if(!c2) fp2 = ch[2];
        auto rm = ch[0]; auto rnd = getFPRoundingModeMpfr(rm);
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpBinaryOp(*va, *vb, e, s, rnd, mpfr_sub);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_SUB, {rm, fp1, fp2});
        return true;
    }
    bool Parser::evaluateFpMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren(); // [rm, fp1, fp2]
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE, fp2 = NodeManager::NULL_NODE;
        bool c1 = evaluatedOperand(this, ch[1], model, fp1), c2 = evaluatedOperand(this, ch[2], model, fp2);
        if(!c1) fp1 = ch[1];
        if(!c2) fp2 = ch[2];
        auto rm = ch[0]; auto rnd = getFPRoundingModeMpfr(rm);
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpBinaryOp(*va, *vb, e, s, rnd, mpfr_mul);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_MUL, {rm, fp1, fp2});
        return true;
    }
    bool Parser::evaluateFpDiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren(); // [rm, fp1, fp2]
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE, fp2 = NodeManager::NULL_NODE;
        bool c1 = evaluatedOperand(this, ch[1], model, fp1), c2 = evaluatedOperand(this, ch[2], model, fp2);
        if(!c1) fp1 = ch[1];
        if(!c2) fp2 = ch[2];
        auto rm = ch[0]; auto rnd = getFPRoundingModeMpfr(rm);
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpBinaryOp(*va, *vb, e, s, rnd, mpfr_div);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_DIV, {rm, fp1, fp2});
        return true;
    }
    bool Parser::evaluateFpFma(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren(); // [rm, fp1, fp2, fp3]
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE, fp3=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, ch[1],model,fp1), c2=evaluatedOperand(this, ch[2],model,fp2), c3=evaluatedOperand(this, ch[3],model,fp3);
        if(!c1) fp1 = ch[1];
        if(!c2) fp2 = ch[2];
        if(!c3) fp3 = ch[3];
        auto rm = ch[0]; auto rnd = getFPRoundingModeMpfr(rm);
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && fp3->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2); auto vc = fpNodeToValue(fp3);
            if(va && vb && vc){
                auto r = FloatingPointUtils::fpTernaryOp(*va, *vb, *vc, e, s, rnd, mpfr_fma);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_FMA, {rm, fp1, fp2, fp3});
        return true;
    }
    bool Parser::evaluateFpSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren();
        std::shared_ptr<DAGNode> rmOut;
        std::shared_ptr<DAGNode> fpIn;
        bool rmChanged = false;
        if(ch.size() == 2 && ch[0]->getSort()->isRoundingMode()) {
            rmOut = NodeManager::NULL_NODE;
            rmChanged = evaluatedOperand(this, ch[0], model, rmOut);
            if(!rmChanged) rmOut = ch[0];
            fpIn = ch[1];
        } else if(ch.size() == 1) {
            rmOut = mkRoundingMode("RNE");
            fpIn = ch[0];
        } else {
            result = expr;
            return false;
        }
        mpfr_rnd_t rnd = MPFR_RNDN;
        if(rmOut->isCRoundingMode()) {
            rnd = getFPRoundingModeMpfr(rmOut);
        }
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool fpChanged = evaluatedOperand(this, fpIn, model, fp1);
        if(!fpChanged) fp1 = fpIn;
        auto sort = fp1->getSort();
        if(fp1->isCFP() && sort && rmOut->isCRoundingMode()){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto v = fpNodeToValue(fp1);
            if(v){
                auto r = FloatingPointUtils::fpUnaryOp(*v, e, s, rnd, mpfr_sqrt);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_SQRT, {rmOut, fp1});
        const bool upgradedLegacyUnary = (ch.size() == 1);
        return rmChanged || fpChanged || upgradedLegacyUnary;
    }
    bool Parser::evaluateFpRem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpRemainder(*va, *vb, e, s);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_REM, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpRoundToIntegral(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren();
        std::shared_ptr<DAGNode> rmOut;
        std::shared_ptr<DAGNode> fpIn;
        bool rmChanged = false;
        if(ch.size() == 2 && ch[0]->getSort()->isRoundingMode()) {
            rmOut = NodeManager::NULL_NODE;
            rmChanged = evaluatedOperand(this, ch[0], model, rmOut);
            if(!rmChanged) rmOut = ch[0];
            fpIn = ch[1];
        } else if(ch.size() == 1) {
            rmOut = mkRoundingMode("RNE");
            fpIn = ch[0];
        } else {
            result = expr;
            return false;
        }
        mpfr_rnd_t rnd = MPFR_RNDN;
        if(rmOut->isCRoundingMode()) {
            rnd = getFPRoundingModeMpfr(rmOut);
        }
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool fpChanged = evaluatedOperand(this, fpIn, model, fp1);
        if(!fpChanged) fp1 = fpIn;
        auto sort = fp1->getSort();
        if(fp1->isCFP() && sort && rmOut->isCRoundingMode()){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto v = fpNodeToValue(fp1);
            if(v){
                auto r = FloatingPointUtils::fpRoundToIntegral(*v, e, s, rnd);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_ROUND_TO_INTEGRAL, {rmOut, fp1});
        const bool upgradedLegacyUnary = (ch.size() == 1);
        return rmChanged || fpChanged || upgradedLegacyUnary;
    }
    bool Parser::evaluateFpMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpMin(*va, *vb);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_MIN, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        auto sort = fp1->getSort();
        if(fp1->isCFP() && fp2->isCFP() && sort){
            size_t e = sort->getExponentWidth(), s = sort->getSignificandWidth();
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                auto r = FloatingPointUtils::fpMax(*va, *vb);
                if(r){ result = mkConstFp(r->toSMTFP(), e, s); return true; }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_MAX, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        if(fp1->isCFP() && fp2->isCFP()){
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                int cmp = FloatingPointUtils::fpCompare(*va, *vb);
                result = (cmp != 2 && cmp <= 0) ? mkTrue() : mkFalse(); return true;
            }
        }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_LE, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        if(fp1->isCFP() && fp2->isCFP()){
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                int cmp = FloatingPointUtils::fpCompare(*va, *vb);
                result = (cmp == -1) ? mkTrue() : mkFalse(); return true;
            }
        }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_LT, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        if(fp1->isCFP() && fp2->isCFP()){
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                int cmp = FloatingPointUtils::fpCompare(*va, *vb);
                result = (cmp == 0 || cmp == 1) ? mkTrue() : mkFalse(); return true;
            }
        }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_GE, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        if(fp1->isCFP() && fp2->isCFP()){
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                int cmp = FloatingPointUtils::fpCompare(*va, *vb);
                result = (cmp == 1) ? mkTrue() : mkFalse(); return true;
            }
        }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_GT, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1=NodeManager::NULL_NODE, fp2=NodeManager::NULL_NODE;
        bool c1=evaluatedOperand(this, expr->getChildren()[0],model,fp1), c2=evaluatedOperand(this, expr->getChildren()[1],model,fp2);
        if(!c1) fp1 = expr->getChildren()[0];
        if(!c2) fp2 = expr->getChildren()[1];
        if(fp1->isCFP() && fp2->isCFP()){
            auto va = fpNodeToValue(fp1); auto vb = fpNodeToValue(fp2);
            if(va && vb){
                int cmp = FloatingPointUtils::fpCompare(*va, *vb);
                result = (cmp == 0) ? mkTrue() : mkFalse(); return true;
            }
        }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_EQ, fp1, fp2);
        return true;
    }
    bool Parser::evaluateFpToUbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        // fp.to_ubv: children = [rm, fp], target BV width from expr sort
        auto ch = expr->getChildren();
        if(ch.size() < 2){ result = expr; return false; }
        auto rm = ch[0];
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, ch[1], model, fp1);
        if(!changed) fp1 = ch[1];
        if(fp1->isCFP()){
            auto sort = expr->getSort();
            if(!sort){ result = expr; return false; }
            size_t bv_width = sort->getBitWidth();
            auto v = fpNodeToValue(fp1);
            if(v){
                auto rnd = getFPRoundingModeMpfr(rm);
                auto bvStr = FloatingPointUtils::fpValueToUbv(*v, bv_width, rnd);
                if(bvStr){
                    result = mkConstBv(*bvStr, bv_width);
                    return true;
                }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_TO_UBV, {rm, fp1});
        return true;
    }
    bool Parser::evaluateFpToSbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        // fp.to_sbv: children = [rm, fp], target BV width from expr sort
        auto ch = expr->getChildren();
        if(ch.size() < 2){ result = expr; return false; }
        auto rm = ch[0];
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, ch[1], model, fp1);
        if(!changed) fp1 = ch[1];
        if(fp1->isCFP()){
            auto sort = expr->getSort();
            if(!sort){ result = expr; return false; }
            size_t bv_width = sort->getBitWidth();
            auto v = fpNodeToValue(fp1);
            if(v){
                auto rnd = getFPRoundingModeMpfr(rm);
                auto bvStr = FloatingPointUtils::fpValueToSbv(*v, bv_width, rnd);
                if(bvStr){
                    result = mkConstBv(*bvStr, bv_width);
                    return true;
                }
            }
        }
        result = mkOper(expr->getSort(), NODE_KIND::NT_FP_TO_SBV, {rm, fp1});
        return true;
    }
    bool Parser::evaluateFpToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP()){
            auto v = fpNodeToValue(fp1);
            if(v){
                auto d = FloatingPointUtils::fpToDouble(*v);
                if(d){
                    result = mkConstReal(Number::fromApproxDouble(*d));
                    return true;
                }
            }
        }
        result = mkOper(SortManager::REAL_SORT, NODE_KIND::NT_FP_TO_REAL, fp1);
        return true;
    }
    bool Parser::evaluateToFp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren();
        auto sort = expr->getSort();
        if(!sort){ result = expr; return false; }
        size_t target_eb = sort->getExponentWidth();
        size_t target_sb = sort->getSignificandWidth();

        if(ch.size() == 3) {
            // Case: ((_ to_fp eb sb) BitVec) — bit reinterpretation, children = [eb, sb, bv]
            std::shared_ptr<DAGNode> bv = NodeManager::NULL_NODE;
            bool changed = evaluatedOperand(this, ch[2], model, bv);
            if(!changed) bv = ch[2];
            if(bv->isCBV()) {
                auto fv = FloatingPointUtils::bvBitsToFpValue(bv->getName(), target_eb, target_sb);
                if(fv) {
                    result = mkConstFp(fv->toSMTFP(), target_eb, target_sb);
                    return true;
                }
            }
            result = mkOper(sort, NODE_KIND::NT_FP_TO_FP, ch[0], ch[1], bv);
            return true;
        } else if(ch.size() == 4) {
            // Children = [eb, sb, rm, param]
            auto rm = ch[2];
            std::shared_ptr<DAGNode> param = NodeManager::NULL_NODE;
            bool changed = evaluatedOperand(this, ch[3], model, param);
            if(!changed) param = ch[3];
            auto rnd = getFPRoundingModeMpfr(rm);

            if(param->isCFP()) {
                // Bit extraction alone does not implement format conversion
                // rounding. Only the same-format identity is safe to fold.
                if(param->getSort()->getExponentWidth() == target_eb
                    && param->getSort()->getSignificandWidth() == target_sb) {
                    result = param;
                    return true;
                }
            } else if(param->isCReal() || param->isCInt()) {
                // Case: Real/Integer → FP
                ensureNumberValue(param);
                auto val = param->getValue();
                if(val) {
                    auto num = val->getNumberValue();
                    auto fv = FloatingPointUtils::realToFpValue(num, target_eb, target_sb, rnd);
                    if(fv) {
                        result = mkConstFp(fv->toSMTFP(), target_eb, target_sb);
                        return true;
                    }
                }
            } else if(param->isCBV()) {
                // Case: Signed BV integer → FP (signed interpretation)
                size_t bv_width = param->getSort()->getBitWidth();
                uint64_t bv_val = FloatingPointUtils::parseBVBits(param->getName());
                auto fv = FloatingPointUtils::bvToFpValueSigned(bv_val, bv_width, target_eb, target_sb, rnd);
                if(fv) {
                    result = mkConstFp(fv->toSMTFP(), target_eb, target_sb);
                    return true;
                }
            }
            // Fallback: rebuild symbolic
            result = mkOper(sort, NODE_KIND::NT_FP_TO_FP, {ch[0], ch[1], rm, param});
            return true;
        }
        // Unknown arity — evaluate children and rebuild
        bool changed = false;
        std::vector<std::shared_ptr<DAGNode>> evaled;
        for(auto& child : ch){
            std::shared_ptr<DAGNode> ev = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, child, model, ev);
            evaled.push_back(ev);
        }
        if(!changed){ result = expr; return false; }
        result = mkOper(sort, NODE_KIND::NT_FP_TO_FP, evaled);
        return true;
    }
    bool Parser::evaluateToFpUnsigned(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m))
        // Children: [eb, sb, rm, bv_param]
        auto ch = expr->getChildren();
        if(ch.size() != 4){ result = expr; return false; }
        auto sort = expr->getSort();
        if(!sort){ result = expr; return false; }
        size_t target_eb = sort->getExponentWidth();
        size_t target_sb = sort->getSignificandWidth();
        auto rm = ch[2];
        std::shared_ptr<DAGNode> param = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, ch[3], model, param);
        if(!changed) param = ch[3];
        if(param->isCBV()) {
            auto rnd = getFPRoundingModeMpfr(rm);
            size_t bv_width = param->getSort()->getBitWidth();
            uint64_t bv_val = FloatingPointUtils::parseBVBits(param->getName());
            auto fv = FloatingPointUtils::bvToFpValueUnsigned(bv_val, bv_width, target_eb, target_sb, rnd);
            if(fv) {
                result = mkConstFp(fv->toSMTFP(), target_eb, target_sb);
                return true;
            }
        }
        result = mkOper(sort, NODE_KIND::NT_FP_TO_FP_UNSIGNED, {ch[0], ch[1], rm, param});
        return true;
    }
    bool Parser::evaluateFpIsNormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsNormal(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NORMAL, fp1);
        return true;
    }
    bool Parser::evaluateFpIsSubnormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsSubnormal(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_SUBNORMAL, fp1);
        return true;
    }
    bool Parser::evaluateFpIsZero(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsZero(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_ZERO, fp1);
        return true;
    }
    bool Parser::evaluateFpIsInf(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsInf(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_INF, fp1);
        return true;
    }
    bool Parser::evaluateFpIsNaN(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsNaN(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NAN, fp1);
        return true;
    }
    bool Parser::evaluateFpIsNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = fpNodeIsNeg(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_NEG, fp1);
        return true;
    }
    bool Parser::evaluateFpIsPos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        std::shared_ptr<DAGNode> fp1 = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChildren()[0], model, fp1);
        if(!changed) fp1 = expr->getChildren()[0];
        if(fp1->isCFP() && fpNodeToValue(fp1)){ result = !fpNodeIsNaN(fp1) && !fpNodeIsNeg(fp1) ? mkTrue() : mkFalse(); return true; }
        result = mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FP_IS_POS, fp1);
        return true;
    }
    bool Parser::evaluateConstArray(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        auto ch = expr->getChildren();
        if(ch.empty()){ result = expr; return false; }
        std::shared_ptr<DAGNode> val = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, ch[0], model, val);
        if(!changed){ result = expr; return false; }
        result = getNodeManager()->createNode(expr->getSort(), NODE_KIND::NT_CONST_ARRAY, "const_array", {val});
        return true;
    }
    bool Parser::evaluateSelect(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        // Evaluate array and index first (this will handle variable substitution)
        std::shared_ptr<DAGNode> array = expr->getSelectArray();
        std::shared_ptr<DAGNode> index = expr->getSelectIndex();
        
        std::shared_ptr<DAGNode> eval_array;
        std::shared_ptr<DAGNode> eval_index;
        bool array_changed = evaluatedOperand(this, array, model, eval_array);
        bool index_changed = evaluatedOperand(this, index, model, eval_index);
        
        // Apply array simplification to the evaluated select
        if (array_changed || index_changed) {
            // Use mkOper directly to create select, then simplify
            auto elem_sort = eval_array->getSort() ? eval_array->getSort()->getElemSort() : nullptr;
            if (!elem_sort) { result = expr; return false; }
            std::shared_ptr<DAGNode> new_select = mkOper(elem_sort, NODE_KIND::NT_SELECT, eval_array, eval_index);
            std::shared_ptr<DAGNode> simplified = simplifyArray(new_select);
            if(simplified->isSelect()){
                // simplifyArray couldn't fully resolve; try model fallback
                auto sel_arr = simplified->getSelectArray();
                auto sel_idx = simplified->getSelectIndex();
                if(sel_arr->isVar() && model){
                    auto mv = model->getArraySelect(sel_arr->getName(), dumpSMTLIB2(sel_idx));
                    if(mv && !mv->isUnknown()){ result = mv; return true; }
                }
            }
            result = simplified;
            return true;
        }
        
        // If nothing changed, try to simplify the original select
        std::shared_ptr<DAGNode> simplified = simplifyArray(expr);
        if (simplified != expr) {
            if(simplified->isSelect()){
                auto sel_arr = simplified->getSelectArray();
                auto sel_idx = simplified->getSelectIndex();
                if(sel_arr->isVar() && model){
                    auto mv = model->getArraySelect(sel_arr->getName(), dumpSMTLIB2(sel_idx));
                    if(mv && !mv->isUnknown()){ result = mv; return true; }
                }
            }
            result = simplified;
            return true;
        }
        
        // Last resort: try model lookup on the original expression
        if(model && array->isVar()){
            auto mv = model->getArraySelect(array->getName(), dumpSMTLIB2(index));
            if(mv && !mv->isUnknown()){ result = mv; return true; }
        }

        result = expr;
        return false;
    }
    bool Parser::evaluateStore(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        // Evaluate array, index, and value first (this will handle variable substitution)
        std::shared_ptr<DAGNode> array = expr->getStoreArray();
        std::shared_ptr<DAGNode> index = expr->getStoreIndex();
        std::shared_ptr<DAGNode> value = expr->getStoreValue();
        
        std::shared_ptr<DAGNode> eval_array;
        std::shared_ptr<DAGNode> eval_index;
        std::shared_ptr<DAGNode> eval_value;
        bool array_changed = evaluatedOperand(this, array, model, eval_array);
        bool index_changed = evaluatedOperand(this, index, model, eval_index);
        bool value_changed = evaluatedOperand(this, value, model, eval_value);
        
        // Apply array simplification to the evaluated store
        if (array_changed || index_changed || value_changed) {
            // Use mkOper directly to create store, then simplify
            std::shared_ptr<DAGNode> new_store = mkOper(eval_array->getSort(), NODE_KIND::NT_STORE, eval_array, eval_index, eval_value);
            std::shared_ptr<DAGNode> simplified = simplifyArray(new_store);
            result = simplified;
            return true;
        }
        
        // If nothing changed, try to simplify the original store
        std::shared_ptr<DAGNode> simplified = simplifyArray(expr);
        if (simplified != expr) {
            result = simplified;
            return true;
        }
        
        result = expr;
        return false;
    }
    bool Parser::evaluateStrLen(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LEN);
    }
    bool Parser::evaluateStrConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CONCAT);
    }
    bool Parser::evaluateStrSubstr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SUBSTR);
    }
    bool Parser::evaluateStrPrefixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_PREFIXOF);
    }
    bool Parser::evaluateStrSuffixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SUFFIXOF);
    }
    bool Parser::evaluateStrIndexof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_INDEXOF);
    }
    bool Parser::evaluateStrCharat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CHARAT);
    }
    bool Parser::evaluateStrUpdate(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_UPDATE);
    }
    bool Parser::evaluateStrReplace(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REPLACE);
    }
    bool Parser::evaluateStrReplaceAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REPLACE_ALL);
    }
    bool Parser::evaluateStrToLower(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_LOWER);
    }
    bool Parser::evaluateStrToUpper(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_UPPER);
    }
    bool Parser::evaluateStrRev(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_REV);
    }
    bool Parser::evaluateStrSplit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        (void)model;
        not_implemented_warning("str.split");
        result = expr;
        return false;
    }
    bool Parser::evaluateStrSplitRest(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SPLIT_REST);
    }
    bool Parser::evaluateStrLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LT);
    }   
    bool Parser::evaluateStrLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_LE);
    }
    bool Parser::evaluateStrGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_GT);
    }
    bool Parser::evaluateStrGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_GE);
    }
    bool Parser::evaluateStrInReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_IN_REG);
    }
    bool Parser::evaluateStrContains(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_CONTAINS);
    }
    bool Parser::evaluateStrIsDigit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_IS_DIGIT);
    }
    bool Parser::evaluateStrFromInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_FROM_INT);
    }
    bool Parser::evaluateStrToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_INT);
    }
    bool Parser::evaluateStrToReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_REG);
    }
    bool Parser::evaluateStrToCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_TO_CODE);
    }
    bool Parser::evaluateStrFromCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_FROM_CODE);
    }
    bool Parser::evaluateRegConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_CONCAT);
    }
    bool Parser::evaluateRegUnion(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_UNION);
    }
    bool Parser::evaluateRegInter(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_INTER);
    }
    bool Parser::evaluateRegDiff(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_DIFF);
    }
    bool Parser::evaluateRegStar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_STAR);
    }
    bool Parser::evaluateRegPlus(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_PLUS);
    }
    bool Parser::evaluateRegOpt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_OPT);
    }
    bool Parser::evaluateRegRange(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_RANGE);
    }
    bool Parser::evaluateRegRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_REPEAT);
    }
    bool Parser::evaluateRegComplement(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_REG_COMPLEMENT);
    }
    bool Parser::evaluateApplyFun(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        if(!expr || expr->getChildrenSize() < 1){
            result = expr;
            return false;
        }
        auto fun = expr->getChild(0);
        if(!fun || !fun->isFuncDef()){
            result = expr;
            return false;
        }
        std::vector<std::shared_ptr<DAGNode>> evaled_args;
        evaled_args.reserve(expr->getChildrenSize() - 1);
        bool args_changed = false;
        for(size_t i = 1; i < expr->getChildrenSize(); ++i){
            std::shared_ptr<DAGNode> ev = NodeManager::NULL_NODE;
            args_changed |= evaluatedOperand(this, expr->getChild(i), model, ev);
            evaled_args.push_back(ev);
        }
        bool old_expand = getOptions()->getExpandFunctions();
        getOptions()->setExpandFunctions(true);
        std::shared_ptr<DAGNode> expanded = applyFun(fun, evaled_args);
        getOptions()->setExpandFunctions(old_expand);
        if(!expanded){
            result = expr;
            return args_changed;
        }
        if(expanded->isErr()){
            result = expanded;
            return true;
        }
        bool body_ev = evaluatedOperand(this, expanded, model, result);
        return args_changed || body_ev;
    }
    bool Parser::evaluateUFApply(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // Strategy: try symbolic key first (matches collect_uf_apps convention),
        // then try evaluated key (for when arguments resolve to constants).

        // 1. Try symbolic key (from original unevaluated expression children)
        std::string sym_key = "uf@@" + expr->getName();
        for (size_t i = 0; i < expr->getChildrenSize(); i++) {
            sym_key += "@@" + sanitizedUfKey(dumpSMTLIB2(expr->getChild(i)));
        }
        auto val = model->get(sym_key);
        if (val && !val->isUnknown()) {
            result = val;
            return true;
        }

        // 2. Evaluate all children (arguments)
        std::vector<std::shared_ptr<DAGNode>> eval_args;
        bool children_changed = false;
        for (size_t i = 0; i < expr->getChildrenSize(); i++) {
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            children_changed |= evaluatedOperand(this, expr->getChild(i), model, eval);
            eval_args.push_back(eval);
        }

        // 3. Try evaluated key (from resolved argument values)
        std::string eval_key = "uf@@" + expr->getName();
        for (const auto& a : eval_args) {
            eval_key += "@@";
            if (a->isConst() || a->isTrue() || a->isFalse()) {
                eval_key += sanitizedUfKey(a->getName());
            } else {
                eval_key += sanitizedUfKey(dumpSMTLIB2(a));
            }
        }
        if (eval_key != sym_key) {
            val = model->get(eval_key);
            if (val && !val->isUnknown()) {
                result = val;
                return true;
            }
        }

        // If children changed, create new UF application with evaluated children
        if (children_changed) {
            result = getNodeManager()->createNode(expr->getSort(), NODE_KIND::NT_UF_APPLY, expr->getName(), eval_args);
            return true;
        }

        result = expr;
        return false;
    }

    // ─── Datatype evaluation ────────────────────────────────────────────────

    bool Parser::areDtValuesEqual(const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b) {
        if(!a->isDtGroundValue() || !b->isDtGroundValue()) return false;
        std::vector<std::pair<EvalNode, EvalNode>> pending{{a, b}};
        std::unordered_map<const DAGNode*, std::unordered_set<const DAGNode*>> seen;
        while(!pending.empty()) {
            auto pair = std::move(pending.back()); pending.pop_back();
            if(!seen[pair.first.get()].insert(pair.second.get()).second) continue;
            if(pair.first->isConstructorApp() && pair.second->isConstructorApp()) {
                if(pair.first->getName() != pair.second->getName()
                   || pair.first->getChildrenSize() != pair.second->getChildrenSize()) return false;
                for(size_t i = 0; i < pair.first->getChildrenSize(); ++i)
                    pending.emplace_back(pair.first->getChild(i), pair.second->getChild(i));
            } else if(pair.first->isConst() && pair.second->isConst()) {
                if(pair.first->toString() != pair.second->toString()) return false;
            } else return false;
        }
        return true;
    }

    bool Parser::evaluateDtConstructor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // Evaluate all children (constructor arguments)
        std::vector<std::shared_ptr<DAGNode>> eval_args;
        bool changed = false;
        for(size_t i = 0; i < expr->getChildrenSize(); i++) {
            std::shared_ptr<DAGNode> eval = NodeManager::NULL_NODE;
            changed |= evaluatedOperand(this, expr->getChild(i), model, eval);
            eval_args.push_back(eval);
        }
        if(changed) {
            result = getNodeManager()->createNode(expr->getSort(), NODE_KIND::NT_DT_CONSTRUCTOR, expr->getName(), eval_args);
            return true;
        }
        result = expr;
        return false;
    }

    bool Parser::evaluateDtSelector(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // A selector takes one argument: the DT value
        if(expr->getChildrenSize() != 1) { result = expr; return false; }
        std::shared_ptr<DAGNode> dt_val = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChild(0), model, dt_val);

        // If the DT value is a constructor application, extract the appropriate field
        if(dt_val->isConstructorApp()) {
            auto dt_sort = dt_val->getSort();
            if(dt_sort && dt_sort->hasDtConstructors()) {
                const auto* ctor = dt_sort->getDtConstructorByName(dt_val->getName());
                if(ctor) {
                    const std::string& sel_name = expr->getName();
                    for(size_t i = 0; i < ctor->selectors.size(); i++) {
                        if(ctor->selectors[i].name == sel_name && i < dt_val->getChildrenSize()) {
                            result = dt_val->getChild(i);
                            return true;
                        }
                    }
                }
            }
        }

        if(changed) {
            result = getNodeManager()->createNode(expr->getSort(), NODE_KIND::NT_DT_SELECTOR, expr->getName(), {dt_val});
            return true;
        }
        result = expr;
        return false;
    }

    bool Parser::evaluateDtTester(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // A tester (is-<ctor>) takes one argument: the DT value
        if(expr->getChildrenSize() != 1) { result = expr; return false; }
        std::shared_ptr<DAGNode> dt_val = NodeManager::NULL_NODE;
        bool changed = evaluatedOperand(this, expr->getChild(0), model, dt_val);

        // If the DT value is a constructor application, check if constructor matches
        if(dt_val->isConstructorApp()) {
            const std::string& tester_name = expr->getName();
            // tester_name is "is-<ctor_name>"
            if(tester_name.size() > 3 && tester_name.rfind("is-", 0) == 0) {
                std::string expected_ctor = tester_name.substr(3);
                if(dt_val->getName() == expected_ctor) {
                    result = mkTrue();
                } else {
                    result = mkFalse();
                }
                return true;
            }
        }

        if(changed) {
            result = getNodeManager()->createNode(expr->getSort(), NODE_KIND::NT_DT_TESTER, expr->getName(), {dt_val});
            return true;
        }
        result = expr;
        return false;
    }

    bool Parser::evaluateMatch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result) {
        // NT_DT_MATCH: child(0) = scrutinee, then pairs (pattern, body)
        if(expr->getChildrenSize() < 3) { result = expr; return false; }

        // Evaluate the scrutinee
        std::shared_ptr<DAGNode> scrutinee = NodeManager::NULL_NODE;
        evaluatedOperand(this, expr->getChild(0), model, scrutinee);

        // Try each case (children[1]=pattern1, children[2]=body1, ...)
        for(size_t i = 1; i + 1 < expr->getChildrenSize(); i += 2) {
            auto pattern = expr->getChild(i);
            auto body = expr->getChild(i + 1);

            if(pattern->isConstructorApp()) {
                // Constructor pattern: check if scrutinee matches this constructor
                if(scrutinee->isConstructorApp() && scrutinee->getName() == pattern->getName()) {
                    // Bind pattern variables to scrutinee's fields via substitution
                    std::unordered_map<std::string, std::shared_ptr<DAGNode>> subst;
                    for(size_t j = 0; j < pattern->getChildrenSize() && j < scrutinee->getChildrenSize(); j++) {
                        subst[pattern->getChild(j)->getName()] = scrutinee->getChild(j);
                    }
                    auto expanded = substitute(body, subst);
                    return evaluatedOperand(this, expanded, model, result);
                }
            } else {
                // Catch-all variable pattern: bind the variable to the scrutinee
                std::unordered_map<std::string, std::shared_ptr<DAGNode>> subst;
                subst[pattern->getName()] = scrutinee;
                auto expanded = substitute(body, subst);
                return evaluatedOperand(this, expanded, model, result);
            }
        }

        // No case matched, return scrutinee (shouldn't happen with well-formed match)
        result = expr;
        return false;
    }

    bool Parser::evaluateLet(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode>& result){
        std::shared_ptr<DAGNode> body = expandLet(expr);
        return evaluatedOperand(this, body, model, result);
    }

    std::shared_ptr<DAGNode> Parser::expandLet(std::shared_ptr<DAGNode> expr){
        if(getOptions()->parsing_preserve_let && (expr->isLet() || expr->isLetChain())){
            // Determine the body based on the structure type
            std::shared_ptr<DAGNode> body;
            if(expr->isLet()){
                // expand let - body is the first child
                body = expr->getChild(0);
            } else {
                // expand let-chain - body is the last child: [bind_var_list1, ..., bind_var_listN, body]
                condAssert(expr->getChildrenSize() >= 2, "let-chain should have at least one bind_var_list and one body");
                body = expr->getChild(expr->getChildrenSize() - 1);
            }
            
            // use iteration instead of recursion to handle all nested let_bind_var
            std::stack<std::shared_ptr<DAGNode>> nodeStack;
            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> resultMap; // save the result of processed nodes
            std::unordered_map<std::shared_ptr<DAGNode>, bool> hasChangedMap; // save the flag of whether the node has been changed
            
            // push the initial node
            nodeStack.push(body);
            
            // iterate until the stack is empty
            while(!nodeStack.empty()) {
                std::shared_ptr<DAGNode> currentNode = nodeStack.top();
                
                // check if the node has been processed
                if(resultMap.find(currentNode) != resultMap.end()) {
                    nodeStack.pop();
                    continue;
                }
                
                // check if all children have been processed
                bool allChildrenProcessed = true;
                std::vector<std::shared_ptr<DAGNode>> processedChildren;
                bool hasChanged = false;
                
                // process the children
                for(size_t i = 0; i < currentNode->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child = currentNode->getChild(i);
                    
                    // if the child has been processed, use the processed result
                    if(resultMap.find(child) != resultMap.end()) {
                        processedChildren.push_back(resultMap[child]);
                        if(hasChangedMap[child]){
                            hasChanged = true;
                        }
                    } else {
                        // if the child has not been processed, push it to the stack and process it
                        nodeStack.push(child);
                        allChildrenProcessed = false;
                        break;
                    }
                }
                
                // if all children have been processed, process the current node
                if(allChildrenProcessed) {
                    nodeStack.pop();
                    std::shared_ptr<DAGNode> result;

                    if(currentNode->isLet() || currentNode->isLetChain()) {
                        // A NESTED let/let-chain (e.g. one sitting inside a
                        // let-binding's value: (let ((a (let ((b ...)) ...))) ...)).
                        // Its body's let_bind_var references were already
                        // substituted during this traversal, so STRIP the let
                        // wrapper and return the processed body — exactly as the
                        // top-level let is stripped via resultMap[body] below.
                        // Without this the inner NT_LET/NT_LET_CHAIN node is
                        // reconstructed verbatim and survives expansion, reaching
                        // the consumer as an unmapped node (false unknown on every
                        // formula with a let nested in a binding value, e.g. the
                        // CSE encodings in QF_ALIA SVCOMP).
                        std::shared_ptr<DAGNode> innerBody = currentNode->isLet()
                            ? currentNode->getChild(0)
                            : currentNode->getChild(currentNode->getChildrenSize() - 1);
                        result = resultMap[innerBody];
                        hasChangedMap[currentNode] = true;
                    } else if(currentNode->isLetBindVar()) {
                        // if the current node is a let_bind_var, replace it with its child(0)
                        condAssert(currentNode->getChildrenSize() > 0, "let_bind_var should have at least one child");
                        result = resultMap[currentNode->getChild(0)]; // use the processed child(0)
                        hasChangedMap[currentNode] = true;
                    } else if(hasChanged) {
                        // if some children have been replaced, reconstruct the node
                        // For UFApply, preserve the original function name (mkOper uses
                        // kindToString() which overwrites "f1" with "UF_APPLY").
                        // SAME for DT kinds (constructor/selector/tester): the operator
                        // NAME identifies which constructor (e.g. "stack" vs "empty").
                        // mkOper would clobber it with kindToString(NT_DT_TESTER) =
                        // "UNKNOWN_KIND", which propagates through xolver to a tester
                        // EUF symbol "#dt.is.UNKNOWN_KIND" — DtReasoner's tester-
                        // consistency then false-conflicts is-empty(u) ∧ u=empty
                        // because "UNKNOWN_KIND" != "empty" (220/308 QF_DT blocksworld
                        // BMC false-UNSATs class).
                        // For other kinds, keep mkOper to retain simp_oper folding.
                        if(currentNode->getKind() == NODE_KIND::NT_UF_APPLY ||
                           currentNode->getKind() == NODE_KIND::NT_FUNC_APPLY ||
                           currentNode->getKind() == NODE_KIND::NT_DT_CONSTRUCTOR ||
                           currentNode->getKind() == NODE_KIND::NT_DT_SELECTOR ||
                           currentNode->getKind() == NODE_KIND::NT_DT_TESTER){
                            result = getNodeManager()->createNode(currentNode->getSort(), currentNode->getKind(), currentNode->getName(), processedChildren);
                        } else {
                            result = mkOper(currentNode->getSort(), currentNode->getKind(), processedChildren);
                        }
                        hasChangedMap[currentNode] = true;
                    } else {
                        // no change, keep the original node
                        result = currentNode;
                        hasChangedMap[currentNode] = false;
                    }
                    
                    // save the processed result
                    resultMap[currentNode] = result;
                }
            }
            
            // return the processed result
            return resultMap[body];
        }
        else{
            return expr;
        }
    }
    bool Parser::evaluateMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MAX);
    }
    bool Parser::evaluateMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_MIN);
    }
    bool Parser::evaluateStrSplitAtRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SPLIT_AT_RE);
    }
    bool Parser::evaluateStrSplitRestRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_SPLIT_REST_RE);
    }
    bool Parser::evaluateStrNumSplitsRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result){
        return evaluateSimpleOp(expr, model, result, NODE_KIND::NT_STR_NUM_SPLITS_RE);
    }
    
}


