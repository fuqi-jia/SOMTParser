/* -*- Source -*-
 *
 * The Objective Class
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

#include "somtparser/frontend/objective.h"

namespace SOMTParser{

    COMP_KIND getDefaultCompareOperator(const std::string& logic, OPT_KIND opt_type){
        condAssert(opt_type == OPT_KIND::OPT_MINIMIZE || opt_type == OPT_KIND::OPT_MAXIMIZE, "getDefaultCompareOperator: opt_type is not minimize or maximize");
        if(logic == "QF_LIA" || logic == "QF_LRA" || logic == "QF_NIA" || logic == "QF_NRA" || logic == "QF_IDL" || logic == "QF_RDL" || logic == "QF_LIRA" || logic == "QF_NIRA"){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_LT : COMP_KIND::COMP_GT;
        }
        if(logic == "QF_BV" || logic == "QF_ABV" || logic == "QF_AUFBV" || logic == "QF_AUFBVFP" || logic == "QF_ABVFP" || logic == "QF_BVFP" || logic == "QF_BVFPLRA"){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_BV_ULT : COMP_KIND::COMP_BV_UGT;
        }
        if(logic == "QF_FP" || logic == "QF_FPLRA" || logic == "QF_ABVFPLRA"){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_FP_LT : COMP_KIND::COMP_FP_GT;
        }
        return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_LT : COMP_KIND::COMP_GT;
    }

    COMP_KIND getCompareOperator(const std::string& symbol){
        if(symbol == "<"){
            return COMP_KIND::COMP_LT;
        }
        if(symbol == "<="){
            return COMP_KIND::COMP_LE;
        }
        if(symbol == ">"){
            return COMP_KIND::COMP_GT;
        }
        if(symbol == ">="){
            return COMP_KIND::COMP_GE;
        }
        if(symbol == "bvult"){
            return COMP_KIND::COMP_BV_ULT;
        }
        if(symbol == "bvule"){
            return COMP_KIND::COMP_BV_ULE;
        }
        if(symbol == "bvugt"){
            return COMP_KIND::COMP_BV_UGT;
        }
        if(symbol == "bvuge"){
            return COMP_KIND::COMP_BV_UGE;
        }
        if(symbol == "bvslt"){
            return COMP_KIND::COMP_BV_SLT;
        }
        if(symbol == "bvsle"){
            return COMP_KIND::COMP_BV_SLE;
        }
        if(symbol == "bvsgt"){
            return COMP_KIND::COMP_BV_SGT;
        }
        if(symbol == "bvsge"){
            return COMP_KIND::COMP_BV_SGE;
        }
        if(symbol == "fp.lt"){
            return COMP_KIND::COMP_FP_LT;
        }
        if(symbol == "fp.leq"){
            return COMP_KIND::COMP_FP_LE;
        }
        if(symbol == "fp.gt"){
            return COMP_KIND::COMP_FP_GT;
        }
        if(symbol == "fp.geq"){
            return COMP_KIND::COMP_FP_GE;
        }
        return COMP_KIND::COMP_LT;
    }

    
    COMP_KIND getNegatedOperator(COMP_KIND comp){
        // get the opposite operator
        switch (comp)
        {
        case COMP_KIND::COMP_LT:
            return COMP_KIND::COMP_GE;
        case COMP_KIND::COMP_LE:
            return COMP_KIND::COMP_GT;
        case COMP_KIND::COMP_GT:
            return COMP_KIND::COMP_LE;
        case COMP_KIND::COMP_GE:
            return COMP_KIND::COMP_LT;
        case COMP_KIND::COMP_BV_ULT:
            return COMP_KIND::COMP_BV_UGE;
        case COMP_KIND::COMP_BV_ULE:
            return COMP_KIND::COMP_BV_UGT;
        case COMP_KIND::COMP_BV_UGT:
            return COMP_KIND::COMP_BV_ULE;
        case COMP_KIND::COMP_BV_UGE:
            return COMP_KIND::COMP_BV_ULT;
        case COMP_KIND::COMP_BV_SLT:
            return COMP_KIND::COMP_BV_SGE;
        case COMP_KIND::COMP_BV_SLE:
            return COMP_KIND::COMP_BV_SGT;
        case COMP_KIND::COMP_BV_SGT:
            return COMP_KIND::COMP_BV_SLE;
        case COMP_KIND::COMP_BV_SGE:
            return COMP_KIND::COMP_BV_SLT;
        case COMP_KIND::COMP_FP_LT:
            return COMP_KIND::COMP_FP_GE;
        case COMP_KIND::COMP_FP_LE:
            return COMP_KIND::COMP_FP_GT;
        case COMP_KIND::COMP_FP_GT:
            return COMP_KIND::COMP_FP_LE;
        case COMP_KIND::COMP_FP_GE:
            return COMP_KIND::COMP_FP_LT;
        default:
            return COMP_KIND::COMP_LT;
        }
    }

    COMP_KIND getFlipOperator(COMP_KIND comp){
        switch (comp)
        {
            case COMP_KIND::COMP_LT:
                return COMP_KIND::COMP_GT;
            case COMP_KIND::COMP_LE:
                return COMP_KIND::COMP_GE;
            case COMP_KIND::COMP_GT:
                return COMP_KIND::COMP_LT;
            case COMP_KIND::COMP_GE:
                return COMP_KIND::COMP_LE;
            case COMP_KIND::COMP_BV_ULT:
                return COMP_KIND::COMP_BV_UGT;
            case COMP_KIND::COMP_BV_ULE:
                return COMP_KIND::COMP_BV_UGE;
            case COMP_KIND::COMP_BV_UGT:
                return COMP_KIND::COMP_BV_ULT;
            case COMP_KIND::COMP_BV_UGE:
                return COMP_KIND::COMP_BV_ULE;
            case COMP_KIND::COMP_BV_SLT:
                return COMP_KIND::COMP_BV_SGT;
            case COMP_KIND::COMP_BV_SLE:
                return COMP_KIND::COMP_BV_SGE;
            case COMP_KIND::COMP_BV_SGT:
                return COMP_KIND::COMP_BV_SLT;
            case COMP_KIND::COMP_BV_SGE:
                return COMP_KIND::COMP_BV_SLE;
            case COMP_KIND::COMP_FP_LT:
                return COMP_KIND::COMP_FP_GT;
            case COMP_KIND::COMP_FP_LE:
                return COMP_KIND::COMP_FP_GE;
            case COMP_KIND::COMP_FP_GT:
                return COMP_KIND::COMP_FP_LT;
            case COMP_KIND::COMP_FP_GE:
                return COMP_KIND::COMP_FP_LE;
            default:
                return COMP_KIND::COMP_LT;
        }
    }

    COMP_KIND getStrictOperator(COMP_KIND comp){
        switch (comp)
        {
        case COMP_KIND::COMP_LT:
            return COMP_KIND::COMP_LT;
        case COMP_KIND::COMP_LE:
            return COMP_KIND::COMP_LT;
        case COMP_KIND::COMP_GT:
            return COMP_KIND::COMP_GT;
        case COMP_KIND::COMP_GE:
            return COMP_KIND::COMP_GT;
        case COMP_KIND::COMP_BV_ULT:
            return COMP_KIND::COMP_BV_ULT;
        case COMP_KIND::COMP_BV_ULE:
            return COMP_KIND::COMP_BV_ULT;
        case COMP_KIND::COMP_BV_UGT:
            return COMP_KIND::COMP_BV_UGT;
        case COMP_KIND::COMP_BV_UGE:
            return COMP_KIND::COMP_BV_UGT;
        case COMP_KIND::COMP_BV_SLT:
            return COMP_KIND::COMP_BV_SLT;
        case COMP_KIND::COMP_BV_SLE:
            return COMP_KIND::COMP_BV_SLT;
        case COMP_KIND::COMP_BV_SGT:
            return COMP_KIND::COMP_BV_SGT;
        case COMP_KIND::COMP_BV_SGE:
            return COMP_KIND::COMP_BV_SGT;
        case COMP_KIND::COMP_FP_LT:
            return COMP_KIND::COMP_FP_LT;
        case COMP_KIND::COMP_FP_LE:
            return COMP_KIND::COMP_FP_LT;
        case COMP_KIND::COMP_FP_GT:
            return COMP_KIND::COMP_FP_GT;
        case COMP_KIND::COMP_FP_GE:
            return COMP_KIND::COMP_FP_GT;
        default:
            return COMP_KIND::COMP_LT;
        }
    }
    
    NODE_KIND getCompareNodeKind(COMP_KIND comp){
        switch (comp)
        {
        case COMP_KIND::COMP_LT:
            return NODE_KIND::NT_LT;
        case COMP_KIND::COMP_LE:
            return NODE_KIND::NT_LE;
        case COMP_KIND::COMP_GT:
            return NODE_KIND::NT_GT;
        case COMP_KIND::COMP_GE:
            return NODE_KIND::NT_GE;
        case COMP_KIND::COMP_BV_ULT:
            return NODE_KIND::NT_BV_ULT;
        case COMP_KIND::COMP_BV_ULE:
            return NODE_KIND::NT_BV_ULE;
        case COMP_KIND::COMP_BV_UGT:
            return NODE_KIND::NT_BV_UGT;
        case COMP_KIND::COMP_BV_UGE:
            return NODE_KIND::NT_BV_UGE;
        case COMP_KIND::COMP_BV_SLT:
            return NODE_KIND::NT_BV_SLT;
        case COMP_KIND::COMP_BV_SLE:
            return NODE_KIND::NT_BV_SLE;
        case COMP_KIND::COMP_BV_SGT:
            return NODE_KIND::NT_BV_SGT;
        case COMP_KIND::COMP_BV_SGE:
            return NODE_KIND::NT_BV_SGE;
        case COMP_KIND::COMP_FP_LT:
            return NODE_KIND::NT_FP_LT;
        case COMP_KIND::COMP_FP_LE:
            return NODE_KIND::NT_FP_LE;
        case COMP_KIND::COMP_FP_GT:
            return NODE_KIND::NT_FP_GT;
        case COMP_KIND::COMP_FP_GE:
            return NODE_KIND::NT_FP_GE;
        default:
            return NODE_KIND::NT_LT;
        }
    }

    NODE_KIND getEqNodeKind(COMP_KIND comp){
        switch (comp)
        {
        case COMP_KIND::COMP_FP_LT:
            return NODE_KIND::NT_FP_EQ;
        case COMP_KIND::COMP_FP_LE:
            return NODE_KIND::NT_FP_EQ;
        case COMP_KIND::COMP_FP_GT:
            return NODE_KIND::NT_FP_EQ;
        case COMP_KIND::COMP_FP_GE:
            return NODE_KIND::NT_FP_EQ;
        default:
            return NODE_KIND::NT_EQ;
        }
    }

    
    OPT_KIND getOptKind(const std::string& symbol){
        if(symbol == "maximize"){
            return OPT_KIND::OPT_MAXIMIZE;
        }
        if(symbol == "minimize"){
            return OPT_KIND::OPT_MINIMIZE;
        }
        if(symbol == "maxsat"){
            return OPT_KIND::OPT_MAXSAT;
        }
        if(symbol == "minsat"){
            return OPT_KIND::OPT_MINSAT;
        }
        if(symbol == "lex"){
            return OPT_KIND::OPT_LEX_OPTIMIZE;
        }
        if(symbol == "pareto"){
            return OPT_KIND::OPT_PARETO_OPTIMIZE;
        }
        if(symbol == "box"){
            return OPT_KIND::OPT_BOX_OPTIMIZE;
        }
        if(symbol == "minmax"){
            return OPT_KIND::OPT_MINMAX;
        }
        if(symbol == "maxmin"){
            return OPT_KIND::OPT_MAXMIN;
        }
        return OPT_KIND::OPT_NULL;
    }

    
    COMP_KIND getCompareOperatorForObjectiveTerm(const std::shared_ptr<DAGNode>& obj_term, OPT_KIND opt_type){
        condAssert(opt_type == OPT_KIND::OPT_MINIMIZE || opt_type == OPT_KIND::OPT_MAXIMIZE, 
                   "getCompareOperatorForObjectiveTerm: opt_type is not minimize or maximize");
        
        if(!obj_term || !obj_term->getSort()){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_LT : COMP_KIND::COMP_GT;
        }
        
        if(obj_term->getSort()->isFp()){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_FP_LT : COMP_KIND::COMP_FP_GT;
        } else if(obj_term->getSort()->isBv()){
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_BV_ULT : COMP_KIND::COMP_BV_UGT;
        } else {
            return opt_type == OPT_KIND::OPT_MINIMIZE ? COMP_KIND::COMP_LT : COMP_KIND::COMP_GT;
        }
    }

    // --- ObjectiveManager ---

    void ObjectiveManager::registerNamed(const std::string& name, const std::shared_ptr<Objective>& obj) {
        objective_map_[name] = obj;
    }

    void ObjectiveManager::addObjective(const std::shared_ptr<Objective>& obj) {
        objectives_.emplace_back(obj);
    }

    std::shared_ptr<Objective> ObjectiveManager::getObjective(const std::string& name) const {
        auto it = objective_map_.find(name);
        return it != objective_map_.end() ? it->second : nullptr;
    }

    std::vector<std::shared_ptr<Objective>> ObjectiveManager::getObjectives() const {
        return objectives_;
    }

    void ObjectiveManager::popToSize(size_t n) {
        if (n >= objectives_.size()) return;
        // Remove entries from objective_map_ that correspond to objectives being popped
        for (size_t i = n; i < objectives_.size(); ++i) {
            if (objectives_[i] == selected_gomt_objective_) selected_gomt_objective_.reset();
            for (auto it = objective_map_.begin(); it != objective_map_.end(); ) {
                if (it->second == objectives_[i]) {
                    it = objective_map_.erase(it);
                } else {
                    ++it;
                }
            }
        }
        objectives_.resize(n);
    }

    void ObjectiveManager::clear() {
        objectives_.clear();
        objective_map_.clear();
        gomt_objectives_.clear();
        gomt_soft_assertions_.clear();
        selected_gomt_objective_.reset();
    }

    namespace {
        std::string objectiveSymbol(const std::string& name) {
            return name.size() >= 2 && name.front() == '|' && name.back() == '|'
                ? name.substr(1, name.size() - 2) : name;
        }
    }

    bool ObjectiveManager::hasGomtObjectives() const {
        return !gomt_objectives_.empty();
    }

    void ObjectiveManager::registerGomtObjective(const std::string& name,
                                                const std::shared_ptr<Objective>& obj) {
        condAssert(obj != nullptr, "GOMT objective must not be null");
        condAssert(gomt_objectives_.emplace(objectiveSymbol(name), obj).second,
                   "GOMT objective is already defined: " + name);
    }

    std::shared_ptr<Objective> ObjectiveManager::getGomtObjective(const std::string& name) const {
        const auto it = gomt_objectives_.find(objectiveSymbol(name));
        return it == gomt_objectives_.end() ? nullptr : it->second;
    }

    void ObjectiveManager::addGomtSoftAssertion(const std::string& name,
                                               const std::shared_ptr<DAGNode>& node,
                                               const std::shared_ptr<DAGNode>& weight) {
        const auto objective = getGomtObjective(name);
        condAssert(objective && objective->isMaxSAT(), "unknown GOMT MaxSMT objective: " + name);
        gomt_soft_assertions_[objectiveSymbol(name)].push_back({node, weight});
    }

    const std::vector<GomtSoftAssertion>& ObjectiveManager::getGomtSoftAssertions(const std::string& name) const {
        static const std::vector<GomtSoftAssertion> empty;
        const auto it = gomt_soft_assertions_.find(objectiveSymbol(name));
        return it == gomt_soft_assertions_.end() ? empty : it->second;
    }

    void ObjectiveManager::selectGomtObjective(const std::string& name) {
        const auto objective = getGomtObjective(name);
        condAssert(objective != nullptr, "unknown GOMT objective: " + name);
        selected_gomt_objective_ = objective;
        objectives_.assign(1, objective);
    }

    std::shared_ptr<Objective> ObjectiveManager::getSelectedGomtObjective() const {
        return selected_gomt_objective_;
    }

    std::shared_ptr<Objective> ObjectiveManager::createObjective(OPT_KIND opt_type, const std::string& grp_id) {
        return std::make_shared<Objective>(opt_type, grp_id);
    }

    std::shared_ptr<Objective> ObjectiveManager::addSingleObjective(OPT_KIND opt_type, const std::string& grp_id) {
        std::shared_ptr<SingleObjective> obj = std::make_shared<SingleObjective>(opt_type, grp_id);
        std::shared_ptr<Objective> objective = std::make_shared<Objective>(opt_type, grp_id);
        objective->addObjective(obj);
        objectives_.emplace_back(objective);
        return objective;
    }

    std::shared_ptr<Objective> ObjectiveManager::addSingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& term,
            COMP_KIND comp_op, const std::shared_ptr<DAGNode>& epsilon, const std::shared_ptr<DAGNode>& M,
            const std::string& grp_id) {
        std::shared_ptr<SingleObjective> obj = std::make_shared<SingleObjective>(opt_type, term, comp_op, epsilon, M, grp_id);
        std::shared_ptr<Objective> objective = std::make_shared<Objective>(opt_type, grp_id);
        objective->addObjective(obj);
        objectives_.emplace_back(objective);
        return objective;
    }
}
