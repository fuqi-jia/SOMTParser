/* -*- Header -*-
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

#ifndef _OBJECTIVE_H
#define _OBJECTIVE_H

#include "somtparser/ir/dag.h"

#include <unordered_map>
#include <vector>

namespace SOMTParser{
    /** Exact numeric token for SMT soft weights; refuses non-finite decimals. */
    std::string softWeightToken(const std::shared_ptr<DAGNode>& weight);

    enum class OPT_KIND{
        // single objective
        OPT_MINIMIZE, OPT_MAXIMIZE, OPT_MAXSAT, OPT_MINSAT, 
        // multi-objective
        OPT_LEX_OPTIMIZE, OPT_PARETO_OPTIMIZE, OPT_BOX_OPTIMIZE, OPT_MINMAX, OPT_MAXMIN,
        // NULL
        OPT_NULL
    };

    enum class COMP_KIND{
        COMP_LT, COMP_LE, COMP_GT, COMP_GE, COMP_BV_ULT, COMP_BV_ULE, COMP_BV_UGT, COMP_BV_UGE, COMP_BV_SLT, COMP_BV_SLE, COMP_BV_SGT, COMP_BV_SGE, COMP_FP_LT, COMP_FP_LE, COMP_FP_GT, COMP_FP_GE, COMP_NULL
    };

    COMP_KIND getDefaultCompareOperator(const std::string& logic, OPT_KIND opt_type = OPT_KIND::OPT_MINIMIZE);
    COMP_KIND getCompareOperator(const std::string& symbol);
    COMP_KIND getNegatedOperator(COMP_KIND comp);
    COMP_KIND getFlipOperator(COMP_KIND comp);
    COMP_KIND getStrictOperator(COMP_KIND comp);
    NODE_KIND getCompareNodeKind(COMP_KIND comp);
    NODE_KIND getEqNodeKind(COMP_KIND comp); // return the NodeKind of the equality node in the same theory

    
    COMP_KIND getCompareOperatorForObjectiveTerm(const std::shared_ptr<DAGNode>& obj_term, OPT_KIND opt_type = OPT_KIND::OPT_MINIMIZE);

    // Composite Pattern
    class MetaObjective{
    protected:
        OPT_KIND opt_kind;
        std::string group_id;
    public:
        MetaObjective(OPT_KIND opt_kind, const std::string& group_id): opt_kind(opt_kind), group_id(group_id){}
        MetaObjective(OPT_KIND opt_kind): opt_kind(opt_kind), group_id(""){}
        MetaObjective(): opt_kind(OPT_KIND::OPT_NULL), group_id(""){}
        virtual ~MetaObjective(){}
        const std::string& getGroupID() const{
            return group_id;
        }
        OPT_KIND getObjectiveKind() const{
            return opt_kind;
        }

        bool isSingleObjective() const{
            return opt_kind == OPT_KIND::OPT_MINIMIZE || opt_kind == OPT_KIND::OPT_MAXIMIZE || opt_kind == OPT_KIND::OPT_MAXSAT || opt_kind == OPT_KIND::OPT_MINSAT;
        }
        bool isMultiObjective() const{
            return opt_kind == OPT_KIND::OPT_LEX_OPTIMIZE || opt_kind == OPT_KIND::OPT_PARETO_OPTIMIZE || opt_kind == OPT_KIND::OPT_BOX_OPTIMIZE || opt_kind == OPT_KIND::OPT_MINMAX || opt_kind == OPT_KIND::OPT_MAXMIN;
        }
        bool isMaximize() const{
            return opt_kind == OPT_KIND::OPT_MAXIMIZE;
        }
        bool isMinimize() const{
            return opt_kind == OPT_KIND::OPT_MINIMIZE;
        }
        bool isMaxSAT() const{
            return opt_kind == OPT_KIND::OPT_MAXSAT;
        }
        bool isMinSAT() const{
            return opt_kind == OPT_KIND::OPT_MINSAT;
        }
        bool isLexOptimize() const{
            return opt_kind == OPT_KIND::OPT_LEX_OPTIMIZE;
        }
        bool isParetoOptimize() const{
            return opt_kind == OPT_KIND::OPT_PARETO_OPTIMIZE;
        }
        bool isBoxOptimize() const{
            return opt_kind == OPT_KIND::OPT_BOX_OPTIMIZE;
        }
        bool isMinmax() const{
            return opt_kind == OPT_KIND::OPT_MINMAX;
        }
        bool isMaxmin() const{
            return opt_kind == OPT_KIND::OPT_MAXMIN;
        }

        // single objective
        // get the objective term
        virtual const std::shared_ptr<DAGNode>& getObjectiveTerm() const = 0;
        // get the compare operator
        virtual COMP_KIND getCompareOperator() const = 0;
        // get the epsilon
        virtual const std::shared_ptr<DAGNode>& getEpsilon() const = 0;
        // get the M
        virtual const std::shared_ptr<DAGNode>& getM() const = 0;

        // multi-objective
        // get the objective
        virtual const std::shared_ptr<MetaObjective>& getObjective(const size_t& idx) const = 0;
        // get the size of the objectives
        virtual size_t getObjectiveSize() const = 0;
    };

    class SingleObjective: public MetaObjective{
    private:
        // the objective term
        std::shared_ptr<DAGNode> objective_term;
        // the compare operator
        COMP_KIND compare_operator;
        // additional constraints
        // epsilon
        std::shared_ptr<DAGNode> epsilon;
        // M
        std::shared_ptr<DAGNode> M;
    public:
        SingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& objective_term, COMP_KIND compare_operator, const std::shared_ptr<DAGNode>& epsilon, const std::shared_ptr<DAGNode>& M, const std::string& group_id):
            MetaObjective(opt_type, group_id), objective_term(objective_term), compare_operator(compare_operator), epsilon(epsilon), M(M){}
        SingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& objective_term, COMP_KIND compare_operator, const std::shared_ptr<DAGNode>& epsilon, const std::shared_ptr<DAGNode>& M):
            SingleObjective(opt_type, objective_term, compare_operator, epsilon, M, ""){}
        SingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& objective_term, COMP_KIND compare_operator, const std::shared_ptr<DAGNode>& epsilon):
            SingleObjective(opt_type, objective_term, compare_operator, epsilon, NodeManager::NULL_NODE, ""){}
        SingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& objective_term, COMP_KIND compare_operator):
            SingleObjective(opt_type, objective_term, compare_operator, NodeManager::NULL_NODE, NodeManager::NULL_NODE, ""){}
        SingleObjective(OPT_KIND opt_type, const std::string& group_id):
            SingleObjective(opt_type, NodeManager::NULL_NODE, COMP_KIND::COMP_LT, NodeManager::NULL_NODE, NodeManager::NULL_NODE, group_id){}
        ~SingleObjective(){}

        // single objective
        // get the objective term
        const std::shared_ptr<DAGNode>& getObjectiveTerm() const override{
            return objective_term;
        }
        // get the compare operator
        COMP_KIND getCompareOperator() const override{
            return compare_operator;
        }
        // get the epsilon
        const std::shared_ptr<DAGNode>& getEpsilon() const override{
            return epsilon;
        }
        // get the M
        const std::shared_ptr<DAGNode>& getM() const override{
            return M;
        }

        // multi-objective
        // get the objective
        const std::shared_ptr<MetaObjective>& getObjective(const size_t& idx) const override{
            if(idx == 0){
                static std::shared_ptr<MetaObjective> self = std::static_pointer_cast<MetaObjective>(std::shared_ptr<SingleObjective>(const_cast<SingleObjective*>(this)));
                return self;
            }
            else{
                static const std::shared_ptr<MetaObjective> nullPtr;
                return nullPtr;
            }
        }
        // get the size of the objectives
        size_t getObjectiveSize() const override{
            return 0;
        }
    };

    class Objective: public MetaObjective{
    private:
        std::vector<std::shared_ptr<MetaObjective>> objectives;
    public:
        Objective(OPT_KIND opt_type, const std::string& group_id): MetaObjective(opt_type, group_id){}
        ~Objective(){}

        bool addObjective(const std::shared_ptr<MetaObjective>& obj){
            objectives.emplace_back(obj);
            return true;
        }

        // single objective
        // get the objective term
        const std::shared_ptr<DAGNode>& getObjectiveTerm() const override{
            if(isSingleObjective()){
                return objectives[0]->getObjectiveTerm();
            }
            return NodeManager::NULL_NODE;
        }
        // get the compare operator
        COMP_KIND getCompareOperator() const override{
            if(isSingleObjective()){
                return objectives[0]->getCompareOperator();
            }
            return COMP_KIND::COMP_NULL;
        }
        // get the epsilon
        const std::shared_ptr<DAGNode>& getEpsilon() const override{
            if(isSingleObjective()){
                return objectives[0]->getEpsilon();
            }
            return NodeManager::NULL_NODE;
        }
        // get the M
        const std::shared_ptr<DAGNode>& getM() const override{
            if(isSingleObjective()){
                return objectives[0]->getM();
            }
            return NodeManager::NULL_NODE;
        }

        // multi-objective
        // get the objective
        const std::shared_ptr<MetaObjective>& getObjective(const size_t& idx) const override{
            return objectives[idx];
        }
        // get the size of the objectives
        size_t getObjectiveSize() const override{
            return objectives.size();
        }
    };

    OPT_KIND getOptKind(const std::string& symbol);

    struct GomtSoftAssertion {
        std::shared_ptr<DAGNode> node;
        std::shared_ptr<DAGNode> weight;
    };

    /**
     * Manager for OMT objectives: named registry (define-objective) and ordered list (minimize/maximize/lex-optimize etc.).
     */
    class ObjectiveManager {
    public:
        ObjectiveManager() = default;

        /** Register a named objective (define-objective <name> ...). */
        void registerNamed(const std::string& name, const std::shared_ptr<Objective>& obj);
        /** Append an objective to the ordered list (minimize/maximize/...). */
        void addObjective(const std::shared_ptr<Objective>& obj);
        /** Get objective by name (for multi-objective references). */
        std::shared_ptr<Objective> getObjective(const std::string& name) const;
        /** Get the ordered list of objectives. */
        std::vector<std::shared_ptr<Objective>> getObjectives() const;

        /** Truncate objectives list to size n and clean up objective_map_. */
        void popToSize(size_t n);

        /** Clear all objectives and named objectives. */
        void clear();

        // GOMT definitions are inactive until optimize-sat selects one.
        bool hasGomtObjectives() const;
        void registerGomtObjective(const std::string& name, const std::shared_ptr<Objective>& obj);
        std::shared_ptr<Objective> getGomtObjective(const std::string& name) const;
        void addGomtSoftAssertion(const std::string& name, const std::shared_ptr<DAGNode>& node,
                                  const std::shared_ptr<DAGNode>& weight);
        const std::vector<GomtSoftAssertion>& getGomtSoftAssertions(const std::string& name) const;
        void selectGomtObjective(const std::string& name);
        std::shared_ptr<Objective> getSelectedGomtObjective() const;

        /** Create an empty Objective (for multi-objective; caller adds sub-objectives then addObjective). */
        std::shared_ptr<Objective> createObjective(OPT_KIND opt_type, const std::string& grp_id);
        /** Add a single objective (maxsat/minsat) to the list and return it. */
        std::shared_ptr<Objective> addSingleObjective(OPT_KIND opt_type, const std::string& grp_id);
        /** Add a single objective (minimize/maximize) to the list and return it. */
        std::shared_ptr<Objective> addSingleObjective(OPT_KIND opt_type, const std::shared_ptr<DAGNode>& term,
            COMP_KIND comp_op, const std::shared_ptr<DAGNode>& epsilon, const std::shared_ptr<DAGNode>& M,
            const std::string& grp_id);

    private:
        std::unordered_map<std::string, std::shared_ptr<Objective>> objective_map_;
        std::vector<std::shared_ptr<Objective>> objectives_;
        std::unordered_map<std::string, std::shared_ptr<Objective>> gomt_objectives_;
        std::unordered_map<std::string, std::vector<GomtSoftAssertion>> gomt_soft_assertions_;
        std::shared_ptr<Objective> selected_gomt_objective_;
    };

    // smart pointers
    typedef std::shared_ptr<MetaObjective> MetaObjectivePtr;
    typedef std::shared_ptr<SingleObjective> SingleObjectivePtr;
    typedef std::shared_ptr<Objective> ObjectivePtr;
}

#endif // _OBJECTIVE_H
