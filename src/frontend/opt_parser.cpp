/* -*- Source -*-
 *
 * An SMT/OMT Parser (OMT part)
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

namespace SOMTParser{
    
    KEYWORD Parser::attemptParseKeywords(){
        if(*bufptr == ':'){
            // :id
            return parseKeyword();
        }
        else{
            return KEYWORD::KW_NULL;
        }
    }
    // (assert-soft <expr> [:weight <numeral>] [:id <symbol>])
    void Parser::assertSoft(std::shared_ptr<DAGNode> node,
                            std::shared_ptr<DAGNode> weight,
                            const std::string& group){
        condAssert(node != nullptr, "assertSoft: null constraint");
        condAssert(!getObjectiveManager()->hasGomtObjectives(),
                   "assertSoft: native soft assertions cannot be mixed with GOMT definitions");
        const size_t index = context_.soft_assertions.size();
        context_.soft_objective_positions.push_back(getObjectives().size());
        context_.soft_assertions.emplace_back(std::move(node));
        // Weight 1 when omitted, which is SMT-LIB's default and what
        // parseAssertSoft records for a bare (assert-soft e).
        context_.soft_weights.emplace_back(weight ? weight : mkConstInt(1));
        if(!group.empty()){
            context_.soft_assertion_groups[group].insert(index);
            context_.registerSoftAssertionGroupInScope(group);
        }
    }

    void Parser::parseAssertSoft(){
        size_t key_ln = line_number;
        std::string grp_id = "";
        std::string weight = "";
        std::string objective_name;
        size_t weight_attributes = 0;
        size_t objective_attributes = 0;
        const auto attributes = [&]() {
            while (*bufptr == ':') {
                const auto key = getSymbol();
                if (!*bufptr || *bufptr == ')' || *bufptr == '(') {
                    err_all(ERROR_TYPE::ERR_PARAM_MIS, "assert-soft attribute requires a value", key_ln);
                }
                if (key == ":weight") { weight = getSymbol(); ++weight_attributes; }
                else if (key == ":id") grp_id = getSymbol();
                else if (key == ":objective") { objective_name = getSymbol(); ++objective_attributes; }
                else err_all(ERROR_TYPE::ERR_PARAM_MIS, "unsupported assert-soft attribute " + key, key_ln);
            }
        };
        attributes();
        std::shared_ptr<DAGNode> assert_expr = parseExpr();
        attributes();
        if (*bufptr != ')' || !assert_expr || !assert_expr->getSort() || !assert_expr->getSort()->isBool()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "assert-soft requires one Boolean term", key_ln);
        }
        std::shared_ptr<DAGNode> weight_node;
        if(weight != ""){
            if(TypeChecker::isInt(weight)){
                weight_node = mkConstInt(weight);
            }
            else if(TypeChecker::isReal(weight)){
                weight_node = mkConstReal(weight);
            }
            else{
                err_param_nnum("Weight", key_ln);
            }
        }
        else{
            weight_node = mkConstInt(1);
        }
        if (!objective_name.empty()) {
            auto manager = getObjectiveManager();
            const auto objective = manager->getGomtObjective(objective_name);
            if (!grp_id.empty() || !context_.scope_stack_.empty() || !objective || !objective->isMaxSAT()
                || objective_attributes != 1 || weight_attributes > 1) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS,
                        "assert-soft :objective requires one declared GOMT MaxSMT objective at the base scope, no :id and at most one weight", key_ln);
            }
            manager->addGomtSoftAssertion(objective_name, assert_expr, weight_node);
            const auto selected = manager->getSelectedGomtObjective();
            bool active = selected == objective;
            if (selected && selected->isMultiObjective()) {
                for (size_t i = 0; i < selected->getObjectiveSize(); ++i) {
                    active = active || selected->getObjective(i) == objective;
                }
            }
            if (active) {
                const size_t index = context_.soft_assertions.size();
                context_.soft_assertions.push_back(assert_expr);
                context_.soft_weights.push_back(weight_node);
                context_.soft_objective_positions.push_back(0);
                context_.soft_assertion_groups[objective->getGroupID()].insert(index);
            }
            return;
        }
        if (getObjectiveManager()->hasGomtObjectives()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT assert-soft requires :objective", key_ln);
        }
        size_t index = context_.soft_assertions.size();
        context_.soft_objective_positions.push_back(getObjectives().size());
        context_.soft_assertions.emplace_back(assert_expr);
        context_.soft_weights.emplace_back(weight_node);
        // add the group id
        if(grp_id != ""){
            if(context_.soft_assertion_groups.find(grp_id) == context_.soft_assertion_groups.end()){
                context_.soft_assertion_groups.insert(std::pair<std::string, std::unordered_set<size_t>>(grp_id, {index}));
            }
            else{
                context_.soft_assertion_groups[grp_id].insert(index);
            }
            context_.registerSoftAssertionGroupInScope(grp_id);
        }
    }
    // (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMaximize(){
        return parseSingleObj(OPT_KIND::OPT_MAXIMIZE);
    }
    // (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMinimize(){
        return parseSingleObj(OPT_KIND::OPT_MINIMIZE);
    }
    // (maxsat <expr> [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMaxsat(){
        return parseSingleObj(OPT_KIND::OPT_MAXSAT);
    }
    // (minsat <expr> [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMinsat(){
        return parseSingleObj(OPT_KIND::OPT_MINSAT);
    }
    std::shared_ptr<Objective> Parser::parseSingleObj(const OPT_KIND& opt_type){
        size_t key_ln = line_number;
        if (getObjectiveManager()->hasGomtObjectives()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "native objectives cannot be mixed with GOMT definitions", key_ln);
        }
        std::string comp = "";
        std::string epsilon = "";
        std::string M = "";
        std::string grp_id = "";
        size_t params_size = 4;
        KEYWORD key = KEYWORD::KW_NULL;
        for(size_t i=0;i<params_size;i++){
            key = attemptParseKeywords();
            if(key == KEYWORD::KW_NULL){ break; } // no :comp, :epsilon, :M or :id
            else if(key == KEYWORD::KW_COMP){
                // :comp
                comp = getSymbol();
            }
            else if(key == KEYWORD::KW_EPSILON){
                // :epsilon
                epsilon = getSymbol();
            }
            else if(key == KEYWORD::KW_M){
                // :M
                M = getSymbol();
            }
            else if(key == KEYWORD::KW_ID){
                // :id
                grp_id = getSymbol();
            }
            else{
                // error
                err_keyword("Error: wrong keywords at line ", key_ln);
            }
        }
        // OptiMathSAT activates a soft group by minimizing its implicit cost
        // symbol. Keep this as a group marker: adding a numeric objective as
        // well as the soft assertions would count the same cost twice.
        if (opt_type == OPT_KIND::OPT_MINIMIZE && *bufptr && *bufptr != '(' && *bufptr != ')') {
            char* saved = bufptr;
            const auto saved_mode = scan_mode;
            const size_t saved_line = line_number;
            const auto symbol = getSymbol();
            const auto identity = [](const std::string& name) {
                return name.size() >= 2 && name.front() == '|' && name.back() == '|'
                    ? name.substr(1, name.size() - 2) : name;
            };
            bool matched = false;
            std::string group;
            if (!isDeclaredVariable(symbol) && !isDeclaredFunction(symbol)) {
                for (const auto& entry : context_.soft_assertion_groups) {
                    if (identity(entry.first) == identity(symbol)) {
                        matched = true;
                        group = entry.first;
                        break;
                    }
                }
                if (!matched && identity(symbol) == "I") {
                    for (size_t i = 0; i < context_.soft_assertions.size(); ++i) {
                        bool grouped = false;
                        for (const auto& entry : context_.soft_assertion_groups) {
                            grouped = grouped || entry.second.count(i) != 0;
                        }
                        if (!grouped) { matched = true; break; }
                    }
                }
            }
            if (matched) {
                if (*bufptr != ')' || !comp.empty() || !epsilon.empty() || !M.empty() || !grp_id.empty()) {
                    err_all(ERROR_TYPE::ERR_PARAM_MIS,
                            "OptiMathSAT soft-group activation does not accept objective attributes", key_ln);
                }
                for (const auto& objective : getObjectives()) {
                    if (objective && objective->isMaxSAT() && objective->getGroupID() == group) {
                        err_all(ERROR_TYPE::ERR_PARAM_MIS,
                                "repeated OptiMathSAT soft-group activation is unsupported", key_ln);
                    }
                }
                return getObjectiveManager()->addSingleObjective(OPT_KIND::OPT_MAXSAT, group);
            }
            bufptr = saved;
            scan_mode = saved_mode;
            line_number = saved_line;
        }
        std::shared_ptr<DAGNode> min_expr = parseExpr();
        for(size_t i=0;i<params_size;i++){
            key = attemptParseKeywords();
            if(key == KEYWORD::KW_NULL){ break; } // no :comp, :epsilon, :M or :id
            else if(key == KEYWORD::KW_COMP){
                // :comp
                comp = getSymbol();
            }
            else if(key == KEYWORD::KW_EPSILON){
                // :epsilon
                epsilon = getSymbol();
            }
            else if(key == KEYWORD::KW_M){
                // :M
                M = getSymbol();
            }
            else if(key == KEYWORD::KW_ID){
                // :id
                grp_id = getSymbol();
            }
            else{
                // error
                err_keyword("Error: wrong keywords at line ", key_ln);
            }
        }

        if(opt_type == OPT_KIND::OPT_MAXSAT || opt_type == OPT_KIND::OPT_MINSAT){
            return getObjectiveManager()->addSingleObjective(opt_type, grp_id);
        }
        COMP_KIND comp_op = comp == "" ? getDefaultCompareOperator(getOptions()->logic, opt_type) : getCompareOperator(comp);
        std::shared_ptr<DAGNode> epsilon_node = epsilon == "" ? NodeManager::NULL_NODE : NodeManager::EPSILON_NODE;
        std::shared_ptr<DAGNode> M_node = M == "" ? NodeManager::NULL_NODE : NodeManager::INT_INF_NODE;
        return getObjectiveManager()->addSingleObjective(opt_type, min_expr, comp_op, epsilon_node, M_node, grp_id);
    }
    // NOTE: the most internal id will be used
    // (define-objective <symbol> signle_opt [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseDefObj(){
        if (!*bufptr || *bufptr == ')' || *bufptr == '(' || *bufptr == ':') {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "define-objective requires a name", line_number);
        }
        std::string obj_name = getSymbol();
        size_t key_ln = line_number;
        if (*bufptr != '(' && *bufptr != ':') {
            auto manager = getObjectiveManager();
            if (!context_.scope_stack_.empty()
                || ((!getObjectives().empty() || !context_.soft_assertions.empty())
                    && !manager->getSelectedGomtObjective())) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT definitions require an unmixed base scope", key_ln);
            }
            if (!*bufptr || *bufptr == ')' || manager->getGomtObjective(obj_name)) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "invalid or duplicate GOMT objective definition", key_ln);
            }
            const auto kind_name = getSymbol();
            OPT_KIND kind;
            if (kind_name == "OBJECTIVE_MIN") kind = OPT_KIND::OPT_MINIMIZE;
            else if (kind_name == "OBJECTIVE_MAX") kind = OPT_KIND::OPT_MAXIMIZE;
            else {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "unsupported GOMT objective kind " + kind_name, key_ln);
                return nullptr;
            }
            const auto term = parseExpr();
            if (*bufptr != ')' || !term || !term->getSort()
                || !(term->getSort()->isInt() || term->getSort()->isReal()
                     || term->getSort()->isBv() || term->getSort()->isFp())) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS,
                        "GOMT objective requires an Int/Real/BV/FP term without additional attributes", key_ln);
            }
            auto objective = manager->createObjective(kind, obj_name);
            objective->addObjective(std::make_shared<SingleObjective>(kind, term,
                getCompareOperatorForObjectiveTerm(term, kind), NodeManager::NULL_NODE,
                NodeManager::NULL_NODE, obj_name));
            manager->registerGomtObjective(obj_name, objective);
            return objective;
        }
        std::string grp_id = "";
        KEYWORD key = attemptParseKeywords();
        if(key == KEYWORD::KW_ID){
            grp_id = getSymbol();
        }
        // single_opt
        parseLpar();
        std::shared_ptr<Objective> objective = nullptr;
        std::string opt_type = getSymbol();
        if(opt_type == "maximize"){
            objective = parseMaximize();
        }
        else if(opt_type == "minimize"){
            objective = parseMinimize();
        }
        else{
            err_unkwn_sym("Objective type", key_ln);
        }
        parseRpar();
        // mk objective
        getObjectiveManager()->registerNamed(obj_name, objective);
        return objective;
    }

    void Parser::parseGomtMultiObjective() {
        const size_t key_ln = line_number;
        auto manager = getObjectiveManager();
        if (!context_.scope_stack_.empty()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT definitions inside push scopes are unsupported", key_ln);
        }
        if (!*bufptr || *bufptr == ')' || *bufptr == '(') {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "define-multi-objective requires a name", key_ln);
        }
        const auto name = getSymbol();
        if (!*bufptr || *bufptr == ')' || manager->getGomtObjective(name)) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "invalid or duplicate GOMT multi-objective", key_ln);
        }
        const auto kind_name = getSymbol();
        OPT_KIND kind;
        if (kind_name == "OBJECTIVE_LEX") kind = OPT_KIND::OPT_LEX_OPTIMIZE;
        else if (kind_name == "OBJECTIVE_PARETO") kind = OPT_KIND::OPT_PARETO_OPTIMIZE;
        else if (kind_name == "OBJECTIVE_BOX") kind = OPT_KIND::OPT_BOX_OPTIMIZE;
        else if (kind_name == "OBJECTIVE_MINMAX") kind = OPT_KIND::OPT_MINMAX;
        else if (kind_name == "OBJECTIVE_MAXMIN") kind = OPT_KIND::OPT_MAXMIN;
        else {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "unsupported GOMT multi-objective kind " + kind_name, key_ln);
            return;
        }
        auto objective = manager->createObjective(kind, name);
        std::unordered_set<const Objective*> members;
        while (*bufptr && *bufptr != ')') {
            if (*bufptr == ':' || *bufptr == '(') {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT multi-objective expects bare member names without attributes", key_ln);
            }
            const auto member = manager->getGomtObjective(getSymbol());
            if (!member || !member->isSingleObjective() || !members.insert(member.get()).second) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT multi-objective requires distinct previously defined scalar members", key_ln);
            }
            objective->addObjective(member);
        }
        if (*bufptr != ')' || members.empty()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT multi-objective requires at least one member", key_ln);
        }
        manager->registerGomtObjective(name, objective);
    }

    void Parser::parseGomtMaxSmtObjective() {
        const size_t key_ln = line_number;
        auto manager = getObjectiveManager();
        if (!context_.scope_stack_.empty()
            || ((!getObjectives().empty() || !context_.soft_assertions.empty())
                && !manager->getSelectedGomtObjective())) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "GOMT definitions require an unmixed base scope", key_ln);
        }
        if (!*bufptr || *bufptr == ')' || *bufptr == '(') {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "define-maxsmt-objective requires a name", key_ln);
        }
        const auto name = getSymbol();
        if (*bufptr != ')' || manager->getGomtObjective(name)) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "invalid, attributed or duplicate GOMT MaxSMT definition", key_ln);
        }
        auto objective = manager->createObjective(OPT_KIND::OPT_MAXSAT, name);
        objective->addObjective(std::make_shared<SingleObjective>(OPT_KIND::OPT_MAXSAT, name));
        manager->registerGomtObjective(name, objective);
    }

    void Parser::parseGomtOptimizeSat() {
        const size_t key_ln = line_number;
        if (!context_.scope_stack_.empty() || !*bufptr || *bufptr == ')' || *bufptr == '(') {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "optimize-sat requires one objective name at the base scope", key_ln);
        }
        const auto name = getSymbol();
        auto manager = getObjectiveManager();
        const auto selected = manager->getGomtObjective(name);
        std::vector<std::shared_ptr<DAGNode>> assumptions;
        while (*bufptr == ':') {
            const auto attribute = getSymbol();
            if (attribute != ":assumption") {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "unsupported optimize-sat attribute " + attribute, key_ln);
            }
            const auto term = parseExpr();
            if (!term || !term->getSort() || !term->getSort()->isBool()) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "optimize-sat assumption must be Boolean", key_ln);
            }
            assumptions.push_back(term);
        }
        if (*bufptr != ')' || !selected) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "optimize-sat requires one previously defined GOMT objective", key_ln);
        }
        std::vector<std::shared_ptr<MetaObjective>> members;
        if (selected->isMultiObjective()) {
            for (size_t i = 0; i < selected->getObjectiveSize(); ++i) {
                members.push_back(selected->getObjective(i));
            }
        } else members.push_back(selected);
        for (const auto& member : members) {
            if (member->isMaxSAT() && manager->getGomtSoftAssertions(member->getGroupID()).empty()) {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "selecting an empty GOMT MaxSMT objective is unsupported", key_ln);
            }
        }
        manager->selectGomtObjective(name);
        context_.soft_assertions.clear();
        context_.soft_weights.clear();
        context_.soft_assertion_groups.clear();
        context_.soft_objective_positions.clear();
        for (const auto& member : members) {
            if (!member->isMaxSAT()) continue;
            const auto& group = member->getGroupID();
            for (const auto& soft : manager->getGomtSoftAssertions(group)) {
                const size_t index = context_.soft_assertions.size();
                context_.soft_assertions.push_back(soft.node);
                context_.soft_weights.push_back(soft.weight);
                context_.soft_objective_positions.push_back(0);
                context_.soft_assertion_groups[group].insert(index);
            }
        }
        if (!assumptions.empty()) context_.assumptions.push_back(std::move(assumptions));
        getOptions()->check_sat = true;
    }

    void Parser::parseObjectiveValueTerms() {
        parseLpar();
        while (*bufptr && *bufptr != ')') {
            std::shared_ptr<Objective> objective;
            if (*bufptr != '(') {
                char* saved = bufptr;
                const auto saved_mode = scan_mode;
                const size_t saved_line = line_number;
                objective = getObjectiveManager()->getGomtObjective(getSymbol());
                if (!objective) {
                    bufptr = saved;
                    scan_mode = saved_mode;
                    line_number = saved_line;
                }
            }
            if (!objective) {
                auto term = parseExpr();
                if (term) pending_value_terms_.push_back(term);
            } else if (objective->isMinimize() || objective->isMaximize()) {
                pending_value_terms_.push_back(objective->getObjectiveTerm());
            } else if (objective->isMaxSAT()) {
                std::vector<std::shared_ptr<DAGNode>> costs;
                for (const auto& soft : getObjectiveManager()->getGomtSoftAssertions(objective->getGroupID())) {
                    const auto zero = soft.weight->getSort()->isReal() ? mkConstReal(std::string("0.0")) : mkConstInt(0);
                    costs.push_back(mkIte(soft.node, zero, soft.weight));
                }
                pending_value_terms_.push_back(costs.empty() ? mkConstInt(0) : mkAdd(costs));
            } else {
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "get-value of a compound GOMT objective is not scalar", line_number);
            }
        }
        parseRpar();
        if (*bufptr != ')') {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "get-value requires one term list", line_number);
        }
    }

    std::shared_ptr<Objective> Parser::parseMultiObj(const OPT_KIND& opt_type){
        if (getObjectiveManager()->hasGomtObjectives()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "native objectives cannot be mixed with GOMT definitions", line_number);
        }
        std::string grp_id = "";
        KEYWORD key = attemptParseKeywords();
        if(key == KEYWORD::KW_ID){
            grp_id = getSymbol();
        }
        // (<symbol>+)
        parseLpar();
        std::vector<std::string> obj_names;
        while(*bufptr != ')'){
            obj_names.emplace_back(getSymbol());
        }
        parseRpar();
        
        key = attemptParseKeywords();
        if(key == KEYWORD::KW_ID){
            std::string grp_id = getSymbol();
        }
        
        // mk multi-objective
        std::shared_ptr<Objective> objective = getObjectiveManager()->createObjective(opt_type, grp_id);
        for(auto& obj_name : obj_names){
            objective->addObjective(getObjectiveManager()->getObjective(obj_name));
        }
        getObjectiveManager()->addObjective(objective);
        return objective;
    }
    // (lex-optimize (<symbol>+) [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseLexOpt(){
        return parseMultiObj(OPT_KIND::OPT_LEX_OPTIMIZE);
    }
    // (pareto-optimize (<symbol>+) [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseParetoOpt(){
        return parseMultiObj(OPT_KIND::OPT_PARETO_OPTIMIZE);
    }
    // (box-optimize (<symbol>+) [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseBoxOpt(){
        return parseMultiObj(OPT_KIND::OPT_BOX_OPTIMIZE);
    }
    // (minmax (<symbol>+) [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMinmax(){
        return parseMultiObj(OPT_KIND::OPT_MINMAX);
    }
    // (maxmin (<symbol>+) [:id <symbol>])
    std::shared_ptr<Objective> Parser::parseMaxmin(){
        return parseMultiObj(OPT_KIND::OPT_MAXMIN);
    }

    // (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
    std::shared_ptr<Objective> Parser::parseOptimize(){
        size_t key_ln = line_number;
        if (getObjectiveManager()->hasGomtObjectives()) {
            err_all(ERROR_TYPE::ERR_PARAM_MIS, "native objectives cannot be mixed with GOMT definitions", key_ln);
        }
        std::string grp_id = "";
        std::string opt_kind = "";
        size_t params_size = 4;
        KEYWORD key = KEYWORD::KW_NULL;
        for(size_t i=0;i<params_size;i++){
            key = attemptParseKeywords();
            if(key == KEYWORD::KW_NULL){ break; } // no :id or :opt_kind
            else if(key == KEYWORD::KW_ID){
                // :id
                grp_id = getSymbol();
            }
            else if(key == KEYWORD::KW_OPT_KIND){
                // :opt_kind
                opt_kind = getSymbol();
            }
            else{
                // error
                err_keyword("Error: wrong keywords at line ", key_ln);
            }
        }

        // (<symbol>+)
        parseLpar();
        std::vector<std::string> obj_names;
        while(*bufptr != ')'){
            obj_names.emplace_back(getSymbol());
        }
        parseRpar();
        
        for(size_t i=0;i<params_size;i++){
            key = attemptParseKeywords();
            if(key == KEYWORD::KW_NULL){ break; } // no :id or :opt_kind
            else if(key == KEYWORD::KW_ID){
                // :id
                grp_id = getSymbol();
            }
            else if(key == KEYWORD::KW_OPT_KIND){
                // :opt_kind
                opt_kind = getSymbol();
            }
            else{
                // error
                err_keyword("Error: wrong keywords at line ", key_ln);
            }
        }

        // mk multi-objective (not added to list; caller may use returned objective)
        std::shared_ptr<Objective> objective = getObjectiveManager()->createObjective(
            opt_kind == "" ? OPT_KIND::OPT_LEX_OPTIMIZE : getOptKind(opt_kind), grp_id);
        for(auto& obj_name : obj_names){
            objective->addObjective(getObjectiveManager()->getObjective(obj_name));
        }
        return objective;
    }
}
