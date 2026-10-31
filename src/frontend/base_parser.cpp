/* -*- Source -*-
 *
 * An SMT/OMT Parser (Base part)
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
#include "somtparser/core/timing.h"
#include "somtparser/translation/translate.h"
#include "somtparser/lowering/optimathsat_array_lowering.h"
#include "somtparser/lowering/z3_finite_set_lowering.h"
#include <fstream>
#include <queue>
#include <stack>
#include <algorithm>
#include <functional>
#include <new>
#include <sstream>
#include <stdexcept>
#include <unordered_set>
#include <utility>

namespace SOMTParser{

namespace {

/** A datatype's `par` parameters shadow sort names only while its constructor
 *  declaration is parsed. Keep those bindings out of SymbolManager's
 *  top-level declaration order and restore outer bindings even on parse error. */
class ScopedSortBindings {
public:
    explicit ScopedSortBindings(std::shared_ptr<SymbolManager> symbols,
                                std::size_t capacity)
        : symbols_(std::move(symbols)) {
        saved_.reserve(capacity);
    }

    ScopedSortBindings(const ScopedSortBindings&) = delete;
    ScopedSortBindings& operator=(const ScopedSortBindings&) = delete;

    ~ScopedSortBindings() {
        for (auto it = saved_.rbegin(); it != saved_.rend(); ++it) {
            symbols_->restoreTemporarySort(it->first, it->second);
        }
    }

    void bind(const std::string& name, const std::shared_ptr<Sort>& sort) {
        // Record before mutating the map so allocation failure cannot leave an
        // untracked temporary binding behind.
        saved_.emplace_back(name, nullptr);
        saved_.back().second = symbols_->bindTemporarySort(name, sort);
    }

private:
    std::shared_ptr<SymbolManager> symbols_;
    std::vector<std::pair<std::string, std::shared_ptr<Sort>>> saved_;
};

/** Quantifier and pattern variables share the lexical term stack with lets.
 *  Separate name maps alone cannot decide which kind of binder is innermost. */
class ScopedTermBindings {
public:
    explicit ScopedTermBindings(std::shared_ptr<SymbolManager> symbols)
        : symbols_(std::move(symbols)) {
        symbols_->pushLetScope();
    }
    ScopedTermBindings(const ScopedTermBindings&) = delete;
    ScopedTermBindings& operator=(const ScopedTermBindings&) = delete;
    ~ScopedTermBindings() {
        symbols_->popLetScope();
        symbols_->popQuantScope(names_);
    }
    void bind(const std::string& name, const std::shared_ptr<DAGNode>& node) {
        names_.push_back(name);
        symbols_->registerQuantVar(name, node);
        symbols_->registerLet(name, node);
    }
private:
    std::shared_ptr<SymbolManager> symbols_;
    std::vector<std::string> names_;
};

} // namespace

	// Response/control commands a consumer must replay in source order to answer
	// an interactive script (echo / get-* / check-sat). These are FEW per script,
	// so they are ALWAYS recorded in the Script even when command_logging_ is off
	// — that keeps the full command log (which also captures the bulk
	// assert/declare commands) opt-in, avoiding per-assert memory on large files.
	static bool isResponseCommand(CMD_TYPE t) {
		switch (t) {
			case CMD_TYPE::CT_ECHO:
			case CMD_TYPE::CT_GET_INFO:
			case CMD_TYPE::CT_GET_VALUE:
			case CMD_TYPE::CT_GET_ASSIGNMENT:
			case CMD_TYPE::CT_GET_MODEL:
			case CMD_TYPE::CT_GET_OBJECTIVES:
			case CMD_TYPE::CT_GET_OPTION:
			case CMD_TYPE::CT_GET_PROOF:
			case CMD_TYPE::CT_GET_ASSERTIONS:
			case CMD_TYPE::CT_GET_UNSAT_CORE:
			case CMD_TYPE::CT_GET_UNSAT_ASSUMPTIONS:
			case CMD_TYPE::CT_CHECK_SAT:
			case CMD_TYPE::CT_CHECK_SAT_ASSUMING:
				return true;
			default:
				return false;
		}
	}

	Parser::Parser(){
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;
		let_nesting_depth = 0;
		parsing_file = false;
		in_quantifier_scope = false;
		allow_placeholder_vars = false;
		placeholder_var_sort = nullptr;
		quant_nesting_depth = 0;
		context_.setNodeManager(std::make_shared<NodeManager>());
		context_.setSortManager(std::make_shared<SortManager>());
		auto sym_mgr = std::make_shared<SymbolManager>();
		sym_mgr->reserve(1024);
		context_.setSymbolManager(std::move(sym_mgr));
		context_.setObjectiveManager(std::make_shared<ObjectiveManager>());
		context_.setOptions(std::make_shared<GlobalOptions>());

		// array cache
		array_select_cache.reserve(1024);
		array_normalize_cache.reserve(1024);
	}

	
	bool Parser::parse(const std::string& filename){
		return parseSmtlib2File(filename);
	}

	Parser::Parser(const std::string& filename) {
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		line_number = 0;
		scan_mode = SCAN_MODE::SM_COMMON;
		let_nesting_depth = 0;
		parsing_file = true;
		in_quantifier_scope = false;
		allow_placeholder_vars = false;
		placeholder_var_sort = nullptr;
		quant_nesting_depth = 0;
		context_.setNodeManager(std::make_shared<NodeManager>());
		context_.setSortManager(std::make_shared<SortManager>());
		auto sym_mgr = std::make_shared<SymbolManager>();
		sym_mgr->reserve(1024);
		context_.setSymbolManager(std::move(sym_mgr));
		context_.setObjectiveManager(std::make_shared<ObjectiveManager>());
		context_.setOptions(std::make_shared<GlobalOptions>());

		// array cache
		array_select_cache.reserve(1024);
		array_normalize_cache.reserve(1024);

		parseSmtlib2File(filename);
	}

	Parser::~Parser() {
		delete[] buffer;
	}

	RESULT_TYPE Parser::getResultType(){
		return result_type;
	}

	std::shared_ptr<DAGNode> Parser::getResult(){
		return result_node;
	}
	
	RESULT_TYPE Parser::checkSat(){
		if(result_type != RESULT_TYPE::RT_UNKNOWN){
			return result_type;
		}

		// simple check
		bool all_true = true;
		for(auto& assertion : context_.assertions){
			if(assertion->isErr()){
				result_type = RESULT_TYPE::RT_ERROR;
				return result_type;
			}
			else if(assertion->isFalse()){
				all_true = false;
				result_type = RESULT_TYPE::RT_UNSAT;
				return result_type;
			}
			else if(assertion->isTrue()){
				continue;
			}
			else{
				// unknown assertion
				result_type = RESULT_TYPE::RT_UNKNOWN;
				return result_type;
			}
		}
		if(all_true){
			result_type = RESULT_TYPE::RT_SAT;
		}
		return result_type;
	}
	
	std::shared_ptr<Model> Parser::getModel(){
		return result_model;
	}

	size_t Parser::getNodeCount(){
		// return getNodeManager()->size();
		// BFS to count the number of nodes
		// only count the nodes in assertions, assumptions, soft_assertions, soft_weights, objectives
		std::unordered_set<std::shared_ptr<DAGNode>> visited;
		std::queue<std::shared_ptr<DAGNode>> q;
		for(size_t i=0;i<context_.assertions.size();i++){
			auto node = context_.assertions[i];
			q.push(node);
			visited.insert(node);
		}
		for(size_t i=0;i<context_.assumptions.size();i++){
			for(size_t j=0;j<context_.assumptions[i].size();j++){
				auto node = context_.assumptions[i][j];
				q.push(node);
				visited.insert(node);
			}
		}
		for(size_t i=0;i<context_.soft_assertions.size();i++){
			auto node = context_.soft_assertions[i];
			q.push(node);
			visited.insert(node);
		}
		for(size_t i=0;i<context_.soft_weights.size();i++){
			auto node = context_.soft_weights[i];
			q.push(node);
			visited.insert(node);
		}
		for (const auto& obj : context_.getObjectives()) {
			auto node = obj->getObjectiveTerm();
			q.push(node);
			visited.insert(node);
		}
		while(!q.empty()){
			auto node = q.front();
			q.pop();
			for(size_t i=0;i<node->getChildrenSize();i++){
				auto child = node->getChild(i);
				if(visited.find(child) == visited.end()){
					visited.insert(child);
					q.push(child);
				}
			}
		}
		return visited.size();
	}
	
	// to solver
	Context& Parser::context() {
		return context_;
	}
	const Context& Parser::context() const {
		return context_;
	}

	std::vector<std::shared_ptr<DAGNode>> Parser::getAssertions() const{
		return context_.getAssertions();
	}
	std::unordered_map<std::string, std::unordered_set<size_t>> Parser::getGroupedAssertions() const{
		return context_.getGroupedAssertions();
	}
	std::unordered_map<std::string, std::shared_ptr<DAGNode>> Parser::getNamedAssertions() const{
		return context_.getNamedAssertions();
	}
	std::vector<std::vector<std::shared_ptr<DAGNode>>> Parser::getAssumptions() const{
		return context_.getAssumptions();
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getSoftAssertions() const{
		return context_.getSoftAssertions();
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getSoftWeights() const{
		return context_.getSoftWeights();
	}
	std::unordered_map<std::string, std::unordered_set<size_t>> Parser::getGroupedSoftAssertions() const{
		return context_.getGroupedSoftAssertions();
	}
	std::vector<std::shared_ptr<Objective>> Parser::getObjectives() const{
		return context_.getObjectives();
	}
	
	void Parser::setOption(const std::string& key, const std::string& value){
		getOptions()->setOption(key, value);
	}
	void Parser::setOption(const std::string& key, const char* value){
		getOptions()->setOption(key, value ? std::string(value) : std::string());
	}
	void Parser::setOption(const std::string& key, const int& value){
		getOptions()->setOption(key, std::to_string(value));
	}
	void  Parser::setOption(const std::string& key, const double& value){
		getOptions()->setOption(key, std::to_string(value));
	}
	void Parser::setOption(const std::string& key, const bool& value){
		getOptions()->setOption(key, value?"true":"false");
	}
	// Declaration order, not hash order: these feed dumpSMT2, and iterating the
	// underlying unordered_map produced a variable order unrelated to the input,
	// so dumping a query and re-parsing it did not converge.
	std::vector<std::shared_ptr<DAGNode>> Parser::getVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		const auto& var_names = getSymbolManager()->getVarNames();
		for(const auto& name : getSymbolManager()->getVarOrder()){
			auto it = var_names.find(name);
			if(it != var_names.end()) vars.emplace_back(it->second);
		}
		const auto& temp_names = getSymbolManager()->getTempVarNames();
		for(const auto& name : getSymbolManager()->getTempVarOrder()){
			auto it = temp_names.find(name);
			if(it != temp_names.end()) vars.emplace_back(it->second);
		}
		return vars;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getDeclaredVariables() const{
		std::vector<std::shared_ptr<DAGNode>> vars;
		const auto& var_names = getSymbolManager()->getVarNames();
		for(const auto& name : getSymbolManager()->getVarOrder()){
			auto it = var_names.find(name);
			if(it != var_names.end()) vars.emplace_back(it->second);
		}
		return vars;
	}

	// Sort-classified variable accessors
	std::vector<std::shared_ptr<DAGNode>> Parser::getBoolVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isBool()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getIntVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isInt()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getRealVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isReal()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getBvVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isBv()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getFpVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isFp()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getRoundingModeVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isRoundingMode()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getArrayVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isArray()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getDatatypeVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isDatatype()) out.emplace_back(kv.second);
		return out;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getStringVars() const{
		std::vector<std::shared_ptr<DAGNode>> out;
		for(const auto& kv : getSymbolManager()->getVarNames())
			if(kv.second->getSort() && kv.second->getSort()->isStr()) out.emplace_back(kv.second);
		return out;
	}
	size_t Parser::getNumBoolVars() const{ return getBoolVars().size(); }
	size_t Parser::getNumIntVars() const{ return getIntVars().size(); }
	size_t Parser::getNumRealVars() const{ return getRealVars().size(); }
	size_t Parser::getNumBvVars() const{ return getBvVars().size(); }
	size_t Parser::getNumFpVars() const{ return getFpVars().size(); }
	size_t Parser::getNumRoundingModeVars() const{ return getRoundingModeVars().size(); }
	size_t Parser::getNumArrayVars() const{ return getArrayVars().size(); }
	size_t Parser::getNumDatatypeVars() const{ return getDatatypeVars().size(); }
	size_t Parser::getNumStringVars() const{ return getStringVars().size(); }

    bool Parser::isRecursiveDatatype(const std::shared_ptr<Sort>& dt_sort) const {
        if (!dt_sort || !dt_sort->isDatatype()) return false;
        const std::string& target = dt_sort->name;
        std::unordered_set<std::string> visited;
        std::vector<std::shared_ptr<Sort>> pending;
        for (const auto& ctor : dt_sort->getDtConstructors())
            for (const auto& selector : ctor.selectors) pending.push_back(selector.sort);
        while (!pending.empty()) {
            auto current = std::move(pending.back());
            pending.pop_back();
            if (!current || !current->isDatatype()) continue;
            if (current->name == target) return true;
            if (!visited.insert(current->name).second) continue;
            for (const auto& ctor : current->getDtConstructors())
                for (const auto& selector : ctor.selectors) pending.push_back(selector.sort);
        }
        return false;
    }

    std::shared_ptr<DAGNode> Parser::mkDefaultDTValue(const std::shared_ptr<Sort>& dt_sort) {
        if (!dt_sort || !dt_sort->isDatatype()) return nullptr;
        // The active set belongs to the current constructor path, not to
        // siblings. Repeated selector sorts are independent finite values.
        struct Frame {
            std::shared_ptr<Sort> sort;
            std::size_t constructor = 0;
            std::vector<std::shared_ptr<DAGNode>> args{};
            bool entered = false;
            bool awaiting = false;
        };
        std::vector<Frame> pending{{dt_sort}};
        std::unordered_set<std::string> active;
        std::shared_ptr<DAGNode> result;
        auto finish = [&](std::shared_ptr<DAGNode> value) {
            if (pending.back().entered) active.erase(pending.back().sort->name);
            pending.pop_back();
            result = std::move(value);
        };
        while (!pending.empty()) {
            auto& frame = pending.back();
            if (!frame.entered) {
                if (!frame.sort) { finish(nullptr); continue; }
                if (!frame.sort->isDatatype()) {
                    auto zero = getZero(frame.sort);
                    finish(zero && !zero->isErr() ? zero : nullptr);
                    continue;
                }
                if (!active.insert(frame.sort->name).second) { finish(nullptr); continue; }
                frame.entered = true;
                const auto& constructors = frame.sort->getDtConstructors();
                auto nullary = std::find_if(constructors.begin(), constructors.end(),
                    [](const auto& constructor) { return constructor.selectors.empty(); });
                if (nullary != constructors.end()) {
                    finish(getNodeManager()->createNode(frame.sort, NODE_KIND::NT_DT_CONSTRUCTOR,
                                                        nullary->name, {}));
                    continue;
                }
            }
            if (frame.awaiting) {
                frame.awaiting = false;
                if (result) frame.args.push_back(std::move(result));
                else { ++frame.constructor; frame.args.clear(); }
            }
            const auto& constructors = frame.sort->getDtConstructors();
            if (frame.constructor == constructors.size()) { finish(nullptr); continue; }
            const auto& constructor = constructors[frame.constructor];
            if (frame.args.size() == constructor.selectors.size()) {
                finish(getNodeManager()->createNode(frame.sort, NODE_KIND::NT_DT_CONSTRUCTOR,
                                                    constructor.name, frame.args));
                continue;
            }
            auto child_sort = constructor.selectors[frame.args.size()].sort;
            frame.awaiting = true;
            pending.push_back({std::move(child_sort)});
        }
        return result;
    }

	std::shared_ptr<DAGNode> Parser::getVariable(const std::string& var_name){
		std::shared_ptr<DAGNode> v = getSymbolManager()->getVar(var_name);
		if(v) return v;
		v = getSymbolManager()->getTempVar(var_name);
		return v ? v : NodeManager::NULL_NODE;
	}
	std::vector<std::shared_ptr<DAGNode>> Parser::getFunctions() const{
		return getSymbolManager()->getFunctions();
	}
	void Parser::setEvaluatePrecision(mpfr_prec_t precision){
		getOptions()->setEvaluatePrecision(precision);
	}
	mpfr_prec_t Parser::getEvaluatePrecision() const{
		return getOptions()->getEvaluatePrecision();
	}
	void Parser::setEvaluateUseFloating(bool use_floating){
		getOptions()->setEvaluateUseFloating(use_floating);
	}
	bool Parser::getEvaluateUseFloating() const{
		return getOptions()->getEvaluateUseFloating();
	}
	void Parser::setStrictSmtlib(bool strict){
		getOptions()->setStrictSmtlib(strict);
	}
	bool Parser::getStrictSmtlib() const{
		return getOptions()->getStrictSmtlib();
	}
	Real Parser::toReal(std::shared_ptr<DAGNode> expr){
		ensureNumberValue(expr);
		condAssert(expr->isCReal() || expr->isCInt(), "Cannot convert non-constant expression to real");
		if(expr->isPi()) return Real::pi(getEvaluatePrecision());
		if(expr->isE()) return Real::e(getEvaluatePrecision());
		auto value = expr->getValue();
		if(value == nullptr) {
			// If value is still nullptr after ensureNumberValue, return 0 as default
			// This can happen if the expression cannot be converted to a number
			return Real(0, getEvaluatePrecision());
		}
		return value->getNumberValue().toReal(getEvaluatePrecision());
	}
	Integer Parser::toInt(std::shared_ptr<DAGNode> expr){
		ensureNumberValue(expr);
		condAssert(expr->isCInt(), "Cannot convert non-integer expression to integer");
		auto value = expr->getValue();
		if(value == nullptr) {
			// If value is still nullptr after ensureNumberValue, return 0 as default
			// This can happen if the expression cannot be converted to a number
			return Integer(0);
		}
		auto opt = value->getNumberValue().asIntegerExact();
			condAssert(opt.has_value(), "Real constant cannot be coerced to integer");
			return opt.value();
	}
	bool Parser::isZero(std::shared_ptr<DAGNode> expr){
		// cannot check zero for root-obj and root-of-with-interval
		if(expr->isCRootObj()) return false;
		if(expr->isCRootOfWithInterval()) return false;
		// otherwise, check zero
		if(expr->isCReal()) return toReal(expr) == 0.0;
		if(expr->isCInt()) return toInt(expr) == 0;
		return false;
	}
	bool Parser::isOne(std::shared_ptr<DAGNode> expr){
		if(expr->isCReal()) return toReal(expr) == 1.0;
		if(expr->isCInt()) return toInt(expr) == 1;
		return false;
	}

	void Parser::ensureNumberValue(std::shared_ptr<DAGNode> expr){
		if(!expr || !expr->isConst()) return;
		if(expr->getValue()!=nullptr) return;

		std::string s = expr->toString();
		try{
			if(TypeChecker::isInt(s)){
				Integer i(s);
				expr->setValue(i);
			}
			else if(TypeChecker::isReal(s)){
				// Store as exact rational instead of approximate MPFR
				Number n(s, false);
				expr->setValue(n);
			}
		} catch (const std::bad_alloc&) {
			throw;
		}catch(...){
			// raise error
			err_all(expr, "Cannot convert non-number expression to number", line_number);
		}
	}

	// parse smt-lib2 file
	std::string Parser::getSymbol() {
		condAssert(!buffer || (bufptr >= buffer && bufptr <= buffer + buflen), "getSymbol: buffer bounds");
		char *beg = bufptr;
		bool in_scientific_notation = false;
		bool has_open_bracket = false;
		int bracket_level = 0;

		// first char was already scanned
		bufptr++;

		// while not eof	
		while (*bufptr != 0) {

			switch (scan_mode) {
			case SCAN_MODE::SM_SYMBOL:
				// check if in scientific notation mode
				if (!in_scientific_notation) {
					// check if current symbol is the start of scientific notation
					std::string current(beg, bufptr - beg);
					size_t e_pos = current.find_first_of("Ee");
					if (e_pos != std::string::npos && e_pos > 0 && e_pos == current.size() - 1) {
						// check if the part before E is a valid real number
						std::string mantissa = current.substr(0, e_pos);
						if (TypeChecker::isReal(mantissa)) {
							// confirm the start of scientific notation
							in_scientific_notation = true;
						}
					}
				}

				// if in scientific notation mode
				if (in_scientific_notation) {
					// handle left parenthesis
					if (*bufptr == '(') {
						has_open_bracket = true;
						bracket_level++;
						bufptr++;
						continue;
					}
					// handle right parenthesis
					else if (*bufptr == ')' && has_open_bracket) {
						bracket_level--;
						if (bracket_level == 0) {
							// right parenthesis matched, end scientific notation
							bufptr++;
							std::string tmp_s(beg, bufptr - beg);
							scanToNextSymbol();
							return tmp_s;
						}
						bufptr++;
						continue;
					}
					// handle right parenthesis when no open bracket — end of symbol
					else if (*bufptr == ')' && !has_open_bracket) {
						std::string tmp_s(beg, bufptr - beg);
						return tmp_s;
					}
					// handle space, allow space in scientific notation mode
					else if (isblank(*bufptr)) {
						bufptr++;
						continue;
					}
					// if encounter newline or other special characters, end scientific notation mode
					else if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f' ||
							 *bufptr == ';' || *bufptr == '|' || *bufptr == '"') {
						in_scientific_notation = false;
						// return the parsed part
						std::string tmp_s(beg, bufptr - beg);
						return tmp_s;
					}
				}
				// normal symbol parsing
				else {
					if (isblank(*bufptr)) {
						// out of symbol mode by ' ' and \t
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						bufptr++;
						scanToNextSymbol();
						return tmp_s;
					}
					else if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
						line_number++;
						// out of symbol mode by '\n', '\r', '\v' and '\f'
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						bufptr++;
						scanToNextSymbol();
						return tmp_s;
					}
					else if (*bufptr == ';' || *bufptr == '|' || *bufptr == '"' || *bufptr == '(' || *bufptr == ')') {
						// out of symbol mode by ';', '|', '"', '(' and ')'
						std::string tmp_s(beg, bufptr - beg);
						return tmp_s;
					}
				}
				break;

			case SCAN_MODE::SM_COMP_SYM:
				if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
					line_number++;
				}
				else if (*bufptr == '|') {
					// out of complicated symbol mode
					bufptr++;
					std::string tmp_s(beg, bufptr - beg);
					// skip space
					scanToNextSymbol();
					return tmp_s;
				}
				break;

			case SCAN_MODE::SM_STRING:
				if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
					line_number++;
				}
				else if (*bufptr == '"') {
					// process the nested quotes - check if it is an escape quote
					if (bufptr + 1 < buffer + buflen && *(bufptr + 1) == '"') {
						// two consecutive quotes are escape quotes, skip the second quote
						bufptr++;
					} else {
						// end of string
						bufptr++;
						std::string tmp_s(beg, bufptr - beg);
						// skip space
						scanToNextSymbol();
						return tmp_s;
					}
				}
				break;

			default:
				condAssert(false, "Invalid scan mode");
			}

			// go next char
			bufptr++;
		}

		if(parsing_file){
			err_unexp_eof();
		}
		else{
			std::string tmp_s(beg, bufptr - beg);
			// skip space
			scanToNextSymbol();
			return tmp_s;
		}

		return "";
	}

	void Parser::scanToNextSymbol() {
		condAssert(!buffer || (bufptr >= buffer && bufptr <= buffer + buflen), "scanToNextSymbol: buffer bounds");
		// init scan mode
		scan_mode = SCAN_MODE::SM_COMMON;

		// while not eof
		while (*bufptr != 0) {

			if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {

				line_number++;

				// out of comment mode
				if (scan_mode == SCAN_MODE::SM_COMMENT) scan_mode = SCAN_MODE::SM_COMMON;

			}
			else if (scan_mode == SCAN_MODE::SM_COMMON && !isblank(*bufptr)) {

				switch (*bufptr) {
				case ';':
					// encounter comment
					scan_mode = SCAN_MODE::SM_COMMENT;
					break;
				case '|':
					// encounter next complicated symbol
					scan_mode = SCAN_MODE::SM_COMP_SYM;
					return;
				case '"':
					// encounter next std::string
					scan_mode = SCAN_MODE::SM_STRING;
					return;
				default:
					// encounter next symbol
					scan_mode = SCAN_MODE::SM_SYMBOL;
					return;
				}

			}

			// go next char
			bufptr++;
		}

	}

	void Parser::parseLpar() {
		if (*bufptr == '(') {
			bufptr++;
			scanToNextSymbol();
		}
		else {
			err_sym_mis("(", line_number);
		}
	}

	void Parser::parseRpar() {
		if (*bufptr == ')') {
			bufptr++;
			scanToNextSymbol();
		}
		else {
			err_sym_mis(")", line_number);
		}
	}

	void Parser::skipToRpar() {

		// skip to next right parenthesis with same depth	
		scan_mode = SCAN_MODE::SM_COMMON;
		size_t level = 0;

		while (*bufptr != 0) {

			if (*bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
				// new line
				line_number++;
				if (scan_mode == SCAN_MODE::SM_COMMENT)
					scan_mode = SCAN_MODE::SM_COMMON;
			}
			else if (scan_mode == SCAN_MODE::SM_COMMON) {

				if (*bufptr == '(') level++;
				else if (*bufptr == ')') {
					if (level == 0) return;
					else level--;
				}
				else if (*bufptr == ';')
					scan_mode = SCAN_MODE::SM_COMMENT;
				else if (*bufptr == '|')
					scan_mode = SCAN_MODE::SM_COMP_SYM;
				else if (*bufptr == '"')
					scan_mode = SCAN_MODE::SM_STRING;

			}
			else if (scan_mode == SCAN_MODE::SM_COMP_SYM && *bufptr == '|')
				scan_mode = SCAN_MODE::SM_COMMON;
			else if (scan_mode == SCAN_MODE::SM_STRING && *bufptr == '"')
				scan_mode = SCAN_MODE::SM_COMMON;

			// go to next char
			bufptr++;
		}

	}

	// parse smt-lib2 file
	bool Parser::parseSmtlib2File(const std::string filename) {

		/*
		load file -- an empty name or "-" reads the script from stdin, so the
		parser can be used in a pipeline. Ported from the SMTStabilizer fork.
		*/
		delete[] buffer;
		buffer = nullptr;

		if (filename.empty() || filename == "-") {
			std::string content((std::istreambuf_iterator<char>(std::cin)),
			                    std::istreambuf_iterator<char>());
			buflen = (long)content.size();
			buffer = new char[buflen + 1];
			if (buflen > 0) std::memcpy(buffer, content.data(), (size_t)buflen);
			buffer[buflen] = 0;
			source_name_ = "<stdin>";
		}
		else {
			std::ifstream fin(filename, std::ifstream::binary);

			if (!fin) {
				std::cerr << "error: Cannot open file \"" << filename << "\"." << std::endl;
				return false;
			}

			fin.seekg(0, std::ios::end);
			buflen = (long)fin.tellg();
			fin.seekg(0, std::ios::beg);

			buffer = new char[buflen + 1];
			fin.read(buffer, buflen);
			buffer[buflen] = 0;
			source_name_ = filename;

			fin.close();
		}
		source_text_.assign(buffer, static_cast<size_t>(buflen));
		source_position_ = {};

		/*
		parse command
		*/
		parsing_file = true;
		bufptr = buffer;
		if (buflen > 0) line_number = 1;

		scanToNextSymbol();
		has_parse_error_ = false;

		try {
			while (*bufptr) {
				const size_t begin_offset = static_cast<size_t>(bufptr - buffer);
				const size_t begin_line = line_number;
				parseLpar();
				CMD_TYPE type = parseCommand();
				const size_t end_offset = static_cast<size_t>(bufptr - buffer) +
				    (*bufptr == ')' ? 1U : 0U);
				parseRpar();
				if (command_logging_ || isResponseCommand(type)) {
					script_.addCommand(makeCommand(type, begin_offset, end_offset,
					                               begin_line));
				}
				else ++next_command_index_;
				if (type == CMD_TYPE::CT_EXIT) break;
			}
		} catch (const ParseErrorException& e) {
			// Kept, not only printed. See Parser::lastParseError.
			last_parse_error_ = e;
			has_parse_error_ = true;
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			return false;
		} catch (const std::bad_alloc&) {
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			throw;
		} catch (const std::exception&) {
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			return false;
		}
		bufptr = nullptr;
		delete[] buffer;
		buffer = nullptr;
		return true;
	}

	char* safe_strdup(const std::string& str) {
		if (str.empty()) return nullptr;
		
		// An exhausted allocation is not malformed input. Let callers and the
		// translation boundary classify std::bad_alloc as a resource failure.
		char* new_str = new char[str.length() + 1];
		
		std::memcpy(new_str, str.c_str(), str.length() + 1);
		return new_str;
	}

	bool Parser::parseStr(const std::string& constraint,
	                     const std::string& source_name) {
		if (constraint.empty()) return true;
		source_text_ = constraint;
		source_position_ = {};
		source_name_ = source_name;
		buffer = safe_strdup(constraint);
		if (!buffer) return false;
		buflen = constraint.length();
		bufptr = buffer;
		if (buflen > 0) line_number = 1;
		scanToNextSymbol();
		has_parse_error_ = false;
		try {
			while (*bufptr) {
				const size_t begin_offset = static_cast<size_t>(bufptr - buffer);
				const size_t begin_line = line_number;
				parseLpar();
				CMD_TYPE type = parseCommand();
				const size_t end_offset = static_cast<size_t>(bufptr - buffer) +
				    (*bufptr == ')' ? 1U : 0U);
				parseRpar();
				if (command_logging_ || isResponseCommand(type)) {
					script_.addCommand(makeCommand(type, begin_offset, end_offset,
					                               begin_line));
				}
				else ++next_command_index_;
				if (type == CMD_TYPE::CT_EXIT) break;
			}
		} catch (const ParseErrorException& e) {
			// Kept, not only printed. See Parser::lastParseError.
			last_parse_error_ = e;
			has_parse_error_ = true;
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			return false;
		} catch (const std::bad_alloc&) {
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			throw;
		} catch (const std::exception&) {
			bufptr = nullptr;
			if (buffer) { delete[] buffer; buffer = nullptr; }
			buflen = 0;
			return false;
		}
		bufptr = nullptr;
		delete[] buffer;
		buffer = nullptr;
		return true;
	}

	bool Parser::loadStr(const std::string& constraint,
	                    const std::string& source_name) {
		delete[] buffer;
		buffer = nullptr;
		bufptr = nullptr;
		buflen = 0;
		if (constraint.empty()) return true;
		source_text_ = constraint;
		source_position_ = {};
		source_name_ = source_name;

		buffer = safe_strdup(constraint);
		if (!buffer) return false;
		buflen = constraint.length();
		bufptr = buffer;
		line_number = 1;
		scanToNextSymbol();
		return true;
	}

	SourcePosition Parser::sourcePosition(size_t offset) const {
		offset = std::min(offset, source_text_.size());
		// Normal command ranges are monotonic, so every source byte is visited
		// once. A backward request still has the same byte/line/column meaning.
		if (offset < source_position_.offset) { source_position_ = {}; }
		while (source_position_.offset < offset) {
			if (source_text_[source_position_.offset++] == '\n') {
				++source_position_.line;
				source_position_.column = 1;
			} else {
				++source_position_.column;
			}
		}
		return source_position_;
	}

	Command Parser::makeCommand(CMD_TYPE type, size_t begin_offset,
	                            size_t end_offset, size_t begin_line) {
		Command cmd(type);
		cmd.index = next_command_index_++;
		cmd.line_number = begin_line;
		cmd.range = {sourcePosition(begin_offset), sourcePosition(end_offset)};
		if (end_offset >= begin_offset && end_offset <= source_text_.size())
			cmd.original = source_text_.substr(begin_offset, end_offset - begin_offset);
		cmd.expr = pending_command_expr_;
		cmd.name = pending_command_name_;
		cmd.sort = pending_command_sort_;
		cmd.params = pending_command_params_;
		cmd.logic = pending_command_logic_;
		cmd.push_pop_level = pending_push_pop_level_;
		if (type == CMD_TYPE::CT_CHECK_SAT_ASSUMING && !context_.assumptions.empty()) {
			cmd.assumptions = context_.assumptions.back();
		}
		if (!pending_value_terms_.empty()) cmd.value_terms = std::move(pending_value_terms_);
		if (!pending_keyword_.empty()) cmd.keyword = std::move(pending_keyword_);
		return cmd;
	}

	bool Parser::assert(const std::string& constraint) {
		parsing_file = false;
		std::shared_ptr<DAGNode> expr = mkExpr(constraint);
		context_.assertions.emplace_back(expr);
		return true;
	}

	bool Parser::assert(std::shared_ptr<DAGNode> node) {
		context_.assertions.emplace_back(node);
		return true;
	}

	std::shared_ptr<DAGNode> Parser::mkExpr(const std::string& expression) {
		parsing_file = false;
		if (expression.empty()) {
			return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
		}
		
		buffer = safe_strdup(expression);
		if (!buffer) {
			return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
		}
		
		buflen = expression.length();
		bufptr = buffer;
		if (buflen > 0) line_number = 1;
		scanToNextSymbol();
		std::shared_ptr<DAGNode> expr = parseExpr();
		
		bufptr = nullptr;
		delete[] buffer;
		buffer = nullptr;
		return expr;
	}
	

	KEYWORD Parser::parseKeyword(){
		
		size_t key_ln = line_number;
		//std::cout << "line_number = " << key_ln << std::endl;
		std::string key = getSymbol();
		//std::cout << "key = " << key << std::endl;
		if(key == ":id"){
			return KEYWORD::KW_ID;
		}
		else if(key == ":weight"){
			return KEYWORD::KW_WEIGHT;
		}
		// Quantifier annotations — ported from the SMTStabilizer fork.
		else if(key == ":pattern"){
			return KEYWORD::KW_PATTERN;
		}
		else if(key == ":no-pattern"){
			return KEYWORD::KW_NO_PATTERN;
		}
		else if(key == ":qid"){
			return KEYWORD::KW_QID;
		}
		else if(key == ":skolemid"){
			return KEYWORD::KW_SKOLEMID;
		}
		else if(key == ":lblpos"){
			return KEYWORD::KW_LBLPOS;
		}
		else if(key == ":lblneg"){
			return KEYWORD::KW_LBLNEG;
		}
		else if (key == ":comp"){
			return KEYWORD::KW_COMP;
		}
		else if (key == ":epsilon"){
			return KEYWORD::KW_EPSILON;
		}
		else if(key == ":M"){
			return KEYWORD::KW_M;
		}else if (key == ":named"){
			return KEYWORD::KW_NAMED;
		}
		else{
			err_unkwn_sym(key, key_ln);
		}
		return KEYWORD::KW_NULL;
	}

	CMD_TYPE Parser::parseCommand() {
		// Reset the per-command interactive payload before parsing this command.
		pending_value_terms_.clear();
		pending_keyword_.clear();
		pending_command_expr_.reset();
		pending_command_name_.clear();
		pending_push_pop_level_ = 1;
		pending_command_sort_.reset();
		pending_command_params_.clear();
		pending_command_logic_.clear();

		size_t command_ln = line_number;
		std::string command = getSymbol();

        if (command == "declare-heap") {
            if (context_.heap_location_sort || !context_.heap_declaration_open ||
                !context_.scope_stack_.empty())
                err_all(ERROR_TYPE::ERR_LOGIC, "declare-heap requires a fresh base context", command_ln);
            parseLpar();
            auto location = parseSort();
            auto data = parseSort();
            parseRpar();
            scanToNextSymbol();
            if (*bufptr != ')')
                err_all(ERROR_TYPE::ERR_PARAM_MIS, "declare-heap expects one sort pair", command_ln);
            context_.heap_location_sort = std::move(location);
            context_.heap_data_sort = std::move(data);
            return CMD_TYPE::CT_DECLARE_HEAP;
        }
        if (command == "assert" || command == "assert-soft" || command == "push" ||
            command == "check-sat" || command == "check-sat-assuming")
            context_.heap_declaration_open = false;

		// (assert <expr>) or (assert <expr> [:id <symbol>])
		if (command == "assert") {
			std::string grp_id = "";
			std::string named_name = "";

			KEYWORD key = attemptParseKeywords();
			if(key == KEYWORD::KW_ID){
				// (assert [:id <symbol>] <expr>)
				grp_id = getSymbol();
			}
			std::shared_ptr<DAGNode> assert_expr = parseExpr();
			pending_command_expr_ = assert_expr;
			// 
			// (assert <expr> [:id <symbol>] [:named <symbol>]), in either order.
			// attemptParseKeywords() consumes the keyword it reads, so the two
			// separate attempts this replaces did not compose: the one looking
			// for :id swallowed a trailing :named and discarded it, and the
			// :named attempt then saw the bare name. Loop over the keywords
			// instead, the way parseAssertSoft already does.
			while(true){
				KEYWORD key_ = attemptParseKeywords();
				if(key_ == KEYWORD::KW_ID && grp_id == ""){
					grp_id = getSymbol();
				}
				else if(key_ == KEYWORD::KW_NAMED && named_name == ""){
					named_name = getSymbol();
				}
				else{
					break;
				}
			}
			// A second term is not an annotation. Silently skipping it changes
			// the apparent assertion and hides malformed input from callers.
			if (*bufptr != ')') { err_param_mis("assert", command_ln); }
			size_t index = context_.assertions.size();
			context_.assertions.emplace_back(assert_expr);
			// if grp_id is not empty, insert to assertion_groups
			if(grp_id != ""){
				if(context_.assertion_groups.find(grp_id) == context_.assertion_groups.end()){
					context_.assertion_groups.insert(std::pair<std::string, std::unordered_set<size_t>>(grp_id, {index}));
				}
				else{
					context_.assertion_groups[grp_id].insert(index);
				}
			}
			//if named_name is not empty, insert to named_assertions
			if (named_name != ""){
				warn_named_displaced(context_.nameAssertion(named_name, assert_expr),
				                     named_name, command_ln);
			}
			if(grp_id != ""){
				context_.registerAssertionGroupInScope(grp_id);
			}
			return CMD_TYPE::CT_ASSERT;
		}
		// (assert-soft <expr> [:weight <numeral>] [:id <symbol>])
		if (command == "assert-soft") {
			parseAssertSoft();
			skipToRpar();
			return CMD_TYPE::CT_ASSERT_SOFT;
		}

		// (check-sat)
		if (command == "check-sat") {
			getOptions()->check_sat = true;
			skipToRpar();
			return CMD_TYPE::CT_CHECK_SAT;
		}

		// (check-sat-assuming (a1, ..., an)), maybe for future incremental mode.
		if (command == "check-sat-assuming") {
			//parse (a1, ..., an)
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> cur_assumptions;
			while (*bufptr != ')') {
				std::shared_ptr<DAGNode> assump = parseExpr();
				cur_assumptions.emplace_back(assump);
			}
			parseRpar();
			context_.assumptions.emplace_back(cur_assumptions);
			return CMD_TYPE::CT_CHECK_SAT_ASSUMING;
		}

		// (declare-const <symbol> <sort>)
		if (command == "declare-const") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			// get returned type
			std::shared_ptr<DAGNode> res = nullptr;
			std::shared_ptr<Sort> sort = parseSort();
			if(!sort || sort->isNull()){
				// (declare-const x) with the sort missing
				err_all(ERROR_TYPE::ERR_PARAM_MIS, "declare-const requires a sort", name_ln);
			}
			res = mkVar(sort, name);
			pending_command_name_ = name;
			pending_command_sort_ = sort;
			pending_command_expr_ = res;

			// multiple declarations
			if (res->isErr()) err_all(res, name, name_ln);
			else context_.registerVarInScope(name);
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_CONST;
		}

		// (declare-fun <symbol> (<sort>*) <sort>)
		if (command == "declare-fun") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			// (declare-fun <symbol> (<sort>*) <sort>)
			//                       ^
			parseLpar();
			// (declare-fun <symbol> (<sort>*) <sort>)
			//                               ^
			std::shared_ptr<DAGNode> res = nullptr;
			if(*bufptr == ')'){
				// (declare-fun <symbol> () <sort>)
				parseRpar();
				std::shared_ptr<Sort> out_sort = parseSort();
				if(!out_sort || out_sort->isNull()){
					err_all(ERROR_TYPE::ERR_PARAM_MIS, "declare-fun requires a return sort", name_ln);
				}
				res = mkVar(out_sort, name);
				if(!res->isErr()) context_.registerVarInScope(name);
			}
			else{
				// (declare-fun <symbol> (<sort>+) <sort>)
				std::vector<std::shared_ptr<Sort>> params;
				while(*bufptr != ')'){
					params.emplace_back(parseSort());
				}
				parseRpar();
				std::shared_ptr<Sort> out_sort = parseSort();
				res = mkFuncDec(name, params, out_sort);
				if(!res->isErr()){
					getSymbolManager()->addFunctionName(name);
					context_.registerFunInScope(name);
				}
			}

			//multiple declarations
			pending_command_name_ = name;
			pending_command_sort_ = res ? res->getSort() : nullptr;
			pending_command_expr_ = res;
			if (res->isErr()) err_all(res, name, name_ln);
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_FUN;
		}

		// (declare-sort <symbol> <numeral>)
		if (command == "declare-sort") {
			//get name
			std::string name = getSymbol();

			//get numeral
			std::string numeral = getSymbol();
			size_t num = std::stoi(numeral);

			// make sort
			std::shared_ptr<Sort> sort = mkSortDec(name, num);
			pending_command_name_ = name;
			pending_command_sort_ = sort;
			getSymbolManager()->registerSort(name, sort);
			context_.registerSortInScope(name);
			skipToRpar();

			return CMD_TYPE::CT_DECLARE_SORT;
		}

		// (declare-datatype <symbol> <datatype-dec>)
		// <datatype-dec> ::= (<constructor-dec>+)
		if (command == "declare-datatype") {
			std::string dt_name = getSymbol();
			auto ps = getSortManager()->createSort(SORT_KIND::SK_DATATYPE, dt_name, 0);
			getSymbolManager()->registerSort(dt_name, ps);
			context_.registerSortInScope(dt_name);
			parseLpar();
			// `(declare-datatype Pair (par (A B) (...)))`. The arity is not
			// written in this form -- it is the number of parameters -- so it is
			// set from what `par` declares.
			{
				const std::vector<std::string> params = parseDatatypeParams();
				ScopedSortBindings scoped_sorts(getSymbolManager(), params.size());
				if (!params.empty()) {
					ps->arity = params.size();
					datatype_params_[dt_name] = params;
					for (const std::string& pn : params) {
						scoped_sorts.bind(
							pn, getSortManager()->createSort(
								SORT_KIND::SK_DEC, pn, 0));
					}
				}
				defineDatatypeConstructors(ps);
				// Out of scope again: a parameter is bound by its `par` and the
				// next command must not see it.
				if (!params.empty()) { parseRpar(); }   // close the `par`
			}
			skipToRpar();
			return CMD_TYPE::CT_DECLARE_DATATYPES;
		}

		// (declare-datatypes (<sort-dec>+) (<datatype-dec>+))
		// where:
		//   <sort-dec>    ::= (<symbol> <numeral>)
		//   <datatype-dec>::= (<constructor-dec>+)
		//   <constructor-dec>::= (<symbol> <selector-dec>*)
		//   <selector-dec>::= (<symbol> <sort>)
		if (command == "declare-datatypes" || command == "declare-codatatypes") {
			const bool coinductive = command == "declare-codatatypes";
			// -- Phase 1: read sort names so we can register forward references --
			parseLpar(); // outer '(' for sort list
			std::vector<std::pair<std::string, size_t>> sort_decls;
			while(*bufptr != ')') {
				parseLpar();
				std::string dt_name = getSymbol();
				std::string arity_str = getSymbol();
				size_t dt_arity = static_cast<size_t>(std::stoi(arity_str));
				sort_decls.emplace_back(dt_name, dt_arity);
				parseRpar();
			}
			parseRpar(); // close sort list

			// Pre-register placeholder sorts so mutual recursion works
			std::vector<std::shared_ptr<Sort>> placeholder_sorts;
			for(auto& sd : sort_decls) {
				auto ps = getSortManager()->createSort(SORT_KIND::SK_DATATYPE, sd.first, sd.second);
				ps->coinductive = coinductive;
				getSymbolManager()->registerSort(sd.first, ps);
				context_.registerSortInScope(sd.first);
				placeholder_sorts.push_back(ps);
			}

			// -- Phase 2: parse constructor lists --
			parseLpar(); // outer '(' for datatype list
			for(size_t ti = 0; ti < sort_decls.size(); ++ti) {
				parseLpar(); // '(' for this datatype
				// `(par (X) (<ctors>))` when the sort was declared with a
				// non-zero arity. The parameters are in scope only while this
				// datatype's constructors are read.
				const std::vector<std::string> params = parseDatatypeParams();
				ScopedSortBindings scoped_sorts(getSymbolManager(), params.size());
				if (!params.empty()) {
					datatype_params_[sort_decls[ti].first] = params;
					for (const std::string& pn : params) {
						scoped_sorts.bind(
							pn, getSortManager()->createSort(
								SORT_KIND::SK_DEC, pn, 0));
					}
				}
				defineDatatypeConstructors(placeholder_sorts[ti]);
				if (!params.empty()) { parseRpar(); }   // close the `par`
			}
			parseRpar(); // close outer datatype list
			skipToRpar(); // close the (co)datatype command

			return coinductive ? CMD_TYPE::CT_DECLARE_CODATATYPES : CMD_TYPE::CT_DECLARE_DATATYPES;
		}

		// (define-const <symbol> <sort> <expr>)
		if (command == "define-const") {
			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			std::shared_ptr<DAGNode> check_fun = getSymbolManager()->getFun(name);
			if(check_fun && check_fun->getKind() == NODE_KIND::NT_FUNC_DEF){
				err_mul_def(name, name_ln);
			}
			if(check_fun){
				return CMD_TYPE::CT_DEFINE_FUN;
			}
			// keep the function name with the same order
			getSymbolManager()->addFunctionName(name);
			context_.registerFunInScope(name);

			// get returned type and body
			std::shared_ptr<Sort> out_sort = parseSort();
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::vector<std::shared_ptr<DAGNode>> params; // empty params for constant
			std::shared_ptr<DAGNode> res = mkFuncDef(name, params, out_sort, func_body);
			pending_command_name_ = name;
			pending_command_sort_ = out_sort;
			pending_command_expr_ = res;
			skipToRpar();
			
			return CMD_TYPE::CT_DEFINE_FUN;
		}

		//(define-fun <symbol> ((<symbol> <sort>)*) <sort> <expr>)
		if (command == "define-fun") {

			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			std::shared_ptr<DAGNode> check_fun = getSymbolManager()->getFun(name);
			if(check_fun && check_fun->getKind() == NODE_KIND::NT_FUNC_DEF){
				err_mul_def(name, name_ln);
			}
			if(check_fun){
				return CMD_TYPE::CT_DEFINE_FUN;
			}
			// keep the function name with the same order
			getSymbolManager()->addFunctionName(name);
			context_.registerFunInScope(name);

			// parse ((x Int))
			//       ^
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> params;
			std::vector<std::string> key_list;
			while(*bufptr!=')'){ // there are still (x Int) left.
				// (x Int)
				// ^
				parseLpar();
				std::string pname = getSymbol();
				std::shared_ptr<Sort> ptype = parseSort();
				key_list.emplace_back(pname);
				std::shared_ptr<DAGNode> expr = nullptr;
				expr = mkFunParamVar(ptype, pname);
				// multiple declarations
				if(getSymbolManager()->hasFunVar(pname)){
					err_mul_decl(pname, line_number);
				}
				else{
					getSymbolManager()->registerFunVar(pname, expr);
					params.emplace_back(expr);
				}
				// (x Int)
				//		 ^
				parseRpar();
			}
			
			//(define-fun <symbol> ((<symbol> <sort>)*) <sort> <expr>)
			//					                      ^
			parseRpar();

			//get returned type
			std::shared_ptr<Sort> out_sort = parseSort();
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::shared_ptr<DAGNode> res = mkFuncDef(name, params, out_sort, func_body);
			pending_command_name_ = name;
			pending_command_sort_ = out_sort;
			pending_command_params_ = params;
			pending_command_expr_ = res;
			skipToRpar();

			//remove key bindings: for let uses local variables. 
			while (key_list.size() > 0) {
				getSymbolManager()->eraseFunVar(key_list.back());
				key_list.pop_back();
			}
			
			return CMD_TYPE::CT_DEFINE_FUN;
		}

		// (define-fun-rec <symbol> ((<symbol> <sort>)*) <sort> <expr>)
		// recursive function definition
		if (command == "define-fun-rec") {
			// get name
			size_t name_ln = line_number;
			std::string name = getSymbol();

			std::shared_ptr<DAGNode> check_fun = getSymbolManager()->getFun(name);
			if(check_fun) err_mul_def(name, name_ln);
			// keep the function name with the same order
			getSymbolManager()->addFunctionName(name);
			context_.registerFunInScope(name);

			// parse ((x Int))
			//       ^
			parseLpar();
			std::vector<std::shared_ptr<DAGNode>> params;
			std::vector<std::string> key_list;
			std::vector<std::shared_ptr<Sort>> param_sorts;
			while(*bufptr!=')'){ // there are still (x Int) left.
				// (x Int)
				// ^
				parseLpar();
				std::string pname = getSymbol();
				std::shared_ptr<Sort> ptype = parseSort();
				key_list.emplace_back(pname);
				param_sorts.emplace_back(ptype);
				std::shared_ptr<DAGNode> expr = nullptr;
				expr = mkFunParamVar(ptype, pname);
				// multiple declarations
				if(getSymbolManager()->hasFunVar(pname)){
					err_mul_decl(pname, line_number);
				}
				else{
					getSymbolManager()->registerFunVar(pname, expr);
					params.emplace_back(expr);
				}
				// (x Int)
				//		 ^
				parseRpar();
			}
			
			//(define-fun-rec <symbol> ((<symbol> <sort>)*) <sort> <expr>)
			//					                        ^
			parseRpar();

			//get returned type
			std::shared_ptr<Sort> out_sort = parseSort();
			
			// For recursive functions, we need to create a function declaration first
			// so it can be referenced in its own body
			std::shared_ptr<DAGNode> func_dec = mkFuncRecDecl(name, param_sorts, out_sort);
			
			// Now parse the function body (which can reference the function itself)
			std::shared_ptr<DAGNode> func_body = parseExpr();
			std::shared_ptr<DAGNode> res = mkFuncRec(name, params, out_sort, func_body);
			pending_command_name_ = name;
			pending_command_sort_ = out_sort;
			pending_command_params_ = params;
			pending_command_expr_ = res;
			skipToRpar();

			//remove key bindings: for let uses local variables. 
			while (key_list.size() > 0) {
				getSymbolManager()->eraseFunVar(key_list.back());
				key_list.pop_back();
			}
			
			return CMD_TYPE::CT_DEFINE_FUN_REC;
		}

		if (command == "define-funs-rec") {
			// (define-funs-rec ((name1 ((param1 type1)...) ret_type1)...) (body1 body2...))
			
			// Parse function declarations first
			parseLpar(); // for function declarations list
			std::vector<std::string> func_names;
			std::vector<std::vector<std::shared_ptr<DAGNode>>> all_params;
			std::vector<std::vector<std::string>> all_key_lists;
			std::vector<std::vector<std::shared_ptr<Sort>>> all_param_sorts;
			std::vector<std::shared_ptr<Sort>> return_sorts;
			
			while(*bufptr != ')') {
				// Parse each function declaration: (name ((param1 type1)...) ret_type)
				parseLpar();
				std::string name = getSymbol();
				
				std::shared_ptr<DAGNode> check_fun = getSymbolManager()->getFun(name);
				if(check_fun || std::find(func_names.begin(), func_names.end(), name) != func_names.end())
					err_mul_def(name, line_number);
				
				func_names.emplace_back(name);
				getSymbolManager()->addFunctionName(name);
				context_.registerFunInScope(name);
				
				// Parse parameters: ((param1 type1)...)
				parseLpar();
				std::vector<std::shared_ptr<DAGNode>> params;
				std::vector<std::string> key_list;
				std::vector<std::shared_ptr<Sort>> param_sorts;
				
				while(*bufptr != ')') {
					parseLpar();
					std::string pname = getSymbol();
					std::shared_ptr<Sort> ptype = parseSort();
					if (std::find(key_list.begin(), key_list.end(), pname) != key_list.end())
						err_mul_decl(pname, line_number);
					key_list.emplace_back(pname);
					param_sorts.emplace_back(ptype);
					std::shared_ptr<DAGNode> expr = mkFunParamVar(ptype, pname);
					params.emplace_back(expr);
					parseRpar();
				}
				parseRpar(); // end of parameters
				
				// Parse return type
				std::shared_ptr<Sort> out_sort = parseSort();
				return_sorts.emplace_back(out_sort);
				
				all_params.emplace_back(params);
				all_key_lists.emplace_back(key_list);
				all_param_sorts.emplace_back(param_sorts);
				
				parseRpar(); // end of function declaration
			}
			parseRpar(); // end of function declarations list
			
			// Create function declarations for all functions first
			// so they can be referenced in each other's bodies
			for(size_t i = 0; i < func_names.size(); i++) {
				mkFuncRecDecl(func_names[i], all_param_sorts[i], return_sorts[i]);
			}
			
			// Parse function bodies
			parseLpar(); // for function bodies list
			for(size_t i = 0; i < func_names.size(); i++) {
				// Add parameter bindings for this function
				for(size_t j = 0; j < all_key_lists[i].size(); j++) {
					getSymbolManager()->registerFunVar(all_key_lists[i][j], all_params[i][j]);
				}
				
				// Parse function body
				std::shared_ptr<DAGNode> func_body = parseExpr();
				std::shared_ptr<DAGNode> res = mkFuncRec(func_names[i], all_params[i], return_sorts[i], func_body);
				
				// Remove parameter bindings for this function
				for(const auto& key : all_key_lists[i]) {
					getSymbolManager()->eraseFunVar(key);
				}
			}
			parseRpar(); // end of function bodies list

			// Remember that these names form one mutually recursive group. The
			// nodes themselves carry no trace of it, so without this the dump
			// would split the group into standalone define-fun-rec commands and
			// forward-reference the members defined later.
			getSymbolManager()->addRecFunGroup(func_names);

			skipToRpar();
			return CMD_TYPE::CT_DEFINE_FUNS_REC;
		}

		// (define-sort <symbol> (<symbol>*) <sort>)
		// <symbol>* is a list of symbols that represent template parameters.
		// for example, (define-sort List (T) (List T))
		// T is a template parameter.
		// then (define-sort IntList () (List Int)) is a valid command.
		if (command == "define-sort") {
			// get name
			std::string name = getSymbol();

			// get params (symbols)
			std::vector<std::string> param_names;
			parseLpar();
			while(*bufptr != ')'){
				param_names.push_back(getSymbol());
			}
			parseRpar();
			
			// convert param names to Sort parameters
			std::vector<std::shared_ptr<Sort>> params;
			for(const auto& name : param_names) {
				params.push_back(getSortManager()->createSort(name));
			}

			// get out sort
			std::shared_ptr<Sort> out_sort = parseSort();
			if(params.size() == 0){
				// it means an alias of the out sort
				getSymbolManager()->registerSort(name, out_sort);
			}
			else{
				std::shared_ptr<Sort> sort = mkSortDef(name, params, out_sort);
				getSymbolManager()->registerSort(name, sort);
			}
			context_.registerSortInScope(name);
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_SORT;
		}

		if (command == "echo") {
			// (echo <string>) — capture the string literal so the consumer can
			// echo it back (was previously discarded with the rest of the line).
			if (*bufptr != ')') pending_keyword_ = getSymbol();
			skipToRpar();
			return CMD_TYPE::CT_ECHO;
		}

		// (exit)
		if (command == "exit") {
			skipToRpar();
			return CMD_TYPE::CT_EXIT;
		}

		// (get-assertions)
		// but used in interactive mode, so ignore it.
		if (command == "get-assertions") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_ASSERTIONS;
		}

		if (command == "get-assignment") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_ASSIGNMENT;
		}

		if (command == "get-info") {
			// (get-info <:keyword>) — capture the keyword to answer the query.
			if (*bufptr != ')') pending_keyword_ = getSymbol();
			skipToRpar();
			return CMD_TYPE::CT_GET_INFO;
		}

		if (command == "get-option") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_OPTION;
		}

		if (command == "get-model") {
			//ignore
			getOptions()->get_model = true;
			skipToRpar();
			return CMD_TYPE::CT_GET_MODEL;
		}

		if (command == "get-option") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_OPTION;
		}

		if (command == "get-proof") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_PROOF;
		}

		if (command == "get-unsat-assumptions") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_UNSAT_ASSUMPTIONS;
		}

		if (command == "get-unsat-core") {
			//ignore
			warn_cmd_nsup(command, command_ln);
			skipToRpar();
			return CMD_TYPE::CT_GET_UNSAT_CORE;
		}

		if (command == "get-value") {
			// (get-value ( <term>+ )) — parse the term list so the consumer can
			// evaluate each term in the model and print (term value) pairs.
			parseObjectiveValueTerms();
			skipToRpar();
			return CMD_TYPE::CT_GET_VALUE;
		}

		if (command == "pop") {
			size_t n = 1;
			if (*bufptr != ')') {
				std::string num = getSymbol();
				if (num.empty() || num.find_first_not_of("0123456789") != std::string::npos) {
					err_param_nnum("pop", command_ln);
				}
				n = std::stoul(num);
			}
			if (n > context_.scope_stack_.size()) {
				err_param_mis("pop: scope underflow", command_ln);
			}
			context_.popScope(n);
			pending_push_pop_level_ = n;
			skipToRpar();
			return CMD_TYPE::CT_POP;
		}

		if (command == "push") {
			size_t n = 1;
			if (*bufptr != ')') {
				std::string num = getSymbol();
				if (num.empty() || num.find_first_not_of("0123456789") != std::string::npos) {
					err_param_nnum("push", command_ln);
				}
				n = std::stoul(num);
			}
			context_.pushScope(n);
			pending_push_pop_level_ = n;
			skipToRpar();
			return CMD_TYPE::CT_PUSH;
		}

		if (command == "reset") {
			context_.resetAll();
			result_type = RESULT_TYPE::RT_UNKNOWN;
			result_node.reset();
			result_model.reset();
			context_.setSymbolManager(std::make_shared<SymbolManager>());
			context_.setObjectiveManager(std::make_shared<ObjectiveManager>());
			skipToRpar();
			return CMD_TYPE::CT_RESET;
		}

		if (command == "reset-assertions") {
			context_.resetAssertions();
			skipToRpar();
			return CMD_TYPE::CT_RESET_ASSERTIONS;
		}

		//<attribute ::= <keyword> | <keyword> <attribute_value>
		//(set-info <attribute>)
		if (command == "set-info") {
			skipToRpar();
			return CMD_TYPE::CT_SET_INFO;
		}

		//(set-logic <symbol>)
		if (command == "set-logic") {
			size_t type_ln = line_number;
			std::string type = getSymbol();
			pending_command_logic_ = type;
			bool is_valid = getOptions()->setLogic(type);
			if(!is_valid){
				// A WARNING, not a parse error. setLogic already handles this
				// case and says so where it is defined: an unrecognised name
				// "should not disable theories; fall back to ALL and report the
				// name as unrecognised". Throwing here contradicted that and
				// made the whole file unparseable.
				//
				// The names this rejects are not exotic. `HORN` is what Z3,
				// Eldarica and Golem consume and what every CHC-COMP instance
				// opens with (docs/languages/chc-comp.md §2.1), and SMT-LIB
				// gains logics over time -- so a released parser refusing an
				// unknown one refuses inputs that are legal today and inputs
				// that become legal later. Falling back to ALL is strictly
				// safer than the alternative, since ALL enables every theory.
				std::cerr << "warning: unrecognised logic \"" << type
				          << "\" in line " << type_ln
				          << "; continuing with ALL, which enables every theory"
				          << std::endl;
			}

			return CMD_TYPE::CT_SET_LOGIC;
		}

		//<option ::= <attribute>
		//(set-option <option>)
		if (command == "set-option") {
			// Store the key/value pair so consumers can read it (e.g. OMT
			// multi-objective :opt.priority).  This command used to be
			// skipped wholesale, silently dropping every option.
			std::string opt_key = getSymbol();
			if (!opt_key.empty() && opt_key[0] == ':') {
				opt_key = opt_key.substr(1);
			}
			std::string opt_value = getSymbol();
			if (opt_key == "global-declarations" && opt_value != "true" && opt_value != "false")
				err_all(ERROR_TYPE::ERR_PARAM_MIS, "global-declarations expects true or false", command_ln);
			if (!opt_key.empty()) {
				setOption(opt_key, opt_value);
			}
			skipToRpar();
			return CMD_TYPE::CT_SET_OPTION;
		}
		
		// quantifier
		// (quantifier ((<symbol> <sort>)+) <expr>)
		if(command == "exists") {
			in_quantifier_scope = true;
			quant_nesting_depth++;
			parseQuant("exists");
			quant_nesting_depth--;
			if(quant_nesting_depth == 0){
				in_quantifier_scope = false;
			}
			skipToRpar();
			return CMD_TYPE::CT_EXISTS;
		}
		if(command == "forall") {
			in_quantifier_scope = true;
			quant_nesting_depth++;
			parseQuant("forall");
			quant_nesting_depth--;
			if(quant_nesting_depth == 0){
				in_quantifier_scope = false;
			}
			skipToRpar();
			return CMD_TYPE::CT_FORALL;
		}

		// optimization
		if (command == "define-multi-objective") {
			parseGomtMultiObjective();
			return CMD_TYPE::CT_DEFINE_OBJ;
		}
		if (command == "define-maxsmt-objective") {
			parseGomtMaxSmtObjective();
			return CMD_TYPE::CT_DEFINE_OBJ;
		}
		if (command == "optimize-sat") {
			const size_t assumptions_before = context_.assumptions.size();
			parseGomtOptimizeSat();
			return context_.assumptions.size() > assumptions_before
			    ? CMD_TYPE::CT_CHECK_SAT_ASSUMING : CMD_TYPE::CT_CHECK_SAT;
		}
		if(command == "get-objectives"){
			getOptions()->get_objectives = true;
			skipToRpar();
			return CMD_TYPE::CT_GET_OBJECTIVES;
		}

		// (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "maximize"){
			parseMaximize();
			skipToRpar();
			return CMD_TYPE::CT_MAXIMIZE;
		}

		// (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "minimize"){
			parseMinimize();
			skipToRpar();
			return CMD_TYPE::CT_MINIMIZE;
		}

		// multi-objective optimization
		// (define-objective <symbol> <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
		if(command == "define-objective"){
			parseDefObj();
			skipToRpar();
			return CMD_TYPE::CT_DEFINE_OBJ;
		}
		// (lex-optimize (<symbol>+) [:id <symbol>])
		if(command == "lex-optimize"){
			parseLexOpt();
			skipToRpar();
			return CMD_TYPE::CT_LEX_OPTIMIZE;
		}
		// (pareto-optimize (<symbol>+) [:id <symbol>])
		if(command == "pareto-optimize"){
			parseParetoOpt();
			skipToRpar();
			return CMD_TYPE::CT_PARETO_OPTIMIZE;
		}
		// (box-optimize (<symbol>+) [:id <symbol>])
		if(command == "box-optimize"){
			parseBoxOpt();
			skipToRpar();
			return CMD_TYPE::CT_BOX_OPTIMIZE;
		}
		// (minmax (<symbol>+) [:id <symbol>])
		if(command == "minmax"){
			parseMinmax();
			skipToRpar();
			return CMD_TYPE::CT_MINMAX;
		}
		// (maxmin (<symbol>+) [:id <symbol>])
		if(command == "maxmin"){
			parseMaxmin();
			skipToRpar();
			return CMD_TYPE::CT_MAXMIN;
		}
		// (maxsat [:id <symbol>])
		if(command == "maxsat"){
			parseMaxsat();
			skipToRpar();
			return CMD_TYPE::CT_MAXSAT;
		}
		// (minsat [:id <symbol>])
		if(command == "minsat"){
			parseMinsat();
			skipToRpar();
			return CMD_TYPE::CT_MINSAT;
		}
		// (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
		if(command == "optimize"){
			parseOptimize();
			skipToRpar();
			return CMD_TYPE::CT_OPTIMIZE;
		}
		err_unkwn_sym(command, command_ln);

		return CMD_TYPE::CT_UNKNOWN;

	}

	// --- Incremental / sequential API ---

	Command Parser::nextCommand() {
		if (!bufptr || !*bufptr) {
			delete[] buffer;
			buffer = nullptr;
			bufptr = nullptr;
			buflen = 0;
			return Command(CMD_TYPE::CT_EOF);
		}
		pending_value_terms_.clear();
		pending_keyword_.clear();
		const size_t begin_offset = static_cast<size_t>(bufptr - buffer);
		const size_t begin_line = line_number;
		parseLpar();
		CMD_TYPE type = parseCommand();
		const size_t end_offset = static_cast<size_t>(bufptr - buffer) +
		    (*bufptr == ')' ? 1U : 0U);
		parseRpar();
		Command cmd = makeCommand(type, begin_offset, end_offset, begin_line);
		if (command_logging_ || isResponseCommand(type)) {
			script_.addCommand(cmd);
		}
		return cmd;
	}

	bool Parser::push(size_t n) {
		context_.pushScope(n);
		const size_t command_index = next_command_index_++;
		if (command_logging_) {
			Command cmd(CMD_TYPE::CT_PUSH);
			cmd.index = command_index;
			cmd.push_pop_level = n;
			script_.addCommand(cmd);
		}
		return true;
	}

	bool Parser::pop(size_t n) {
		if (n > context_.scope_stack_.size()) {
			return false; // pop underflow
		}
		context_.popScope(n);
		const size_t command_index = next_command_index_++;
		if (command_logging_) {
			Command cmd(CMD_TYPE::CT_POP);
			cmd.index = command_index;
			cmd.push_pop_level = n;
			script_.addCommand(cmd);
		}
		return true;
	}

	bool Parser::resetAssertions() {
		context_.resetAssertions();
		const size_t command_index = next_command_index_++;
		if (command_logging_) {
			Command cmd(CMD_TYPE::CT_RESET_ASSERTIONS);
			cmd.index = command_index;
			script_.addCommand(std::move(cmd));
		}
		return true;
	}

	bool Parser::reset() {
		context_.resetAll();
		result_type = RESULT_TYPE::RT_UNKNOWN;
		result_node.reset();
		result_model.reset();
		const size_t command_index = next_command_index_++;
		if (command_logging_) {
			Command cmd(CMD_TYPE::CT_RESET);
			cmd.index = command_index;
			script_.addCommand(std::move(cmd));
		}
		return true;
	}

	// sort ::= <identifier> | (<identifier> <sort>+)
    std::shared_ptr<Sort> Parser::parseSort() {
        if (*bufptr == ')') return SortManager::NULL_SORT;
        static const std::unordered_map<std::string, std::shared_ptr<Sort>> BASIC_SORTS = {
            {"Bool", SortManager::BOOL_SORT}, {"Int", SortManager::INT_SORT},
            {"Real", SortManager::REAL_SORT}, {"RoundingMode", SortManager::ROUNDING_MODE_SORT},
            {"String", SortManager::STR_SORT}, {"Float16", SortManager::FLOAT16_SORT},
            {"Float32", SortManager::FLOAT32_SORT}, {"Float64", SortManager::FLOAT64_SORT},
            {"RegLan", SortManager::REG_SORT}, {"Reg", SortManager::REG_SORT},
            {"RegEx", SortManager::REG_SORT}
        };
        struct Frame {
            std::string head;
            std::size_t line;
            std::size_t arity;
            std::shared_ptr<Sort> prototype;
            std::vector<std::shared_ptr<Sort>> children;
        };
        std::vector<Frame> pending;
        std::shared_ptr<Sort> result;
        bool have_result = false;
        while (true) {
            if (!have_result) {
                if (*bufptr != '(') {
                    const std::size_t line = line_number;
                    const std::string name = getSymbol();
                    const auto basic = BASIC_SORTS.find(name);
                    if (basic != BASIC_SORTS.end()) result = basic->second;
                    else if (name == "UnitTuple") result = getSortManager()->createTupleSort({});
                    else {
                        result = getSymbolManager()->resolveSort(name);
                        if (!result) err_unkwn_sym(name, line);
                        if (result && result->isDatatype() && result->getChildrenSize() == 0) {
                            const auto params = datatypeParams(name);
                            if (!params.empty())
                                err_arity_mis(name + " (a datatype taking " +
                                    std::to_string(params.size()) + " sort argument(s), used with none)", line);
                        }
                    }
                    have_result = true;
                } else {
                    parseLpar();
                    Frame frame{getSymbol(), line_number, 0, SortManager::NULL_SORT, {}};
                    if (frame.head == "_") {
                        const std::string indexed = getSymbol();
                        if (indexed == "BitVec") {
                            const std::string width = getSymbol();
                            const std::string key = "BV_" + width;
                            frame.prototype = getSymbolManager()->resolveSort(key);
                            if (!frame.prototype) {
                                frame.prototype = getSortManager()->createBVSort(std::stoi(width));
                                getSymbolManager()->registerSort(key, frame.prototype);
                            }
                        } else if (indexed == "FloatingPoint") {
                            const std::string exponent = getSymbol();
                            const std::string significand = getSymbol();
                            const std::string key = "FP_" + exponent + "_" + significand;
                            frame.prototype = getSymbolManager()->resolveSort(key);
                            if (!frame.prototype) {
                                frame.prototype = getSortManager()->createFPSort(
                                    std::stoi(exponent), std::stoi(significand));
                                getSymbolManager()->registerSort(key, frame.prototype);
                            }
                        } else err_unkwn_sym(frame.head, frame.line);
                    } else if (frame.head == "Array") frame.arity = 2;
                    else if (frame.head == "Set" || frame.head == "RegEx") frame.arity = 1;
                    else if (frame.head == "Tuple") frame.arity = static_cast<std::size_t>(-1);
                    else if (frame.head != "Datatype" && frame.head != "Relation"
                             && frame.head != "Bag" && frame.head != "Sequence" && frame.head != "UF") {
                        const auto basic = BASIC_SORTS.find(frame.head);
                        frame.prototype = basic != BASIC_SORTS.end() ? basic->second
                            : getSymbolManager()->resolveSort(frame.head);
                        if (!frame.prototype) err_unkwn_sym(frame.head, frame.line);
                        frame.arity = frame.prototype->arity;
                    }
                    pending.push_back(std::move(frame));
                }
            }
            if (have_result) {
                if (pending.empty()) return result;
                pending.back().children.push_back(std::move(result));
                have_result = false;
            }
            auto& frame = pending.back();
            scanToNextSymbol();
            const bool tuple = frame.head == "Tuple";
            if ((tuple && *bufptr != ')') || (!tuple && frame.children.size() < frame.arity)) {
                if (!*bufptr || *bufptr == ')') err_arity_mis(frame.head, frame.line);
                continue;
            }
            if (frame.head == "Array" || frame.head == "Set") {
                const std::string key = frame.head == "Array"
                    ? "ARRAY_" + frame.children[0]->toString() + "_" + frame.children[1]->toString()
                    : "SET_" + frame.children[0]->toString();
                result = getSymbolManager()->resolveSort(key);
                if (!result) {
                    result = frame.head == "Array"
                        ? getSortManager()->createArraySort(frame.children[0], frame.children[1])
                        : getSortManager()->createSetSort(frame.children[0]);
                    getSymbolManager()->registerSort(key, result);
                }
            } else if (tuple) result = getSortManager()->createTupleSort(frame.children);
            else if (frame.head == "RegEx") {
                if (!frame.children[0]->isStr())
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "RegEx sort expects String alphabet", frame.line);
                result = SortManager::REG_SORT;
            } else if (frame.arity > 0) {
                result = std::make_shared<Sort>(*frame.prototype);
                result->children = std::move(frame.children);
            } else result = frame.prototype;
            parseRpar();
            pending.pop_back();
            have_result = true;
        }
    }

	std::vector<std::shared_ptr<DAGNode>> Parser::parseParams() {

		std::vector<std::shared_ptr<DAGNode>> params;

		while (*bufptr != ')'){
			std::shared_ptr<DAGNode> expr = parseExpr();
			params.emplace_back(expr);
		}

		return params;

	}

	// struct for let context
	struct LetContext {
		std::vector<std::shared_ptr<DAGNode>> params;  // let bind vars for current level
		std::vector<std::string> binding_names;  // parallel RHSs retain the outer scope
		std::shared_ptr<DAGNode> result;  // Store the result directly
		std::shared_ptr<DAGNode> bind_var_list;  // LET_BIND_VAR_LIST for current level
		int nesting_level;
		bool is_complete;
		bool scope_pushed = false;
		std::unordered_set<std::string> frame_names;
		std::vector<std::pair<std::string, std::shared_ptr<DAGNode>>> pending_bindings;
		
		LetContext(int level = 0) : result(nullptr), bind_var_list(nullptr), nesting_level(level), is_complete(false) {}
	};

	// parse let expression preserving the let-binding
	// (let (<keybinding>+) expr), return expr
	// In this function, the let-binding is preserved, and the let-binding is not expanded
	// So the bind_var cannot be the same in different let-binding
	// For example, (let ((x 1) (x 2)) x) is not allowed
	// Use let-chain to parse the let expression
	// let-chain: [LET_BIND_VAR_LIST, LET_BIND_VAR_LIST, ..., Body]
	// LET_BIND_VAR_LIST: [(<symbol> expr)]
	// Body: expr
	std::shared_ptr<DAGNode> Parser::parsePreservingLet(){
		// Iterative let parser that preserves let-structure as NT_LET_CHAIN.
		// Uses unified let scope with pushLetScope/popLetScope for shadowing support.
		
		std::vector<LetContext> stateStack;
		std::vector<std::shared_ptr<DAGNode>> all_bind_var_lists;
		stateStack.emplace_back(LetContext(0));
		parseLpar();
		
		while (!stateStack.empty()) {
			auto &currentState = stateStack.back();
			auto &params = currentState.params;
			
			if(!currentState.is_complete){
				getSymbolManager()->pushLetScope();
				currentState.scope_pushed = true;
				
				while (*bufptr != ')') {
					parseLpar();
					size_t name_ln = line_number;
					std::string name = getSymbol();
					
					if (currentState.frame_names.count(name)) {
						for (auto &state : stateStack) {
							if (state.scope_pushed) {
								getSymbolManager()->popLetScope();
								state.scope_pushed = false;
							}
						}
						err_sym_mis("Duplicate variable binding: " + name, name_ln);
					}
					
					std::shared_ptr<DAGNode> expr = parseExpr();
					if (expr->isErr()) {
						for (auto &state : stateStack) {
							if (state.scope_pushed) {
								getSymbolManager()->popLetScope();
								state.scope_pushed = false;
							}
						}
						err_all(expr, name, name_ln);
					}
					
					std::shared_ptr<DAGNode> let_var = mkLetBindVar(name, expr);
					currentState.pending_bindings.emplace_back(name, let_var);
					currentState.frame_names.insert(name);
					params.emplace_back(let_var);
					parseRpar();
				}
				
				if (params.empty()) {
					for (auto &state : stateStack) {
						if (state.scope_pushed) {
							getSymbolManager()->popLetScope();
							state.scope_pushed = false;
						}
					}
					err_sym_mis("let requires at least one binding", line_number);
				}
				// SMT-LIB let bindings are simultaneous. Every RHS must be
				// parsed in the outer environment; only the body sees this frame.
				for (const auto& binding : currentState.pending_bindings)
					getSymbolManager()->registerLet(binding.first, binding.second);
				currentState.bind_var_list = mkLetBindVarList(params);
				all_bind_var_lists.emplace_back(currentState.bind_var_list);
				parseRpar();
			}
			
			if (*bufptr == '(' && peekSymbol() == "let") {
				parseLpar();
				std::string let_key = getSymbol();
				condAssert(let_key == "let", "Invalid keyword for let");
				parseLpar();
				stateStack.emplace_back(LetContext(currentState.nesting_level + 1));
			}
			else{
				if(*bufptr != ')'){
					currentState.result = parseExpr();
				}
				
				auto completedState = currentState;
				if (completedState.scope_pushed) {
					getSymbolManager()->popLetScope();
					completedState.scope_pushed = false;
				}
				stateStack.pop_back();
				
				if (stateStack.empty()) {
					return mkLetChain(all_bind_var_lists, completedState.result);
				}
				else{
					parseRpar();
					stateStack.back().result = completedState.result;
					stateStack.back().is_complete = true;
				}
			}
		}
		
		return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
	}
	/*
	keybinding ::= (<symbol> expr)
	(let (<keybinding>+) expr), return expr
	*/
	std::shared_ptr<DAGNode> Parser::parseLet() {
		// Iterative let parser that expands let-bindings inline.
		// Uses unified let scope with pushLetScope/popLetScope for shadowing support.
		
		std::vector<LetContext> stateStack;
		stateStack.emplace_back(LetContext(0));
		parseLpar();
		
		while (!stateStack.empty()) {
			auto &currentState = stateStack.back();
			auto &params = currentState.params;
			
			if(!currentState.is_complete){
				getSymbolManager()->pushLetScope();
				currentState.scope_pushed = true;
				
				while (*bufptr != ')') {
					parseLpar();
					size_t name_ln = line_number;
					std::string name = getSymbol();
					
					if (currentState.frame_names.count(name)) {
						for (auto &state : stateStack) {
							if (state.scope_pushed) {
								getSymbolManager()->popLetScope();
								state.scope_pushed = false;
							}
						}
						err_sym_mis("Duplicate variable binding: " + name, name_ln);
					}
					
					std::shared_ptr<DAGNode> expr = parseExpr();
					if (expr->isErr()) {
						for (auto &state : stateStack) {
							if (state.scope_pushed) {
								getSymbolManager()->popLetScope();
								state.scope_pushed = false;
							}
						}
						err_all(expr, name, name_ln);
					}
					
					currentState.pending_bindings.emplace_back(name, expr);
					currentState.frame_names.insert(name);
					params.emplace_back(expr);
					parseRpar();
				}
				
				if (params.empty()) {
					for (auto &state : stateStack) {
						if (state.scope_pushed) {
							getSymbolManager()->popLetScope();
							state.scope_pushed = false;
						}
					}
					err_sym_mis("let requires at least one binding", line_number);
				}
				for (const auto& binding : currentState.pending_bindings)
					getSymbolManager()->registerLet(binding.first, binding.second);
				parseRpar();
			}
			
			if (currentState.is_complete && *bufptr == ')') {
				if (currentState.scope_pushed) {
					getSymbolManager()->popLetScope();
					currentState.scope_pushed = false;
				}
				std::shared_ptr<DAGNode> result = currentState.result;
				stateStack.pop_back();
				if (stateStack.empty()) {
					return result;
				}
				parseRpar();
				stateStack.back().result = result;
				stateStack.back().is_complete = true;
				continue;
			}

			if (*bufptr == '(' && peekSymbol() == "let") {
				parseLpar();
				std::string let_key = getSymbol();
				condAssert(let_key == "let", "Invalid keyword for let");
				parseLpar();
				stateStack.emplace_back(LetContext(currentState.nesting_level + 1));
			}
			else{
				std::shared_ptr<DAGNode> completedResult;
				if(*bufptr != ')'){
					currentState.result = parseExpr();
					completedResult = currentState.result;
				} else {
					currentState.result = mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
					completedResult = currentState.result;
				}
				if (currentState.scope_pushed) {
					getSymbolManager()->popLetScope();
					currentState.scope_pushed = false;
				}
				stateStack.pop_back();
				if (stateStack.empty()) {
					return completedResult;
				}
				else{
					parseRpar();
					stateStack.back().result = completedResult;
					stateStack.back().is_complete = true;
				}
			}
		}
		
		return mkErr(ERROR_TYPE::ERR_UNEXP_EOF);
	}

	// Helper function to preview the next symbol without consuming input
	std::string Parser::peekSymbol() {
		char *save_bufptr = bufptr;
		SCAN_MODE save_mode = scan_mode;
		size_t save_line = line_number;
		
		std::string symbol;
		if (*bufptr == '(') {
			bufptr++;
			scanToNextSymbol();
			symbol = getSymbol();
		} else {
			symbol = getSymbol();
		}
		
		// Restore state
		bufptr = save_bufptr;
		scan_mode = save_mode;
		line_number = save_line;
		
		return symbol;
	}

	/** The key under which dtParamBinding records the APPLIED datatype sort for a
	 *  constructor, whose declared result is the bare name. Not a valid SMT-LIB
	 *  symbol, so it cannot collide with a parameter. */
	static const char* const kDtSelfKey = "\x01self";

	/** Collect a parameter binding by matching a DECLARED sort against an ACTUAL
	 *  one. Names in @p names are the parameters; anything else must agree
	 *  structurally, and a disagreement is reported by the caller's sort check
	 *  rather than here. */
    static void matchSortParams(const std::shared_ptr<Sort>& declared,
                                const std::shared_ptr<Sort>& actual,
                                const std::unordered_set<std::string>& names,
                                std::unordered_map<std::string, std::shared_ptr<Sort>>& out) {
        using Pair = std::pair<std::shared_ptr<Sort>, std::shared_ptr<Sort>>;
        std::vector<Pair> pending{{declared, actual}};
        std::unordered_map<const Sort*, std::unordered_set<const Sort*>> visited;
        while (!pending.empty()) {
            auto current = std::move(pending.back());
            pending.pop_back();
            if (!current.first || !current.second) continue;
            if (!visited[current.first.get()].insert(current.second.get()).second) continue;
            if (names.count(current.first->name)) {
                out.emplace(current.first->name, current.second);
                continue;
            }
            const std::size_t count = std::min(current.first->children.size(), current.second->children.size());
            for (std::size_t i = count; i > 0; --i)
                pending.emplace_back(current.first->children[i - 1], current.second->children[i - 1]);
        }
    }

    // Rebuild only changed sort paths and retain sharing under one binding map.
    static std::shared_ptr<Sort> substituteSortParams(
            const std::shared_ptr<Sort>& root,
            const std::unordered_map<std::string, std::shared_ptr<Sort>>& bindings) {
        if (!root || bindings.empty()) return root;
        struct Frame { std::shared_ptr<Sort> sort; std::size_t next = 0; };
        std::vector<Frame> pending{{root}};
        std::unordered_map<const Sort*, std::shared_ptr<Sort>> completed;
        std::unordered_set<const Sort*> active{root.get()};
        while (!pending.empty()) {
            auto& frame = pending.back();
            const auto binding = bindings.find(frame.sort->name);
            if (binding != bindings.end()) {
                completed.emplace(frame.sort.get(), binding->second);
                active.erase(frame.sort.get());
                pending.pop_back();
                continue;
            }
            if (frame.next < frame.sort->children.size()) {
                auto child = frame.sort->children[frame.next++];
                if (!child || completed.count(child.get())) continue;
                condAssert(active.insert(child.get()).second, "cyclic applied sort in datatype substitution");
                pending.push_back({std::move(child)});
                continue;
            }
            bool changed = false;
            std::vector<std::shared_ptr<Sort>> children;
            children.reserve(frame.sort->children.size());
            for (const auto& child : frame.sort->children) {
                auto replacement = child ? completed.at(child.get()) : nullptr;
                changed |= replacement != child;
                children.push_back(std::move(replacement));
            }
            auto result = frame.sort;
            if (changed) {
                result = std::make_shared<Sort>(*frame.sort);
                result->children = std::move(children);
            }
            completed.emplace(frame.sort.get(), std::move(result));
            active.erase(frame.sort.get());
            pending.pop_back();
        }
        return completed.at(root.get());
    }

	/** The sort-parameter binding for an application of a PARAMETRIC datatype's
	 *  member, empty when the datatype has none.
	 *
	 *  A member is polymorphic and its declaration records the parameters
	 *  rather than an instance: `hd` is declared `L -> X`, so applying it to an
	 *  `(L Int)` must give `Int` and not `X` -- a sort no longer in scope, over
	 *  which the next operator reports a type mismatch naming a symbol the
	 *  script never wrote.
	 *
	 *  For a SELECTOR or TESTER the argument determines everything: its sort is
	 *  the instance, and its sort arguments are the parameters in order. Its
	 *  declared domain cannot serve, because that is the BARE datatype -- `L`
	 *  carrying its arity and no arguments -- with nothing in it to match a
	 *  parameter against.
	 *
	 *  For a CONSTRUCTOR the parameters appear among the argument sorts, so they
	 *  are matched structurally; the result is the bare datatype name and is
	 *  applied to the bindings in parameter order, under the reserved key below.
	 *  A constructor that mentions no parameter -- `nil` -- cannot be resolved
	 *  this way and needs the script's own `(as nil (L Int))`.
	 */
	void Parser::dtParamBinding(const std::shared_ptr<DAGNode>& fun,
	                            const std::vector<std::shared_ptr<DAGNode>>& params,
	                            std::unordered_map<std::string, std::shared_ptr<Sort>>& out){
		if(!fun) return;
		const std::vector<std::shared_ptr<DAGNode>> declared = fun->getFuncParams();
		const std::shared_ptr<Sort> ret = fun->getSort();
		const std::string dt_name = ret ? ret->name : std::string();
		const auto pit = datatype_params_.find(dt_name);
		const std::string arg_dt =
			(!params.empty() && params[0] && params[0]->getSort())
				? params[0]->getSort()->name : std::string();
		const auto ait = datatype_params_.find(arg_dt);
		const std::vector<std::string>* names = nullptr;
		if(pit != datatype_params_.end()) names = &pit->second;
		else if(ait != datatype_params_.end()) names = &ait->second;
		if(!names || names->empty()) return;

		const std::unordered_set<std::string> nameset(names->begin(), names->end());
		if(ait != datatype_params_.end() && !params.empty() && params[0]
		   && params[0]->getSort()){
			const std::shared_ptr<Sort> inst = params[0]->getSort();
			const auto& kids = inst->children;
			for(size_t i = 0; i < names->size() && i < kids.size(); i++){
				out[(*names)[i]] = kids[i];
			}
			// The datatype's own NAME binds to the instance. A selector's
			// declared domain is the BARE datatype -- `hd : L -> X`, with `L`
			// carrying its arity and no arguments -- and an applied instance is
			// a different sort from it now that a datatype's arguments count in
			// a comparison. Without this binding `(hd (tl l))` fails its own
			// argument check: `tl` correctly returns `(L Int)`, and `hd`
			// declares it takes `L`.
			if(!kids.empty()) out[arg_dt] = inst;
		}
		for(size_t i = 0; i < params.size() && i < declared.size(); i++){
			if(!declared[i] || !params[i]) continue;
			matchSortParams(declared[i]->getSort(), params[i]->getSort(), nameset, out);
		}
		if(pit != datatype_params_.end() && ret && ret->children.empty()
		   && out.size() >= names->size()){
			auto applied = std::make_shared<Sort>(*ret);
			bool complete = true;
			for(const std::string& pn : *names){
				const auto b = out.find(pn);
				if(b == out.end()){ complete = false; break; }
				applied->children.push_back(b->second);
			}
			if(complete) out[kDtSelfKey] = applied;
		}
	}

	/** The result sort an application should carry. Returns the declared sort
	 *  unchanged for a non-parametric datatype and for everything else, so the
	 *  cost is one failed map lookup on the ordinary path. */
	std::shared_ptr<Sort> Parser::dtAppliedSort(
			const std::shared_ptr<DAGNode>& fun,
			const std::vector<std::shared_ptr<DAGNode>>& params){
		std::unordered_map<std::string, std::shared_ptr<Sort>> b;
		dtParamBinding(fun, params, b);
		if(b.empty()) return fun ? fun->getSort() : nullptr;
		const auto self = b.find(kDtSelfKey);
		if(self != b.end()) return self->second;
		return substituteSortParams(fun->getSort(), b);
	}

	std::shared_ptr<DAGNode> Parser::applyFun(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> & params){
		// check the number of params
		if (fun->getFuncParamsSize() != params.size()){
			return mkErr(ERROR_TYPE::ERR_PARAM_MIS);
		}

		// ...and their SORTS, which were not checked at all. A declaration is a
		// signature, and an application that ignores it is not an application
		// of that function:
		//
		//     (declare-fun f (Int) Bool)
		//     (declare-const b Bool)
		//     (assert (f b))            -- accepted, and is not a term
		//
		// The count was checked and the sorts were not, so the half of the
		// signature that says what the arguments MEAN was carried by nothing.
		//
		// Sort::operator== is what decides, so the numeric leniency the rest of
		// the parser depends on is unchanged: a literal carries IntOrReal and
		// compares equal to both Int and Real, so `(f 1)` against an Int or a
		// Real parameter still applies.
		const std::vector<std::shared_ptr<DAGNode>> declared = fun->getFuncParams();

		// A member of a PARAMETRIC datatype is polymorphic, and its declaration
		// records the parameters rather than any instance of them: `hd` is
		// declared `L -> X`, so applying it to an `(L Int)` must give `Int` and
		// not `X`. The binding is read off the arguments -- for a selector or a
		// tester there is one argument and it determines every parameter, and
		// for a constructor the parameters appear among its argument sorts.
		//
		// Without this the declaration and the application disagree: the term
		// gets sort `X`, a sort no longer in scope, and the next operator over
		// it reports a type mismatch naming a symbol the script never wrote.
		std::unordered_map<std::string, std::shared_ptr<Sort>> dt_binding;
		dtParamBinding(fun, params, dt_binding);

		for (size_t i = 0; i < params.size() && i < declared.size(); i++){
			if (!declared[i] || !params[i]) continue;
			const std::shared_ptr<Sort> want =
				substituteSortParams(declared[i]->getSort(), dt_binding);
			const std::shared_ptr<Sort> got = params[i]->getSort();
			// A missing sort on either side is someone else's error to report;
			// refusing here would turn it into a misleading one.
			if (!want || !got || want->isNull() || got->isNull()) continue;
			if (*want != *got){
				return mkErr(ERROR_TYPE::ERR_TYPE_MIS);
			}
		}

        // The declaration is already recursive while its body is being parsed.
        if (fun->isFuncRec() && (fun->getFuncBody()->isNull() ||
            !getOptions()->getExpandRecursiveFunctions())) return mkApplyRecFunc(fun, params);

		// For declare-fun (uninterpreted functions), create a function application node
		if(fun->getFuncBody()->isNull()){
			// Determine if this is a datatype constructor/selector/tester
			NODE_KIND nk = getDtFunctionKind(fun->getSort(), fun->getName(), params);
			std::shared_ptr<Sort> ret_sort = fun->getSort();
			if(!dt_binding.empty()){
				const auto self = dt_binding.find(kDtSelfKey);
				ret_sort = self != dt_binding.end()
					? self->second
					: substituteSortParams(ret_sort, dt_binding);
			}
			std::shared_ptr<DAGNode> result = getNodeManager()->createNode(ret_sort, nk, fun->getName(), params);
			return result;
		}

	// For recursive functions (define-fun-rec), behavior depends on expand_recursive_functions option
	// If expand_recursive_functions is true, expand it like define-fun
	// If false (default), create a recursive function application node to avoid infinite recursion
	if(fun->isFuncRec()){
		if(!getOptions()->getExpandRecursiveFunctions()){
			// Don't expand recursive functions (default behavior)
			return mkApplyRecFunc(fun, params);
		}
		// Otherwise, fall through to expand it like define-fun
	}
	else if(fun->isFuncDec()){
		// a only declared function, i.e., uninterpreted function or datatype function
		return mkApplyUF(fun->getSort(), fun->getName(), params);
	}

	// For regular functions (define-fun), check expand_functions option
	if(fun->isFuncDef()){
		if(!getOptions()->getExpandFunctions()){
			// Don't expand functions, create a function application node
			return mkApplyFunc(fun, params);
		}
		// Otherwise, fall through to expand the function
	}

	if(fun->getFuncBody()->isErr()){
		return fun->getFuncBody();
	}
	
	// Expand the function: replace parameters with actual arguments
	// variable map for local variables
	std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> new_params_map;
	std::vector<std::shared_ptr<DAGNode>> func_params = fun->getFuncParams();
	for (size_t i = 0; i < func_params.size(); i++) {
		if(params[i]->isErr()){
			return params[i];
		}
		new_params_map.emplace(func_params[i], params[i]);
	}
	
	// function content
	std::shared_ptr<DAGNode> formula = fun->getFuncBody();

	// Iterative implementation to replace recursive applyFunPostOrder
	return applyFunPostOrder(formula, new_params_map);
	}

    // Substitution is keyed by binder identity. Definition/symbol children of
    // applications are metadata and must never be substituted or unfolded here.
    std::shared_ptr<DAGNode> Parser::applyFunPostOrder(std::shared_ptr<DAGNode> node,
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& params) {
        if (!node) return nullptr;
        std::vector<std::pair<std::shared_ptr<DAGNode>, bool>> todo{{node, false}};
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> results;
        while (!todo.empty()) {
            auto [current, processed] = todo.back();
            todo.pop_back();
            if (results.count(current)) continue;
            if (auto it = params.find(current); it != params.end()) {
                results.emplace(current, it->second);
                continue;
            }
            if (!current->getChildrenSize()) {
                results.emplace(current, current);
                continue;
            }
            const bool application = current->isFuncApplication() || current->isFuncRecApplication();
            const size_t first = application ? 1 : 0;
            if (!processed) {
                todo.emplace_back(current, true);
                for (size_t i = current->getChildrenSize(); i > first; --i)
                    todo.emplace_back(current->getChild(i - 1), false);
                continue;
            }
            std::vector<std::shared_ptr<DAGNode>> args;
            bool changed = false;
            for (size_t i = first; i < current->getChildrenSize(); ++i) {
                auto child = results.at(current->getChild(i));
                changed |= child != current->getChild(i);
                args.push_back(child);
            }
            auto result = current;
            if (current->isFuncApplication()) result = applyFun(current->getChild(0), args);
            else if (changed && current->isFuncRecApplication())
                result = mkApplyRecFunc(current->getChild(0), args);
            else if (changed && (current->isUFApplication() || current->isConstructorApp() ||
                                 current->isSelectorApp() || current->isTesterApp()))
                result = getNodeManager()->createNode(current->getSort(), current->getKind(), current->getName(), args);
            else if (changed) result = mkOper(current->getSort(), current->getKind(), args);
            results.emplace(current, result);
        }
        return results.at(node);
    }

	std::shared_ptr<DAGNode> Parser::mkApplyFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params){
		// Intern function applications through NodeManager to avoid creating大量重复 NT_FUNC_APPLY 节点
		// when expand_functions=false and the same function call appears many times.
		std::vector<std::shared_ptr<DAGNode>> children;
		children.reserve(params.size() + 1);
		children.emplace_back(fun);
		for(const auto& p : params) children.emplace_back(p);
		auto res = getNodeManager()->createNode(fun->getSort(), NODE_KIND::NT_FUNC_APPLY, fun->getName(), std::move(children));
		getSymbolManager()->addStaticFunction(res);
		return res;
	}

	
    std::shared_ptr<DAGNode> Parser::mkApplyRecFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params){
        fun = getSymbolManager()->getRecursiveSymbol(fun);
        // Intern recursive function applications through NodeManager as well.
		std::vector<std::shared_ptr<DAGNode>> children;
		children.reserve(params.size() + 1);
		children.emplace_back(fun);
		for(const auto& p : params) children.emplace_back(p);
		auto res = getNodeManager()->createNode(fun->getSort(), NODE_KIND::NT_FUNC_REC_APPLY, fun->getName(), std::move(children));
		getSymbolManager()->addStaticFunction(res);
		return res;
    }

    NODE_KIND Parser::getDtFunctionKind(const std::shared_ptr<Sort>& return_sort, const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params) {
        // SymbolManager resolves quoted and bare spellings to the same
        // declaration. Datatype metadata retains that declaration's spelling.
        const auto declaration = getSymbolManager()->resolveFun(name);
        const std::string& member = declaration ? declaration->getName() : name;
        // Constructor: return sort is DT and has a constructor with this name
        if(return_sort && return_sort->isDatatype() && return_sort->hasDtConstructor(member)) {
            return NODE_KIND::NT_DT_CONSTRUCTOR;
        }
        // Selector: first param sort is DT and has a selector with this name
        if(!params.empty()) {
            auto first_sort = params[0]->getSort();
            if(first_sort && first_sort->isDatatype()) {
                if(first_sort->hasDtSelector(member)) {
                    return NODE_KIND::NT_DT_SELECTOR;
                }
                if(first_sort->hasDtTester(member)) {
                    return NODE_KIND::NT_DT_TESTER;
                }
            }
        }
        return NODE_KIND::NT_UF_APPLY;
    }

    std::shared_ptr<DAGNode> Parser::mkApplyUF(const std::shared_ptr<Sort>& sort, const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params){
        NODE_KIND nk = getDtFunctionKind(sort, name, params);
        if (nk != NODE_KIND::NT_UF_APPLY) {
            if (auto declaration = getSymbolManager()->resolveFun(name)) {
                return getNodeManager()->createNode(sort, nk, declaration->getName(), params);
            }
        }
        return getNodeManager()->createNode(sort, nk, name, params);
    }

    /** `(par (X Y) (<ctors>))` -- SMT-LIB's PARAMETRIC datatype body.
     *
     *  The parameters are sorts, and inside the body they are ordinary sorts in
     *  scope: `(cons (hd X) (tl (L X)))` needs `X` to resolve while the
     *  constructors are read and needs it gone afterwards, or the next command
     *  would see a sort the script never declared.
     *
     *  Returns the parameter names, empty when the body is not parametric. The
     *  names are kept because they are not recoverable from the sort -- a sort
     *  records its ARITY and not what its parameters were called -- and
     *  dumpSMT2 has to write the same `par` form back.
     *
     *  Leaves the buffer positioned exactly where the non-parametric form
     *  would, so the caller does not branch. */
    std::vector<std::string> Parser::parseDatatypeParams() {
        char* const save = bufptr;
        const size_t save_line = line_number;
        std::vector<std::string> params;
        // `par` sits where a constructor's `(` would, so a symbol here means
        // the parametric form and anything else means the plain one.
        if (*bufptr == '(') { return params; }
        std::string head = getSymbol();
        if (head != "par") {
            bufptr = save;
            line_number = save_line;
            return params;
        }
        scanToNextSymbol();           // getSymbol stops AT the symbol's end
        parseLpar();
        while (*bufptr != ')') {
            params.push_back(getSymbol());
            scanToNextSymbol();
        }
        parseRpar();
        parseLpar();                  // the constructor list's own '('
        return params;
    }

    void Parser::defineDatatypeConstructors(const std::shared_ptr<Sort>& dt_sort) {
        std::vector<Sort::DtConstructor> constructors;
        while (*bufptr != ')') {
            parseLpar();
            std::string ctor_name = getSymbol();
            Sort::DtConstructor ctor;
            ctor.name = ctor_name;
            while (*bufptr != ')') {
                parseLpar();
                std::string sel_name = getSymbol();
                std::shared_ptr<Sort> sel_sort = parseSort();
                parseRpar();
                ctor.selectors.push_back({sel_name, sel_sort});
            }
            parseRpar();
            constructors.push_back(ctor);
        }
        parseRpar();

        dt_sort->dt_constructors = std::make_shared<std::vector<Sort::DtConstructor>>(constructors);

        for (auto& ctor : constructors) {
            std::vector<std::shared_ptr<Sort>> sel_sorts;
            for (auto& sel : ctor.selectors)
                sel_sorts.push_back(sel.sort);
            auto ctor_node = mkFuncDec(ctor.name, sel_sorts, dt_sort);
            if (!ctor_node->isErr()) {
                getSymbolManager()->addFunctionName(ctor.name);
                context_.registerFunInScope(ctor.name);
            }
            for (auto& sel : ctor.selectors) {
                std::vector<std::shared_ptr<Sort>> sel_params = {dt_sort};
                auto sel_node = mkFuncDec(sel.name, sel_params, sel.sort);
                if (!sel_node->isErr()) {
                    getSymbolManager()->addFunctionName(sel.name);
                    context_.registerFunInScope(sel.name);
                }
            }
            std::string tester_name = "is-" + ctor.name;
            std::vector<std::shared_ptr<Sort>> tester_params = {dt_sort};
            auto tester_node = mkFuncDec(tester_name, tester_params, SortManager::BOOL_SORT);
            if (!tester_node->isErr()) {
                getSymbolManager()->addFunctionName(tester_name);
                context_.registerFunInScope(tester_name);
            }
        }
    }

    // MATCH EXPRESSION
    // (match <term> ((<pattern> <body>) ... ))
    std::shared_ptr<DAGNode> Parser::parseMatch(){
        // Parse the scrutinee term
        std::shared_ptr<DAGNode> scrutinee = parseExpr();

        // Collect match cases: alternating (pattern, body) pairs
        std::vector<std::shared_ptr<DAGNode>> children;
        children.push_back(scrutinee);

        auto dt_sort = scrutinee->getSort();

        scanToNextSymbol();
        parseLpar(); // open the case-list: ((<pattern> <body>) ...)
        if (*bufptr == ')') {
            err_sym_mis("match case", line_number);
        }

        std::shared_ptr<Sort> result_sort;
        scanToNextSymbol();
        while(*bufptr != ')'){
            parseLpar(); // open a case: (<pattern> <body>)

            ScopedTermBindings bindings(getSymbolManager());
            std::shared_ptr<DAGNode> pattern;

            scanToNextSymbol();
            if(*bufptr == '('){
                // Constructor pattern: (<ctor> <var1> ... <varN>)
                parseLpar();
                std::string ctor_name = getSymbol();
                if (auto declaration = getSymbolManager()->resolveFun(ctor_name)) {
                    ctor_name = declaration->getName();
                }

                // Look up the constructor in the DT sort to get selector sorts
                std::vector<std::shared_ptr<DAGNode>> pat_vars;
                if(dt_sort && dt_sort->isDatatype() && dt_sort->hasDtConstructor(ctor_name)){
                    const auto* ctor = dt_sort->getDtConstructorByName(ctor_name);
                    if(ctor){
                        for(size_t i = 0; i < ctor->selectors.size(); i++){
                            std::string var_name = getSymbol();
                            auto var = getNodeManager()->createNode(ctor->selectors[i].sort, NODE_KIND::NT_QUANT_VAR, var_name);
                            bindings.bind(var_name, var);
                            pat_vars.push_back(var);
                        }
                    }
                }
                parseRpar(); // close the pattern parens

                pattern = getNodeManager()->createNode(dt_sort, NODE_KIND::NT_DT_CONSTRUCTOR, ctor_name, pat_vars);
            } else {
                // Either a nullary constructor name or a catch-all variable
                std::string sym = getSymbol();
                const auto declaration = getSymbolManager()->resolveFun(sym);
                const std::string& member = declaration ? declaration->getName() : sym;
                if(dt_sort && dt_sort->isDatatype() && dt_sort->hasDtConstructor(member)){
                    // Nullary constructor pattern
                    pattern = getNodeManager()->createNode(dt_sort, NODE_KIND::NT_DT_CONSTRUCTOR, member, {});
                } else {
                    // Catch-all variable pattern — bind the variable to a fresh var node
                    auto var = getNodeManager()->createNode(dt_sort, NODE_KIND::NT_QUANT_VAR, sym);
                    bindings.bind(sym, var);
                    pattern = var;
                }
            }

            // Parse the body with quantifier scope active for bound pattern vars
            bool saved_in_quant = in_quantifier_scope;
            in_quantifier_scope = true;
            std::shared_ptr<DAGNode> body = parseExpr();
            in_quantifier_scope = saved_in_quant;

            // Every case of a match expression must return the same sort.
            // Record the first case and reject inconsistent later branches
            // before constructing an ill-sorted match node.
            auto body_sort = body ? body->getSort() : nullptr;
            if (!body_sort || (result_sort && !result_sort->isEqTo(body_sort))) {
                err_type_mis("match cases must have the same result sort", line_number);
            }
            if (!result_sort) {
                result_sort = body_sort;
            }

            children.push_back(pattern);
            children.push_back(body);

            parseRpar(); // close the case

            scanToNextSymbol();
        }
        parseRpar(); // close the case-list; caller closes (match ...)

        return getNodeManager()->createNode(result_sort, NODE_KIND::NT_DT_MATCH, "match", children);
    }


	// QUANTIFIERS
	// (quantifier ((<identifier> <sort>)+） <expr>)
	std::shared_ptr<DAGNode> Parser::mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort){
		auto var = getNodeManager()->createNode(sort, NODE_KIND::NT_QUANT_VAR, name);
		getSymbolManager()->registerQuantVar(name, var);
		return var;
	}
    std::shared_ptr<DAGNode> Parser::parseQuant(const std::string& type) {
        parseLpar();
        std::vector<std::shared_ptr<DAGNode>> params;
        std::vector<std::string> names;
        std::unordered_set<std::string> local;
        auto symbols = getSymbolManager();
        // Let and quantifier bindings share lexical precedence. A quantifier
        // masks an outer let; an inner let can in turn mask the quantifier.
        symbols->pushLetScope();
        struct Scope {
            std::shared_ptr<SymbolManager> symbols;
            std::vector<std::string>& names;
            ~Scope() { symbols->popQuantScope(names); symbols->popLetScope(); }
        } scope{symbols, names};
        while (*bufptr != ')') {
            parseLpar();
            const auto name = getSymbol();
            const auto key = name.size() > 2 && name.front() == '|' && name.back() == '|'
                ? name.substr(1, name.size() - 2) : name;
            if (!local.insert(key).second) err_mul_decl(name, line_number);
            const auto sort = parseSort();
            auto variable = mkQuantVar(name, sort);
            names.push_back(name);
            params.push_back(variable);
            symbols->registerLet(name, variable);
            parseRpar();
        }
        if (params.empty()) err_all(ERROR_TYPE::ERR_PARAM_MIS, "empty quantifier binder list", line_number);
        parseRpar();
        auto body = parseExpr();
        params.insert(params.begin(), body);
        return type == "forall" ? mkForall(params) : mkExists(params);
    }

	std::shared_ptr<DAGNode> Parser::mkForall(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_FORALL, params);
	}
	std::shared_ptr<DAGNode> Parser::mkExists(const std::vector<std::shared_ptr<DAGNode>> &params){
		return mkOper(SortManager::BOOL_SORT, NODE_KIND::NT_EXISTS, params);
	}

	
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params){
		std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
		return substitute(expr, params, visited);
	}
	// visited is used to avoid infinite loop
	std::shared_ptr<DAGNode> Parser::substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited){
		/*
			Convert the previously recursive implementation into an iterative, stack-based
			post-order traversal to avoid potential stack-overflow on very deep/large DAGs.
			The algorithm mirrors the logic of applyFunPostOrder used elsewhere in this file.
		*/

		// Quick hit: if we already substituted this node, return the cached result.
		if(visited.find(expr) != visited.end()){
			return visited[expr];
		}

		// (node, processed?)  processed==false  => first time we see the node
		//                      processed==true   => all children have been handled
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		todo.push(std::make_pair(expr, false));

		while(!todo.empty()){
			auto curPair   = todo.top();
			todo.pop();
			std::shared_ptr<DAGNode> current = curPair.first;
			bool processed                  = curPair.second;

			// If we already computed a substitute for this node elsewhere, skip.
			if(visited.find(current) != visited.end()){
				continue;
			}

		if(processed){
			/*
				All children have been processed – build the new node using the
				(possibly substituted) child results that are now stored in
				`visited`.
			*/
			std::vector<std::shared_ptr<DAGNode>> newChildren;
			newChildren.reserve(current->getChildrenSize());
			for(size_t i = 0; i < current->getChildrenSize(); ++i){
				newChildren.emplace_back(visited[current->getChild(i)]);
			}
			std::shared_ptr<DAGNode> newNode;
			// For nodes with meaningful names (UF applications, function applications, etc.),
			// preserve the original name instead of using kindToString
			if(current->isUFApplication() || 
			   current->isFuncApplication() || 
			   current->isFuncRecApplication() ||
			   current->isArray()) {
				// Create node with original name preserved
				newNode = getNodeManager()->createNode(current->getSort(), current->getKind(), current->getName(), newChildren);
			} else {
				// Use standard mkOper for other node types
				newNode = mkOper(current->getSort(), current->getKind(), newChildren);
			}
			visited[current] = newNode;
		}
			else{
				/* First visit */
				if(current->isVar()){
					// Variable: replace if it appears in the substitution map
					auto it = params.find(current->getName());
					visited[current] = (it != params.end()) ? it->second : current;
				}
				else if(current->isConst() || current->isFuncParam()){
					// Constants and function-parameters stay unchanged
					visited[current] = current;
				}
				else{
					// Non-leaf operator node – schedule a second visit after children
					todo.push(std::make_pair(current, true));
					// Push children (reverse order keeps original left-to-right after pop)
					for(int i = static_cast<int>(current->getChildrenSize()) - 1; i >= 0; --i){
						auto child = current->getChild(i);
						if(visited.find(child) == visited.end()){
							todo.push(std::make_pair(child, false));
						}
					}
				}
			}
		}

		return visited[expr];
	}

	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr){
		bool is_changed = false;
		return arithNormalize(expr, is_changed);
	}


	std::shared_ptr<DAGNode> Parser::arithNormalize(std::shared_ptr<DAGNode> expr, bool& is_changed){
		// Iterative implementation to avoid stack overflow on very deep/large DAGs
		if(expr->isErr()){
			is_changed = false;
			return expr;
		}

		// Expand outer let expression (expandLet itself can still be recursive, but the overall depth is usually limited)
		if(expr->isLet()){
			expr = expandLet(expr);
		}

		// Use manual post-order traversal stack
		std::stack<std::pair<std::shared_ptr<DAGNode>, bool>> todo;
		std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> result_map;   // Record normalized nodes
		std::unordered_map<std::shared_ptr<DAGNode>, bool>                     changed_map;  // Record if the node has changed

		todo.push({expr, false});

		while(!todo.empty()){
			auto [node, processed] = todo.top();
			todo.pop();

			// If already processed, skip
			if(result_map.find(node) != result_map.end()) continue;

		if(processed){
			/* Second visit: all children have been processed, can construct the current node */
			if(node->isConst() || node->isVar() || node->isArithTerm() || node->isErr()){
				result_map[node]  = node;
				changed_map[node] = false;
				continue;
			}

			if(node->isArithComp()){
				condAssert(node->getChildrenSize()==2, "ArithComp should have two children");
				std::shared_ptr<DAGNode> leftN  = result_map[node->getChild(0)];
				std::shared_ptr<DAGNode> rightN = result_map[node->getChild(1)];
				bool child_changed = changed_map[node->getChild(0)] || changed_map[node->getChild(1)];

				bool cur_changed = child_changed;
				std::shared_ptr<DAGNode> new_node = node; // default to keep unchanged

				if(!rightN->isConst()){
					cur_changed = true;
					auto left_sub = mkOper(leftN->getSort(), NODE_KIND::NT_SUB, {leftN, rightN});
					auto zero     = getZero(leftN->getSort());
					new_node      = mkOper(SortManager::BOOL_SORT, node->getKind(), {left_sub, zero});
				}else if(child_changed){
					new_node = mkOper(node->getSort(), node->getKind(), {leftN, rightN});
				}

				result_map[node]  = new_node;
				changed_map[node] = cur_changed;
				continue;
			}

			/* General operator */
			std::vector<std::shared_ptr<DAGNode>> new_children;
			bool any_changed = false;
			new_children.reserve(node->getChildrenSize());
			for(size_t i=0;i<node->getChildrenSize();++i){
				auto child = node->getChild(i);
				new_children.emplace_back(result_map[child]);
				any_changed = any_changed || changed_map[child];
			}

			std::shared_ptr<DAGNode> new_node;
			if(any_changed){
				// For nodes with meaningful names (UF applications, function applications, etc.),
				// preserve the original name instead of using kindToString
				if(	node->isUFApplication() || 
					node->isFuncApplication() || 
					node->isFuncRecApplication() ||
					node->isArray()) {
					// Create node with original name preserved
					new_node = getNodeManager()->createNode(node->getSort(), node->getKind(), node->getName(), new_children);
				} else {
					// Use standard mkOper for other node types
					new_node = mkOper(node->getSort(), node->getKind(), new_children);
				}
			} else {
				new_node = node;
			}

			// Apply array simplification if the node is an array operation
			if(new_node->isSelect() || new_node->isStore()){
				std::shared_ptr<DAGNode> simplified = simplifyArray(new_node);
				if(simplified != new_node){
					new_node = simplified;
					any_changed = true;
				}
			}

			// Apply simplification for equality operations (including array equality)
			if(new_node->isEq()){
				std::shared_ptr<DAGNode> simplified;
				if(new_node->getChildrenSize() == 2){
					simplified = simp_oper(new_node->getKind(), new_node->getChild(0), new_node->getChild(1));
				}
				else if(new_node->getChildrenSize() > 2){
					simplified = simp_oper(new_node->getKind(), new_children);
				}
				else{
					simplified = NodeManager::UNKNOWN_NODE;
				}
				if(simplified && !simplified->isUnknown()){
					new_node = simplified;
					any_changed = true;
				}
			}

			result_map[node]  = new_node;
			changed_map[node] = any_changed;
			}else{
				/* First visit */
				// Leaf node directly processed
				if(node->isConst() || node->isVar() || node->isArithTerm() || node->isErr()){
					result_map[node]  = node;
					changed_map[node] = false;
					continue;
				}

				// If it is still let, expand and push back to stack for processing
				if(node->isLet()){
					node = expandLet(node);
					todo.push({node, false});
					continue;
				}

				// Push back self (mark as visited), then push children
				todo.push({node, true});
				for(int i = static_cast<int>(node->getChildrenSize()) - 1; i >= 0; --i){
					todo.push({node->getChild(i), false});
				}
			}
		}

		is_changed = changed_map[expr];
		return result_map[expr];
	}

	std::vector<std::shared_ptr<DAGNode>> Parser::arithNormalize(std::vector<std::shared_ptr<DAGNode>> exprs){
		std::vector<std::shared_ptr<DAGNode>> res;
		for(auto& expr : exprs){
			res.emplace_back(arithNormalize(expr));
		}
		return res;
	}


	// aux functions
	NODE_KIND Parser::getAddOp(std::shared_ptr<Sort> sort){
		if(sort->isInt() || sort->isReal() || sort->isIntOrReal()){
			return NODE_KIND::NT_ADD;
		}
		else if(sort->isBv()){
			return NODE_KIND::NT_BV_ADD;
		}
		else if(sort->isFp()){
			return NODE_KIND::NT_FP_ADD;
		}
		else{
			return NODE_KIND::NT_ERROR;
		}
	}
	NODE_KIND Parser::getNegatedKind(NODE_KIND kind){
		return SOMTParser::getNegatedKind(kind);
	}
	std::shared_ptr<DAGNode> Parser::getZero(std::shared_ptr<Sort> sort){
		if(sort->isInt() || sort->isIntOrReal()){
			return mkConstInt(0);
		}
		else if(sort->isReal()){
			return mkConstReal(0.0);
		}
		else if(sort->isBv()){
			return mkConstBv("0", sort->getBitWidth());
		}
		else if(sort->isFp()){
			return mkConstFp("0.0", sort->getExponentWidth(), sort->getSignificandWidth());
		}
		else if(sort->isStr()){
			return mkConstStr("");
		}
		else{
			return mkErr(ERROR_TYPE::ERR_UNKWN_SYM);
		}
	}

	// Helper function to parse symbol name that may start with invalid characters
	// Returns the symbol name, wrapping with |...| if it starts with invalid characters
	std::string Parser::parseModelSymbolName() {
		if (*bufptr == '(') {
			// Check if this is an empty symbol (next is parameter list) or a symbol starting with '('
			// Skip whitespace after '('
			char* lookahead = bufptr + 1;
			while (*lookahead && (*lookahead == ' ' || *lookahead == '\t' || *lookahead == '\n' || *lookahead == '\r' || *lookahead == '\v' || *lookahead == '\f')) {
				lookahead++;
			}
			// If next is ')' or '(', it's likely a parameter list, so empty symbol
			if (*lookahead == ')' || *lookahead == '(') {
				return "||";
			} else {
				// Symbol starts with '(', need to parse it and wrap with |...|
				// Parse the symbol manually: read all non-whitespace characters until we hit whitespace
				// that is followed by '(' or ')' (parameter list start)
				char* name_start = bufptr;
				while (*bufptr && *bufptr != 0) {
					// Check if current position is whitespace
					if (*bufptr == ' ' || *bufptr == '\t' || *bufptr == '\n' || *bufptr == '\r' || *bufptr == '\v' || *bufptr == '\f') {
						// Found whitespace, check what comes after
						char* after_ws = bufptr + 1;
						while (*after_ws && (*after_ws == ' ' || *after_ws == '\t' || *after_ws == '\n' || *after_ws == '\r' || *after_ws == '\v' || *after_ws == '\f')) {
							after_ws++;
						}
						// If next non-whitespace is '(' or ')', this is the end of symbol
						if (*after_ws == '(' || *after_ws == ')') {
							break;
						}
					}
					bufptr++;
				}
				std::string raw_name(name_start, bufptr - name_start);
				scanToNextSymbol();
				return "|" + raw_name + "|";
			}
		} else {
			std::string name = getSymbol();
			// Check if symbol starts with invalid character (digit, ')', etc.)
			if (!name.empty()) {
				char first_char = name[0];
				if ((first_char >= '0' && first_char <= '9') || first_char == ')' || first_char == ';') {
					// Invalid first character, wrap with |...|
					return "|" + name + "|";
				}
			}
			return name;
		}
		return std::string(); // unreachable — all if/else branches above return
	}

	// parse model
	ModelPtr Parser::parseModel(const std::string& model, bool only_declared){
		std::shared_ptr<Model> model_ptr = std::make_shared<Model>();
		
		// Save original parser state
		char* original_buffer = buffer;
		char* original_bufptr = bufptr;
		size_t original_buflen = buflen;
		bool original_parsing_file = parsing_file;
		
		// Set temporary parsing state
		parsing_file = false;
		size_t original_line_number = line_number;
		line_number = 1;
		buffer = safe_strdup(model);
		if (!buffer) {
			line_number = original_line_number;
			return model_ptr;
		}
		buflen = model.length();
		bufptr = buffer;
		scanToNextSymbol();
		
		try {
			// Check if wrapped with (model ...) or just (...)
			char* start_pos = bufptr;
			if (*bufptr == '(') {
				char* lookahead = bufptr + 1;
				while (*lookahead && (*lookahead == ' ' || *lookahead == '\t' || *lookahead == '\n' || *lookahead == '\r')) {
					lookahead++;
				}
				
				// Check if next symbol is "model"
				if (strncmp(lookahead, "model", 5) == 0 && 
				    (lookahead[5] == ' ' || lookahead[5] == '\t' || lookahead[5] == '\n' || lookahead[5] == '\r' || lookahead[5] == '(')) {
					// Skip outer (model ...)
					parseLpar();
					std::string keyword = getSymbol();
					// Now we're inside (model ...) or just (...), continue parsing define-fun
				} else {
					// Just a plain ( wrapping the define-funs, skip it
					parseLpar();
				}
			}
			start_pos = bufptr;
			
			// FIRST PASS: Declare all functions (including parameterized ones)
			// This allows forward references in expressions
			while (*bufptr && *bufptr != 0) {
				// Skip whitespace
				while (*bufptr && (*bufptr == ' ' || *bufptr == '\t' || *bufptr == '\n' || *bufptr == '\r')) {
					bufptr++;
					if (*bufptr == '\n') line_number++;
				}
				
				if (*bufptr == 0 || *bufptr == ')') break;
				
				if (*bufptr != '(') break;
				
				// Parse one define-fun
				parseLpar();
				std::string keyword = getSymbol();
				
				if (keyword != "define-fun") {
					// Not a define-fun, skip it
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Parse function name (may start with invalid characters like '(')
				std::string func_name = parseModelSymbolName();
				
				// Parse parameter list
				parseLpar();
				std::vector<std::shared_ptr<Sort>> param_sorts;
				while (*bufptr != ')') {
					parseLpar();
					getSymbol(); // parameter name (ignored)
					std::shared_ptr<Sort> param_sort = parseSort();
					param_sorts.push_back(param_sort);
					parseRpar();
				}
				parseRpar();
				
				// Parse return type
				std::shared_ptr<Sort> return_sort = parseSort();
				
				// Declare the function so it can be referenced.
				// Solver models re-define functions the input already
				// declared (uninterpreted functions get concrete bodies in
				// get-model output) — skip re-declaration instead of raising
				// a spurious "Multiple declarations" error.
				if (!param_sorts.empty()) {
					if (!getSymbolManager()->getFun(func_name)) {
						mkFuncDec(func_name, param_sorts, return_sort);
					}
					if (!getSymbolManager()->getFun(func_name) || !getSymbolManager()->hasFunctionName(func_name)) {
						getSymbolManager()->addFunctionName(func_name);
					}
				}
				
				// Skip the function body for now
				skipToRpar();
				parseRpar();
			}
			
			// SECOND PASS: Parse variable values (only for 0-parameter functions)
			// Reset to start position
			bufptr = start_pos;
			line_number = 1;
			
			while (*bufptr && *bufptr != 0) {
				// Skip whitespace
				while (*bufptr && (*bufptr == ' ' || *bufptr == '\t' || *bufptr == '\n' || *bufptr == '\r')) {
					bufptr++;
					if (*bufptr == '\n') line_number++;
				}
				
				if (*bufptr == 0 || *bufptr == ')') break;
				
				if (*bufptr != '(') break;
				
				// Parse one define-fun
				parseLpar();
				std::string keyword = getSymbol();
				
				if (keyword != "define-fun") {
					// Not a define-fun, skip it
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Parse variable name (can be any symbol including | | or ||)
				// Note: In SMT-LIB, | | means a symbol containing a space, || means an empty symbol
				// May start with invalid characters like '('
				std::string var_name = parseModelSymbolName();
				
				// Parse parameter list
				parseLpar();
				bool has_params = (*bufptr != ')');
				
				// Skip parameters
				while (*bufptr != ')') {
					parseLpar();
					getSymbol(); // parameter name
					parseSort(); // parameter type
					parseRpar();
				}
				parseRpar();
				
				// If has parameters, skip this function definition in second pass
				if (has_params) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Parse type
				std::shared_ptr<Sort> var_sort = parseSort();
				if (!var_sort) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Check if only declared variables
				if (only_declared && !isDeclaredVariable(var_name)) {
					skipToRpar();
					parseRpar();
					continue;
				}
				
				// Define variable first
				std::shared_ptr<DAGNode> var_node = mkVar(var_sort, var_name);
				
				// Parse value expression
				std::shared_ptr<DAGNode> value = parseExpr();
				
				if (value && !value->isErr()) {
					model_ptr->add(var_node, value);
				}
				
				// Close the define-fun
				parseRpar();
			}
			
		} catch (...) {
			// Ignore errors and return what we have
		}
		
		// Restore original state
		delete[] buffer;
		buffer = original_buffer;
		bufptr = original_bufptr;
		buflen = original_buflen;
		parsing_file = original_parsing_file;
		
		return model_ptr;
	}

	ModelPtr Parser::newEmptyModel(){
		// new empty model
		std::shared_ptr<Model> model = std::make_shared<Model>();
		// get all variables
		std::vector<std::shared_ptr<DAGNode>> vars = getDeclaredVariables();
		for(auto& var : vars){
			model->addVar(var);
		}
		return model;
	}

	bool Parser::isDeclaredVariable(const std::string& var_name) const{
		return getSymbolManager()->hasVar(var_name);
	}
	bool Parser::isDeclaredFunction(const std::string& func_name) const{
		return getSymbolManager()->getFun(func_name) != nullptr;
	}


	// error operations: store ERROR_TYPE in error node's name for correct err_all(DAGNode) dispatch
	static std::string errorTypeToName(ERROR_TYPE t) {
		switch (t) {
			case ERROR_TYPE::ERR_UNEXP_EOF: return "ERR_UNEXP_EOF";
			case ERROR_TYPE::ERR_SYM_MIS: return "ERR_SYM_MIS";
			case ERROR_TYPE::ERR_UNKWN_SYM: return "ERR_UNKWN_SYM";
			case ERROR_TYPE::ERR_PARAM_MIS: return "ERR_PARAM_MIS";
			case ERROR_TYPE::ERR_PARAM_NBOOL: return "ERR_PARAM_NBOOL";
			case ERROR_TYPE::ERR_PARAM_NNUM: return "ERR_PARAM_NNUM";
			case ERROR_TYPE::ERR_PARAM_NSAME: return "ERR_PARAM_NSAME";
			case ERROR_TYPE::ERR_LOGIC: return "ERR_LOGIC";
			case ERROR_TYPE::ERR_MUL_DECL: return "ERR_MUL_DECL";
			case ERROR_TYPE::ERR_MUL_DEF: return "ERR_MUL_DEF";
			case ERROR_TYPE::ERR_ZERO_DIVISOR: return "ERR_ZERO_DIVISOR";
			case ERROR_TYPE::ERR_FUN_LOCAL_VAR: return "ERR_FUN_LOCAL_VAR";
			case ERROR_TYPE::ERR_ARI_MIS: return "ERR_ARI_MIS";
			case ERROR_TYPE::ERR_TYPE_MIS: return "ERR_TYPE_MIS";
			case ERROR_TYPE::ERR_NEG_PARAM: return "ERR_NEG_PARAM";
		}
		return "ERR_UNKWN_SYM";
	}
	static ERROR_TYPE errorNameToType(const std::string& name) {
		if (name == "ERR_UNEXP_EOF") return ERROR_TYPE::ERR_UNEXP_EOF;
		if (name == "ERR_SYM_MIS") return ERROR_TYPE::ERR_SYM_MIS;
		if (name == "ERR_UNKWN_SYM") return ERROR_TYPE::ERR_UNKWN_SYM;
		if (name == "ERR_PARAM_MIS") return ERROR_TYPE::ERR_PARAM_MIS;
		if (name == "ERR_PARAM_NBOOL") return ERROR_TYPE::ERR_PARAM_NBOOL;
		if (name == "ERR_PARAM_NNUM") return ERROR_TYPE::ERR_PARAM_NNUM;
		if (name == "ERR_PARAM_NSAME") return ERROR_TYPE::ERR_PARAM_NSAME;
		if (name == "ERR_LOGIC") return ERROR_TYPE::ERR_LOGIC;
		if (name == "ERR_MUL_DECL") return ERROR_TYPE::ERR_MUL_DECL;
		if (name == "ERR_MUL_DEF") return ERROR_TYPE::ERR_MUL_DEF;
		if (name == "ERR_ZERO_DIVISOR") return ERROR_TYPE::ERR_ZERO_DIVISOR;
		if (name == "ERR_FUN_LOCAL_VAR") return ERROR_TYPE::ERR_FUN_LOCAL_VAR;
		if (name == "ERR_ARI_MIS") return ERROR_TYPE::ERR_ARI_MIS;
		if (name == "ERR_TYPE_MIS") return ERROR_TYPE::ERR_TYPE_MIS;
		if (name == "ERR_NEG_PARAM") return ERROR_TYPE::ERR_NEG_PARAM;
		return ERROR_TYPE::ERR_UNKWN_SYM;
	}
	std::shared_ptr<DAGNode> Parser::mkErr(const ERROR_TYPE t){
		return getNodeManager()->createNode(NODE_KIND::NT_ERROR, errorTypeToName(t));
	}
	void Parser::err_all(const ERROR_TYPE e, const std::string s, const size_t ln) const {
		switch (e) {
		case ERROR_TYPE::ERR_UNEXP_EOF:
			err_unexp_eof();
			break;
		case ERROR_TYPE::ERR_SYM_MIS:
			err_sym_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_UNKWN_SYM:
			err_unkwn_sym(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_MIS:
			err_param_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NBOOL:
			err_param_nbool(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NNUM:
			err_param_nnum(s, ln);
			break;
		case ERROR_TYPE::ERR_PARAM_NSAME:
			err_param_nsame(s, ln);
			break;
		case ERROR_TYPE::ERR_LOGIC:
			err_logic(s, ln);
			break;
		case ERROR_TYPE::ERR_MUL_DECL:
			err_mul_decl(s, ln);
			break;
		case ERROR_TYPE::ERR_MUL_DEF:
			err_mul_def(s, ln);
			break;
		case ERROR_TYPE::ERR_ZERO_DIVISOR:
			err_zero_divisor(ln);
			break;
		case ERROR_TYPE::ERR_FUN_LOCAL_VAR:
			err_param_nsame(s, ln);
			break;
		case ERROR_TYPE::ERR_ARI_MIS:
			err_arity_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_TYPE_MIS:
			err_type_mis(s, ln);
			break;
		case ERROR_TYPE::ERR_NEG_PARAM:
			err_neg_param(ln);
			break;
		}
	}

	void Parser::err_all(const std::shared_ptr<DAGNode> e, const std::string s, const size_t ln) const {
		if (e->getKind() != NODE_KIND::NT_ERROR) {
			err_all(ERROR_TYPE::ERR_TYPE_MIS, s, ln);
			return;
		}
		err_all(errorNameToType(e->getName()), s, ln);
	}

	/*
	Every err_* below writes to std::cerr, never std::cout.

	This is not a style preference. dumpSMT2()/toSmt2() hand back a script that
	callers pipe straight into a solver, and somt-convert writes exactly that to
	its stdout. A diagnostic printed on the same stream is spliced into the
	middle of the SMT-LIB text, where it survives `2>/dev/null` and turns a
	visible failure into a corrupt model. These used to print to std::cout, so
	`somt-convert bad.mzn 2>/dev/null` emitted `error: Kind mismatch ...` as if
	it were part of the translation. See test/regression/
	test_parser_diagnostics_stream.cpp.
	*/
	// unexpected end of file
	void Parser::err_unexp_eof() const {
		std::cerr << "error: Unexpected end of file found." << std::endl;
		throw ParseErrorException();
	}

	// symbol missing
	void Parser::err_sym_mis(const std::string mis, const size_t ln) const {
		std::cerr << "error: \"" << mis << "\" missing in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	void Parser::err_sym_mis(const std::string mis, const std::string nm, const size_t ln) const {
		std::cerr << "error: \"" << mis << "\" missing before \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// unknown symbol
	void Parser::err_unkwn_sym(const std::string nm, const size_t ln) const {
		if (nm == "") err_unexp_eof();
		std::cerr << "error: Unknown or unexpected symbol \"" << nm << "\" in line " << ln << '.' << std::endl;
		// Carried, not only printed: an unknown symbol means this build does
		// not implement the construct, which is a different conclusion from a
		// malformed file and belongs in a different bucket.
		throw ParseErrorException(ParseErrorException::Kind::UNKNOWN_SYMBOL, nm, ln);
	}

	// wrong number of parameters
	void Parser::err_param_mis(const std::string nm, const size_t ln) const {
		std::cerr << "error: Wrong number of parameters of \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException(ParseErrorException::Kind::ARITY, nm, ln);
	}

	// paramerter type error
	void Parser::err_param_nbool(const std::string nm, const size_t ln) const {
		std::cerr << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerter is not a boolean." << std::endl;
		throw ParseErrorException();
	}

	void Parser::err_param_nnum(const std::string nm, const size_t ln) const {
		std::cerr << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerter is not an integer or a real." << std::endl;
		throw ParseErrorException();
	}

	// paramerters are not in same type
	void Parser::err_param_nsame(const std::string nm, const size_t ln) const {
		std::cerr << "error: Invalid command \"" << nm << "\" in line "
			<< ln << ", paramerters are not in same type." << std::endl;
		throw ParseErrorException();
	}

	// logic doesnt support
	void Parser::err_logic(const std::string nm, const size_t ln) const {
		std::cerr << "error: Logic does not support \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// multiple declaration
	void Parser::err_mul_decl(const std::string nm, const size_t ln) const {
		std::cerr << "error: Multiple declarations of \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// multiple definition
	void Parser::err_mul_def(const std::string nm, const size_t ln) const {
		std::cerr << "error: Multiple definitions or keybindings of \""
			<< nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// divisor is zero
	void Parser::err_zero_divisor(const size_t ln) const {
		std::cerr << "error: Divisor is zero in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// arity mismatch
	void Parser::err_arity_mis(const std::string nm, const size_t ln) const{
		std::cerr << "error: Arity mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// kind mismatch
	void Parser::err_type_mis(const std::string nm, const size_t ln) const{
		std::cerr << "error: Kind mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}


	void Parser::err_neg_param(const size_t ln) const{
		std::cerr << "error: Negative parameter in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	// keyword error
	void Parser::err_keyword(const std::string nm, const size_t ln) const{
		std::cerr << "error: keyword mismatch of command \"" << nm << "\" in line " << ln << '.' << std::endl;
		throw ParseErrorException();
	}

	/*
	global errors
	*/
	// cannot open file
	void Parser::err_open_file(const std::string filename) const {
		std::cerr << "error: Cannot open file \"" << filename << "\"." << std::endl;
		throw ParseErrorException();
	}

	std::shared_ptr<DAGNode> Parser::rename(std::shared_ptr<DAGNode> expr, const std::string& new_name){
		condAssert(expr->isVar(), "Only variable can be renamed");
		std::string old_name = expr->getName();
		if(expr->isTempVar()){
			getSymbolManager()->renameTempVar(old_name, new_name);
		}
		else{
			getSymbolManager()->renameVar(old_name, new_name);
		}
		expr->rename(new_name);

		return expr;
	}	

	std::string Parser::toString(std::shared_ptr<DAGNode> expr){
		return dumpSMTLIB2(expr);
	}

	std::string Parser::toString(std::shared_ptr<Sort> sort){
		return sort->toString();
	}

	std::string Parser::toString(const NODE_KIND& kind){
		return kindToString(kind);
	}

	std::string Parser::optionToString(){
		return getOptions()->toString();
	}

	std::string Parser::dumpSMT2(){
		return dumpSMT2(Lower::OmtDialect::Z3);
	}

	std::string Parser::dumpSMT2(Lower::OmtDialect dialect){
		std::ostringstream out;
		writeSMT2(out, dialect);
		return out.str();
	}

	void Parser::writeSMT2(std::ostream& out){
		writeSMT2(out, Lower::OmtDialect::Z3);
	}

	void Parser::writeSMT2(std::ostream& destination, Lower::OmtDialect dialect){
		const bool lower_sets = dialect == Lower::OmtDialect::OptiMathSAT
		    && Lower::needsOptiMathSatSetLowering(*this);
		const bool lower_arrays = dialect == Lower::OmtDialect::OptiMathSAT
		    && (lower_sets || (Lower::needsOptiMathSatArrayLowering(*this) || Lower::needsOptiMathSatDefinitionLowering(*this)));
		std::ostringstream array_output;
		std::ostream& out = lower_arrays ? static_cast<std::ostream&>(array_output) : destination;
		// Dump the current state, followed by the last query and its response
		// requests. Replaying earlier checks against this state would be wrong.
		const auto& commands = script_.commands();
		size_t tail = 0;
		const Command* query = nullptr;
		for (size_t i = 0; i < commands.size(); ++i) {
			if (commands[i].isCheckSat() || commands[i].isCheckSatAssuming()) {
				query = &commands[i];
				tail = i + 1;
			}
		}
		// A snapshot cannot replay a query about a declaration removed by pop or
		// reset. In particular, do not replace it with an unrelated earlier query.
		auto validateQueryTerms = [&](const std::vector<std::shared_ptr<DAGNode>>& terms) {
			std::vector<std::shared_ptr<DAGNode>> pending(terms);
			std::unordered_set<const DAGNode*> seen;
			while (!pending.empty()) {
				auto node = std::move(pending.back());
				pending.pop_back();
				if (!node || !seen.insert(node.get()).second) continue;
				if (node->isVar() && !node->isQuantVar() && !node->isLetBindVar()) {
					auto current = node->isTempVar()
					    ? getSymbolManager()->getTempVar(node->getName())
					    : getSymbolManager()->getVar(node->getName());
					if (current != node) {
						throw std::runtime_error("writeSMT2: last query refers to a removed declaration: "
						                         + node->getName() + "; issue a new query or export a module");
					}
				}
				if ((node->isFuncDec() || node->isFuncDef() || node->isFuncRec())
				    && getSymbolManager()->getFunctionByRecordedName(node->getName()) != node) {
					throw std::runtime_error("writeSMT2: last query refers to a removed function: "
					                         + node->getName());
				}
				for (size_t i = 0; i < node->getChildrenSize(); ++i) pending.push_back(node->getChild(i));
			}
		};
		if (query) validateQueryTerms(query->assumptions);
		for (size_t i = tail; i < commands.size(); ++i) validateQueryTerms(commands[i].value_terms);
		const auto omt = renderSMT2Objectives(dialect);
		out << omt.preamble;
		writeSMT2State(out, {}, true, dialect);
		out << omt.commands;
		if (query && query->isCheckSatAssuming()) {
			if (dialect == Lower::OmtDialect::SmtLib2025 && !omt.objective_names.empty()) {
				const auto close = omt.query.rfind(')');
				condAssert(close != std::string::npos, "writeSMT2: invalid optimization query");
				out << omt.query.substr(0, close);
				for (const auto& term : query->assumptions) {
					out << " :assumption ";
					dumpSMTLIB2Shared(term, out);
				}
				out << ")\n";
			} else {
				out << "(check-sat-assuming (";
				bool first = true;
				for (const auto& term : query->assumptions) {
					if (!first) out << ' ';
					first = false;
					dumpSMTLIB2Shared(term, out);
				}
				out << "))\n";
			}
		} else {
			out << omt.query;
		}
		for (size_t i = tail; i < commands.size(); ++i) {
			const auto& command = commands[i];
			if (isResponseCommand(command.type) && !command.isCheckSat()
			    && !command.isCheckSatAssuming() && !command.original.empty()) {
				if (command.type == CMD_TYPE::CT_GET_VALUE && !command.value_terms.empty()) {
					out << "(get-value (";
					for (size_t j = 0; j < command.value_terms.size(); ++j) {
						if (j) out << ' ';
						dumpSMTLIB2Shared(command.value_terms[j], out);
					}
					out << "))\n";
				} else if (dialect == Lower::OmtDialect::SmtLib2025
				    && command.type == CMD_TYPE::CT_GET_OBJECTIVES) {
					if (!omt.objective_names.empty()) {
						out << "(get-value (";
						for (size_t j = 0; j < omt.objective_names.size(); ++j) {
							if (j) out << ' ';
							out << omt.objective_names[j];
						}
						out << "))\n";
					}
				} else out << command.original << '\n';
			}
		}
		out << "(exit)\n";
		if (lower_arrays) destination << Lower::lowerBooleanArraysForOptiMathSat(lower_sets
		    ? Lower::lowerFiniteSetsForOptiMathSat(array_output.str()) : array_output.str());
		if(!out || !destination){
			throw std::runtime_error("writeSMT2: failed while writing SMT-LIB output");
		}
	}

	std::string Parser::dumpSMT2Module(const std::unordered_set<std::string>& bound_parameters){
		std::ostringstream out;
		writeSMT2Module(out, bound_parameters);
		return out.str();
	}

	void Parser::writeSMT2Module(std::ostream& out,
	                             const std::unordered_set<std::string>& bound_parameters){
		writeSMT2State(out, bound_parameters, false, Lower::OmtDialect::Z3);
	}

	void Parser::writeSMT2HardModule(std::ostream& out){
		writeSMT2State(out, {}, true, Lower::OmtDialect::None);
	}

	void Parser::writeSMT2State(std::ostream& out,
	                           const std::unordered_set<std::string>& bound_parameters,
	                           bool include_objectives, Lower::OmtDialect dialect){
		// An input without (set-logic ...) leaves the logic at the placeholder
		// UNKNOWN_LOGIC, which is not a logic name any parser accepts -- ours
		// included -- so emitting it made every such dump unreadable. That is the
		// exact round trip Parser::parseAny relies on to move a translated model
		// into an existing parser. Fall back to ALL, which is what "no logic was
		// stated" means for a dump; an explicitly stated logic passes through.
		const std::string logic = getOptions()->getLogic();
		out << "(set-logic " << (logic == "UNKNOWN_LOGIC" ? "ALL" : logic) << ")" << '\n';
		if (include_objectives && dialect != Lower::OmtDialect::None) {
			// Internal parser settings are not SMT-LIB solver options.
			static const std::unordered_set<std::string> internal = {
				"keep_let", "precision", "float_evaluate", "expand_functions",
				"expand_recursive_functions", "strict_smtlib_fp", "preserve_annotations"};
			std::vector<std::pair<std::string, std::string>> options;
			for (const auto& option : getOptions()->options) {
				if (internal.count(option.first) || option.first == "opt.priority"
                    || option.first == "enable-omt") continue;
                if (dialect == Lower::OmtDialect::OptiMathSAT && option.first == "produce-models"
                    && option.second == "true"
                    && (!getObjectives().empty() || !context_.soft_assertions.empty())) continue;
                options.push_back(option);
			}
			std::sort(options.begin(), options.end());
			for (const auto& option : options) {
				out << "(set-option :" << option.first << ' ' << option.second << ")\n";
			}
		}
		// custom sorts, in declaration order (getSortKeyMap is unordered)
		const auto& sort_map = getSymbolManager()->getSortKeyMap();
		// Names introduced by a datatype declaration: its constructors, their
		// selectors and the derived testers. (declare-datatypes ...) already
		// declares all of them, so emitting a declare-fun for each as well
		// would make the dump reject itself as a redeclaration.
		std::unordered_set<std::string> datatype_member_names;
		// Datatype sorts in declaration order; emitted in dependency groups
		// after this loop, because a group cannot be split.
		std::vector<std::string> datatype_order;
		for(const auto& sort_name : getSymbolManager()->getSortOrder()){
			auto it = sort_map.find(sort_name);
			if(it == sort_map.end() || !it->second) continue;
			const auto& sort = it->second;
			if(sort->isDec()){
				out << "(declare-sort " << sort_name << " " << sort->arity << ")" << '\n';
			}
			else if(sort->isDatatype() && sort->hasDtConstructors()){
				// Emitted below, in dependency groups. A datatype whose
				// selector names another datatype cannot be declared before
				// it, and MUTUALLY recursive ones cannot be declared apart at
				// all -- SMT-LIB puts a whole group in one command for exactly
				// that reason.
				datatype_order.push_back(sort_name);
			}
		}
		// (declare-datatypes ((T 0) (TL 0)) ((<T ctors>) (<TL ctors>)))
		//
		// One command per group of mutually recursive datatypes, groups in
		// dependency order. Emitting one command per SORT is what this did, and
		// it produced a script THIS PARSER COULD NOT READ for any mutually
		// recursive pair: `T` mentions `TL` in a selector, `TL` is declared in
		// the next command, and re-parsing failed with `Unknown or unexpected
		// symbol "TL"`. dumpSMT2 returned that text and reported nothing.
		//
		// A datatype that depends on nothing still gets its own command, so the
		// output for every non-mutual script is unchanged.
		if(!datatype_order.empty()){
			const auto ctors_of = [&](const std::string& n)
				-> const std::vector<Sort::DtConstructor>* {
				auto i = sort_map.find(n);
				if(i == sort_map.end() || !i->second) return nullptr;
				return &i->second->getDtConstructors();
			};
			// A -> B when a selector of A MENTIONS B anywhere in its sort.
			// Collected by NAME, since a placeholder sort and the finished one
			// are different objects.
			//
			// Anywhere, not just at the top: a selector of sort
			// `(Array Int TL)` depends on TL exactly as one of sort `TL` does,
			// and reading only the outermost name missed the edge. The two
			// datatypes then landed in different groups, were emitted as
			// separate commands, and the second was named before it was
			// declared -- which is the very defect this grouping exists to fix,
			// reached through a sort constructor instead of directly. It is
			// also the reason the fix looked complete: `(Array Int TL)` and
			// `(Set Q)` are the ordinary ways a datatype refers to a collection
			// of another, and neither is the shape the first round tested.
			std::unordered_map<std::string, std::unordered_set<std::string>> deps;
			std::unordered_set<std::string> is_dt(datatype_order.begin(),
			                                      datatype_order.end());
            const auto mentions = [&](const std::shared_ptr<Sort>& sort,
                                      const std::string& owner) {
                std::vector<std::shared_ptr<Sort>> pending{sort};
                std::unordered_set<const Sort*> visited;
                while (!pending.empty()) {
                    auto current = std::move(pending.back());
                    pending.pop_back();
                    if (!current || !visited.insert(current.get()).second) continue;
                    if (current->name != owner && is_dt.count(current->name))
                        deps[owner].insert(current->name);
                    pending.insert(pending.end(), current->children.begin(), current->children.end());
                }
            };
            for (const auto& name : datatype_order) {
                const auto* constructors = ctors_of(name);
                if (!constructors) continue;
                for (const auto& constructor : *constructors)
                    for (const auto& selector : constructor.selectors) mentions(selector.sort, name);
            }
            // Explicit Tarjan frames preserve dependency-first declaration order
            // even when the input contains a long chain of datatype definitions.
            std::unordered_map<std::string, int> index, low;
            std::unordered_set<std::string> on_stack;
            std::vector<std::string> stack;
            std::vector<std::vector<std::string>> groups;
            int next_index = 0;
            struct ComponentFrame {
                std::string name;
                std::vector<std::string> edges;
                std::size_t next = 0;
            };
            std::vector<ComponentFrame> pending;
            const auto enter = [&](const std::string& name) {
                index[name] = low[name] = next_index++;
                stack.push_back(name);
                on_stack.insert(name);
                ComponentFrame frame{name, {}};
                const auto dependencies = deps.find(name);
                if (dependencies != deps.end())
                    frame.edges.assign(dependencies->second.begin(), dependencies->second.end());
                pending.push_back(std::move(frame));
            };
            for (const auto& name : datatype_order) {
                if (index.count(name)) continue;
                enter(name);
                while (!pending.empty()) {
                    auto& frame = pending.back();
                    if (frame.next < frame.edges.size()) {
                        const std::string child = frame.edges[frame.next++];
                        if (!index.count(child)) enter(child);
                        else if (on_stack.count(child))
                            low[frame.name] = std::min(low[frame.name], index[child]);
                        continue;
                    }
                    const std::string current = frame.name;
                    if (low[current] == index[current]) {
                        std::vector<std::string> group;
                        for (;;) {
                            const std::string member = std::move(stack.back());
                            stack.pop_back();
                            on_stack.erase(member);
                            group.push_back(member);
                            if (member == current) break;
                        }
                        groups.push_back(std::move(group));
                    }
                    pending.pop_back();
                    if (!pending.empty()) {
                        const auto& parent = pending.back().name;
                        low[parent] = std::min(low[parent], low[current]);
                    }
                }
            }

			for(auto& group : groups){
				// Declaration order within a group, so a one-element group and
				// a group of three both read the way the script declared them.
				std::sort(group.begin(), group.end(),
				          [&](const std::string& a, const std::string& b){
					          return std::find(datatype_order.begin(),
					                           datatype_order.end(), a)
					               < std::find(datatype_order.begin(),
					                           datatype_order.end(), b);
				          });
				const bool coinductive = sort_map.at(group.front())->coinductive;
				for (const auto& name : group) {
					condAssert(sort_map.at(name)->coinductive == coinductive,
					           "mutually recursive datatype group mixes inductive and coinductive declarations");
				}
				out << (coinductive ? "(declare-codatatypes (" : "(declare-datatypes (");
				for(std::size_t gi = 0; gi < group.size(); ++gi){
					auto i = sort_map.find(group[gi]);
					const size_t ar = (i != sort_map.end() && i->second)
					                      ? i->second->arity : 0;
					if(gi) out << " ";
					out << "(" << group[gi] << " " << ar << ")";
				}
				out << ") (";
				for(std::size_t gi = 0; gi < group.size(); ++gi){
					const auto* cs = ctors_of(group[gi]);
					if(gi) out << " ";
					out << "(";
					// A PARAMETRIC datatype's body is wrapped in `par`, which
					// binds the sort names its selectors mention. The names are
					// not recoverable from the sort -- a Sort records its arity
					// and not what its parameters were called -- so they are
					// carried in datatype_params_ from the declaration.
					const auto pit = datatype_params_.find(group[gi]);
					const bool parametric = pit != datatype_params_.end()
						&& !pit->second.empty();
					if(parametric){
						out << "par (";
						for(std::size_t pi = 0; pi < pit->second.size(); ++pi){
							if(pi) out << " ";
							out << pit->second[pi];
						}
						out << ") (";
					}
					bool first_ctor = true;
					if(cs){
						for(const auto& ctor : *cs){
							if(!first_ctor) out << " ";
							first_ctor = false;
							datatype_member_names.insert(ctor.name);
							datatype_member_names.insert("is-" + ctor.name);
							out << "(" << ctor.name;
							for(const auto& sel : ctor.selectors){
								datatype_member_names.insert(sel.name);
								out << " (" << sel.name << " "
								   << sel.sort->toString() << ")";
							}
							out << ")";
						}
					}
					if(parametric){ out << ")"; }      // close the `par`
					out << ")";
				}
				out << "))" << '\n';
			}
		}
		// Heap sorts may refer to user-defined sorts declared above.
        if (getHeapLocationSort())
            out << "(declare-heap (" << getHeapLocationSort()->toString() << " "
               << getHeapDataSort()->toString() << "))\n";
		// variables
		std::vector<std::shared_ptr<DAGNode>> vars = getVariables();
		for(auto& var : vars){
			if(bound_parameters.count(var->getName())) continue;
			out << "(declare-fun " << smtSymbol(var->getName()) << " () " << var->getSort()->toString() << ")" << '\n';
		}
	std::vector<std::shared_ptr<DAGNode>> functions = getFunctions();
	// Members of a (define-funs-rec ...) group are emitted together, at the
	// position of whichever member comes first, so the rest must be skipped
	// when the loop reaches them.
	std::unordered_set<std::string> emitted_funcs;
	for(auto& func : functions){
		if(!func) continue;
		if(datatype_member_names.count(func->getName())) continue;
		if(!emitted_funcs.insert(func->getName()).second) continue;
		if(const auto* group = getSymbolManager()->getRecFunGroup(func->getName())){
			std::vector<std::shared_ptr<DAGNode>> members;
			for(const auto& member_name : *group){
				auto member = getSymbolManager()->getFun(member_name);
				// A member removed via removeFuns() leaves the rest of the
				// group behind; dropping it silently would emit a group whose
				// bodies call a name nothing defines, so refuse instead.
				condAssert(member != nullptr,
					"dumpSMT2: define-funs-rec group member `" + member_name + "` is gone");
				members.emplace_back(member);
				emitted_funcs.insert(member_name);
			}
			dumpFuncsRec(members, out);
			out << '\n';
			continue;
		}
		if(func->isFuncDec()){
			// NT_FUNC_DEC: Uninterpreted function declaration (declare-fun)
			dumpFuncDec(func, out);
			out << '\n';
		}
		else if(func->isFuncRec()){
			// NT_FUNC_REC: Recursive function definition (define-fun-rec)
			dumpFuncRec(func, out);
			out << '\n';
		}
		else{
			// NT_FUNC_DEF: Regular function definition (define-fun)
			dumpFuncDef(func, out);
			out << '\n';
		}
	}
		// constraints. A `:named` annotation is stripped during parsing and kept
		// aside for unsat cores; dumping it back is what lets a dumped script
		// still answer (get-unsat-core) with the names the input used.
		// Hash-consing can put one named node in `assertions` more than once --
		// (assert (! p :named n)) (assert p) -- and repeating the name would be a
		// duplicate declaration on re-parse, so only the first occurrence carries it.
		//
		// NOT SUPPORTED: a name on a nested subterm, e.g.
		// (assert (and (! p :named n) q)).  SMT-LIB allows :named on any term,
		// and the parser records such a name so getNamedAssertions() can find
		// it, but this loop annotates whole assertions, so the name is dropped
		// from the dump.  Emitting it would mean re-inserting the annotation at
		// the right position while printing the term.
		std::unordered_set<std::string> emitted_names;
		for(auto& constraint : context_.assertions){
			const std::string* name = context_.getAssertionName(constraint);
			if(name && emitted_names.insert(*name).second){
				out << "(assert (! ";
				dumpSMTLIB2Shared(constraint, out);
				out << " :named " << *name << "))" << '\n';
			}
			else{
				out << "(assert ";
				dumpSMTLIB2Shared(constraint, out);
				out << ")" << '\n';
			}
		}
		// Soft assertions. They were parsed into context_ and never emitted, so
		// a MaxSAT problem read through this library and dumped came back as a
		// plain SAT problem -- the optimisation objective silently gone, the
		// script well-formed, and the answer to a different question. The same
		// failure family as the floating-point and string constants that could
		// be built and not read back, and the most consequential of them.
		for(size_t i = 0; !include_objectives && i < context_.soft_assertions.size(); i++){
			out << "(assert-soft ";
			dumpSMTLIB2Shared(context_.soft_assertions[i], out);
			if(i < context_.soft_weights.size() && context_.soft_weights[i]){
				out << " :weight " << softWeightToken(context_.soft_weights[i]);
			}
			// The :id is stored group-first, so the group owning this index is
			// found by lookup rather than carried alongside.
			for(const auto& g : context_.soft_assertion_groups){
				if(g.second.count(i) != 0){
					out << " :id " << g.first;
					break;
				}
			}
			out << ")" << '\n';
		}
		if(!out){
			throw std::runtime_error("writeSMT2Module: failed while writing SMT-LIB module");
		}
	}

	std::string Parser::dumpSMT2(const std::string& filename){
		return dumpSMT2(filename, Lower::OmtDialect::Z3);
	}

	std::string Parser::dumpSMT2(const std::string& filename, Lower::OmtDialect dialect){
		// Validate before truncating an existing destination.
		(void)renderSMT2Objectives(dialect);
		const bool lower_arrays = dialect == Lower::OmtDialect::OptiMathSAT
		    && (Lower::needsOptiMathSatSetLowering(*this) || (Lower::needsOptiMathSatArrayLowering(*this) || Lower::needsOptiMathSatDefinitionLowering(*this)));
		// Dialect lowering can reject an unsupported array construct. Complete
		// that work before opening the user's destination with truncation.
		std::string rendered;
		if (lower_arrays) rendered = dumpSMT2(dialect);
		std::ofstream file(filename, std::ios::binary | std::ios::out | std::ios::trunc);
		if(!file){
			throw std::runtime_error("dumpSMT2: could not open destination: " + filename);
		}
		if (lower_arrays) file << rendered;
		else writeSMT2(file, dialect);
		file.flush();
		if(!file){
			throw std::runtime_error("dumpSMT2: failed while writing destination: " + filename);
		}
		return filename;
	}

	size_t Parser::removeFuns(const std::vector<std::string>& funcNames){
		size_t removedCount = 0;
		
		for(const auto& funcName : funcNames){
			if(getSymbolManager()->getFun(funcName)){
				getSymbolManager()->removeFun(funcName);
				removedCount++;
			}
		}
		
		return removedCount;
	}

	/*
	warnings
	*/
	// command not support
	void Parser::warn_cmd_nsup(const std::string nm, const size_t ln) const {
		std::cout << "warning: \"" << nm << "\" command is safely ignored in line " << ln << "." << std::endl;
	}

	// An assertion carries at most one name, so a second ":named" on the same
	// assertion -- or a name taken from another one -- drops a binding. Say so:
	// the loss is silent otherwise and only shows up in an unsat core.
	void Parser::warn_named_displaced(const NameAssertionOutcome& outcome, const std::string& name, const size_t ln) const {
		if (outcome.assertion_was_named) {
			std::cout << "warning: assertion was already named \"" << outcome.previous_name
			          << "\" in line " << ln << "; keeping only the last name \"" << name << "\"." << std::endl;
		}
		if (outcome.name_was_reused) {
			std::cout << "warning: name \"" << name << "\" was already used for another assertion in line "
			          << ln << "; keeping only the last assertion so named." << std::endl;
		}
	}

	ParserPtr newParser(){
		return std::make_shared<Parser>();
	}

	ParserPtr newParser(const std::string& filename){
		return std::make_shared<Parser>(filename);
	}

	bool Parser::isUnit(std::shared_ptr<DAGNode> node) const {
		if (!node) {
			return true;
		}
		
		std::stack<std::shared_ptr<DAGNode>> nodeStack;
		std::unordered_set<std::shared_ptr<DAGNode>> visited;
		std::unordered_set<std::shared_ptr<DAGNode>> vars;
		
		nodeStack.push(node);
		
		while (!nodeStack.empty()) {
			std::shared_ptr<DAGNode> currentNode = nodeStack.top();
			nodeStack.pop();
			
			// if visited, skip
			if (visited.find(currentNode) != visited.end()) {
				continue;
			}
			visited.insert(currentNode);
			
			// if current node is a variable, add to the variable set
			if (currentNode->isVar()) {
				vars.insert(currentNode);
				if(vars.size() > 1){
					return false;
				}
			}
			
			// push the children to the stack
			for (size_t i = 0; i < currentNode->getChildrenSize(); i++) {
				std::shared_ptr<DAGNode> child = currentNode->getChild(i);
				if (visited.find(child) == visited.end()) {
					nodeStack.push(child);
				}
			}
		}
		
		// if there is no variable or only one variable, return true
		if (vars.size() <= 1) {
			return true;
		}

		return false;
	}

	bool Parser::isUnitAtom(std::shared_ptr<DAGNode> node) const {
		return node && isUnit(node) && node->isAtom();
	}

	std::shared_ptr<DAGNode> Parser::getUnitVar(std::shared_ptr<DAGNode> node) const {
		if (!node) {
			return NodeManager::NULL_NODE;
		}
		
		// use iterative method to traverse all nodes, collect variables
		std::stack<std::shared_ptr<DAGNode>> nodeStack;
		std::unordered_set<std::shared_ptr<DAGNode>> visited;
		std::unordered_set<std::shared_ptr<DAGNode>> vars;
		
		nodeStack.push(node);
		
		while (!nodeStack.empty()) {
			std::shared_ptr<DAGNode> currentNode = nodeStack.top();
			nodeStack.pop();
			
			// if visited, skip
			if (visited.find(currentNode) != visited.end()) {
				continue;
			}
			visited.insert(currentNode);
			
			// if current node is a variable, add to the variable set
			if (currentNode->isVar()) {
				vars.insert(currentNode);
				if(vars.size() > 1){
					return NodeManager::NULL_NODE;
				}
			}
			
			// push the children to the stack
			for (size_t i = 0; i < currentNode->getChildrenSize(); i++) {
				std::shared_ptr<DAGNode> child = currentNode->getChild(i);
				if (visited.find(child) == visited.end()) {
					nodeStack.push(child);
				}
			}
		}
		
		// if there is only one variable, return it
		if (vars.size() == 1) {
			return *vars.begin();
		}

		return NodeManager::NULL_NODE;
	}

	bool Parser::parseAny(const std::string& path) {
		Lang::SourceUnit unit;
		unit.main_path = path;
		unit.display_name = path;
		return parseAny(unit);
	}

	bool Parser::parseAny(const Lang::SourceUnit& unit) {
		TranslateOptions opts;
		Translation t = translate(unit, opts);
		auto report = std::make_shared<Uir::TranslationReport>(t.report());
		last_report_ = report;
		if (!t.ok()) {
			// This is the reachable failure path: every source-language lex,
			// parse or type error, every unsupported construct and every
			// rejected profile arrives here. translate() recorded why in its
			// own Diagnostics, which dies with the Translation -- report()
			// carries none of it. Copying it across is the only thing that
			// keeps the failure visible to a caller that inspects
			// lastTranslationReport() rather than the return value; without it
			// that caller reads an exact-fidelity report with no entries at
			// all, which is indistinguishable from a translation that
			// succeeded.
			for (const auto& d : t.diagnostics().all()) {
				report->addWarning(d);
			}
			if (!t.diagnostics().hasErrors()) {
				// Every !ok() return inside translate() records an error first,
				// so this is a guard against a future path that forgets to.
				// Copying zero ERROR entries would put the report straight back
				// to reading as a success.
				Uir::Diagnostic d;
				d.severity = Uir::Severity::ERROR;
				d.code = Uir::ErrorCode::E_INTERNAL;
				d.message = "parseAny: translating '" + unit.main_path
					+ "' failed without recording a cause";
				report->addWarning(d);
			}
			return false;
		}
		// Move the translated content into this Parser by replaying it as
		// SMT-LIB text. HirToParser never lowers objectives onto a Parser
		// object directly -- they exist only as the text toSmt2() renders --
		// so plain dumpSMT2() (declarations + assertions only) would silently
		// drop any minimize/maximize goal. toSmt2() carries them, but the
		// dialect must be one *this* parser can read back: it is an internal
		// detail of moving content between two in-process Parsers, not the
		// caller's TranslateOptions::omt_dialect, which governs what toSmt2()
		// hands to an *external* solver. toSmt2()'s default (the SMT 2025
		// proposal syntax, define-objective/optimize-sat) is not implemented
		// by this parser's command dispatch (base_parser.cpp recognises
		// "define-objective" but with this project's own, different grammar,
		// and does not recognise "optimize-sat" at all). Lower::OmtDialect::Z3
		// emits (minimize t)/(maximize t), which is exactly the grammar this
		// parser's own "minimize"/"maximize" commands accept
		// (src/frontend/opt_parser.cpp, parseSingleObj), so it is the one
		// objective grammar that actually round-trips here. Keep the native
		// theory terms: external Z3 export may lower Set to arrays or refuse
		// an unsupported carrier, neither of which belongs in this transfer.
		//
		// Count what is already here first. A Parser is not required to be
		// empty when parseAny() is called -- the header documents parsing an
		// objective by hand and then calling parseAny(), and a batch driver may
		// reuse one Parser across inputs -- so the check below has to be about
		// what *this* call added, not about the total.
		const size_t objectives_before = getObjectives().size();
		if (!parseStr(t.toParserSmt2())) {
			// Returning false with nothing recorded would leave
			// lastTranslationReport() reading as a successful, exact-fidelity
			// translation -- translate() genuinely succeeded, the round trip
			// into *this* parser is what failed -- so a caller that inspects
			// the report instead of the return value would see no failure at
			// all. Record it where that caller looks.
			Uir::Diagnostic d;
			d.severity = Uir::Severity::ERROR;
			d.code = Uir::ErrorCode::E_INTERNAL;
			d.message = "parseAny: the translated model did not parse back into "
				"the destination parser (details on stderr)";
			report->addWarning(d);
			return false;
		}
		// A round trip that silently drops objectives is worse than a failure:
		// the caller would get back a Parser that looks fine and solves the
		// wrong (unconstrained) problem. Verify what this call added against
		// the HIR model's count -- not parser()->getObjectives(), which is
		// unconditionally empty per the note above -- and fail loudly on a
		// mismatch instead of returning true.
		//
		// Compared as totals rather than as a subtraction: size() is unsigned,
		// and a hypothetical decrease would underflow into a huge "added" count
		// that reads as a wildly different defect than the one that occurred.
		const size_t objectives_now = getObjectives().size();
		if (objectives_now != objectives_before + t.objectiveCount()) {
			Uir::Diagnostic d;
			d.severity = Uir::Severity::ERROR;
			d.code = Uir::ErrorCode::E_INTERNAL;
			d.message = "parseAny: " + std::to_string(t.objectiveCount())
				+ " objective(s) in the translated model, so this parser should"
				  " hold " + std::to_string(objectives_before + t.objectiveCount())
				+ " after adding them to the " + std::to_string(objectives_before)
				+ " it already had, but it holds " + std::to_string(objectives_now);
			report->addWarning(d);
			return false;
		}
		return true;
	}

	const Uir::TranslationReport& Parser::lastTranslationReport() const {
		static const Uir::TranslationReport kEmpty;
		return last_report_ ? *last_report_ : kEmpty;
	}

}
