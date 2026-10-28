/* -*- Header -*-
 *
 * An SMT/OMT Parser
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

#ifndef PARSER_HEADER
#define PARSER_HEADER

#include "somtparser/ir/dag.h"
#include "somtparser/core/util.h"
#include "somtparser/core/options.h"
#include "somtparser/frontend/objective.h"
#include "somtparser/model/model.h"
#include "somtparser/ir/node.h"
#include "somtparser/passes/visitor.h"
#include "somtparser/frontend/op_utils.h"
#include "somtparser/frontend/parser_context.h"
#include "somtparser/passes/op_dispatcher.h"
#include "somtparser/frontend/symbol_manager.h"
#include "somtparser/frontend/command.h"
#include <exception>

namespace SOMTParser{
    #undef assert
    enum class SCAN_MODE {
        SM_COMMON,
        SM_SYMBOL,
        SM_COMP_SYM,
        SM_COMMENT,
        SM_STRING
    };

    // LET mode, only used in preserving let mode
    enum class LET_MODE {
        LM_NON_LET, // not in let
        LM_START_LET, // start of let
        LM_IN_LET, // in let
    };

    enum class KEYWORD{
        KW_ID, KW_WEIGHT, KW_COMP, KW_EPSILON, KW_M, KW_OPT_KIND, KW_NAMED,
        // Quantifier annotations — ported from the SMTStabilizer fork.
        KW_PATTERN, KW_NO_PATTERN, KW_QID, KW_SKOLEMID, KW_LBLPOS, KW_LBLNEG,
        KW_NULL
    };

    enum class CMD_TYPE {
        CT_UNKNOWN, CT_EOF,
        // COMMANDS
        CT_ASSERT, CT_CHECK_SAT, CT_CHECK_SAT_ASSUMING,
        CT_DECLARE_CONST, CT_DECLARE_FUN, CT_DECLARE_SORT, CT_DECLARE_DATATYPES,
        CT_DEFINE_FUN, CT_DEFINE_FUN_REC, CT_DEFINE_FUNS_REC, CT_DEFINE_SORT,
        CT_ECHO, CT_EXIT,
        CT_GET_ASSERTIONS, CT_GET_ASSIGNMENT, CT_GET_INFO,
        CT_GET_MODEL, CT_GET_OPTION, CT_GET_PROOF,
        CT_GET_UNSAT_ASSUMPTIONS, CT_GET_UNSAT_CORE, CT_GET_VALUE,
        CT_POP, CT_PUSH, CT_RESET, CT_RESET_ASSERTIONS,
        CT_SET_INFO, CT_SET_LOGIC, CT_SET_OPTION,
        // QUANTIFIER
        CT_EXISTS, CT_FORALL,
        // OPTIMIZATION COMMANDS
        CT_GET_OBJECTIVES, CT_ASSERT_SOFT, 
        CT_DEFINE_OBJ, CT_DEFINE_MIN_OBJ, CT_DEFINE_MAX_OBJ,
        CT_MINIMIZE, CT_MAXIMIZE, CT_LEX_OPTIMIZE, CT_PARETO_OPTIMIZE, CT_BOX_OPTIMIZE, CT_MINMAX, CT_MAXMIN, CT_MAXSAT, CT_MINSAT, CT_OPTIMIZE,
        CT_DECLARE_HEAP
        // CT_LEX_MAXIMIZE, CT_PARETO_MINIMIZE, CT_PARETO_MAXIMIZE, 
        // CT_BOX_MINIMIZE, CT_BOX_MAXIMIZE, CT_MINMAX, CT_MAXMIN
    };

    enum class ERROR_TYPE {
        ERR_UNEXP_EOF,
        ERR_SYM_MIS,
        ERR_UNKWN_SYM,
        ERR_PARAM_MIS,
        ERR_PARAM_NBOOL,
        ERR_PARAM_NNUM,
        ERR_PARAM_NSAME,
        ERR_LOGIC,
        ERR_MUL_DECL,
        ERR_MUL_DEF,
        ERR_ZERO_DIVISOR,
        ERR_FUN_LOCAL_VAR,
        ERR_ARI_MIS,
        ERR_TYPE_MIS,
        ERR_NEG_PARAM
    };

    enum class RESULT_TYPE {
        RT_SAT,
        RT_UNSAT,
        RT_DELTA_SAT,
        RT_UNKNOWN,
        RT_ERROR
    };

    /** Thrown when parsing fails so that parse() can return false instead of exit(0). */
    class ParseErrorException : public std::exception {
    public:
        const char* what() const noexcept override { return "parse error"; }
    };

    /*
    Parser
    */

    // Incremental mode supported via push/pop/reset and nextCommand()
    class Parser {
    private:

        // attributes

        // vars for parser
        char 			                        *buffer;
        unsigned long	                        buflen;
        char			                        *bufptr;
        size_t 	                                line_number;
        SCAN_MODE 		                        scan_mode;
        LET_MODE 		                        current_let_mode; // tracks whether parser is inside a let expression
        size_t                                  let_nesting_depth; // track let nesting depth
        size_t                                  quant_nesting_depth; // track quantifier nesting depth
        bool                                    in_quantifier_scope;
        bool                                    allow_placeholder_vars; // allow creating placeholder variables
        std::shared_ptr<Sort>                   placeholder_var_sort; // sort for placeholder variables

        bool                                    parsing_file;

        // conversion map
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        cnf_map;
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        cnf_atom_map; // bool_var -> atom
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        cnf_bool_var_map; // atom -> bool_var
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        dnf_map;
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>
                                                        nnf_map;

        // array simplification cache
        // Cache for select rewrite: (array, index) -> result
        struct PairNodeHash {
            size_t operator()(const std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& p) const {
                size_t h1 = p.first ? p.first->hashCode() : 0;
                size_t h2 = p.second ? p.second->hashCode() : 0;
                return h1 ^ (h2 << 1);
            }
        };
        struct PairNodeEqual {
            bool operator()(const std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& p1,
                          const std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& p2) const {
                return p1.first == p2.first && p1.second == p2.second;
            }
        };
        std::unordered_map<std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>, 
                          std::shared_ptr<DAGNode>, PairNodeHash, PairNodeEqual>
                                                        array_select_cache;
        // Cache for normalized store chains: array -> normalized_array
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>, NodeHash, NodeEqual>
                                                        array_normalize_cache;
        
        // Structure to represent canonical form of an array (needed for cache)
        struct ArrayCanonicalForm {
            std::shared_ptr<DAGNode> base;  // Base value (for const array) or base array
            std::vector<std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>> writes; // Final writes: (index, value) pairs, sorted by pointer
            bool is_const_array;  // true if base is a const array value, false if base is an array node
            
            // Compute hash for canonical form
            // Note: writes are sorted by hash code, so same content -> same order -> same hash
            size_t computeHash() const {
                size_t h = base ? base->hashCode() : 0;
                // Combine writes in order (since they're sorted, same content -> same order)
                for (const auto& w : writes) {
                    size_t idx_hash = w.first ? w.first->hashCode() : 0;
                    size_t val_hash = w.second ? w.second->hashCode() : 0;
                    // Combine index and value hash
                    size_t write_hash = idx_hash ^ (val_hash << 1);
                    // Combine with base hash using boost::hash_combine style
                    h ^= write_hash + 0x9e3779b9 + (h << 6) + (h >> 2);
                }
                return h;
            }
        };
        
        // Cache for canonical form: array -> canonical_form
        std::unordered_map<std::shared_ptr<DAGNode>, ArrayCanonicalForm, NodeHash, NodeEqual>
                                                        array_canonical_cache;

        // result
        RESULT_TYPE                                   result_type = RESULT_TYPE::RT_UNKNOWN;
        std::shared_ptr<DAGNode>                      result_node;
        std::shared_ptr<Model>                        result_model;

        /** Context holding assertions, assumptions, objectives, etc. */
        ParserContext                                 context_;

        /** Accumulated command script (when command_logging_ is true). */
        Script                                        script_;

        /** Whether to log each parsed command into script_. */
        bool                                          command_logging_ = false;

        /** Payload of the command currently being parsed, threaded from
         *  parseCommand() into the Command built by nextCommand(). Cleared at
         *  the start of each nextCommand(). */
        std::vector<std::shared_ptr<DAGNode>>         pending_value_terms_;
        std::string                                   pending_keyword_;
        std::shared_ptr<DAGNode>                      pending_command_expr_;
        std::string                                   pending_command_name_;
        std::shared_ptr<Sort>                         pending_command_sort_;
        std::vector<std::shared_ptr<DAGNode>>         pending_command_params_;
        std::string                                   pending_command_logic_;
        std::string                                   source_text_;
        // Byte offsets of line starts in source_text_, rebuilt on each input.
        // Command ranges may be queried in any order without rescanning prefixes.
        std::vector<size_t>                            source_line_starts_{0};
        std::string                                   source_name_ = "<memory>";
        size_t                                        next_command_index_ = 0;

        void indexSourceLines();
        SourcePosition sourcePosition(size_t offset) const;
        Command makeCommand(CMD_TYPE type, size_t begin_offset,
                            size_t end_offset, size_t begin_line);

    public:
        
        /**
         * @brief Constructor with filename
         * 
         * Creates a Parser object and immediately tries to parse the specified SMT-LIB2 file.
         * 
         * @param filename Path to the SMT-LIB2 file to parse
         */
        Parser(const std::string& filename);
        
        /**
         * @brief Default constructor
         * 
         * Creates an empty Parser object, parse method must be called later to parse a file.
         */
        Parser();
        
        /**
         * @brief Destructor
         * 
         * Releases all resources used by the Parser
         */
        ~Parser();
        
        /**
         * @brief Parse SMT-LIB2 file
         * 
         * Parses the specified SMT-LIB2 file and builds internal data structures.
         * 
         * @param filename Path to the SMT-LIB2 file to parse
         * @return True if parsing was successful, false otherwise
         */
        bool parse(const std::string& filename);

        /**
         * @brief Parse a constraint
         * 
         * Parses the specified constraint and builds internal data structures.
         * 
         * @param constraint Constraint to parse
         * @return True if parsing was successful, false otherwise
         */
        bool parseStr(const std::string& constraint,
                      const std::string& source_name = "<memory>");

        /** Load SMT-LIB text for command-at-a-time parsing with nextCommand(). */
        bool loadStr(const std::string& constraint,
                     const std::string& source_name = "<memory>");

        const std::string& getSourceText() const { return source_text_; }
        const std::string& getSourceName() const { return source_name_; }
        
        /**
         * @brief Assert a constraint
         * 
         * Asserts the specified constraint and builds internal data structures.
         * 
         * @note Any variables in the constraint must be declared before assertion.
         * 
         * @param constraint Constraint to assert
         * @return True if assertion was successful, false otherwise
         */
        bool assert(const std::string& constraint);

        /**
         * @brief Assert a constraint
         * 
         * Asserts the specified constraint and builds internal data structures.
         * 
         * @param node Constraint to assert
         * @return True if assertion was successful, false otherwise
         */
        bool assert(std::shared_ptr<DAGNode> node);

        /**
         * @brief Create a DAG node from a string expression
         * 
         * Parses the specified string expression and returns the corresponding DAG node.
         * 
         * @param expression String expression to parse
         * @return Parsed DAG node
         */
        std::shared_ptr<DAGNode> mkExpr(const std::string& expression);

        // to solver
        /**
         * @brief Get the context (assertions, assumptions, objectives, etc.)
         * @return Reference to the parser context (base class); pass to Dispatcher or use get* below.
         */
        Context& context();
        const Context& context() const;

        /**
         * @brief Get all assertions
         * 
         * @return Vector of all assertions
         */
        std::vector<std::shared_ptr<DAGNode>> getAssertions() const;

        /**
         * @brief Get the node manager (for Rewriter, etc.)
         * @return shared_ptr to the parser's NodeManager
         */
        std::shared_ptr<NodeManager> getNodeManager() { return context_.getNodeManager(); }
        std::shared_ptr<NodeManager> getNodeManager() const { return context_.getNodeManager(); }
        std::shared_ptr<Sort> getHeapLocationSort() const { return context_.heap_location_sort; }
        std::shared_ptr<Sort> getHeapDataSort() const { return context_.heap_data_sort; }
        std::shared_ptr<DAGNode> mkSpatial(NODE_KIND, const std::vector<std::shared_ptr<DAGNode>>&);

        std::shared_ptr<SortManager> getSortManager() { return context_.getSortManager(); }
        std::shared_ptr<SortManager> getSortManager() const { return context_.getSortManager(); }
        std::shared_ptr<SymbolManager> getSymbolManager() { return context_.getSymbolManager(); }
        std::shared_ptr<SymbolManager> getSymbolManager() const { return context_.getSymbolManager(); }
        std::shared_ptr<ObjectiveManager> getObjectiveManager() { return context_.getObjectiveManager(); }
        std::shared_ptr<ObjectiveManager> getObjectiveManager() const { return context_.getObjectiveManager(); }

        /**
         * @brief Get grouped assertions
         *
         * Returns assertion groups map. Use (assert expr :id group_name) to assign 
         * assertions to groups. Assertions without an ID go to the default group.
         *
         * @return Map from group names to sets of assertion indices
         */
        std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedAssertions() const;

        /** Get assertions indexed by their SMT-LIB :named attribute. */
        std::unordered_map<std::string, std::shared_ptr<DAGNode>> getNamedAssertions() const;

        /**
         * @brief Get assumptions
         * 
         * Returns a vector of all assumptions. Use (check-sat-assuming (assumptions)) to check satisfiability
         * under the given assumptions.
         * 
         * @return Vector of all assumptions
         */ 
        std::vector<std::vector<std::shared_ptr<DAGNode>>> getAssumptions() const;

        /**
         * @brief Get soft assertions
         * 
         * Returns soft assertions. Use (assert-soft expr :weight weight :id group_name) to group and weight them.
         * 
         * @return Vector of all soft assertions
         */
        std::vector<std::shared_ptr<DAGNode>> getSoftAssertions() const;

        /**
         * @brief Get soft assertion weights
         * 
         * @return Vector of all soft assertion weights
         */
        std::vector<std::shared_ptr<DAGNode>> getSoftWeights() const;

        /**
         * @brief Get grouped soft assertions
         * 
         * Returns a map of soft assertion groups. Use (assert-soft expr :weight weight :id group_name) to group and weight them.
         * 
         * @return Map from group names to sets of soft assertion indices
         */
        std::unordered_map<std::string, std::unordered_set<size_t>> getGroupedSoftAssertions() const;

        /**
         * @brief Get objectives
         * 
         * @return Vector of all objectives
         */
        std::vector<std::shared_ptr<Objective>> getObjectives() const;

        /** 
        * @brief Set global options
        * 
        * @return set option value
        */
        void setOption(const std::string& key, const std::string& value);
        // A string literal must be treated as a string, not as a bool. Without
        // this overload setOption("keep_let", "false") selects the bool
        // overload -- pointer-to-bool is a standard conversion and so beats the
        // user-defined conversion to std::string -- and silently sets true.
        void setOption(const std::string& key, const char* value);
        void setOption(const std::string& key, const int& value);
        void setOption(const std::string& key, const double& value);
        void setOption(const std::string& key, const bool& value);

        /**
         * @brief Get global options
         * 
         * @return Pointer to global options
         */
        std::shared_ptr<GlobalOptions> getOptions() const { return context_.getOptions(); }

        /**
         * @brief Get variables
         * 
         * @return Vector of all variables
         */
        std::vector<std::shared_ptr<DAGNode>> getVariables() const;

        /**
         * @brief Get declared variables
         * 
         * @return Vector of all declared variables
         */
        std::vector<std::shared_ptr<DAGNode>> getDeclaredVariables() const;
        
        /**
         * @brief Get declared variables filtered by sort kind.
         *
         * These convenience accessors filter getDeclaredVariables() by the
         * sort of each variable.  They are useful for downstream solvers that
         * maintain separate variable models for each theory.
         */
        std::vector<std::shared_ptr<DAGNode>> getBoolVars() const;
        std::vector<std::shared_ptr<DAGNode>> getIntVars() const;
        std::vector<std::shared_ptr<DAGNode>> getRealVars() const;
        std::vector<std::shared_ptr<DAGNode>> getBvVars() const;
        std::vector<std::shared_ptr<DAGNode>> getFpVars() const;
        std::vector<std::shared_ptr<DAGNode>> getRoundingModeVars() const;
        std::vector<std::shared_ptr<DAGNode>> getArrayVars() const;
        std::vector<std::shared_ptr<DAGNode>> getDatatypeVars() const;
        std::vector<std::shared_ptr<DAGNode>> getStringVars() const;

        /** Counts corresponding to the sort-classified accessors above. */
        size_t getNumBoolVars() const;
        size_t getNumIntVars() const;
        size_t getNumRealVars() const;
        size_t getNumBvVars() const;
        size_t getNumFpVars() const;
        size_t getNumRoundingModeVars() const;
        size_t getNumArrayVars() const;
        size_t getNumDatatypeVars() const;
        size_t getNumStringVars() const;

        /**
         * @brief Check whether a datatype sort is (directly or mutually) recursive.
         *
         * A datatype is recursive if at least one of its constructors has a selector
         * whose sort transitively refers back to this datatype (direct or mutual).
         *
         * @param dt_sort A Sort with isDatatype() == true.
         * @return true if the datatype is recursive; false otherwise (or if dt_sort
         *         is null / not a datatype / has no constructors).
         */
        bool isRecursiveDatatype(const std::shared_ptr<Sort>& dt_sort) const;

        /**
         * @brief Build a concrete default (ground) term of the given datatype sort.
         *
         * Selects the first nullary constructor if available; otherwise selects the
         * first constructor whose selector sorts can all be recursively defaulted.
         * Handles mutual recursion via a visited-sort guard.
         * Returns nullptr when the sort has no well-founded base case (e.g. a
         * mutually-recursive DT with no nullary constructor on either branch).
         *
         * @param dt_sort A Sort with isDatatype() == true.
         * @return A ground DAGNode of sort dt_sort, or nullptr on failure.
         */
        std::shared_ptr<DAGNode> mkDefaultDTValue(const std::shared_ptr<Sort>& dt_sort);

        /**
         * @brief Check if a variable is declared
         * 
         * @param var_name Variable name
         * @return True if the variable is declared, false otherwise
         */
        bool isDeclaredVariable(const std::string& var_name) const;
        
        /**
         * @brief Get variable
         * 
         * @param var_name Variable name
         * @return Variable node
         */
        std::shared_ptr<DAGNode> getVariable(const std::string& var_name);

        /**
         * @brief Check if a DAG node is unit (contains at most one unique variable)
         * 
         * @param node The DAG node to check
         * @return True if the node contains at most one unique variable, false otherwise
         */
        bool isUnit(std::shared_ptr<DAGNode> node) const;

        /**
         * @brief Check if a DAG node is a unit atom
         * 
         * @param node The DAG node to check
         * @return True if the node is a unit atom, false otherwise
         */
        bool isUnitAtom(std::shared_ptr<DAGNode> node) const;

        /**
         * @brief Get the unique variable from a DAG node
         * 
         * @param node The DAG node
         * @return The unique variable if exists, NULL_NODE otherwise
         */
        std::shared_ptr<DAGNode> getUnitVar(std::shared_ptr<DAGNode> node) const;

        /**
         * @brief Get functions
         * 
         * Returns a vector of all functions. Use (define-fun name (params) body) to define a function.
         * 
         * @return Vector of all functions
         */
        std::vector<std::shared_ptr<DAGNode>> getFunctions() const;
        std::vector<SymbolManager::RecursiveDefinition> getRecursiveDefinitions() const {
            return getSymbolManager()->getRecursiveDefinitions();
        }

        /**
         * @brief Check if a function is declared
         * 
         * @param func_name Function name
         * @return True if the function is declared, false otherwise
         */
        bool isDeclaredFunction(const std::string& func_name) const;

        // get sort
        /**
         * @brief Get sort
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(const std::vector<std::shared_ptr<DAGNode>>& params);

        /**
         * @brief Get sort
         * 
         * @param param Parameter
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> param);

        /**
         * @brief Get sort
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Get sort
         * 
         * @param params Vector of parameters
         * @return Sort
         */
        std::shared_ptr<Sort> getSort(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> m);
        
        /**
         * @brief Get kind
         * 
         * @param s String
         * @return NODE_KIND
         */
        NODE_KIND getKind(const std::string& s);

        /**
         * @brief Get kind
         * 
         * @param node Node
         * @return NODE_KIND
         */
        NODE_KIND getKind(const std::shared_ptr<DAGNode>& node);

        // get result type
        /**
         * @brief Get result type
         * 
         * @return Result type
         */
        RESULT_TYPE getResultType();

        // get result
        /**
         * @brief Get result
         * 
         * @return Result
         */
        std::shared_ptr<DAGNode> getResult();

        // check sat
        /**
         * @brief Check satisfiability
         * 
         * @return True if satisfiable, false otherwise
         */
        RESULT_TYPE checkSat();

        // get model
        /**
         * @brief Get model
         * 
         * @return Model
         */
        std::shared_ptr<Model> getModel();

        // get node count
        /**
         * @brief Get node count
         * 
         * @return Node count
         */
        size_t getNodeCount();

        // mk oper 
        /**
         * @brief Create an operation
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param p Parameters
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> p);

        /**
         * @brief Create an operation
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param l Left parameter
         * @param r Right parameter
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create an operation
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Operation Node
         */     
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create an operation
         * 
         * @param sort Sort
         * @param t Operation kind
         * @param p Parameters
         * @return Operation Node
         */
        std::shared_ptr<DAGNode> mkOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p);

        /**
         * @brief Simplify an operation
         * 
         * @note The parameters are assumed to be constant.
         * 
         * @param t Operation kind
         * @param p Parameters
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> p);

        /**
         * @brief Simplify an operation
         * 
         * @note The parameters are assumed to be constant.
         * 
         * @param t Operation kind
         * @param l Left parameter
         * @param r Right parameter
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Simplify an operation
         * 
         * @note The parameters are assumed to be constant.
         * 
         * @param t Operation kind
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Simplify an operation
         * 
         * @param t Operation kind
         * @param p Parameters
         * @return Simplified operation node
         */
        std::shared_ptr<DAGNode> simp_oper(const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>> &p);

        // mk function
        /**
         * @brief Create a function declaration
         * 
         * @param name Function name
         * @param params Parameters
         * @param out_sort Output sort
         * @return Function declaration node
         */
        std::shared_ptr<DAGNode> mkFuncDec(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);
        std::shared_ptr<DAGNode> mkFuncRecDecl(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);

        /**
         * @brief Create a function definition
         * 
         * @param name Function name
         * @param params Parameters
         * @param out_sort Output sort
         * @param body Body
         * @return Function definition node
         */
        std::shared_ptr<DAGNode> mkFuncDef(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body);

        /**
         * @brief Create a recursive function definition
         * 
         * @param name Function name
         * @param params Parameters
         * @param out_sort Output sort
         * @param body Body
         * @return Recursive function definition node
         */
        std::shared_ptr<DAGNode> mkFuncRec(const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params, std::shared_ptr<Sort> out_sort, std::shared_ptr<DAGNode> body);

        /**
         * @brief Create a recursive function application
         * 
         * @param sort Sort
         * @param name Function name
         * @param params Parameters
         * @return Recursive function application node
         */
        std::shared_ptr<DAGNode> mkApplyRecFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params);


        /**
         * @brief Apply an uninterpreted function
         * 
         * @param sort Sort
         * @param name Function name
         * @param params Parameters
         * @return Uninterpreted function application node
         */
        std::shared_ptr<DAGNode> mkApplyUF(const std::shared_ptr<Sort>& sort, const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params);

        /**
         * @brief Determine the correct NODE_KIND for a function application.
         * Returns NT_DT_CONSTRUCTOR, NT_DT_SELECTOR, NT_DT_TESTER if the
         * function is a datatype function, otherwise NT_UF_APPLY.
         */
        NODE_KIND getDtFunctionKind(const std::shared_ptr<Sort>& return_sort, const std::string &name, const std::vector<std::shared_ptr<DAGNode>> &params);

        // mk sort
        /**
         * @brief Create a sort declaration
         * 
         * @param name Sort name
         * @param arity Arity
         * @return Sort declaration node
         */
        std::shared_ptr<Sort> mkSortDec(const std::string &name, const size_t &arity);

        /**
         * @brief Create a sort definition
         * 
         * @param name Sort name
         * @param params Parameters
         * @param out_sort Output sort
         * @return Sort definition node
         */
        std::shared_ptr<Sort> mkSortDef(const std::string &name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);

        /**
         * @brief Apply a declared sort constructor: `(S Bool)`.
         *
         * `(declare-sort S 1)` declares a function from sorts to sorts, not a
         * sort, so `mkSortDec` alone cannot produce a sort a variable may have.
         * parseSort builds the application inline; there was no builder, so a
         * caller working through the API could declare a constructor and had no
         * way to instantiate it except by reaching into `Sort::children`.
         *
         * Bad input yields the NULL sort rather than throwing, unlike the
         * DAGNode builders: those report through err_all, which throws and is
         * caught by parseStr, and an escaped exception makes a caller's own bad
         * argument look like a defect in this parser.
         *
         * @param ctor  the declared constructor, from `mkSortDec(name, arity)`
         * @param args  one sort per declared parameter; arity 0 returns @p ctor
         * @return the applied sort, or the NULL sort if the arity disagrees
         */
        std::shared_ptr<Sort> mkSortApp(const std::shared_ptr<Sort> &ctor,
                                        const std::vector<std::shared_ptr<Sort>> &args);

        // mk special sort
        /**
         * @brief Create an integer sort
         * 
         * @return Integer sort
         */
        std::shared_ptr<Sort> mkIntSort();
        /**
         * @brief Create a real sort
         * 
         * @return Real sort
         */
        std::shared_ptr<Sort> mkRealSort();
        /**
         * @brief Create a boolean sort
         * 
         * @return Boolean sort
         */
        std::shared_ptr<Sort> mkBoolSort();
        /**
         * @brief Create a string sort
         * 
         * @return String sort
         */
        std::shared_ptr<Sort> mkStrSort();
        /**
         * @brief Create a regular expression sort
         * 
         * @return Regular expression sort
         */
        std::shared_ptr<Sort> mkRegSort();
        /**
         * @brief Create a rounding mode sort
         * 
         * @return Rounding mode sort
         */
        std::shared_ptr<Sort> mkRoundingModeSort();
        /**
         * @brief Create a natural sort
         * 
         * @return Natural sort
         */
        std::shared_ptr<Sort> mkNatSort();
        /**
         * @brief Create a bit-vector sort
         * 
         * @param width Width of the bit-vector
         * @return Bit-vector sort
         */
        std::shared_ptr<Sort> mkBVSort(const size_t &width);
        /**
         * @brief Create a floating-point sort
         * 
         * @param e Exponent size
         * @param s Significand size
         * @return Floating-point sort
         */
        std::shared_ptr<Sort> mkFPSort(const size_t &e, const size_t &s);
        /**
         * @brief Create an array sort
         * 
         * @param index Index sort
         * @param elem Element sort
         * @return Array sort
         */
        std::shared_ptr<Sort> mkArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem);

        // declare var
        /**
         * @brief Declare a variable
         * 
         * @param name Variable name
         * @param sort Sort
         */
        std::shared_ptr<DAGNode> declareVar(const std::string &name, const std::string &sort);

        /**
         * @brief Declare a variable
         * 
         * @param name Variable name
         * @param sort Sort
         */
        std::shared_ptr<DAGNode> declareVar(const std::string &name, const std::shared_ptr<Sort> &sort);

        // mk true/false
        /**
         * @brief Create a true node
         * 
         * @return True node
         */
        std::shared_ptr<DAGNode>	mkTrue(); // true

        /**
         * @brief Create a false node
         * 
         * @return False node
         */
        std::shared_ptr<DAGNode>	mkFalse(); // false

        /**
         * @brief Create an unknown node
         * 
         * @return Unknown node
         */
        std::shared_ptr<DAGNode>    mkUnknown(); // unknown
        // CORE OPERATORS
        /**
         * @brief Create an equality node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Equality node
         */
        std::shared_ptr<DAGNode> mkEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r

        /**
         * @brief Create an equality node
         * 
         * @param params Parameters
         * @return Equality node
         */
        std::shared_ptr<DAGNode> mkEq(const std::vector<std::shared_ptr<DAGNode>>& params); // l = r = ... 
        
        /**
         * @brief Create a distinct node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Distinct node
         */
        std::shared_ptr<DAGNode> mkDistinct(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);

        /**
         * @brief Create a distinct node
         * 
         * @param params Parameters
         * @return Distinct node
         */
        std::shared_ptr<DAGNode> mkDistinct(const std::vector<std::shared_ptr<DAGNode>> &params); // l != r != ...
        
        // CONST
        /**
         * @brief Create an integer constant from string
         *
         * @param v Value (string)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const std::string &v); // CONST_INT
        
        /**
         * @brief Create an integer constant
         *
         * @param v Value (int)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const int& v); // CONST_INT
        
        /**
         * @brief Create an integer constant
         *
         * @param v Value (Integer)
         * @return Integer constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const Integer &v); // CONST_INT

        /**
         * @brief Create a real constant from number
         *
         * @param v Value (Number)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstInt(const Number& v); // CONST_INT

        /**
         * @brief Create a real constant from string
         *
         * @param v Value (string)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const std::string &v); // CONST_REAL
        
        /**
         * @brief Create a real constant
         *
         * @param v Value (Real)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const Real &v); // CONST_REAL
        
        /**
         * @brief Create a real constant from double
         *
         * @param v Value (double)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const double &v); // CONST_REAL
        
        /**
         * @brief Create a real constant from integer
         *
         * @param v Value (Integer)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const Integer &v); // CONST_REAL

        /**
         * @brief Create a real constant from number
         *
         * @param v Value (Number)
         * @return Real constant node
         */
        std::shared_ptr<DAGNode> mkConstReal(const Number& v); // CONST_REAL
        
        /**
         * @brief Create a string constant
         *
         * @param v Value (string)
         * @return String constant node
         */
        std::shared_ptr<DAGNode> mkConstStr(const std::string &v); // CONST_Str
        
        /**
         * @brief Create a bit-vector constant
         *
         * @param v Value (string)
         * @param width Width of the bit-vector
         * @return Bit-vector constant node
         */
        std::shared_ptr<DAGNode> mkConstBv(const std::string &v, const size_t& width); // CONST_BV
        
        /**
         * @brief Create a floating-point constant
         *
         * @param v Value (string)
         * @param e Exponent size
         * @param s Significand size
         * @return Floating-point constant node
         */
        std::shared_ptr<DAGNode> mkConstFp(const std::string &v, const size_t& e, const size_t& s); // CONST_FP
        
        /**
         * @brief Create a floating-point constant from expression
         *
         * @param fp_expr Floating-point expression string
         * @return Floating-point constant node
         */
        std::shared_ptr<DAGNode> mkConstFP(const std::string &fp_expr); // CONST_FP from expression
        
        /**
         * @brief Create a regular expression constant
         *
         * @param v Value (string)
         * @return Regular expression constant node
         */
        std::shared_ptr<DAGNode> mkConstReg(const std::string &v); // CONST_REG
        
        /**
         * @brief Create a rounding mode constant
         * 
         * @param mode Rounding mode string (RNE, RNA, RTP, RTN, RTZ)
         * @return Rounding mode constant node
         */
        std::shared_ptr<DAGNode> mkRoundingMode(const std::string &mode); // ROUNDING_MODE
        
        /**
         * @brief Create a rounding mode variable
         * 
         * @param name Variable name
         * @return Rounding mode variable node
         */
        std::shared_ptr<DAGNode> mkVarRoundingMode(const std::string &name); // VAR_ROUNDING_MODE
        
        // VAR
        /**
         * @brief Create a variable
         *
         * @param sort Sort
         * @param name Variable name
         * @return Variable node 
         */
        std::shared_ptr<DAGNode> mkVar(const std::shared_ptr<Sort>& sort, const std::string &name); // VAR
        std::shared_ptr<DAGNode> mkPlaceholderVar(const std::string &name); // PLACEHOLDER_VAR
        
        /**
         * @brief Create a temporary variable
         *
         * @param sort Sort
         * @return Temporary variable node
         */
        std::shared_ptr<DAGNode> mkTempVar(const std::shared_ptr<Sort>& sort); // TEMP_VAR
        
        /**
         * @brief Create a boolean variable
         *
         * @param name Variable name
         * @return Boolean variable node
         */
        std::shared_ptr<DAGNode> mkVarBool(const std::string &name); // VAR_BOOL
        
        /**
         * @brief Create an integer variable
         *
         * @param name Variable name
         * @return Integer variable node
         */
        std::shared_ptr<DAGNode> mkVarInt(const std::string &name); // VAR_INT
        
        /**
         * @brief Create a real variable
         *
         * @param name Variable name
         * @return Real variable node
         */
        std::shared_ptr<DAGNode> mkVarReal(const std::string &name); // VAR_REAL
        
        /**
         * @brief Create a bit-vector variable
         *
         * @param name Variable name
         * @param width Width of the bit-vector
         * @return Bit-vector variable node
         */
        std::shared_ptr<DAGNode> mkVarBv(const std::string &name, const size_t& width); // VAR_BV
        
        /**
         * @brief Create a floating-point variable
         *
         * @param name Variable name
         * @param e Exponent size
         * @param s Significand size
         * @return Floating-point variable node
         */
        std::shared_ptr<DAGNode> mkVarFp(const std::string &name, const size_t& e, const size_t& s); // VAR_FP
        
        /**
         * @brief Create a string variable
         *
         * @param name Variable name
         * @return String variable node
         */
        std::shared_ptr<DAGNode> mkVarStr(const std::string &name); // VAR_STR
        
        /**
         * @brief Create a regular expression variable
         *
         * @param name Variable name
         * @return Regular expression variable node
         */
        std::shared_ptr<DAGNode> mkVarReg(const std::string &name); // VAR_REG
        
        /**
         * @brief Create a function parameter variable
         *
         * @param sort Sort
         * @param name Variable name
         * @return Function parameter variable node
         */
        std::shared_ptr<DAGNode> mkFunParamVar(std::shared_ptr<Sort> sort, const std::string &name); // FUN_PARAM_VAR
        
        /**
         * @brief Create an array
         *
         * @param name Array name
         * @param index Index sort
         * @param elem Element sort
         * @return Array node
         */
        std::shared_ptr<DAGNode> mkArray(const std::string &name, std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem); // ARRAY
        
        /**
         * @brief Create a constant array node
         * 
         * @param sort Array sort
         * @param value Constant value for all elements
         * @return Constant array node
         */
        std::shared_ptr<DAGNode> mkConstArray(std::shared_ptr<Sort> sort, std::shared_ptr<DAGNode> value); // CONST ARRAY
        
        // BOOLEAN
        /**
         * @brief Create a not node
         * 
         * @param param Parameter
         * @return Not node (not param)
         */
        std::shared_ptr<DAGNode> mkNot(std::shared_ptr<DAGNode> param);
        
        /**
         * @brief Create an and node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return And node (l and r)
         */
        std::shared_ptr<DAGNode> mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an and node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return And node (l and m and r)
         */
        std::shared_ptr<DAGNode> mkAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an and node
         * 
         * @param params Parameters
         * @return And node (l and m and r and ...)
         */
        std::shared_ptr<DAGNode> mkAnd(const std::vector<std::shared_ptr<DAGNode>> &params);

        /**
         * @brief Create an and node
         * 
         * @param params Parameters
         * @return And node (l or r)
         */
        std::shared_ptr<DAGNode> mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an or node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Or node (l or m or r)
         */
        std::shared_ptr<DAGNode> mkOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an or node
         * 
         * @param params Parameters
         * @return Or node (l or m or r or ...)
         */
        std::shared_ptr<DAGNode> mkOr(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an implies node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Implies node (l -> r)
         */
        std::shared_ptr<DAGNode> mkImplies(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an implies node
         * 
         * @param params Parameters
         * @return Implies node (l -> r -> ...)
         */
        std::shared_ptr<DAGNode> mkImplies(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an xor node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Xor node (l xor r)
         */
        std::shared_ptr<DAGNode> mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an xor node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Xor node (l xor m xor r)
         */
        std::shared_ptr<DAGNode> mkXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an xor node
         * 
         * @param params Parameters
         * @return Xor node (l xor m xor r xor ...)
         */
        std::shared_ptr<DAGNode> mkXor(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an ite node
         * 
         * @param cond Condition
         * @param l Left parameter
         * @param r Right parameter
         * @return Ite node (cond ? l : r)
         */
        std::shared_ptr<DAGNode> mkIte(std::shared_ptr<DAGNode> cond, std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an ite node
         *
         * @note It only accepts 3 parameters.
         * 
         * @param params Parameters
         * @return Ite node (cond ? l : r)
         */
        std::shared_ptr<DAGNode> mkIte(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        // ARITHMATIC COMMON OPERATORS

        /**
         * @brief Create an add node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Add node (l + r)
         */
        std::shared_ptr<DAGNode> mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an add node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Add node (l + m + r)
         */
        std::shared_ptr<DAGNode> mkAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an add node
         * 
         * @param params Parameters
         * @return Add node (l + r + ...)
         */
        std::shared_ptr<DAGNode> mkAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        
        /**
         * @brief Create an mul node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Mul node (l * r)
         */
        std::shared_ptr<DAGNode> mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an mul node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Mul node (l * m * r) 
         */
        std::shared_ptr<DAGNode> mkMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an mul node
         *  
         * @param params Parameters
         * @return Mul node (l * r * ...)
         */
        std::shared_ptr<DAGNode> mkMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        
        /**
         * @brief Create an iand node
         * 
         * @param params Parameters
         * @return Iand node (l & r & ...)
         */
        std::shared_ptr<DAGNode> mkIand(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ... 
        
        /**
         * @brief Create an pow2 node
         * 
         * @param param Parameter
         * @return Pow2 node (2^param)
         */
        std::shared_ptr<DAGNode> mkPow2(std::shared_ptr<DAGNode> param); // 2^param
        
        /**
         * @brief Create an pow node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Pow node (l^r)
         */
        std::shared_ptr<DAGNode> mkPow(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l^r
        
        /**
         * @brief Create an sub node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Sub node (l - r)
         */
        std::shared_ptr<DAGNode> mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an sub node
         * 
         * @param l Left parameter
         * @param m Middle parameter
         * @param r Right parameter
         * @return Sub node (l - m - r)
         */
        std::shared_ptr<DAGNode> mkSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> m, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an sub node
         * 
         * @param params Parameters
         * @return Sub node (l - r - ...)
         */
        std::shared_ptr<DAGNode> mkSub(const std::vector<std::shared_ptr<DAGNode>> &params);
        
        /**
         * @brief Create an neg node
         * 
         * @param param Parameter
         * @return Neg node (-param)
         */
        std::shared_ptr<DAGNode> mkNeg(std::shared_ptr<DAGNode> param); // -param
        
        /**
         * @brief Create an div node
         * 
         * @note This is the real division operator.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * @note This is the real division operator.
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDiv(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /**
         * @brief Create an div node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDivInt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * @param params Parameters
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDivInt(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /**
         * @brief Create an div node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Div node (l / r)
         */
        std::shared_ptr<DAGNode> mkDivReal(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        
        /**
         * @brief Create an div node
         * 
         * @param params Parameters
         * @return Div node (l / r / ...)
         */
        std::shared_ptr<DAGNode> mkDivReal(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /** 
         * @brief Create an mod node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Mod node (l % r)
         */
        std::shared_ptr<DAGNode> mkMod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create an abs node
         * 
         * @param param Parameter
         * @return Abs node (|param|)
         */
        std::shared_ptr<DAGNode> mkAbs(std::shared_ptr<DAGNode> param); // |param|
        
        /**
         * @brief Create an sqrt node
         * 
         * @note assert(param >= 0) 
         *
         * @param param Parameter
         * @return Sqrt node (sqrt(param))
         */
        std::shared_ptr<DAGNode> mkSqrt(std::shared_ptr<DAGNode> param); // sqrt(param)
        
        /**
         * @brief Create an safeSqrt node
         * 
         * @note if param < 0, return 0
         * 
         * @param param Parameter
         * @return Safesqrt node (safeSqrt(param))
         */
        std::shared_ptr<DAGNode> mkSafeSqrt(std::shared_ptr<DAGNode> param); // safeSqrt(param)
        
        /**
         * @brief Create an ceil node
         * 
         * @param param Parameter
         * @return Ceil node (ceil(param))
         */
        std::shared_ptr<DAGNode> mkCeil(std::shared_ptr<DAGNode> param); // ceil(param)
        
        /**
         * @brief Create an floor node
         * 
         * @param param Parameter
         * @return Floor node (floor(param))
         */
        std::shared_ptr<DAGNode> mkFloor(std::shared_ptr<DAGNode> param); // floor(param)
        
        /**
         * @brief Create an round node
         * 
         * @param param Parameter
         * @return Round node (round(param))
         */
        std::shared_ptr<DAGNode> mkRound(std::shared_ptr<DAGNode> param); // round(param)
        
        // TRANSCENDENTAL ARITHMATIC
        /**
         * @brief Create an exp node
         * 
         * @param param Parameter
         * @return Exp node (exp(param))
         */
        std::shared_ptr<DAGNode> mkExp(std::shared_ptr<DAGNode> param); // exp(param)
        
        /**
         * @brief Create an ln node
         * 
         * @note assert(param > 0)
         * 
         * @param param Parameter
         * @return Ln node (ln(param))
         */
        std::shared_ptr<DAGNode> mkLn(std::shared_ptr<DAGNode> param); // ln(param)
        
        /**
         * @brief Create an lg/log10 node
         * 
         * @note assert(param > 0)
         *
         * @param param Parameter
         * @return Lg node (lg(param))
         */
        std::shared_ptr<DAGNode> mkLg(std::shared_ptr<DAGNode> param); // lg(param)
        
        /**
         * @brief Create an lb/log2 node
         * 
         * @note assert(param > 0)
         *
         * @param param Parameter
         * @return Lb node (lb(param))
         */
        std::shared_ptr<DAGNode> mkLb(std::shared_ptr<DAGNode> param); // lb(param)
        
        /**
         * @brief Create an log node
         * 
         * @note r is the base, l is the argument
         * @note assert(r > 0 && r != 1 && l > 0)
         *
         * @param l Left parameter
         * @param r Right parameter
         * @return Log node (log_r(l))
         */
        std::shared_ptr<DAGNode> mkLog(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // log_l(r)
        
        /**
         * @brief Create an sin node
         * 
         * @param param Parameter
         * @return Sin node (sin(param))
         */
        std::shared_ptr<DAGNode> mkSin(std::shared_ptr<DAGNode> param); // sin(param)
        
        /**
         * @brief Create an cos node
         * 
         * @param param Parameter
         * @return Cos node (cos(param))
         */
        std::shared_ptr<DAGNode> mkCos(std::shared_ptr<DAGNode> param); // cos(param)
        
        /**
         * @brief Create an sec node
         * 
         * @param param Parameter
         * @return Sec node (sec(param))
         */
        std::shared_ptr<DAGNode> mkSec(std::shared_ptr<DAGNode> param); // sec(param)
        
        /**
         * @brief Create an csc node
         * 
         * @param param Parameter
         * @return Csc node (csc(param))
         */
        std::shared_ptr<DAGNode> mkCsc(std::shared_ptr<DAGNode> param); // csc(param)
        
        /**
         * @brief Create an tan node
         * 
         * @note assert(param != (pi/2) + k*pi)
         * 
         * @param param Parameter
         * @return Tan node (tan(param))
         */
        std::shared_ptr<DAGNode> mkTan(std::shared_ptr<DAGNode> param); // tan(param)
        
        /**
         * @brief Create a cot node
         * 
         * @note assert(param != k*pi)
         * 
         * @param param Parameter
         * @return Cot node (cot(param))
         */
        std::shared_ptr<DAGNode> mkCot(std::shared_ptr<DAGNode> param); // cot(param)
        
        /**
         * @brief Create an asin node
         * 
         * @note assert(param >= -1 && param <= 1)
         * 
         * @param param Parameter
         * @return Asin node (asin(param))
         */
        std::shared_ptr<DAGNode> mkAsin(std::shared_ptr<DAGNode> param); // asin(param)
        
        /**
         * @brief Create an acos node
         * 
         * @note assert(param >= -1 && param <= 1)
         * 
         * @param param Parameter
         * @return Acos node (acos(param))
         */
        std::shared_ptr<DAGNode> mkAcos(std::shared_ptr<DAGNode> param); // acos(param)
        
        /**
         * @brief Create an asec node
         * 
         * @note assert(param <= -1 || param >= 1)
         * 
         * @param param Parameter
         * @return Asec node (asec(param))
         */
        std::shared_ptr<DAGNode> mkAsec(std::shared_ptr<DAGNode> param); // asec(param)
        
        /**
         * @brief Create an acsc node
         * 
         * @note assert(param <= -1 || param >= 1)
         * 
         * @param param Parameter
         * @return Acsc node (acsc(param))
         */
        std::shared_ptr<DAGNode> mkAcsc(std::shared_ptr<DAGNode> param); // acsc(param)
        
        /**
         * @brief Create an atan node
         * 
         * @param param Parameter
         * @return Atan node (atan(param))
         */
        std::shared_ptr<DAGNode> mkAtan(std::shared_ptr<DAGNode> param); // atan(param)
        
        /**
         * @brief Create an acot node
         * 
         * @param param Parameter
         * @return Acot node (acot(param))
         */
        std::shared_ptr<DAGNode> mkAcot(std::shared_ptr<DAGNode> param); // acot(param)
        
        /**
         * @brief Create a sinh node
         * 
         * @param param Parameter
         * @return Sinh node (sinh(param))
         */
        std::shared_ptr<DAGNode> mkSinh(std::shared_ptr<DAGNode> param); // sinh(param)
        
        /**
         * @brief Create a cosh node
         * 
         * @param param Parameter
         * @return Cosh node (cosh(param))
         */
        std::shared_ptr<DAGNode> mkCosh(std::shared_ptr<DAGNode> param); // cosh(param)
        
        /**
         * @brief Create a tanh node
         * 
         * @param param Parameter
         * @return Tanh node (tanh(param))
         */
        std::shared_ptr<DAGNode> mkTanh(std::shared_ptr<DAGNode> param); // tanh(param)
        
        /**
         * @brief Create a sech node
         * 
         * @param param Parameter
         * @return Sech node (sech(param))
         */
        std::shared_ptr<DAGNode> mkSech(std::shared_ptr<DAGNode> param); // sech(param)
        
        /**
         * @brief Create a csch node
         * 
         * @note assert(param != 0)
         * 
         * @param param Parameter
         * @return Csch node (csch(param))
         */
        std::shared_ptr<DAGNode> mkCsch(std::shared_ptr<DAGNode> param); // csch(param)
        
        /**
         * @brief Create a coth node
         * 
         * @note assert(param < -1 || param > 1)
         * 
         * @param param Parameter
         * @return Coth node (coth(param))
         */
        std::shared_ptr<DAGNode> mkCoth(std::shared_ptr<DAGNode> param); // coth(param)
        
        /**
         * @brief Create an asinh node
         * 
         * @param param Parameter
         * @return Asinh node (asinh(param))
         */
        std::shared_ptr<DAGNode> mkAsinh(std::shared_ptr<DAGNode> param); // asinh(param)
        
        /**
         * @brief Create an acosh node
         * 
         * @note assert(param >= 1)
         * 
         * @param param Parameter
         * @return Acosh node (acosh(param))
         */
        std::shared_ptr<DAGNode> mkAcosh(std::shared_ptr<DAGNode> param); // acosh(param)
        
        /**
         * @brief Create an atanh node
         * 
         * @note assert(param > -1 && param < 1)
         * 
         * @param param Parameter
         * @return Atanh node (atanh(param))
         */
        std::shared_ptr<DAGNode> mkAtanh(std::shared_ptr<DAGNode> param); // atanh(param)
        
        /**
         * @brief Create an asech node
         * 
         * @note assert(param > 0 && param <= 1)
         * 
         * @param param Parameter
         * @return Asech node (asech(param))
         */
        std::shared_ptr<DAGNode> mkAsech(std::shared_ptr<DAGNode> param); // asech(param)
        
        /**
         * @brief Create an acsch node
         * 
         * @note assert(param != 0)
         * 
         * @param param Parameter
         * @return Acsch node (acsch(param))
         */
        std::shared_ptr<DAGNode> mkAcsch(std::shared_ptr<DAGNode> param); // acsch(param)
        
        /**
         * @brief Create an acoth node
         * 
         * @note assert(param < -1 || param > 1)
         * 
         * @param param Parameter
         * @return Acoth node (acoth(param))
         */
        std::shared_ptr<DAGNode> mkAcoth(std::shared_ptr<DAGNode> param); // acoth(param)
        
        /**
         * @brief Create an atan2 node
         * 
         * @note Represents the angle in radians between the positive x-axis and the ray to point (r, l)
         * @note atan2(l, r) = atan(l/r) with appropriate quadrant adjustment
         * 
         * @param l Left parameter (y-coordinate)
         * @param r Right parameter (x-coordinate)
         * @return Atan2 node (atan2(l, r))
         */
        std::shared_ptr<DAGNode> mkAtan2(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r);
        // ARITHMATIC COMP

        /**
         * @brief Create a le node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Le node (l <= r)
         */
        std::shared_ptr<DAGNode> mkLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r

        /**
         * @brief Create a lt node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Lt node (l < r)
         */
        std::shared_ptr<DAGNode> mkLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        
        /**
         * @brief Create a ge node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Ge node (l >= r)
         */
        std::shared_ptr<DAGNode> mkGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r

        /**
         * @brief Create a gt node
         *
         * @param l Left parameter
         * @param r Right parameter
         * @return Gt node (l > r)
         */
        std::shared_ptr<DAGNode> mkGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        
        /**
         * @brief Create a le node
         * 
         * @param params Parameters
         * @return Le node (l <= r <= ... <= s)
         */
        std::shared_ptr<DAGNode> mkLe(const std::vector<std::shared_ptr<DAGNode>>& params); // l <= r

        /**
         * @brief Create a lt node
         * 
         * @param params Parameters
         * @return Lt node (l < r < ... < s)
         */
        std::shared_ptr<DAGNode> mkLt(const std::vector<std::shared_ptr<DAGNode>>& params); // l < r

        /**
         * @brief Create a ge node
         * 
         * @param params Parameters
         * @return Ge node (l >= r >= ... >= s)
         */
        std::shared_ptr<DAGNode> mkGe(const std::vector<std::shared_ptr<DAGNode>>& params); // l >= r >= ... >= s

        /**
         * @brief Create a gt node
         * 
         * @param params Parameters
         * @return Gt node (l > r > ... > s)
         */
        std::shared_ptr<DAGNode> mkGt(const std::vector<std::shared_ptr<DAGNode>>& params); // l > r > ... > s
        
        // ARITHMATIC CONVERSION

        /**
         * @brief Create a to_int node
         * 
         * @param param Parameter
         * @return To_int node (to_int(param))
         */
        std::shared_ptr<DAGNode> mkToInt(std::shared_ptr<DAGNode> param); // to_int(param)

        /**
         * @brief Create a to_real node
         * 
         * @param param Parameter
         * @return To_real node (to_real(param))
         */
        std::shared_ptr<DAGNode> mkToReal(std::shared_ptr<DAGNode> param); // to_real(param)

        // ARITHMATIC PROPERTIES
        /**
         * @brief Create a is_int node
         * 
         * @param param Parameter
         * @return Is_int node (is_int(param))
         */
        std::shared_ptr<DAGNode> mkIsInt(std::shared_ptr<DAGNode> param); // is_int(param)

        /**
         * @brief Create a is_divisible node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Is_divisible node (is_divisible(l, r), l divides r)
         */
        std::shared_ptr<DAGNode> mkIsDivisible(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // is_divisible(l, r)

        /**
         * @brief Create a is_prime node
         * 
         * @param param Parameter
         * @return Is_prime node (is_prime(param))
         */
        std::shared_ptr<DAGNode> mkIsPrime(std::shared_ptr<DAGNode> param); // is_prime(param)

        /**
         * @brief Create a is_even node
         * 
         * @param param Parameter
         * @return Is_even node (is_even(param))
         */
        std::shared_ptr<DAGNode> mkIsEven(std::shared_ptr<DAGNode> param); // is_even(param)

        /**
         * @brief Create a is_odd node
         * 
         * @param param Parameter
         * @return Is_odd node (is_odd(param))
         */
        std::shared_ptr<DAGNode> mkIsOdd(std::shared_ptr<DAGNode> param); // is_odd(param)

        // ARITHMATIC CONSTANTS

        /**
         * @brief Create a pi node
         * 
         * @return Pi node (pi, i.e., the ratio of the circumference of a circle to its diameter)
         */
        std::shared_ptr<DAGNode> mkPi(); // pi

        /**
         * @brief Create a e node
         * 
         * @return E node (e, i.e., the base of the natural logarithm)
         */
        std::shared_ptr<DAGNode> mkE(); // e

        /**
         * @brief Create a infinity node
         * 
         * @return Infinity node (infinity)
         */
        std::shared_ptr<DAGNode> mkInfinity(std::shared_ptr<Sort> sort); // infinity

        /**
         * @brief Create a positive infinity node
         * 
         * @param sort Optional sort (for FP types, will include eb sb in name)
         * @return Positive infinity node (+infinity)
         */
        std::shared_ptr<DAGNode> mkPosInfinity(std::shared_ptr<Sort> sort = nullptr); // +infinity

        /**
         * @brief Create a negative infinity node
         * 
         * @param sort Optional sort (for FP types, will include eb sb in name)
         * @return Negative infinity node (-infinity)
         */
        std::shared_ptr<DAGNode> mkNegInfinity(std::shared_ptr<Sort> sort = nullptr); // -infinity

        /**
         * @brief Create a NaN node
         * 
         * @param sort Optional sort (for FP types, will include eb sb in name)
         * @return NaN node (nan, i.e., Not a Number)
         */
        std::shared_ptr<DAGNode> mkNaN(std::shared_ptr<Sort> sort = nullptr); // nan

        /**
         * @brief Create a epsilon node
         * 
         * @return Epsilon node (epsilon, i.e., a infinitesimal number)
         */
        std::shared_ptr<DAGNode> mkEpsilon(); // epsilon
        
        /**
         * @brief Create a positive epsilon node
         * 
         * @return Positive epsilon node (+epsilon)
         */
        std::shared_ptr<DAGNode> mkPosEpsilon(); // +epsilon

        /**
         * @brief Create a negative epsilon node
         * 
         * @return Negative epsilon node (-epsilon)
         */ 
        std::shared_ptr<DAGNode> mkNegEpsilon(); // -epsilon
        
        // ARITHMATIC FUNCTIONS
        
        /**
         * @brief Create a gcd node
         * 
         * @note assert(l != 0 || r != 0)
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Gcd node (gcd(l, r))
         */
        std::shared_ptr<DAGNode> mkGcd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // gcd(l, r)

        /**
         * @brief Create a lcm node
         * 
         * @note assert(l != 0 && r != 0)
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Lcm node (lcm(l, r))
         */
        std::shared_ptr<DAGNode> mkLcm(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // lcm(l, r)

        /**
         * @brief Create a factorial node
         * 
         * @note assert(param >= 0)
         * 
         * @param param Parameter
         * @return Factorial node (factorial(param))
         */
        std::shared_ptr<DAGNode> mkFact(std::shared_ptr<DAGNode> param); // factorial(param)
        
        // BITVECTOR COMMON OPERATORS
        /**
         * @brief Create a bitvector not node
         * 
         * @param param Parameter
         * @return Bitvector not node (~param)
         */
        std::shared_ptr<DAGNode> mkBvNot(std::shared_ptr<DAGNode> param); // ~param
        
        /**
         * @brief Create a bitvector and node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector and node (l & r)
         */
        std::shared_ptr<DAGNode> mkBvAnd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l & r
        
        /**
         * @brief Create a bitvector and node
         * 
         * @param params Parameters
         * @return Bitvector and node (l & r & ...)
         */
        std::shared_ptr<DAGNode> mkBvAnd(const std::vector<std::shared_ptr<DAGNode>> &params); // l & r & ...
        
        /**
         * @brief Create a bitvector or node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector or node (l | r)
         */
        std::shared_ptr<DAGNode> mkBvOr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l | r
        
        /**
         * @brief Create a bitvector or node
         * 
         * @param params Parameters
         * @return Bitvector or node (l | r | ...)
         */
        std::shared_ptr<DAGNode> mkBvOr(const std::vector<std::shared_ptr<DAGNode>> &params); // l | r | ...
        
        /**
         * @brief Create a bitvector xor node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector xor node (l ^ r)
         */
        std::shared_ptr<DAGNode> mkBvXor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l ^ r
        
        /**
         * @brief Create a bitvector xor node
         * 
         * @param params Parameters
         * @return Bitvector xor node (l ^ r ^ ...)
         */
        std::shared_ptr<DAGNode> mkBvXor(const std::vector<std::shared_ptr<DAGNode>> &params); // l ^ r ^ ...
        
        /**
         * @brief Create a bitvector nand node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector nand node (~(l & r))
         */
        std::shared_ptr<DAGNode> mkBvNand(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l & r)
        
        /**
         * @brief Create a bitvector nand node
         * 
         * @param params Parameters
         * @return Bitvector nand node (~(l & r & ...))
         */
        std::shared_ptr<DAGNode> mkBvNand(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l & r & ...)
        
        /**
         * @brief Create a bitvector nor node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector nor node (~(l | r))
         */
        std::shared_ptr<DAGNode> mkBvNor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l | r)
        
        /**
         * @brief Create a bitvector nor node
         * 
         * @param params Parameters
         * @return Bitvector nor node (~(l | r | ...))
         */
        std::shared_ptr<DAGNode> mkBvNor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l | r | ...)
        
        /**
         * @brief Create a bitvector xnor node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector xnor node (~(l ^ r))
         */
        std::shared_ptr<DAGNode> mkBvXnor(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // ~(l ^ r)
        
        /**
         * @brief Create a bitvector comparison node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector comparison node (l = r ? #b1 : #b0)
         */
        std::shared_ptr<DAGNode> mkBvComp(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        
        /**
         * @brief Create a bitvector xnor node
         * 
         * @param params Parameters
         * @return Bitvector xnor node (~(l ^ r ^ ...))
         */
        std::shared_ptr<DAGNode> mkBvXnor(const std::vector<std::shared_ptr<DAGNode>> &params); // ~(l ^ r ^ ...)
        
        /**
         * @brief Create a bitvector negation node
         * 
         * @param param Parameter
         * @return Bitvector negation node (-param)
         */
        std::shared_ptr<DAGNode> mkBvNeg(std::shared_ptr<DAGNode> param); // -param
        
        /**
         * @brief Create a bitvector addition node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector addition node (l + r)
         */
        std::shared_ptr<DAGNode> mkBvAdd(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l + r
        
        /**
         * @brief Create a bitvector addition node
         * 
         * @param params Parameters
         * @return Bitvector addition node (l + r + ...)
         */
        std::shared_ptr<DAGNode> mkBvAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        
        /**
         * @brief Create a bitvector subtraction node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector subtraction node (l - r)
         */
        std::shared_ptr<DAGNode> mkBvSub(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l - r
        
        /**
         * @brief Create a bitvector subtraction node
         * 
         * @param params Parameters
         * @return Bitvector subtraction node (l - r - ...)
         */
        std::shared_ptr<DAGNode> mkBvSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        
        /**
         * @brief Create a bitvector multiplication node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector multiplication node (l * r)
         */
        std::shared_ptr<DAGNode> mkBvMul(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        
        /**
         * @brief Create a bitvector multiplication node
         * 
         * @param params Parameters
         * @return Bitvector multiplication node (l * r * ...)
         */
        std::shared_ptr<DAGNode> mkBvMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        
        /**
         * @brief Create a bitvector unsigned division node
         * 
         * @note if r == 0, then return all ones bit-vector
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned division node (l / r)
         */
        std::shared_ptr<DAGNode> mkBvUdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        
        /**
         * @brief Create a bitvector unsigned remainder node
         * 
         * @note if r == 0, then return l
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned remainder node (l % r)
         */
        std::shared_ptr<DAGNode> mkBvUrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create a bitvector unsigned modulo node
         * 
         * @note if r == 0, then return l
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned modulo node (l % r)
         */
        std::shared_ptr<DAGNode> mkBvUmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create a bitvector signed division node
         * 
         * @note if r == 0, then return all ones bit-vector if l is positive, otherwise 1
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed division node (l / r)
         */
        std::shared_ptr<DAGNode> mkBvSdiv(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l / r
        
        /**
         * @brief Create a bitvector signed remainder node
         * 
         * @note if r == 0, then return l
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed remainder node (l % r)
         */
        std::shared_ptr<DAGNode> mkBvSrem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create a bitvector signed modulo node
         * 
         * @note if r == 0, then return l
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed modulo node (l % r)
         */
        std::shared_ptr<DAGNode> mkBvSmod(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create a bitvector shift left node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector shift left node (l << r)
         */
        std::shared_ptr<DAGNode> mkBvShl(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l << r
        
        /**
         * @brief Create a bitvector logical shift right node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector logical shift right node (l >> r)
         */
        std::shared_ptr<DAGNode> mkBvLshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        
        /**
         * @brief Create a bitvector arithmetic shift right node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector arithmetic shift right node (l >> r)
         */
        std::shared_ptr<DAGNode> mkBvAshr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >> r
        
        /**
         * @brief Create a bitvector concatenation node
         * 
         * @param params Parameters
         * @return Bitvector concatenation node (l ++ r ++ ...)
         */
        std::shared_ptr<DAGNode> mkBvConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // l ++ r ++ ...
        
        /**
         * @brief Create a bitvector extract node
         * 
         * Creates a bitvector extract node that extracts a range of bits.
         * 
         * @note assert(r >= s && r < bitwidth(l))
         * 
         * @param l Source bitvector
         * @param r Upper index (inclusive)
         * @param s Lower index (inclusive)
         * @return Bitvector extract node (l[r:s])
         */
        std::shared_ptr<DAGNode> mkBvExtract(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l[r:s]
        
        /**
         * @brief Create a bitvector repeat node
         * 
         * Creates a bitvector repeat node that repeats the bitvector r times.
         * 
         * @note assert(r > 0)
         * 
         * @param l Source bitvector
         * @param r Repeat count
         * @return Bitvector repeat node (l repeated r times)
         */
        std::shared_ptr<DAGNode> mkBvRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l * r
        
        /**
         * @brief Create a bitvector zero extension node
         * 
         * Creates a bitvector zero extension node that extends the bitvector with r zero bits.
         * 
         * @param l Source bitvector
         * @param r Number of bits to extend
         * @return Bitvector zero extension node (l zero_extend r)
         */
        std::shared_ptr<DAGNode> mkBvZeroExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l zero_extend r
        
        /**
         * @brief Create a bitvector sign extension node
         * 
         * Creates a bitvector sign extension node that extends the bitvector with r sign bits.
         * 
         * @param l Source bitvector
         * @param r Number of bits to extend
         * @return Bitvector sign extension node (l sign_extend r)
         */
        std::shared_ptr<DAGNode> mkBvSignExt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l sign_extend r
        
        /**
         * @brief Create a bitvector rotate left node
         * 
         * @param l Source bitvector
         * @param r Rotation amount
         * @return Bitvector rotate left node (l <<< r)
         */
        std::shared_ptr<DAGNode> mkBvRotateLeft(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <<< r
        
        /**
         * @brief Create a bitvector rotate right node
         * 
         * @param l Source bitvector
         * @param r Rotation amount
         * @return Bitvector rotate right node (l >>> r)
         */
        std::shared_ptr<DAGNode> mkBvRotateRight(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >>> r
        
        // BITVECTOR COMP
        /**
         * @brief Create a bitvector unsigned less than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned less than node (l < r)
         */
        std::shared_ptr<DAGNode> mkBvUlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        
        /**
         * @brief Create a bitvector unsigned less than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned less than or equal node (l <= r)
         */
        std::shared_ptr<DAGNode> mkBvUle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        
        /**
         * @brief Create a bitvector unsigned greater than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned greater than node (l > r)
         */
        std::shared_ptr<DAGNode> mkBvUgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        
        /**
         * @brief Create a bitvector unsigned greater than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector unsigned greater than or equal node (l >= r)
         */
        std::shared_ptr<DAGNode> mkBvUge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        
        /**
         * @brief Create a bitvector signed less than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed less than node (l < r)
         */
        std::shared_ptr<DAGNode> mkBvSlt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        
        /**
         * @brief Create a bitvector signed less than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed less than or equal node (l <= r)
         */
        std::shared_ptr<DAGNode> mkBvSle(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        
        /**
         * @brief Create a bitvector signed greater than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed greater than node (l > r)
         */
        std::shared_ptr<DAGNode> mkBvSgt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        
        /**
         * @brief Create a bitvector signed greater than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Bitvector signed greater than or equal node (l >= r)
         */
        std::shared_ptr<DAGNode> mkBvSge(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        
        // BITVECTOR CONVERSION
        /**
         * @brief Create a bitvector to natural number conversion node
         * 
         * @param param Parameter
         * @return Bitvector to natural number conversion node (to_nat(param))
         */
        std::shared_ptr<DAGNode> mkBvToNat(std::shared_ptr<DAGNode> param); // to_nat(param)
        
        /**
         * @brief Create a natural number to bitvector conversion node
         * 
         * @note assert(param >= 0 && width > 0 && param < 2^width)
         * 
         * @param param Parameter (natural number)
         * @param width Width of the resulting bitvector
         * @return Natural number to bitvector conversion node (to_bv(param, width))
         */
        std::shared_ptr<DAGNode> mkNatToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)
        
        /**
         * @brief Create a bitvector to integer conversion node
         * 
         * @param param Parameter
         * @return Bitvector to integer conversion node (to_int(param))
         */
        std::shared_ptr<DAGNode> mkBvToInt(std::shared_ptr<DAGNode> param); // to_int(param)
        
        /**
         * @brief Create an integer to bitvector conversion node
         * 
         * @note assert(width > 0 && param >= -2^(width-1) && param < 2^(width-1))
         * 
         * @param param Parameter (integer number)
         * @param width Width of the resulting bitvector
         * @return Integer to bitvector conversion node (to_bv(param, width))
         */
        std::shared_ptr<DAGNode> mkIntToBv(std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> width); // to_bv(param, width)

        /**
         * @brief Create an unsigned bitvector-to-integer node (SMT-LIB 2.7 ubv_to_int)
         *
         * @param param Bitvector parameter
         * @return ubv_to_int(param)
         */
        std::shared_ptr<DAGNode> mkUbvToInt(std::shared_ptr<DAGNode> param);

        /**
         * @brief Create a signed bitvector-to-integer node (SMT-LIB 2.7 sbv_to_int)
         *
         * @param param Bitvector parameter
         * @return sbv_to_int(param)
         */
        std::shared_ptr<DAGNode> mkSbvToInt(std::shared_ptr<DAGNode> param);

        // FLOATING POINT COMMON OPERATORS
        /**
         * @brief Create a floating-point addition node
         * 
         * @param params Parameters
         * @return Floating-point addition node (fp.add(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkFpAdd(const std::vector<std::shared_ptr<DAGNode>> &params); // l + r + ...
        
        /**
         * @brief Create a floating-point subtraction node
         * 
         * @param params Parameters
         * @return Floating-point subtraction node (fp.sub(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkFpSub(const std::vector<std::shared_ptr<DAGNode>> &params); // l - r - ...
        
        /**
         * @brief Create a floating-point multiplication node
         * 
         * @param params Parameters
         * @return Floating-point multiplication node (fp.mul(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkFpMul(const std::vector<std::shared_ptr<DAGNode>> &params); // l * r * ...
        
        /**
         * @brief Create a floating-point division node
         * 
         * @note Division by zero results in appropriate IEEE-754 behavior
         * 
         * @param params Parameters
         * @return Floating-point division node (fp.div(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkFpDiv(const std::vector<std::shared_ptr<DAGNode>> &params); // l / r / ...
        
        /**
         * @brief Create a floating-point absolute value node
         * 
         * @param param Parameter
         * @return Floating-point absolute value node (fp.abs(param))
         */
        std::shared_ptr<DAGNode> mkFpAbs(std::shared_ptr<DAGNode> param); // |param|
        
        /**
         * @brief Create a floating-point negation node
         * 
         * @param param Parameter
         * @return Floating-point negation node (fp.neg(param))
         */
        std::shared_ptr<DAGNode> mkFpNeg(std::shared_ptr<DAGNode> param); // -param
        
        /**
         * @brief Create a floating-point remainder node
         * 
         * @note IEEE-754 remainder operation
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point remainder node (fp.rem(l, r))
         */
        std::shared_ptr<DAGNode> mkFpRem(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l % r
        
        /**
         * @brief Create a floating-point fused multiply-add node
         * 
         * @note The operation (a * b + c) performed with only one rounding
         * 
         * @param params Parameters (should have exactly 3 elements)
         * @return Floating-point fused multiply-add node (fp.fma(a, b, c) = a * b + c)
         */
        std::shared_ptr<DAGNode> mkFpFma(const std::vector<std::shared_ptr<DAGNode>> &params); // fma(a, b, c) = a * b + c
        
        /**
         * @brief Create a floating-point square root node
         * 
         * @note Returns NaN for negative values
         * 
         * @param param Parameter
         * @return Floating-point square root node (fp.sqrt(param))
         */
        std::shared_ptr<DAGNode> mkFpSqrt(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param); // sqrt(rm, param)
        
        /**
         * @brief Create a floating-point round to integral node
         * 
         * @param param Parameter
         * @return Floating-point round to integral node (fp.roundToIntegral(param))
         */
        std::shared_ptr<DAGNode> mkFpRoundToIntegral(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param); // round_to_integral(rm, param)
        
        /**
         * @brief Create a floating-point minimum node
         * 
         * @param params Parameters
         * @return Floating-point minimum node (fp.min(params))
         */
        std::shared_ptr<DAGNode> mkFpMin(const std::vector<std::shared_ptr<DAGNode>> &params); // fp.min(params)
        
        /**
         * @brief Create a floating-point maximum node
         * 
         * @param params Parameters
         * @return Floating-point maximum node (fp.max(params))
         */
        std::shared_ptr<DAGNode> mkFpMax(const std::vector<std::shared_ptr<DAGNode>> &params); // fp.max(params)
        
        // FLOATING POINT COMP
        /**
         * @brief Create a floating-point less than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point less than or equal node (fp.leq(l, r))
         */
        std::shared_ptr<DAGNode> mkFpLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l <= r
        
        /**
         * @brief Create a floating-point less than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point less than node (fp.lt(l, r))
         */
        std::shared_ptr<DAGNode> mkFpLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l < r
        
        /**
         * @brief Create a floating-point greater than or equal node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point greater than or equal node (fp.geq(l, r))
         */
        std::shared_ptr<DAGNode> mkFpGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l >= r
        
        /**
         * @brief Create a floating-point greater than node
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point greater than node (fp.gt(l, r))
         */
        std::shared_ptr<DAGNode> mkFpGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l > r
        
        /**
         * @brief Create a floating-point equality node
         * 
         * @note This is IEEE-754 equality (NaN != NaN)
         * 
         * @param l Left parameter
         * @param r Right parameter
         * @return Floating-point equality node (fp.eq(l, r))
         */
        std::shared_ptr<DAGNode> mkFpEq(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l = r
        
        // FLOATING POINT CONVERSION
        /**
         * @brief Create a floating-point to unsigned bitvector conversion node
         * 
         * @note Rounds toward zero, returns max representable value if out of range
         * 
         * @param param Floating-point value
         * @param size Size of resulting bitvector
         * @return Floating-point to unsigned bitvector conversion node (fp.to_ubv(param, size))
         */
        std::shared_ptr<DAGNode> mkFpToUbv(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_ubv(rm, param, size)
        
        /**
         * @brief Create a floating-point to signed bitvector conversion node
         * 
         * @note Rounds toward zero, returns max/min representable value if out of range
         * 
         * @param param Floating-point value
         * @param size Size of resulting bitvector
         * @return Floating-point to signed bitvector conversion node (fp.to_sbv(param, size))
         */
        std::shared_ptr<DAGNode> mkFpToSbv(std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param, std::shared_ptr<DAGNode> size); // to_sbv(rm, param, size)
        
        /**
         * @brief Create a floating-point to real conversion node
         * 
         * @note NaN and infinity cannot be converted to real
         * 
         * @param param Floating-point value
         * @return Floating-point to real conversion node (fp.to_real(param))
         */
        std::shared_ptr<DAGNode> mkFpToReal(std::shared_ptr<DAGNode> param); // to_real(param)
        
        /**
         * @brief Create a floating-point to IEEE bit-vector conversion node
         * 
         * @param param Floating-point value
         * @return Bit-vector of width ebits+sbits representing the IEEE-754 encoding
         */
        std::shared_ptr<DAGNode> mkFpToIeeeBv(std::shared_ptr<DAGNode> param); // ((_ fp.to_ieee_bv nbits) param)
        
        /**
         * @brief Create a value to floating-point conversion node
         * 
         * @param eb Exponent bit width
         * @param sb Significand bit width
         * @param param Value to convert
         * @return Value to floating-point conversion node (to_fp(eb, sb, param))
         */
        std::shared_ptr<DAGNode> mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param); // to_fp(eb, sb, rm, param)
        std::shared_ptr<DAGNode> mkToFp(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> param); // to_fp(eb, sb, param)
        std::shared_ptr<DAGNode> mkToFpUnsigned(std::shared_ptr<DAGNode> eb, std::shared_ptr<DAGNode> sb, std::shared_ptr<DAGNode> rm, std::shared_ptr<DAGNode> param); // to_fp_unsigned(eb, sb, rm, param)
        std::shared_ptr<DAGNode> mkFpConst(std::shared_ptr<DAGNode> sign, std::shared_ptr<DAGNode> exp, std::shared_ptr<DAGNode> mant); // fp(sign, exp, mant)
        
        // ROOT OBJECT
        std::shared_ptr<DAGNode> mkRootObj(std::shared_ptr<DAGNode> expr, int index); // root-obj(expr, index)
        std::shared_ptr<DAGNode> mkRootOfWithInterval(const std::vector<std::shared_ptr<DAGNode>>& coeffs, std::shared_ptr<DAGNode> lower_bound, std::shared_ptr<DAGNode> upper_bound); // root-of-with-interval(coeffs, lower_bound, upper_bound)
        std::shared_ptr<DAGNode> mkRealAlgebraicNumber(std::shared_ptr<DAGNode> polynomial, std::shared_ptr<DAGNode> lower_bound, std::shared_ptr<DAGNode> upper_bound); // (_ real_algebraic_number <polynomial>, (lower_bound, upper_bound)>)
        
        // FLOATING POINT PROPERTIES
        /**
         * @brief Create a floating-point is-normal check node
         * 
         * @param param Parameter to check
         * @return Is-normal check node (fp.isNormal(param))
         */
        std::shared_ptr<DAGNode> mkFpIsNormal(std::shared_ptr<DAGNode> param); // is_normal(param)
        
        /**
         * @brief Create a floating-point is-subnormal check node
         * 
         * @param param Parameter to check
         * @return Is-subnormal check node (fp.isSubnormal(param))
         */
        std::shared_ptr<DAGNode> mkFpIsSubnormal(std::shared_ptr<DAGNode> param); // is_subnormal(param)
        
        /**
         * @brief Create a floating-point is-zero check node
         * 
         * @param param Parameter to check
         * @return Is-zero check node (fp.isZero(param))
         */
        std::shared_ptr<DAGNode> mkFpIsZero(std::shared_ptr<DAGNode> param); // is_zero(param)
        
        /**
         * @brief Create a floating-point is-infinity check node
         * 
         * @param param Parameter to check
         * @return Is-infinity check node (fp.isInf(param))
         */
        std::shared_ptr<DAGNode> mkFpIsInf(std::shared_ptr<DAGNode> param); // is_inf(param)
        
        /**
         * @brief Create a floating-point is-NaN check node
         * 
         * @param param Parameter to check
         * @return Is-NaN check node (fp.isNaN(param))
         */
        std::shared_ptr<DAGNode> mkFpIsNaN(std::shared_ptr<DAGNode> param); // is_nan(param)
        
        /**
         * @brief Create a floating-point is-negative check node
         * 
         * @param param Parameter to check
         * @return Is-negative check node (fp.isNegative(param))
         */
        std::shared_ptr<DAGNode> mkFpIsNeg(std::shared_ptr<DAGNode> param); // is_neg(param)
        
        /**
         * @brief Create a floating-point is-positive check node
         * 
         * @param param Parameter to check
         * @return Is-positive check node (fp.isPositive(param))
         */
        std::shared_ptr<DAGNode> mkFpIsPos(std::shared_ptr<DAGNode> param); // is_pos(param)
        
        // ARRAY
        /**
         * @brief Create an array select node
         * 
         * @param l Array
         * @param r Index
         * @return Array select node (l[r])
         */
        std::shared_ptr<DAGNode> mkSelect(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l[r]
        
        /**
         * @brief Create an array store node
         * 
         * @note Returns a new array, the original array is not modified
         * 
         * @param l Array
         * @param r Index
         * @param v Value
         * @return Array store node (l[r] = v)
         */
        std::shared_ptr<DAGNode> mkStore(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // l[r] = v

        // TERM ANNOTATIONS
        /** @brief Create a :pattern annotation node holding the trigger terms */
        std::shared_ptr<DAGNode> mkPattern(const std::vector<std::shared_ptr<DAGNode>> &params);
        /** @brief Create a :no-pattern annotation node */
        std::shared_ptr<DAGNode> mkNoPattern(std::shared_ptr<DAGNode> param);
        /** @brief Create a :weight annotation node */
        std::shared_ptr<DAGNode> mkWeight(std::shared_ptr<DAGNode> weight);
        /** @brief Create a :qid annotation node */
        std::shared_ptr<DAGNode> mkQid(const std::string &qid);
        /**
         * @brief Wrap @p term in (! <term> <annotations>...); returns @p term unchanged
         *        when there are no annotations.
         */
        std::shared_ptr<DAGNode> mkAttribute(std::shared_ptr<DAGNode> term, const std::vector<std::shared_ptr<DAGNode>> &annotations);

        // TUPLE OPERATORS
        /**
         * @brief Create a tuple constructor node (tuple t1 ... tn); nullary yields tuple.unit
         */
        std::shared_ptr<DAGNode> mkTuple(const std::vector<std::shared_ptr<DAGNode>> &params);
        /**
         * @brief Create a tuple projection node ((_ tuple.select i) t)
         */
        std::shared_ptr<DAGNode> mkTupleSelect(std::shared_ptr<DAGNode> tuple, std::shared_ptr<DAGNode> index);
        /**
         * @brief Create a functional tuple update node ((_ tuple.update i) t v)
         */
        std::shared_ptr<DAGNode> mkTupleUpdate(std::shared_ptr<DAGNode> tuple, std::shared_ptr<DAGNode> index, std::shared_ptr<DAGNode> value);
        /**
         * @brief Create a tuple projection node ((_ tuple.project i1 ... ik) t)
         */
        std::shared_ptr<DAGNode> mkTupleProject(std::shared_ptr<DAGNode> tuple, const std::vector<std::shared_ptr<DAGNode>> &indices);
        /**
         * @brief Create a datatype update node ((_ update <selector>) t v)
         */
        std::shared_ptr<DAGNode> mkDtUpdate(const std::string &selector, std::shared_ptr<DAGNode> dt, std::shared_ptr<DAGNode> value);

        // STRINGS COMMON OPERATORS
        /**
         * @brief Create a string length node
         * 
         * @param param String
         * @return String length node (str.len(param))
         */
        std::shared_ptr<DAGNode> mkStrLen(std::shared_ptr<DAGNode> param); // str.len(param)
        
        /**
         * @brief Create a string concatenation node
         * 
         * @param params Strings to concatenate
         * @return String concatenation node (str.++(param1, param2, ...))
         */
        std::shared_ptr<DAGNode> mkStrConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // str.++(param1, param2, ...)
        
        /**
         * @brief Create a string substring node
         * 
         * @param l String
         * @param r Start index
         * @param s Length
         * @return String substring node (str.substr(l, r, s), i.e., l[r, r+s))
         */
        std::shared_ptr<DAGNode> mkStrSubstr(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.substr(l, r, s)
        
        /**
         * @brief Create a string prefix check node
         * 
         * @param l Prefix
         * @param r String
         * @return String prefix check node (str.prefixof(l, r))
         */
        std::shared_ptr<DAGNode> mkStrPrefixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.prefixof(l, r)
        
        /**
         * @brief Create a string suffix check node
         * 
         * @param l Suffix
         * @param r String
         * @return String suffix check node (str.suffixof(l, r))
         */
        std::shared_ptr<DAGNode> mkStrSuffixof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.suffixof(l, r)
        
        /**
         * @brief Create a string index-of node
         * 
         * @param l String
         * @param r Substring to find
         * @param s Start index
         * @return String index-of node (str.indexof(l, r, s))
         */
        std::shared_ptr<DAGNode> mkStrIndexof(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.indexof(l, r, s)
        
        /**
         * @brief Create a string char-at node
         * 
         * @param l String
         * @param r Index
         * @return String char-at node (str.at(l, r))
         */
        std::shared_ptr<DAGNode> mkStrCharat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.charAt(l, r)
        
        /**
         * @brief Create a string update node
         * 
         * @param l String
         * @param r Index
         * @param v New character
         * @return String update node (str.update(l, r, v), i.e., l[r] = v)
         */
        std::shared_ptr<DAGNode> mkStrUpdate(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // str.update(l, r, v)
        
        /**
         * @brief Create a string replace node
         * 
         * @param l String
         * @param r Substring to replace
         * @param v Replacement string
         * @return String replace node (str.replace(l, r, v))
         */
        std::shared_ptr<DAGNode> mkStrReplace(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // str.replace(l, r, v)
        
        /**
         * @brief Create a string replace-all node
         * 
         * @param l String
         * @param r Substring to replace
         * @param v Replacement string
         * @return String replace-all node (str.replace_all(l, r, v))
         */
        std::shared_ptr<DAGNode> mkStrReplaceAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // str.replace_all(l, r, v)
        
        /**
         * @brief Create a string replace-regex node
         * 
         * @param l String
         * @param r Regular expression
         * @param v Replacement string
         * @return String replace-regex node (str.replace_re(l, r, v))
         */
        std::shared_ptr<DAGNode> mkStrReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // str.replace_re(l, r, v)
        
        /**
         * @brief Create a string replace-regex-all node
         * 
         * @param l String
         * @param r Regular expression
         * @param v Replacement string
         * @return String replace-regex-all node (str.replace_re_all(l, r, v))
         */
        std::shared_ptr<DAGNode> mkStrReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // str.replace_re_all(l, r, v)
        
        /**
         * @brief Create a string indexof-regex node
         * 
         * @param l String
         * @param r Regular expression
         * @return String indexof-regex node (str.indexof_re(l, r))
         */
        std::shared_ptr<DAGNode> mkStrIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> i); // str.indexof_re(l, r, i)

        /**
         * @brief Create a string to-lower node
         * 
         * @param param String
         * @return String to-lower node (str.to_lower(param))
         */
        std::shared_ptr<DAGNode> mkStrToLower(std::shared_ptr<DAGNode> param); // str.to_lower(param)
        
        /**
         * @brief Create a string to-upper node
         * 
         * @param param String
         * @return String to-upper node (str.to_upper(param))
         */
        std::shared_ptr<DAGNode> mkStrToUpper(std::shared_ptr<DAGNode> param); // str.to_upper(param)
        
        /**
         * @brief Create a string reverse node
         * 
         * @param param String
         * @return String reverse node (str.rev(param))
         */
        std::shared_ptr<DAGNode> mkStrRev(std::shared_ptr<DAGNode> param); // str.rev(param)
        
        /**
         * @brief Create a string split node
         * 
         * @param l String
         * @param r Delimiter
         * @return String split node (str.split(l, r))
         */
        std::shared_ptr<DAGNode> mkStrSplit(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.split(l, r)
        
        std::shared_ptr<DAGNode> mkStrSplitAt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.split_at(l, r, s)
        
        std::shared_ptr<DAGNode> mkStrSplitRest(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.split_rest(l, r, s)
        
        std::shared_ptr<DAGNode> mkStrNumSplits(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.num_splits(l, r)
        
        std::shared_ptr<DAGNode> mkStrSplitAtRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.split_at_re(l, r, s)
        
        std::shared_ptr<DAGNode> mkStrSplitRestRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // str.split_rest_re(l, r, s)
        
        std::shared_ptr<DAGNode> mkStrNumSplitsRe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.num_splits_re(l, r)
        
        // STRINGS COMP
        /**
         * @brief Create a string less-than node
         * 
         * @param l Left string
         * @param r Right string
         * @return String less-than node (str.<(l, r))
         */
        std::shared_ptr<DAGNode> mkStrLt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.<(l, r)
        
        /**
         * @brief Create a string less-than-or-equal node
         * 
         * @param l Left string
         * @param r Right string
         * @return String less-than-or-equal node (str.<=(l, r))
         */
        std::shared_ptr<DAGNode> mkStrLe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.<=(l, r)
        
        /**
         * @brief Create a string greater-than node
         * 
         * @param l Left string
         * @param r Right string
         * @return String greater-than node (str.>(l, r))
         */
        std::shared_ptr<DAGNode> mkStrGt(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.>(l, r)
        
        /**
         * @brief Create a string greater-than-or-equal node
         * 
         * @param l Left string
         * @param r Right string
         * @return String greater-than-or-equal node (str.>=(l, r))
         */
        std::shared_ptr<DAGNode> mkStrGe(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.>=(l, r)
        
        // STRINGS PROPERTIES
        /**
         * @brief Create a string in-regex check node
         * 
         * @param l String
         * @param r Regular expression
         * @return String in-regex check node (str.in_re(l, r))
         */
        std::shared_ptr<DAGNode> mkStrInReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.in_re(l, r)
        
        /**
         * @brief Create a string contains check node
         * 
         * @param l String
         * @param r Substring
         * @return String contains check node (str.contains(l, r))
         */
        std::shared_ptr<DAGNode> mkStrContains(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // str.contains(l, r)
        
        /**
         * @brief Create a string is-digit check node
         * 
         * @param param String
         * @return String is-digit check node (str.is_digit(param))
         */
        std::shared_ptr<DAGNode> mkStrIsDigit(std::shared_ptr<DAGNode> param); // str.is_digit(param)
        
        // STRINGS CONVERSION
        /**
         * @brief Create a string from-integer conversion node
         * 
         * @param param Integer
         * @return String from-integer conversion node (str.from_int(param))
         */
        std::shared_ptr<DAGNode> mkStrFromInt(std::shared_ptr<DAGNode> param); // str.from_int(param)
        
        /**
         * @brief Create a string to-integer conversion node
         * 
         * @note Returns -1 if the string does not represent a valid integer
         * 
         * @param param String
         * @return String to-integer conversion node (str.to_int(param))
         */
        std::shared_ptr<DAGNode> mkStrToInt(std::shared_ptr<DAGNode> param); // str.to_int(param)
        
        /**
         * @brief Create a string to-regex conversion node
         * 
         * @param param String
         * @return String to-regex conversion node (str.to_reg(param))
         */
        std::shared_ptr<DAGNode> mkStrToReg(std::shared_ptr<DAGNode> param); // str.to_reg(param)
        
        /**
         * @brief Create a string to-code conversion node
         * 
         * Creates a node that converts a string to its ASCII code.
         * 
         * @note Assumes the string has exactly one character
         * 
         * @param param String
         * @return String to-code conversion node (str.to_code(param))
         */
        std::shared_ptr<DAGNode> mkStrToCode(std::shared_ptr<DAGNode> param); // str.to_code(param) assci code
        
        /**
         * @brief Create a string from-code conversion node
         * 
         * Creates a node that converts an ASCII code to a string.
         * 
         * @param param ASCII code
         * @return String from-code conversion node (str.from_code(param))
         */
        std::shared_ptr<DAGNode> mkStrFromCode(std::shared_ptr<DAGNode> param); // str.from_code(param) assci code
        
        // STRINGS RE CONSTANTS
        /**
         * @brief Create a regex none node
         * 
         * Creates a regex node that matches nothing.
         * 
         * @return Regex none node (re.none)
         */
        std::shared_ptr<DAGNode> mkRegNone(); // re.none
        
        /**
         * @brief Create a regex all node
         * 
         * Creates a regex node that matches any string.
         * 
         * @return Regex all node (re.all)
         */
        std::shared_ptr<DAGNode> mkRegAll(); // re.all
        
        /**
         * @brief Create a regex allchar node
         * 
         * Creates a regex node that matches any single character.
         * 
         * @return Regex allchar node (re.allchar)
         */
        std::shared_ptr<DAGNode> mkRegAllChar(); // re.allchar
        
        // STRINGS RE COMMON OPERATORS
        /**
         * @brief Create a regex concatenation node
         * 
         * Creates a regex concatenation node that matches the concatenation of patterns.
         * 
         * @param params Regex patterns
         * @return Regex concatenation node (re.++(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkRegConcat(const std::vector<std::shared_ptr<DAGNode>> &params); // re.++(l, r, ...)
        
        /**
         * @brief Create a regex union node
         * 
         * Creates a regex union node that matches any of the patterns.
         * 
         * @param params Regex patterns
         * @return Regex union node (re.union(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkRegUnion(const std::vector<std::shared_ptr<DAGNode>> &params); // re.union(l, r, ...)
        
        /**
         * @brief Create a regex intersection node
         * 
         * Creates a regex intersection node that matches strings that match all patterns.
         * 
         * @param params Regex patterns
         * @return Regex intersection node (re.inter(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkRegInter(const std::vector<std::shared_ptr<DAGNode>> &params); // re.inter(l, r, ...)
        
        /**
         * @brief Create a regex difference node
         * 
         * Creates a regex difference node that matches strings matching the first pattern but not subsequent patterns.
         * 
         * @param params Regex patterns
         * @return Regex difference node (re.diff(l, r, ...))
         */
        std::shared_ptr<DAGNode> mkRegDiff(const std::vector<std::shared_ptr<DAGNode>> &params); // re.diff(l, r, ...)
        
        /**
         * @brief Create a regex star node
         * 
         * Creates a regex star node that matches zero or more occurrences of the pattern.
         * 
         * @param param Regex pattern
         * @return Regex star node (re.*(param), i.e., param*)
         */
        std::shared_ptr<DAGNode> mkRegStar(std::shared_ptr<DAGNode> param); // re.*(param)
        
        /**
         * @brief Create a regex plus node
         * 
         * Creates a regex plus node that matches one or more occurrences of the pattern.
         * 
         * @param param Regex pattern
         * @return Regex plus node (re.+(param), i.e., param+)
         */
        std::shared_ptr<DAGNode> mkRegPlus(std::shared_ptr<DAGNode> param); // param+
        
        /**
         * @brief Create a regex option node
         * 
         * Creates a regex option node that matches zero or one occurrence of the pattern.
         * 
         * @param param Regex pattern
         * @return Regex option node (re.?(param)/re.opt(param), i.e., param?)
         */
        std::shared_ptr<DAGNode> mkRegOpt(std::shared_ptr<DAGNode> param); // param?
        
        /**
         * @brief Create a regex range node
         * 
         * Creates a regex range node that matches characters in the specified range.
         * 
         * @param l Lower bound (inclusive)
         * @param r Upper bound (inclusive)
         * @return Regex range node (re.range(l, r), i.e., l..r)
         */
        std::shared_ptr<DAGNode> mkRegRange(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // l..r
        
        /**
         * @brief Create a regex repeat node
         * 
         * Creates a regex repeat node that matches exactly r occurrences of the pattern.
         * 
         * @param l Regex pattern
         * @param r Number of repetitions
         * @return Regex repeat node (re.^(n, l), i.e., l^n)
         */
        std::shared_ptr<DAGNode> mkRegRepeat(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // re.^(n, l)
        
        /**
         * @brief Create a regex loop node
         * 
         * Creates a regex loop node that matches between r and s occurrences of the pattern.
         * 
         * @param l Regex pattern
         * @param r Minimum number of repetitions
         * @param s Maximum number of repetitions
         * @return Regex loop node (re.loop(l, r, s), i.e., l{r,s})
         */
        std::shared_ptr<DAGNode> mkRegLoop(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> s); // l{r,s}
        
        /**
         * @brief Create a regex complement node
         * 
         * Creates a regex complement node that matches strings not matching the pattern.
         * 
         * @param param Regex pattern
         * @return Regex complement node (re.complement(param), i.e., ~param)
         */
        std::shared_ptr<DAGNode> mkRegComplement(std::shared_ptr<DAGNode> param); // ~param
        
        // STRINGS RE FUNCTIONS
        /**
         * @brief Create a string replace-regex node
         * 
         * Creates a node that replaces the first match of a regex pattern.
         * 
         * @param l String
         * @param r Regex pattern
         * @param v Replacement string
         * @return String replace-regex node (str.replace_re(l, r, v))
         */
        std::shared_ptr<DAGNode> mkReplaceReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace(l, r, v)
        
        /**
         * @brief Create a string replace-all-regex node
         * 
         * Creates a node that replaces all matches of a regex pattern.
         * 
         * @param l String
         * @param r Regex pattern
         * @param v Replacement string
         * @return String replace-all-regex node (str.replace_all_re(l, r, v))
         */
        std::shared_ptr<DAGNode> mkReplaceRegAll(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r, std::shared_ptr<DAGNode> v); // replace_all(l, r, v)
        
        /**
         * @brief Create a string index-of-regex node
         * 
         * Creates a node that returns the index of the first match of a regex pattern.
         * 
         * @param l String
         * @param r Regex pattern
         * @return String index-of-regex node (str.indexof(l, r))
         */
        std::shared_ptr<DAGNode> mkIndexofReg(std::shared_ptr<DAGNode> l, std::shared_ptr<DAGNode> r); // indexof(l, r)
        
        // INTERVAL
        /**
         * @brief Create a max node
         * 
         * @param params List of parameters
         * @return Max node (max(p1, p2, ...))
         */
        std::shared_ptr<DAGNode> mkMax(const std::vector<std::shared_ptr<DAGNode>> &params); // max(p1, p2, ...)
        
        /**
         * @brief Create a min node
         * 
         * @param params List of parameters
         * @return Min node (min(p1, p2, ...))
         */
        std::shared_ptr<DAGNode> mkMin(const std::vector<std::shared_ptr<DAGNode>> &params); // min(p1, p2, ...)

        // LET 
        /**
         * @brief Create a let node
         * 
         * @param params List of (key, value) pairs
         * @return Let node (let((key1, val1), (key2, val2), ...))
         */
        std::shared_ptr<DAGNode> mkLet(const std::vector<std::shared_ptr<DAGNode>> &params); // let((key1, val1), (key2, val2), ...)
        
        // QUANTIFIERS
        /**
         * @brief Create a quantifier variable node
         * 
         * @param name Variable name
         * @param sort Variable sort
         * @return Quantifier variable node (var1, sort1)
         */
        std::shared_ptr<DAGNode> mkQuantVar(const std::string& name, std::shared_ptr<Sort> sort);
        
        /**
         * @brief Create a forall node
         * 
         * @param params List of (variable, sort) pairs
         * @return Forall node (forall((var1, sort1), (var2, sort2), ..., body))
         */
        std::shared_ptr<DAGNode> mkForall(const std::vector<std::shared_ptr<DAGNode>> &params); // forall((var1, sort1), (var2, sort2), ..., body)
        
        /**
         * @brief Create an exists node
         * 
         * @param params List of (variable, sort) pairs
         * @return Exists node (exists((var1, sort1), (var2, sort2), ..., body))
         */
        std::shared_ptr<DAGNode> mkExists(const std::vector<std::shared_ptr<DAGNode>> &params); // exists((var1, sort1), (var2, sort2), ..., body)
        
        // FUNCTION
        /**
         * @brief Create a function application node
         * 
         * @param fun Function node
         * @param params List of parameters
         * @return Function application node (fun(p1, p2, ..., pn))
         */
        std::shared_ptr<DAGNode> mkApplyFunc(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> &params); // static apply function, only (f p1 p2 ... pn) without substitution
        

        // parse smt-lib2 file
        /**
         * @brief Parse an SMT-LIB2 file
         * 
         * Parses an SMT-LIB2 file and returns a boolean indicating success.
         * 
         * @param filename Path to the SMT-LIB2 file
         * @return Boolean indicating success
         */
        bool 	                 parseSmtlib2File(const std::string filename);

        // --- Incremental / sequential API ---

        /**
         * @brief Parse the next command from the current buffer.
         * @return The parsed Command object. type == CT_EOF if no more commands.
         */
        Command nextCommand();

        /**
         * @brief Push n scope levels.
         * @return true on success, false on error.
         */
        bool push(size_t n = 1);

        /**
         * @brief Pop n scope levels.
         * @return true on success, false on error.
         */
        bool pop(size_t n = 1);

        /** Get the current incremental push/pop depth. */
        size_t getScopeDepth() const { return context_.scope_stack_.size(); }

        /**
         * @brief Reset assertions (keep declarations and options).
         * @return true on success.
         */
        bool resetAssertions();

        /**
         * @brief Full reset (return to initial state).
         * @return true on success.
         */
        bool reset();

        /**
         * @brief Enable or disable command logging to the Script.
         */
        void setCommandLogging(bool enable) { command_logging_ = enable; }

        /**
         * @brief Get the accumulated command script.
         */
        const Script& getScript() const { return script_; }

        /**
         * @brief Get the arity of a node kind
         * 
         * @param k Node kind
         * @return Arity of the node kind
         */
        int                      getArity(NODE_KIND k) const;

        // aux functions
        /**
         * @brief Get the add operator for a sort
         * 
         * @param sort Sort
         * @return Add operator for the sort
         */ 
        NODE_KIND                getAddOp(std::shared_ptr<Sort> sort); // mk unique add 

        /**
         * @brief Get the opposite kind of a node kind
         * 
         * @param kind Node kind
         * @return Opposite kind of the node kind
         */
        NODE_KIND                getNegatedKind(NODE_KIND kind);

        /**
         * @brief Get the zero for a sort
         * 
         * @param sort Sort
         * @return Zero for the sort
         */
        std::shared_ptr<DAGNode> getZero(std::shared_ptr<Sort> sort); // mk unique zero
        
        // additional functions
        /**
         * @brief Substitute variables in an expression
         *
         * @note This function is used to substitute variables in an expression but not simplify the expression.
         * 
         * @param expr Expression to substitute
         * @param params Map of variable names to their corresponding values
         * @return Substituted expression
         */
        std::shared_ptr<DAGNode>                substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params);
        
        // apply function
        /**
         * @brief Apply a function to a list of parameters
         * 
         * @param fun Function node
         * @param params List of parameters
         * @return Applied function (fun(p1, p2, ..., pn))
         */
        std::shared_ptr<DAGNode>	            applyFun(std::shared_ptr<DAGNode> fun, const std::vector<std::shared_ptr<DAGNode>> & params);
        
        // negate an atom
        /**
         * @brief Negate a comparison atom
         * 
         * @note This function is used to negate a comparison atom (for example, negateComp(x = y) <=> x != y).
         * 
         * @param atom Comparison atom to negate
         * @return Negated comparison atom
         */
        std::shared_ptr<DAGNode>	            negateComp(std::shared_ptr<DAGNode> atom);

        // converse of a comparison atom
        /**
         * @brief Rewrite a comparison atom into its converse relation
         *
         * @note Swaps the operands while keeping the operator, i.e. the
         *       result is the CONVERSE of the input, not an equivalent form:
         *       converseComp(x < 3) = (3 < x), which means x > 3.
         *       Symmetric relations (=, distinct) are returned unchanged.
         *       For an equivalence-preserving rewrite use mirrorComp().
         *
         * @param atom Comparison atom to flip
         * @return Converse comparison atom
         */
        std::shared_ptr<DAGNode>	            converseComp(std::shared_ptr<DAGNode> atom);

        // mirror a comparison atom
        /**
         * @brief Rewrite a comparison atom into its mirrored equivalent form
         *
         * @note Swaps the operands AND flips the operator, so the result is
         *       logically EQUIVALENT to the input:
         *       mirrorComp(x < 3) = (3 > x), which still means x < 3.
         *       Atoms without a mirrored operator are returned unchanged.
         *
         * @param atom Comparison atom to mirror
         * @return Equivalent mirrored comparison atom
         */
        std::shared_ptr<DAGNode>	            mirrorComp(std::shared_ptr<DAGNode> atom);
        
        // evaluate: return true if the evaluation has changed the expression
        /**
         * @brief Set the precision for evaluation
         * 
         * @param precision Precision
         */
        void                                    setEvaluatePrecision(mpfr_prec_t precision);

        /**
         * @brief Get the precision for evaluation
         * 
         * @return Precision
         */
        mpfr_prec_t                             getEvaluatePrecision() const;

        /**
         * @brief Set the use floating for evaluation
         * 
         * @param use_floating Use floating
         */
        void                                    setEvaluateUseFloating(bool use_floating);

        /**
         * @brief Get the use floating for evaluation
         * 
         * @return Use floating
         */
        bool                                    getEvaluateUseFloating() const;

        /** When true, enforce stricter SMT-LIB FloatingPoint surface syntax (see GlobalOptions::strict_smtlib_fp). */
        void                                    setStrictSmtlib(bool strict);
        bool                                    getStrictSmtlib() const;

        /**
         * @brief Evaluate an expression
         * 
         * @note The model can be a partial model and this function will simplify the expression.
         * 
         * @param expr Expression to evaluate
         * @param model Model
         * @return Evaluated expression
         */
        std::shared_ptr<DAGNode>                evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model);
        

        /**
         * @brief Evaluate an expression
         * 
         * @param expr Expression to evaluate
         * @param model Model
         * @return Evaluated expression
         */
        std::shared_ptr<DAGNode>                evaluate(std::shared_ptr<DAGNode> expr, const Model &model);

        /**
         * @brief Evaluate an expression
         * 
         * @note The model can be a partial model and this function will simplify the expression.
         * 
         * @param expr Expression to evaluate
         * @param model Model
         * @param result Result
         * @return true if the evaluation has changed the expression, false otherwise
         */
        bool                                    evaluate(std::shared_ptr<DAGNode> expr, const std::shared_ptr<Model> &model, std::shared_ptr<DAGNode> &result);


        /**
         * @brief Check if an expression has some kinds
         * 
         * @param expr Expression to check
         * @param kinds Kinds to check
         * @return true if the expression has some kind, false otherwise
         */
        bool                                    hasSomeKinds(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& kinds);

        // type conversion
        /**
         * @brief Convert an expression to a real
         * 
         * @param expr Expression to convert
         * @return Real
         */
        Real                                    toReal(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Convert an expression to an integer
         * 
         * @param expr Expression to convert
         * @return Integer
         */
        Integer                                 toInt(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Check if an expression is zero
         * 
         * @param expr Expression to check
         * @return true if the expression is zero, false otherwise
         */
        bool                                    isZero(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Check if an expression is one
         * 
         * @param expr Expression to check
         * @return true if the expression is one, false otherwise
         */
        bool                                    isOne(std::shared_ptr<DAGNode> expr);

        // Format conversion
        /**
         * @brief Expand a let expression
         * 
         * @param expr Let expression to expand
         * @return Expanded expression
         */
        std::shared_ptr<DAGNode>                expandLet(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Collect atoms from an expression
         * 
         * @param expr Expression to collect atoms from
         * @param atoms Atoms (stored in a set)
         */
        void                                    collectAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms);

        /**
         * @brief Collect atoms from a vector of expressions
         * 
         * @param exprs Expressions to collect atoms from
         * @param atoms Atoms (stored in a set)
         */
        void                                    collectAtoms(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& atoms);   


        // collect ground atoms
        /**
         * @brief Collect ground atoms from an expression
         * 
         * @param expr Expression to collect ground atoms from
         * @param atoms Ground atoms (stored in a set)
         */
        void                                    collectGroundAtoms(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& atoms);

        /**
         * @brief Collect variables from a vector of expressions
         * 
         * @param exprs Expressions to collect variables from
         * @param vars Variables (stored in a set)
         */
        void                                    collectVars(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& vars);

        /**
         * @brief Collect variables from an expression
         * 
         * @param expr Expression to collect variables from
         * @param vars Variables (stored in a set)
         */
        void                                    collectVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars);

        /**
         * @brief Collect assignable variables from a vector of expressions
         * 
         * @param exprs Expressions to collect assignable variables from
         * @param vars Assignable variables (stored in a set)
         */
        void                                    collectAssignableVars(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& vars);

        /**
         * @brief Collect assignable variables from an expression
         * 
         * @param expr Expression to collect assignable variables from
         * @param vars Assignable variables (stored in a set)
         */
        void                                    collectAssignableVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars);

        /**
         * @brief Replace atoms in an expression
         * 
         * @param expr Expression to replace atoms in
         * @param atom_map Atom map (stored in a map)
         * @return Expression with replaced atoms
         */
        std::shared_ptr<DAGNode>                replaceAtoms(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map);

                /**
         * @brief Replace nodes in an expression (general node replacement)
         *  
         * @param expr Expression to replace nodes in
         * @param node_map Node map (stored in a map)
         * @return Expression with replaced nodes
         */
        std::shared_ptr<DAGNode>                replaceNodes(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& node_map);

        /**
         * @brief Convert an expression to Tseitin CNF
         * 
         * @param expr Expression to convert
         * @param clauses Clauses (stored in a vector)
         * @return Expression in Tseitin CNF
         */
        std::shared_ptr<DAGNode>                toTseitinCNF(std::shared_ptr<DAGNode> expr, std::vector<std::shared_ptr<DAGNode>>& clauses);

        /**
         * @brief Convert a vector of expressions to CNF
         * 
         * @param exprs Expressions to convert
         * @return Expressions in CNF
         */
        std::shared_ptr<DAGNode>                toCNF(std::vector<std::shared_ptr<DAGNode>> exprs);


        /**
         * @brief Check if an expression is in CNF
         * 
         * @param expr Expression to check
         * @return true if the expression is in CNF, false otherwise
         */
        bool                                    isCNF(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Check if a vector of expressions is in CNF
         * 
         * @param exprs Expressions to check
         * @return true if the expressions are in CNF, false otherwise
         */
        bool                                    isCNF(std::vector<std::shared_ptr<DAGNode>> exprs);

        /**
         * @brief Get the original atom from the CNF atom
         * 
         * @note If the bool_var is not a CNF atom, the function will return NodeManager::NULL_NODE.
         * 
         * @param bool_var Boolean variable
         * @return Original atom
         */
        std::shared_ptr<DAGNode>                getCNFAtom(std::shared_ptr<DAGNode> bool_var);

        /**
         * @brief Get the T-explanation of an expression
         * 
         * @note The same as getCNFAtom, but the function will return the original atom instead of the CNF atom.
         * 
         * @param expr Expression to get T-explanation from
         * @return T-explanation
         */
        std::shared_ptr<DAGNode>                getTExplanation(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Check if an expression is a T-abstraction
         * 
         * @param expr Expression to check
         * @return true if the expression is a T-abstraction, false otherwise
         */
        bool                                    isTAbstraction(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Get all CNF atoms from an expression
         * 
         * @param expr Expression to get CNF atoms from
         * @return CNF atoms
         */
        std::vector<std::shared_ptr<DAGNode>>   getCNFAtoms();

        /**
         * @brief Get the CNF variable from the original atom
         * 
         * @note If the atom is not a CNF variable, the function will return NodeManager::NULL_NODE.
         * 
         * @param atom Original atom
         * @return CNF variable
         */
        std::shared_ptr<DAGNode>                getCNFBoolVar(std::shared_ptr<DAGNode> atom);

        /**
         * @brief Get all CNF variables from an expression
         * 
         * @param expr Expression to get CNF variables from
         * @return CNF variables
         */
        std::vector<std::shared_ptr<DAGNode>>   getCNFBoolVars();

        /**
         * @brief Convert an expression to DNF
         * 
         * @param expr Expression to convert
         * @return Expression in DNF
         */
        std::shared_ptr<DAGNode>                toDNF(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Convert a vector of expressions to DNF
         * 
         * @param exprs Expressions to convert
         * @return Expressions in DNF
         */
        std::shared_ptr<DAGNode>                toDNF(std::vector<std::shared_ptr<DAGNode>> exprs);

        /**
         * @brief Convert an expression to NNF
         * 
         * @param expr Expression to convert
         * @return Expression in NNF
         */
        std::shared_ptr<DAGNode>                toNNF(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Convert a vector of expressions to NNF
         * 
         * @param exprs Expressions to convert
         * @return Expressions in NNF
         */
        std::shared_ptr<DAGNode>                toNNF(std::vector<std::shared_ptr<DAGNode>> exprs);


        /**
         * @brief Eliminate top level and
         * 
         * @param exprs Expressions to eliminate top level and
         * @return Expressions without top level and
         */
        bool                                    eliminateTopContinuousAnd(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs);

        /**
         * @brief Eliminate top level or
         * 
         * @param exprs Expressions to eliminate top level or
         * @return Expressions without top level or
         */
        bool                                    eliminateContinuousOr(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs);

        /**
         * @brief Eliminate top level redandancy
         * 
         * @param exprs Expressions to eliminate top level redandancy (continuous and, continuous or)
         * @return Expressions without top level redandancy
         */
        bool                                    eliminateTopRedandancy(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs);

        /**
         * @brief Normalize an expression
         * 
         * @note make the right hand side of the expression a constant, e.g. f(x) < g(x) -> f(x) - g(x) < 0
         *       If expr is a constraint, the function will traverse the children of the constraint and normalize each child.
         * 
         * @param expr Expression to normalize 
         * @return Normalized expression
         */
        std::shared_ptr<DAGNode>                arithNormalize(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Normalize a vector of expressions
         * 
         * @param exprs Expressions to normalize
         * @return Normalized expressions
         */
        std::vector<std::shared_ptr<DAGNode>>   arithNormalize(std::vector<std::shared_ptr<DAGNode>> exprs);

        /**
         * @brief Split an expression into a vector of expressions
         * 
         * @note E.g., split comparison into two inequalities, i.e., x != y -> x < y or x > y, x >= y -> x > y or x = y, etc.
         * 
         * @param expr Expression to split
         * @param op_set Set of node kinds to split
         * @return Vector of expressions
         */
        std::shared_ptr<DAGNode>                splitOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set);

        /**
         * @brief Binarize an expression
         * 
         * @note E.g., (= a b c) -> (and (= a b) (= a c))
         * 
         * @param expr Expression to binarize
         * @param op_set Set of node kinds to binarize
         * @return Binarized expression
         */
        std::shared_ptr<DAGNode>                binarizeOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set);

        /**
         * @brief Binarize a vector of expressions
         * 
         * @param exprs Expressions to binarize
         * @param op_set Set of node kinds to binarize
         * @return Binarized expressions
         */
        std::shared_ptr<DAGNode>                binarizeOp(std::vector<std::shared_ptr<DAGNode>> exprs, const std::unordered_set<NODE_KIND>& op_set);


        /**
         * @brief Binarize an expression
         * 
         * @note use a default set of node kinds to binarize, {=, !=, <=, >=, <, >}
         * 
         * @param expr Expression to binarize
         * @return Binarized expression
         */
        std::shared_ptr<DAGNode>                binarizeOp(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Binarize a vector of expressions
         * 
         * @note use a default set of node kinds to binarize, {=, !=, <=, >=, <, >}
         * 
         * @param exprs Expressions to binarize
         * @return Binarized expressions
         */
        std::shared_ptr<DAGNode>                binarizeOp(std::vector<std::shared_ptr<DAGNode>> exprs);

        /**
         * @brief Get the split lemmas
         * 
         * @note Return the split lemmas generated by splitOp last time.
         * 
         * @return Split lemmas
         */
        std::vector<std::shared_ptr<DAGNode>>   getSplitLemmas();

        /**
         * @brief Remove all the nodes in the expression
         * 
         * @param expr Expression to remove nodes from
         * @param nodes Nodes to remove
         * @return Expression with removed nodes
         */
        std::shared_ptr<DAGNode>                remove(std::shared_ptr<DAGNode> expr, const std::unordered_set<std::shared_ptr<DAGNode>>& nodes);


        /**
         * @brief Rename a node
         * 
         * @param expr Expression to rename
         * @param new_name New name
         * @return Expression with renamed node
         */
        std::shared_ptr<DAGNode>                rename(std::shared_ptr<DAGNode> expr, const std::string& new_name);

        // print
        /**
         * @brief Print an expression
         * 
         * @param expr Expression to print
         * @return String representation of the expression
         */
        std::string                             toString(std::shared_ptr<DAGNode> expr);
        
        /**
         * @brief Print a node kind
         * 
         * @param kind Node kind to print
         * @return String representation of the node kind
         */
        std::string                             toString(const NODE_KIND& kind);

        /**
         * @brief Print a sort
         * 
         * @param sort Sort to print
         * @return String representation of the sort
         */
        std::string                             toString(std::shared_ptr<Sort> sort);

        /**
         * @brief Print the options
         * 
         * @return String representation of the options
         */
        std::string                             optionToString();

        /**
         * @brief Dump the SMT2 representation of the parsed expressions
         * 
         * @return String representation of the SMT2
         */
        std::string                             dumpSMT2();

        /**
         * @brief Dump the SMT2 representation of the parsed expressions to a file
         * 
         * @param filename Filename to save the SMT2
         * @return Filename
         */
        std::string                             dumpSMT2(const std::string& filename);

        /**
         * @brief Remove functions by name
         * 
         * @param funcNames Vector of function names to remove
         * @return Number of functions actually removed
         */
        size_t                                  removeFuns(const std::vector<std::string>& funcNames);

        /**
         * @brief ensure the expression is a number
         * 
         * @param expr Expression to ensure
         */
        void                                    ensureNumberValue(std::shared_ptr<DAGNode> expr);

        /**
         * @brief Parse a model
         * 
         * @param model Model to parse
         * @return Model
         */
        ModelPtr                                parseModel(const std::string& model, bool only_declared = false);

        /**
         * @brief Create a new empty model with declared variables
         * 
         * @return New empty model
         */
        ModelPtr                                newEmptyModel();
        
    private:
        friend struct EvalAccess;   // grants eval_dispatch.cpp access to evaluateXxx

        // parse smt-lib2 file
        std::string	                            getSymbol();
        void 		                            scanToNextSymbol();
        void		                            parseLpar();
        void 		                            parseRpar();
        void		                            skipToRpar();
        // Helper for parseModel: parse symbol name that may start with invalid characters
        std::string                             parseModelSymbolName();
        std::string                             peekSymbol();


        CMD_TYPE	                            parseCommand();
        KEYWORD                                 parseKeyword();
        std::shared_ptr<Sort>	                parseSort();
        std::shared_ptr<DAGNode>		        parseExpr();
        std::shared_ptr<DAGNode>		        parseConstFunc(const std::string& s);
        std::shared_ptr<DAGNode>		        parseOper(const std::string& s, const std::vector<std::shared_ptr<DAGNode>>& func_args, const std::vector<std::shared_ptr<DAGNode>> &oper_params, bool indexed_under_score = false);
        std::vector<std::shared_ptr<DAGNode>>	parseParams();
        std::shared_ptr<DAGNode>		        parsePreservingLet();
        std::shared_ptr<DAGNode>		        parseLet();
        std::shared_ptr<DAGNode>		        mkLetBindVar(const std::string& name, const std::shared_ptr<DAGNode>& expr);
        std::shared_ptr<DAGNode>		        mkLetBindVarList(const std::vector<std::shared_ptr<DAGNode>>& bind_vars);
        std::shared_ptr<DAGNode>		        mkLetChain(const std::vector<std::shared_ptr<DAGNode>>& bind_var_lists, const std::shared_ptr<DAGNode>& body);
        std::string                             parseGroup();
        std::string                             parseWeight();
        std::shared_ptr<DAGNode>                parseQuant(const std::string& type);
        std::shared_ptr<DAGNode>                parseMatch();
        /** Parse one <datatype_dec> ((ctor...)...) after its opening '('; register ctors/selectors/testers on @p dt_sort. */
        void                                    defineDatatypeConstructors(const std::shared_ptr<Sort>& dt_sort);
        /** Reads an optional `(par (X ...)` wrapper before a datatype's
         *  constructor list and returns the parameter names, empty when the body
         *  is not parametric. Leaves the buffer where the plain form would. */
        std::vector<std::string>                parseDatatypeParams();
        /** Sort-parameter binding for an application of a parametric datatype's
         *  member. See the definition for how selectors, testers and
         *  constructors each determine it. */
        void                                    dtParamBinding(const std::shared_ptr<DAGNode>& fun,
                                                    const std::vector<std::shared_ptr<DAGNode>>& params,
                                                    std::unordered_map<std::string, std::shared_ptr<Sort>>& out);
    public:
        /** The result sort an application of @p fun should carry, with a
         *  parametric datatype's parameters substituted. Returns the declared
         *  sort unchanged for everything else. */
        std::shared_ptr<Sort>                   dtAppliedSort(const std::shared_ptr<DAGNode>& fun,
                                                    const std::vector<std::shared_ptr<DAGNode>>& params);
        /** A parametric datatype's sort parameters, in declaration order; empty
         *  for an ordinary one. A Sort records only the arity, so a caller that
         *  needs the names has to ask here. */
        std::vector<std::string>                datatypeParams(const std::string& dt) const {
            const auto it = datatype_params_.find(dt);
            return it == datatype_params_.end() ? std::vector<std::string>{} : it->second;
        }
        /** Record a parametric datatype's parameter names, for a caller that
         *  builds a model programmatically rather than parsing a script. */
        void                                    setDatatypeParams(const std::string& dt,
                                                    const std::vector<std::string>& p) {
            datatype_params_[dt] = p;
        }
    private:
        /** Sort-parameter names per parametric datatype, in declaration order.
         *  A Sort records its ARITY and not what its parameters were called, so
         *  dumpSMT2 could not otherwise write the `par` form back. */
        std::unordered_map<std::string, std::vector<std::string>> datatype_params_;
        
        // parse optimization
        // single_opt = (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>]) 
        //            | (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        void                                    parseAssertSoft();
        // (maximize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>              parseMaximize();
        // (minimize <expr> [:comp <symbol>] [:epsilon <symbol>] [:M <symbol>] [:id <symbol>])
        std::shared_ptr<Objective>              parseMinimize();
        // (maxsat <expr> [:id])
        std::shared_ptr<Objective>              parseMaxsat();
        // (minsat <expr> [:id])
        std::shared_ptr<Objective>              parseMinsat();
        std::shared_ptr<Objective>              parseSingleObj(const OPT_KIND& opt_type);
        std::shared_ptr<Objective>              parseMultiObj(const OPT_KIND& opt_type);
        // (define-objective <symbol> signle_opt [:id <symbol>])
        std::shared_ptr<Objective>              parseDefObj();
        // (lex-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>              parseLexOpt();
        // (pareto-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>              parseParetoOpt();
        // (box-optimize (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>              parseBoxOpt();
        // (minmax (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>              parseMinmax();
        // (maxmin (<symbol>+) [:id <symbol>])
        std::shared_ptr<Objective>              parseMaxmin();
        // (optimize (<symbol>+) [:id <symbol>] [:opt_kind <symbol>])
        std::shared_ptr<Objective>              parseOptimize();
        KEYWORD                                 attemptParseKeywords();

        
        // auxilary functions
        
        std::shared_ptr<DAGNode>                mkInternalOper(const std::shared_ptr<Sort>& sort, const NODE_KIND& t, const std::vector<std::shared_ptr<DAGNode>>& p);

        std::shared_ptr<DAGNode>	            bindLetVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>	            bindFunVar(const std::string &key, std::shared_ptr<DAGNode> expr);
        // conversion
        std::shared_ptr<DAGNode>                substitute(std::shared_ptr<DAGNode> expr, std::unordered_map<std::string, std::shared_ptr<DAGNode>> &params, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> & visited);
        std::shared_ptr<DAGNode>	            applyFunPostOrder(std::shared_ptr<DAGNode> node, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> &params);
        
        std::shared_ptr<DAGNode>                replaceAtoms(std::shared_ptr<DAGNode> expr, 
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map, 
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, 
                                                            bool& is_changed);
        std::shared_ptr<DAGNode>                replaceNodes(std::shared_ptr<DAGNode> expr, 
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& node_map, 
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, 
                                                            bool& is_changed);
        std::shared_ptr<DAGNode>                toCNF(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toTseitinCNF(std::shared_ptr<DAGNode> expr, 
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, 
                                                            std::vector<std::shared_ptr<DAGNode>>& clauses);
        // encode a formula in asserted (top-level, positive) position without a
        // Tseitin variable for its root connective; see conv_parser.cpp
        void                                    assertTopCNF(std::shared_ptr<DAGNode> expr,
                                                            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited,
                                                            std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinXor(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinEq(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toTseitinDistinct(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses);
        std::shared_ptr<DAGNode>                toDNFEliminateAll(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                toDNFEliminateAll(std::shared_ptr<DAGNode> expr,
                                                                   std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited,
                                                                   bool& is_changed);
        std::shared_ptr<DAGNode>                toDNFEliminateXOR(const std::vector<std::shared_ptr<DAGNode>>& children);
        std::shared_ptr<DAGNode>                toDNFEliminateEq(const std::vector<std::shared_ptr<DAGNode>>& children);
        std::shared_ptr<DAGNode>                toDNFEliminateDistinct(const std::vector<std::shared_ptr<DAGNode>>& children);

        std::shared_ptr<DAGNode>                applyDNFDistributiveLaw(std::shared_ptr<DAGNode> expr);
        std::shared_ptr<DAGNode>                applyDNFDistributiveLawRec(std::shared_ptr<DAGNode> expr,
                                                                         std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited);
        std::shared_ptr<DAGNode>                flattenDNF(std::shared_ptr<DAGNode> expr);
        
        std::shared_ptr<DAGNode>                toNNF(std::shared_ptr<DAGNode> expr, bool is_not);

        std::shared_ptr<DAGNode>                arithNormalize(std::shared_ptr<DAGNode> expr, bool& is_changed);
        
        // Array simplification functions
        // Structure to represent a store chain
        struct StoreChain {
            std::shared_ptr<DAGNode> base;
            std::vector<std::pair<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>> updates; // (index, value) pairs, oldest -> newest
        };
        
        // Collect store chain from an array term
        StoreChain                              collectStoreChain(std::shared_ptr<DAGNode> arrayTerm);
        
        // Canonicalize an array to canonical form (base, writes)
        ArrayCanonicalForm                      canonicalizeArray(std::shared_ptr<DAGNode> array);
        
        // Check if two arrays are equal using canonical form
        bool                                    areArraysEqual(const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b);
        
        // Check if two DT ground values are structurally equal
        bool                                    areDtValuesEqual(const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b);
        
        // Check if an array contains variables (that prevent equality determination)
        bool                                    arrayContainsVar(const std::shared_ptr<DAGNode>& array);
        
        // Rewrite select(store(...), index) to value or select(base, index)
        std::shared_ptr<DAGNode>                rewriteSelect(std::shared_ptr<DAGNode> selectNode);
        
        // Normalize store chain: merge duplicate indices, fix order
        std::shared_ptr<DAGNode>                normalizeStoreChain(std::shared_ptr<DAGNode> arrayTerm);
        
        // Main array simplification entry point
        std::shared_ptr<DAGNode>                simplifyArray(std::shared_ptr<DAGNode> node);
        
        // Check if two nodes are definitely equal (for index comparison)
        bool                                    areDefinitelyEqual(const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b);
        
        std::shared_ptr<DAGNode>                splitOp(std::shared_ptr<DAGNode> expr, 
                                                        const std::unordered_set<NODE_KIND>& op_set, 
                                                        bool& is_changed, 
                                                        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited);
        std::shared_ptr<DAGNode>                binarizeOp(std::shared_ptr<DAGNode> expr, 
                                                        const std::unordered_set<NODE_KIND>& op_set, 
                                                        bool& is_changed, 
                                                        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited);
        
        std::shared_ptr<DAGNode>                remove(std::shared_ptr<DAGNode> expr, const std::unordered_set<std::shared_ptr<DAGNode>>& nodes, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited);
        
        //errors & warnings
        // mk errror node
        std::shared_ptr<DAGNode>	            mkErr(const ERROR_TYPE t);
        // error/warning information
        void 		err_all(const ERROR_TYPE e, const std::string s = "", const size_t ln = 0) const;
        void 		err_all(const std::shared_ptr<DAGNode> e, const std::string s = "", const size_t ln = 0) const;

        void 		err_unexp_eof() const;
        void 		err_sym_mis(const std::string mis, const size_t ln) const;
        void 		err_sym_mis(const std::string mis, const std::string nm, const size_t ln) const;
        void 		err_unkwn_sym(const std::string nm, const size_t ln) const;
        void 		err_param_mis(const std::string nm, const size_t ln) const;
        void 		err_param_nbool(const std::string nm, const size_t ln) const;
        void 		err_param_nnum(const std::string nm, const size_t ln) const;
        void 		err_param_nsame(const std::string nm, const size_t ln) const;
        void 		err_logic(const std::string nm, const size_t ln) const;
        void 		err_mul_decl(const std::string nm, const size_t ln) const;
        void 		err_mul_def(const std::string nm, const size_t ln) const;
        void 		err_zero_divisor(const size_t ln) const;
        void        err_arity_mis(const std::string nm, const size_t ln) const;
        void        err_keyword(const std::string nm, const size_t ln) const;
        void        err_type_mis(const std::string nm, const size_t ln) const;
        void        err_neg_param(const size_t ln) const;

        void		err_open_file(const std::string) const;

        void 		warn_cmd_nsup(const std::string nm, const size_t ln) const;
        /** Reports what a `:named` annotation displaced; silent when it displaced nothing. */
        void        warn_named_displaced(const NameAssertionOutcome& outcome, const std::string& name, const size_t ln) const;

        // collect atoms
        void        collectAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms, std::unordered_set<std::shared_ptr<DAGNode>>& visited);
        void        collectGroundAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms, std::unordered_set<std::shared_ptr<DAGNode>>& visited);
        void        collectVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars, std::unordered_set<std::shared_ptr<DAGNode>>& visited);
        void        collectAssignableVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars, std::unordered_set<std::shared_ptr<DAGNode>>& visited);
        // evaluate functions
        bool		evaluateSimpleOp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result, NODE_KIND op);
        bool		evaluateAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateImpl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDistinct(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIte(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDivInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDivReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);   
        bool		evaluateMod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluatePow(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluatePow2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSafeSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCeil(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFloor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRound(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateExp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLn(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLog(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLb(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateTan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCsc(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSec(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsec(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcsc(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtan(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateTanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateCsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsinh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcosh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtanh(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAsech(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcsch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAcoth(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateAtan2(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsDivisible(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsPrime(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsEven(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateIsOdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateGcd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLcm(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFact(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNot(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAnd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvOr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvXor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNand(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvXnor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvComp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSdiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSrem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSmod(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvShl(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvLshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvAshr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvUge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSlt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSle(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSgt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSge(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvToNat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvNatToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvIntToBv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvExtract(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvZeroExt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvSignExt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvRotLeft(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateBvRotRight(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpAbs(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpAdd(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpSub(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMul(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpDiv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpFma(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpSqrt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpRem(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpRoundToIntegral(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpEq(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToUbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToSbv(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpToReal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToFp(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateToFpUnsigned(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsSubnormal(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsZero(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsInf(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNaN(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsNeg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateFpIsPos(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateSelect(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStore(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateConstArray(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLen(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSubstr(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrPrefixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSuffixof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrIndexof(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrCharat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrUpdate(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrReplace(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrReplaceAll(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToLower(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToUpper(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrRev(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrLe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrGt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrGe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrInReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrContains(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrIsDigit(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrFromInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToInt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToReg(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrToCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrFromCode(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegConcat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegUnion(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegInter(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegDiff(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegStar(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegPlus(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegOpt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegRange(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegRepeat(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateRegComplement(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateApplyFun(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateUFApply(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDtConstructor(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDtSelector(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateDtTester(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateMatch(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateLet(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool        evaluateMax(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool        evaluateMin(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplitAt(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplitRest(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrNumSplits(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplitAtRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrSplitRestRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
        bool		evaluateStrNumSplitsRe(const std::shared_ptr<DAGNode>& expr, const std::shared_ptr<Model>& model, std::shared_ptr<DAGNode> &result);
    };


    // smart pointer
    typedef std::shared_ptr<Parser> ParserPtr;
    ParserPtr newParser();
    ParserPtr newParser(const std::string& filename);
}
#endif
