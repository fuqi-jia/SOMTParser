/* -*- Header -*-
 *
 * The Sort Class
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

#ifndef _SORT_H
#define _SORT_H

#include "somtparser/core/kind.h"
#include "somtparser/core/asserting.h"

#include <cstdint>
#include <vector>
#include <string>
#include <memory>
#include <unordered_map>
#include <functional>

namespace SOMTParser{
    
    // supported const/variable types
    enum class SORT_KIND {
        SK_NULL=0, SK_UNKNOWN, SK_BOOL, SK_INT, SK_REAL, SK_BV, SK_FP, SK_STR, SK_ARRAY, SK_DATATYPE, SK_SET, SK_RELATION, SK_BAG, SK_SEQ,
        SK_TUPLE, // (Tuple T1 ... Tn) — ported from the SMTStabilizer fork
        SK_UF,
        SK_REG, // regular expression
        SK_EXT, // extended real
        SK_RAT, // rational number
        SK_NAT, // natural number
        SK_ALGEBRAIC, // algebraic number
        SK_TRANSCENDENTAL, // transcendental number
        SK_RAND, // random number
        SK_INTOREAL, // int or real, for constant
        SK_DEC, // declare-sort 
        SK_DEF, // define-sort
        SK_ROUNDING_MODE // rounding mode for floating point operations
    };

    class Sort{
    public:
        SORT_KIND kind;
        std::string name;
        size_t arity;
        std::vector<std::shared_ptr<Sort>> children;

        // Datatype constructor/selector information (non-null only when kind == SK_DATATYPE)
        struct DtSelector {
            std::string name;
            std::shared_ptr<Sort> sort;
        };
        struct DtConstructor {
            std::string name;
            std::vector<DtSelector> selectors;
        };
        std::shared_ptr<std::vector<DtConstructor>> dt_constructors; // nullptr if not DT
        Sort(SORT_KIND kind, std::string name, size_t arity, std::vector<std::shared_ptr<Sort>> children): kind(kind), name(name), arity(arity), children(children) {}
        Sort(SORT_KIND kind, std::string name, size_t arity): kind(kind), name(name), arity(arity) {}
        Sort(SORT_KIND kind, std::string name): kind(kind), name(name), arity(0) {}
        Sort(SORT_KIND kind): kind(kind), name(""), arity(0) {}
        Sort(std::string name): kind(SORT_KIND::SK_UNKNOWN), name(name), arity(0) {}
        Sort(): kind(SORT_KIND::SK_UNKNOWN), name(""), arity(0) {}
        Sort(const Sort& other): kind(other.kind), name(other.name), arity(other.arity), children(other.children), dt_constructors(other.dt_constructors) {}


        // check the type of the sort
        bool isNull() const { return kind == SORT_KIND::SK_NULL; }
        bool isUnknown() const { return kind == SORT_KIND::SK_UNKNOWN; }
        bool isBool() const { return kind == SORT_KIND::SK_BOOL; }
        // it is an integer but can also be a real
        bool isIntOrReal() const { return kind == SORT_KIND::SK_INTOREAL; }
        bool isInt() const { return kind == SORT_KIND::SK_INT; }
        bool isReal() const { return kind == SORT_KIND::SK_REAL; }
        bool isAlgebraic() const { return kind == SORT_KIND::SK_ALGEBRAIC; }
        bool isTranscendental() const { return kind == SORT_KIND::SK_TRANSCENDENTAL; }
        bool isBv() const { return kind == SORT_KIND::SK_BV; }
        bool isFp() const { return kind == SORT_KIND::SK_FP; }
        bool isStr() const { return kind == SORT_KIND::SK_STR; }
        bool isReg() const { return kind == SORT_KIND::SK_REG; }
        bool isExt() const { return kind == SORT_KIND::SK_EXT; }
        bool isArray() const { return kind == SORT_KIND::SK_ARRAY; }
        bool isDatatype() const { return kind == SORT_KIND::SK_DATATYPE; }
        bool isSet() const { return kind == SORT_KIND::SK_SET; }
        bool isRelation() const { return kind == SORT_KIND::SK_RELATION; }
        bool isBag() const { return kind == SORT_KIND::SK_BAG; }
        bool isSeq() const { return kind == SORT_KIND::SK_SEQ; }
        bool isTuple() const { return kind == SORT_KIND::SK_TUPLE; }
        size_t getChildrenSize() const { return children.size(); }
        std::shared_ptr<Sort> getChild(size_t i) const {
            condAssert(i < children.size(), "Sort::getChild: index out of range");
            return children[i];
        }
        bool isUF() const { return kind == SORT_KIND::SK_UF; }
        bool isNat() const { return kind == SORT_KIND::SK_NAT; }
        bool isRand() const { return kind == SORT_KIND::SK_RAND; }
        bool isDec() const { return kind == SORT_KIND::SK_DEC; }
        bool isDef() const { return kind == SORT_KIND::SK_DEF; }
        bool isRoundingMode() const { return kind == SORT_KIND::SK_ROUNDING_MODE; }

        // Datatype accessors
        bool hasDtConstructors() const { return dt_constructors != nullptr && !dt_constructors->empty(); }

        const std::vector<DtConstructor>& getDtConstructors() const {
            static const std::vector<DtConstructor> empty;
            return dt_constructors ? *dt_constructors : empty;
        }

        /// Find a constructor by name. Returns nullptr if not found.
        const DtConstructor* getDtConstructorByName(const std::string& ctor_name) const {
            if(!dt_constructors) return nullptr;
            for(const auto& c : *dt_constructors)
                if(c.name == ctor_name) return &c;
            return nullptr;
        }

        /// Check if the given name is a constructor of this datatype.
        bool hasDtConstructor(const std::string& ctor_name) const {
            return getDtConstructorByName(ctor_name) != nullptr;
        }

        /// Check if the given name is a selector of any constructor in this datatype.
        bool hasDtSelector(const std::string& sel_name) const {
            if(!dt_constructors) return false;
            for(const auto& c : *dt_constructors)
                for(const auto& s : c.selectors)
                    if(s.name == sel_name) return true;
            return false;
        }

        /// Check if the given name is a tester (is-<ctor>) of this datatype.
        bool hasDtTester(const std::string& tester_name) const {
            if(!dt_constructors) return false;
            if(tester_name.size() <= 3 || tester_name.rfind("is-", 0) != 0) return false;
            std::string ctor_name = tester_name.substr(3);
            return hasDtConstructor(ctor_name);
        }

        // compare two sorts
        bool operator==(const Sort& other) const {
            // same sort name and arity -- and, for a sort constructor applied
            // to arguments, the same arguments.
            //
            // `(declare-sort P 1)` makes P a sort CONSTRUCTOR, so `(P Int)` and
            // `(P Bool)` are two sorts, exactly as `(Array Int Int)` and
            // `(Array Int Bool)` are. parseSort already instantiates them --
            // it clones the declared sort and fills `children` with the
            // arguments -- and this comparison then ignored `children` and
            // reported the two equal. `(= x y)` across them type-checked, so a
            // script the standard forbids parsed and translated with no
            // diagnostic. The array and set branches below compare their
            // children for this reason; a declared constructor needs it too.
            //
            // A PARAMETRIC DATATYPE needs the same treatment, for the same
            // reason and with the same consequence. `(declare-datatypes ((L 1))
            // ((par (X) ...)))` makes L a sort constructor, so `(L Int)` and
            // `(L Bool)` are two sorts; comparing by name alone let a value of
            // one be used where the other was declared. An arity-0 datatype has
            // no children and is unaffected.
            if((isDef() || isDec() || isDatatype())
               && (other.isDef() || other.isDec() || other.isDatatype())
               && name == other.name && arity == other.arity){
                if(children.size() != other.children.size()) return false;
                for(size_t i = 0; i < children.size(); i++){
                    if(!children[i] || !other.children[i]){
                        if(children[i] != other.children[i]) return false;
                        continue;
                    }
                    if(!(*children[i] == *other.children[i])) return false;
                }
                return true;
            }

            // int or real
            if((isInt() && other.isIntOrReal()) || (isIntOrReal() && other.isInt())){
                return true;
            }
            else if((isReal() && other.isIntOrReal()) || (isIntOrReal() && other.isReal())){
                return true;
            }

            // floating point
            else if(isFp() && other.isFp()){
                // For floating point types, compare exponent and significand widths
                return getExponentWidth() == other.getExponentWidth() &&
                    getSignificandWidth() == other.getSignificandWidth();
            }

            // bit-vectors: widths live in children, not in name/arity
            else if(isBv() && other.isBv()){
                return getBitWidth() == other.getBitWidth();
            }

            // arrays: compare index and element sorts recursively
            else if(isArray() && other.isArray()){
                if(children.size() != other.children.size()){
                    return false;
                }
                for(size_t i = 0; i < children.size(); i++){
                    if(!children[i] || !other.children[i]){
                        if(children[i] != other.children[i]) return false;
                        continue;
                    }
                    if(!(*children[i] == *other.children[i])) return false;
                }
                return true;
            }

            // other sorts
            else{
                return kind == other.kind && name == other.name && arity == other.arity;
            }
        }
        bool operator!=(const Sort& other) const {
            return !(*this == other);
        }

        // print the sort
        std::string toString() const {
            switch (kind) {
                case SORT_KIND::SK_BOOL: return "Bool";
                case SORT_KIND::SK_INT: return "Int";
                case SORT_KIND::SK_REAL: return "Real";
                case SORT_KIND::SK_BV:
                    return "(_ BitVec " + std::to_string(children[0]->arity) + ")";
                case SORT_KIND::SK_FP:
                    return "(_ FloatingPoint " + std::to_string(children[0]->arity) + " " + std::to_string(children[1]->arity) + ")";
                case SORT_KIND::SK_STR: return "String";
                case SORT_KIND::SK_ARRAY: return "(Array " + children[0]->toString() + " " + children[1]->toString() + ")";
                // A PARAMETRIC datatype applied to arguments must print them:
                // `(L X)` is not `L`. SK_DEC below already does this, and a
                // datatype sort constructor was left returning its bare name --
                // so `(tl (L X))` dumped as `(tl L)`, a constructor at the wrong
                // arity, which nothing else reads.
                case SORT_KIND::SK_DATATYPE: {
                    if(name.empty()) return "Datatype";
                    if(children.empty()) return name;
                    std::string s = "(" + name;
                    for(const auto& ch : children) s += " " + (ch ? ch->toString() : "?");
                    return s + ")";
                }
                case SORT_KIND::SK_SET: return "Set";
                case SORT_KIND::SK_RELATION: return "Relation";
                case SORT_KIND::SK_BAG: return "Bag";
                case SORT_KIND::SK_SEQ: return "Sequence";
                case SORT_KIND::SK_TUPLE: {
                    // (Tuple T1 ... Tn); the nullary tuple sort is UnitTuple.
                    if(children.empty()) return "UnitTuple";
                    std::string s = "(Tuple";
                    for(const auto& ch : children) s += " " + ch->toString();
                    return s + ")";
                }
                case SORT_KIND::SK_UF: return "UF";
                // The regular-expression sort is spelled RegLan in SMT-LIB;
                // base_parser reads that spelling, so printing anything else
                // made our own output unparsable by us.
                case SORT_KIND::SK_REG: return "RegLan";
                case SORT_KIND::SK_EXT: return "ExtReal";
                case SORT_KIND::SK_NAT: return "Natural";
                case SORT_KIND::SK_RAND: return "Random";
                case SORT_KIND::SK_INTOREAL: return "IntOrReal";
                case SORT_KIND::SK_ALGEBRAIC: return "Algebraic";
                case SORT_KIND::SK_TRANSCENDENTAL: return "Transcendental";
                // An applied sort constructor prints WITH its arguments.
                // Printing the bare name emitted `(declare-fun x () P)` for a P
                // declared at arity 1 -- a sort constructor used with no
                // arguments, which this parser happens to read back and no
                // other tool accepts.
                case SORT_KIND::SK_DEC:
                case SORT_KIND::SK_DEF: {
                    if(children.empty()) return name;
                    std::string s = "(" + name;
                    for(const auto& ch : children) s += " " + (ch ? ch->toString() : "?");
                    return s + ")";
                }
                case SORT_KIND::SK_ROUNDING_MODE: return "RoundingMode";
                default: return "Unknown";
            }
        }

        size_t getBitWidth() const {
            condAssert(kind == SORT_KIND::SK_BV, "Cannot get bit width of non-bitvector sort");
            condAssert(children.size() >= 1 && children[0], "Malformed bit-vector sort: missing width");
            return children[0]->arity;
        }

        /** SMT-LIB exponent field width `e` for `(_ FloatingPoint e s)`. Stored as `children[0]->arity`; well-formed FP sorts come from `SortManager::createFPSort` or static `FLOAT*` sorts. */
        size_t getExponentWidth() const {
            condAssert(kind == SORT_KIND::SK_FP, "Cannot get exponent width of non-floating-point sort");
            condAssert(children.size() >= 2 && children[0], "Malformed FP sort: missing exponent width (use SortManager::createFPSort)");
            return children[0]->arity;
        }

        /** Total significand width \(s\) (incl. hidden bit) for `(_ FloatingPoint e s)`. Stored as `children[1]->arity`. */
        size_t getSignificandWidth() const {
            condAssert(kind == SORT_KIND::SK_FP, "Cannot get significand width of non-floating-point sort");
            condAssert(children.size() >= 2 && children[1], "Malformed FP sort: missing significand width (use SortManager::createFPSort)");
            return children[1]->arity;
        }

        std::shared_ptr<Sort> getIndexSort() const {
            condAssert(kind == SORT_KIND::SK_ARRAY, "Cannot get index sort of non-array sort");
            if (children.size() < 1 || !children[0]) return nullptr;
            return children[0];
        }

        std::shared_ptr<Sort> getElemSort() const {
            condAssert(kind == SORT_KIND::SK_ARRAY, "Cannot get element sort of non-array sort");
            if (children.size() < 2 || !children[1]) return nullptr;
            return children[1];
        }
        
        std::shared_ptr<Sort> getParamSort(size_t index) const {
            condAssert(kind == SORT_KIND::SK_DEF, "Cannot get parameter sort of non-define-sort sort");
            return children[index];
        }
        
        std::vector<std::shared_ptr<Sort>> getParams() const {
            condAssert(kind == SORT_KIND::SK_DEF, "Cannot get parameters of non-define-sort sort");
            return std::vector<std::shared_ptr<Sort>>(children.begin(), children.end() - 1);
        }

        std::shared_ptr<Sort> getOutSort() const {
            condAssert(kind == SORT_KIND::SK_DEF, "Cannot get output sort of non-define-sort sort");
            return children[children.size() - 1];
        }
        
        bool isEqTo(const Sort& other) const {
            return *this == other;
        }

        bool isEqTo(const std::shared_ptr<Sort>& other) const {
            return *this == *other;
        }

        // Hash function for Sort deduplication
        size_t hash() const {
            size_t result = std::hash<int>{}(static_cast<int>(kind));
            result ^= std::hash<std::string>{}(name) + 0x9e3779b9 + (result << 6) + (result >> 2);
            result ^= std::hash<size_t>{}(arity) + 0x9e3779b9 + (result << 6) + (result >> 2);
            
            // Hash children
            for (const auto& child : children) {
                if (child) {
                    result ^= child->hash() + 0x9e3779b9 + (result << 6) + (result >> 2);
                }
            }
            
            return result;
        }
    };

    // Sort Manager for managing and deduplicating Sort instances
    class SortManager {
        private:
            std::vector<std::shared_ptr<Sort>> sorts;
            std::unordered_map<size_t, std::vector<std::pair<std::shared_ptr<Sort>, size_t>>> sort_buckets;
            
        public:
            SortManager();
            ~SortManager();
            
            std::shared_ptr<Sort> getSort(const size_t index) const;
            size_t getIndex(const std::shared_ptr<Sort>& sort) const;
            size_t size() const;
            
            // createSort methods corresponding to Sort constructors
            std::shared_ptr<Sort> createSort(SORT_KIND kind, std::string name, size_t arity, std::vector<std::shared_ptr<Sort>> children);
            std::shared_ptr<Sort> createSort(SORT_KIND kind, std::string name, size_t arity);
            std::shared_ptr<Sort> createSort(SORT_KIND kind, std::string name);
            std::shared_ptr<Sort> createSort(SORT_KIND kind);
            std::shared_ptr<Sort> createSort(std::string name);
            std::shared_ptr<Sort> createSort();
            
            // Specific sort creation methods (replacing global mk* functions)
            std::shared_ptr<Sort> createBVSort(size_t width);
            std::shared_ptr<Sort> createFPSort(size_t exp, size_t sig);
            std::shared_ptr<Sort> createArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem);
            /** (Tuple T1 ... Tn); an empty field list yields the unit tuple sort. */
            std::shared_ptr<Sort> createTupleSort(const std::vector<std::shared_ptr<Sort>>& fields);
            std::shared_ptr<Sort> createDatatypeSort(const std::string& name,
                const std::vector<Sort::DtConstructor>& constructors);
            std::shared_ptr<Sort> createSortDec(const std::string& name, size_t arity);
            std::shared_ptr<Sort> createSortDef(const std::string& name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort);
            
            void clear();
            
            // Getter functions for static constant sorts
            static std::shared_ptr<Sort> getNull() { return NULL_SORT; }
            static std::shared_ptr<Sort> getUnknown() { return UNKNOWN_SORT; }
            static std::shared_ptr<Sort> getBool() { return BOOL_SORT; }
            static std::shared_ptr<Sort> getInt() { return INT_SORT; }
            static std::shared_ptr<Sort> getReal() { return REAL_SORT; }
            static std::shared_ptr<Sort> getAlgebraic() { return ALGEBRAIC_SORT; }
            static std::shared_ptr<Sort> getTranscendental() { return TRANSCENDENTAL_SORT; }
            static std::shared_ptr<Sort> getStr() { return STR_SORT; }
            static std::shared_ptr<Sort> getReg() { return REG_SORT; }
            static std::shared_ptr<Sort> getExt() { return EXT_SORT; }
            static std::shared_ptr<Sort> getNat() { return NAT_SORT; }
            static std::shared_ptr<Sort> getRand() { return RAND_SORT; }
            static std::shared_ptr<Sort> getIntOrReal() { return INTOREAL_SORT; }
            static std::shared_ptr<Sort> getFloat64() { return FLOAT64_SORT; }
            static std::shared_ptr<Sort> getFloat32() { return FLOAT32_SORT; }
            static std::shared_ptr<Sort> getFloat16() { return FLOAT16_SORT; }
            static std::shared_ptr<Sort> getRoundingMode() { return ROUNDING_MODE_SORT; }

            size_t getBitWidth(const std::shared_ptr<Sort> &sort);
            size_t getExponentWidth(const std::shared_ptr<Sort> &sort);
            size_t getSignificandWidth(const std::shared_ptr<Sort> &sort);
            std::shared_ptr<Sort> getIndexSort(const std::shared_ptr<Sort> &sort);
            std::shared_ptr<Sort> getElemSort(const std::shared_ptr<Sort> &sort);
            std::shared_ptr<Sort> getParamSort(const std::shared_ptr<Sort> &sort, size_t index);
            std::vector<std::shared_ptr<Sort>> getParams(const std::shared_ptr<Sort> &sort);
            std::shared_ptr<Sort> getOutSort(const std::shared_ptr<Sort> &sort);
            
        public:
            // static constant sorts (inline for guaranteed initialization order)
            inline static const std::shared_ptr<Sort> NULL_SORT = std::make_shared<Sort>(SORT_KIND::SK_NULL, "Null", 0);
            inline static const std::shared_ptr<Sort> UNKNOWN_SORT = std::make_shared<Sort>(SORT_KIND::SK_UNKNOWN, "Unknown", 0);
            inline static const std::shared_ptr<Sort> BOOL_SORT = std::make_shared<Sort>(SORT_KIND::SK_BOOL, "Bool", 0);
            inline static const std::shared_ptr<Sort> INT_SORT = std::make_shared<Sort>(SORT_KIND::SK_INT, "Int", 0);
            inline static const std::shared_ptr<Sort> REAL_SORT = std::make_shared<Sort>(SORT_KIND::SK_REAL, "Real", 0);
            inline static const std::shared_ptr<Sort> ALGEBRAIC_SORT = std::make_shared<Sort>(SORT_KIND::SK_ALGEBRAIC, "Algebraic", 0);
            inline static const std::shared_ptr<Sort> TRANSCENDENTAL_SORT = std::make_shared<Sort>(SORT_KIND::SK_TRANSCENDENTAL, "Transcendental", 0);
            inline static const std::shared_ptr<Sort> STR_SORT = std::make_shared<Sort>(SORT_KIND::SK_STR, "String", 0);
            inline static const std::shared_ptr<Sort> REG_SORT = std::make_shared<Sort>(SORT_KIND::SK_REG, "Reg", 0);
            inline static const std::shared_ptr<Sort> EXT_SORT = std::make_shared<Sort>(SORT_KIND::SK_EXT, "ExtReal", 0);
            inline static const std::shared_ptr<Sort> NAT_SORT = std::make_shared<Sort>(SORT_KIND::SK_NAT, "Natural", 0);
            inline static const std::shared_ptr<Sort> RAND_SORT = std::make_shared<Sort>(SORT_KIND::SK_RAND, "Random", 0);
            inline static const std::shared_ptr<Sort> INTOREAL_SORT = std::make_shared<Sort>(SORT_KIND::SK_INTOREAL, "IntOrReal", 0);
            inline static const std::shared_ptr<Sort> FLOAT64_SORT = std::make_shared<Sort>(SORT_KIND::SK_FP, "Float64", 0, std::vector<std::shared_ptr<Sort>>{std::make_shared<Sort>(SORT_KIND::SK_NULL, "Exp", 11), std::make_shared<Sort>(SORT_KIND::SK_NULL, "Sig", 53)});
            inline static const std::shared_ptr<Sort> FLOAT32_SORT = std::make_shared<Sort>(SORT_KIND::SK_FP, "Float32", 0, std::vector<std::shared_ptr<Sort>>{std::make_shared<Sort>(SORT_KIND::SK_NULL, "Exp", 8), std::make_shared<Sort>(SORT_KIND::SK_NULL, "Sig", 24)});
            inline static const std::shared_ptr<Sort> FLOAT16_SORT = std::make_shared<Sort>(SORT_KIND::SK_FP, "Float16", 0, std::vector<std::shared_ptr<Sort>>{std::make_shared<Sort>(SORT_KIND::SK_NULL, "Exp", 5), std::make_shared<Sort>(SORT_KIND::SK_NULL, "Sig", 11)});
            inline static const std::shared_ptr<Sort> ROUNDING_MODE_SORT = std::make_shared<Sort>(SORT_KIND::SK_ROUNDING_MODE, "RoundingMode", 0);
            

        private:
            void initializeStaticSorts();
            std::shared_ptr<Sort> insertSortToBucket(const std::shared_ptr<Sort>& sort);
    };
    
    // smart pointer
    typedef std::shared_ptr<Sort> SortPtr;
    typedef std::shared_ptr<SortManager> SortManagerPtr;
}
#endif
 
