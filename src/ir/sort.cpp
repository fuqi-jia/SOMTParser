/* -*- Source -*-
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

#include "somtparser/ir/sort.h"

#include <cerrno>
#include <cstdlib>
#include <iterator>
#include <new>
#include <stdexcept>
#include <unordered_set>

#if defined(_WIN32)
#include <io.h>
#else
#include <unistd.h>
#endif

namespace SOMTParser{

namespace {

struct SortReleaseQueue {
    std::vector<std::shared_ptr<Sort>> sorts;
    std::vector<std::shared_ptr<std::vector<Sort::DtConstructor>>> constructors;
};

// Enqueue only members of an object already being destroyed. A use_count()
// snapshot cannot authorize modifying another node: a concurrent weak lock
// could keep it alive. Each thread's outer destructor owns its own queue.
thread_local SortReleaseQueue* releasingSorts = nullptr;

template <std::size_t N>
[[noreturn]] void abortSortRelease(const char (&message)[N]) noexcept {
    std::size_t written = 0;
    while (written < N - 1) {
#if defined(_WIN32)
        const auto count = _write(2, message + written,
                                  static_cast<unsigned>(N - 1 - written));
#else
        const auto count = ::write(STDERR_FILENO, message + written, N - 1 - written);
#endif
        if (count < 0 && errno == EINTR) { continue; }
        if (count <= 0) { break; }
        written += static_cast<std::size_t>(count);
    }
    std::abort();
}

void enqueueSortMembers(Sort& sort, SortReleaseQueue& queue) noexcept {
    try {
        queue.sorts.insert(queue.sorts.end(),
            std::make_move_iterator(sort.children.begin()),
            std::make_move_iterator(sort.children.end()));
        // Metadata must itself be queued: destroying selectors here could
        // recursively enter another datatype's destructor before we return.
        if (sort.dt_constructors) {
            queue.constructors.push_back(std::move(sort.dt_constructors));
        }
    } catch (const std::bad_alloc&) {
        abortSortRelease("SOMTParser Sort destruction: memory allocation failed\n");
    } catch (const std::length_error&) {
        abortSortRelease("SOMTParser Sort destruction: memory allocation failed (worklist capacity)\n");
    }
    sort.children.clear();
}

using SortPair = std::pair<const Sort*, const Sort*>;
struct SortPairHash {
    std::size_t operator()(const SortPair& pair) const noexcept {
        const auto left = std::hash<const Sort*>{}(pair.first);
        return left ^ (std::hash<const Sort*>{}(pair.second) + 0x9e3779b9
                       + (left << 6) + (left >> 2));
    }
};

size_t initialSortHash(const Sort& sort) {
    size_t result = std::hash<int>{}(static_cast<int>(sort.kind));
    result ^= std::hash<std::string>{}(sort.name) + 0x9e3779b9 + (result << 6) + (result >> 2);
    result ^= std::hash<size_t>{}(sort.arity) + 0x9e3779b9 + (result << 6) + (result >> 2);
    return result;
}

} // namespace

Sort::~Sort() noexcept {
    if (children.empty() && !dt_constructors) { return; }
    if (releasingSorts) {
        enqueueSortMembers(*this, *releasingSorts);
        return;
    }
    SortReleaseQueue pending;
    // The common single-child chain reuses its existing vector capacity.
    pending.sorts.swap(children);
    releasingSorts = &pending;
    enqueueSortMembers(*this, pending);
    while (!pending.sorts.empty() || !pending.constructors.empty()) {
        if (!pending.sorts.empty()) {
            auto child = std::move(pending.sorts.back());
            pending.sorts.pop_back();
            child.reset();
        } else {
            auto constructors = std::move(pending.constructors.back());
            pending.constructors.pop_back();
            constructors.reset();
        }
    }
    releasingSorts = nullptr;
}

bool Sort::operator==(const Sort& other) const {
    if (this == &other) { return true; }
    const bool nominal = (isDef() || isDec() || isDatatype())
        && (other.isDef() || other.isDec() || other.isDatatype())
        && name == other.name && arity == other.arity;
    const bool compareChildren = nominal || (isSet() && other.isSet())
        || (isArray() && other.isArray());
    // Primitive sort checks are frequent; they need no traversal allocation.
    if (!compareChildren) {
        if ((isInt() && other.isIntOrReal()) || (isIntOrReal() && other.isInt()) ||
            (isReal() && other.isIntOrReal()) || (isIntOrReal() && other.isReal())) { return true; }
        if (isFp() && other.isFp()) {
            return getExponentWidth() == other.getExponentWidth()
                && getSignificandWidth() == other.getSignificandWidth();
        }
        if (isBv() && other.isBv()) { return getBitWidth() == other.getBitWidth(); }
        return kind == other.kind && name == other.name && arity == other.arity;
    }
    if (children.size() != other.children.size()) { return false; }
    if (children.empty()) { return true; }
    std::vector<SortPair> pending{{this, &other}};
    std::unordered_set<SortPair, SortPairHash> visited;
    while (!pending.empty()) {
        const auto pair = pending.back();
        pending.pop_back();
        if (pair.first == pair.second) { continue; }
        const Sort& left = *pair.first;
        const Sort& right = *pair.second;
        if (!visited.insert(pair).second) { continue; }
        const bool nominal = (left.isDef() || left.isDec() || left.isDatatype())
            && (right.isDef() || right.isDec() || right.isDatatype())
            && left.name == right.name && left.arity == right.arity;
        if (nominal || (left.isSet() && right.isSet())
                    || (left.isArray() && right.isArray())) {
            if (left.children.size() != right.children.size()) { return false; }
            for (size_t i = 0; i < left.children.size(); ++i) {
                if (!left.children[i] || !right.children[i]) {
                    if (left.children[i] != right.children[i]) { return false; }
                } else {
                    pending.emplace_back(left.children[i].get(), right.children[i].get());
                }
            }
        } else if ((left.isInt() && right.isIntOrReal()) ||
                   (left.isIntOrReal() && right.isInt()) ||
                   (left.isReal() && right.isIntOrReal()) ||
                   (left.isIntOrReal() && right.isReal())) {
            continue;
        } else if (left.isFp() && right.isFp()) {
            if (left.getExponentWidth() != right.getExponentWidth() ||
                left.getSignificandWidth() != right.getSignificandWidth()) { return false; }
        } else if (left.isBv() && right.isBv()) {
            if (left.getBitWidth() != right.getBitWidth()) { return false; }
        } else if (left.kind != right.kind || left.name != right.name || left.arity != right.arity) {
            return false;
        }
    }
    return true;
}

size_t Sort::hash() const {
    if (children.empty()) { return initialSortHash(*this); }
    struct Frame { const Sort* sort; size_t next; size_t value; };
    std::vector<Frame> pending{{this, 0, initialSortHash(*this)}};
    std::unordered_map<const Sort*, size_t> completed;
    std::unordered_set<const Sort*> active{this};
    while (!pending.empty()) {
        auto& frame = pending.back();
        if (frame.next == frame.sort->children.size()) {
            completed.emplace(frame.sort, frame.value);
            active.erase(frame.sort);
            pending.pop_back();
            continue;
        }
        const auto* child = frame.sort->children[frame.next].get();
        if (!child) { ++frame.next; continue; }
        const auto found = completed.find(child);
        if (found != completed.end()) {
            frame.value ^= found->second + 0x9e3779b9 + (frame.value << 6) + (frame.value >> 2);
            ++frame.next;
        } else {
            if (!active.insert(child).second) {
                throw std::invalid_argument("Sort::hash: cyclic structural sort arguments");
            }
            pending.push_back({child, 0, initialSortHash(*child)});
        }
    }
    return completed.at(this);
}

std::string Sort::toString() const {
    // Keep primitive rendering allocation-free apart from the returned string.
    switch (kind) {
        case SORT_KIND::SK_BOOL: return "Bool";
        case SORT_KIND::SK_INT: return "Int";
        case SORT_KIND::SK_REAL: return "Real";
        case SORT_KIND::SK_BV: return "(_ BitVec " + std::to_string(getBitWidth()) + ")";
        case SORT_KIND::SK_FP:
            return "(_ FloatingPoint " + std::to_string(getExponentWidth())
                + " " + std::to_string(getSignificandWidth()) + ")";
        case SORT_KIND::SK_STR: return "String";
        case SORT_KIND::SK_RELATION: return "Relation";
        case SORT_KIND::SK_BAG: return "Bag";
        case SORT_KIND::SK_SEQ: return "Sequence";
        case SORT_KIND::SK_UF: return "UF";
        case SORT_KIND::SK_REG: return "RegLan";
        case SORT_KIND::SK_EXT: return "ExtReal";
        case SORT_KIND::SK_NAT: return "Natural";
        case SORT_KIND::SK_RAND: return "Random";
        case SORT_KIND::SK_INTOREAL: return "IntOrReal";
        case SORT_KIND::SK_ALGEBRAIC: return "Algebraic";
        case SORT_KIND::SK_TRANSCENDENTAL: return "Transcendental";
        case SORT_KIND::SK_ROUNDING_MODE: return "RoundingMode";
        case SORT_KIND::SK_DATATYPE: if (name.empty()) { return "Datatype"; } [[fallthrough]];
        case SORT_KIND::SK_DEF:
        case SORT_KIND::SK_DEC: if (children.empty()) { return name; } break;
        case SORT_KIND::SK_SET: if (children.empty()) { return "Set"; } break;
        case SORT_KIND::SK_TUPLE: if (children.empty()) { return "UnitTuple"; } break;
        case SORT_KIND::SK_ARRAY: break;
        default: return "Unknown";
    }
    struct Frame {
        const Sort* sort;
        size_t next = 0;
        size_t count = 0;
        bool entered = false;
        bool allowNull = false;
    };
    std::vector<Frame> pending{{this}};
    std::unordered_set<const Sort*> active;
    std::string result;
    while (!pending.empty()) {
        auto& frame = pending.back();
        const Sort& sort = *frame.sort;
        if (!frame.entered) {
            const char* atom = nullptr;
            switch (sort.kind) {
                case SORT_KIND::SK_BOOL: atom = "Bool"; break;
                case SORT_KIND::SK_INT: atom = "Int"; break;
                case SORT_KIND::SK_REAL: atom = "Real"; break;
                case SORT_KIND::SK_BV:
                    result += "(_ BitVec " + std::to_string(sort.getBitWidth()) + ")";
                    pending.pop_back(); continue;
                case SORT_KIND::SK_FP:
                    result += "(_ FloatingPoint " + std::to_string(sort.getExponentWidth())
                        + " " + std::to_string(sort.getSignificandWidth()) + ")";
                    pending.pop_back(); continue;
                case SORT_KIND::SK_STR: atom = "String"; break;
                case SORT_KIND::SK_ARRAY:
                    condAssert(sort.children.size() >= 2, "Malformed array sort: missing arguments");
                    result += "(Array"; frame.count = 2; break;
                case SORT_KIND::SK_DATATYPE:
                    if (sort.name.empty()) { atom = "Datatype"; break; }
                    [[fallthrough]];
                case SORT_KIND::SK_DEC:
                case SORT_KIND::SK_DEF:
                    if (sort.children.empty()) {
                        result += sort.name; pending.pop_back(); continue;
                    }
                    result += "(" + sort.name;
                    frame.count = sort.children.size(); frame.allowNull = true; break;
                case SORT_KIND::SK_SET:
                    if (sort.children.empty()) { atom = "Set"; break; }
                    result += "(Set"; frame.count = 1; break;
                case SORT_KIND::SK_RELATION: atom = "Relation"; break;
                case SORT_KIND::SK_BAG: atom = "Bag"; break;
                case SORT_KIND::SK_SEQ: atom = "Sequence"; break;
                case SORT_KIND::SK_TUPLE:
                    if (sort.children.empty()) { atom = "UnitTuple"; break; }
                    result += "(Tuple"; frame.count = sort.children.size(); break;
                case SORT_KIND::SK_UF: atom = "UF"; break;
                case SORT_KIND::SK_REG: atom = "RegLan"; break;
                case SORT_KIND::SK_EXT: atom = "ExtReal"; break;
                case SORT_KIND::SK_NAT: atom = "Natural"; break;
                case SORT_KIND::SK_RAND: atom = "Random"; break;
                case SORT_KIND::SK_INTOREAL: atom = "IntOrReal"; break;
                case SORT_KIND::SK_ALGEBRAIC: atom = "Algebraic"; break;
                case SORT_KIND::SK_TRANSCENDENTAL: atom = "Transcendental"; break;
                case SORT_KIND::SK_ROUNDING_MODE: atom = "RoundingMode"; break;
                default: atom = "Unknown"; break;
            }
            if (atom) { result += atom; pending.pop_back(); continue; }
            if (!active.insert(frame.sort).second) {
                throw std::invalid_argument("Sort::toString: cyclic structural sort arguments");
            }
            frame.entered = true;
        }
        if (frame.next == frame.count) {
            result += ")"; active.erase(frame.sort); pending.pop_back(); continue;
        }
        const auto* child = sort.children[frame.next++].get();
        result += " ";
        if (!child && frame.allowNull) { result += "?"; continue; }
        condAssert(child != nullptr, "Malformed sort: null argument");
        pending.push_back({child});
    }
    return result;
}

    // Static constant sorts are now defined inline in the header file

    // SortManager implementation
    SortManager::SortManager() {
        initializeStaticSorts();
    }

    SortManager::~SortManager() {
        clear();
    }

    void SortManager::initializeStaticSorts() {
        // Add static sorts to the manager
        sorts.push_back(NULL_SORT);
        sorts.push_back(UNKNOWN_SORT);
        sorts.push_back(BOOL_SORT);
        sorts.push_back(INT_SORT);
        sorts.push_back(REAL_SORT);
        sorts.push_back(ALGEBRAIC_SORT);
        sorts.push_back(TRANSCENDENTAL_SORT);
        sorts.push_back(STR_SORT);
        sorts.push_back(REG_SORT);
        sorts.push_back(EXT_SORT);
        sorts.push_back(NAT_SORT);
        sorts.push_back(RAND_SORT);
        sorts.push_back(INTOREAL_SORT);
        sorts.push_back(FLOAT64_SORT);
        sorts.push_back(FLOAT32_SORT);
        sorts.push_back(FLOAT16_SORT);
        sorts.push_back(ROUNDING_MODE_SORT);
        
        // Add them to the hash buckets for deduplication
        for (size_t i = 0; i < sorts.size(); ++i) {
            size_t hash_val = sorts[i]->hash();
            sort_buckets[hash_val].push_back({sorts[i], i});
        }
    }

    std::shared_ptr<Sort> SortManager::getSort(const size_t index) const {
        if (index >= sorts.size()) {
            return nullptr;
        }
        return sorts[index];
    }

    size_t SortManager::getIndex(const std::shared_ptr<Sort>& sort) const {
        for (size_t i = 0; i < sorts.size(); ++i) {
            if (sorts[i] == sort) {
                return i;
            }
        }
        return SIZE_MAX; // Not found
    }

    size_t SortManager::size() const {
        return sorts.size();
    }

    void SortManager::clear() {
        sorts.clear();
        sort_buckets.clear();
    }

    std::shared_ptr<Sort> SortManager::insertSortToBucket(const std::shared_ptr<Sort>& sort) {
        size_t hash_val = sort->hash();
        
        // Check if an equivalent sort already exists
        auto bucket_it = sort_buckets.find(hash_val);
        if (bucket_it != sort_buckets.end()) {
            for (const auto& pair : bucket_it->second) {
                if (*pair.first == *sort) {
                    return pair.first; // Return existing sort
                }
            }
        }
        
        // Add new sort
        size_t new_index = sorts.size();
        sorts.push_back(sort);
        sort_buckets[hash_val].push_back({sort, new_index});
        
        return sort;
    }

    // createSort methods
    std::shared_ptr<Sort> SortManager::createSort(SORT_KIND kind, std::string name, size_t arity, std::vector<std::shared_ptr<Sort>> children) {
        auto sort = std::make_shared<Sort>(kind, name, arity, children);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSort(SORT_KIND kind, std::string name, size_t arity) {
        auto sort = std::make_shared<Sort>(kind, name, arity);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSort(SORT_KIND kind, std::string name) {
        auto sort = std::make_shared<Sort>(kind, name);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSort(SORT_KIND kind) {
        auto sort = std::make_shared<Sort>(kind);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSort(std::string name) {
        auto sort = std::make_shared<Sort>(name);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSort() {
        auto sort = std::make_shared<Sort>();
        return insertSortToBucket(sort);
    }

    // Specific sort creation methods
    std::shared_ptr<Sort> SortManager::createBVSort(size_t width) {
        auto width_sort = std::make_shared<Sort>(SORT_KIND::SK_NULL, "Width", width);
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_BV, "BV", 0, std::vector<std::shared_ptr<Sort>>{width_sort});
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createFPSort(size_t exp, size_t sig) {
        auto exp_sort = std::make_shared<Sort>(SORT_KIND::SK_NULL, "Exp", exp);
        auto sig_sort = std::make_shared<Sort>(SORT_KIND::SK_NULL, "Sig", sig);
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_FP, "FP", 0, std::vector<std::shared_ptr<Sort>>{exp_sort, sig_sort});
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createArraySort(std::shared_ptr<Sort> index, std::shared_ptr<Sort> elem) {
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0, std::vector<std::shared_ptr<Sort>>{index, elem});
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSetSort(std::shared_ptr<Sort> elem) {
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_SET, "Set", 0, std::vector<std::shared_ptr<Sort>>{elem});
        return insertSortToBucket(sort);
    }

    // Ported from the SMTStabilizer fork.
    std::shared_ptr<Sort> SortManager::createTupleSort(const std::vector<std::shared_ptr<Sort>>& fields) {
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_TUPLE, "Tuple", 0, fields);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createDatatypeSort(const std::string& name,
            const std::vector<Sort::DtConstructor>& constructors) {
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_DATATYPE, name, 0);
        sort->dt_constructors = std::make_shared<std::vector<Sort::DtConstructor>>(constructors);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSortDec(const std::string& name, size_t arity) {
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_DEC, name, arity);
        return insertSortToBucket(sort);
    }

    std::shared_ptr<Sort> SortManager::createSortDef(const std::string& name, const std::vector<std::shared_ptr<Sort>> &params, std::shared_ptr<Sort> out_sort) {
        std::vector<std::shared_ptr<Sort>> children;
        children.insert(children.end(), params.begin(), params.end());
        children.push_back(out_sort);
        auto sort = std::make_shared<Sort>(SORT_KIND::SK_DEF, name, children.size() - 1, children);
        return insertSortToBucket(sort);
    }


    size_t SortManager::getBitWidth(const std::shared_ptr<Sort> &sort) {
        condAssert(sort != nullptr, "Sort is null");
        return sort->getBitWidth();
    }
    
    size_t SortManager::getExponentWidth(const std::shared_ptr<Sort> &sort) {
        condAssert(sort != nullptr, "Sort is null");
        return sort->getExponentWidth();
    }
    
    size_t SortManager::getSignificandWidth(const std::shared_ptr<Sort> &sort) {
        condAssert(sort != nullptr, "Sort is null");
        return sort->getSignificandWidth();
    }
    
    std::shared_ptr<Sort> SortManager::getIndexSort(const std::shared_ptr<Sort> &sort) {
        return sort->getIndexSort();
    }
    
    std::shared_ptr<Sort> SortManager::getElemSort(const std::shared_ptr<Sort> &sort) {
        return sort->getElemSort();
    }
    
    std::shared_ptr<Sort> SortManager::getParamSort(const std::shared_ptr<Sort> &sort, size_t index) {
        return sort->getParamSort(index);
    }
    
    std::vector<std::shared_ptr<Sort>> SortManager::getParams(const std::shared_ptr<Sort> &sort) {
        return sort->getParams();
    }
    
    std::shared_ptr<Sort> SortManager::getOutSort(const std::shared_ptr<Sort> &sort) {
        return sort->getOutSort();
    }
}