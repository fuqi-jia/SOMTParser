/* -*- Source -*-
 *
 * An SMT/OMT Parser (Conversion part)
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
#include <array>
#include <stack>

namespace SOMTParser {

    namespace {
    using ConversionNode = std::shared_ptr<DAGNode>;
    using ConversionCache = std::unordered_map<ConversionNode, ConversionNode>;

    // Dependencies are materialized once per frame. Finishing a node only
    // reads completed children; no rule re-enters the traversal.
    template<class Dependencies, class Finish>
    ConversionNode conversionPostorder(const ConversionNode& root, ConversionCache& cache,
                                        Dependencies dependencies, Finish finish) {
        struct Frame { ConversionNode node; std::vector<ConversionNode> children; size_t next = 0; };
        if(cache.count(root)) return cache.at(root);
        std::vector<Frame> pending{{root, dependencies(root)}};
        std::unordered_set<const DAGNode*> active{root.get()};
        while(!pending.empty()) {
            auto& frame = pending.back();
            if(frame.next < frame.children.size()) {
                auto child = frame.children[frame.next++];
                if(cache.count(child)) continue;
                condAssert(child && active.insert(child.get()).second,
                           "cyclic or null expression in conversion");
                pending.push_back({child, dependencies(child)});
                continue;
            }
            auto node = frame.node;
            cache[node] = finish(node);
            active.erase(node.get());
            pending.pop_back();
        }
        return cache.at(root);
    }
    }


    void Parser::collectAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        collectAtoms(expr, atoms, visited);
    }

    void Parser::collectAtoms(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& atoms) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        for(auto& expr : exprs) {
            collectAtoms(expr, atoms, visited);
        }
    }

    void Parser::collectAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms, std::unordered_set<std::shared_ptr<DAGNode>>& visited) {
        std::vector<ConversionNode> pending{expr};
        while(!pending.empty()) {
            auto node = std::move(pending.back()); pending.pop_back();
            if(!visited.insert(node).second) continue;
            if(node->isAtom()) { atoms.insert(node); continue; }
            const size_t count = node->getChildrenSize();
            for(size_t i = count; i > 0; --i) pending.push_back(node->getChild(i - 1));
        }
    }
    void Parser::collectGroundAtoms(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& atoms) {
        // convert to NNF
        std::vector<std::shared_ptr<DAGNode>> nnf_exprs;
        for(auto& expr : exprs) {
            nnf_exprs.emplace_back(toNNF(expr));
        }
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        for(auto& expr : nnf_exprs) {
            if(visited.find(expr) != visited.end()){
                continue;
            }
            collectGroundAtoms(expr, atoms, visited);
        }
    }
    void Parser::collectGroundAtoms(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& atoms, std::unordered_set<std::shared_ptr<DAGNode>>& visited) {
        std::vector<ConversionNode> pending{expr};
        while(!pending.empty()) {
            auto node = std::move(pending.back()); pending.pop_back();
            if(!visited.insert(node).second) continue;
            if(node->isAtom()) { atoms.insert(node); continue; }
            if(!(node->isAnd() || node->isOr() || node->isNot())) continue;
            const size_t count = node->getChildrenSize();
            for(size_t i = count; i > 0; --i) pending.push_back(node->getChild(i - 1));
        }
    }

    std::shared_ptr<DAGNode> Parser::getCNFAtom(std::shared_ptr<DAGNode> bool_var) {
        if(cnf_atom_map.find(bool_var) != cnf_atom_map.end()){
            return cnf_atom_map[bool_var];
        }
        return NodeManager::NULL_NODE;
    }
    std::shared_ptr<DAGNode> Parser::getTExplanation(std::shared_ptr<DAGNode> expr) {
        if(cnf_atom_map.find(expr) != cnf_atom_map.end()){
            return cnf_atom_map[expr];
        }
        return NodeManager::NULL_NODE;
    }
    bool Parser::isTAbstraction(std::shared_ptr<DAGNode> expr) {
        if(cnf_atom_map.find(expr) != cnf_atom_map.end()){
            return true;
        }
        return false;
    }
    std::vector<std::shared_ptr<DAGNode>> Parser::getCNFAtoms() {
        // Only report positive pairs; each atom is registered together with its
        // negation, so filtering by polarity (instead of a visited-set that
        // depends on unordered_map iteration order) yields a stable result.
        std::vector<std::shared_ptr<DAGNode>> atoms;
        std::unordered_set<std::shared_ptr<DAGNode>> seen;
        for(auto& [atom, bool_var] : cnf_bool_var_map){
            if(atom->isNot() || bool_var->isNot()){
                continue;
            }
            if(!seen.insert(bool_var).second){
                continue;
            }
            atoms.emplace_back(atom);
        }
        return atoms;
    }
    std::shared_ptr<DAGNode> Parser::getCNFBoolVar(std::shared_ptr<DAGNode> atom) {
        if(cnf_bool_var_map.find(atom) != cnf_bool_var_map.end()){
            return cnf_bool_var_map[atom];
        }
        return NodeManager::NULL_NODE;
    }
    std::vector<std::shared_ptr<DAGNode>> Parser::getCNFBoolVars() {
        // Symmetric to getCNFAtoms: keep only positive pairs so the result is
        // independent of unordered_map iteration order.
        std::vector<std::shared_ptr<DAGNode>> bool_vars;
        std::unordered_set<std::shared_ptr<DAGNode>> seen;
        for(auto& [bool_var, atom] : cnf_atom_map){
            if(bool_var->isNot() || atom->isNot()){
                continue;
            }
            if(!seen.insert(bool_var).second){
                continue;
            }
            bool_vars.emplace_back(bool_var);
        }
        return bool_vars;
    }

    void Parser::collectVars(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& vars) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        for(auto& expr : exprs) {
            collectVars(expr, vars, visited);
        }
    }

    void Parser::collectVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        collectVars(expr, vars, visited);
    }

    void Parser::collectVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars, std::unordered_set<std::shared_ptr<DAGNode>>& visited) {
        std::vector<ConversionNode> pending{expr};
        while(!pending.empty()) {
            auto node = std::move(pending.back()); pending.pop_back();
            if(!visited.insert(node).second) continue;
            if(node->isVar() && !node->isLetBindVar()) { vars.insert(node); continue; }
            const size_t count = node->isLetBindVar()
                ? std::min<size_t>(1, node->getChildrenSize()) : node->getChildrenSize();
            for(size_t i = count; i > 0; --i) pending.push_back(node->getChild(i - 1));
        }
    }

    void Parser::collectAssignableVars(std::vector<std::shared_ptr<DAGNode>> exprs, std::unordered_set<std::shared_ptr<DAGNode>>& vars) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        for(auto& expr : exprs) {
            collectAssignableVars(expr, vars, visited);
        }
    }

    void Parser::collectAssignableVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars) {
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        collectAssignableVars(expr, vars, visited);
    }

    void Parser::collectAssignableVars(std::shared_ptr<DAGNode> expr, std::unordered_set<std::shared_ptr<DAGNode>>& vars, std::unordered_set<std::shared_ptr<DAGNode>>& visited) {
        std::vector<ConversionNode> pending{expr};
        while(!pending.empty()) {
            auto node = std::move(pending.back()); pending.pop_back();
            if(!visited.insert(node).second) continue;
            if(node->isAssignableVar()) { vars.insert(node); continue; }
            const size_t count = node->getChildrenSize();
            for(size_t i = count; i > 0; --i) pending.push_back(node->getChild(i - 1));
        }
    }


    std::shared_ptr<DAGNode> Parser::replaceAtoms(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map) {
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        bool is_changed = false;
        std::shared_ptr<DAGNode> new_expr = replaceAtoms(expr, atom_map, visited, is_changed);
        if (is_changed) {
            return new_expr;
        }
        return expr;
    }

    std::shared_ptr<DAGNode> Parser::replaceAtoms(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& atom_map, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, bool& is_changed) {
        const auto dependencies = [&](const ConversionNode& node) {
            return (node->isAtom() && atom_map.count(node)) ? std::vector<ConversionNode>{} : node->getChildren();
        };
        const auto finish = [&](const ConversionNode& node) {
            if(node->isAtom() && atom_map.count(node)) return atom_map.at(node);
            bool changed = false;
            std::vector<ConversionNode> children;
            for(const auto& child : node->getChildren()) {
                auto replacement = visited.at(child);
                changed |= replacement != child;
                children.push_back(std::move(replacement));
            }
            return changed ? mkOper(node->getSort(), node->getKind(), children) : node;
        };
        auto result = conversionPostorder(expr, visited, dependencies, finish);
        is_changed |= result != expr;
        return result;
    }

    std::shared_ptr<DAGNode> Parser::replaceNodes(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& node_map) {
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        bool is_changed = false;
        std::shared_ptr<DAGNode> new_expr = replaceNodes(expr, node_map, visited, is_changed);
        if (is_changed) {
            return new_expr;
        }
        return expr;
    }

    std::shared_ptr<DAGNode> Parser::replaceNodes(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& node_map, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, bool& is_changed) {
        const auto dependencies = [&](const ConversionNode& node) {
            return (node_map.count(node)) ? std::vector<ConversionNode>{} : node->getChildren();
        };
        const auto finish = [&](const ConversionNode& node) {
            if(node_map.count(node)) return node_map.at(node);
            bool changed = false;
            std::vector<ConversionNode> children;
            for(const auto& child : node->getChildren()) {
                auto replacement = visited.at(child);
                changed |= replacement != child;
                children.push_back(std::move(replacement));
            }
            return changed ? mkOper(node->getSort(), node->getKind(), children) : node;
        };
        auto result = conversionPostorder(expr, visited, dependencies, finish);
        is_changed |= result != expr;
        return result;
    }

    std::shared_ptr<DAGNode> Parser::toTseitinCNF(std::shared_ptr<DAGNode> expr, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        std::shared_ptr<DAGNode> result = toTseitinCNF(expr, visited, clauses);
        return result;
    }
    std::shared_ptr<DAGNode> Parser::toTseitinXor(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        // c <-> a xor b <=> (c -> a xor b) and (a xor b -> c)
        // => c -> a xor b => ¬c or a xor b => ¬c or ((¬a or ¬b) and (a or b))
        //    => (¬c or ¬a or ¬b) and (¬c or a or b)
        // => a xor b -> c => ¬((¬a and b) or (a and ¬b)) or c => (a or ¬b) and (¬a or b) -> c
        //    => (a or ¬b or c) and (¬a or b or c)
        std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);
        // -a -b -c
        std::vector<std::shared_ptr<DAGNode>> or_children1;
        or_children1.emplace_back(mkNot(c));
        or_children1.emplace_back(mkNot(a));
        or_children1.emplace_back(mkNot(b));
        clauses.emplace_back(mkOr(or_children1));
        // a b -c
        std::vector<std::shared_ptr<DAGNode>> or_children2;
        or_children2.emplace_back(mkNot(c));
        or_children2.emplace_back(a);
        or_children2.emplace_back(b);
        clauses.emplace_back(mkOr(or_children2));
        // -a b c
        std::vector<std::shared_ptr<DAGNode>> or_children3;
        or_children3.emplace_back(c);
        or_children3.emplace_back(mkNot(a));
        or_children3.emplace_back(b);
        clauses.emplace_back(mkOr(or_children3));
        // a -b c
        std::vector<std::shared_ptr<DAGNode>> or_children4;
        or_children4.emplace_back(c);
        or_children4.emplace_back(a);
        or_children4.emplace_back(mkNot(b));
        clauses.emplace_back(mkOr(or_children4));
        return c;
    }

    // auxiliary function: handle the equivalence relation between two boolean variables
    std::shared_ptr<DAGNode> Parser::toTseitinEq(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);

        // c <-> (a <-> b) -> c -> (a <-> b) and (a <-> b) -> c
        // => (¬c or a or ¬b) and (¬c or ¬a or b) and (c or a or b) and (c or ¬a or ¬b)

        // add clause: (¬c ∨ a ∨ ¬b) - when a is false or b is true, c can be false
        clauses.emplace_back(mkOr({mkNot(c), a, mkNot(b)}));

        // add clause: (¬c ∨ ¬a ∨ b) - when a is true or b is false, c can be false
        clauses.emplace_back(mkOr({mkNot(c), mkNot(a), b}));

        // add clause: (c ∨ a ∨ b) - when a and b are both false, c must be true
        clauses.emplace_back(mkOr({c, a, b}));

        // add clause: (c ∨ ¬a ∨ ¬b) - when a and b are both true, c must be true
        clauses.emplace_back(mkOr({c, mkNot(a), mkNot(b)}));

        return c;
    }

    // auxiliary function: handle the inequality relation between two boolean variables
    std::shared_ptr<DAGNode> Parser::toTseitinDistinct(std::shared_ptr<DAGNode> a, std::shared_ptr<DAGNode> b, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);

        // c <-> (a != b) -> c -> (a != b)
        // => (¬c or a or b) and (¬c or ¬a or ¬b) and (c or ¬a or b) and (c or a or ¬b)

        // add clause: (¬c ∨ a ∨ b) - when a and b are both false, c can be false
        clauses.emplace_back(mkOr({mkNot(c), a, b}));

        // add clause: (¬c ∨ ¬a ∨ ¬b) - when a and b are both true, c can be false
        clauses.emplace_back(mkOr({mkNot(c), mkNot(a), mkNot(b)}));

        // add clause: (c ∨ ¬a ∨ b) - when a is true and b is false, c must be true
        clauses.emplace_back(mkOr({c, mkNot(a), b}));

        // add clause: (c ∨ a ∨ ¬b) - when a is false and b is true, c must be true
        clauses.emplace_back(mkOr({c, a, mkNot(b)}));

        return c;
    }
    std::shared_ptr<DAGNode> Parser::toTseitinCNF(std::shared_ptr<DAGNode> expr, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited, std::vector<std::shared_ptr<DAGNode>>& clauses) {
        ConversionCache expanded;
        const auto dependencies = [&](const ConversionNode& node) {
            if(node->isAtom() || node->isLiteral() || node->isTempVar()) return std::vector<ConversionNode>{};
            if(node->isLet()) {
                expanded[node] = expandLet(node);
                return std::vector<ConversionNode>{expanded.at(node)};
            }
            return node->getChildren();
        };
        const auto completed = [&](const ConversionNode& node) { return visited.at(node); };
        const auto finish = [&](const ConversionNode& expr) -> ConversionNode {

            // Tseitin CNF is ¬applied to atoms: all atoms are already in CNF form
            if(expr->isAtom()){
                auto atom_it = cnf_map.find(expr);
                if(atom_it != cnf_map.end()){
                    return atom_it->second;
                }
                // Standalone toTseitinCNF call (outside the toCNF pipeline): the
                // atom has not been abstracted yet, so register a fresh Boolean
                // abstraction variable on the fly, mirroring the bookkeeping done
                // in toCNF. Returning cnf_map[expr] blindly would hand out a null
                // node in release builds.
                std::shared_ptr<DAGNode> new_var = mkTempVar(SortManager::BOOL_SORT);
                std::shared_ptr<DAGNode> not_atom = mkNot(expr);
                std::shared_ptr<DAGNode> not_new_var = mkNot(new_var);
                cnf_map[expr] = new_var;
                cnf_map[not_atom] = not_new_var;
                cnf_atom_map[new_var] = expr;
                cnf_bool_var_map[expr] = new_var;
                cnf_atom_map[not_new_var] = not_atom;
                cnf_bool_var_map[not_atom] = not_new_var;
                return new_var;
            }
            if(expr->isLiteral() || expr->isTempVar()) {
                // always return the original expression
                // and no need to add to visited
                return expr;
            }
            if (visited.find(expr) != visited.end()) {
                return visited[expr];
            }

            if(expr->isLet()){
                std::shared_ptr<DAGNode> result = completed(expanded.at(expr));
                visited[expr] = result;
                return result;
            }
            // c <-> ¬a <=> c -> ¬a and ¬a -> c
            // => ¬c or ¬a
            // => a or c
            if(expr->isNot()){
                // Convert the child first so that clauses only ever reference
                // literals / abstraction variables (the child may be an atom or a
                // nested formula when toTseitinCNF is called outside toCNF).
                std::shared_ptr<DAGNode> a = completed(expr->getChild(0));
                std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);
                clauses.emplace_back(mkOr({mkNot(c), mkNot(a)}));
                clauses.emplace_back(mkOr({a, c}));
                visited[expr] = c;
                return c;
            }
            // a and b and ... <=> c <-> a and b and ...
            // => c -> a and b and ... => ¬c or a and b and ... => (¬c or a) and (¬c or b) and ...
            // => a and b and ... -> c => ¬a or ¬b or ... or c
            else if (expr->isAnd()) {
                std::vector<std::shared_ptr<DAGNode>> children;
                for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child_cnf = completed(expr->getChild(i));
                    children.emplace_back(child_cnf);
                }
                if(children.size() == 1){
                    // return the only child, which is a temp var or boolean variable
                    condAssert(children[0]->isLiteral(), "toTseitinCNF: children[0] is not a literal");
                    return children[0];
                }
                // Two-sided, and that is what preserves the MODEL COUNT rather
                // than merely satisfiability: `c → childᵢ` and `(⋀ childᵢ) → c`
                // together make the auxiliary functionally determined by the
                // originals, so each source model extends to exactly one target
                // model. A one-sided (Plaisted-Greenbaum) encoding would emit only
                // the first half, stay equisatisfiable, and multiply the number of
                // models -- a difference no satisfiability test can observe, so it
                // has to be measured by counting.
                std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);
                std::vector<std::shared_ptr<DAGNode>> or_children;
                for(auto& child : children) {
                    clauses.emplace_back(mkOr({mkNot(c), child}));
                    or_children.emplace_back(mkNot(child));
                }
                or_children.emplace_back(c);
                clauses.emplace_back(mkOr(or_children));
                visited[expr] = c; // no need to visit again
                condAssert(c->isLiteral() || c->isTempVar(), "toTseitinCNF: c is not a literal or temp var");
                return c;
            }
            // a or b or ... <=> c <-> a or b or ...
            // => c -> a or b or ... => ¬c or a or b or ... => ¬c or a or b or ...
            // => a or b or ... -> c => (¬a and ¬b and ...) or c => ¬a or c and ¬b or c and ...
            else if (expr->isOr()) {
                std::vector<std::shared_ptr<DAGNode>> children;
                for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child_cnf = completed(expr->getChild(i));
                    children.emplace_back(child_cnf);
                }
                if(children.size() == 1){
                    // return the only child, which is a temp var or boolean variable
                    condAssert(children[0]->isLiteral(), "toTseitinCNF: children[0] is not a literal");
                    return children[0];
                }
                std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);
                std::vector<std::shared_ptr<DAGNode>> or_children;
                for(auto& child : children) {
                    clauses.emplace_back(mkOr({mkNot(child), c}));
                    or_children.emplace_back(child);
                }
                or_children.emplace_back(mkNot(c));
                clauses.emplace_back(mkOr(or_children));
                visited[expr] = c; // no need to visit again
                condAssert(c->isLiteral() || c->isTempVar(), "toTseitinCNF: c is not a literal or temp var");
                return c;
            }
            // c <-> (a1 -> a2 -> ... -> an), which is c <-> (¬a1 or ... or ¬a(n-1) or an).
            // => forward:  c -> the disjunction  =>  ¬c or ¬a1 or ... or ¬a(n-1) or an
            // => converse: the disjunction -> c.  A disjunction implies c exactly when
            //    EVERY disjunct does, so this is one clause PER DISJUNCT, not one clause
            //    listing them all:
            //        (a1 or c), ..., (a(n-1) or c), (¬an or c)
            //    The single clause (¬a1 or ... or ¬an or c) that stood here is a
            //    different formula -- it encodes (a1 and ... and an) -> c -- and it is
            //    strictly weaker. With a1 false the antecedent a1 -> a2 holds, so c must
            //    be true, but that clause is already satisfied by ¬a1 and leaves c free.
            //    The result stays equisatisfiable, which is why nothing caught it for so
            //    long, and stops being equivalent: the auxiliary is no longer a function
            //    of the originals, so the number of models grows. Counted on
            //    (or x (=> a b)) over all variables of the encoding: 7 models for the
            //    formula, 9 for the clause set. Only a nested implication is affected --
            //    an implication that is the whole assertion has its definition variable
            //    pinned by the assertion itself, which is why this survived.
            else if (expr->isImplies()) {
                std::vector<std::shared_ptr<DAGNode>> children;
                for (size_t i = 0; i < expr->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child_cnf = completed(expr->getChild(i));
                    children.emplace_back(child_cnf);
                }
                if(children.size() == 1){
                    // return the only child, which is a temp var or boolean variable
                    condAssert(children[0]->isLiteral(), "toTseitinCNF: children[0] is not a literal");
                    return children[0];
                }
                std::shared_ptr<DAGNode> c = mkTempVar(SortManager::BOOL_SORT);
                std::vector<std::shared_ptr<DAGNode>> or_children1;
                or_children1.emplace_back(mkNot(c));
                for(size_t i = 0; i < children.size(); i++) {
                    if(i == children.size() - 1){
                        or_children1.emplace_back(children[i]);
                    } else {
                        or_children1.emplace_back(mkNot(children[i]));
                    }
                }
                clauses.emplace_back(mkOr(or_children1));
                // The converse, one clause per disjunct of the implication.
                for(size_t i = 0; i < children.size(); i++) {
                    std::vector<std::shared_ptr<DAGNode>> converse;
                    if(i == children.size() - 1){
                        converse.emplace_back(mkNot(children[i]));
                    } else {
                        converse.emplace_back(children[i]);
                    }
                    converse.emplace_back(c);
                    clauses.emplace_back(mkOr(converse));
                }
                visited[expr] = c; // no need to visit again
                condAssert(c->isLiteral() || c->isTempVar(), "toTseitinCNF: c is not a literal or temp var");
                return c;
            }
            // c <-> a xor b <=> (c -> a xor b) and (a xor b -> c)
            // => c -> a xor b => ¬c or a xor b => ¬c or ((¬a or ¬b) and (a or b))
            //    => (¬c or ¬a or ¬b) and (¬c or a or b)
            // => a xor b -> c => ¬((¬a and b) or (a and ¬b)) or c => (a or ¬b) and (¬a or b) -> c
            //    => (a or ¬b or c) and (¬a or b or c)
            else if (expr->isXor()) {
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i));
                    children.emplace_back(child);
                }
                std::shared_ptr<DAGNode> result = children[0];
                for(size_t i = 1; i < children.size(); i++){
                    result = toTseitinXor(result, children[i], clauses);
                }
                visited[expr] = result;
                return result;
            }
            else if(expr->isEq()){
                // all children are boolean variables
                bool all_bool = true;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    if(!expr->getChild(i)->getSort()->isBool()){
                        all_bool = false;
                        err_all(ERROR_TYPE::ERR_TYPE_MIS, "Need boolean variables for eq, but got " + expr->getChild(i)->getSort()->toString());
                        break;
                    }
                }

                condAssert(all_bool, "toTseitinCNF: eq has non-boolean variables");

                if(all_bool){
                    if(expr->getChildrenSize() == 1){
                        // directly return the only child
                        std::shared_ptr<DAGNode> child_cnf = completed(expr->getChild(0));
                        visited[expr] = child_cnf;
                        return child_cnf;
                    }
                    else if(expr->getChildrenSize() == 2){
                        // two children
                        std::shared_ptr<DAGNode> a = completed(expr->getChild(0));
                        std::shared_ptr<DAGNode> b = completed(expr->getChild(1));
                        std::shared_ptr<DAGNode> c = toTseitinEq(a, b, clauses);
                        visited[expr] = c;
                        condAssert(c->isLiteral() || c->isTempVar(), "toTseitinCNF: c is not a literal or temp var");
                        return c;
                    }
                    else{
                        // multiple children
                        std::vector<std::shared_ptr<DAGNode>> eq_results;
                        std::shared_ptr<DAGNode> first = completed(expr->getChild(0));

                        for(size_t i = 1; i < expr->getChildrenSize(); i++){
                            std::shared_ptr<DAGNode> next = completed(expr->getChild(i));
                            eq_results.emplace_back(toTseitinEq(first, next, clauses));
                        }

                        // combine all equalities using AND
                        std::shared_ptr<DAGNode> result = mkTempVar(SortManager::BOOL_SORT);

                        // add the equivalence relation clauses
                        // result -> (eq1 ∧ eq2 ∧ ... ∧ eqn)
                        // => ¬result ∨ (eq1 ∧ eq2 ∧ ... ∧ eqn)
                        // => (¬result ∨ eq1) ∧ (¬result ∨ eq2) ∧ ... ∧ (¬result ∨ eqn)
                        for(auto& eq : eq_results){
                            clauses.emplace_back(mkOr({mkNot(result), eq}));
                        }

                        // (eq1 ∧ eq2 ∧ ... ∧ eqn) -> result
                        // => ¬(eq1 ∧ eq2 ∧ ... ∧ eqn) ∨ result
                        // => (¬eq1 ∨ ¬eq2 ∨ ... ∨ ¬eqn) ∨ result
                        std::vector<std::shared_ptr<DAGNode>> or_children;
                        for(auto& eq : eq_results){
                            or_children.emplace_back(mkNot(eq));
                        }
                        or_children.emplace_back(result);
                        clauses.emplace_back(mkOr(or_children));

                        visited[expr] = result;
                        condAssert(result->isLiteral() || result->isTempVar(), "toTseitinCNF: result is not a literal or temp var");
                        return result;
                    }
                }
            }
            else if(expr->isDistinct() && expr->getChild(0)->getSort()->isBool() && expr->getChild(1)->getSort()->isBool()){
                // ensure all children are boolean
                bool all_bool = true;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    if(!expr->getChild(i)->getSort()->isBool()){
                        all_bool = false;
                        break;
                    }
                }

                if(all_bool){
                    // handle boolean inequality
                    if(expr->getChildrenSize() == 1){
                        // single child, meaningless, return true
                        err_all(ERROR_TYPE::ERR_TYPE_MIS, "distinct with 1 variable is meaningless");
                        return mkTrue();
                    }
                    else if(expr->getChildrenSize() == 2){
                        // two children
                        std::shared_ptr<DAGNode> a = completed(expr->getChild(0));
                        std::shared_ptr<DAGNode> b = completed(expr->getChild(1));
                        std::shared_ptr<DAGNode> c = toTseitinDistinct(a, b, clauses);
                        visited[expr] = c;
                        condAssert(c->isLiteral() || c->isTempVar(), "toTseitinCNF: c is not a literal or temp var");
                        return c;
                    }
                    else{
                        // for boolean variables, distinct with more than 2 variables is always unsatisfiable
                        // because boolean values can only be true or false
                        // std::cerr << "toTseitinCNF: distinct with more than 2 variables is always unsatisfiable" << std::endl;
                        return mkFalse();
                    }
                }
            }
            else if(expr->isIte() && expr->getChild(1)->getSort()->isBool() && expr->getChild(2)->getSort()->isBool()){
                // handle condition expression: if a then b else c
                std::shared_ptr<DAGNode> a = completed(expr->getChild(0));
                std::shared_ptr<DAGNode> b = completed(expr->getChild(1));
                std::shared_ptr<DAGNode> c = completed(expr->getChild(2));
                std::shared_ptr<DAGNode> d = mkTempVar(SortManager::BOOL_SORT);

                // add clause: (¬d ∨ ¬a ∨ b) - when a is true, d must be the same as b
                clauses.emplace_back(mkOr({mkNot(d), mkNot(a), b}));

                // add clause: (¬d ∨ a ∨ c) - when a is false, d must be the same as c
                clauses.emplace_back(mkOr({mkNot(d), a, c}));

                // add clause: (d ∨ ¬a ∨ ¬b) - when a is true and b is true, d must be true
                clauses.emplace_back(mkOr({d, mkNot(a), mkNot(b)}));

                // add clause: (d ∨ a ∨ ¬c) - when a is false and c is false, d must be true
                clauses.emplace_back(mkOr({d, a, mkNot(c)}));

                visited[expr] = d;
                condAssert(d->isLiteral() || d->isTempVar(), "toTseitinCNF: d is not a literal or temp var");
                return d;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "unsupported node type: " + kindToString(expr->getKind()));
                return mkFalse();
            }

            return expr;

        };
        return conversionPostorder(expr, visited, dependencies, finish);
    }

    bool Parser::isCNF(std::shared_ptr<DAGNode> expr){
        if(expr->isAnd()){
            return isCNF(expr->getChildren());
        }
        else if(expr->isOr()){
            for(size_t i=0;i<expr->getChildrenSize();i++){
                if(!expr->getChild(i)->isLiteral()){
                    return false;
                }
            }
            return true;
        }
        else if(expr->isLiteral()){
            return true;
        }
        else{
            return false;
        }
    }

    bool Parser::isCNF(std::vector<std::shared_ptr<DAGNode>> exprs){

        // check whether it is already a CNF
        bool is_cnf = true;
        for(auto& expr : exprs){
            if(expr->isOr()){
                // a or b or not c or ...
                for(size_t i=0;i<expr->getChildrenSize();i++){
                    if(!expr->getChild(i)->isLiteral()){
                        is_cnf = false;
                        break;
                    }
                }
            }
            else if(expr->isLiteral()){
                // a
                continue;
            }
            else{
                is_cnf = false;
                break;
            }
        }
        return is_cnf;
    }

    bool Parser::eliminateTopContinuousAnd(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs){
        // eliminate continuous and on the top level
        bool is_changed = false;
        std::vector<std::shared_ptr<DAGNode>> eli_exprs;
        for(auto& expr : exprs){
            if(expr->isAnd()){
                // if it is an and, eliminate the continuous and on the top level
                std::stack<std::shared_ptr<DAGNode>> stack;
                stack.push(expr);
                while(!stack.empty()){
                    auto current = stack.top();
                    stack.pop();
                    if(current->isAnd()){
                        for(size_t i=0;i<current->getChildrenSize();i++){
                            stack.push(current->getChild(i));
                        }
                    } else {
                        // not and, add to eli_exprs
                        eli_exprs.push_back(current);
                    }
                }
                is_changed = true;
            }
            else{
                eli_exprs.emplace_back(expr);
            }
        }
        new_exprs = eli_exprs;
        return is_changed;
    }

    bool Parser::eliminateContinuousOr(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs){
        // eliminate continuous or on the top level
        bool is_changed = false;
        std::vector<std::shared_ptr<DAGNode>> eli_exprs;

        for(auto& expr : exprs){
            if(expr->isOr()){
                // if it is an or, eliminate the continuous or on the top level
                std::vector<std::shared_ptr<DAGNode>> or_children;
                std::stack<std::shared_ptr<DAGNode>> stack;

                // push all children of the or to the stack
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    stack.push(expr->getChild(i));
                }

                // expand all nested ors
                while(!stack.empty()){
                    auto current = stack.top();
                    stack.pop();

                    if(current->isOr()){
                        // if the child is also an or, continue expanding
                        for(size_t i = 0; i < current->getChildrenSize(); i++){
                            stack.push(current->getChild(i));
                        }
                        is_changed = true;
                    } else {
                        // not or, add to children list
                        or_children.push_back(current);
                    }
                }

                // create a new or expression
                if(is_changed){
                    eli_exprs.emplace_back(mkOr(or_children));
                }
                else{
                    eli_exprs.emplace_back(expr);
                }
            } else {
                // not or, add to children list
                eli_exprs.emplace_back(expr);
            }
        }

        new_exprs = eli_exprs;
        return is_changed;
    }

    bool Parser::eliminateTopRedandancy(std::vector<std::shared_ptr<DAGNode>> exprs, std::vector<std::shared_ptr<DAGNode>>& new_exprs){
        // eliminate continuous and and continuous or on the top level
        bool is_changed = false;
        while(true){
            bool cur_is_changed = false;
            std::vector<std::shared_ptr<DAGNode>> eli_exprs;
            cur_is_changed = eliminateTopContinuousAnd(exprs, eli_exprs) || cur_is_changed;
            exprs = eli_exprs;

            eli_exprs.clear();
            cur_is_changed = eliminateContinuousOr(exprs, eli_exprs) || cur_is_changed;
            exprs = eli_exprs;

            if(!cur_is_changed){
                break;
            }
            condAssert(cur_is_changed, "eliminateTopRedandancy: cur_is_changed is false");
            is_changed = true;
        }
        new_exprs = exprs;
        return is_changed;
    }

    // Encode a formula that sits in asserted (top-level, positive) position.
    // The root connective needs no Tseitin definition variable: conjunctions
    // split into independently asserted conjuncts, literals become unit
    // clauses, and a disjunction/xor/implication/iff root is emitted as its
    // direct clausal form. Only nested boolean structure goes through
    // toTseitinCNF and receives definition variables.
    void Parser::assertTopCNF(std::shared_ptr<DAGNode> expr,
                              std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited,
                              std::vector<std::shared_ptr<DAGNode>>& clauses) {
        std::vector<ConversionNode> pending{expr};
        while(!pending.empty()) {
            auto expr = std::move(pending.back()); pending.pop_back();

            if(expr->isLet()){
                pending.push_back(expandLet(expr));
                continue;
            }
            if(expr->isAtom()){
                // map the atom to its boolean abstraction literal (no clauses emitted)
                clauses.emplace_back(toTseitinCNF(expr, visited, clauses));
                continue;
            }
            if(expr->isLiteral()){
                if(expr->isTrue()){
                    continue; // asserting true adds no constraint
                }
                clauses.emplace_back(expr);
                continue;
            }
            if(expr->isAnd()){
                // each conjunct is asserted independently
                for(size_t i = expr->getChildrenSize(); i > 0; --i){
                    pending.push_back(expr->getChild(i - 1));
                }
                continue;
            }
            if(expr->isNot()){
                // NNF pushes negation onto atoms; an unabstracted ¬atom lands here
                std::shared_ptr<DAGNode> lit = toTseitinCNF(expr->getChild(0), visited, clauses);
                clauses.emplace_back(mkNot(lit));
                continue;
            }
            if(expr->isOr()){
                // an asserted disjunction is itself a single clause
                std::vector<std::shared_ptr<DAGNode>> lits;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    lits.emplace_back(toTseitinCNF(expr->getChild(i), visited, clauses));
                }
                clauses.emplace_back(mkOr(lits));
                continue;
            }
            if(expr->isXor()){
                // fold all but the last operand through Tseitin, then assert the
                // final pair directly: r xor l <=> (r or l) and (¬r or ¬l)
                std::vector<std::shared_ptr<DAGNode>> lits;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    lits.emplace_back(toTseitinCNF(expr->getChild(i), visited, clauses));
                }
                if(lits.size() == 1){
                    clauses.emplace_back(lits[0]);
                    continue;
                }
                std::shared_ptr<DAGNode> r = lits[0];
                for(size_t i = 1; i + 1 < lits.size(); i++){
                    r = toTseitinXor(r, lits[i], clauses);
                }
                std::shared_ptr<DAGNode> last = lits.back();
                clauses.emplace_back(mkOr({r, last}));
                clauses.emplace_back(mkOr({mkNot(r), mkNot(last)}));
                continue;
            }
            if(expr->isImplies()){
                // (=> a1 ... an b) asserted is the single clause ¬a1 ∨ ... ∨ ¬an ∨ b
                std::vector<std::shared_ptr<DAGNode>> lits;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    lits.emplace_back(toTseitinCNF(expr->getChild(i), visited, clauses));
                }
                if(lits.size() == 1){
                    clauses.emplace_back(lits[0]);
                    continue;
                }
                std::vector<std::shared_ptr<DAGNode>> or_children;
                for(size_t i = 0; i + 1 < lits.size(); i++){
                    or_children.emplace_back(mkNot(lits[i]));
                }
                or_children.emplace_back(lits.back());
                clauses.emplace_back(mkOr(or_children));
                continue;
            }
            if(expr->isEq() && expr->getChildrenSize() >= 2){
                bool all_bool = true;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    if(!expr->getChild(i)->getSort()->isBool()){
                        all_bool = false;
                        break;
                    }
                }
                if(all_bool){
                    // asserted iff chain: a1 = ai for all i, two binary clauses each
                    std::vector<std::shared_ptr<DAGNode>> lits;
                    for(size_t i = 0; i < expr->getChildrenSize(); i++){
                        lits.emplace_back(toTseitinCNF(expr->getChild(i), visited, clauses));
                    }
                    for(size_t i = 1; i < lits.size(); i++){
                        clauses.emplace_back(mkOr({mkNot(lits[0]), lits[i]}));
                        clauses.emplace_back(mkOr({lits[0], mkNot(lits[i])}));
                    }
                    continue;
                }
            }
            if(expr->isDistinct() && expr->getChildrenSize() == 2 &&
               expr->getChild(0)->getSort()->isBool() && expr->getChild(1)->getSort()->isBool()){
                std::shared_ptr<DAGNode> a = toTseitinCNF(expr->getChild(0), visited, clauses);
                std::shared_ptr<DAGNode> b = toTseitinCNF(expr->getChild(1), visited, clauses);
                clauses.emplace_back(mkOr({a, b}));
                clauses.emplace_back(mkOr({mkNot(a), mkNot(b)}));
                continue;
            }
            // anything else: define the subformula and assert its literal
            clauses.emplace_back(toTseitinCNF(expr, visited, clauses));
        }
    }

    // convert a list of expressions to CNF (a large AND node, whose children are all OR clauses)
    std::shared_ptr<DAGNode> Parser::toCNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
        // make a large AND node -> the same atom will use the same variable
        // assume exprs is a vector of assertions, so we can first collect all top atoms

        // rebuild the maps
        cnf_atom_map.clear();
        cnf_bool_var_map.clear();
        cnf_map.clear();

        std::vector<std::shared_ptr<DAGNode>> first_exprs;
        // simply conversions first
        for(auto& expr : exprs){
            // expand let
            if(expr->isLet()){
                expr = expandLet(expr);
            }
            // convert to NNF first
            expr = toNNF(expr);
            first_exprs.emplace_back(expr);
        }
        exprs = first_exprs;

        // eliminate top level redandancy
        std::vector<std::shared_ptr<DAGNode>> new_exprs;
        bool is_changed = eliminateTopRedandancy(exprs, new_exprs);
        if(is_changed){
            exprs = new_exprs;
        }

        // handle empty expressions
        if(exprs.size() == 0){
            return mkTrue();
        }

        // check if it is already a CNF (structure-wise)
        bool already_cnf = isCNF(exprs);

        // collect all non-boolean variable atoms (including nested ones)
        std::unordered_set<std::shared_ptr<DAGNode>> atoms;
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        for(auto& expr : exprs){
            collectAtoms(expr, atoms, visited);
        }

        // create a new variable for each non-boolean variable atom
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> atom_map;
        std::vector<std::shared_ptr<DAGNode>> new_children;
        for(auto& atom : atoms){
            if(!atom->isVBool()){
                // it is an atom, but not a boolean variable
                std::shared_ptr<DAGNode> new_var = mkTempVar(SortManager::BOOL_SORT);
                new_children.emplace_back(new_var);
                // add to cnf_map
                std::shared_ptr<DAGNode> not_atom = mkNot(atom);
                std::shared_ptr<DAGNode> not_new_var = mkNot(new_var);
                cnf_map[atom] = new_var;
                cnf_map[not_atom] = not_new_var;
                atom_map[atom] = new_var;
                atom_map[not_atom] = not_new_var;

                cnf_atom_map[new_var] = atom;
                cnf_bool_var_map[atom] = new_var;
                cnf_atom_map[not_new_var] = not_atom;
                cnf_bool_var_map[not_atom] = not_new_var;
            }
        }

        // replace atoms with new variables in all expressions
        new_exprs.clear();
        for(auto& expr : exprs){
            if(atom_map.size() != 0){
                new_exprs.emplace_back(replaceAtoms(expr, atom_map));
            }
            else{
                new_exprs.emplace_back(expr);
            }
        }

        std::shared_ptr<DAGNode> result = mkAnd(new_exprs);
        std::shared_ptr<DAGNode> cnf;

        // if it is already a CNF, no need to convert again
        if(already_cnf){
            cnf = result;
        }
        else{
            // convert to CNF
            cnf = toCNF(result);
        }

        // Note: new_children contains the Tseitin variables for atoms, but these should NOT
        // be added as independent clauses. The atom definitions are handled implicitly
        // through the cnf_atom_map and cnf_bool_var_map mappings. The CNF formula already
        // contains all necessary clauses after Tseitin transformation.
        // So we don't need to add new_children to the CNF result.

        // add to cnf_map
        cnf_map[result] = cnf;
        return cnf;
    }

    // convert a single expression to CNF
    std::shared_ptr<DAGNode> Parser::toCNF(std::shared_ptr<DAGNode> expr) {
        if(cnf_map.find(expr) != cnf_map.end()){
            return cnf_map[expr];
        }

        // expand let if needed
        if(expr->isLet()){
            expr = expandLet(expr);
        }

        // convert to NNF first
        expr = toNNF(expr);

        // check if it is already a CNF (structure-wise)
        bool already_cnf = isCNF(expr);

        // collect all non-boolean variable atoms (including nested ones)
        std::unordered_set<std::shared_ptr<DAGNode>> atoms;
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        collectAtoms(expr, atoms, visited);

        // create a new variable for each non-boolean variable atom
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> atom_map;
        std::vector<std::shared_ptr<DAGNode>> new_children;
        for (auto& atom : atoms) {
            if(!atom->isVBool()){
                // it is an atom, but not a boolean variable
                std::shared_ptr<DAGNode> new_var = mkTempVar(SortManager::BOOL_SORT);
                new_children.emplace_back(new_var);
                // add to cnf_map
                std::shared_ptr<DAGNode> not_atom = mkNot(atom);
                std::shared_ptr<DAGNode> not_new_var = mkNot(new_var);
                cnf_map[atom] = new_var;
                cnf_map[not_atom] = not_new_var;
                atom_map[atom] = new_var;
                atom_map[not_atom] = not_new_var;

                cnf_atom_map[new_var] = atom;
                cnf_bool_var_map[atom] = new_var;
                cnf_atom_map[not_new_var] = not_atom;
                cnf_bool_var_map[not_atom] = not_new_var;
            }
        }

        // replace atoms with new variables
        std::shared_ptr<DAGNode> new_expr = expr;
        if(atom_map.size() != 0){
            new_expr = replaceAtoms(expr, atom_map);
        }

        std::shared_ptr<DAGNode> cnf;

        // if it is already a CNF, no need to convert again
        if(already_cnf){
            cnf = new_expr;
        }
        else{
            // convert to CNF: the asserted root (and any top-level conjunction)
            // is encoded directly; only nested structure gets Tseitin variables
            std::vector<std::shared_ptr<DAGNode>> clauses;
            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
            assertTopCNF(new_expr, visited, clauses);

            if(clauses.empty()){
                cnf = mkTrue();
            }
            else if (clauses.size() == 1) {
                // if there is only one clause, return it directly
                cnf = clauses[0];
            }
            else{
                // otherwise, create an AND node, containing all OR clauses
                cnf = mkAnd(clauses);
            }
        }

        // Note: new_children contains the Tseitin variables for atoms, but these should NOT
        // be added as independent clauses. The atom definitions are handled implicitly
        // through the cnf_atom_map and cnf_bool_var_map mappings. The CNF formula already
        // contains all necessary clauses after Tseitin transformation.
        // So we don't need to add new_children to the CNF result.

        cnf_map[expr] = cnf;
        return cnf;
    }

    // convert a list of expressions to DNF (a large OR node, whose children are all AND terms)
    std::shared_ptr<DAGNode> Parser::toDNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
        std::shared_ptr<DAGNode> result = mkAnd(exprs);
        std::shared_ptr<DAGNode> dnf = toDNF(result);
        dnf_map[result] = dnf;
        return dnf;
    }

    // convert a single expression to DNF
    std::shared_ptr<DAGNode> Parser::toDNF(std::shared_ptr<DAGNode> expr) {
        // eliminate xor, implies, ite, eq, distinct
        expr = toDNFEliminateAll(expr);
        expr = toNNF(expr);
        std::shared_ptr<DAGNode> dnf = applyDNFDistributiveLaw(expr);
        dnf_map[expr] = dnf;
        return dnf;
    }

    // eliminate xor, implies, ite, eq, distinct
    std::shared_ptr<DAGNode> Parser::toDNFEliminateAll(std::shared_ptr<DAGNode> expr){
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        bool is_changed = true;
        while(is_changed){
            is_changed = false;
            expr = toDNFEliminateAll(expr, visited, is_changed);
        }
        return expr;
    }

    std::shared_ptr<DAGNode> Parser::toDNFEliminateAll(std::shared_ptr<DAGNode> expr,
                                                        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited,
                                                        bool& is_changed){
        ConversionCache expanded;
        const auto dependencies = [&](const ConversionNode& node) {
            if(node->isLiteral() || node->isAtom() || node->isTempVar()) return std::vector<ConversionNode>{};
            if(node->isLet()) {
                expanded[node] = expandLet(node);
                return std::vector<ConversionNode>{expanded.at(node)};
            }
            return node->getChildren();
        };
        const auto completed = [&](const ConversionNode& node, bool& changed) {
            auto result = visited.at(node);
            changed |= result != node;
            return result;
        };
        const auto finish = [&](const ConversionNode& expr) -> ConversionNode {
            bool is_changed = false;

            if(expr->isLiteral() || expr->isAtom() || expr->isTempVar()){ return expr; }
            if(visited.find(expr) != visited.end()){
                return visited[expr];
            }

            if(expr->isLet()){
                std::shared_ptr<DAGNode> result = completed(expanded.at(expr), is_changed);
                visited[expr] = result;
                return result;
            }

            if(expr->isNot()){
                bool child_changed = false;
                std::shared_ptr<DAGNode> child = completed(expr->getChild(0), child_changed);
                if(child_changed){
                    is_changed = true;
                }
                std::shared_ptr<DAGNode> result = mkNot(child);
                visited[expr] = result;
                return result;
            }
            else if(expr->isAnd()){
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i), child_changed);
                    if(child_changed){
                        is_changed = true;
                    }
                    children.emplace_back(child);
                }
                if(is_changed){
                    std::shared_ptr<DAGNode> result = mkAnd(children);
                    visited[expr] = result;
                    return result;
                }
                else{
                    // no change, return the original expression
                    visited[expr] = expr;
                    return expr;
                }
            }
            else if(expr->isOr()){
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i), child_changed);
                    if(child_changed){
                        is_changed = true;
                    }
                    children.emplace_back(child);
                }
                if(is_changed){
                    std::shared_ptr<DAGNode> result = mkOr(children);
                    visited[expr] = result;
                    return result;
                }
                else{
                    // no change, return the original expression
                    visited[expr] = expr;
                    return expr;
                }
            }
            else if(expr->isImplies()){
                // A -> B <=> ¬A ∨ B
                std::vector<ConversionNode> disjuncts;
                for(size_t i = 0; i < expr->getChildrenSize(); ++i) {
                    auto child = completed(expr->getChild(i), is_changed);
                    disjuncts.push_back(i + 1 == expr->getChildrenSize() ? child : mkNot(child));
                }
                std::shared_ptr<DAGNode> result = mkOr(disjuncts);
                is_changed = true;
                visited[expr] = result;
                return result;
            }
            else if(expr->isIte()){
                // if a then b else c <=> (¬a ∨ b) ∧ (a ∨ c)
                std::shared_ptr<DAGNode> A = completed(expr->getChild(0), is_changed);
                std::shared_ptr<DAGNode> B = completed(expr->getChild(1), is_changed);
                std::shared_ptr<DAGNode> C = completed(expr->getChild(2), is_changed);
                std::shared_ptr<DAGNode> result = mkAnd({mkOr({mkNot(A), B}), mkOr({A, C})});
                is_changed = true;
                visited[expr] = result;
                return result;
            }
            else if(expr->isXor()){
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i), is_changed);
                    children.emplace_back(child);
                }
                std::shared_ptr<DAGNode> result = toDNFEliminateXOR(children);
                is_changed = true;
                visited[expr] = result;
                return result;
            }
            else if(expr->isEq()){
                // check if all children are boolean types
                bool all_bool = true;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    if(!expr->getChild(i)->getSort()->isBool()){
                        all_bool = false;
                        break;
                    }
                }

                if(!all_bool){
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "eq with non-boolean variables");
                    return mkFalse();
                }

                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i), child_changed);
                    if(child_changed){
                        is_changed = true;
                    }
                    children.emplace_back(child);
                }

                std::shared_ptr<DAGNode> result = toDNFEliminateEq(children);
                is_changed = true;
                visited[expr] = result;
                return result;
            }
            else if(expr->isDistinct()){
                // check if all children are boolean types
                bool all_bool = true;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    if(!expr->getChild(i)->getSort()->isBool()){
                        all_bool = false;
                        break;
                    }
                }

                if(!all_bool){
                    err_all(ERROR_TYPE::ERR_TYPE_MIS, "distinct with non-boolean variables");
                    return mkFalse();
                }

                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i), child_changed);
                    if(child_changed){
                        is_changed = true;
                    }
                    children.emplace_back(child);
                }

                // if boolean type and more than 2 variables, distinct is unsatisfiable
                if(all_bool && children.size() > 2){
                    std::shared_ptr<DAGNode> result = mkFalse();
                    is_changed = true;
                    visited[expr] = result;
                    return result;
                }

                std::shared_ptr<DAGNode> result = toDNFEliminateDistinct(children);
                is_changed = true;
                visited[expr] = result;
                return result;
            }
            else{
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "unsupported node type: " + kindToString(expr->getKind()));
                return mkFalse();
            }

        };
        auto result = conversionPostorder(expr, visited, dependencies, finish);
        is_changed |= result != expr;
        return result;
    }

    // apply DNF distributive law
    std::shared_ptr<DAGNode> Parser::applyDNFDistributiveLaw(std::shared_ptr<DAGNode> expr) {
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        std::shared_ptr<DAGNode> result = applyDNFDistributiveLawRec(expr, visited);
        return flattenDNF(result);
    }

    // flatten DNF expression, eliminate nested OR/AND
    std::shared_ptr<DAGNode> Parser::flattenDNF(std::shared_ptr<DAGNode> expr) {
        ConversionCache cache;
        return conversionPostorder(expr, cache,
            [](const ConversionNode& node) {
                return node->isOr() || node->isAnd() ? node->getChildren() : std::vector<ConversionNode>{};
            }, [&](const ConversionNode& node) {
                if(!node->isOr() && !node->isAnd()) return node;
                std::vector<ConversionNode> children;
                std::unordered_set<ConversionNode> seen;
                for(const auto& original : node->getChildren()) {
                    auto child = cache.at(original);
                    const bool flatten = node->isOr() ? child->isOr() : child->isAnd();
                    const auto terms = flatten ? child->getChildren() : std::vector<ConversionNode>{child};
                    for(const auto& term : terms) if(seen.insert(term).second) children.push_back(term);
                }
                return node->isOr() ? mkOr(children) : mkAnd(children);
            });
    }

    // Postorder implementation; the public helper name is retained for compatibility.
    std::shared_ptr<DAGNode> Parser::applyDNFDistributiveLawRec(
            std::shared_ptr<DAGNode> expr,
            std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited) {
        ConversionCache expanded;
        const auto dependencies = [&](const ConversionNode& node) {
            if(node->isLiteral() || node->isAtom() || node->isTempVar() || node->isNot()) return std::vector<ConversionNode>{};
            if(node->isLet()) {
                expanded[node] = expandLet(node);
                return std::vector<ConversionNode>{expanded.at(node)};
            }
            return node->getChildren();
        };
        const auto completed = [&](const ConversionNode& node) { return visited.at(node); };
        const auto finish = [&](const ConversionNode& expr) -> ConversionNode {


            // base case: literal or visited node
            if(expr->isLiteral() || expr->isAtom() || expr->isTempVar()) {
                return expr;
            }

            if(visited.find(expr) != visited.end()) {
                return visited[expr];
            }

            if(expr->isLet()){
                std::shared_ptr<DAGNode> result = completed(expanded.at(expr));
                visited[expr] = result;
                return result;
            }

            if(expr->isNot()) {
                // negation only appears in front of literals in NNF
                return expr;
            }
            else if(expr->isOr()) {
                // Read each completed child.
                std::vector<std::shared_ptr<DAGNode>> children;
                bool has_or_child = false;

                for(size_t i = 0; i < expr->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i));
                    if(child->isOr()) {
                        has_or_child = true;
                    }
                    children.push_back(child);
                }

                // if there are no nested OR children, return the OR node directly
                if(!has_or_child) {
                    std::shared_ptr<DAGNode> result = mkOr(children);
                    visited[expr] = result;
                    return result;
                }

                // otherwise, flatten the nested OR node
                std::vector<std::shared_ptr<DAGNode>> flattened;
                for(auto& child : children) {
                    if(child->isOr()) {
                        for(size_t j = 0; j < child->getChildrenSize(); j++) {
                            flattened.push_back(child->getChild(j));
                        }
                    } else {
                        flattened.push_back(child);
                    }
                }

                std::shared_ptr<DAGNode> result = mkOr(flattened);
                visited[expr] = result;
                return result;
            }
            else if(expr->isAnd()) {
                // Partition completed children into OR children and non-OR children.
                std::vector<std::shared_ptr<DAGNode>> andChildren;
                std::vector<std::shared_ptr<DAGNode>> orChildren;

                for(size_t i = 0; i < expr->getChildrenSize(); i++) {
                    std::shared_ptr<DAGNode> child = completed(expr->getChild(i));
                    if(child->isOr()) {
                        orChildren.push_back(child);
                    } else {
                        andChildren.push_back(child);
                    }
                }

                // if there are no OR children, return the AND node directly
                if(orChildren.empty()) {
                    std::shared_ptr<DAGNode> result = mkAnd(andChildren);
                    visited[expr] = result;
                    return result;
                }

                // Keep disjuncts as a sequence: mkOr may simplify a prefix
                // to one literal or a constant, so its children are not always
                // the next distribution operands.
                std::vector<ConversionNode> terms = orChildren.front()->getChildren();
                for(size_t i = 1; i < orChildren.size(); ++i) {
                    std::vector<ConversionNode> next;
                    for(const auto& left : terms) {
                        for(const auto& right : orChildren[i]->getChildren()) {
                            auto term = mkAnd({left, right});
                            if(!term->isFalse()) next.push_back(std::move(term));
                        }
                    }
                    terms = std::move(next);
                }
                if(!andChildren.empty()) {
                    for(auto& term : terms) {
                        auto conjuncts = andChildren;
                        conjuncts.insert(conjuncts.begin(), term);
                        term = mkAnd(conjuncts);
                    }
                }
                auto distributedOr = mkOr(terms);
                visited[expr] = distributedOr;
                return distributedOr;
            }
            else {
                // other node types (should not appear, because all complex operators have been processed through NNF conversion)
                err_all(ERROR_TYPE::ERR_TYPE_MIS, "unsupported node type in DNF conversion: " + kindToString(expr->getKind()));
                return expr;
            }

        };
        return conversionPostorder(expr, visited, dependencies, finish);
    }


    // eliminate xor
    std::shared_ptr<DAGNode> Parser::toDNFEliminateXOR(const std::vector<std::shared_ptr<DAGNode>>& children) {
        // Cancel repeated parity terms before expansion. A shared operand
        // occurring twice contributes false; its negation also toggles the
        // constant parity. Expanding first can create exponentially many
        // contradictory terms even when the final formula is constant.
        bool inverted = false;
        std::vector<ConversionNode> order;
        std::unordered_map<ConversionNode, bool> odd;
        for(auto child : children) {
            while(child->isNot()) {
                inverted = !inverted;
                child = child->getChild(0);
            }
            if(child->isTrue()) { inverted = !inverted; continue; }
            if(child->isFalse()) continue;
            auto inserted = odd.emplace(child, true);
            if(inserted.second) order.push_back(child);
            else inserted.first->second = !inserted.first->second;
        }
        std::vector<ConversionNode> operands;
        for(const auto& child : order) if(odd.at(child)) operands.push_back(child);
        if(operands.empty()) return inverted ? mkTrue() : mkFalse();
        // Left-associative parity fold; the expression grows on the heap,
        // not on the C++ call stack as the number of XOR operands increases.
        auto result = operands.front();
        for(size_t i = 1; i < operands.size(); ++i) {
            const auto& right = operands[i];
            result = mkOr({mkAnd({result, mkNot(right)}),
                           mkAnd({mkNot(result), right})});
        }
        return inverted ? mkNot(result) : result;
    }

    // eliminate eq
    std::shared_ptr<DAGNode> Parser::toDNFEliminateEq(const std::vector<std::shared_ptr<DAGNode>>& children) {
        if (children.size() <= 1) {
            return mkTrue(); // return true
        }
        std::vector<ConversionNode> equalities;
        for(size_t i = 1; i < children.size(); ++i) {
            const auto& left = children[i - 1];
            const auto& right = children[i];
            equalities.push_back(mkOr({mkAnd({left, right}),
                                       mkAnd({mkNot(left), mkNot(right)})}));
        }
        return mkAnd(equalities);
    }

    // eliminate distinct
    std::shared_ptr<DAGNode> Parser::toDNFEliminateDistinct(const std::vector<std::shared_ptr<DAGNode>>& children) {
        if (children.size() <= 1) {
            return mkTrue(); // return true
        }
        if (children.size() == 2) {
            // A ≠ B <=> (A ∧ ¬B) ∨ (¬A ∧ B)
            std::shared_ptr<DAGNode> A = children[0];
            std::shared_ptr<DAGNode> B = children[1];
            return mkOr({
                mkAnd({A, mkNot(B)}),
                mkAnd({mkNot(A), B})
            });
        }

        // multiple variables distinct: at least one pair is distinct
        // for boolean variables, more than 2 variables distinct is unsatisfiable
        return mkFalse(); // boolean domain, more than 2 variables distinct is unsatisfiable
    }

    // convert a list of expressions to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::vector<std::shared_ptr<DAGNode>> exprs) {
        std::shared_ptr<DAGNode> target = mkAnd(exprs);
        std::shared_ptr<DAGNode> result = toNNF(target);
        nnf_map[target] = result;
        return result;
    }

    // convert a single expression to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::shared_ptr<DAGNode> expr, bool is_not) {
        struct Key { ConversionNode node; bool negative; };
        struct Frame { Key key; std::vector<Key> children; size_t next = 0; };
        std::unordered_map<ConversionNode, std::array<ConversionNode, 2>> cache;
        ConversionCache expanded;
        const auto dependencies = [&](const Key& key) {
            std::vector<Key> children;
            auto node = key.node;
            if(node->isCBool() || node->isVBool()) return children;
            if(node->isLet()) {
                expanded[node] = expandLet(node);
                children.push_back({expanded.at(node), key.negative});
            } else if(node->isNot()) {
                children.push_back({node->getChild(0), !key.negative});
            } else if(node->isAnd() || node->isOr()) {
                for(const auto& child : node->getChildren()) children.push_back({child, key.negative});
            } else if(node->isImplies()) {
                for(size_t i = 0; i < node->getChildrenSize(); ++i) {
                    children.push_back({node->getChild(i),
                        i + 1 == node->getChildrenSize() ? key.negative : !key.negative});
                }
            } else if(node->isIte() && node->getChild(1)->getSort()->isBool()) {
                children = {{node->getChild(0), false}, {node->getChild(1), key.negative},
                            {node->getChild(0), true}, {node->getChild(2), key.negative}};
            }
            return children;
        };
        const auto completed = [&](const Key& key) { return cache.at(key.node)[key.negative]; };
        std::vector<Frame> pending{{{expr, is_not}, dependencies({expr, is_not})}};
        std::unordered_map<const DAGNode*, std::array<bool, 2>> active;
        active[expr.get()][is_not] = true;
        while(!pending.empty()) {
            auto& frame = pending.back();
            if(frame.next < frame.children.size()) {
                const auto child = frame.children[frame.next++];
                if(cache[child.node][child.negative]) continue;
                condAssert(!active[child.node.get()][child.negative], "cyclic expression in NNF conversion");
                active[child.node.get()][child.negative] = true;
                pending.push_back({child, dependencies(child)});
                continue;
            }
            auto node = frame.key.node;
            const bool negative = frame.key.negative;
            ConversionNode result;
            if(node->isLet() || node->isNot()) {
                result = completed(frame.children[0]);
            } else if(node->isAnd() || node->isOr() || node->isImplies()) {
                std::vector<ConversionNode> children;
                for(const auto& child : frame.children) children.push_back(completed(child));
                const bool conjunction = node->isImplies() ? negative : node->isAnd() != negative;
                result = conjunction ? mkAnd(children) : mkOr(children);
            } else if(node->isIte() && node->getChild(1)->getSort()->isBool()) {
                result = mkOr({mkAnd({completed(frame.children[0]), completed(frame.children[1])}),
                               mkAnd({completed(frame.children[2]), completed(frame.children[3])})});
            } else {
                result = negative ? mkNot(node) : node;
            }
            cache[node][negative] = result;
            if(!negative && node->isLet()) nnf_map[node] = result;
            active[node.get()][negative] = false;
            pending.pop_back();
        }
        return cache.at(expr)[is_not];
    }

    // convert a single expression to NNF
    std::shared_ptr<DAGNode> Parser::toNNF(std::shared_ptr<DAGNode> expr) {
        if(nnf_map.find(expr) != nnf_map.end()){
            return nnf_map[expr];
        }
        std::shared_ptr<DAGNode> result = toNNF(expr, false);
        nnf_map[expr] = result;
        return result;
    }

    std::shared_ptr<DAGNode> Parser::splitOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set){
        bool is_changed = false;
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        context_.split_lemmas.clear();
        return splitOp(expr, op_set, is_changed, visited);
    }

    std::shared_ptr<DAGNode> Parser::splitOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set, bool& is_changed, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited){
        const auto completed = [&](const ConversionNode& node, bool& changed) {
            auto result = visited.at(node); changed |= result != node; return result;
        };
        const auto finish = [&](const ConversionNode& expr) -> ConversionNode {
            bool is_changed = false;

            if(visited.find(expr) != visited.end()){
                return visited[expr];
            }
            if(op_set.find(expr->getKind()) != op_set.end()){
                if(expr->isLt() || expr->isGt() || expr->isEq()){
                    // std::cerr << "splitArithComp: " << expr->toString() << " is not supported"<< std::endl;
                    is_changed = false;
                    return expr;
                }
                else if(expr->isGe()){
                    is_changed = true;
                    std::shared_ptr<DAGNode> left = expr->getChild(0);
                    std::shared_ptr<DAGNode> right = expr->getChild(1);
                    std::shared_ptr<DAGNode> gt = mkGt(left, right);
                    std::shared_ptr<DAGNode> eq = mkEq(left, right);
                    context_.split_lemmas.emplace_back(mkOr({
                        mkNot(gt),
                        mkNot(eq)
                    }));
                    return mkOr({
                        gt,
                        eq
                    });
                }
                else if(expr->isLe()){
                    is_changed = true;
                    std::shared_ptr<DAGNode> left = expr->getChild(0);
                    std::shared_ptr<DAGNode> right = expr->getChild(1);
                    std::shared_ptr<DAGNode> lt = mkLt(left, right);
                    std::shared_ptr<DAGNode> eq = mkEq(left, right);
                    context_.split_lemmas.emplace_back(mkOr({
                        mkNot(lt),
                        mkNot(eq)
                    }));
                    return mkOr({
                        lt,
                        eq
                    });
                }
                else if(expr->isDistinct()){
                    is_changed = true;
                    std::shared_ptr<DAGNode> left = expr->getChild(0);
                    std::shared_ptr<DAGNode> right = expr->getChild(1);
                    std::shared_ptr<DAGNode> lt = mkLt(left, right);
                    std::shared_ptr<DAGNode> gt = mkGt(left, right);
                    context_.split_lemmas.emplace_back(mkOr({
                        mkNot(lt),
                        mkNot(gt)
                    }));
                    return mkOr({
                        lt,
                        gt
                    });
                }
                else{
                    // std::cerr << "splitArithComp: " << expr->toString() << " is not supported"<< std::endl;
                    is_changed = false;
                    return expr;
                }
            }
            else{
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = expr->getChild(i);
                    std::shared_ptr<DAGNode> split_child = completed(child, child_changed);
                    is_changed = is_changed || child_changed;
                    children.emplace_back(split_child);
                }
                if(is_changed){
                    std::shared_ptr<DAGNode> result = mkOper(expr->getSort(), expr->getKind(), children);
                    visited[expr] = result;
                    return result;
                }
            }
            visited[expr] = expr;
            return expr;

        };
        auto result = conversionPostorder(expr, visited, [&](const ConversionNode& node) {
            return (op_set.count(node->getKind())) ? std::vector<ConversionNode>{} : node->getChildren();
        }, finish);
        is_changed |= result != expr;
        return result;
    }

    std::vector<std::shared_ptr<DAGNode>> Parser::getSplitLemmas(){
        return context_.getSplitLemmas();
    }

    // remove all the nodes in the expression
    std::shared_ptr<DAGNode> Parser::remove(std::shared_ptr<DAGNode> expr, const std::unordered_set<std::shared_ptr<DAGNode>>& nodes){
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        return remove(expr, nodes, visited);
    }

    std::shared_ptr<DAGNode> Parser::remove(std::shared_ptr<DAGNode> expr, const std::unordered_set<std::shared_ptr<DAGNode>>& nodes, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited){
        return conversionPostorder(expr, visited, [&](const ConversionNode& node) {
            return nodes.count(node) ? std::vector<ConversionNode>{} : node->getChildren();
        }, [&](const ConversionNode& node) {
            if(nodes.count(node)) return NodeManager::NULL_NODE;
            bool changed = false;
            std::vector<ConversionNode> children;
            for(const auto& child : node->getChildren()) {
                auto result = visited.at(child);
                changed |= result != child;
                if(result != NodeManager::NULL_NODE) children.push_back(result);
            }
            return changed ? mkOper(node->getSort(), node->getKind(), children) : node;
        });
    }

    std::shared_ptr<DAGNode> Parser::binarizeOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set){
        bool is_changed = false;
        std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>> visited;
        return binarizeOp(expr, op_set, is_changed, visited);
    }

    std::shared_ptr<DAGNode> Parser::binarizeOp(std::vector<std::shared_ptr<DAGNode>> exprs, const std::unordered_set<NODE_KIND>& op_set){
        return binarizeOp(mkAnd(exprs), op_set);
    }

    std::shared_ptr<DAGNode> Parser::binarizeOp(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& op_set, bool& is_changed, std::unordered_map<std::shared_ptr<DAGNode>, std::shared_ptr<DAGNode>>& visited){
        const auto completed = [&](const ConversionNode& node, bool& changed) {
            auto result = visited.at(node); changed |= result != node; return result;
        };
        const auto finish = [&](const ConversionNode& expr) -> ConversionNode {
            bool is_changed = false;

            if(visited.find(expr) != visited.end()){
                return visited[expr];
            }
            if(op_set.find(expr->getKind()) != op_set.end()){

                if(expr->isEq()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (= a b c) -> (and (= a b) (= a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            children.emplace_back(mkEq({expr->getChild(i), expr->getChild(i+1)}));
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else if(expr->isDistinct()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (distinct a b c) -> (and (distinct a b) (distinct a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            for(size_t j = i + 1; j < expr->getChildrenSize(); j++){
                                children.emplace_back(mkDistinct({expr->getChild(i), expr->getChild(j)}));
                            }
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else if(expr->isGe()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (>= a b c) -> (and (>= a b) (>= a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            children.emplace_back(mkGe({expr->getChild(i), expr->getChild(i+1)}));
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else if(expr->isLe()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (<= a b c) -> (and (<= a b) (<= a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            children.emplace_back(mkLe({expr->getChild(i), expr->getChild(i+1)}));
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else if(expr->isGt()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (> a b c) -> (and (> a b) (> a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            children.emplace_back(mkGt({expr->getChild(i), expr->getChild(i+1)}));
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else if(expr->isLt()){
                    if(expr->getChildrenSize() > 2){
                        is_changed = true;
                        // (< a b c) -> (and (< a b) (< a c))
                        std::vector<std::shared_ptr<DAGNode>> children;
                        for(size_t i = 0; i < expr->getChildrenSize() - 1; i++){
                            children.emplace_back(mkLt({expr->getChild(i), expr->getChild(i+1)}));
                        }
                        std::shared_ptr<DAGNode> result = mkAnd(children);
                        visited[expr] = result;
                        return result;
                    }
                    else{
                        // nothing to do
                        is_changed = false;
                    }
                }
                else{
                    // not supported now
                    std::vector<std::shared_ptr<DAGNode>> children;
                    for(size_t i = 0; i < expr->getChildrenSize(); i++){
                        bool child_changed = false;
                        std::shared_ptr<DAGNode> child = expr->getChild(i);
                        std::shared_ptr<DAGNode> binarized_child = completed(child, child_changed);
                        is_changed = is_changed || child_changed;
                        children.emplace_back(binarized_child);
                    }
                    if(is_changed){
                        std::shared_ptr<DAGNode> result = mkOper(expr->getSort(), expr->getKind(), children);
                        visited[expr] = result;
                        return result;
                    }
                }
            }
            else{
                // not in op_set, just go on recursion
                std::vector<std::shared_ptr<DAGNode>> children;
                for(size_t i = 0; i < expr->getChildrenSize(); i++){
                    bool child_changed = false;
                    std::shared_ptr<DAGNode> child = expr->getChild(i);
                    std::shared_ptr<DAGNode> binarized_child = completed(child, child_changed);
                    is_changed = is_changed || child_changed;
                    children.emplace_back(binarized_child);
                }
                if(is_changed){
                    std::shared_ptr<DAGNode> result = mkOper(expr->getSort(), expr->getKind(), children);
                    visited[expr] = result;
                    return result;
                }
            }
            visited[expr] = expr;
            return expr;

        };
        auto result = conversionPostorder(expr, visited, [&](const ConversionNode& node) {
            return (op_set.count(node->getKind()) && (node->isEq() || node->isDistinct() || node->isGe() || node->isLe() || node->isGt() || node->isLt())) ? std::vector<ConversionNode>{} : node->getChildren();
        }, finish);
        is_changed |= result != expr;
        return result;
    }

    std::shared_ptr<DAGNode> Parser::binarizeOp(std::shared_ptr<DAGNode> expr){
        return binarizeOp(expr, {NODE_KIND::NT_EQ, NODE_KIND::NT_EQ_BOOL, NODE_KIND::NT_EQ_OTHER,
                                NODE_KIND::NT_DISTINCT, NODE_KIND::NT_DISTINCT_BOOL, NODE_KIND::NT_DISTINCT_OTHER,
                                NODE_KIND::NT_GE, NODE_KIND::NT_LE, NODE_KIND::NT_GT, NODE_KIND::NT_LT});
    }

    std::shared_ptr<DAGNode> Parser::binarizeOp(std::vector<std::shared_ptr<DAGNode>> exprs){
        return binarizeOp(mkAnd(exprs), {NODE_KIND::NT_EQ, NODE_KIND::NT_EQ_BOOL, NODE_KIND::NT_EQ_OTHER,
                                        NODE_KIND::NT_DISTINCT, NODE_KIND::NT_DISTINCT_BOOL, NODE_KIND::NT_DISTINCT_OTHER,
                                        NODE_KIND::NT_GE, NODE_KIND::NT_LE, NODE_KIND::NT_GT, NODE_KIND::NT_LT});
    }

    bool Parser::hasSomeKinds(std::shared_ptr<DAGNode> expr, const std::unordered_set<NODE_KIND>& kinds){
        // iterative
        std::stack<std::shared_ptr<DAGNode>> node_stack;
        node_stack.push(expr);
        std::unordered_set<std::shared_ptr<DAGNode>> visited;
        while(!node_stack.empty()){
            std::shared_ptr<DAGNode> node = node_stack.top();
            node_stack.pop();
            if(visited.find(node) != visited.end()){
                continue;
            }
            if(kinds.find(node->getKind()) != kinds.end()){
                return true;
            }
            visited.insert(node);
            for(size_t i = 0; i < node->getChildrenSize(); i++){
                std::shared_ptr<DAGNode> child = node->getChild(i);
                if(visited.find(child) == visited.end()){
                    node_stack.push(child);
                }
            }
        }
        return false;
    }
}
