#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <atomic>
#include <cstdlib>
#include <memory>
#include <new>
#include <string>
#include <thread>
#include <vector>

using namespace SOMTParser;

namespace {
thread_local bool forbidAllocations = false;
thread_local std::size_t allocationAttempts = 0;
using Node = std::shared_ptr<DAGNode>;

Node leaf() {
    return std::make_shared<DAGNode>(SortManager::BOOL_SORT, NODE_KIND::NT_VAR,
                                     std::string("leaf"));
}
Node chain(Node root, std::size_t depth, std::size_t width = 1) {
    for (std::size_t i = 0; i < depth; ++i) {
        std::vector<Node> children(width, root);
        root = std::make_shared<DAGNode>(SortManager::BOOL_SORT,
            width == 1 ? NODE_KIND::NT_NOT : NODE_KIND::NT_AND,
            std::string(), std::move(children));
    }
    return root;
}
void releaseWithoutAllocations(Node& root) {
    allocationAttempts = 0;
    forbidAllocations = true;
    root.reset();
    forbidAllocations = false;
    VERIFY(allocationAttempts == 0);
}
}

void* operator new(std::size_t size) {
    if (forbidAllocations) {
        ++allocationAttempts;
        throw std::bad_alloc();
    }
    if (void* value = std::malloc(size ? size : 1)) return value;
    throw std::bad_alloc();
}
void* operator new[](std::size_t size) { return ::operator new(size); }
void operator delete(void* value) noexcept { std::free(value); }
void operator delete[](void* value) noexcept { std::free(value); }
void operator delete(void* value, std::size_t) noexcept { std::free(value); }
void operator delete[](void* value, std::size_t) noexcept { std::free(value); }

int main() {
    // These nodes deliberately have no NodeManager to unlink them beforehand.
    {
        auto bottom = leaf();
        std::weak_ptr<DAGNode> weak = bottom;
        auto root = chain(std::move(bottom), 100000);
        releaseWithoutAllocations(root);
        VERIFY(weak.expired());
    }
    {
        auto kept = chain(leaf(), 20000, 4);
        const auto child = kept->getChild(0);
        auto root = chain(kept, 20000, 8);
        releaseWithoutAllocations(root);
        // A separately owned descendant must retain all its original edges.
        VERIFY(kept->getChildrenSize() == 4 && kept->getChild(0) == child);
        std::weak_ptr<DAGNode> weak = kept;
        releaseWithoutAllocations(kept);
        VERIFY(weak.expired());
    }
    {
        // A copied node has fresh queue scratch and retains normal DAG sharing.
        auto original = chain(leaf(), 20000, 2);
        auto copy = std::make_shared<DAGNode>(*original);
        const auto first = original->getChild(0);
        releaseWithoutAllocations(original);
        VERIFY(copy->getChildrenSize() == 2 && copy->getChild(0) == first);
        releaseWithoutAllocations(copy);
    }
    {
        auto parser = newParser();
        std::string expression;
        for (std::size_t i = 0; i < 20000; ++i) expression += "(forall ((x Bool)) ";
        expression += "x";
        expression.append(20000, ')');
        auto escaped = parser->mkExpr(expression);
        parser.reset();
        VERIFY(escaped->getKind() == NODE_KIND::NT_FORALL);
        std::weak_ptr<DAGNode> weak = escaped;
        releaseWithoutAllocations(escaped);
        VERIFY(weak.expired());
    }
    {
        // Distinct dying roots may enqueue a shared descendant concurrently.
        auto shared = chain(leaf(), 20000, 4);
        std::weak_ptr<DAGNode> weak = shared;
        std::vector<Node> roots;
        for (int i = 0; i < 4; ++i) roots.push_back(chain(shared, 5000, 4));
        shared.reset();
        std::atomic<bool> start{false};
        std::vector<std::thread> workers;
        for (auto& root : roots) {
            workers.emplace_back([owned = std::move(root), &start]() mutable {
                while (!start.load(std::memory_order_acquire)) {}
                releaseWithoutAllocations(owned);
            });
        }
        start.store(true, std::memory_order_release);
        for (auto& worker : workers) worker.join();
        VERIFY(weak.expired());
    }
    return 0;
}
