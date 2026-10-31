#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <atomic>
#include <cstdlib>
#include <memory>
#include <new>
#include <thread>

#if defined(__unix__)
static thread_local bool fail_allocation = false;
void* operator new(std::size_t bytes) {
    if (fail_allocation) throw std::bad_alloc();
    if (void* pointer = std::malloc(bytes ? bytes : 1)) return pointer;
    throw std::bad_alloc();
}
void operator delete(void* pointer) noexcept { std::free(pointer); }
void operator delete(void* pointer, std::size_t) noexcept { std::free(pointer); }
#endif

namespace H = SOMTParser::Uir::Hir;
using SortPtr = std::shared_ptr<const H::Sort>;

static SortPtr chain(std::size_t depth, SortPtr root) {
    for (std::size_t i = 0; i < depth; ++i) {
        H::Sort parent;
        parent.kind = H::SortKind::SET;
        parent.elem = std::move(root);
        root = std::make_shared<const H::Sort>(std::move(parent));
    }
    return root;
}

int main() {
    {
        auto leaf = std::make_shared<const H::Sort>(H::Sort::boolean());
        std::weak_ptr<const H::Sort> observed = leaf;
        auto root = chain(200000, std::move(leaf));
#if defined(__unix__)
        // A pure element chain needs no new storage during destruction.
        fail_allocation = true;
#endif
        root.reset();
#if defined(__unix__)
        fail_allocation = false;
#endif
        VERIFY(observed.expired());
    }
    {
        // All three edge categories, shared edges, and genuinely const nodes.
        auto retained = chain(1000, std::make_shared<const H::Sort>(H::Sort::integer()));
        auto root = std::make_shared<const H::Sort>(H::Sort::boolean());
        std::weak_ptr<const H::Sort> observed = root;
        for (std::size_t i = 0; i < 50000; ++i) {
            H::Sort parent;
            if (i % 3 == 0) {
                parent.kind = H::SortKind::ARRAY;
                parent.index = retained;
                parent.elem = root;
            } else if (i % 3 == 1) {
                parent.kind = H::SortKind::TUPLE;
                parent.args = {retained, root, root};
            } else {
                parent.kind = H::SortKind::SET;
                parent.elem = root;
            }
            root = std::make_shared<const H::Sort>(std::move(parent));
        }
        const auto child = retained->elem;
#if defined(__unix__)
        // Branching and duplicate edges must also be allocation-free, not
        // merely the one-element chain covered above.
        fail_allocation = true;
#endif
        root.reset();
#if defined(__unix__)
        fail_allocation = false;
#endif
        VERIFY(observed.expired());
        VERIFY(retained->kind == H::SortKind::SET && retained->elem == child);
    }
    {
        auto common = chain(50000, std::make_shared<const H::Sort>(H::Sort::boolean()));
        std::weak_ptr<const H::Sort> observed = common;
        auto left = chain(50000, common);
        auto right = chain(50000, common);
        common.reset();
        std::atomic<bool> start{false};
        const auto release = [&start](SortPtr root) {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
#if defined(__unix__)
            fail_allocation = true;
#endif
            root.reset();
#if defined(__unix__)
            fail_allocation = false;
#endif
        };
        std::thread first(release, std::move(left));
        std::thread second(release, std::move(right));
        start.store(true, std::memory_order_release);
        first.join();
        second.join();
        VERIFY(observed.expired());
    }
#if defined(__unix__)
    {
        // An Array has two inline edges and no args buffer. Previously the
        // second edge allocated in the noexcept destructor and aborted THF's
        // ordinary single-allocation exception-propagation regression.
        auto root = std::make_shared<const H::Sort>(H::Sort::array(
            H::Sort::boolean(), H::Sort::integer()));
        const std::weak_ptr<const H::Sort> index = root->index, element = root->elem;
        fail_allocation = true;
        root.reset();
        fail_allocation = false;
        VERIFY(index.expired() && element.expired());
    }
#endif
    {
        auto shared = chain(2000, std::make_shared<const H::Sort>(H::Sort::boolean()));
        std::weak_ptr<const H::Sort> observed = shared;
        H::Sort a, b;
        a.kind = b.kind = H::SortKind::TUPLE;
        for (std::size_t i = 0; i < 2000; ++i) {
            a.args.push_back(shared);
            b.args.push_back(shared);
        }
        auto left = std::make_shared<const H::Sort>(a);
        auto right = std::make_shared<const H::Sort>(b);
        a.args.clear(); b.args.clear(); shared.reset();
        std::atomic<bool> start{false};
        const auto release = [&start](SortPtr root) {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
#if defined(__unix__)
            fail_allocation = true;
#endif
            root.reset();
#if defined(__unix__)
            fail_allocation = false;
#endif
        };
        std::thread first(release, std::move(left));
        std::thread second(release, std::move(right));
        std::thread reader([&]() {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
            for (std::size_t i = 0; i < 100000; ++i) {
                auto pinned = observed.lock();
                if (!pinned) break;
                VERIFY(pinned->kind == H::SortKind::SET);
                VERIFY(pinned->elem && pinned->elem->kind == H::SortKind::SET);
            }
        });
        start.store(true, std::memory_order_release);
        first.join(); second.join(); reader.join();
        VERIFY(observed.expired());
    }
    return 0;
}
