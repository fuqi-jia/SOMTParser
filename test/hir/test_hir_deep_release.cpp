#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <memory>
#include <cstdlib>
#include <new>
#include <atomic>
#include <thread>

#if defined(__unix__)
#include <csignal>
#include <cstring>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

static bool fail_allocation = false;

void* operator new(std::size_t bytes) {
    if (fail_allocation) { throw std::bad_alloc(); }
    if (void* pointer = std::malloc(bytes ? bytes : 1)) { return pointer; }
    throw std::bad_alloc();
}

void operator delete(void* pointer) noexcept { std::free(pointer); }
void operator delete(void* pointer, std::size_t) noexcept { std::free(pointer); }
#endif

namespace H = SOMTParser::Uir::Hir;

static H::ExprPtr chain(std::size_t depth, H::ExprPtr leaf) {
    for (std::size_t i = 0; i < depth; ++i) {
        leaf = H::mkOp(H::Op::NOT, {std::move(leaf)});
    }
    return leaf;
}

int main() {
    constexpr std::size_t depth = 200000;
    {
        // No artificial keepalive vector: releasing the root must release the
        // complete chain without a destructor call stack of the same depth.
        auto leaf = H::mkBool(true);
        std::weak_ptr<const H::Expr> observed_leaf = leaf;
        auto root = chain(depth, std::move(leaf));
        std::weak_ptr<const H::Expr> observed_root = root;
        root.reset();
        VERIFY(observed_root.expired());
        VERIFY(observed_leaf.expired());
    }
    {
        // Shared descendants owned by another model must remain unchanged.
        auto retained = chain(depth, H::mkIdent("p", H::Sort::boolean()));
        const H::Expr* first_child = retained->args[0].get();
        auto root = H::mkOp(H::Op::AND, {retained, retained});
        std::weak_ptr<const H::Expr> observed = retained;
        root.reset();
        VERIFY(!observed.expired());
        VERIFY(retained->op == H::Op::NOT);
        VERIFY(retained->args.size() == 1);
        VERIFY(retained->args[0].get() == first_child);
        retained.reset();
        VERIFY(observed.expired());
    }
    {
        // ExprPtr also permits genuinely const allocations. Reclamation must
        // not cast away const and mutate a live child's operand vector.
        auto temporary = H::mkOp(H::Op::AND, {chain(depth, H::mkBool(false))});
        H::ExprPtr root = std::make_shared<const H::Expr>(*temporary);
        temporary.reset();
        std::weak_ptr<const H::Expr> observed = root->args[0];
        root.reset();
        VERIFY(observed.expired());
    }
    {
        // Deep and wide at once, with repeated edges and an external shared
        // leaf. This grows the iterative frontier and exercises last-owner
        // transitions inside the queue, without duplicating the shared DAG.
        auto shared = H::mkIdent("still_alive", H::Sort::boolean());
        auto root = H::mkBool(false);
        std::weak_ptr<const H::Expr> observed_leaf = root;
        for (std::size_t i = 0; i < 50000; ++i) {
            std::vector<H::ExprPtr> args{shared, root};
            if (i % 31 == 0) {
                for (std::size_t j = 0; j < 16; ++j) { args.push_back(root); }
            }
            root = H::mkOp(H::Op::AND, std::move(args));
        }
        root.reset();
        VERIFY(observed_leaf.expired());
        VERIFY(shared->name == "still_alive");
        VERIFY(shared->args.empty());
    }
    {
        // Final owners can be dropped simultaneously by different threads.
        // Either thread may end up reclaiming the common suffix; neither may
        // use the other's active worklist or retain it after the drain ends.
        auto common = chain(50000, H::mkBool(true));
        std::weak_ptr<const H::Expr> observed = common;
        auto left = chain(50000, common);
        auto right = chain(50000, common);
        common.reset();
        std::atomic<bool> start{false};
        auto release = [&start](H::ExprPtr root) {
            while (!start.load(std::memory_order_acquire)) { std::this_thread::yield(); }
            root.reset();
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
        // Allocation failure while expanding the release worklist must be a
        // diagnosed resource failure, never an exception from a noexcept
        // destructor or a recursive fallback into an arbitrarily deep DAG.
        auto root = H::mkOp(H::Op::NOT, {H::mkOp(H::Op::AND,
            {H::mkBool(true), H::mkBool(false)})});
        int descriptors[2];
        VERIFY(pipe(descriptors) == 0);
        const pid_t child = fork();
        VERIFY(child >= 0);
        if (child == 0) {
            close(descriptors[0]);
            if (dup2(descriptors[1], STDERR_FILENO) < 0) { _exit(90); }
            close(descriptors[1]);
            const rlimit no_core{0, 0};
            setrlimit(RLIMIT_CORE, &no_core);
            fail_allocation = true;
            root.reset();
            _exit(91);
        }
        close(descriptors[1]);
        char message[256]{};
        const ssize_t count = read(descriptors[0], message, sizeof(message) - 1);
        close(descriptors[0]);
        int status = 0;
        VERIFY(waitpid(child, &status, 0) == child);
        VERIFY(count > 0);
        VERIFY(std::strstr(message, "HIR destruction: memory allocation failed") != nullptr);
        VERIFY(WIFSIGNALED(status));
        VERIFY(WTERMSIG(status) == SIGABRT);
    }
#endif
    return 0;
}
