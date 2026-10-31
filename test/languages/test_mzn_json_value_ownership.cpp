#include "../../languages/minizinc/src/mzn_json_value.h"
#include "test_helpers.h"

#include <atomic>
#include <memory>
#include <thread>

#if defined(__unix__)
#include <csignal>
#include <cstring>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

static thread_local bool fail_allocation = false;
void* operator new(std::size_t bytes) {
    if (fail_allocation) throw std::bad_alloc();
    if (void* pointer = std::malloc(bytes ? bytes : 1)) return pointer;
    throw std::bad_alloc();
}
void operator delete(void* pointer) noexcept { std::free(pointer); }
void operator delete(void* pointer, std::size_t) noexcept { std::free(pointer); }
#endif

using Value = SOMTParser::Lang::detail::JsonRecordNode;

static Value chain(std::size_t depth) {
    Value root;
    root.text = "17";
    for (std::size_t i = 0; i < depth; ++i) {
        Value parent;
        parent.kind = i % 2 ? Value::Kind::RECORD : Value::Kind::ARRAY;
        auto& children = i % 2 ? parent.fields : parent.elements;
        children.push_back(std::move(root));
        root = std::move(parent);
    }
    return root;
}

static Value& leaf(Value& root, std::size_t depth) {
    Value* node = &root;
    for (std::size_t i = 0; i < depth; ++i) {
        const auto& children = node->kind == Value::Kind::RECORD ? node->fields : node->elements;
        VERIFY(children.size() == 1);
        node = node->kind == Value::Kind::RECORD ? &node->fields.front() : &node->elements.front();
    }
    VERIFY(node->kind == Value::Kind::INTEGER);
    VERIFY(node->fields.empty() && node->elements.empty());
    return *node;
}

int main() {
    constexpr std::size_t depth = 200000;
    {
        auto root = chain(depth);
        Value copied(root);
        VERIFY(leaf(copied, depth).text == "17");
        leaf(copied, depth).text = "23";
        VERIFY(leaf(root, depth).text == "17");
        Value assigned = chain(10000);
        assigned = copied;
        VERIFY(leaf(assigned, depth).text == "23");
        root = std::move(assigned); // Dispose the old deep value during move assignment.
        VERIFY(leaf(root, depth).text == "23");
    }
    {
        auto root = chain(50000);
        for (std::size_t i = 0; i < 20000; ++i) {
            Value parent;
            parent.kind = Value::Kind::RECORD;
            parent.fields.push_back(std::move(root));
            if (i % 31 == 0) {
                parent.fields.resize(9);
                parent.elements.resize(7);
            }
            root = std::move(parent);
        }
        Value copied(root); // Mixed deep/wide tree: both vectors must be drained.
    }
    {
        auto left = chain(50000), right = chain(50000);
        std::atomic<bool> start{false};
        const auto release = [&start](Value root) {
            while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
            root = Value{};
        };
        std::thread first(release, std::move(left));
        std::thread second(release, std::move(right));
        start.store(true, std::memory_order_release);
        first.join(); second.join();
    }
#if defined(__unix__)
    {
        // A single chain reuses the first child buffer even under OOM.
        auto root = chain(depth);
        fail_allocation = true;
        root = Value{};
        fail_allocation = false;
    }
    {
        // The explicit frontier may allocate on branching trees. Its failure
        // is a diagnosed resource abort, with no recursive fallback.
        auto root = std::make_unique<Value>();
        root->fields.resize(1);
        root->fields.front().elements.resize(2);
        int descriptors[2];
        VERIFY(pipe(descriptors) == 0);
        const auto child = fork();
        VERIFY(child >= 0);
        if (child == 0) {
            close(descriptors[0]);
            if (dup2(descriptors[1], STDERR_FILENO) < 0) _exit(90);
            close(descriptors[1]);
            const rlimit no_core{0, 0};
            setrlimit(RLIMIT_CORE, &no_core);
            fail_allocation = true;
            root.reset();
            _exit(91);
        }
        close(descriptors[1]);
        char message[256]{};
        const auto count = read(descriptors[0], message, sizeof(message) - 1);
        close(descriptors[0]);
        int status = 0;
        VERIFY(waitpid(child, &status, 0) == child);
        VERIFY(count > 0);
        VERIFY(std::strstr(message, "MiniZinc JSON destruction: memory allocation failed"));
        VERIFY(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
    }
#endif
}
