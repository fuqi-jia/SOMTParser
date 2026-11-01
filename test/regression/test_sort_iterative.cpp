#include "somtparser/ir/sort.h"
#include "test_helpers.h"

#include <atomic>
#include <cstdlib>
#include <memory>
#include <new>
#include <stdexcept>
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
    if (void* p = std::malloc(bytes ? bytes : 1)) { return p; }
    throw std::bad_alloc();
}
void operator delete(void* p) noexcept { std::free(p); }
void operator delete(void* p, std::size_t) noexcept { std::free(p); }
#endif

using namespace SOMTParser;

static SortPtr nest(std::size_t depth, SortPtr leaf, SORT_KIND kind = SORT_KIND::SK_DEC) {
    for (std::size_t i = 0; i < depth; ++i) {
        leaf = std::make_shared<Sort>(kind, "P", 1, std::vector<SortPtr>{std::move(leaf)});
    }
    return leaf;
}

static size_t localHash(const Sort& s) {
    size_t value = std::hash<int>{}(static_cast<int>(s.kind));
    value ^= std::hash<std::string>{}(s.name) + 0x9e3779b9 + (value << 6) + (value >> 2);
    value ^= std::hash<size_t>{}(s.arity) + 0x9e3779b9 + (value << 6) + (value >> 2);
    return value;
}
static size_t mixHash(size_t value, size_t child) {
    return value ^ (child + 0x9e3779b9 + (value << 6) + (value >> 2));
}

int main() {
    constexpr size_t depth = 100000;
    {
        auto left = nest(depth, std::make_shared<Sort>(SORT_KIND::SK_INT));
        auto right = nest(depth, std::make_shared<Sort>(SORT_KIND::SK_INT));
        auto different = nest(depth, std::make_shared<Sort>(SORT_KIND::SK_BOOL));
        VERIFY(*left == *right);
        VERIFY(*left != *different);
        VERIFY(left->hash() == right->hash());
        std::string expected;
        for (size_t i = 0; i < depth; ++i) { expected += "(P "; }
        expected += "Int";
        expected.append(depth, ')');
        VERIFY(left->toString() == expected);
        std::weak_ptr<Sort> observed = left;
        left.reset();
        VERIFY(observed.expired());
    }
    {
        // Sharing is a DAG, not a request to traverse an exponentially large
        // unfolded tree. Hash preserves the old per-edge combining formula.
        auto left = std::make_shared<Sort>(SORT_KIND::SK_BOOL);
        auto right = std::make_shared<Sort>(SORT_KIND::SK_BOOL);
        size_t expected = localHash(*left);
        for (size_t i = 0; i < 100; ++i) {
            left = std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0,
                                         std::vector<SortPtr>{left, left});
            right = std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0,
                                          std::vector<SortPtr>{right, right});
            expected = mixHash(mixHash(localHash(*left), expected), expected);
        }
        VERIFY(*left == *right);
        VERIFY(left->hash() == expected);
        VERIFY(right->hash() == expected);
    }
    {
        SortManager manager;
        auto integer = manager.getInt(), real = manager.getReal(), ambiguous = manager.getIntOrReal();
        VERIFY(*integer == *ambiguous);
        VERIFY(*real == *ambiguous);
        VERIFY(*integer != *real);
        auto a = manager.createSetSort(integer), b = manager.createSetSort(real);
        VERIFY(*a != *b);
        VERIFY(*a == *manager.createSetSort(ambiguous));
        auto bv = manager.createBVSort(32), fp = manager.createFPSort(8, 24);
        VERIFY(*bv != *manager.createBVSort(31));
        VERIFY(*fp != *manager.createFPSort(8, 23));
        VERIFY(bv->toString() == "(_ BitVec 32)");
        VERIFY(fp->toString() == "(_ FloatingPoint 8 24)");
        VERIFY(manager.createArraySort(integer, a)->toString() == "(Array Int (Set Int))");
        VERIFY(manager.createTupleSort({bv, a})->toString() == "(Tuple (_ BitVec 32) (Set Int))");
        VERIFY(manager.createTupleSort({})->toString() == "UnitTuple");
        auto dt = std::make_shared<Sort>(SORT_KIND::SK_DATATYPE, "List", 1, std::vector<SortPtr>{a});
        Sort same(SORT_KIND::SK_DATATYPE, "List", 1, {a});
        Sort different(SORT_KIND::SK_DATATYPE, "List", 1, {b});
        dt->dt_constructors = std::make_shared<std::vector<Sort::DtConstructor>>(
            std::vector<Sort::DtConstructor>{{"cons", {{"tail", dt}}}});
        VERIFY(*dt == same);
        VERIFY(*dt != different);
        VERIFY(dt->toString() == "(List (Set Int))");
        VERIFY(dt->hash() == same.hash());
        // Preserve nominal identity across declaration/definition instantiation.
        VERIFY(same == Sort(SORT_KIND::SK_DEC, "List", 1, {a}));
        dt->dt_constructors.reset(); // Explicitly break this intentional owner cycle.
        Sort nullable(SORT_KIND::SK_DEF, "P", 1, {nullptr});
        VERIFY(nullable.toString() == "(P ?)");
        VERIFY(nullable == Sort(SORT_KIND::SK_DEF, "P", 1, {nullptr}));
        VERIFY(nullable != Sort(SORT_KIND::SK_DEF, "P", 1, {integer}));
    }
    {
        // Selector metadata releases a deep chain too; no structure comparison
        // follows selectors, and shared metadata is never changed in place.
        auto leaf = std::make_shared<Sort>(SORT_KIND::SK_BOOL);
        std::weak_ptr<Sort> observed = leaf;
        auto root = std::move(leaf);
        for (size_t i = 0; i < depth; ++i) {
            auto parent = std::make_shared<Sort>(SORT_KIND::SK_DATATYPE, "D", 0);
            parent->dt_constructors = std::make_shared<std::vector<Sort::DtConstructor>>(
                std::vector<Sort::DtConstructor>{{"C", {{"next", std::move(root)}}}});
            root = std::move(parent);
        }
        auto metadata = root->dt_constructors;
        root.reset();
        VERIFY(!observed.expired());
        VERIFY(metadata->at(0).selectors.at(0).sort->name == "D");
        metadata.reset();
        VERIFY(observed.expired());
    }
    {
        auto retained = nest(depth, std::make_shared<Sort>(SORT_KIND::SK_INT));
        const Sort* first = retained->children[0].get();
        auto parent = std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0,
                                            std::vector<SortPtr>{retained, retained});
        parent.reset();
        VERIFY(retained->children.size() == 1);
        VERIFY(retained->children[0].get() == first);
        auto copy = std::make_shared<Sort>(*retained);
        retained.reset();
        VERIFY(copy->children[0].get() == first);
    }
    {
        auto common = nest(30000, std::make_shared<Sort>(SORT_KIND::SK_INT));
        std::weak_ptr<Sort> observed = common;
        auto left = nest(30000, common), right = nest(30000, common);
        common.reset();
        std::atomic<bool> start{false};
        auto release = [&start](SortPtr root) {
            while (!start.load(std::memory_order_acquire)) { std::this_thread::yield(); }
            root.reset();
        };
        std::thread first(release, std::move(left)), second(release, std::move(right));
        start.store(true, std::memory_order_release);
        first.join(); second.join();
        VERIFY(observed.expired());
    }
    {
        auto cyclic = std::make_shared<Sort>(SORT_KIND::SK_DEC, "P", 1);
        cyclic->children.push_back(cyclic);
        bool hashRejected = false, textRejected = false;
        try { cyclic->hash(); } catch (const std::invalid_argument&) { hashRejected = true; }
        try { cyclic->toString(); } catch (const std::invalid_argument&) { textRejected = true; }
        VERIFY(hashRejected && textRejected);
        cyclic->children.clear();
    }
#if defined(__unix__)
    {
        auto root = nest(depth, std::make_shared<Sort>(SORT_KIND::SK_INT));
        std::weak_ptr<Sort> observed = root;
        fail_allocation = true;
        root.reset(); // A chain drains using its existing vector buffer.
        fail_allocation = false;
        VERIFY(observed.expired());
    }
    {
        auto wide = std::make_shared<Sort>(SORT_KIND::SK_ARRAY, "Array", 0,
            std::vector<SortPtr>{std::make_shared<Sort>(SORT_KIND::SK_INT),
                                 std::make_shared<Sort>(SORT_KIND::SK_BOOL)});
        auto root = nest(1, std::move(wide));
        int descriptors[2]; VERIFY(pipe(descriptors) == 0);
        const pid_t child = fork(); VERIFY(child >= 0);
        if (child == 0) {
            close(descriptors[0]);
            if (dup2(descriptors[1], STDERR_FILENO) < 0) { _exit(90); }
            close(descriptors[1]);
            const rlimit noCore{0, 0}; setrlimit(RLIMIT_CORE, &noCore);
            fail_allocation = true;
            root.reset();
            _exit(91);
        }
        close(descriptors[1]);
        char message[256]{};
        const ssize_t count = read(descriptors[0], message, sizeof(message)-1);
        close(descriptors[0]);
        int status = 0; VERIFY(waitpid(child, &status, 0) == child);
        VERIFY(count > 0);
        VERIFY(std::strstr(message, "Sort destruction: memory allocation failed") != nullptr);
        VERIFY(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
    }
#endif
    return 0;
}
