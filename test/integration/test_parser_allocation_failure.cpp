#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <cstdlib>
#include <new>
#include <string>

namespace {
// Fail one allocation, then restore allocations so cleanup and diagnostics
// remain observable. This is deterministic and does not exhaust host memory.
long allocationCountdown = -1;
bool injected = false;
}

void* operator new(std::size_t size) {
    if (allocationCountdown >= 0 && allocationCountdown-- == 0) {
        allocationCountdown = -1;
        injected = true;
        throw std::bad_alloc();
    }
    if (void* memory = std::malloc(size ? size : 1)) { return memory; }
    throw std::bad_alloc();
}
void* operator new[](std::size_t size) { return ::operator new(size); }
void operator delete(void* memory) noexcept { std::free(memory); }
void operator delete[](void* memory) noexcept { std::free(memory); }
void operator delete(void* memory, std::size_t) noexcept { std::free(memory); }
void operator delete[](void* memory, std::size_t) noexcept { std::free(memory); }

int main() {
    const std::string source =
        "(declare-const x Int)(declare-const b Bool)"
        "(assert (and b (>= x 12)))(check-sat)";
    unsigned resourceFailures = 0;
    bool reachedSuccess = false;
    for (long offset = 0; offset < 2000; ++offset) {
        SOMTParser::Parser parser;
        parser.setCommandLogging(true);
        injected = false;
        allocationCountdown = offset;
        bool propagated = false;
        bool parsed = false;
        try {
            parsed = parser.parseStr(source);
        } catch (const std::bad_alloc&) {
            propagated = true;
        }
        allocationCountdown = -1;
        if (!injected) {
            VERIFY(parsed);
            reachedSuccess = true;
            break;
        }
        // In particular, returning false must not mislabel OOM as a syntax
        // error at the SMT-LIB language frontend's outer translation boundary.
        VERIFY(propagated);
        VERIFY(!parser.lastParseError());
        ++resourceFailures;
    }
    VERIFY(resourceFailures > 10);
    VERIFY(reachedSuccess);
    SOMTParser::Parser malformed;
    VERIFY(!malformed.parseStr("(assert true false)"));
    VERIFY(malformed.lastParseError());
    VERIFY(malformed.getAssertions().empty());
    SOMTParser::Parser valid;
    VERIFY(valid.parseStr("(assert true :id group :named fact ; comment\n)"));
    VERIFY(valid.getAssertions().size() == 1);
    return 0;
}
