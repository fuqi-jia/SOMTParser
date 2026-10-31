// Fail exactly one allocation at each exercised parser allocation position.
// Later diagnostic allocations succeed, so wrapping bad_alloc as a syntax
// error cannot accidentally pass just because its error message also OOMs.
#include "../../languages/tptp/src/thf_expression_parser.h"
#include "test_helpers.h"

#include <cstdlib>
#include <new>

namespace {
thread_local bool armed = false;
thread_local bool fired = false;
thread_local std::size_t allocation = 0;
thread_local std::size_t failure_at = 0;

std::size_t parse() {
    using namespace SOMTParser::Lang::ThfPrototype;
    FunctionHirBuilder builder;
    ThfFileParser parser(
        "thf(p_type,type,p:$o).\n"
        "thf(f_type,type,f:($o > $o)).\n"
        "thf(fact,axiom,(f @ p)).\n"
        "thf(goal,conjecture,((^ [X:$o] : X) @ p)).\n",
        "allocation-locations.p", builder);
    return parser.parse().formulas.size();
}
} // namespace

void* operator new(std::size_t size) {
    if (armed && ++allocation == failure_at) {
        armed = false;
        fired = true;
        throw std::bad_alloc();
    }
    if (void* value = std::malloc(size ? size : 1)) { return value; }
    throw std::bad_alloc();
}
void* operator new[](std::size_t size) { return ::operator new(size); }
void operator delete(void* value) noexcept { std::free(value); }
void operator delete[](void* value) noexcept { std::free(value); }
void operator delete(void* value, std::size_t) noexcept { std::free(value); }
void operator delete[](void* value, std::size_t) noexcept { std::free(value); }

int main() {
    // Initialize any process-global immutable tables before counting positions.
    VERIFY(parse() == 2);
    armed = true;
    const auto formulas = parse();
    armed = false;
    const auto count = allocation;
    VERIFY(formulas == 2 && count > 0);
    std::size_t injected = 0;
    for (std::size_t index = 1; index <= count; ++index) {
        allocation = 0;
        failure_at = index;
        fired = false;
        armed = true;
        bool propagated = false;
        bool mislabeled = false;
        try {
            (void)parse();
        } catch (const std::bad_alloc&) {
            propagated = true;
        } catch (...) {
            mislabeled = true;
        }
        armed = false;
        if (fired) { ++injected; }
        VERIFY(!mislabeled);
        VERIFY(propagated == fired);
    }
    VERIFY(injected == count);
    VERIFY(parse() == 2);
    return 0;
}
