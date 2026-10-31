#include "somtparser/core/root_expression_cache.h"
#include "test_helpers.h"

#include <cstddef>
#include <memory>
#include <unordered_map>

using SOMTParser::Detail::clearExpressionRootCache;

struct SaltedHash {
    std::size_t salt;
    std::size_t operator()(std::size_t key) const { return key ^ salt; }
};

struct ExactEqual {
    int tag;
    bool operator()(std::size_t a, std::size_t b) const { return a == b; }
};

int main() {
    using Cache = std::unordered_map<std::size_t, std::shared_ptr<int>,
                                     SaltedHash, ExactEqual>;
    Cache cache(0, SaltedHash{19}, ExactEqual{23});
    cache.max_load_factor(0.75f);
    auto held = std::make_shared<int>(7);
    std::weak_ptr<int> lifetime = held;
    for (std::size_t i = 0; i < 50000; ++i) { cache.emplace(i, held); }
    held.reset();
    const auto large_buckets = cache.bucket_count();
    VERIFY(large_buckets > 1024);
    clearExpressionRootCache(cache);
    VERIFY(cache.empty() && lifetime.expired());
    VERIFY(cache.bucket_count() == large_buckets);

    // A tiny root after the large one releases peak capacity. Its cached
    // native nodes must also be released, with no stale pointer-key result.
    held = std::make_shared<int>(11);
    lifetime = held;
    cache.emplace(0, held);
    cache.emplace(50001, held);
    held.reset();
    clearExpressionRootCache(cache);
    VERIFY(cache.empty() && lifetime.expired());
    VERIFY(cache.bucket_count() < large_buckets / 8);
    VERIFY(cache.hash_function().salt == 19);
    VERIFY(cache.key_eq().tag == 23);
    VERIFY(cache.max_load_factor() == 0.75f);

    // Ordinary roots reuse their small allocation; rebuilding on every root
    // would add allocator churn to the common many-small-constraints case.
    for (std::size_t i = 0; i < 16; ++i) {
        cache.emplace(i, std::make_shared<int>(int(i)));
    }
    const auto small_buckets = cache.bucket_count();
    for (std::size_t root = 0; root < 10000; ++root) {
        clearExpressionRootCache(cache);
        VERIFY(cache.empty() && cache.bucket_count() == small_buckets);
        for (std::size_t i = 0; i < 16; ++i) {
            cache.emplace(i, std::make_shared<int>(int(root)));
        }
        VERIFY(*cache.at(0) == int(root));
    }
    clearExpressionRootCache(cache);

    // A split consuming root clears in a noexcept destructor. The next root
    // sees an empty oversized table and releases it before reusing addresses.
    cache.reserve(50000);
    cache.clear();
    const auto cleared_peak = cache.bucket_count();
    clearExpressionRootCache(cache);
    VERIFY(cache.empty() && cache.bucket_count() < cleared_peak / 8);
    return 0;
}
