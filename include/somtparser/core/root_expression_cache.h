#ifndef SOMTPARSER_CORE_ROOT_EXPRESSION_CACHE_HEADER
#define SOMTPARSER_CORE_ROOT_EXPRESSION_CACHE_HEADER

namespace SOMTParser::Detail {

/** End a memoization root without retaining its peak bucket array forever.
 *
 * unordered_map::clear() can visit every allocated bucket even when only a
 * few entries remain. One wide root followed by many tiny roots would then
 * repeatedly pay for the widest root. Retain ordinary capacity, but replace
 * an oversized, sparsely used table. Otherwise the retained bucket count is
 * bounded by a constant or eight times the number of entries being cleared.
 * The one-time release of a large bucket array is charged to its earlier
 * allocation; subsequent small roots do not pay that cost again.
 *
 * This is only a storage policy: every old key/value is discarded, and no
 * expression, model or batch size is restricted. Call only at existing root
 * boundaries, never inside a retained immutable batch or lexical scope.
 */
template<class Cache>
void clearExpressionRootCache(Cache& cache) {
    if (cache.bucket_count() > 1024 && cache.bucket_count() / 8 > cache.size()) {
        Cache empty(0, cache.hash_function(), cache.key_eq(), cache.get_allocator());
        empty.max_load_factor(cache.max_load_factor());
        cache.swap(empty);
    } else {
        cache.clear();
    }
}

} // namespace SOMTParser::Detail

#endif
