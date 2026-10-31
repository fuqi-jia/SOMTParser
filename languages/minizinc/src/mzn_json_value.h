// Internal MiniZinc JSON value ownership. Not part of the public frontend API.
#ifndef SOMTPARSER_MINIZINC_JSON_VALUE_H
#define SOMTPARSER_MINIZINC_JSON_VALUE_H

#include <cerrno>
#include <cstdlib>
#include <iterator>
#include <new>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#if defined(_WIN32)
#include <io.h>
#else
#include <unistd.h>
#endif

namespace SOMTParser::Lang::detail {

struct JsonRecordNode {
    enum class Kind { INTEGER, REAL, BOOLEAN, STRING, ENUM, RECORD, ARRAY } kind = Kind::INTEGER;
    std::string text;
    std::string field_name;
    bool boolean = false;
    std::vector<JsonRecordNode> fields;
    std::vector<JsonRecordNode> elements;

    JsonRecordNode() = default;
    JsonRecordNode(JsonRecordNode&&) noexcept = default;
    JsonRecordNode& operator=(JsonRecordNode&&) noexcept = default;
    JsonRecordNode(const JsonRecordNode& other) {
        // A vector's implicit copy would recurse through nested records just
        // as its implicit destructor would. Build the value snapshot in a
        // worklist, with stable child addresses after each vector is sized.
        std::vector<std::pair<const JsonRecordNode*, JsonRecordNode*>> pending{{&other, this}};
        while (!pending.empty()) {
            const auto [source, target] = pending.back();
            pending.pop_back();
            target->kind = source->kind;
            target->text = source->text;
            target->field_name = source->field_name;
            target->boolean = source->boolean;
            target->fields.resize(source->fields.size());
            target->elements.resize(source->elements.size());
            for (std::size_t i = 0; i < source->fields.size(); ++i) {
                pending.emplace_back(&source->fields[i], &target->fields[i]);
            }
            for (std::size_t i = 0; i < source->elements.size(); ++i) {
                pending.emplace_back(&source->elements[i], &target->elements[i]);
            }
        }
    }
    JsonRecordNode& operator=(const JsonRecordNode& other) {
        if (this != &other) {
            JsonRecordNode copy(other);
            *this = std::move(copy);
        }
        return *this;
    }

    [[noreturn]] static void releaseFailure() noexcept {
        static constexpr char message[] =
            "SOMTParser MiniZinc JSON destruction: memory allocation failed\n";
        std::size_t written = 0;
        while (written < sizeof(message) - 1) {
#if defined(_WIN32)
            const auto count = _write(2, message + written,
                static_cast<unsigned>(sizeof(message) - 1 - written));
#else
            const auto count = ::write(STDERR_FILENO, message + written,
                                      sizeof(message) - 1 - written);
#endif
            if (count < 0 && errno == EINTR) continue;
            if (count <= 0) break;
            written += static_cast<std::size_t>(count);
        }
        std::abort();
    }

    ~JsonRecordNode() noexcept {
        if (fields.empty() && elements.empty()) return;
        // Only dying value nodes are moved. Each thread has its own
        // outermost queue, and every moved-from vector element is shallow.
        // Reusing a root child buffer makes an ordinary chain allocation
        // free; a branching frontier may need capacity. OOM then emits a
        // fixed resource message and aborts, never recursively falls back.
        static thread_local std::vector<JsonRecordNode>* releasing = nullptr;
        const auto enqueue = [&](std::vector<JsonRecordNode>& children) {
            if (children.empty()) return;
            try {
                releasing->insert(releasing->end(),
                    std::make_move_iterator(children.begin()),
                    std::make_move_iterator(children.end()));
            } catch (const std::bad_alloc&) {
                releaseFailure();
            } catch (const std::length_error&) {
                releaseFailure();
            }
            children.clear();
        };
        if (releasing) {
            enqueue(fields);
            enqueue(elements);
            return;
        }
        std::vector<JsonRecordNode> pending;
        pending.swap(fields.empty() ? elements : fields);
        releasing = &pending;
        enqueue(fields);
        enqueue(elements);
        while (!pending.empty()) {
            JsonRecordNode child = std::move(pending.back());
            pending.pop_back();
            // child enqueues its immediate children after this iteration.
            // Reallocation/clear only destroys moved-from shallow nodes,
            // so destructor nesting is bounded independently of depth.
        }
        releasing = nullptr;
    }
};

} // namespace SOMTParser::Lang::detail

#endif
