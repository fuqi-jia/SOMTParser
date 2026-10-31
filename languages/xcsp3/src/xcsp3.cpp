/* -*- Source -*-
 * XCSP3-core frontend.
 *
 * The format is docs/languages/xcsp3.md; its `implicit-constraints` block is the
 * specification this file implements, and each entry has a fixture in
 * languages/xcsp3/instances.
 *
 * Three of the five obligations are about a value that is *not* what it looks
 * like, and each one is a silent wrong answer rather than a crash:
 *
 *   * **A sparse domain `1 3 5 7` is not the range `1..7`.** `VarDecl` carries
 *     two bounds and nothing else, so the enumeration has to become a
 *     membership constraint as well. Storing only the bounds admits 2, 4 and 6
 *     -- solutions the instance forbids -- and the model still type-checks.
 *   * **A short table's `*` is not the value `*`, and not a fresh variable
 *     either.** It stands for any value in this column's declared domain. The
 *     exact domain is already enforced globally, so the wildcard adds no local
 *     factor; treating it as a literal makes the tuple match nothing.
 *   * **`conflicts` is not `supports` negated in place.** It forbids exactly
 *     the listed tuples and says nothing about the rest; its complement is the
 *     supports table only over the full Cartesian product of the declared
 *     domains, which is not what the file lists.
 *
 * The other two are refusals. `circuit` needs position variables or subtour
 * elimination -- pairwise distinctness alone admits sub-cycles and is *unsound*,
 * which is the one direction this project never takes -- and `div`/`mod` have no
 * HIR operator (see docs/open-questions-2026-08-13.md A6).
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/xcsp3.h"

#include <algorithm>
#include <array>
#include <cstring>
#include <cstdint>
#include <cctype>
#include <charconv>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iterator>
#include <limits>
#include <iterator>
#include <list>
#include <map>
#include <memory>
#include <new>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** Recognize an explicitly enumerated set of all products in [-n,n]^2.
 *  Endpoints alone are not a certificate: check every input value, strict
 *  ordering, and the cardinality of the independently generated product set.
 *  A failed/budgeted recognition leaves the original text authoritative. */
long long boundedProductDomain(std::string_view text) {
    if (text.size() < 1024) { return 0; }
    const char* position = text.data();
    const char* end = position + text.size();
    const auto next = [&](long long& value) {
        while (position != end && std::isspace(static_cast<unsigned char>(*position))) {
            ++position;
        }
        if (position == end) { return false; }
        const auto parsed = std::from_chars(position, end, value);
        if (parsed.ec != std::errc() || parsed.ptr == position
            || (parsed.ptr != end && !std::isspace(static_cast<unsigned char>(*parsed.ptr)))) {
            return false;
        }
        position = parsed.ptr;
        return true;
    };
    long long first = 0;
    // This is an optimization budget, not a restriction on accepted domains.
    constexpr long long max_factor = 2048;
    if (!next(first) || first >= -1 || first < -max_factor * max_factor) { return 0; }
    const long long square = -first;
    long long bound = 1;
    while (bound * bound < square) { ++bound; }
    if (bound * bound != square) { return 0; }
    std::vector<unsigned char> products(static_cast<std::size_t>(square) + 1, 0);
    std::size_t cardinality = 1; // zero, then each positive product and its negation
    for (long long a = 1; a <= bound; ++a) {
        for (long long b = 1; b <= a; ++b) {
            auto& present = products[static_cast<std::size_t>(a * b)];
            if (!present) { present = 1; cardinality += 2; }
        }
    }
    std::size_t seen = 1;
    long long previous = first;
    for (;;) {
        while (position != end && std::isspace(static_cast<unsigned char>(*position))) {
            ++position;
        }
        if (position == end) { break; }
        long long value = 0;
        if (!next(value) || value <= previous || value > square) { return 0; }
        // value > previous >= -square, so negation and indexing are safe.
        if (value != 0 && !products[static_cast<std::size_t>(value < 0 ? -value : value)]) {
            return 0;
        }
        ++seen;
        previous = value;
    }
    return previous == square && seen == cardinality ? bound : 0;
}

/** An XML element: name, attributes, text, children. Enough of XML for
 *  XCSP3-core, and deliberately no more -- no namespaces, no entities beyond
 *  the five predefined ones, no DTD. A file using any of those is refused by
 *  the tokenizer rather than half-read. */
struct Elem {
    std::string name;
    std::unordered_map<std::string, std::string> attrs;
    std::string text;                 // direct character data, whitespace-collapsed
    // Entity-free table text can dominate the input. Borrow it until parsing
    // finishes; instantiated templates materialize only if they contain formals.
    std::string_view table_text;
    // Streaming input owns one shared immutable copy per distinct table text.
    std::shared_ptr<const std::string> table_storage;
    // Nonzero only after exact recognition of the decoded integer domain.
    long long product_domain_bound = 0;
    // Empty leaves need no child storage. List nodes can be released after
    // lowering without invalidating templates or references to sibling nodes.
    std::list<Elem> children;
    int line = 1;

    Elem() = default;
    Elem(Elem&&) noexcept = default;
    Elem& operator=(Elem&&) noexcept = default;
    Elem(const Elem& other) {
        std::vector<std::pair<const Elem*, Elem*>> pending{{&other, this}};
        while (!pending.empty()) {
            const auto entry = pending.back(); pending.pop_back();
            const Elem& from = *entry.first;
            Elem& to = *entry.second;
            to.name = from.name; to.attrs = from.attrs; to.text = from.text;
            to.table_text = from.table_text; to.table_storage = from.table_storage;
            to.product_domain_bound = from.product_domain_bound; to.line = from.line;
            for (const Elem& child : from.children) {
                to.children.emplace_back();
                pending.emplace_back(&child, &to.children.back());
            }
        }
    }
    Elem& operator=(const Elem& other) {
        if (this != &other) { Elem copy(other); *this = std::move(copy); }
        return *this;
    }
    ~Elem() noexcept {
        // Same-allocator list splice transfers ownership without allocation.
        // Every popped element is a leaf, including during exception unwinding.
        std::list<Elem> pending;
        pending.splice(pending.end(), children);
        while (!pending.empty()) {
            pending.splice(pending.end(), pending.front().children);
            pending.pop_front();
        }
    }

    std::string_view textView() const {
        if (table_storage) { return *table_storage; }
        return table_text.empty() ? std::string_view(text) : table_text;
    }

    const Elem* child(const std::string& n) const {
        for (const auto& c : children) { if (c.name == n) { return &c; } }
        return nullptr;
    }
    Elem* child(const std::string& n) {
        for (auto& c : children) { if (c.name == n) { return &c; } }
        return nullptr;
    }
    std::string attr(const std::string& n, const std::string& fallback = "") const {
        auto it = attrs.find(n);
        return it == attrs.end() ? fallback : it->second;
    }
};

std::size_t countOperators(const H::ExprPtr& root) {
    std::size_t count = 0;
    std::unordered_set<const H::Expr*> seen;
    std::vector<const H::Expr*> pending{root.get()};
    while (!pending.empty()) {
        const auto* expression = pending.back(); pending.pop_back();
        if (!expression || !seen.insert(expression).second) { continue; }
        if (expression->kind == H::ExprKind::OP) { ++count; }
        for (const auto& child : expression->args) { pending.push_back(child.get()); }
    }
    return count;
}

// File input uses one bounded read window. Inline input keeps its existing
// borrowed views; a view into the streaming window must never escape a read.
class XmlCursor {
public:
    XmlCursor(std::string_view source, std::istream* stream)
        : source_(source), stream_(stream) {}

    std::string_view available(std::size_t lookahead = 1) {
        if (!stream_) { return source_.substr(begin_); }
        if (end_ - begin_ < lookahead && !finished_) {
            const std::size_t retained = end_ - begin_;
            std::memmove(buffer_.data(), buffer_.data() + begin_, retained);
            begin_ = 0;
            end_ = retained;
            stream_->read(buffer_.data() + end_, buffer_.size() - end_);
            end_ += static_cast<std::size_t>(stream_->gcount());
            failed_ = stream_->bad() || (stream_->fail() && !stream_->eof());
            finished_ = !*stream_;
        }
        return {buffer_.data() + begin_, end_ - begin_};
    }
    int peek() {
        const auto bytes = available();
        return bytes.empty() ? -1 : static_cast<unsigned char>(bytes.front());
    }
    bool startsWith(std::string_view marker) {
        const auto bytes = available(marker.size());
        return bytes.size() >= marker.size() && bytes.substr(0, marker.size()) == marker;
    }
    void advance(std::size_t count) { begin_ += count; }
    bool isStreaming() const { return stream_ != nullptr; }
    bool failed() const { return failed_; }

private:
    std::string_view source_;
    std::istream* stream_ = nullptr;
    std::array<char, 64 * 1024> buffer_;
    std::size_t begin_ = 0;
    std::size_t end_ = 0;
    bool finished_ = false;
    bool failed_ = false;
};

class XmlReader {
public:
    using CompletedElement = std::function<bool(Elem&, Elem&, std::size_t, bool&)>;
    XmlReader(std::string_view source, std::string file, std::istream* stream = nullptr,
              CompletedElement completed = {})
        : cursor_(source, stream), completed_(std::move(completed)), file_(std::move(file)) {}

    bool read(Elem& root, Uir::Diagnostics& diags) {
        skipProlog();
        const bool parsed = element(root, diags, 0);
        if (cursor_.failed()) {
            diags.error(ErrorCode::E_IO, "failed reading '" + file_ + "'", at());
            return false;
        }
        return parsed;
    }

private:
    Uir::SourceLoc at() const {
        Uir::SourceLoc loc;
        loc.file = file_;
        loc.line = line_;
        loc.column = 1;
        return loc;
    }

    // Consume only the current window. Callers scan/append before advancing;
    // the next available() may refill and invalidate its previous view.
    void bump(std::size_t count) {
        const auto bytes = cursor_.available();
        line_ += static_cast<int>(std::count(bytes.begin(), bytes.begin() + count, '\n'));
        cursor_.advance(count);
    }
    void skipWs() {
        for (;;) {
            const auto bytes = cursor_.available();
            std::size_t count = 0;
            while (count < bytes.size()
                   && std::isspace(static_cast<unsigned char>(bytes[count]))) { ++count; }
            if (count) { bump(count); }
            if (count < bytes.size() || bytes.empty()) { return; }
        }
    }
    bool skipThrough(std::string_view terminator) {
        for (;;) {
            const auto bytes = cursor_.available(terminator.size());
            if (bytes.empty()) { return false; }
            const auto found = bytes.find(terminator);
            if (found != std::string_view::npos) {
                bump(found + terminator.size());
                return true;
            }
            if (bytes.size() < terminator.size()) {
                bump(bytes.size());
                return false;
            }
            // Retain the suffix that may begin a marker crossing a refill.
            bump(bytes.size() - terminator.size() + 1);
        }
    }
    bool textUntil(char delimiter, std::string& text) {
        for (;;) {
            const auto bytes = cursor_.available();
            if (bytes.empty()) { return false; }
            const auto found = bytes.find(delimiter);
            const auto count = found == std::string_view::npos ? bytes.size() : found;
            text.append(bytes.data(), count);
            if (count) { bump(count); }
            if (found != std::string_view::npos) { return true; }
        }
    }
    /** `<?xml ...?>`, comments and doctype before the root. */
    void skipProlog() {
        for (;;) {
            skipWs();
            if (cursor_.startsWith("<!--")) { skipThrough("-->"); }
            else if (cursor_.startsWith("<?")) { skipThrough("?>"); }
            else if (cursor_.startsWith("<!DOCTYPE")) { skipThrough(">"); }
            else { return; }
        }
    }
    std::string name() {
        std::string result;
        for (;;) {
            const int next = cursor_.peek();
            if (next < 0 || !(std::isalnum(static_cast<unsigned char>(next))
                             || next == '_' || next == '-' || next == '.' || next == ':')) {
                return result;
            }
            result += static_cast<char>(next);
            bump(1);
        }
    }
    static std::string unescape(std::string input) {
        if (input.find('&') == std::string::npos) { return input; }
        std::string result;
        for (std::size_t k = 0; k < input.size(); ++k) {
            if (input[k] != '&') { result += input[k]; continue; }
            const auto semicolon = input.find(';', k);
            if (semicolon == std::string::npos) { result += input[k]; continue; }
            const auto entity = input.substr(k + 1, semicolon - k - 1);
            if      (entity == "lt")   { result += '<'; }
            else if (entity == "gt")   { result += '>'; }
            else if (entity == "amp")  { result += '&'; }
            else if (entity == "quot") { result += '"'; }
            else if (entity == "apos") { result += '\''; }
            else { result += input.substr(k, semicolon - k + 1); }
            k = semicolon;
        }
        return result;
    }
    std::shared_ptr<const std::string> tableStorage(std::string text) {
        // Exact byte equality resolves hash collisions. Weak memo entries do
        // not keep consumed table text alive; copies of an Elem share ownership.
        const std::size_t hash = std::hash<std::string_view>{}(text);
        auto& bucket = table_storage_[hash];
        for (auto it = bucket.begin(); it != bucket.end();) {
            const auto existing = it->lock();
            if (!existing) { it = bucket.erase(it); continue; }
            if (*existing == text) { return existing; }
            ++it;
        }
        auto stored = std::make_shared<const std::string>(std::move(text));
        bucket.push_back(stored);
        return stored;
    }
    bool openElement(Elem& out, bool& closed, Uir::Diagnostics& diags) {
        skipWs();
        if (cursor_.peek() != '<') {
            diags.error(ErrorCode::E_PARSE, "expected an element", at());
            return false;
        }
        out.line = line_;
        bump(1);
        out.name = name();
        if (out.name.empty()) {
            diags.error(ErrorCode::E_PARSE, "an element has no name", at());
            return false;
        }
        for (;;) {
            skipWs();
            if (cursor_.peek() < 0) {
                diags.error(ErrorCode::E_PARSE, "unterminated element '" + out.name + "'", at());
                return false;
            }
            if (cursor_.startsWith("/>")) { bump(2); closed = true; return true; }
            if (cursor_.peek() == '>') { bump(1); break; }
            const std::string key = name();
            if (key.empty()) {
                diags.error(ErrorCode::E_PARSE, "expected an attribute in '" + out.name + "'", at());
                return false;
            }
            skipWs();
            if (cursor_.peek() != '=') {
                diags.error(ErrorCode::E_PARSE, "attribute '" + key + "' has no value", at());
                return false;
            }
            bump(1);
            skipWs();
            const int quote = cursor_.peek();
            if (quote != '"' && quote != '\'') {
                diags.error(ErrorCode::E_PARSE, "attribute '" + key + "' is not quoted", at());
                return false;
            }
            bump(1);
            std::string value;
            if (!textUntil(static_cast<char>(quote), value)) {
                diags.error(ErrorCode::E_PARSE, "unterminated element '" + out.name + "'", at());
                return false;
            }
            out.attrs[key] = unescape(std::move(value));
            bump(1);
        }
        return true;
    }

    bool element(Elem& out, Uir::Diagnostics& diags, std::size_t /*depth*/) {
        struct Frame {
            Elem storage;
            Elem* element = nullptr;
            std::string text;
            bool closed = false;
            bool table = false;
        };
        // Stable frames own unfinished children until the completed-element
        // callback either consumes them or installs them in their parent.
        std::list<Frame> pending;
        const auto push = [&](Elem* external) {
            pending.emplace_back();
            Frame& frame = pending.back();
            frame.element = external ? external : &frame.storage;
            if (!openElement(*frame.element, frame.closed, diags)) { return false; }
            frame.table = frame.element->name == "supports" || frame.element->name == "conflicts";
            if (!frame.closed && frame.table && !cursor_.isStreaming()) {
                const auto bytes = cursor_.available();
                const auto end = bytes.find('<');
                if (end != std::string_view::npos && bytes.substr(end, 2) == "</"
                    && bytes.substr(0, end).find('&') == std::string_view::npos) {
                    frame.element->table_text = bytes.substr(0, end);
                    if (end) { bump(end); }
                }
            }
            return true;
        };
        if (!push(&out)) { return false; }
        while (!pending.empty()) {
            Frame& frame = pending.back();
            Elem& current = *frame.element;
            if (frame.closed) {
                if (pending.size() == 1) { return true; }
                auto parent = std::prev(pending.end(), 2);
                bool consumed = false;
                if (completed_ && !completed_(*parent->element, current,
                                              pending.size() - 2, consumed)) { return false; }
                if (!consumed) { parent->element->children.push_back(std::move(current)); }
                pending.pop_back();
                continue;
            }
            if (cursor_.peek() < 0) {
                diags.error(ErrorCode::E_PARSE, "unclosed element '" + current.name + "'", at());
                return false;
            }
            if (cursor_.startsWith("<!--")) { skipThrough("-->"); continue; }
            if (cursor_.startsWith("</")) {
                bump(2);
                const std::string close = name();
                if (close != current.name) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + current.name + "' is closed by '" + close + "'", at());
                    return false;
                }
                skipWs();
                if (cursor_.peek() != '>') {
                    diags.error(ErrorCode::E_PARSE,
                                "the closing tag for '" + current.name + "' is not terminated "
                                "by '>'", at());
                    return false;
                }
                bump(1);
                if (frame.table && cursor_.isStreaming()) {
                    current.table_storage = tableStorage(unescape(std::move(frame.text)));
                } else {
                    current.text = unescape(std::move(frame.text));
                    if (current.children.empty()
                        && (current.name == "domain" || current.name == "var" || current.name == "array")
                        && current.attr("as").empty()
                        && (current.attr("type").empty() || current.attr("type") == "integer")) {
                        current.product_domain_bound = boundedProductDomain(current.text);
                        if (current.product_domain_bound) { std::string().swap(current.text); }
                    }
                }
                frame.closed = true;
            } else if (cursor_.peek() == '<') {
                if (!push(nullptr)) { return false; }
            } else {
                textUntil('<', frame.text);
            }
        }
        return true;
    }

    XmlCursor cursor_;
    CompletedElement completed_;
    std::string file_;
    int line_ = 1;
    std::unordered_map<std::size_t, std::vector<std::weak_ptr<const std::string>>> table_storage_;
};

// ---- helpers ------------------------------------------------------------

std::vector<std::string> words(const std::string& s) {
    std::vector<std::string> out;
    std::istringstream in(s);
    std::string w;
    while (in >> w) { out.push_back(w); }
    return out;
}

bool toInt(const std::string& s, long long& v) {
    const char* first = s.data();
    const char* last = first + s.size();
    const auto r = std::from_chars(first, last, v);
    return r.ec == std::errc() && r.ptr == last;
}

/** A variable's declared domain, kept as the *set* the file wrote rather than
 *  as the interval that contains it. The distinction is the whole of the first
 *  obligation, and it is also what `*` in a short table expands over. */
struct Domain {
    long long lo = 0;
    long long hi = 0;
    bool empty = false;
    /** Enumeration unless the domain is an interval or a certified product set. */
    std::vector<long long> values;
    long long product_bound = 0;
    bool sparse() const { return product_bound != 0 || !values.empty(); }
};

// Array cells and aliases share immutable source domains. HIR bounds and
// membership formulas remain per variable, with their own source locations.
using DomainPtr = std::shared_ptr<const Domain>;

// Domains may be shared across variables; identifiers must remain per variable.
// Keep the leaf cache beside the source-domain entry to avoid a second hash
// table (and a second copy of every cell name) for large arrays.
struct SourceVariable {
    DomainPtr domain;
    mutable H::ExprPtr expression;
};

struct ArrayInfo {
    std::vector<long long> dimensions;
    std::vector<long long> starts;
};

struct Transition {
    std::string source;
    long long value = 0;
    std::string target;
};

class Xcsp3Parser {
public:
    Xcsp3Parser(std::string_view source, std::string file, std::istream* stream = nullptr)
        : src_(source), stream_(stream), file_(std::move(file)) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags,
                                Uir::TranslationReport& report) {
        report_ = &report;
        Elem root;
        {
            // Inline views refer to the caller-owned SourceUnit. Streaming
            // table views instead have shared immutable storage on each Elem.
            const auto completed = [&](Elem& parent, Elem& child, std::size_t depth,
                                       bool& consumed) {
                if (!stream_) { return true; }
                if (depth == 0 && parent.name == "instance" && child.name == "variables"
                    && !streamed_variables_) {
                    bool compact = false;
                    for (const Elem& declaration : child.children) {
                        if (declaration.name != "array") { continue; }
                        std::vector<long long> shape;
                        Domain candidate;
                        Uir::Diagnostics probe;
                        if (arrayShape(declaration.attr("size"), shape, declaration, probe)
                            && compactArrayDomain(declaration, shape, candidate)) {
                            compact = true;
                            break;
                        }
                    }
                    if (compact) {
                        model_ = std::make_shared<H::ConstraintModel>();
                        if (!variables(child, diags)) { return false; }
                        child.children.clear();
                        streamed_variables_ = true;
                    }
                } else if (depth == 1 && parent.name == "constraints" && streamed_variables_) {
                    // A complete top-level group/block is enough to resolve
                    // its lexical template. Consume it before reading later
                    // siblings, instead of keeping the whole XML tree live.
                    Elem wrapper;
                    wrapper.name = "constraints";
                    wrapper.line = parent.line;
                    wrapper.children.push_back(std::move(child));
                    extension_template_by_element_.clear();
                    extension_templates_.clear();
                    indexOrdinaryExtensionTemplates(wrapper);
                    if (!constraints(wrapper, diags)) { return false; }
                    extension_template_by_element_.clear();
                    extension_templates_.clear();
                    consumed = true;
                }
                return true;
            };
            XmlReader reader(src_, file_, stream_, completed);
            if (!reader.read(root, diags)) { return nullptr; }
        }
        src_ = {};
        if (root.name != "instance") {
            diags.error(ErrorCode::E_PARSE,
                        "the root element is '" + root.name + "', not 'instance'", at(root));
            return nullptr;
        }
        if (root.attr("format") != "XCSP3") {
            diags.error(ErrorCode::E_PARSE,
                        "the instance format attribute must be 'XCSP3'", at(root));
            return nullptr;
        }
        const std::string type = root.attr("type");
        if (type != "CSP" && type != "COP") {
            diags.error(ErrorCode::E_PARSE,
                        "instance type '" + type + "' is neither CSP nor COP", at(root));
            return nullptr;
        }
        std::unordered_map<std::string, std::size_t> section_counts;
        int previous_rank = -1;
        for (const Elem& section : root.children) {
            int rank = -1;
            if (section.name == "variables") { rank = 0; }
            else if (section.name == "constraints") { rank = 1; }
            else if (section.name == "objectives") { rank = 2; }
            else if (section.name == "annotations") { rank = 3; }
            else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "unknown XCSP3 instance section '" + section.name
                                + "' cannot be ignored", at(section));
                return nullptr;
            }
            if (rank < previous_rank) {
                diags.error(ErrorCode::E_PARSE,
                            "XCSP3 instance sections are out of specification order",
                            at(section));
                return nullptr;
            }
            previous_rank = rank;
            if (++section_counts[section.name] != 1) {
                diags.error(ErrorCode::E_PARSE,
                            "duplicate XCSP3 <" + section.name + "> section", at(section));
                return nullptr;
            }
        }
        const bool has_objectives = section_counts["objectives"] != 0;
        if ((type == "CSP" && has_objectives) || (type == "COP" && !has_objectives)) {
            diags.error(ErrorCode::E_PARSE,
                        type + " instance has an inconsistent <objectives> section", at(root));
            return nullptr;
        }
        if (!model_) { model_ = std::make_shared<H::ConstraintModel>(); }
        if (Elem* vars = root.child("variables")) {
            if (!streamed_variables_ && !variables(*vars, diags)) { return nullptr; }
            // Arrays may alias any earlier declaration, so keep the complete
            // variables section until its pass has finished. It is dead after
            // that point and can release its XML nodes before HIR construction.
            vars->children.clear();
        }
        if (Elem* cons = root.child("constraints")) {
            indexOrdinaryExtensionTemplates(*cons);
            if (!constraints(*cons, diags)) { return nullptr; }
        }
        if (Elem* objs = root.child("objectives")) {
            if (!objectives(*objs, diags)) { return nullptr; }
            if (model_->objectives.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "a COP <objectives> section must contain an objective",
                            at(*objs));
                return nullptr;
            }
            objs->children.clear();
        }
        if (section_counts["annotations"] != 0 && report_) {
            report_->addChoice(
                {file_, "annotations", "operational-hints-only", Uir::Fidelity::exact(),
                 "XCSP3 annotations guide search/filtering and do not alter the source "
                 "solution relation; the semantic adapter therefore omits them"});
        }
        return model_;
    }

    std::vector<H::ExprPtr> declarationTerms() const {
        std::vector<H::ExprPtr> terms(model_->decls.size());
        for (std::size_t i = 0; i < model_->decls.size(); ++i) {
            const auto& declaration = model_->decls[i];
            if (!declaration.lower_bound && !declaration.upper_bound) { continue; }
            const auto source = findSource(declaration.name);
            if (source != nullptr) {
                terms[i] = source->expression;
            } else {
                const auto auxiliary = variable_exprs_.find(declaration.name);
                if (auxiliary != variable_exprs_.end()) { terms[i] = auxiliary->second; }
            }
        }
        return terms;
    }

private:
    Uir::SourceLoc at(const Elem& e) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = e.line;
        l.column = 1;
        return l;
    }

    struct CompactSourceRange {
        std::size_t range = 0;
        SourceVariable variable;
    };

    const CompactSourceRange* compactSource(const std::string& name,
                                            std::uint64_t* offset = nullptr) const {
        if (name.empty() || name.back() != ']') { return nullptr; }
        const auto open = name.rfind('[');
        if (open == std::string::npos) { return nullptr; }
        const auto found = compact_variables_.find(name.substr(0, open + 1));
        if (found == compact_variables_.end()) { return nullptr; }
        const auto& range = model_->scalar_var_ranges[found->second.range];
        std::uint64_t index = 0;
        if (!range.contains(name, &index)) { return nullptr; }
        if (offset) { *offset = index - range.first; }
        return &found->second;
    }

    const SourceVariable* findSource(const std::string& name) const {
        const auto ordinary = domains_.find(name);
        if (ordinary != domains_.end()) { return &ordinary->second; }
        const auto compact = compactSource(name);
        return compact ? &compact->variable : nullptr;
    }

    const SourceVariable& sourceVariable(const std::string& name) const {
        const auto found = findSource(name);
        if (!found) { throw std::out_of_range("undeclared XCSP3 source variable"); }
        return *found;
    }

    // This is a storage decision only. Every indexed coordinate is still a
    // source observable and receives its own scalar declaration and bounds.
    bool compactArrayDomain(const Elem& e, const std::vector<long long>& shape,
                             Domain& d) const {
        if (!e.children.empty() || !e.attr("as").empty() || shape.empty()
            || e.attr("id").find_first_of("|\\\n\r\t") != std::string::npos
            || (!e.attr("type").empty() && e.attr("type") != "integer")) { return false; }
        long long start = 0;
        if ((!e.attr("startIndex").empty() && !toInt(e.attr("startIndex"), start))
            || start < 0) { return false; }
        std::size_t count = 1;
        for (const auto dimension : shape) {
            if (dimension <= 0 || static_cast<unsigned long long>(dimension)
                    > std::numeric_limits<std::size_t>::max() / count
                || start > std::numeric_limits<long long>::max() - (dimension - 1)) {
                return false;
            }
            count *= static_cast<std::size_t>(dimension);
        }
        if (count < 65536) { return false; }
        const auto tokens = words(e.text);
        if (tokens.empty()) { return false; }
        if (tokens.size() > 1) {
            // Explicit finite domains share a checked membership predicate.
            // Interval unions keep their existing parser and diagnostics; do
            // not enumerate a large interval just to choose a storage layout.
            std::vector<long long> values;
            values.reserve(tokens.size());
            for (const auto& token : tokens) {
                long long value = 0;
                if (!toInt(token, value)) { return false; }
                values.push_back(value);
            }
            std::sort(values.begin(), values.end());
            values.erase(std::unique(values.begin(), values.end()), values.end());
            d.lo = values.front();
            d.hi = values.back();
            bool contiguous = true;
            for (std::size_t i = 1; i < values.size(); ++i) {
                if (values[i - 1] == std::numeric_limits<long long>::max()
                    || values[i] != values[i - 1] + 1) {
                    contiguous = false;
                    break;
                }
            }
            if (!contiguous) { d.values = std::move(values); }
            return true;
        }
        const auto dots = tokens[0].find("..");
        if (dots == std::string::npos) {
            if (!toInt(tokens[0], d.lo)) { return false; }
            d.hi = d.lo;
        } else if (!toInt(tokens[0].substr(0, dots), d.lo)
                   || !toInt(tokens[0].substr(dots + 2), d.hi) || d.lo > d.hi) {
            return false;
        }
        return true;
    }

    void declareCompactArray(const std::string& id, const ArrayInfo& info,
                              Domain domain, const Elem& e) {
        const auto source = std::make_shared<const Domain>(std::move(domain));
        std::string membership_function;
        if (!source->values.empty()) {
            H::FunDecl definition;
            definition.name = freshGroupFunctionName();
            definition.params = {H::Sort::integer()};
            definition.result = H::Sort::boolean();
            definition.auxiliary = true;
            definition.loc = at(e);
            const std::string bound_name = definition.name + "_value";
            definition.binders = {{bound_name, H::Sort::integer()}};
            const auto bound = H::mkBoundVar(bound_name, H::Sort::integer());
            std::vector<H::ExprPtr> alternatives;
            alternatives.reserve(source->values.size());
            for (const auto value : source->values) {
                alternatives.push_back(H::mkOp(H::Op::EQ, {bound, num(value)}));
            }
            definition.body = disjunction(std::move(alternatives), e);
            membership_function = definition.name;
            model_->funs.push_back(std::move(definition));
            if (!packed_calls_) {
                packed_calls_ = std::make_shared<H::PackedFunctionCalls>();
                model_->packed_function_calls = packed_calls_;
            }
        }
        const std::size_t dimension = info.dimensions.size() - 1;
        std::vector<long long> offsets(dimension, 0);
        bool more = true;
        while (more) {
            std::string prefix = id;
            for (std::size_t d = 0; d < dimension; ++d) {
                prefix += "[" + std::to_string(info.starts[d] + offsets[d]) + "]";
            }
            H::ScalarVarRange range;
            range.prefix = std::move(prefix) + "[";
            range.first = static_cast<std::uint64_t>(info.starts[dimension]);
            range.count = static_cast<std::uint64_t>(info.dimensions[dimension]);
            range.loc = at(e);
            range.lower_bound = num(source->lo);
            range.upper_bound = num(source->hi);
            const auto index = model_->scalar_var_ranges.size();
            compact_variables_.emplace(range.prefix,
                CompactSourceRange{index, SourceVariable{source, {}}});
            const auto count = range.count;
            model_->scalar_var_ranges.push_back(std::move(range));
            // Every coordinate, including cells not mentioned by any
            // constraint, gets its exact sparse domain. Calls use the
            // same typed range IDs as ordinary packed groups; no HIR
            // identifier or membership tree is allocated per scalar.
            if (!membership_function.empty()) {
                for (std::uint64_t offset = 0; offset < count;) {
                    const auto length = std::min<std::uint64_t>(65536, count - offset);
                    H::PackedFunctionCallBatch batch;
                    batch.function = membership_function;
                    batch.arity = 1;
                    batch.loc = at(e);
                    batch.arguments.reserve(static_cast<std::size_t>(length));
                    for (std::uint64_t k = 0; k < length; ++k) {
                        batch.arguments.push_back({index, offset + k});
                    }
                    packed_calls_->batches.push_back(std::move(batch));
                    offset += length;
                }
            }
            more = false;
            for (std::size_t d = dimension; d != 0;) {
                --d;
                if (++offsets[d] < info.dimensions[d]) { more = true; break; }
                offsets[d] = 0;
            }
        }
        report_->addChoice({file_ + ":" + std::to_string(e.line), "integer-array",
            "finite-scalar-declaration-ranges", Uir::Fidelity::exact(),
            "Every original indexed scalar, including unused cells, remains a source "
            "observable with its exact integer domain; sparse memberships use "
            "checked packed predicate calls and metadata is shared by row"});
    }

    bool packFunctionCall(const std::string& function,
                           const std::vector<std::string>& names, const Elem& e) {
        if (model_->scalar_var_ranges.empty() || names.empty()) { return false; }
        while (indexed_declarations_ < model_->decls.size()) {
            declaration_ids_.emplace(model_->decls[indexed_declarations_].name,
                                     indexed_declarations_);
            ++indexed_declarations_;
        }
        std::vector<H::PackedScalarArgument> arguments;
        arguments.reserve(names.size());
        for (const auto& name : names) {
            std::uint64_t offset = 0;
            if (const auto range = compactSource(name, &offset)) {
                arguments.push_back({range->range, offset});
            } else {
                const auto declaration = declaration_ids_.find(name);
                if (declaration == declaration_ids_.end()) { return false; }
                arguments.push_back({H::PackedScalarArgument::DECLARATION,
                                     declaration->second});
            }
        }
        if (!packed_calls_) {
            packed_calls_ = std::make_shared<H::PackedFunctionCalls>();
            model_->packed_function_calls = packed_calls_;
        }
        if (packed_calls_->batches.empty()
            || packed_calls_->batches.back().function != function
            || packed_calls_->batches.back().loc.line != e.line
            || packed_calls_->batches.back().arguments.size() >= 65536) {
            H::PackedFunctionCallBatch batch;
            batch.function = function;
            batch.arity = names.size();
            batch.loc = at(e);
            packed_calls_->batches.push_back(std::move(batch));
        }
        auto& batch = packed_calls_->batches.back();
        batch.arguments.insert(batch.arguments.end(), arguments.begin(), arguments.end());
        return true;
    }

    H::ExprPtr var(const std::string& name) const {
        const auto source = findSource(name);
        if (source != nullptr && !compactSource(name)) {
            auto& expression = source->expression;
            if (!expression) { expression = H::mkIdent(name, H::Sort::integer()); }
            return expression;
        }
        // Auxiliary identifiers without source-domain entries use this cache.
        const auto found = variable_exprs_.find(name);
        if (found != variable_exprs_.end()) { return found->second; }
        H::ExprPtr expression = H::mkIdent(name, H::Sort::integer());
        variable_exprs_.emplace(name, expression);
        return expression;
    }
    H::ExprPtr num(long long value) const {
        const auto found = integer_exprs_.find(value);
        if (found != integer_exprs_.end()) { return found->second; }
        H::ExprPtr expression = H::mkInt(std::to_string(value));
        integer_exprs_.emplace(value, expression);
        return expression;
    }

    H::ExprPtr auxiliary(const H::Sort& sort, const Elem& e,
                         H::ExprPtr lower = {}, H::ExprPtr upper = {}) {
        std::string name;
        do {
            name = "__somt_xcsp3_aux_" + std::to_string(auxiliary_counter_++);
        } while (findSource(name) != nullptr);
        H::VarDecl declaration;
        declaration.name = name;
        declaration.sort = sort;
        declaration.lower_bound = std::move(lower);
        declaration.upper_bound = std::move(upper);
        declaration.loc = at(e);
        declaration.auxiliary = true;
        model_->decls.push_back(std::move(declaration));
        rememberGroupSymbol(name);
        return H::mkIdent(name, sort, at(e));
    }

    static std::string cellName(const std::string& base,
                                const std::vector<long long>& indices) {
        std::string name = base;
        for (const long long index : indices) {
            name += "[" + std::to_string(index) + "]";
        }
        return name;
    }

    bool arrayShape(const std::string& text, std::vector<long long>& dimensions,
                    const Elem& e, Uir::Diagnostics& diags) const {
        std::size_t i = 0;
        while (i < text.size()) {
            if (text[i] != '[') {
                diags.error(ErrorCode::E_PARSE,
                            "array size '" + text + "' is not a sequence of [n] dimensions",
                            at(e));
                return false;
            }
            const std::size_t close = text.find(']', i + 1);
            if (close == std::string::npos) {
                diags.error(ErrorCode::E_PARSE,
                            "array size '" + text + "' has an unterminated dimension",
                            at(e));
                return false;
            }
            long long dimension = 0;
            if (!toInt(text.substr(i + 1, close - i - 1), dimension)
                || dimension <= 0) {
                diags.error(ErrorCode::E_PARSE,
                            "array dimension '" + text.substr(i, close - i + 1)
                                + "' is not a positive integer", at(e));
                return false;
            }
            dimensions.push_back(dimension);
            i = close + 1;
        }
        if (dimensions.empty()) {
            diags.error(ErrorCode::E_PARSE, "an array has no dimensions", at(e));
            return false;
        }
        return true;
    }

    bool arrayCellNames(const std::string& base, const ArrayInfo& info,
                        std::vector<std::string>& names, const Elem& e,
                        Uir::Diagnostics& diags) const {
        std::size_t total = 1;
        for (std::size_t i = 0; i < info.dimensions.size(); ++i) {
            const long long dimension = info.dimensions[i];
            if (static_cast<unsigned long long>(dimension)
                > std::numeric_limits<std::size_t>::max() / total) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "array '" + base + "' is too large to materialise", at(e));
                return false;
            }
            if (info.starts[i]
                > std::numeric_limits<long long>::max() - (dimension - 1)) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "array '" + base + "' index exceeds int64", at(e));
                return false;
            }
            total *= static_cast<std::size_t>(dimension);
        }
        names.reserve(names.size() + total);
        std::vector<long long> indices(info.dimensions.size());
        for (std::size_t linear = 0; linear < total; ++linear) {
            std::size_t rest = linear;
            for (std::size_t rev = info.dimensions.size(); rev-- > 0;) {
                const std::size_t dimension =
                    static_cast<std::size_t>(info.dimensions[rev]);
                indices[rev] = info.starts[rev]
                    + static_cast<long long>(rest % dimension);
                rest /= dimension;
            }
            names.push_back(cellName(base, indices));
        }
        return true;
    }

    H::ExprPtr extremumValue(std::vector<H::ExprPtr> terms, bool minimum,
                            const Uir::SourceLoc& loc) {
        // Each comparison and ITE branch references the selected operand.
        // A left fold therefore expands exponentially in tree-based consumers;
        // a balanced reduction keeps that expansion polynomial. Both operands
        // must be defined for each comparison, including the unselected one.
        const H::Op compare = minimum ? H::Op::LE : H::Op::GE;
        while (terms.size() > 1) {
            std::vector<H::ExprPtr> next;
            next.reserve((terms.size() + 1) / 2);
            for (std::size_t i = 0; i < terms.size(); i += 2) {
                if (i + 1 == terms.size()) {
                    next.push_back(terms[i]);
                    continue;
                }
                H::ExprPtr select = relational_.value(compare,
                                                       {terms[i], terms[i + 1]}, loc);
                next.push_back(relational_.conditional(select, terms[i], terms[i + 1], loc));
            }
            terms = std::move(next);
        }
        return terms.front();
    }

    void noteRelationalPartiality(const Elem& e) {
        if (said_partiality_ || report_ == nullptr) { return; }
        said_partiality_ = true;
        report_->addChoice(
            {file_ + ":" + std::to_string(e.line), "partial-expression",
             "constraint-root-definedness", Uir::Fidelity::exact(),
             "XCSP3 Java tools evaluate div/mod with Java integer / and %, hence "
             "truncation toward zero; the nonzero divisor guard propagates to the "
             "root intension constraint"});
    }

    // ---- variables -------------------------------------------------------

    /** `0..10`, `1 3 5 7`, `0..3 7 9..12`. Returns false on a malformed one. */
    bool domain(const std::string& text, Domain& d, const Elem& e,
                Uir::Diagnostics& diags) {
        if (e.product_domain_bound) {
            d.product_bound = e.product_domain_bound;
            d.hi = d.product_bound * d.product_bound;
            d.lo = -d.hi;
            return true;
        }
        const std::vector<std::string> parts = words(text);
        if (parts.empty()) {
            // XCSP3 section 2.10: an explicitly empty domain is legal and
            // makes the model inconsistent. It is different from an array
            // cell that no <domain for=...> selector defines.
            d.empty = true;
            return true;
        }
        // A single interval is already represented exactly by lo/hi. Do not
        // enumerate it merely to rediscover that fact: `-10^9..10^9` is a
        // compact legal XCSP3 domain, not a two-billion-element input.
        if (parts.size() == 1) {
            const std::size_t dots = parts.front().find("..");
            if (dots != std::string::npos) {
                long long lo = 0, hi = 0;
                if (!toInt(parts.front().substr(0, dots), lo)
                    || !toInt(parts.front().substr(dots + 2), hi)) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + parts.front() + "' is not a range", at(e));
                    return false;
                }
                if (hi < lo) {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + parts.front() + "' is an empty range", at(e));
                    return false;
                }
                d.lo = lo;
                d.hi = hi;
                return true;
            }
        }
        bool contiguous = true;
        std::vector<long long> vals;
        for (const std::string& p : parts) {
            const std::size_t dots = p.find("..");
            if (dots != std::string::npos) {
                long long lo = 0, hi = 0;
                if (!toInt(p.substr(0, dots), lo) || !toInt(p.substr(dots + 2), hi)) {
                    diags.error(ErrorCode::E_PARSE, "'" + p + "' is not a range", at(e));
                    return false;
                }
                if (hi < lo) {
                    diags.error(ErrorCode::E_PARSE, "'" + p + "' is an empty range", at(e));
                    return false;
                }
                // A range wider than this would make the membership constraint
                // larger than the instance. Only reached when the domain is
                // ALSO sparse, since a single range needs no enumeration.
                const unsigned long long width =
                    static_cast<unsigned long long>(hi)
                    - static_cast<unsigned long long>(lo);
                if (width > 100000) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "the range '" + p + "' has more than 100000 values and the "
                                "domain is not a single interval, so it cannot be "
                                "enumerated", at(e));
                    return false;
                }
                for (long long v = lo;; ++v) {
                    vals.push_back(v);
                    if (v == hi) { break; }
                }
            } else {
                long long v = 0;
                if (!toInt(p, v)) {
                    diags.error(ErrorCode::E_PARSE, "'" + p + "' is not an integer", at(e));
                    return false;
                }
                vals.push_back(v);
            }
        }
        std::sort(vals.begin(), vals.end());
        vals.erase(std::unique(vals.begin(), vals.end()), vals.end());
        d.lo = vals.front();
        d.hi = vals.back();
        for (std::size_t k = 1; k < vals.size(); ++k) {
            if (vals[k] != vals[k - 1] + 1) { contiguous = false; break; }
        }
        // **The first obligation.** The enumeration is kept only when it is NOT
        // an interval; a contiguous one is fully described by its two bounds and
        // an extra membership constraint would be noise. When it is not
        // contiguous the bounds are a strictly weaker statement, so the values
        // have to travel too.
        if (!contiguous) { d.values = std::move(vals); }
        return true;
    }

    /** Declare one integer variable, with its bounds and -- if the domain is
     *  sparse -- the membership constraint that the bounds cannot express. */
    bool declare(const std::string& name, DomainPtr source_domain, const Elem& e,
                 Uir::Diagnostics& diags,
                 std::vector<H::ExprPtr>* memberships = nullptr,
                 const std::string& finite_domain_helper = {}) {
        if (findSource(name) != nullptr
            || arrays_.find(name) != arrays_.end()) {
            diags.error(ErrorCode::E_PARSE,
                        "variable or array id '" + name + "' is declared more than once",
                        at(e));
            return false;
        }
        const Domain& d = *source_domain;
        H::VarDecl decl;
        decl.name = name;
        decl.sort = H::Sort::integer();
        if (finite_domain_helper.empty() && !d.empty) {
            decl.lower_bound = num(d.lo);
            decl.upper_bound = num(d.hi);
        }
        decl.loc = at(e);
        model_->decls.push_back(std::move(decl));
        domains_.emplace(name, SourceVariable{std::move(source_domain), {}});
        rememberGroupSymbol(name);
        if (d.empty) {
            const auto inconsistent = H::mkBool(false, memberships ? Uir::SourceLoc{} : at(e));
            if (memberships) { memberships->push_back(inconsistent); }
            else { addFormula(inconsistent, e); }
            return true;
        }
        if (!d.sparse()) { return true; }
        // Generated array predicates inherit the enclosing array constraint's
        // exact location. Repeating its file path per cell adds no information.
        const Uir::SourceLoc member_loc = memberships ? Uir::SourceLoc{} : at(e);
        auto addMembership = [&](H::ExprPtr formula) {
            if (memberships) { memberships->push_back(std::move(formula)); }
            else { addFormula(std::move(formula), e); }
        };
        if (!finite_domain_helper.empty()) {
            // The predicate enforces the complete finite domain, including its
            // bounds. Avoid recording the same bounds again on every VarDecl
            // and materializing one extra semantic-contract axiom per cell.
            addMembership(H::mkApply(finite_domain_helper, H::Sort::boolean(),
                                     {var(name)}, member_loc));
            return true;
        }
        if (d.product_bound) {
            // These witnesses are local to membership, not source observables.
            // Avoid capturing even a deliberately similarly named source var.
            std::string left_name = "__somt_xcsp3_domain_left";
            std::string right_name = "__somt_xcsp3_domain_right";
            while (left_name == name) { left_name += '_'; }
            while (right_name == name) { right_name += '_'; }
            const auto left = H::mkBoundVar(left_name, H::Sort::integer(), member_loc);
            const auto right = H::mkBoundVar(right_name, H::Sort::integer(), member_loc);
            const auto low = num(-d.product_bound), high = num(d.product_bound);
            const auto body = conjunction({
                H::mkOp(H::Op::LE, {low, left}, member_loc),
                H::mkOp(H::Op::LE, {left, high}, member_loc),
                H::mkOp(H::Op::LE, {low, right}, member_loc),
                H::mkOp(H::Op::LE, {right, high}, member_loc),
                H::mkOp(H::Op::EQ, {var(name), H::mkOp(H::Op::MUL, {left, right}, member_loc)}, member_loc)
            }, e);
            addMembership(H::mkExists({{left_name, H::Sort::integer()},
                                       {right_name, H::Sort::integer()}}, body, member_loc));
            return true;
        }
        // Explicit sparse domains often list a complete arithmetic progression
        // (e.g. every fourth frequency in FAPP). Bounds plus one congruence are
        // exactly that finite set, without one equality node per listed value.
        if (d.values.size() >= 3) {
            const auto gap = [](long long high, long long low) {
                // Unsigned subtraction represents the full signed-endpoint
                // distance without overflowing, including LLONG_MIN.
                return static_cast<unsigned long long>(high)
                     - static_cast<unsigned long long>(low);
            };
            const unsigned long long step = gap(d.values[1], d.values[0]);
            bool progression = step != 0;
            for (std::size_t i = 2; progression && i < d.values.size(); ++i) {
                progression = gap(d.values[i], d.values[i - 1]) == step;
            }
            if (progression) {
                H::ExprPtr offset = d.lo == 0 ? var(name)
                    : H::mkOp(H::Op::SUB, {var(name), num(d.lo)}, member_loc);
                H::ExprPtr divisor = H::mkInt(std::to_string(step), member_loc);
                H::ExprPtr residue = H::mkOp(H::Op::MOD_EUCLID,
                                             {std::move(offset), std::move(divisor)}, member_loc);
                addMembership(H::mkOp(H::Op::EQ, {std::move(residue), num(0)}, member_loc));
                return true;
            }
        }
        // A dense finite set can be cheaper as its missing values inside the
        // already-enforced declaration bounds. For {-1,1}, one (distinct x 0)
        // replaces two equalities and an OR, which matters for large arrays.
        // The missing constants are unique, so n-ary DISTINCT adds exactly
        // x != missing[i]; comparisons among constants are tautologies.
        std::size_t missing_count = 0;
        bool small_complement = true;
        for (std::size_t i = 1; i < d.values.size(); ++i) {
            const auto gap = static_cast<unsigned long long>(d.values[i])
                           - static_cast<unsigned long long>(d.values[i - 1]) - 1;
            if (gap > d.values.size() - missing_count) {
                small_complement = false;
                break;
            }
            missing_count += static_cast<std::size_t>(gap);
        }
        if (small_complement && missing_count) {
            std::vector<H::ExprPtr> different;
            different.reserve(missing_count + 1);
            different.push_back(var(name));
            for (std::size_t i = 1; i < d.values.size(); ++i) {
                for (long long value = d.values[i - 1] + 1; value < d.values[i]; ++value) {
                    different.push_back(num(value));
                }
            }
            addMembership(H::mkOp(H::Op::DISTINCT, std::move(different), member_loc));
            return true;
        }
        std::vector<H::ExprPtr> alts;
        alts.reserve(d.values.size());
        for (long long v : d.values) {
            alts.push_back(H::mkOp(H::Op::EQ, {var(name), num(v)}, member_loc));
        }
        addMembership(alts.size() == 1 ? alts.front()
                                       : H::mkOp(H::Op::OR, std::move(alts), member_loc));
        return true;
    }

    // Count source declarations without materializing cell names. Exact upfront
    // capacity avoids retaining a half-full old declaration buffer while a
    // doubled buffer is allocated for a large array. Invalid or unresolved
    // shapes fall back to the ordinary diagnostic-producing variable parser.
    std::size_t sourceDeclarationCount(const Elem& vars) const {
        std::unordered_map<std::string, std::size_t> sizes;
        std::size_t total = 0;
        const std::size_t maximum = model_->decls.max_size();
        for (const Elem& e : vars.children) {
            const std::string id = e.attr("id");
            if (id.empty() || sizes.count(id)) { return 0; }
            if (!e.attr("type").empty() && e.attr("type") != "integer") { return 0; }
            std::size_t count = 1;
            if (e.name == "array") {
                std::vector<long long> dimensions;
                Uir::Diagnostics ignored;
                if (!arrayShape(e.attr("size"), dimensions, e, ignored)) { return 0; }
                long long start = 0;
                if (!e.attr("startIndex").empty() && !toInt(e.attr("startIndex"), start)) { return 0; }
                for (const long long dimension : dimensions) {
                    if (static_cast<unsigned long long>(dimension) > maximum / count
                        || start > std::numeric_limits<long long>::max() - (dimension - 1)) {
                        return 0;
                    }
                    count *= static_cast<std::size_t>(dimension);
                }
                Domain compact_domain;
                if (compactArrayDomain(e, dimensions, compact_domain)) { count = 0; }
            } else if (e.name == "var") {
                const std::string alias = e.attr("as");
                if (!alias.empty()) {
                    const auto source = sizes.find(alias);
                    // A cell alias is valid but is deliberately left to the
                    // ordinary parser rather than guessing a cell name here.
                    if (source == sizes.end()) { return 0; }
                    count = source->second;
                }
            } else { return 0; }
            if (count > maximum - total) { return 0; }
            total += count;
            sizes.emplace(id, count);
        }
        return total;
    }

    bool variables(const Elem& vars, Uir::Diagnostics& diags) {
        model_->decls.reserve(sourceDeclarationCount(vars));
        // Domain helpers can now be introduced while reading declarations.
        // Reserve all source declaration IDs first, including later scalars;
        // generated function names must not steal a future source symbol.
        for (const Elem& e : vars.children) {
            const std::string id = e.attr("id");
            if (isGroupGeneratedName(id)) { group_symbol_keys_.insert(smtSymbolKey(id)); }
        }
        for (const Elem& e : vars.children) {
            if (e.name == "var") {
                const std::string id = e.attr("id");
                if (id.empty()) {
                    diags.error(ErrorCode::E_PARSE, "a <var> has no id", at(e));
                    return false;
                }
                if (!e.attr("type").empty() && e.attr("type") != "integer") {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "variables of type '" + e.attr("type")
                                    + "' are not supported; only integer", at(e));
                    return false;
                }
                Domain d;
                // `<var id="yy" as="zz"/>` -- yy takes zz's domain, and carries
                // no domain text of its own. Without this the empty text
                // reached domain() and was reported as "a variable has an empty
                // domain": true of the element, and the wrong thing to tell
                // the author, who wrote a perfectly ordinary alias.
                const std::string alias = e.attr("as");
                if (!alias.empty()) {
                    const auto src = findSource(alias);
                    if (src != nullptr) {
                        if (!declare(id, src->domain, e, diags)) { return false; }
                        continue;
                    }
                    const auto source_array = arrays_.find(alias);
                    if (source_array == arrays_.end()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "<var id=\"" + id + "\" as=\"" + alias
                                        + "\"> refers to no earlier variable or array",
                                    at(e));
                        return false;
                    }
                    if (findSource(id) != nullptr
                        || arrays_.find(id) != arrays_.end()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "variable or array id '" + id
                                        + "' is declared more than once", at(e));
                        return false;
                    }
                    const ArrayInfo alias_info = source_array->second;
                    std::vector<std::string> source_cells, target_cells;
                    if (!arrayCellNames(alias, alias_info, source_cells, e, diags)
                        || !arrayCellNames(id, alias_info, target_cells, e, diags)) {
                        return false;
                    }
                    arrays_[id] = alias_info;
                    rememberGroupSymbol(id);
                    std::vector<H::ExprPtr> memberships;
                    for (std::size_t i = 0; i < source_cells.size(); ++i) {
                        const auto source_domain = findSource(source_cells[i]);
                        if (source_domain == nullptr) {
                            // An array-domain alias keeps the same holes.
                            continue;
                        }
                        if (!declare(target_cells[i], source_domain->domain, e, diags, &memberships)) {
                            return false;
                        }
                    }
                    if (!memberships.empty()) {
                        addFormula(conjunction(std::move(memberships), e), e);
                    }
                    continue;
                }
                if (!domain(e.text, d, e, diags)) { return false; }
                if (!declare(id, std::make_shared<const Domain>(std::move(d)), e, diags)) { return false; }
            } else if (e.name == "array") {
                const std::string id = e.attr("id");
                const std::string size = e.attr("size");
                if (id.empty() || size.empty()) {
                    diags.error(ErrorCode::E_PARSE, "an <array> needs id and size", at(e));
                    return false;
                }
                if (findSource(id) != nullptr
                    || arrays_.find(id) != arrays_.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "variable or array id '" + id
                                    + "' is declared more than once", at(e));
                    return false;
                }
                if (!e.attr("type").empty() && e.attr("type") != "integer") {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "arrays of type '" + e.attr("type")
                                    + "' are not supported; only integer", at(e));
                    return false;
                }
                ArrayInfo info;
                if (!arrayShape(size, info.dimensions, e, diags)) { return false; }
                long long start = 0;
                if (!e.attr("startIndex").empty()
                    && !toInt(e.attr("startIndex"), start)) {
                    diags.error(ErrorCode::E_PARSE,
                                "array startIndex '" + e.attr("startIndex")
                                    + "' is not an integer", at(e));
                    return false;
                }
                info.starts.assign(info.dimensions.size(), start);
                Domain compact_domain;
                if (compactArrayDomain(e, info.dimensions, compact_domain)) {
                    arrays_[id] = info;
                    rememberGroupSymbol(id);
                    declareCompactArray(id, info, std::move(compact_domain), e);
                    continue;
                }
                std::vector<std::string> cells;
                if (!arrayCellNames(id, info, cells, e, diags)) { return false; }
                arrays_[id] = info;
                rememberGroupSymbol(id);

                // `as` copies content only (XCSP3 section 10.5). In particular,
                // Heterosquare's two diagonal sums copy a longer row-sum
                // array's domain, while keeping their own [2] shape.
                const Elem* definition = &e;
                const std::string alias = e.attr("as");
                if (!alias.empty()) {
                    if (!words(e.text).empty() || !e.children.empty()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "an array with as must not have its own content", at(e));
                        return false;
                    }
                    for (const Elem& previous : vars.children) {
                        if (&previous == &e) { break; }
                        if (previous.attr("id") == alias) { definition = &previous; }
                    }
                    if (definition == &e || !definition->attr("as").empty()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "array as must name an earlier non-alias declaration", at(e));
                        return false;
                    }
                    std::vector<const Elem*> descendants;
                    for (const Elem& child : definition->children) { descendants.push_back(&child); }
                    while (!descendants.empty()) {
                        const Elem* child = descendants.back();
                        descendants.pop_back();
                        if (!child->attr("id").empty()) {
                            diags.error(ErrorCode::E_PARSE,
                                        "array as cannot copy content containing an id", at(e));
                            return false;
                        }
                        for (const Elem& nested : child->children) { descendants.push_back(&nested); }
                    }
                }
                // One array declaration has one source location. Keep all
                // exact cell memberships but attach constraint metadata once.
                std::vector<H::ExprPtr> memberships;
                std::unordered_map<std::string, DomainPtr> assigned;
                if (definition->children.empty()) {
                    Domain d;
                    if (!domain(definition->text, d, *definition, diags)) { return false; }
                    const auto shared_domain = std::make_shared<const Domain>(std::move(d));
                    std::string finite_domain_helper;
                    if (cells.size() >= 256 && shared_domain->sparse()
                        && shared_domain->values.size() == 2) {
                        H::FunDecl definition;
                        definition.name = freshGroupFunctionName();
                        definition.params = {H::Sort::integer()};
                        definition.result = H::Sort::boolean();
                        definition.auxiliary = true;
                        definition.loc = at(e);
                        const std::string bound_name = definition.name + "_value";
                        definition.binders = {{bound_name, H::Sort::integer()}};
                        const auto bound = H::mkBoundVar(bound_name, H::Sort::integer());
                        definition.body = disjunction({
                            H::mkOp(H::Op::EQ, {bound, num(shared_domain->values[0])}),
                            H::mkOp(H::Op::EQ, {bound, num(shared_domain->values[1])})}, e);
                        finite_domain_helper = definition.name;
                        model_->funs.push_back(std::move(definition));
                    }
                    // Uniform arrays need no second, temporary per-cell map.
                    for (const std::string& cell : cells) {
                        if (!declare(cell, shared_domain, e, diags, &memberships,
                                     finite_domain_helper)) { return false; }
                    }
                    if (!memberships.empty()) {
                        addFormula(conjunction(std::move(memberships), e), e);
                    }
                    continue;
                } else {
                    bool saw_others = false;
                    DomainPtr others;
                    std::size_t child_index = 0;
                    for (auto child_it = definition->children.begin();
                         child_it != definition->children.end(); ++child_it, ++child_index) {
                        const Elem& child = *child_it;
                        if (child.name != "domain") {
                            diags.error(ErrorCode::E_PARSE,
                                        "array '" + id + "' contains <" + child.name
                                            + "> instead of <domain>", at(child));
                            return false;
                        }
                        Domain child_domain;
                        if (!domain(child.text, child_domain, child, diags)) { return false; }
                        const auto shared_domain = std::make_shared<const Domain>(std::move(child_domain));
                        const std::string selector = child.attr("for");
                        if (selector == "others") {
                            if (saw_others || child_index + 1 != definition->children.size()) {
                                diags.error(ErrorCode::E_PARSE,
                                            "array <domain for=\"others\"> must occur once "
                                            "and last", at(child));
                                return false;
                            }
                            saw_others = true;
                            others = shared_domain;
                            continue;
                        }
                        if (selector.empty()) {
                            diags.error(ErrorCode::E_PARSE,
                                        "an array <domain> has no for selector", at(child));
                            return false;
                        }
                        std::vector<std::string> selected;
                        if (!varList(selector, selected, child, diags, true)) { return false; }
                        for (const std::string& cell : selected) {
                            if (cell.compare(0, id.size() + 1, id + "[") != 0) {
                                diags.error(ErrorCode::E_PARSE,
                                            "domain selector '" + selector
                                                + "' names a variable outside array '" + id
                                                + "'", at(child));
                                return false;
                            }
                            if (!assigned.emplace(cell, shared_domain).second) {
                                diags.error(ErrorCode::E_PARSE,
                                            "array cell '" + cell
                                                + "' receives more than one domain", at(child));
                                return false;
                            }
                        }
                    }
                    for (const std::string& cell : cells) {
                        if (saw_others && assigned.find(cell) == assigned.end()) {
                            assigned[cell] = others;
                        }
                    }
                }
                for (const std::string& cell : cells) {
                    auto assignment = assigned.find(cell);
                    // Unselected cells have no domain definition and are not
                    // source variables. A later use still receives a parse
                    // error; silently omitting a constraint operand is wrong.
                    if (assignment == assigned.end()) { continue; }
                    if (!declare(cell, assignment->second, e, diags, &memberships)) { return false; }
                    assigned.erase(assignment);
                }
                if (!memberships.empty()) {
                    addFormula(conjunction(std::move(memberships), e), e);
                }
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "'" + e.name + "' is not a supported variable declaration",
                            at(e));
                return false;
            }
        }
        // A scalar declared before a compact array must not be hidden by the
        // later range. Check once per ordinary symbol, not once per array cell.
        for (const auto& declaration : domains_) {
            if (compactSource(declaration.first)) {
                diags.error(ErrorCode::E_PARSE,
                    "variable or array cell '" + declaration.first + "' is declared more than once",
                    at(vars));
                return false;
            }
        }
        return true;
    }

    /** `q[0] q[1] q[2]` or `q[]`, the latter meaning the whole array. */
    bool varList(const std::string& text, std::vector<std::string>& out, const Elem& e,
                 Uir::Diagnostics& diags, bool domain_selector = false) {
        for (const std::string& w : words(text)) {
            if (findSource(w) != nullptr) {
                out.push_back(w);
                continue;
            }
            const std::size_t first_bracket = w.find('[');
            if (first_bracket == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "'" + w + "' is not a declared variable",
                            at(e));
                return false;
            }
            const std::string base = w.substr(0, first_bracket);
            const auto array = arrays_.find(base);
            if (array == arrays_.end()) {
                diags.error(ErrorCode::E_PARSE, "'" + base + "' is not an array", at(e));
                return false;
            }
            std::vector<std::vector<long long>> selections;
            std::size_t i = first_bracket;
            while (i < w.size()) {
                if (w[i] != '[') {
                    diags.error(ErrorCode::E_PARSE,
                                "compact array reference '" + w + "' is malformed", at(e));
                    return false;
                }
                const std::size_t close = w.find(']', i + 1);
                if (close == std::string::npos) {
                    diags.error(ErrorCode::E_PARSE,
                                "compact array reference '" + w + "' is unterminated", at(e));
                    return false;
                }
                selections.emplace_back();
                const std::size_t dimension = selections.size() - 1;
                if (dimension >= array->second.dimensions.size()) {
                    diags.error(ErrorCode::E_PARSE,
                                "array reference '" + w + "' has too many indices", at(e));
                    return false;
                }
                const long long first = array->second.starts[dimension];
                const long long last = first + array->second.dimensions[dimension] - 1;
                const std::string selector = w.substr(i + 1, close - i - 1);
                long long lo = first, hi = last;
                if (!selector.empty()) {
                    const std::size_t dots = selector.find("..");
                    if (dots == std::string::npos) {
                        if (!toInt(selector, lo)) {
                            diags.error(ErrorCode::E_PARSE,
                                        "array index '" + selector + "' is not an integer",
                                        at(e));
                            return false;
                        }
                        hi = lo;
                    } else if (!toInt(selector.substr(0, dots), lo)
                               || !toInt(selector.substr(dots + 2), hi)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "array slice '" + selector + "' is not an interval",
                                    at(e));
                        return false;
                    }
                }
                if (lo < first || hi > last || hi < lo) {
                    diags.error(ErrorCode::E_TYPE,
                                "array selector '" + selector + "' is outside dimension "
                                    + std::to_string(dimension) + " of '" + base + "'",
                                at(e));
                    return false;
                }
                for (long long value = lo;; ++value) {
                    selections.back().push_back(value);
                    if (value == hi) { break; }
                }
                i = close + 1;
            }
            if (selections.size() != array->second.dimensions.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "array reference '" + w + "' has "
                                + std::to_string(selections.size()) + " index dimension(s), "
                                "expected "
                                + std::to_string(array->second.dimensions.size()), at(e));
                return false;
            }
            std::size_t total = 1;
            for (const auto& selection : selections) { total *= selection.size(); }
            for (std::size_t linear = 0; linear < total; ++linear) {
                std::size_t rest = linear;
                std::vector<long long> indices(selections.size());
                for (std::size_t rev = selections.size(); rev-- > 0;) {
                    indices[rev] = selections[rev][rest % selections[rev].size()];
                    rest /= selections[rev].size();
                }
                const std::string cell = cellName(base, indices);
                if (!domain_selector && findSource(cell) == nullptr) {
                    diags.error(ErrorCode::E_PARSE,
                                "array cell '" + cell + "' has no domain definition "
                                "and cannot occur in a constraint or objective", at(e));
                    return false;
                }
                out.push_back(cell);
            }
        }
        return true;
    }

    // Compact array references expand before positional template substitution.
    // Whitespace inside a functional expression is not a list separator.
    bool expandedList(const std::string& text, std::vector<std::string>& out,
                      const Elem& e, Uir::Diagnostics& diags) {
        std::size_t begin = 0;
        int depth = 0;
        for (std::size_t i = 0; i <= text.size(); ++i) {
            if (i < text.size()) {
                if (text[i] == '(') { ++depth; }
                if (text[i] == ')' && --depth < 0) {
                    diags.error(ErrorCode::E_PARSE, "unmatched ')' in a list", at(e));
                    return false;
                }
                if (depth || !std::isspace(static_cast<unsigned char>(text[i]))) {
                    continue;
                }
            }
            if (i > begin) {
                const std::string token = text.substr(begin, i - begin);
                if (token.find('(') == std::string::npos
                    && token.find('[') != std::string::npos) {
                    if (!varList(token, out, e, diags)) { return false; }
                } else {
                    out.push_back(token);
                }
            }
            begin = i + 1;
        }
        if (depth) {
            diags.error(ErrorCode::E_PARSE, "unmatched '(' in a list", at(e));
            return false;
        }
        return true;
    }

    bool expressionList(const std::string& text, std::vector<H::ExprPtr>& out,
                        const Elem& e, Uir::Diagnostics& diags) {
        std::vector<std::string> tokens;
        if (!expandedList(text, tokens, e, diags)) { return false; }
        for (const std::string& token : tokens) {
            std::size_t position = 0;
            H::ExprPtr term = intension(token, position, e, diags, 0);
            if (!term) { return false; }
            if (position != token.size()) {
                diags.error(ErrorCode::E_PARSE, "trailing text in list expression '"
                                + token + "'", at(e));
                return false;
            }
            if (term->sort.kind == H::SortKind::BOOL) {
                term = relational_.conditional(term, num(1), num(0), at(e));
            }
            if (term->sort.kind != H::SortKind::INT) {
                diags.error(ErrorCode::E_TYPE, "a list expression must be integer-valued",
                            at(e));
                return false;
            }
            out.push_back(std::move(term));
        }
        return true;
    }

    H::ExprPtr scalar(const std::string& text, const Elem& e,
                      Uir::Diagnostics& diags) const {
        const std::vector<std::string> tokens = words(text);
        if (tokens.size() != 1) {
            diags.error(ErrorCode::E_PARSE,
                        "expected one integer value or variable, got '" + text + "'", at(e));
            return nullptr;
        }
        long long value = 0;
        if (toInt(tokens.front(), value)) { return num(value); }
        if (findSource(tokens.front()) == nullptr) {
            diags.error(ErrorCode::E_PARSE,
                        "'" + tokens.front() + "' is not an integer or declared variable",
                        at(e));
            return nullptr;
        }
        return var(tokens.front());
    }

    bool termList(const std::string& text, std::vector<H::ExprPtr>& out, const Elem& e,
                  Uir::Diagnostics& diags,
                  std::size_t max_entries = std::numeric_limits<std::size_t>::max()) {
        const std::vector<std::string> tokens = words(text);
        if (tokens.empty()) {
            diags.error(ErrorCode::E_PARSE, "a list is empty", at(e));
            return false;
        }
        max_entries = std::min(max_entries, out.max_size());
        for (const std::string& token : tokens) {
            long long value = 0;
            if (toInt(token, value)) {
                if (out.size() >= max_entries) {
                    diags.error(ErrorCode::E_PARSE, "too many terms for the list", at(e));
                    return false;
                }
                out.push_back(num(value));
            } else {
                const std::size_t repeat = token.find('x');
                if (repeat != std::string::npos && toInt(token.substr(0, repeat), value)) {
                    long long count = 0;
                    if (!toInt(token.substr(repeat + 1), count) || count <= 0
                        || static_cast<unsigned long long>(count) > max_entries - out.size()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "invalid or oversized integer repetition '" + token + "'", at(e));
                        return false;
                    }
                    out.insert(out.end(), static_cast<std::size_t>(count), num(value));
                    continue;
                }
                std::vector<std::string> variables;
                if (!varList(token, variables, e, diags)) { return false; }
                if (variables.size() > max_entries - out.size()) {
                    diags.error(ErrorCode::E_PARSE, "too many terms for the list", at(e));
                    return false;
                }
                for (const std::string& variable : variables) {
                    out.push_back(var(variable));
                }
            }
        }
        return true;
    }

    bool mixedTermList(std::string text, std::vector<H::ExprPtr>& out, const Elem& e,
                       Uir::Diagnostics& diags) {
        std::replace(text.begin(), text.end(), ',', ' ');
        return termList(text, out, e, diags);
    }

    bool termMatrix(const std::string& text,
                    std::vector<std::vector<H::ExprPtr>>& rows,
                    const Elem& e, Uir::Diagnostics& diags) {
        const std::string body = trim(text);
        std::size_t i = 0;
        while (i < body.size()) {
            while (i < body.size()
                   && std::isspace(static_cast<unsigned char>(body[i]))) { ++i; }
            if (i == body.size()) { break; }
            if (body[i] != '(') {
                diags.error(ErrorCode::E_PARSE,
                            "tuple rows must be parenthesized", at(e));
                return false;
            }
            const std::size_t close = body.find(')', i + 1);
            if (close == std::string::npos) {
                diags.error(ErrorCode::E_PARSE,
                            "a tuple row has no closing ')'", at(e));
                return false;
            }
            rows.emplace_back();
            if (!mixedTermList(body.substr(i + 1, close - i - 1),
                               rows.back(), e, diags)) {
                return false;
            }
            i = close + 1;
        }
        if (rows.size() < 2 || rows.front().empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "a tuple matrix requires at least two nonempty rows", at(e));
            return false;
        }
        const std::size_t columns = rows.front().size();
        for (const auto& row : rows) {
            if (row.size() != columns) {
                diags.error(ErrorCode::E_PARSE,
                            "all tuple rows must have the same length", at(e));
                return false;
            }
        }
        return true;
    }

    H::ExprPtr conjunction(std::vector<H::ExprPtr> terms, const Elem& e) const {
        if (terms.empty()) { return H::mkBool(true, at(e)); }
        if (terms.size() == 1) { return terms.front(); }
        return H::mkOp(H::Op::AND, std::move(terms), at(e));
    }

    H::ExprPtr disjunction(std::vector<H::ExprPtr> terms, const Elem& e) const {
        if (terms.empty()) { return H::mkBool(false, at(e)); }
        if (terms.size() == 1) { return terms.front(); }
        return H::mkOp(H::Op::OR, std::move(terms), at(e));
    }

    H::ExprPtr implication(H::ExprPtr antecedent, H::ExprPtr consequent,
                           const Elem& e) const {
        return disjunction(
            {H::mkOp(H::Op::NOT, {std::move(antecedent)}, at(e)),
             std::move(consequent)}, e);
    }

    H::ExprPtr condition(const H::ExprPtr& lhs, const std::string& text, const Elem& e,
                         Uir::Diagnostics& diags) const {
        std::string body;
        for (const char ch : text) {
            if (!std::isspace(static_cast<unsigned char>(ch))) { body += ch; }
        }
        if (body.size() < 5 || body.front() != '(' || body.back() != ')') {
            diags.error(ErrorCode::E_PARSE,
                        "condition '" + text + "' must have form (operator,operand)", at(e));
            return nullptr;
        }
        body = body.substr(1, body.size() - 2);
        const std::size_t comma = body.find(',');
        if (comma == std::string::npos) {
            diags.error(ErrorCode::E_PARSE,
                        "condition '" + text + "' has no operand", at(e));
            return nullptr;
        }
        const std::string op = body.substr(0, comma);
        const std::string rhs_text = body.substr(comma + 1);
        if (op == "in" || op == "notin") {
            std::vector<H::ExprPtr> members;
            const std::size_t dots = rhs_text.find("..");
            if (dots != std::string::npos) {
                long long lo = 0, hi = 0;
                if (!toInt(rhs_text.substr(0, dots), lo)
                    || !toInt(rhs_text.substr(dots + 2), hi) || hi < lo) {
                    diags.error(ErrorCode::E_PARSE,
                                "condition interval '" + rhs_text + "' is invalid", at(e));
                    return nullptr;
                }
                if (op == "in") {
                    return conjunction(
                        {H::mkOp(H::Op::GE, {lhs, num(lo)}, at(e)),
                         H::mkOp(H::Op::LE, {lhs, num(hi)}, at(e))}, e);
                }
                return disjunction(
                    {H::mkOp(H::Op::LT, {lhs, num(lo)}, at(e)),
                     H::mkOp(H::Op::GT, {lhs, num(hi)}, at(e))}, e);
            }
            const bool braces = rhs_text.size() >= 2 && rhs_text.front() == '{'
                && rhs_text.back() == '}';
            const bool functional = rhs_text.size() >= 5
                && rhs_text.compare(0, 4, "set(") == 0 && rhs_text.back() == ')';
            if (!braces && !functional) {
                diags.error(ErrorCode::E_PARSE,
                            "'" + op + "' requires an interval or integer set operand", at(e));
                return nullptr;
            }
            const std::string entries = braces ? rhs_text.substr(1, rhs_text.size() - 2)
                : rhs_text.substr(4, rhs_text.size() - 5);
            if (!entries.empty() && entries.back() == ',') {
                diags.error(ErrorCode::E_PARSE, "an integer set has a trailing comma", at(e));
                return nullptr;
            }
            std::size_t begin = 0;
            while (begin < entries.size()) {
                const std::size_t next = entries.find(',', begin);
                const std::string entry = entries.substr(
                    begin, next == std::string::npos ? std::string::npos : next - begin);
                long long value = 0;
                if (!toInt(entry, value)) {
                    diags.error(ErrorCode::E_PARSE,
                                "set entry '" + entry + "' is not an integer", at(e));
                    return nullptr;
                }
                H::ExprPtr equal = H::mkOp(H::Op::EQ, {lhs, num(value)}, at(e));
                members.push_back(op == "in"
                                      ? equal
                                      : H::mkOp(H::Op::NOT, {equal}, at(e)));
                if (next == std::string::npos) { break; }
                begin = next + 1;
            }
            return op == "in" ? disjunction(std::move(members), e)
                              : conjunction(std::move(members), e);
        }
        H::ExprPtr rhs = scalar(rhs_text, e, diags);
        if (!rhs) { return nullptr; }
        if (op == "eq") { return H::mkOp(H::Op::EQ, {lhs, rhs}, at(e)); }
        if (op == "ne") {
            return H::mkOp(H::Op::NOT,
                           {H::mkOp(H::Op::EQ, {lhs, rhs}, at(e))}, at(e));
        }
        if (op == "lt") { return H::mkOp(H::Op::LT, {lhs, rhs}, at(e)); }
        if (op == "le") { return H::mkOp(H::Op::LE, {lhs, rhs}, at(e)); }
        if (op == "gt") { return H::mkOp(H::Op::GT, {lhs, rhs}, at(e)); }
        if (op == "ge") { return H::mkOp(H::Op::GE, {lhs, rhs}, at(e)); }
        diags.error(ErrorCode::E_PARSE,
                    "condition operator '" + op + "' is not an XCSP3 operator", at(e));
        return nullptr;
    }

    void addFormula(H::ExprPtr formula, const Elem& e) {
        H::Constraint constraint;
        constraint.loc = at(e);
        constraint.formula = std::move(formula);
        model_->constraints.push_back(std::move(constraint));
    }

    // ---- intension -------------------------------------------------------

    /** `le(add(x, 3), 10)` -- prefix functional syntax, comma-separated. */
    H::ExprPtr intension(const std::string& s, std::size_t& i, const Elem& e,
                         Uir::Diagnostics& diags, int /*depth*/) {
        struct Frame { std::string head; std::vector<H::ExprPtr> args; };
        std::vector<Frame> pending;
        const auto skip = [&]() {
            while (i < s.size() && std::isspace(static_cast<unsigned char>(s[i]))) { ++i; }
        };
        const auto finish = [&]() -> H::ExprPtr {
            Frame frame = std::move(pending.back()); pending.pop_back();
            if (pending.empty()) { return apply(frame.head, frame.args, e, diags); }
            // All variables are globally declared. Keep child ownership in the
            // key so pointer identities cannot be reused after a node dies.
            // Unlike cached source substrings, this uses linear space for a
            // deeply nested expression and preserves shared subexpressions.
            const auto key = std::make_tuple(e.line, frame.head, frame.args);
            const auto found = intension_exprs_.find(key);
            if (found != intension_exprs_.end()) { return found->second; }
            auto expression = apply(frame.head, frame.args, e, diags);
            if (expression) { intension_exprs_.emplace(key, expression); }
            return expression;
        };
        for (;;) {
            skip();
            H::ExprPtr expression;
            if (!pending.empty() && i < s.size() && s[i] == ')') {
                ++i;
                expression = finish();
            } else {
                const std::size_t start = i;
                while (i < s.size()
                       && (std::isalnum(static_cast<unsigned char>(s[i])) || s[i] == '_'
                           || s[i] == '[' || s[i] == ']' || s[i] == '-' || s[i] == '.')) { ++i; }
                const std::string head = s.substr(start, i - start);
                if (head.empty()) {
                    diags.error(ErrorCode::E_PARSE,
                                "expected an operator or operand in the intension expression", at(e));
                    return nullptr;
                }
                skip();
                if (i < s.size() && s[i] == '(') {
                    ++i;
                    pending.push_back({head, {}});
                    continue;
                }
                long long value = 0;
                if (toInt(head, value)) { expression = num(value); }
                else if (findSource(head)) { expression = var(head); }
                else {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + head + "' is not a declared variable", at(e));
                    return nullptr;
                }
            }
            if (!expression) { return nullptr; }
            for (;;) {
                if (pending.empty()) { return expression; }
                pending.back().args.push_back(std::move(expression));
                skip();
                if (i < s.size() && s[i] == ',') { ++i; break; }
                if (i >= s.size() || s[i] != ')') {
                    diags.error(ErrorCode::E_PARSE,
                                "expected ',' or ')' in '" + pending.back().head + "(...)'", at(e));
                    return nullptr;
                }
                ++i;
                expression = finish();
                if (!expression) { return nullptr; }
            }
        }
    }

    H::ExprPtr apply(const std::string& op, const std::vector<H::ExprPtr>& arguments, const Elem& e,
                     Uir::Diagnostics& diags) {
        const Uir::SourceLoc l = at(e);
        std::vector<H::ExprPtr> a = arguments;
        // XCSP3 predicates denote the integer values 0 and 1. HIR keeps Bool
        // distinct from Int, so adapt numeric operand positions explicitly.
        // Use the relational builder so an undefined predicate does not become
        // a defined integer merely because it occurs beneath this coercion.
        const bool numeric = op == "add" || op == "mul" || op == "sub"
            || op == "neg" || op == "lt" || op == "le" || op == "gt"
            || op == "ge" || op == "eq" || op == "ne" || op == "abs"
            || op == "sqr" || op == "pow" || op == "min" || op == "max"
            || op == "dist" || op == "div" || op == "mod" || op == "set";
        for (std::size_t i = 0; i < a.size(); ++i) {
            const bool numericPosition = numeric || (op == "if" && i > 0)
                || ((op == "in" || op == "notin") && i == 0);
            if (numericPosition && a[i]->sort.kind == H::SortKind::BOOL) {
                a[i] = relational_.conditional(a[i], num(1), num(0), l);
            }
        }
        auto arity = [&](std::size_t n) {
            if (a.size() == n) { return true; }
            diags.error(ErrorCode::E_PARSE,
                        "'" + op + "' takes " + std::to_string(n) + " argument(s), got "
                            + std::to_string(a.size()), l);
            return false;
        };
        auto minimumArity = [&](std::size_t n) {
            if (a.size() >= n) { return true; }
            diags.error(ErrorCode::E_PARSE,
                        "'" + op + "' takes at least " + std::to_string(n)
                            + " argument(s), got " + std::to_string(a.size()), l);
            return false;
        };
        auto asBoolean = [&](const H::ExprPtr& expression) -> H::ExprPtr {
            if (!expression) { return nullptr; }
            if (expression->sort.kind == H::SortKind::BOOL) { return expression; }
            if (expression->kind == H::ExprKind::IDENT) {
                const auto it = findSource(expression->name);
                if (it != nullptr && !it->domain->sparse()
                    && it->domain->lo == 0 && it->domain->hi == 1) {
                    // XCSP3 boolExpr uses 01Var: false is 0 and true is 1.
                    return relational_.value(H::Op::EQ, {expression, num(1)}, l);
                }
            }
            diags.error(ErrorCode::E_TYPE,
                        "a Boolean XCSP3 operand must be a predicate or a variable "
                        "whose declared domain is exactly 0..1", l);
            return nullptr;
        };
        auto booleanArgs = [&]() {
            std::vector<H::ExprPtr> converted;
            converted.reserve(a.size());
            for (const H::ExprPtr& argument : a) {
                H::ExprPtr boolean = asBoolean(argument);
                if (!boolean) { return std::vector<H::ExprPtr>{}; }
                converted.push_back(std::move(boolean));
            }
            return converted;
        };
        auto allEqual = [&](const std::vector<H::ExprPtr>& terms) -> H::ExprPtr {
            std::vector<H::ExprPtr> equalities;
            equalities.reserve(terms.size() - 1);
            for (std::size_t i = 1; i < terms.size(); ++i) {
                equalities.push_back(
                    relational_.value(H::Op::EQ, {terms[0], terms[i]}, l));
            }
            return equalities.size() == 1
                ? equalities.front()
                : relational_.value(H::Op::AND, equalities, l);
        };
        if (op == "add") {
            return minimumArity(2) ? relational_.value(H::Op::ADD, a, l) : nullptr;
        }
        if (op == "mul") {
            return minimumArity(2) ? relational_.value(H::Op::MUL, a, l) : nullptr;
        }
        if (op == "sub") { return arity(2) ? relational_.value(H::Op::SUB, a, l) : nullptr; }
        if (op == "neg") {
            return arity(1) ? relational_.value(H::Op::SUB, {num(0), a[0]}, l) : nullptr;
        }
        if (op == "lt")  { return arity(2) ? relational_.value(H::Op::LT, a, l) : nullptr; }
        if (op == "le")  { return arity(2) ? relational_.value(H::Op::LE, a, l) : nullptr; }
        if (op == "gt")  { return arity(2) ? relational_.value(H::Op::GT, a, l) : nullptr; }
        if (op == "ge")  { return arity(2) ? relational_.value(H::Op::GE, a, l) : nullptr; }
        if (op == "eq")  { return minimumArity(2) ? allEqual(a) : nullptr; }
        if (op == "ne")  {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr equal = relational_.value(H::Op::EQ, a, l);
            return relational_.value(H::Op::NOT, {equal}, l);
        }
        if (op == "and" || op == "or" || op == "xor") {
            if (!minimumArity(2)) { return nullptr; }
            std::vector<H::ExprPtr> terms = booleanArgs();
            if (terms.size() != a.size()) { return nullptr; }
            const H::Op hir_op = op == "and" ? H::Op::AND
                                   : op == "or" ? H::Op::OR : H::Op::XOR;
            return relational_.value(hir_op, terms, l);
        }
        if (op == "not") {
            if (!arity(1)) { return nullptr; }
            H::ExprPtr term = asBoolean(a[0]);
            return term ? relational_.value(H::Op::NOT, {term}, l) : nullptr;
        }
        // No Op::IMPLIES or Op::IFF in the HIR; both expansions are exact.
        if (op == "imp") {
            if (!arity(2)) { return nullptr; }
            std::vector<H::ExprPtr> terms = booleanArgs();
            if (terms.size() != a.size()) { return nullptr; }
            H::ExprPtr negated = relational_.value(H::Op::NOT, {terms[0]}, l);
            return relational_.value(H::Op::OR, {negated, terms[1]}, l);
        }
        if (op == "iff") {
            if (!minimumArity(2)) { return nullptr; }
            std::vector<H::ExprPtr> terms = booleanArgs();
            return terms.size() == a.size() ? allEqual(terms) : nullptr;
        }
        if (op == "if")  {
            if (!arity(3)) { return nullptr; }
            H::ExprPtr condition = asBoolean(a[0]);
            return condition ? relational_.conditional(condition, a[1], a[2], l) : nullptr;
        }
        // abs, min, max and dist have no operator either, but unlike division
        // their ITE expansion is exact and total, so they are translated rather
        // than refused.
        if (op == "abs") {
            if (!arity(1)) { return nullptr; }
            H::ExprPtr nonnegative = relational_.value(H::Op::GE, {a[0], num(0)}, l);
            H::ExprPtr negative = relational_.value(H::Op::SUB, {num(0), a[0]}, l);
            return relational_.conditional(nonnegative, a[0], negative, l);
        }
        if (op == "sqr") {
            return arity(1) ? relational_.value(H::Op::MUL, {a[0], a[0]}, l) : nullptr;
        }
        if (op == "pow") {
            if (!arity(2)) { return nullptr; }
            if (a[1]->kind != H::ExprKind::LIT_INT || !H::fitsInt64(*a[1])
                || a[1]->int_value < 0 || a[1]->int_value > 64) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "pow is implemented exactly for literal exponents 0..64; "
                            "a symbolic, negative or larger exponent needs a bounded "
                            "piecewise encoding", l);
                return nullptr;
            }
            if (a[1]->int_value == 0) { return num(1); }
            H::ExprPtr power = a[0];
            for (long long exponent = 1; exponent < a[1]->int_value; ++exponent) {
                power = relational_.value(H::Op::MUL, {power, a[0]}, l);
            }
            return power;
        }
        if (op == "set") {
            const H::Sort set_sort = H::Sort::set(H::Sort::integer());
            H::ExprPtr empty = H::mkSetConst("set.empty", set_sort, l);
            if (a.empty()) { return empty; }
            std::vector<H::ExprPtr> inserted = a;
            inserted.push_back(std::move(empty));
            return relational_.value(H::Op::SET_INSERT, inserted, l);
        }
        if (op == "in" || op == "notin") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr member = relational_.value(H::Op::SET_MEMBER, a, l);
            return op == "in" ? member
                              : relational_.value(H::Op::NOT, {member}, l);
        }
        if (op == "min" || op == "max") {
            if (!minimumArity(2)) { return nullptr; }
            return extremumValue(std::move(a), op == "min", l);
        }
        if (op == "dist") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr d = relational_.value(H::Op::SUB, {a[0], a[1]}, l);
            H::ExprPtr nonnegative = relational_.value(H::Op::GE, {d, num(0)}, l);
            H::ExprPtr negative = relational_.value(H::Op::SUB, {num(0), d}, l);
            return relational_.conditional(nonnegative, d, negative, l);
        }
        if (op == "div" || op == "mod") {
            if (!arity(2)) { return nullptr; }
            noteRelationalPartiality(e);
            H::ExprPtr domain;
            if (a[1]->kind == H::ExprKind::LIT_INT && H::fitsInt64(*a[1])) {
                // A known nonzero divisor contributes no definedness guard.
                // Retaining syntactic (k != 0) for every constant divisor
                // unnecessarily keeps every enclosing expression partial.
                if (a[1]->int_value == 0) { domain = H::mkBool(false, l); }
            } else {
                domain = H::mkOp(
                    H::Op::NOT, {H::mkOp(H::Op::EQ, {a[1], num(0)}, l)}, l);
            }
            return relational_.value(op == "div" ? H::Op::DIV_TRUNC : H::Op::MOD_TRUNC,
                                     a, l, std::move(domain));
        }
        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "the intension operator '" + op + "' is not implemented", l);
        return nullptr;
    }

    // ---- extension -------------------------------------------------------

    struct TableCell {
        long long value = 0;
        bool wildcard = false;

        bool operator<(const TableCell& other) const {
            if (wildcard != other.wildcard) { return wildcard < other.wildcard; }
            return value < other.value;
        }
    };

    // Flat numeric storage avoids a string object per cell and an allocation
    // per row. A separate wildcard bit preserves the entire signed value range.
    struct TupleTable {
        std::size_t width;
        std::vector<long long> values;
        std::vector<bool> wildcards;

        std::size_t size() const { return values.size() / width; }
        bool empty() const { return values.empty(); }
        void append(TableCell cell) {
            values.push_back(cell.value);
            wildcards.push_back(cell.wildcard);
        }
        TableCell cell(std::size_t row, std::size_t column) const {
            const std::size_t i = row * width + column;
            return {values[i], wildcards[i]};
        }
    };

    struct ExtensionTemplateOccurrence {
        Elem* element = nullptr;
        std::string kind;
        std::string_view table_text;
        std::shared_ptr<const std::string> table_storage;
        std::vector<std::string> scope;
        std::vector<std::size_t> alias_classes;
    };

    struct SharedExtensionTemplate {
        std::string kind;
        // Retain streaming storage after its original XML node is consumed.
        // Inline input gets one owned representative copy instead.
        std::shared_ptr<const std::string> table_text;
        std::vector<std::string> representative_scope;
        std::vector<std::size_t> representative_slots;
        std::size_t occurrences = 0;
        bool processed = false;
        bool disabled = false;
        bool ready = false;
        bool constant = false;
        bool constant_value = false;
        std::string function_name;
    };

    /** Parse and validate each integer/wildcard once, before table rewrites. */
    bool tuples(std::string_view text, TupleTable& out, const Elem& e,
                Uir::Diagnostics& diags) {
        std::size_t i = 0;
        std::string token;
        while (i < text.size()) {
            while (i < text.size() && std::isspace(static_cast<unsigned char>(text[i]))) { ++i; }
            if (i >= text.size()) { break; }
            if (text[i] != '(') {
                diags.error(ErrorCode::E_PARSE, "expected '(' starting a tuple", at(e));
                return false;
            }
            ++i;
            const std::size_t close = text.find(')', i);
            if (close == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "an unterminated tuple", at(e));
                return false;
            }
            std::size_t columns = 0;
            token.clear();
            for (std::size_t k = i; k <= close; ++k) {
                if (k == close || text[k] == ',') {
                    TableCell cell;
                    cell.wildcard = token == "*";
                    if (!cell.wildcard && !toInt(token, cell.value)) {
                        diags.error(ErrorCode::E_PARSE,
                                    "'" + token + "' is not an integer or '*'", at(e));
                        return false;
                    }
                    out.append(cell);
                    ++columns;
                    token.clear();
                } else if (!std::isspace(static_cast<unsigned char>(text[k]))) {
                    token += text[k];
                }
            }
            if (columns != out.width) {
                diags.error(ErrorCode::E_PARSE,
                            "a tuple has " + std::to_string(columns)
                                + " entries but the scope has " + std::to_string(out.width),
                            at(e));
                return false;
            }
            i = close + 1;
        }
        return true;
    }

    H::ExprPtr tableEquality(const std::string& variable, long long value) {
        // Competition groups reuse these total predicates across thousands of
        // tables. Keep one immutable expression per model/variable/value;
        // occurrence locations remain on the surrounding constraints.
        auto& values = table_equalities_[variable];
        const auto found = values.find(value);
        if (found != values.end()) { return found->second; }
        H::ExprPtr equality = H::mkOp(H::Op::EQ, {var(variable), num(value)});
        values.emplace(value, equality);
        return equality;
    }

    /** The conjunct saying variable `v` takes the value in one tuple cell.
     *
     *  **The `*` obligation.** A short table's `*` means "any value in this
     *  column's DECLARED domain". Expanding it over that domain is the whole
     *  content of the source rule; treating `*` as a literal makes the row
     *  match nothing. Although dropping a guard would be wrong if domains were
     *  implicit, this frontend enforces every declaration's exact domain in
     *  the complete model. The wildcard is therefore always true there and
     *  contributes no local expression. */
    H::ExprPtr cell(const std::string& v, TableCell value, const Elem& e) {
        if (value.wildcard) { return nullptr; }
        return tableEquality(v, value.value);
    }

    bool complementDenseTable(const std::vector<std::string>& scope,
                              TupleTable& rows) const {
        // Complement only over the complete declared Cartesian product. This
        // is exact even for sparse domains and repeated variables in the scope.
        // Bound the search work; large domains and short tables keep their
        // original encoding instead of being rejected or expanded speculatively.
        const std::size_t cell_budget = 250000;
        if (scope.size() > cell_budget || rows.empty()) { return false; }
        const std::size_t product_limit = std::min(
            cell_budget / scope.size(),
            rows.size() > cell_budget / 2 ? cell_budget : 2 * rows.size());
        std::size_t product = 1;
        std::vector<std::size_t> sizes;
        for (const std::string& variable : scope) {
            const Domain& d = *sourceVariable(variable).domain;
            if (d.product_bound) { return false; }
            const unsigned long long width = static_cast<unsigned long long>(d.hi)
                - static_cast<unsigned long long>(d.lo);
            if (!d.sparse() && width >= product_limit / product) { return false; }
            const std::size_t size = d.sparse() ? d.values.size()
                : static_cast<std::size_t>(width) + 1;
            if (size > product_limit / product) { return false; }
            product *= size;
            sizes.push_back(size);
        }
        if (rows.size() <= product / 2) { return false; }
        std::set<std::vector<long long>> listed;
        for (std::size_t row = 0; row < rows.size(); ++row) {
            std::vector<long long> values;
            bool in_domain = true;
            for (std::size_t i = 0; i < scope.size(); ++i) {
                const TableCell entry = rows.cell(row, i);
                if (entry.wildcard) { return false; }
                const long long value = entry.value;
                const Domain& d = *sourceVariable(scope[i]).domain;
                in_domain = in_domain && value >= d.lo && value <= d.hi
                    && (!d.sparse()
                        || std::find(d.values.begin(), d.values.end(), value) != d.values.end());
                values.push_back(value);
            }
            if (in_domain) { listed.insert(std::move(values)); }
        }
        if (listed.size() <= product / 2) { return false; }
        TupleTable missing{scope.size(), {}, {}};
        for (std::size_t index = 0; index < product; ++index) {
            std::size_t position = index;
            std::vector<long long> tuple;
            for (std::size_t i = 0; i < scope.size(); ++i) {
                const Domain& d = *sourceVariable(scope[i]).domain;
                const std::size_t offset = position % sizes[i];
                position /= sizes[i];
                tuple.push_back(d.sparse() ? d.values[offset]
                    : d.lo + static_cast<long long>(offset));
            }
            if (listed.find(tuple) != listed.end()) { continue; }
            for (const long long value : tuple) {
                missing.append({value, false});
            }
        }
        rows = std::move(missing);
        return true;
    }

    H::ExprPtr factoredTable(const std::vector<std::string>& scope,
                            const TupleTable& rows,
                            const Elem& e,
                            std::size_t& operator_count) {
        // A reduced decision diagram factors identical suffix relations. It
        // uses only Boolean combinations of the original column equalities:
        // there are no witnesses, quantifiers, or new source observables.
        operator_count = 0;
        using Edge = std::pair<TableCell, std::size_t>;
        using Key = std::pair<std::size_t, std::vector<Edge>>;
        std::map<Key, std::size_t> interned;
        std::map<std::pair<std::size_t, TableCell>, H::ExprPtr> cells;
        std::vector<H::ExprPtr> nodes{H::mkBool(true, at(e))};
        // Sort row indices once. Every prefix partition is then a contiguous
        // interval, so trie construction needs no map or row vector per
        // cell. The lexicographic TableCell order is the same as the old maps;
        // duplicate rows and wildcard edges retain their exact meaning.
        std::vector<std::size_t> selected;
        selected.reserve(rows.size());
        for (std::size_t row = 0; row < rows.size(); ++row) { selected.push_back(row); }
        const auto rowLess = [&](std::size_t a, std::size_t b) {
            for (std::size_t column = 0; column < scope.size(); ++column) {
                const TableCell left = rows.cell(a, column);
                const TableCell right = rows.cell(b, column);
                if (left < right) { return true; }
                if (right < left) { return false; }
            }
            return false;
        };
        // Competition generators often emit tuples in prefix order already.
        // Verify that order in linear time before paying for a full sort.
        if (!std::is_sorted(selected.begin(), selected.end(), rowLess)) {
            std::sort(selected.begin(), selected.end(), rowLess);
        }
        const auto finishNode = [&](std::size_t column, std::vector<Edge> edges) {
            Key key{column, edges};
            const auto found = interned.find(key);
            if (found != interned.end()) { return found->second; }

            // Group raw cells before building equalities. Equal suffixes often
            // collect a long arithmetic progression of values; recognize that
            // set first so no per-value EQ nodes are allocated speculatively.
            std::map<std::size_t, std::vector<long long>> values_by_child;
            std::unordered_set<std::size_t> wildcard_children;
            for (const Edge& edge : edges) {
                if (edge.first.wildcard) { wildcard_children.insert(edge.second); }
                else { values_by_child[edge.second].push_back(edge.first.value); }
            }
            auto unsignedGap = [](long long high, long long low) {
                return static_cast<unsigned long long>(high)
                     - static_cast<unsigned long long>(low);
            };
            auto labelGuard = [&](std::vector<long long> labels) {
                std::sort(labels.begin(), labels.end());
                labels.erase(std::unique(labels.begin(), labels.end()), labels.end());
                const Domain& domain = *sourceVariable(scope[column]).domain;

                // If the labels contain every declared value, the global
                // domain constraint makes this disjunction true. Sparse
                // domains are enumerated; intervals are checked by endpoints
                // and cardinality without iterating over their values.
                bool covers_domain = false;
                if (domain.product_bound) {
                    // Keep the explicit labels; do not mistake an intentionally
                    // absent enumeration for an empty declared set.
                    covers_domain = false;
                } else if (domain.sparse()) {
                    covers_domain = std::includes(labels.begin(), labels.end(),
                                                   domain.values.begin(),
                                                   domain.values.end());
                } else if (!labels.empty()) {
                    const auto first = std::lower_bound(labels.begin(), labels.end(), domain.lo);
                    const auto after = std::upper_bound(labels.begin(), labels.end(), domain.hi);
                    if (first != after && *first == domain.lo && *(after - 1) == domain.hi) {
                        const auto count = static_cast<unsigned long long>(after - first);
                        covers_domain = unsignedGap(domain.hi, domain.lo) == count - 1;
                    }
                }
                if (covers_domain) { return H::mkBool(true, at(e)); }

                // Use a range/congruence guard only when it is cheaper than
                // the exact equality disjunction. Unsigned differences avoid
                // signed overflow across negative or extreme Int endpoints;
                // the positive modulus is rendered as an arbitrary-size HIR
                // numeral rather than narrowed back to long long.
                std::size_t disjunction_cost = labels.size() > 1 ? 1 : 0;
                for (const long long value : labels) {
                    if (cells.find(std::make_pair(column, TableCell{value, false}))
                        == cells.end()) {
                        ++disjunction_cost;
                    }
                }
                bool progression = labels.size() >= 3;
                const unsigned long long step = progression
                    ? unsignedGap(labels[1], labels[0]) : 0;
                progression = progression && step != 0;
                for (std::size_t i = 2; progression && i < labels.size(); ++i) {
                    progression = unsignedGap(labels[i], labels[i - 1]) == step;
                }
                if (progression) {
                    const std::size_t guard_cost = step == 1 ? 3
                        : (labels.front() == 0 ? 5 : 6);
                    if (guard_cost < disjunction_cost) {
                        std::vector<H::ExprPtr> terms{
                            H::mkOp(H::Op::GE, {var(scope[column]), num(labels.front())}, at(e)),
                            H::mkOp(H::Op::LE, {var(scope[column]), num(labels.back())}, at(e))};
                        if (step > 1) {
                            H::ExprPtr offset = var(scope[column]);
                            if (labels.front() != 0) {
                                offset = H::mkOp(H::Op::SUB,
                                                 {offset, num(labels.front())}, at(e));
                            }
                            H::ExprPtr divisor = H::mkInt(std::to_string(step), at(e));
                            H::ExprPtr residue = H::mkOp(H::Op::MOD_EUCLID,
                                                         {std::move(offset),
                                                          std::move(divisor)}, at(e));
                            terms.push_back(H::mkOp(H::Op::EQ,
                                                    {std::move(residue), num(0)}, at(e)));
                        }
                        return conjunction(std::move(terms), e);
                    }
                }

                // A shared suffix can label several dense value intervals
                // separated by holes or outliers. Encode each maximal
                // contiguous run directly, but only if the exact operator-DAG
                // cost is below the equality disjunction. Discover all runs
                // before creating any equality nodes so a losing candidate
                // leaves no speculative per-value expressions behind.
                std::vector<std::pair<std::size_t, std::size_t>> runs;
                for (std::size_t begin = 0; begin < labels.size();) {
                    std::size_t end = begin + 1;
                    while (end < labels.size()
                           && unsignedGap(labels[end], labels[end - 1]) == 1) {
                        ++end;
                    }
                    runs.emplace_back(begin, end);
                    begin = end;
                }
                std::size_t range_cost = runs.size() > 1 ? 1 : 0;
                for (const auto& run : runs) {
                    if (run.second - run.first == 1) {
                        const TableCell key_cell{labels[run.first], false};
                        if (cells.find(std::make_pair(column, key_cell)) == cells.end()) {
                            ++range_cost;
                        }
                    } else {
                        range_cost += 3;  // GE, LE, AND
                    }
                }
                if (range_cost < disjunction_cost) {
                    std::vector<H::ExprPtr> guards;
                    guards.reserve(runs.size());
                    for (const auto& run : runs) {
                        if (run.second - run.first == 1) {
                            const TableCell key_cell{labels[run.first], false};
                            auto existing = cells.find(std::make_pair(column, key_cell));
                            if (existing == cells.end()) {
                                existing = cells.emplace(std::make_pair(column, key_cell),
                                    tableEquality(scope[column], labels[run.first])).first;
                            }
                            guards.push_back(existing->second);
                        } else {
                            guards.push_back(conjunction(
                                {H::mkOp(H::Op::GE,
                                         {var(scope[column]), num(labels[run.first])}, at(e)),
                                 H::mkOp(H::Op::LE,
                                         {var(scope[column]), num(labels[run.second - 1])}, at(e))}, e));
                        }
                    }
                    return disjunction(std::move(guards), e);
                }

                std::vector<H::ExprPtr> equalities;
                equalities.reserve(labels.size());
                for (const long long value : labels) {
                    const TableCell key_cell{value, false};
                    const auto cell_key = std::make_pair(column, key_cell);
                    auto existing = cells.find(cell_key);
                    if (existing == cells.end()) {
                        existing = cells.emplace(cell_key,
                            tableEquality(scope[column], value)).first;
                    }
                    equalities.push_back(existing->second);
                }
                return disjunction(std::move(equalities), e);
            };
            std::vector<H::ExprPtr> alternatives;
            std::set<std::size_t> children;
            for (const auto& child : values_by_child) { children.insert(child.first); }
            children.insert(wildcard_children.begin(), wildcard_children.end());
            bool accepts_every_value = false;
            for (const std::size_t child : children) {
                if (wildcard_children.find(child) != wildcard_children.end()) {
                    if (child == 0) { accepts_every_value = true; break; }
                    alternatives.push_back(nodes[child]);
                    continue;
                }
                H::ExprPtr guard = labelGuard(values_by_child.at(child));
                if (guard->kind == H::ExprKind::LIT_BOOL && guard->bool_value) {
                    if (child == 0) { accepts_every_value = true; break; }
                    alternatives.push_back(nodes[child]);
                } else if (child == 0) {
                    alternatives.push_back(std::move(guard));
                } else {
                    alternatives.push_back(conjunction({std::move(guard), nodes[child]}, e));
                }
            }
            if (accepts_every_value) {
                interned.emplace(std::move(key), std::size_t{0});
                return std::size_t{0};
            }
            const std::size_t id = nodes.size();
            nodes.push_back(disjunction(std::move(alternatives), e));
            interned.emplace(std::move(key), id);
            return id;
        };
        struct Frame {
            std::size_t column, next, end;
            std::vector<Edge> edges;
            TableCell label{};
            std::size_t after = 0;
        };
        std::vector<Frame> pending{{0, 0, selected.size(), {}}};
        std::size_t result_id = 0;
        while (!pending.empty()) {
            auto& frame = pending.back();
            if (frame.column != scope.size() && frame.next != frame.end) {
                frame.label = rows.cell(selected[frame.next], frame.column);
                frame.after = frame.next + 1;
                while (frame.after < frame.end) {
                    const auto next = rows.cell(selected[frame.after], frame.column);
                    if (frame.label < next || next < frame.label) { break; }
                    ++frame.after;
                }
                pending.push_back({frame.column + 1, frame.next, frame.after, {}});
                continue;
            }
            result_id = frame.column == scope.size() ? 0
                : finishNode(frame.column, std::move(frame.edges));
            pending.pop_back();
            if (!pending.empty()) {
                auto& parent = pending.back();
                parent.edges.emplace_back(parent.label, result_id);
                parent.next = parent.after;
            }
        }
        const H::ExprPtr result = nodes[result_id];
        // Count only operators reachable in the emitted expression, once per DAG node.
        operator_count = countOperators(result);
        return result;
    }

    /** The exact multi-column relation used by ordinary extension lowering.
     *  Keeping this shared lets group helpers reuse the same dense complement,
     *  domain-aware factoring, and direct fallback choices as expanded rows. */
    H::ExprPtr extensionRelation(const std::vector<std::string>& scope,
                                 TupleTable& rows, bool& positive,
                                 const Elem& e) {
        if (complementDenseTable(scope, rows)) { positive = !positive; }
        if (rows.empty()) { return H::mkBool(!positive, at(e)); }
        if (rows.size() > 1) {
            std::size_t factored_count = 0;
            H::ExprPtr relation = factoredTable(scope, rows, e, factored_count);
            if (!relation) { return nullptr; }
            std::size_t direct_count = 1;  // outer OR or AND
            for (std::size_t row = 0; row < rows.size(); ++row) {
                std::size_t conjuncts = 0;
                for (std::size_t i = 0; i < scope.size(); ++i) {
                    if (!rows.cell(row, i).wildcard) { ++conjuncts; ++direct_count; }
                }
                direct_count += (conjuncts > 1 ? 1 : 0) + (!positive ? 1 : 0);
            }
            // A diagonal table has no reusable suffixes: its decision chain
            // can be larger than a single conjunction per row. Keep the
            // original encoding unless factoring reduces the operator DAG.
            if (factored_count + (!positive ? 1 : 0) < direct_count) {
                return positive ? relation
                                : H::mkOp(H::Op::NOT, {relation}, at(e));
            }
        }
        std::vector<H::ExprPtr> row_forms;
        for (std::size_t row = 0; row < rows.size(); ++row) {
            std::vector<H::ExprPtr> conj;
            for (std::size_t k = 0; k < scope.size(); ++k) {
                H::ExprPtr f = cell(scope[k], rows.cell(row, k), e);
                if (f) { conj.push_back(f); }
            }
            row_forms.push_back(conj.empty() ? H::mkBool(true, at(e))
                                : conj.size() == 1 ? conj.front()
                                                   : H::mkOp(H::Op::AND, conj, at(e)));
        }
        if (positive) {
            return row_forms.size() == 1 ? row_forms.front()
                                         : H::mkOp(H::Op::OR, row_forms, at(e));
        }
        // Exactly the listed tuples are forbidden: conjoin their negations.
        // The optional complement above enumerates the complete declared
        // Cartesian product before swapping table polarity.
        std::vector<H::ExprPtr> negs;
        negs.reserve(row_forms.size());
        for (const auto& form : row_forms) {
            negs.push_back(H::mkOp(H::Op::NOT, {form}, at(e)));
        }
        return negs.size() == 1 ? negs.front()
                                : H::mkOp(H::Op::AND, negs, at(e));
    }

    static std::vector<std::size_t> scopeAliasClasses(
            const std::vector<std::string>& scope) {
        std::unordered_map<std::string, std::size_t> classes;
        std::vector<std::size_t> result;
        result.reserve(scope.size());
        for (const std::string& variable : scope) {
            const auto inserted = classes.emplace(variable, classes.size());
            result.push_back(inserted.first->second);
        }
        return result;
    }

    static std::vector<std::size_t> scopeRepresentativeSlots(
            const std::vector<std::size_t>& alias_classes) {
        std::vector<std::size_t> result;
        std::unordered_set<std::size_t> seen;
        for (std::size_t i = 0; i < alias_classes.size(); ++i) {
            if (seen.insert(alias_classes[i]).second) { result.push_back(i); }
        }
        return result;
    }

    bool sameScopeTemplate(const ExtensionTemplateOccurrence& left,
                           const ExtensionTemplateOccurrence& right) const {
        if (left.scope.size() != right.scope.size()
            || left.alias_classes != right.alias_classes) {
            return false;
        }
        for (std::size_t i = 0; i < left.scope.size(); ++i) {
            const auto left_domain = findSource(left.scope[i]);
            const auto right_domain = findSource(right.scope[i]);
            if (left_domain == nullptr || right_domain == nullptr) {
                return false;
            }
            const Domain& a = *left_domain->domain;
            const Domain& b = *right_domain->domain;
            if (a.lo != b.lo || a.hi != b.hi || a.values != b.values
                || a.product_bound != b.product_bound) { return false; }
        }
        return true;
    }

    void indexOrdinaryExtensionTemplates(Elem& constraints_node) {
        using CandidateGroup = std::vector<ExtensionTemplateOccurrence>;
        std::unordered_map<std::size_t, std::vector<CandidateGroup>> buckets;
        const auto collect = [&](Elem& extension) {
            if (!extension.attrs.empty() || extension.children.size() != 2) { return; }
            Elem* list = nullptr;
            Elem* table = nullptr;
            std::string kind;
            for (Elem& child : extension.children) {
                if (child.name == "list" && !list) { list = &child; }
                else if ((child.name == "supports" || child.name == "conflicts")
                         && !table) {
                    table = &child;
                    kind = child.name;
                } else {
                    return;
                }
            }
            if (!list || !table || !list->attrs.empty() || !list->children.empty()
                || !table->attrs.empty() || !table->children.empty()) {
                return;
            }
            const std::string_view text = table->textView();
            if (text.empty()) { return; }
            Uir::Diagnostics probe;
            std::vector<std::string> scope;
            if (!varList(std::string(list->textView()), scope, *list, probe)
                || scope.size() < 2) {
                return;
            }
            ExtensionTemplateOccurrence occurrence;
            occurrence.element = &extension;
            occurrence.kind = std::move(kind);
            occurrence.table_text = text;
            occurrence.table_storage = table->table_storage;
            occurrence.scope = std::move(scope);
            occurrence.alias_classes = scopeAliasClasses(occurrence.scope);

            std::size_t hash = std::hash<std::string_view>{}(text);
            hash ^= std::hash<std::string>{}(occurrence.kind) + 0x9e3779b9
                + (hash << 6) + (hash >> 2);
            auto& groups = buckets[hash];
            for (CandidateGroup& group : groups) {
                const ExtensionTemplateOccurrence& representative = group.front();
                if (representative.kind == occurrence.kind
                    && representative.table_text.size() == text.size()
                    && representative.table_text == text
                    && sameScopeTemplate(representative, occurrence)) {
                    group.push_back(std::move(occurrence));
                    return;
                }
            }
            groups.push_back(CandidateGroup{std::move(occurrence)});
        };

        using ChildIterator = std::list<Elem>::iterator;
        std::vector<std::pair<ChildIterator, ChildIterator>> pending{
            {constraints_node.children.begin(), constraints_node.children.end()}};
        while (!pending.empty()) {
            auto& frame = pending.back();
            if (frame.first == frame.second) { pending.pop_back(); continue; }
            Elem& child = *frame.first++;
            if (child.name == "extension") { collect(child); }
            else if (child.name == "block") {
                pending.emplace_back(child.children.begin(), child.children.end());
            }
        }

        for (auto& bucket : buckets) {
            for (CandidateGroup& group : bucket.second) {
                if (group.size() < 2) { continue; }
                SharedExtensionTemplate memo;
                memo.kind = group.front().kind;
                memo.table_text = group.front().table_storage;
                if (!memo.table_text) {
                    memo.table_text = std::make_shared<const std::string>(group.front().table_text);
                }
                memo.representative_scope = group.front().scope;
                memo.representative_slots = scopeRepresentativeSlots(
                    group.front().alias_classes);
                memo.occurrences = group.size();
                const std::size_t memo_index = extension_templates_.size();
                extension_templates_.push_back(std::move(memo));
                for (const ExtensionTemplateOccurrence& occurrence : group) {
                    extension_template_by_element_.emplace(occurrence.element, memo_index);
                }
            }
        }
    }

    H::ExprPtr bindRelation(const H::ExprPtr& root,
                            const std::unordered_map<std::string, std::string>& names,
                            bool allow_globals) const {
        if (!root) { return nullptr; }
        struct Frame { H::ExprPtr expression; std::size_t next = 0; };
        std::vector<Frame> pending{{root}};
        std::unordered_set<const H::Expr*> active{root.get()};
        std::unordered_map<const H::Expr*, H::ExprPtr> rebound;
        while (!pending.empty()) {
            auto& frame = pending.back();
            const auto* expression = frame.expression.get();
            if (expression->kind == H::ExprKind::IDENT) {
                const auto found = names.find(expression->name);
                if (found != names.end()) {
                    rebound.emplace(expression, H::mkBoundVar(
                        found->second, expression->sort, expression->loc));
                } else if (allow_globals && findSource(expression->name)) {
                    rebound.emplace(expression, frame.expression);
                } else { return nullptr; }
            } else {
                if (expression->kind != H::ExprKind::OP
                    && expression->kind != H::ExprKind::LIT_BOOL
                    && expression->kind != H::ExprKind::LIT_INT
                    && !(allow_globals && expression->kind == H::ExprKind::LIT_SET)) {
                    return nullptr;
                }
                if (frame.next < expression->args.size()) {
                    const auto& child = expression->args[frame.next++];
                    if (!child) { return nullptr; }
                    if (rebound.find(child.get()) != rebound.end()) { continue; }
                    if (!active.insert(child.get()).second) { return nullptr; }
                    pending.push_back({child});
                    continue;
                }
                auto copy = std::make_shared<H::Expr>(*expression);
                copy->args.clear();
                copy->args.reserve(expression->args.size());
                for (const auto& child : expression->args) {
                    copy->args.push_back(rebound.at(child.get()));
                }
                rebound.emplace(expression, std::move(copy));
            }
            active.erase(expression);
            pending.pop_back();
        }
        return rebound.at(root.get());
    }

    bool makeSharedExtensionDefinition(const std::vector<std::string>& scope,
                                       const H::ExprPtr& relation,
                                       Uir::SourceLoc definition_loc,
                                       H::FunDecl& definition,
                                       std::size_t& body_operators,
                                       bool allow_globals = false) {
        const std::vector<std::size_t> slots = scopeRepresentativeSlots(
            scopeAliasClasses(scope));
        const std::string function_name = freshGroupFunctionName();
        std::vector<H::Binder> binders;
        binders.reserve(slots.size());
        std::unordered_set<std::string> bound_names;
        for (std::size_t i = 0; i < slots.size(); ++i) {
            H::Binder binder;
            binder.name = freshGroupBinderName(function_name, i, bound_names);
            binder.sort = H::Sort::integer();
            bound_names.insert(binder.name);
            binders.push_back(std::move(binder));
        }
        std::unordered_map<std::string, std::string> bound_by_actual;
        for (std::size_t i = 0; i < slots.size(); ++i) {
            bound_by_actual.emplace(scope[slots[i]], binders[i].name);
        }

        H::ExprPtr body = bindRelation(relation, bound_by_actual, allow_globals);
        if (!body) { return false; }
        body_operators = countOperators(body);

        definition.name = function_name;
        definition.params.assign(slots.size(), H::Sort::integer());
        definition.result = H::Sort::boolean();
        definition.loc = definition_loc;
        definition.binders = std::move(binders);
        definition.body = std::move(body);
        definition.auxiliary = true;
        return true;
    }

    bool extension(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        if (!list) {
            diags.error(ErrorCode::E_PARSE, "<extension> has no <list>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        if (scope.empty()) {
            diags.error(ErrorCode::E_PARSE, "<extension> has an empty scope", at(e));
            return false;
        }
        const Elem* sup = e.child("supports");
        const Elem* con = e.child("conflicts");
        if ((sup == nullptr) == (con == nullptr)) {
            diags.error(ErrorCode::E_PARSE,
                        "<extension> needs exactly one of <supports> and <conflicts>",
                        at(e));
            return false;
        }
        const Elem& table = sup ? *sup : *con;
        if (scope.size() == 1) {
            std::vector<H::ExprPtr> entries;
            for (const std::string& token : words(std::string(table.textView()))) {
                if (token == "*") {
                    entries.push_back(H::mkBool(true, at(e)));
                    continue;
                }
                const std::size_t dots = token.find("..");
                if (dots != std::string::npos) {
                    long long lo = 0, hi = 0;
                    if (!toInt(token.substr(0, dots), lo)
                        || !toInt(token.substr(dots + 2), hi) || hi < lo) {
                        diags.error(ErrorCode::E_PARSE,
                                    "unary table interval '" + token + "' is invalid", at(e));
                        return false;
                    }
                    entries.push_back(conjunction(
                        {H::mkOp(H::Op::GE, {var(scope[0]), num(lo)}, at(e)),
                         H::mkOp(H::Op::LE, {var(scope[0]), num(hi)}, at(e))}, e));
                    continue;
                }
                long long value = 0;
                if (!toInt(token, value)) {
                    diags.error(ErrorCode::E_PARSE,
                                "unary table entry '" + token
                                    + "' is not an integer or interval", at(e));
                    return false;
                }
                entries.push_back(H::mkOp(H::Op::EQ,
                                           {var(scope[0]), num(value)}, at(e)));
            }
            if (sup) {
                addFormula(disjunction(std::move(entries), e), e);
            } else {
                std::vector<H::ExprPtr> forbidden;
                for (H::ExprPtr& entry : entries) {
                    forbidden.push_back(H::mkOp(H::Op::NOT, {entry}, at(e)));
                }
                addFormula(conjunction(std::move(forbidden), e), e);
            }
            return true;
        }

        SharedExtensionTemplate* shared = nullptr;
        auto shared_index = extension_template_by_element_.find(&e);
        if (shared_index != extension_template_by_element_.end()
            && shared_index->second < extension_templates_.size()) {
            const std::size_t index = shared_index->second;
            // Constraints are erased as soon as they are lowered. Remove the
            // address key now so a later temporary slide copy cannot reuse a
            // freed node's address and inherit its memo accidentally.
            extension_template_by_element_.erase(shared_index);
            shared = &extension_templates_[index];
            if (shared->kind != table.name
                || *shared->table_text != table.textView()) {
                shared->disabled = true;
                shared = nullptr;
            } else if (shared->disabled) {
                shared = nullptr;
            } else if (shared->ready) {
                if (shared->constant) {
                    addFormula(H::mkBool(shared->constant_value, at(e)), e);
                } else {
                    std::vector<H::ExprPtr> arguments;
                    arguments.reserve(shared->representative_slots.size());
                    for (const std::size_t slot : shared->representative_slots) {
                        arguments.push_back(var(scope[slot]));
                    }
                    addFormula(H::mkApply(shared->function_name, H::Sort::boolean(),
                                          std::move(arguments), at(e)), e);
                }
                return true;
            } else if (shared->processed) {
                shared = nullptr;
            }
        }

        TupleTable rows{scope.size(), {}, {}};
        if (!tuples(table.textView(), rows, e, diags)) { return false; }
        bool positive = sup != nullptr;
        H::ExprPtr relation = extensionRelation(scope, rows, positive, e);
        if (!relation) { return false; }

        if (shared) {
            shared->processed = true;
            if (relation->kind == H::ExprKind::LIT_BOOL) {
                shared->constant = true;
                shared->constant_value = relation->bool_value;
                shared->ready = true;
                addFormula(H::mkBool(shared->constant_value, at(e)), e);
                return true;
            }
            H::FunDecl definition;
            std::size_t body_operators = 0;
            if (makeSharedExtensionDefinition(scope, relation, at(e),
                                              definition, body_operators)
                && body_operators > 1
                && shared->occurrences > body_operators / (body_operators - 1)) {
                shared->function_name = definition.name;
                shared->ready = true;
                model_->funs.push_back(std::move(definition));
                std::vector<H::ExprPtr> arguments;
                arguments.reserve(shared->representative_slots.size());
                for (const std::size_t slot : shared->representative_slots) {
                    arguments.push_back(var(scope[slot]));
                }
                addFormula(H::mkApply(shared->function_name, H::Sort::boolean(),
                                      std::move(arguments), at(e)), e);
                return true;
            }
            shared->disabled = true;
        }
        addFormula(std::move(relation), e);
        return true;
    }

    static std::string trim(std::string text) {
        const auto first = std::find_if_not(
            text.begin(), text.end(), [](unsigned char ch) { return std::isspace(ch); });
        const auto last = std::find_if_not(
            text.rbegin(), text.rend(), [](unsigned char ch) { return std::isspace(ch); }).base();
        return first < last ? std::string(first, last) : std::string{};
    }

    bool transitions(const Elem& node, std::vector<Transition>& out,
                     Uir::Diagnostics& diags) const {
        const std::string& text = node.text;
        std::size_t i = 0;
        while (i < text.size()) {
            while (i < text.size()
                   && std::isspace(static_cast<unsigned char>(text[i]))) { ++i; }
            if (i == text.size()) { break; }
            if (text[i] != '(') {
                diags.error(ErrorCode::E_PARSE,
                            "a transition must start with '('", at(node));
                return false;
            }
            const std::size_t first_comma = text.find(',', i + 1);
            const std::size_t second_comma = first_comma == std::string::npos
                ? std::string::npos : text.find(',', first_comma + 1);
            const std::size_t close = second_comma == std::string::npos
                ? std::string::npos : text.find(')', second_comma + 1);
            if (first_comma == std::string::npos || second_comma == std::string::npos
                || close == std::string::npos) {
                diags.error(ErrorCode::E_PARSE,
                            "an automaton transition must have form (source,value,target)",
                            at(node));
                return false;
            }
            Transition transition;
            transition.source = trim(text.substr(i + 1, first_comma - i - 1));
            const std::string value =
                trim(text.substr(first_comma + 1, second_comma - first_comma - 1));
            transition.target =
                trim(text.substr(second_comma + 1, close - second_comma - 1));
            if (transition.source.empty() || transition.target.empty()
                || !toInt(value, transition.value)) {
                diags.error(ErrorCode::E_PARSE,
                            "an automaton transition has an empty state or non-integer label",
                            at(node));
                return false;
            }
            out.push_back(std::move(transition));
            i = close + 1;
        }
        if (out.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "an automaton has no transitions", at(node));
            return false;
        }
        return true;
    }

    bool languageConstraint(const Elem& e, bool mdd, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* transition_node = e.child("transitions");
        if (!list || !transition_node) {
            diags.error(ErrorCode::E_PARSE,
                        e.name + " requires <list> and <transitions>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        if (scope.empty()) {
            diags.error(ErrorCode::E_PARSE, e.name + " has an empty variable list", at(e));
            return false;
        }
        std::vector<Transition> edges;
        if (!transitions(*transition_node, edges, diags)) { return false; }

        std::set<std::string> state_set;
        for (const Transition& edge : edges) {
            state_set.insert(edge.source);
            state_set.insert(edge.target);
        }
        std::string start;
        std::vector<std::string> finals;
        if (!mdd) {
            const Elem* start_node = e.child("start");
            const Elem* final_node = e.child("final");
            if (!start_node || !final_node) {
                diags.error(ErrorCode::E_PARSE,
                            "regular requires <start> and <final>", at(e));
                return false;
            }
            const std::vector<std::string> starts = words(start_node->text);
            finals = words(final_node->text);
            if (starts.size() != 1 || finals.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "regular requires one start state and at least one final state",
                            at(e));
                return false;
            }
            start = starts.front();
            if (state_set.find(start) == state_set.end()) {
                diags.error(ErrorCode::E_PARSE,
                            "regular start state '" + start + "' occurs in no transition",
                            at(e));
                return false;
            }
            std::set<std::string> unique_finals;
            for (const std::string& final : finals) {
                if (state_set.find(final) == state_set.end()) {
                    diags.error(ErrorCode::E_PARSE,
                                "regular final state '" + final
                                    + "' occurs in no transition", at(e));
                    return false;
                }
                unique_finals.insert(final);
            }
            finals.assign(unique_finals.begin(), unique_finals.end());
        } else {
            std::unordered_map<std::string, std::size_t> indegree;
            std::unordered_map<std::string, std::size_t> outdegree;
            std::unordered_map<std::string, std::vector<std::string>> adjacency;
            for (const std::string& state : state_set) {
                indegree[state] = 0;
                outdegree[state] = 0;
            }
            std::set<std::pair<std::string, std::string>> arcs;
            for (const Transition& edge : edges) {
                if (!arcs.emplace(edge.source, edge.target).second) { continue; }
                ++indegree[edge.target];
                ++outdegree[edge.source];
                adjacency[edge.source].push_back(edge.target);
            }
            std::vector<std::string> roots, terminals;
            for (const std::string& state : state_set) {
                if (indegree[state] == 0) { roots.push_back(state); }
                if (outdegree[state] == 0) { terminals.push_back(state); }
            }
            if (roots.size() != 1 || terminals.size() != 1) {
                diags.error(ErrorCode::E_PARSE,
                            "mdd must have exactly one root and one terminal node", at(e));
                return false;
            }
            std::unordered_map<std::string, int> colour;
            struct Frame { std::string state; std::size_t next = 0; };
            std::vector<Frame> pending;
            for (const std::string& state : state_set) {
                if (colour[state] != 0) { continue; }
                colour[state] = 1;
                pending.push_back({state});
                while (!pending.empty()) {
                    auto& frame = pending.back();
                    const auto adjacent = adjacency.find(frame.state);
                    if (adjacent == adjacency.end() || frame.next == adjacent->second.size()) {
                        colour[frame.state] = 2;
                        pending.pop_back();
                        continue;
                    }
                    const std::string next = adjacent->second[frame.next++];
                    if (colour[next] == 1) {
                        diags.error(ErrorCode::E_PARSE,
                                    "mdd transitions contain a directed cycle", at(e));
                        return false;
                    }
                    if (colour[next] == 0) {
                        colour[next] = 1;
                        pending.push_back({next});
                    }
                }
            }
            start = roots.front();
            finals = {terminals.front()};
        }

        if (state_set.size() > 250000 / scope.size()) {
            diags.error(ErrorCode::E_RESOURCE,
                        e.name + " unrolling would introduce more than 250000 reachability "
                            "variables", at(e));
            return false;
        }
        std::vector<std::string> states(state_set.begin(), state_set.end());
        std::vector<std::unordered_map<std::string, H::ExprPtr>> reach(scope.size() + 1);
        for (const std::string& state : states) {
            reach[0][state] = H::mkBool(state == start, at(e));
        }
        for (std::size_t position = 0; position < scope.size(); ++position) {
            for (const std::string& state : states) {
                reach[position + 1][state] = auxiliary(H::Sort::boolean(), e);
            }
            for (const std::string& state : states) {
                std::vector<H::ExprPtr> incoming;
                for (const Transition& edge : edges) {
                    if (edge.target != state) { continue; }
                    H::ExprPtr label = H::mkOp(
                        H::Op::EQ, {var(scope[position]), num(edge.value)}, at(e));
                    incoming.push_back(conjunction(
                        {reach[position].at(edge.source), std::move(label)}, e));
                }
                addFormula(H::mkOp(
                    H::Op::EQ,
                    {reach[position + 1].at(state),
                     disjunction(std::move(incoming), e)}, at(e)), e);
            }
        }
        std::vector<H::ExprPtr> accepting;
        for (const std::string& final : finals) {
            accepting.push_back(reach.back().at(final));
        }
        addFormula(disjunction(std::move(accepting), e), e);
        if (report_) {
            report_->addChoice(
                {file_ + ":" + std::to_string(e.line), e.name,
                 "layered-reachability-with-auxiliary-booleans", Uir::Fidelity::exact(),
                 "one reachability equivalence per position/state preserves exactly the "
                 "accepted finite words; beta omits the uniquely constrained witnesses"});
        }
        return true;
    }

    bool precedenceConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* values_node = e.child("values");
        if (!list && values_node) {
            diags.error(ErrorCode::E_PARSE,
                        "precedence with <values> also requires <list>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list ? list->text : e.text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "precedence requires at least two variables", at(e));
            return false;
        }

        std::vector<long long> values;
        bool covered = false;
        if (values_node) {
            const std::string covered_text = values_node->attr("covered", "false");
            if (covered_text != "true" && covered_text != "false") {
                diags.error(ErrorCode::E_PARSE,
                            "precedence covered must be true or false", at(e));
                return false;
            }
            covered = covered_text == "true";
            std::set<long long> unique;
            for (const std::string& token : words(values_node->text)) {
                long long value = 0;
                if (!toInt(token, value)) {
                    diags.error(ErrorCode::E_PARSE,
                                "precedence value '" + token + "' is not an integer", at(e));
                    return false;
                }
                if (!unique.insert(value).second) {
                    diags.error(ErrorCode::E_PARSE,
                                "precedence values must be distinct", at(e));
                    return false;
                }
                values.push_back(value);
            }
            if (values.size() < 2) {
                diags.error(ErrorCode::E_PARSE,
                            "precedence <values> requires at least two values", at(e));
                return false;
            }
        } else {
            std::set<long long> ordered_values;
            constexpr std::size_t limit = 100000;
            for (const std::string& variable : scope) {
                const Domain& domain = *sourceVariable(variable).domain;
                if (domain.product_bound) {
                    ordered_values.insert(0);
                    for (long long a = 1; a <= domain.product_bound; ++a) {
                        for (long long b = 1; b <= a; ++b) {
                            ordered_values.insert(a * b);
                            ordered_values.insert(-a * b);
                            if (ordered_values.size() > limit) {
                                diags.error(ErrorCode::E_RESOURCE,
                                            "precedence without <values> needs an ordered union "
                                            "of domains larger than 100000 values", at(e));
                                return false;
                            }
                        }
                    }
                } else if (domain.sparse()) {
                    ordered_values.insert(domain.values.begin(), domain.values.end());
                    if (ordered_values.size() > limit) {
                        diags.error(ErrorCode::E_RESOURCE,
                                    "precedence without <values> needs an ordered union of "
                                    "domains larger than 100000 values", at(e));
                        return false;
                    }
                } else {
                    const unsigned long long width =
                        static_cast<unsigned long long>(domain.hi)
                        - static_cast<unsigned long long>(domain.lo);
                    if (width >= limit) {
                        diags.error(ErrorCode::E_RESOURCE,
                                    "precedence without <values> needs an ordered union of "
                                    "domains larger than 100000 values", at(e));
                        return false;
                    }
                    for (long long value = domain.lo;; ++value) {
                        ordered_values.insert(value);
                        if (ordered_values.size() > limit) {
                            diags.error(ErrorCode::E_RESOURCE,
                                        "precedence without <values> needs an ordered union "
                                        "of domains larger than 100000 values", at(e));
                            return false;
                        }
                        if (value == domain.hi) { break; }
                    }
                }
            }
            values.assign(ordered_values.begin(), ordered_values.end());
        }
        const long double estimated = static_cast<long double>(values.size())
            * static_cast<long double>(scope.size())
            * static_cast<long double>(scope.size() + 1) / 2.0L;
        if (estimated > 2000000.0L) {
            diags.error(ErrorCode::E_RESOURCE,
                        "precedence expansion would exceed 2000000 relational atoms", at(e));
            return false;
        }

        std::vector<H::ExprPtr> formulas;
        for (std::size_t value_index = 0; value_index + 1 < values.size(); ++value_index) {
            std::vector<H::ExprPtr> earlier_previous;
            for (const std::string& variable : scope) {
                H::ExprPtr next_here = H::mkOp(
                    H::Op::EQ, {var(variable), num(values[value_index + 1])}, at(e));
                formulas.push_back(implication(
                    std::move(next_here), disjunction(earlier_previous, e), e));
                earlier_previous.push_back(H::mkOp(
                    H::Op::EQ, {var(variable), num(values[value_index])}, at(e)));
            }
        }
        if (covered && !values.empty()) {
            std::vector<H::ExprPtr> last_occurs;
            for (const std::string& variable : scope) {
                last_occurs.push_back(H::mkOp(
                    H::Op::EQ, {var(variable), num(values.back())}, at(e)));
            }
            // The precedence chain then forces every earlier listed value to
            // occur as well, exactly as Semantics 10 in XCSP3-core specifies.
            formulas.push_back(disjunction(std::move(last_occurs), e));
        }
        addFormula(conjunction(std::move(formulas), e), e);
        return true;
    }

    bool clauseConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const std::vector<std::string> literals = words(list ? list->text : e.text);
        if (literals.empty()) {
            diags.error(ErrorCode::E_PARSE, "clause has no literals", at(e));
            return false;
        }
        std::vector<H::ExprPtr> terms;
        for (const std::string& literal : literals) {
            bool negated = false;
            std::string name = literal;
            if (literal.size() > 5 && literal.compare(0, 4, "not(") == 0
                && literal.back() == ')') {
                negated = true;
                name = literal.substr(4, literal.size() - 5);
            }
            const auto domain = findSource(name);
            if (domain == nullptr) {
                diags.error(ErrorCode::E_PARSE,
                            "clause literal '" + literal
                                + "' does not name a declared 0/1 variable", at(e));
                return false;
            }
            if (domain->domain->sparse() || domain->domain->lo != 0
                || domain->domain->hi != 1) {
                diags.error(ErrorCode::E_TYPE,
                            "clause literal '" + name
                                + "' must have domain exactly 0..1", at(e));
                return false;
            }
            terms.push_back(H::mkOp(
                H::Op::EQ, {var(name), num(negated ? 0 : 1)}, at(e)));
        }
        addFormula(disjunction(std::move(terms), e), e);
        return true;
    }

    bool variableMatrix(const std::string& text,
                        std::vector<std::vector<std::string>>& rows,
                        const Elem& e, Uir::Diagnostics& diags) {
        const std::string body = trim(text);
        if (body.empty()) {
            diags.error(ErrorCode::E_PARSE, "a matrix is empty", at(e));
            return false;
        }
        if (body.find('(') == std::string::npos) {
            const std::size_t bracket = body.find('[');
            const std::string base = trim(body.substr(0, bracket));
            const auto array = arrays_.find(base);
            if (bracket == std::string::npos || array == arrays_.end()
                || array->second.dimensions.size() != 2) {
                diags.error(ErrorCode::E_PARSE,
                            "a compact matrix must select a declared two-dimensional array",
                            at(e));
                return false;
            }
            std::vector<std::string> cells;
            if (!varList(body, cells, e, diags)) { return false; }
            std::string previous_row;
            for (const std::string& cell : cells) {
                const std::size_t open = cell.find('[', base.size());
                const std::size_t close = open == std::string::npos
                    ? std::string::npos : cell.find(']', open + 1);
                if (close == std::string::npos) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "expanded matrix cell has no row index", at(e));
                    return false;
                }
                const std::string row = cell.substr(open + 1, close - open - 1);
                if (rows.empty() || row != previous_row) {
                    rows.emplace_back();
                    previous_row = row;
                }
                rows.back().push_back(cell);
            }
        } else {
            std::size_t i = 0;
            while (i < body.size()) {
                while (i < body.size()
                       && std::isspace(static_cast<unsigned char>(body[i]))) { ++i; }
                if (i == body.size()) { break; }
                if (body[i] != '(') {
                    diags.error(ErrorCode::E_PARSE,
                                "matrix rows must be parenthesized", at(e));
                    return false;
                }
                const std::size_t close = body.find(')', i + 1);
                if (close == std::string::npos) {
                    diags.error(ErrorCode::E_PARSE,
                                "a matrix row has no closing ')'", at(e));
                    return false;
                }
                std::string row_text = body.substr(i + 1, close - i - 1);
                std::replace(row_text.begin(), row_text.end(), ',', ' ');
                rows.emplace_back();
                if (!varList(row_text, rows.back(), e, diags)) { return false; }
                i = close + 1;
            }
        }
        if (rows.size() < 2 || rows.front().size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "a matrix requires at least two rows and two columns", at(e));
            return false;
        }
        const std::size_t columns = rows.front().size();
        for (const auto& row : rows) {
            if (row.size() != columns) {
                diags.error(ErrorCode::E_PARSE,
                            "all matrix rows must have the same length", at(e));
                return false;
            }
        }
        return true;
    }

    H::ExprPtr allDifferentFormula(const std::vector<H::ExprPtr>& scope,
                                   const std::vector<long long>& except,
                                   const Elem& e) {
        if (except.empty()) {
            return relational_.relation(H::mkGlobal("alldifferent", scope, at(e)), scope);
        }
        std::vector<H::ExprPtr> pairs;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            for (std::size_t j = i + 1; j < scope.size(); ++j) {
                std::vector<H::ExprPtr> allowed;
                allowed.push_back(H::mkOp(
                    H::Op::NOT,
                    {H::mkOp(H::Op::EQ, {scope[i], scope[j]}, at(e))}, at(e)));
                for (const long long value : except) {
                    allowed.push_back(H::mkOp(
                        H::Op::EQ, {scope[i], num(value)}, at(e)));
                }
                pairs.push_back(disjunction(std::move(allowed), e));
            }
        }
        return relational_.relation(conjunction(std::move(pairs), e), scope);
    }

    H::ExprPtr allDifferentFormula(const std::vector<std::string>& scope,
                                   const std::vector<long long>& except,
                                   const Elem& e) {
        std::vector<H::ExprPtr> terms;
        terms.reserve(scope.size());
        for (const std::string& variable : scope) { terms.push_back(var(variable)); }
        return allDifferentFormula(terms, except, e);
    }

    bool exceptValues(const Elem& e, std::vector<long long>& values,
                      Uir::Diagnostics& diags) const {
        const Elem* excluded = e.child("except");
        if (!excluded) { return true; }
        std::set<long long> unique;
        for (const std::string& token : words(excluded->text)) {
            long long value = 0;
            if (!toInt(token, value)) {
                diags.error(ErrorCode::E_PARSE,
                            e.name + " except entry '" + token
                                + "' is not an integer", at(e));
                return false;
            }
            if (unique.insert(value).second) { values.push_back(value); }
        }
        if (values.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        e.name + " <except> is empty", at(e));
            return false;
        }
        return true;
    }

    bool allDifferentConstraint(const Elem& e, Uir::Diagnostics& diags) {
        std::vector<const Elem*> list_nodes;
        for (const Elem& child : e.children) {
            if (child.name == "list") { list_nodes.push_back(&child); }
        }
        const Elem* matrix = e.child("matrix");
        if (matrix && !list_nodes.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "allDifferent cannot combine <matrix> and <list> forms", at(e));
            return false;
        }
        if (list_nodes.size() >= 2) {
            std::vector<std::vector<std::string>> tuples(list_nodes.size());
            for (std::size_t i = 0; i < list_nodes.size(); ++i) {
                if (!varList(list_nodes[i]->text, tuples[i], *list_nodes[i], diags)) {
                    return false;
                }
                if (tuples[i].size() < 2
                    || (i != 0 && tuples[i].size() != tuples.front().size())) {
                    diags.error(ErrorCode::E_PARSE,
                                "allDifferent tuple lists must have one common size >= 2",
                                at(*list_nodes[i]));
                    return false;
                }
            }

            std::vector<std::vector<long long>> exceptions;
            if (const Elem* except_node = e.child("except")) {
                const std::string body = trim(except_node->text);
                std::size_t position = 0;
                while (position < body.size()) {
                    while (position < body.size()
                           && std::isspace(
                               static_cast<unsigned char>(body[position]))) {
                        ++position;
                    }
                    if (position == body.size()) { break; }
                    if (body[position] != '(') {
                        diags.error(ErrorCode::E_PARSE,
                                    "allDifferent tuple exceptions must be parenthesized",
                                    at(*except_node));
                        return false;
                    }
                    const std::size_t close = body.find(')', position + 1);
                    if (close == std::string::npos) {
                        diags.error(ErrorCode::E_PARSE,
                                    "allDifferent tuple exception has no closing ')'",
                                    at(*except_node));
                        return false;
                    }
                    std::string tuple_text =
                        body.substr(position + 1, close - position - 1);
                    std::replace(tuple_text.begin(), tuple_text.end(), ',', ' ');
                    const std::vector<std::string> tokens = words(tuple_text);
                    if (tokens.size() != tuples.front().size()) {
                        diags.error(ErrorCode::E_PARSE,
                                    "allDifferent tuple exception has the wrong arity",
                                    at(*except_node));
                        return false;
                    }
                    exceptions.emplace_back();
                    for (const std::string& token : tokens) {
                        long long value = 0;
                        if (!toInt(token, value)) {
                            diags.error(ErrorCode::E_PARSE,
                                        "allDifferent tuple exception entry '" + token
                                            + "' is not an integer", at(*except_node));
                            return false;
                        }
                        exceptions.back().push_back(value);
                    }
                    position = close + 1;
                }
                if (exceptions.empty()) {
                    diags.error(ErrorCode::E_PARSE,
                                "allDifferent tuple <except> is empty", at(*except_node));
                    return false;
                }
            }

            // A finite integer tuple has an injective mixed-radix encoding.
            // Common column bounds are essential: per-row radices would make
            // equal tuples encode differently. SMT integers do not overflow,
            // including a column spanning the entire signed 64-bit range.
            // This replaces O(rows^2 * width) component disequalities by one
            // native DISTINCT over O(rows * width) arithmetic expressions.
            if (exceptions.empty()) {
                const std::size_t width = tuples.front().size();
                std::vector<long long> lows(width, std::numeric_limits<long long>::max());
                std::vector<long long> highs(width, std::numeric_limits<long long>::min());
                for (const auto& tuple : tuples) {
                    for (std::size_t column = 0; column < width; ++column) {
                        const Domain& d = *sourceVariable(tuple[column]).domain;
                        lows[column] = std::min(lows[column], d.lo);
                        highs[column] = std::max(highs[column], d.hi);
                    }
                }
                std::vector<H::ExprPtr> radices(width);
                for (std::size_t column = 1; column < width; ++column) {
                    const auto distance = static_cast<unsigned long long>(highs[column])
                                        - static_cast<unsigned long long>(lows[column]);
                    radices[column] = H::mkInt(
                        distance == std::numeric_limits<unsigned long long>::max()
                            ? "18446744073709551616" : std::to_string(distance + 1), at(e));
                }
                std::vector<H::ExprPtr> encoded;
                encoded.reserve(tuples.size());
                for (const auto& tuple : tuples) {
                    H::ExprPtr value;
                    for (std::size_t column = 0; column < width; ++column) {
                        H::ExprPtr digit = var(tuple[column]);
                        if (lows[column] != 0) {
                            digit = H::mkOp(H::Op::SUB, {digit, num(lows[column])}, at(e));
                        }
                        value = value ? H::mkOp(H::Op::ADD,
                            {H::mkOp(H::Op::MUL, {value, radices[column]}, at(e)), digit},
                            at(e)) : digit;
                    }
                    encoded.push_back(std::move(value));
                }
                addFormula(H::mkOp(H::Op::DISTINCT, std::move(encoded), at(e)), e);
                return true;
            }

            const auto tupleInExceptions = [&](const std::vector<std::string>& tuple) {
                std::vector<H::ExprPtr> alternatives;
                for (const auto& exception : exceptions) {
                    std::vector<H::ExprPtr> equalities;
                    for (std::size_t i = 0; i < tuple.size(); ++i) {
                        equalities.push_back(H::mkOp(
                            H::Op::EQ, {var(tuple[i]), num(exception[i])}, at(e)));
                    }
                    alternatives.push_back(conjunction(std::move(equalities), e));
                }
                return disjunction(std::move(alternatives), e);
            };
            std::vector<H::ExprPtr> formulas;
            for (std::size_t left = 0; left < tuples.size(); ++left) {
                for (std::size_t right = left + 1; right < tuples.size(); ++right) {
                    std::vector<H::ExprPtr> allowed;
                    for (std::size_t component = 0;
                         component < tuples[left].size(); ++component) {
                        allowed.push_back(H::mkOp(
                            H::Op::NOT,
                            {H::mkOp(H::Op::EQ,
                                     {var(tuples[left][component]),
                                      var(tuples[right][component])}, at(e))}, at(e)));
                    }
                    if (!exceptions.empty()) {
                        allowed.push_back(tupleInExceptions(tuples[left]));
                        allowed.push_back(tupleInExceptions(tuples[right]));
                    }
                    formulas.push_back(disjunction(std::move(allowed), e));
                }
            }
            addFormula(conjunction(std::move(formulas), e), e);
            return true;
        }

        std::vector<long long> except;
        if (!exceptValues(e, except, diags)) { return false; }
        if (matrix) {
            std::vector<std::vector<std::string>> rows;
            if (!variableMatrix(matrix->text, rows, *matrix, diags)) { return false; }
            std::vector<H::ExprPtr> formulas;
            for (const auto& row : rows) {
                formulas.push_back(allDifferentFormula(row, except, e));
            }
            for (std::size_t column = 0; column < rows.front().size(); ++column) {
                std::vector<std::string> variables;
                for (const auto& row : rows) { variables.push_back(row[column]); }
                formulas.push_back(allDifferentFormula(variables, except, e));
            }
            addFormula(conjunction(std::move(formulas), e), e);
            return true;
        }
        std::vector<H::ExprPtr> scope;
        const std::string text = list_nodes.empty() ? e.text : list_nodes.front()->text;
        if (!expressionList(text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "allDifferent requires at least two expressions", at(e));
            return false;
        }
        addFormula(allDifferentFormula(scope, except, e), e);
        return true;
    }

    bool circuitConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* size_node = e.child("size");
        if (!list && size_node) {
            diags.error(ErrorCode::E_PARSE,
                        "circuit with <size> also requires <list>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list ? list->text : e.text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "circuit requires at least two successor variables", at(e));
            return false;
        }
        long long start = 0;
        if (list && !list->attr("startIndex").empty()
            && !toInt(list->attr("startIndex"), start)) {
            diags.error(ErrorCode::E_PARSE,
                        "circuit startIndex is not an integer", at(e));
            return false;
        }
        const unsigned long long index_headroom =
            static_cast<unsigned long long>(std::numeric_limits<long long>::max())
            - static_cast<unsigned long long>(start);
        if (scope.size() - 1 > index_headroom) {
            diags.error(ErrorCode::E_RESOURCE,
                        "circuit node indices exceed int64", at(e));
            return false;
        }
        const long long last = start + static_cast<long long>(scope.size() - 1);

        std::vector<H::ExprPtr> successors, active, positions;
        successors.reserve(scope.size());
        active.reserve(scope.size());
        positions.reserve(scope.size());
        std::vector<H::ExprPtr> formulas;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            H::ExprPtr successor = var(scope[i]);
            successors.push_back(successor);
            formulas.push_back(conjunction(
                {H::mkOp(H::Op::GE, {successor, num(start)}, at(e)),
                 H::mkOp(H::Op::LE, {successor, num(last)}, at(e))}, e));
            H::ExprPtr self = H::mkOp(
                H::Op::EQ,
                {successor, num(start + static_cast<long long>(i))}, at(e));
            active.push_back(H::mkOp(H::Op::NOT, {std::move(self)}, at(e)));
            positions.push_back(auxiliary(
                H::Sort::integer(), e, num(-1),
                num(static_cast<long long>(scope.size() - 1))));
        }
        formulas.push_back(H::mkGlobal("alldifferent", successors, at(e)));

        std::vector<H::ExprPtr> indicators;
        for (const H::ExprPtr& enabled : active) {
            indicators.push_back(H::mkOp(
                H::Op::ITE, {enabled, num(1), num(0)}, at(e)));
        }
        H::ExprPtr actual_size = H::mkOp(H::Op::ADD, std::move(indicators), at(e));
        formulas.push_back(H::mkOp(H::Op::GT, {actual_size, num(1)}, at(e)));
        if (size_node) {
            H::ExprPtr required_size = scalar(size_node->text, e, diags);
            if (!required_size) { return false; }
            long long literal_size = 0;
            if (toInt(trim(size_node->text), literal_size) && literal_size <= 1) {
                diags.error(ErrorCode::E_PARSE,
                            "circuit size must be strictly greater than 1", at(e));
                return false;
            }
            formulas.push_back(H::mkOp(
                H::Op::EQ, {actual_size, std::move(required_size)}, at(e)));
        }

        std::vector<H::ExprPtr> tagged_positions;
        tagged_positions.reserve(scope.size());
        H::ExprPtr position_array = H::mkConstArray(
            H::Sort::array(H::Sort::integer(), H::Sort::integer()), num(0), at(e));
        for (std::size_t i = 0; i < scope.size(); ++i) {
            // Inactive positions use distinct negative tags only for this
            // allDifferent observation; their actual witness remains -1.
            tagged_positions.push_back(H::mkOp(H::Op::ITE,
                {active[i], positions[i], num(-1 - static_cast<long long>(i))}, at(e)));
            position_array = H::mkOp(H::Op::STORE,
                {position_array, num(start + static_cast<long long>(i)), positions[i]}, at(e));
            H::ExprPtr in_position_range = conjunction(
                {H::mkOp(H::Op::GE, {positions[i], num(0)}, at(e)),
                 H::mkOp(H::Op::LT, {positions[i], actual_size}, at(e))}, e);
            formulas.push_back(implication(active[i], std::move(in_position_range), e));
            formulas.push_back(implication(
                H::mkOp(H::Op::NOT, {active[i]}, at(e)),
                H::mkOp(H::Op::EQ, {positions[i], num(-1)}, at(e)), e));
        }
        formulas.push_back(H::mkOp(H::Op::DISTINCT, std::move(tagged_positions), at(e)));
        // Define the finite position lookup once, including its outside-domain
        // default. A fresh unconstrained array would add infinitely many target
        // models; a total definition preserves the original scalar witnesses.
        H::FunDecl position_definition;
        position_definition.name = freshGroupFunctionName();
        position_definition.result = position_array->sort;
        position_definition.loc = at(e);
        position_definition.body = position_array;
        position_definition.auxiliary = true;
        position_array = H::mkApply(position_definition.name, position_definition.result, {}, at(e));
        model_->funs.push_back(std::move(position_definition));

        // Every non-self successor advances one step in a cyclic ordering of
        // all active nodes. Since active positions are a permutation of
        // 0..actual_size-1, two disjoint non-trivial cycles cannot satisfy
        // these equations; self loops remain exactly the ignored nodes allowed
        // by XCSP3-core Semantics 30.
        for (std::size_t i = 0; i < scope.size(); ++i) {
            H::ExprPtr incremented = H::mkOp(
                H::Op::ADD, {positions[i], num(1)}, at(e));
            H::ExprPtr wrapped = H::mkOp(
                H::Op::ITE,
                {H::mkOp(H::Op::EQ, {incremented, actual_size}, at(e)),
                 num(0), incremented}, at(e));
            // A shared total array replaces the quadratic target enumeration.
            // The successor range constraints ensure that only stored source
            // indices can be selected; the default is therefore unobservable.
            const auto next_position = H::mkOp(H::Op::SELECT,
                {position_array, successors[i]}, at(e));
            formulas.push_back(implication(active[i],
                H::mkOp(H::Op::EQ, {next_position, wrapped}, at(e)), e));
        }
        addFormula(conjunction(std::move(formulas), e), e);
        if (report_) {
            report_->addChoice(
                {file_ + ":" + std::to_string(e.line), "circuit",
                 "successor-permutation-with-cyclic-position-witnesses",
                 Uir::Fidelity::equisat(),
                 "range and allDifferent form a successor permutation; guarded cyclic "
                 "positions permit self loops but exclude multiple non-trivial subcycles; "
                 "beta omits position witnesses. NOT count-preserving: the position "
                 "constraints are implications, and every one of them is invariant "
                 "under rotating the positions along the cycle, so nothing pins a "
                 "particular node to position 0. One source model therefore extends to "
                 "actual_size target models. Measured on a three-node instance: 5 "
                 "assignments to the successors, 12 models over the target, which is "
                 "3 two-cycles x 2 rotations + 2 three-cycles x 3 rotations. Contrast "
                 "the automaton encoding above, whose auxiliaries are defined by an "
                 "equivalence and so are functionally determined"});
        }
        return true;
    }

    bool noOverlapConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* origins_node = e.child("origins");
        const Elem* lengths_node = e.child("lengths");
        if (!origins_node || !lengths_node) {
            diags.error(ErrorCode::E_PARSE,
                        "noOverlap requires <origins> and <lengths>", at(e));
            return false;
        }
        const std::string ignored_text = e.attr("zeroIgnored", "true");
        if (ignored_text != "true" && ignored_text != "false") {
            diags.error(ErrorCode::E_PARSE,
                        "noOverlap zeroIgnored must be true or false", at(e));
            return false;
        }
        const bool zero_ignored = ignored_text == "true";
        std::vector<std::vector<H::ExprPtr>> origins, lengths;
        if (origins_node->text.find('(') == std::string::npos) {
            std::vector<std::string> variables;
            if (!varList(origins_node->text, variables, *origins_node, diags)) {
                return false;
            }
            origins.resize(variables.size());
            for (std::size_t i = 0; i < variables.size(); ++i) {
                origins[i].push_back(var(variables[i]));
            }
            std::vector<H::ExprPtr> flat_lengths;
            if (!mixedTermList(lengths_node->text, flat_lengths, *lengths_node, diags)) {
                return false;
            }
            lengths.resize(flat_lengths.size());
            for (std::size_t i = 0; i < flat_lengths.size(); ++i) {
                lengths[i].push_back(flat_lengths[i]);
            }
        } else {
            std::vector<std::vector<std::string>> origin_names;
            if (!variableMatrix(origins_node->text, origin_names, *origins_node, diags)) {
                return false;
            }
            for (const auto& row : origin_names) {
                origins.emplace_back();
                for (const std::string& variable : row) {
                    origins.back().push_back(var(variable));
                }
            }
            if (!termMatrix(lengths_node->text, lengths, *lengths_node, diags)) {
                return false;
            }
        }
        if (origins.size() < 2 || origins.size() != lengths.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "noOverlap needs equally many origins and lengths (at least two)",
                        at(e));
            return false;
        }
        for (std::size_t i = 0; i < origins.size(); ++i) {
            if (origins[i].empty() || origins[i].size() != lengths[i].size()) {
                diags.error(ErrorCode::E_PARSE,
                            "each noOverlap origin and length tuple must have the same "
                            "positive dimension", at(e));
                return false;
            }
        }

        std::vector<H::ExprPtr> pairwise;
        for (std::size_t i = 0; i < origins.size(); ++i) {
            for (std::size_t j = i + 1; j < origins.size(); ++j) {
                std::vector<H::ExprPtr> alternatives;
                if (zero_ignored) {
                    for (const H::ExprPtr& length : lengths[i]) {
                        alternatives.push_back(H::mkOp(
                            H::Op::EQ, {length, num(0)}, at(e)));
                    }
                    for (const H::ExprPtr& length : lengths[j]) {
                        alternatives.push_back(H::mkOp(
                            H::Op::EQ, {length, num(0)}, at(e)));
                    }
                }
                for (std::size_t dimension = 0;
                     dimension < origins[i].size(); ++dimension) {
                    alternatives.push_back(H::mkOp(
                        H::Op::LE,
                        {H::mkOp(H::Op::ADD,
                                 {origins[i][dimension], lengths[i][dimension]}, at(e)),
                         origins[j][dimension]}, at(e)));
                    alternatives.push_back(H::mkOp(
                        H::Op::LE,
                        {H::mkOp(H::Op::ADD,
                                 {origins[j][dimension], lengths[j][dimension]}, at(e)),
                         origins[i][dimension]}, at(e)));
                }
                pairwise.push_back(disjunction(std::move(alternatives), e));
            }
        }
        addFormula(conjunction(std::move(pairwise), e), e);
        return true;
    }

    bool cumulativeConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* origins_node = e.child("origins");
        const Elem* lengths_node = e.child("lengths");
        const Elem* heights_node = e.child("heights");
        const Elem* condition_node = e.child("condition");
        if (!origins_node || !lengths_node || !heights_node || !condition_node) {
            diags.error(ErrorCode::E_PARSE,
                        "cumulative requires origins, lengths, heights and condition",
                        at(e));
            return false;
        }
        std::vector<std::string> origins;
        if (!varList(origins_node->text, origins, *origins_node, diags)) { return false; }
        std::vector<H::ExprPtr> lengths, heights;
        if (!mixedTermList(lengths_node->text, lengths, *lengths_node, diags)
            || !mixedTermList(heights_node->text, heights, *heights_node, diags)) {
            return false;
        }
        if (origins.size() < 2 || origins.size() != lengths.size()
            || origins.size() != heights.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "cumulative origins, lengths and heights must have equal size >= 2",
                        at(e));
            return false;
        }
        std::vector<H::ExprPtr> formulas;
        if (const Elem* ends_node = e.child("ends")) {
            std::vector<std::string> ends;
            if (!varList(ends_node->text, ends, *ends_node, diags)) { return false; }
            if (ends.size() != origins.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "cumulative ends must match the number of tasks", at(e));
                return false;
            }
            for (std::size_t i = 0; i < origins.size(); ++i) {
                formulas.push_back(H::mkOp(
                    H::Op::EQ,
                    {H::mkOp(H::Op::ADD, {var(origins[i]), lengths[i]}, at(e)),
                     var(ends[i])}, at(e)));
            }
        }
        std::vector<H::ExprPtr> starts, ends;
        starts.reserve(origins.size());
        ends.reserve(origins.size());
        for (std::size_t i = 0; i < origins.size(); ++i) {
            starts.push_back(var(origins[i]));
            ends.push_back(H::mkOp(H::Op::ADD, {starts.back(), lengths[i]}, at(e)));
        }
        const auto loadAt = [&](const H::ExprPtr& time) {
            std::vector<H::ExprPtr> usage;
            usage.reserve(origins.size());
            for (std::size_t i = 0; i < origins.size(); ++i) {
                H::ExprPtr active = conjunction(
                    {H::mkOp(H::Op::LE, {starts[i], time}, at(e)),
                     H::mkOp(H::Op::LT, {time, ends[i]}, at(e))}, e);
                usage.push_back(H::mkOp(
                    H::Op::ITE, {std::move(active), heights[i], num(0)}, at(e)));
            }
            return H::mkOp(H::Op::ADD, std::move(usage), at(e));
        };
        // A finite collection of half-open integer intervals changes its load
        // only at a start or end. Check all events and the zero-load baseline
        // outside every interval. This preserves arbitrary load conditions and
        // signed heights: unlike a start-only maximum check, an end can
        // increase load when a departing task has negative height.
        // Nonpositive lengths are empty intervals, just as in the original
        // s <= t && t < s + length relation. No horizon or extra domain
        // restrictions are introduced, including under Boolean reification.
        bool shared_load = origins.size() >= 64;
        if (shared_load) {
            std::unordered_set<const H::Expr*> visited;
            std::vector<H::ExprPtr> pending(starts);
            pending.insert(pending.end(), lengths.begin(), lengths.end());
            pending.insert(pending.end(), heights.begin(), heights.end());
            while (!pending.empty()) {
                const auto term = std::move(pending.back());
                pending.pop_back();
                if (!term || !visited.insert(term.get()).second) { continue; }
                // Group/function parameters are lexical. Do not move their
                // load definition into the surrounding model scope.
                if (term->kind == H::ExprKind::BOUND_VAR || !term->binders.empty()) {
                    shared_load = false;
                    break;
                }
                pending.insert(pending.end(), term->args.begin(), term->args.end());
            }
        }
        std::string load_name;
        if (shared_load) {
            H::FunDecl definition;
            definition.name = freshGroupFunctionName();
            const std::string time_name = freshGroupBinderName(definition.name, 0, {});
            definition.params = {H::Sort::integer()};
            definition.result = H::Sort::integer();
            definition.binders = {{time_name, H::Sort::integer()}};
            definition.body = loadAt(H::mkBoundVar(time_name, H::Sort::integer(), at(e)));
            definition.loc = at(e);
            definition.auxiliary = true;
            load_name = definition.name;
            model_->funs.push_back(std::move(definition));
        }
        const auto checkAt = [&](const H::ExprPtr& time) {
            H::ExprPtr total = shared_load
                ? H::mkApply(load_name, H::Sort::integer(), {time}, at(e))
                : loadAt(time);
            return condition(total, condition_node->text, e, diags);
        };
        // Baseline means load zero, not load at time zero. The original
        // all-Int universal also checks times outside every finite interval.
        H::ExprPtr baseline = condition(num(0), condition_node->text, e, diags);
        if (!baseline) { return false; }
        formulas.push_back(std::move(baseline));
        for (std::size_t i = 0; i < origins.size(); ++i) {
            for (const H::ExprPtr& event : {starts[i], ends[i]}) {
                H::ExprPtr at_event = checkAt(event);
                if (!at_event) { return false; }
                formulas.push_back(std::move(at_event));
            }
        }
        addFormula(conjunction(std::move(formulas), e), e);
        if (report_) {
            report_->addChoice(
                {file_ + ":" + std::to_string(e.line), "cumulative",
                 shared_load ? "integer-time-events-shared-load" : "integer-time-events",
                 Uir::Fidelity::exact(),
                 "the exact half-open load condition is checked at every start/end "
                 "event and at zero load; negative times are retained and no horizon is assumed"});
        }
        return true;
    }

    bool flowConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const auto metadataOnly = [&](const Elem& node) {
            for (const auto& attribute : node.attrs) {
                if (attribute.first != "id" && attribute.first != "note"
                    && attribute.first != "class") {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "unsupported flow attribute '" + attribute.first + "'",
                                at(node));
                    return false;
                }
            }
            return true;
        };
        if (!metadataOnly(e)) { return false; }
        std::set<std::string> seen;
        for (const Elem& child : e.children) {
            if ((child.name != "list" && child.name != "balance" && child.name != "arcs"
                 && child.name != "capacities" && child.name != "weights"
                 && child.name != "condition")
                || !seen.insert(child.name).second || !child.children.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "flow has an unknown, repeated or nested field", at(child));
                return false;
            }
            if (!metadataOnly(child)) { return false; }
        }
        const Elem* list = e.child("list");
        const Elem* balance_node = e.child("balance");
        const Elem* arcs_node = e.child("arcs");
        const Elem* weights_node = e.child("weights");
        const Elem* condition_node = e.child("condition");
        if (!list || !balance_node || !arcs_node
            || (weights_node != nullptr) != (condition_node != nullptr)
            || !trim(e.text).empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "flow requires list, balance and arcs; weights and condition "
                        "must occur together", at(e));
            return false;
        }
        std::vector<std::string> scope;
        std::vector<H::ExprPtr> balances;
        std::vector<std::vector<H::ExprPtr>> arcs;
        if (!varList(list->text, scope, *list, diags)
            || !mixedTermList(balance_node->text, balances, *balance_node, diags)
            || !termMatrix(arcs_node->text, arcs, *arcs_node, diags)) {
            return false;
        }
        if (scope.size() < 2 || arcs.size() != scope.size() || arcs.front().size() != 2) {
            diags.error(ErrorCode::E_PARSE,
                        "flow requires one pair of node identifiers per arc variable",
                        at(e));
            return false;
        }
        std::map<long long, std::vector<H::ExprPtr>> incoming, outgoing;
        for (std::size_t i = 0; i < arcs.size(); ++i) {
            for (const H::ExprPtr& endpoint : arcs[i]) {
                if (endpoint->kind != H::ExprKind::LIT_INT) {
                    diags.error(ErrorCode::E_PARSE,
                                "flow node identifiers must be integer literals", at(*arcs_node));
                    return false;
                }
                incoming.try_emplace(endpoint->int_value);
                outgoing.try_emplace(endpoint->int_value);
            }
            outgoing[arcs[i][0]->int_value].push_back(var(scope[i]));
            incoming[arcs[i][1]->int_value].push_back(var(scope[i]));
        }
        if (balances.size() < 2 || balances.size() != incoming.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "flow balance must contain one entry per graph node", at(*balance_node));
            return false;
        }
        // The official XCSP3 checker indexes balances by node - minimum_node.
        // Check that convention explicitly rather than inventing a sparse map.
        auto previous = incoming.begin();
        for (auto next = std::next(previous); next != incoming.end(); ++next, ++previous) {
            if (previous->first == std::numeric_limits<long long>::max()
                || next->first != previous->first + 1) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "flow node identifiers must form a consecutive integer range",
                            at(*arcs_node));
                return false;
            }
        }
        const auto sum = [&](const std::vector<H::ExprPtr>& terms) {
            if (terms.empty()) { return num(0); }
            if (terms.size() == 1) { return terms.front(); }
            return H::mkOp(H::Op::ADD, terms, at(e));
        };
        std::vector<H::ExprPtr> formulas;
        std::size_t node_index = 0;
        for (const auto& node : incoming) {
            // Semantics 45: outgoing minus incoming equals this node's balance.
            // Parallel arcs, repeated variables and self loops retain multiplicity.
            formulas.push_back(H::mkOp(H::Op::EQ,
                {H::mkOp(H::Op::SUB, {sum(outgoing.at(node.first)), sum(node.second)}, at(e)),
                 balances[node_index++]}, at(e)));
        }
        if (const Elem* capacities = e.child("capacities")) {
            std::size_t arc_index = 0;
            for (const std::string& token : words(capacities->text)) {
                const auto repetition = token.find('x');
                const std::string interval = token.substr(0, repetition);
                const auto dots = interval.find("..");
                long long lower = 0, upper = 0, count = 1;
                if (dots == std::string::npos || !toInt(interval.substr(0, dots), lower)
                    || !toInt(interval.substr(dots + 2), upper) || lower > upper
                    || (repetition != std::string::npos
                        && (!toInt(token.substr(repetition + 1), count) || count <= 0))
                    || static_cast<unsigned long long>(count) > scope.size() - arc_index) {
                    diags.error(ErrorCode::E_PARSE,
                                "flow capacities must be ordered integer intervals, one per arc",
                                at(*capacities));
                    return false;
                }
                for (long long repeat = 0; repeat < count; ++repeat, ++arc_index) {
                    formulas.push_back(H::mkOp(H::Op::GE, {var(scope[arc_index]), num(lower)}, at(e)));
                    formulas.push_back(H::mkOp(H::Op::LE, {var(scope[arc_index]), num(upper)}, at(e)));
                }
            }
            if (arc_index != scope.size()) {
                diags.error(ErrorCode::E_PARSE, "flow capacities count differs from arcs", at(*capacities));
                return false;
            }
        }
        if (weights_node) {
            std::vector<H::ExprPtr> weights, products;
            if (!mixedTermList(weights_node->text, weights, *weights_node, diags)) { return false; }
            if (weights.size() != scope.size()) {
                diags.error(ErrorCode::E_PARSE, "flow weights count differs from arcs", at(*weights_node));
                return false;
            }
            for (std::size_t i = 0; i < scope.size(); ++i) {
                products.push_back(H::mkOp(H::Op::MUL, {var(scope[i]), weights[i]}, at(e)));
            }
            H::ExprPtr cost = condition(sum(products), condition_node->text, e, diags);
            if (!cost) { return false; }
            formulas.push_back(std::move(cost));
        }
        addFormula(conjunction(std::move(formulas), e), e);
        if (report_) {
            report_->addChoice({file_ + ":" + std::to_string(e.line), "flow",
                "integer-node-conservation-capacities-and-cost", Uir::Fidelity::exact(),
                "every arc contributes once at each endpoint; optional capacities and "
                "weighted cost use the shared integer HIR without auxiliary variables"});
        }
        return true;
    }

    bool knapsackConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* weights_node = e.child("weights");
        const Elem* profits_node = e.child("profits");
        std::vector<const Elem*> conditions;
        for (const Elem& child : e.children) {
            if (child.name == "condition") { conditions.push_back(&child); }
        }
        if (!list || !weights_node || !profits_node || conditions.size() != 2) {
            diags.error(ErrorCode::E_PARSE,
                        "knapsack requires list, weights, two conditions and profits",
                        at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, *list, diags)) { return false; }
        std::vector<H::ExprPtr> weights, profits;
        if (!mixedTermList(weights_node->text, weights, *weights_node, diags)
            || !mixedTermList(profits_node->text, profits, *profits_node, diags)) {
            return false;
        }
        if (scope.size() < 2 || weights.size() != scope.size()
            || profits.size() != scope.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "knapsack list, weights and profits must have equal size >= 2",
                        at(e));
            return false;
        }
        std::vector<H::ExprPtr> weighted, profitable;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            weighted.push_back(H::mkOp(
                H::Op::MUL, {weights[i], var(scope[i])}, at(e)));
            profitable.push_back(H::mkOp(
                H::Op::MUL, {profits[i], var(scope[i])}, at(e)));
        }
        H::ExprPtr weight_condition = condition(
            H::mkOp(H::Op::ADD, std::move(weighted), at(e)),
            conditions[0]->text, e, diags);
        H::ExprPtr profit_condition = condition(
            H::mkOp(H::Op::ADD, std::move(profitable), at(e)),
            conditions[1]->text, e, diags);
        if (!weight_condition || !profit_condition) { return false; }
        addFormula(conjunction(
            {std::move(weight_condition), std::move(profit_condition)}, e), e);
        return true;
    }

    bool binPackingConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* sizes_node = e.child("sizes");
        const Elem* condition_node = e.child("condition");
        const Elem* limits_node = e.child("limits");
        const Elem* loads_node = e.child("loads");
        if (!list || !sizes_node
            || static_cast<int>(condition_node != nullptr)
                 + static_cast<int>(limits_node != nullptr)
                 + static_cast<int>(loads_node != nullptr) != 1) {
            diags.error(ErrorCode::E_PARSE,
                        "binPacking requires list, sizes, and exactly one of condition, "
                        "limits or loads", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, *list, diags)) { return false; }
        std::vector<H::ExprPtr> sizes;
        if (!mixedTermList(sizes_node->text, sizes, *sizes_node, diags)) { return false; }
        if (scope.size() < 2 || sizes.size() != scope.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "binPacking needs equally many items and sizes (at least two)", at(e));
            return false;
        }
        auto loadFor = [&](const H::ExprPtr& bin) {
            std::vector<H::ExprPtr> contributions;
            for (std::size_t i = 0; i < scope.size(); ++i) {
                H::ExprPtr selected = H::mkOp(
                    H::Op::EQ, {var(scope[i]), bin}, at(e));
                contributions.push_back(H::mkOp(
                    H::Op::ITE, {std::move(selected), sizes[i], num(0)}, at(e)));
            }
            return H::mkOp(H::Op::ADD, std::move(contributions), at(e));
        };
        auto someItemIn = [&](const H::ExprPtr& bin) {
            std::vector<H::ExprPtr> occurrences;
            for (const std::string& item : scope) {
                occurrences.push_back(H::mkOp(
                    H::Op::EQ, {var(item), bin}, at(e)));
            }
            return disjunction(std::move(occurrences), e);
        };

        if (condition_node) {
            const std::string bin_name =
                "__somt_xcsp3_bin_" + std::to_string(auxiliary_counter_++);
            H::ExprPtr bin = H::mkBoundVar(bin_name, H::Sort::integer(), at(e));
            H::ExprPtr restricted = condition(loadFor(bin), condition_node->text, e, diags);
            if (!restricted) { return false; }
            addFormula(H::mkForall(
                {H::Binder{bin_name, H::Sort::integer()}},
                implication(someItemIn(bin), std::move(restricted), e), at(e)), e);
            return true;
        }

        const Elem& bin_values_node = limits_node ? *limits_node : *loads_node;
        std::vector<H::ExprPtr> bin_values;
        if (!mixedTermList(bin_values_node.text, bin_values, bin_values_node, diags)) {
            return false;
        }
        if (bin_values.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "binPacking limits/loads list is empty", at(e));
            return false;
        }
        std::vector<H::ExprPtr> formulas;
        for (const std::string& item : scope) {
            formulas.push_back(conjunction(
                {H::mkOp(H::Op::GE, {var(item), num(0)}, at(e)),
                 H::mkOp(H::Op::LT,
                         {var(item), num(static_cast<long long>(bin_values.size()))}, at(e))}, e));
        }
        for (std::size_t bin_index = 0; bin_index < bin_values.size(); ++bin_index) {
            H::ExprPtr bin = num(static_cast<long long>(bin_index));
            H::ExprPtr relation = H::mkOp(
                limits_node ? H::Op::LE : H::Op::EQ,
                {loadFor(bin), bin_values[bin_index]}, at(e));
            // Array forms specify a condition for every listed bin, including
            // empty bins with load zero. Only the single-condition form above
            // restricts its condition to bins occupied by an item.
            formulas.push_back(std::move(relation));
        }
        addFormula(conjunction(std::move(formulas), e), e);
        return true;
    }

    bool allEqual(const Elem& e, Uir::Diagnostics& diags) {
        std::vector<std::string> scope;
        const std::string text = e.child("list") ? e.child("list")->text : e.text;
        if (!varList(text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE, "allEqual requires at least two variables", at(e));
            return false;
        }
        std::vector<H::ExprPtr> terms;
        terms.reserve(scope.size());
        for (const auto& name : scope) { terms.push_back(var(name)); }
        addFormula(H::mkOp(H::Op::EQ, std::move(terms), at(e)), e);
        return true;
    }

    bool sumConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* result = e.child("condition");
        if (!list || !result) {
            diags.error(ErrorCode::E_PARSE, "sum requires <list> and <condition>", at(e));
            return false;
        }
        std::vector<H::ExprPtr> scope;
        if (!expressionList(list->text, scope, e, diags)) { return false; }
        if (scope.empty()) {
            diags.error(ErrorCode::E_PARSE, "sum requires a nonempty list", at(e));
            return false;
        }
        std::vector<H::ExprPtr> coefficients(scope.size(), num(1));
        if (const Elem* coeffs = e.child("coeffs")) {
            coefficients.clear();
            if (!termList(coeffs->text, coefficients, e, diags, scope.size())) { return false; }
            if (coefficients.size() != scope.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "sum has " + std::to_string(coefficients.size())
                                + " coefficients for " + std::to_string(scope.size())
                                + " variables", at(e));
                return false;
            }
        }
        std::vector<H::ExprPtr> terms;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            terms.push_back(relational_.value(H::Op::MUL,
                                              {coefficients[i], scope[i]}, at(e)));
        }
        H::ExprPtr total = terms.size() == 1 ? terms.front()
            : relational_.value(H::Op::ADD, terms, at(e));
        H::ExprPtr formula = condition(total, result->text, e, diags);
        if (!formula) { return false; }
        addFormula(relational_.relation(std::move(formula), {total}), e);
        return true;
    }

    bool countConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* values = e.child("values");
        const Elem* result = e.child("condition");
        if (!list || !values || !result) {
            diags.error(ErrorCode::E_PARSE,
                        "count requires <list>, <values> and <condition>", at(e));
            return false;
        }
        std::vector<H::ExprPtr> scope;
        if (!expressionList(list->text, scope, e, diags)) { return false; }
        std::vector<H::ExprPtr> sought;
        if (!termList(values->text, sought, e, diags)) { return false; }
        if (scope.empty() || sought.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "count requires a nonempty list and at least one value", at(e));
            return false;
        }
        std::vector<H::ExprPtr> indicators;
        for (const H::ExprPtr& term : scope) {
            std::vector<H::ExprPtr> matches;
            for (const H::ExprPtr& value : sought) {
                matches.push_back(relational_.value(H::Op::EQ, {term, value}, at(e)));
            }
            H::ExprPtr match = matches.size() == 1 ? matches.front()
                : relational_.value(H::Op::OR, matches, at(e));
            indicators.push_back(relational_.conditional(match, num(1), num(0), at(e)));
        }
        H::ExprPtr total = indicators.size() == 1 ? indicators.front()
            : relational_.value(H::Op::ADD, indicators, at(e));
        H::ExprPtr formula = condition(total, result->text, e, diags);
        if (!formula) { return false; }
        addFormula(relational_.relation(std::move(formula), {total}), e);
        return true;
    }

    bool nValuesConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* result = e.child("condition");
        if (!list || !result) {
            diags.error(ErrorCode::E_PARSE,
                        "nValues requires <list> and <condition>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE, "nValues requires at least two variables", at(e));
            return false;
        }
        std::vector<long long> except;
        if (const Elem* excluded = e.child("except")) {
            for (const std::string& token : words(excluded->text)) {
                long long value = 0;
                if (!toInt(token, value)) {
                    diags.error(ErrorCode::E_PARSE,
                                "nValues except entry '" + token + "' is not an integer",
                                at(e));
                    return false;
                }
                except.push_back(value);
            }
        }
        std::string compact_condition;
        for (const char c : result->text) {
            if (!std::isspace(static_cast<unsigned char>(c))) { compact_condition += c; }
        }
        const bool one_value = compact_condition == "(eq,1)"
            || compact_condition == "(le,1)" || compact_condition == "(lt,2)";
        const bool multiple_values = compact_condition == "(ne,1)"
            || compact_condition == "(gt,1)" || compact_condition == "(ge,2)";
        if (except.empty() && (one_value || multiple_values)) {
            // A nonempty list has exactly one distinct value iff every entry
            // equals its first. Ramsey instances post this relation many times;
            // materializing the cardinality first needlessly builds O(n^2) ASTs.
            // Native n-ary equality is the same chain relation with one
            // operator. Keeping NOT outside it is essential for nValues > 1:
            // at least one unequal pair does not mean pairwise distinctness.
            std::vector<H::ExprPtr> terms;
            terms.reserve(scope.size());
            for (const auto& name : scope) { terms.push_back(var(name)); }
            H::ExprPtr uniform = H::mkOp(H::Op::EQ, std::move(terms), at(e));
            addFormula(one_value ? uniform : H::mkOp(H::Op::NOT, {uniform}, at(e)), e);
            return true;
        }
        // xi contributes once exactly when it is not excluded and no earlier
        // variable has the same value. This is O(n^2), exact, and introduces no
        // auxiliary model components that beta would have to hide.
        std::vector<H::ExprPtr> indicators;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            std::vector<H::ExprPtr> first;
            for (const long long value : except) {
                H::ExprPtr equal = H::mkOp(H::Op::EQ,
                                           {var(scope[i]), num(value)}, at(e));
                first.push_back(H::mkOp(H::Op::NOT, {equal}, at(e)));
            }
            for (std::size_t j = 0; j < i; ++j) {
                H::ExprPtr equal = H::mkOp(H::Op::EQ,
                                           {var(scope[i]), var(scope[j])}, at(e));
                first.push_back(H::mkOp(H::Op::NOT, {equal}, at(e)));
            }
            indicators.push_back(H::mkOp(
                H::Op::ITE, {conjunction(std::move(first), e), num(1), num(0)}, at(e)));
        }
        H::ExprPtr total = H::mkOp(H::Op::ADD, std::move(indicators), at(e));
        H::ExprPtr formula = condition(total, result->text, e, diags);
        if (!formula) { return false; }
        addFormula(std::move(formula), e);
        return true;
    }

    bool extremumConstraint(const Elem& e, bool minimum, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* result = e.child("condition");
        const Elem* index_node = e.child("index");
        if (!list || (!result && !index_node)) {
            diags.error(ErrorCode::E_PARSE,
                        e.name + " requires <list> and either <condition> or <index>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        e.name + " requires at least two variables", at(e));
            return false;
        }
        std::vector<H::ExprPtr> terms;
        for (const std::string& name : scope) { terms.push_back(var(name)); }
        H::ExprPtr value = extremumValue(std::move(terms), minimum, at(e));
        std::vector<H::ExprPtr> formulas;
        if (result) {
            H::ExprPtr formula = condition(value, result->text, e, diags);
            if (!formula) { return false; }
            formulas.push_back(std::move(formula));
        }
        if (index_node) {
            H::ExprPtr index = scalar(index_node->text, e, diags);
            if (!index || index->kind != H::ExprKind::IDENT) {
                if (index) {
                    diags.error(ErrorCode::E_PARSE,
                                e.name + " <index> must be a declared variable", at(e));
                }
                return false;
            }
            long long start = 0;
            if (!list->attr("startIndex").empty()
                && !toInt(list->attr("startIndex"), start)) {
                diags.error(ErrorCode::E_PARSE,
                            e.name + " startIndex is not an integer", at(e));
                return false;
            }
            const std::string rank = index_node->attr("rank", "any");
            if (rank != "any" && rank != "first" && rank != "last") {
                diags.error(ErrorCode::E_PARSE,
                            e.name + " rank '" + rank + "' is invalid", at(e));
                return false;
            }
            std::vector<H::ExprPtr> alternatives;
            for (std::size_t i = 0; i < scope.size(); ++i) {
                std::vector<H::ExprPtr> selected;
                selected.push_back(H::mkOp(
                    H::Op::EQ,
                    {index, num(start + static_cast<long long>(i))}, at(e)));
                selected.push_back(H::mkOp(H::Op::EQ,
                                           {var(scope[i]), value}, at(e)));
                const std::size_t begin = rank == "last" ? i + 1 : 0;
                const std::size_t end = rank == "first" ? i : scope.size();
                if (rank != "any") {
                    for (std::size_t j = begin; j < end; ++j) {
                        H::ExprPtr tie = H::mkOp(H::Op::EQ,
                                                {var(scope[j]), value}, at(e));
                        selected.push_back(H::mkOp(H::Op::NOT, {tie}, at(e)));
                    }
                }
                alternatives.push_back(conjunction(std::move(selected), e));
            }
            formulas.push_back(disjunction(std::move(alternatives), e));
        }
        addFormula(conjunction(std::move(formulas), e), e);
        return true;
    }

    bool elementConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* matrix = e.child("matrix");
        const Elem* index_node = e.child("index");
        const Elem* condition_node = e.child("condition");
        const Elem* value_node = e.child("value");
        if (static_cast<int>(list != nullptr) + static_cast<int>(matrix != nullptr) != 1) {
            diags.error(ErrorCode::E_PARSE,
                        "element requires exactly one of <list> or <matrix>", at(e));
            return false;
        }

        if (matrix) {
            if (!index_node
                || static_cast<int>(condition_node != nullptr)
                     + static_cast<int>(value_node != nullptr) != 1) {
                diags.error(ErrorCode::E_PARSE,
                            "matrix element requires <index> and exactly one of "
                            "<condition> or <value>", at(e));
                return false;
            }
            std::vector<std::vector<H::ExprPtr>> rows;
            if (trim(matrix->text).find('(') == std::string::npos) {
                std::vector<std::vector<std::string>> names;
                if (!variableMatrix(matrix->text, names, *matrix, diags)) { return false; }
                for (const auto& row : names) {
                    rows.emplace_back();
                    for (const std::string& name : row) {
                        rows.back().push_back(var(name));
                    }
                }
            } else if (!termMatrix(matrix->text, rows, *matrix, diags)) {
                return false;
            }

            std::vector<std::string> indices;
            if (!varList(index_node->text, indices, *index_node, diags)) { return false; }
            if (indices.size() != 2) {
                diags.error(ErrorCode::E_PARSE,
                            "matrix element <index> must contain exactly two integer "
                            "variables", at(*index_node));
                return false;
            }
            long long row_start = 0, column_start = 0;
            if ((!matrix->attr("startRowIndex").empty()
                 && !toInt(matrix->attr("startRowIndex"), row_start))
                || (!matrix->attr("startColIndex").empty()
                    && !toInt(matrix->attr("startColIndex"), column_start))) {
                diags.error(ErrorCode::E_PARSE,
                            "matrix element start indexes must be integers", at(*matrix));
                return false;
            }
            const auto indexValue = [&](long long start, std::size_t offset,
                                        long long& result) {
                if (offset > static_cast<std::size_t>(
                                 std::numeric_limits<long long>::max())) {
                    return false;
                }
                const long long delta = static_cast<long long>(offset);
                if (start > std::numeric_limits<long long>::max() - delta) {
                    return false;
                }
                result = start + delta;
                return true;
            };
            H::ExprPtr deprecated_value;
            if (value_node) {
                deprecated_value = scalar(value_node->text, *value_node, diags);
                if (!deprecated_value) { return false; }
            }
            std::vector<H::ExprPtr> alternatives;
            for (std::size_t row = 0; row < rows.size(); ++row) {
                long long row_index = 0;
                if (!indexValue(row_start, row, row_index)) {
                    diags.error(ErrorCode::E_RESOURCE,
                                "matrix element row index exceeds int64", at(*matrix));
                    return false;
                }
                for (std::size_t column = 0; column < rows[row].size(); ++column) {
                    long long column_index = 0;
                    if (!indexValue(column_start, column, column_index)) {
                        diags.error(ErrorCode::E_RESOURCE,
                                    "matrix element column index exceeds int64", at(*matrix));
                        return false;
                    }
                    H::ExprPtr relation = condition_node
                        ? condition(rows[row][column], condition_node->text,
                                    *condition_node, diags)
                        : H::mkOp(H::Op::EQ,
                                  {rows[row][column], deprecated_value}, at(e));
                    if (!relation) { return false; }
                    alternatives.push_back(conjunction(
                        {H::mkOp(H::Op::EQ,
                                 {var(indices[0]), num(row_index)}, at(e)),
                         H::mkOp(H::Op::EQ,
                                 {var(indices[1]), num(column_index)}, at(e)),
                         std::move(relation)}, e));
                }
            }
            addFormula(disjunction(std::move(alternatives), e), e);
            return true;
        }

        if (!index_node && (!value_node || condition_node)) {
            diags.error(ErrorCode::E_PARSE,
                        "element membership requires <list> and <value>", at(e));
            return false;
        }
        if (index_node
            && static_cast<int>(condition_node != nullptr)
                 + static_cast<int>(value_node != nullptr) != 1) {
            diags.error(ErrorCode::E_PARSE,
                        "indexed element requires exactly one of <condition> or <value>",
                        at(e));
            return false;
        }
        std::vector<H::ExprPtr> entries;
        if (!termList(list->text, entries, e, diags)) { return false; }
        if (entries.size() < 2) {
            diags.error(ErrorCode::E_PARSE, "element requires at least two list entries", at(e));
            return false;
        }
        H::ExprPtr value;
        if (value_node) {
            value = scalar(value_node->text, *value_node, diags);
            if (!value) { return false; }
        }
        std::vector<H::ExprPtr> alternatives;
        if (!index_node) {
            for (const H::ExprPtr& entry : entries) {
                alternatives.push_back(H::mkOp(H::Op::EQ, {entry, value}, at(e)));
            }
        } else {
            H::ExprPtr index = scalar(index_node->text, e, diags);
            if (!index || index->kind != H::ExprKind::IDENT) {
                if (index) {
                    diags.error(ErrorCode::E_PARSE,
                                "element <index> must be a declared integer variable", at(e));
                }
                return false;
            }
            long long start = 0;
            if (!list->attr("startIndex").empty()
                && !toInt(list->attr("startIndex"), start)) {
                diags.error(ErrorCode::E_PARSE,
                            "element startIndex is not an integer", at(e));
                return false;
            }
            const std::string rank = index_node->attr("rank", "any");
            if (rank != "any" && rank != "first" && rank != "last") {
                diags.error(ErrorCode::E_PARSE,
                            "element rank '" + rank + "' is invalid", at(e));
                return false;
            }
            // Ordinary MiniXCSP instances repeat indexed equality with many
            // different lists. A positional helper shares the selection tree
            // without capturing any row's cells or conflating aliased actuals.
            // Only total integer operands enter it; partial expression views
            // retain their established relational-definedness lowering below.
            const auto totalInteger = [](const H::ExprPtr& term) {
                return term && term->sort.kind == H::SortKind::INT
                    && (term->kind == H::ExprKind::IDENT
                        || term->kind == H::ExprKind::LIT_INT);
            };
            if (!compiling_shared_element_ && rank == "any" && value_node
                && totalInteger(value)
                && std::all_of(entries.begin(), entries.end(), totalInteger)
                && entries.size() - 1 <= static_cast<std::size_t>(
                    std::numeric_limits<long long>::max())
                && start <= std::numeric_limits<long long>::max()
                    - static_cast<long long>(entries.size() - 1)) {
                const auto key = std::make_pair(entries.size(), start);
                auto found = positional_element_helpers_.find(key);
                if (found == positional_element_helpers_.end()) {
                    H::FunDecl definition;
                    definition.name = freshGroupFunctionName();
                    definition.result = H::Sort::boolean();
                    definition.loc = at(e);
                    definition.auxiliary = true;
                    std::vector<H::ExprPtr> operands;
                    std::unordered_set<std::string> names;
                    for (std::size_t i = 0; i < entries.size() + 2; ++i) {
                        const std::string name = freshGroupBinderName(definition.name, i, names);
                        names.insert(name);
                        definition.params.push_back(H::Sort::integer());
                        definition.binders.push_back({name, H::Sort::integer()});
                        operands.push_back(H::mkBoundVar(name, H::Sort::integer(), at(e)));
                    }
                    std::vector<H::ExprPtr> choices;
                    for (std::size_t i = 0; i < entries.size(); ++i) {
                        choices.push_back(conjunction({
                            H::mkOp(H::Op::EQ,
                                {operands[entries.size()], num(start + static_cast<long long>(i))},
                                at(e)),
                            H::mkOp(H::Op::EQ,
                                {operands[i], operands[entries.size() + 1]}, at(e))}, e));
                    }
                    definition.body = disjunction(std::move(choices), e);
                    found = positional_element_helpers_.emplace(key, definition.name).first;
                    model_->funs.push_back(std::move(definition));
                }
                entries.push_back(std::move(index));
                entries.push_back(std::move(value));
                // The helper is already exact for positional aliases. Keep
                // pure scalar calls in the same compact representation as
                // group calls, so their coordinates need not be materialized
                // again in the ordinary lowering preamble. Literal or partial
                // operands retain the ordinary expression path.
                if (std::all_of(entries.begin(), entries.end(), [](const H::ExprPtr& term) {
                        return term->kind == H::ExprKind::IDENT;
                    })) {
                    std::vector<std::string> names;
                    names.reserve(entries.size());
                    for (const auto& entry : entries) { names.push_back(entry->name); }
                    if (packFunctionCall(found->second, names, e)) { return true; }
                }
                addFormula(H::mkApply(found->second, H::Sort::boolean(),
                                      std::move(entries), at(e)), e);
                return true;
            }
            for (std::size_t i = 0; i < entries.size(); ++i) {
                if (i > static_cast<std::size_t>(
                            std::numeric_limits<long long>::max())
                    || start > std::numeric_limits<long long>::max()
                                   - static_cast<long long>(i)) {
                    diags.error(ErrorCode::E_RESOURCE,
                                "element index exceeds int64", at(*list));
                    return false;
                }
                std::vector<H::ExprPtr> selected;
                selected.push_back(H::mkOp(
                    H::Op::EQ, {index, num(start + static_cast<long long>(i))}, at(e)));
                H::ExprPtr relation = condition_node
                    ? condition(entries[i], condition_node->text, *condition_node, diags)
                    : H::mkOp(H::Op::EQ, {entries[i], value}, at(e));
                if (!relation) { return false; }
                selected.push_back(std::move(relation));
                const std::size_t begin = rank == "last" ? i + 1 : 0;
                const std::size_t end = rank == "first" ? i : entries.size();
                if (rank != "any") {
                    if (!value) {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                    "element rank requires the deprecated equality <value> "
                                    "form", at(*index_node));
                        return false;
                    }
                    for (std::size_t j = begin; j < end; ++j) {
                        H::ExprPtr equal = H::mkOp(H::Op::EQ,
                                                   {entries[j], value}, at(e));
                        selected.push_back(H::mkOp(H::Op::NOT, {equal}, at(e)));
                    }
                }
                alternatives.push_back(conjunction(std::move(selected), e));
            }
        }
        addFormula(disjunction(std::move(alternatives), e), e);
        return true;
    }

    bool integerList(const std::string& text, std::vector<long long>& out,
                     std::size_t expected, const Elem& e, Uir::Diagnostics& diags) {
        for (const std::string& token : words(text)) {
            const std::size_t repeat = token.find('x');
            long long value = 0, count = 1;
            if (!toInt(token.substr(0, repeat), value)
                || (repeat != std::string::npos
                    && (!toInt(token.substr(repeat + 1), count) || count <= 0))) {
                diags.error(ErrorCode::E_PARSE,
                            "invalid integer or repetition '" + token + "'", at(e));
                return false;
            }
            // Check against the accompanying scope before expanding a compact
            // repetition; malformed huge counts must not cause an allocation.
            if (static_cast<unsigned long long>(count) > expected - out.size()) {
                diags.error(ErrorCode::E_PARSE, "too many integer values for the list", at(e));
                return false;
            }
            out.insert(out.end(), static_cast<std::size_t>(count), value);
        }
        if (out.size() != expected) {
            diags.error(ErrorCode::E_PARSE,
                        "the list has " + std::to_string(out.size()) + " integer values for "
                            + std::to_string(expected) + " terms", at(e));
            return false;
        }
        return true;
    }

    bool instantiationConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* values = e.child("values");
        if (!list || !values) {
            diags.error(ErrorCode::E_PARSE,
                        "instantiation requires <list> and <values>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        std::vector<long long> integers;
        if (!integerList(values->text, integers, scope.size(), e, diags)) { return false; }
        std::vector<H::ExprPtr> equalities;
        for (std::size_t i = 0; i < scope.size(); ++i) {
            equalities.push_back(H::mkOp(H::Op::EQ,
                                         {var(scope[i]), num(integers[i])}, at(e)));
        }
        addFormula(conjunction(std::move(equalities), e), e);
        return true;
    }

    H::ExprPtr orderedRelation(const std::string& op, H::ExprPtr lhs, H::ExprPtr rhs,
                               const Elem& e, Uir::Diagnostics& diags) const {
        if (op == "lt") { return H::mkOp(H::Op::LT, {lhs, rhs}, at(e)); }
        if (op == "le") { return H::mkOp(H::Op::LE, {lhs, rhs}, at(e)); }
        if (op == "gt") { return H::mkOp(H::Op::GT, {lhs, rhs}, at(e)); }
        if (op == "ge") { return H::mkOp(H::Op::GE, {lhs, rhs}, at(e)); }
        diags.error(ErrorCode::E_PARSE,
                    "ordered operator '" + op + "' must be lt, le, gt or ge", at(e));
        return nullptr;
    }

    bool orderedConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const std::string list_text = list ? list->text : e.text;
        std::vector<std::string> scope;
        if (!varList(list_text, scope, e, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE, "ordered requires at least two variables", at(e));
            return false;
        }
        std::string op;
        if (const Elem* operation = e.child("operator")) {
            const std::vector<std::string> tokens = words(operation->text);
            if (tokens.size() != 1) {
                diags.error(ErrorCode::E_PARSE, "ordered has an invalid operator", at(e));
                return false;
            }
            op = tokens.front();
        } else {
            const std::string kind = e.attr("case");
            if (kind == "increasing") { op = "le"; }
            else if (kind == "strictlyIncreasing") { op = "lt"; }
            else if (kind == "decreasing") { op = "ge"; }
            else if (kind == "strictlyDecreasing") { op = "gt"; }
            else {
                diags.error(ErrorCode::E_PARSE,
                            "ordered needs <operator> or a valid case attribute", at(e));
                return false;
            }
        }
        std::vector<H::ExprPtr> lengths;
        if (const Elem* length_node = e.child("lengths")) {
            if (!termList(length_node->text, lengths, e, diags)) { return false; }
            if (lengths.size() + 1 != scope.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "ordered has " + std::to_string(lengths.size())
                                + " lengths for " + std::to_string(scope.size())
                                + " variables", at(e));
                return false;
            }
        }
        std::vector<H::ExprPtr> relations;
        for (std::size_t i = 0; i + 1 < scope.size(); ++i) {
            H::ExprPtr lhs = var(scope[i]);
            if (!lengths.empty()) {
                lhs = H::mkOp(H::Op::ADD, {lhs, lengths[i]}, at(e));
            }
            H::ExprPtr relation = orderedRelation(op, lhs, var(scope[i + 1]), e, diags);
            if (!relation) { return false; }
            relations.push_back(std::move(relation));
        }
        addFormula(conjunction(std::move(relations), e), e);
        return true;
    }

    H::ExprPtr lexPair(const std::vector<H::ExprPtr>& left,
                       const std::vector<H::ExprPtr>& right, const std::string& op,
                       const Elem& e, Uir::Diagnostics& diags) const {
        if (left.size() != right.size() || left.empty()) {
            diags.error(ErrorCode::E_PARSE,
                        "lex lists must have the same nonzero length", at(e));
            return nullptr;
        }
        const bool strict = op == "lt" || op == "gt";
        const bool ascending = op == "lt" || op == "le";
        if (op != "lt" && op != "le" && op != "gt" && op != "ge") {
            diags.error(ErrorCode::E_PARSE,
                        "lex operator '" + op + "' must be lt, le, gt or ge", at(e));
            return nullptr;
        }
        // A suffix represents the comparison after an equal prefix. Keeping
        // that suffix once avoids copying O(n^2) equality operands. The final
        // equal tuple is accepted exactly for a non-strict comparison.
        H::ExprPtr suffix = H::mkBool(!strict, at(e));
        for (std::size_t i = left.size(); i-- > 0;) {
            H::ExprPtr comparison = H::mkOp(
                ascending ? H::Op::LT : H::Op::GT,
                {left[i], right[i]}, at(e));
            H::ExprPtr equal = H::mkOp(H::Op::EQ, {left[i], right[i]}, at(e));
            H::ExprPtr continuation = conjunction({std::move(equal),
                                                  std::move(suffix)}, e);
            suffix = disjunction({std::move(comparison),
                                  std::move(continuation)}, e);
        }
        return suffix;
    }

    bool lexConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* operation = e.child("operator");
        if (!operation) {
            diags.error(ErrorCode::E_PARSE, "lex has no <operator>", at(e));
            return false;
        }
        const std::vector<std::string> op_tokens = words(operation->text);
        if (op_tokens.size() != 1) {
            diags.error(ErrorCode::E_PARSE, "lex has an invalid operator", at(e));
            return false;
        }
        std::vector<std::vector<H::ExprPtr>> lists;
        if (const Elem* matrix = e.child("matrix")) {
            std::vector<std::vector<std::string>> names;
            if (!variableMatrix(matrix->text, names, *matrix, diags)) { return false; }
            for (const auto& row : names) {
                lists.emplace_back();
                for (const std::string& name : row) {
                    lists.back().push_back(var(name));
                }
            }
            std::vector<H::ExprPtr> relations;
            for (std::size_t row = 0; row + 1 < lists.size(); ++row) {
                H::ExprPtr relation = lexPair(
                    lists[row], lists[row + 1], op_tokens.front(), e, diags);
                if (!relation) { return false; }
                relations.push_back(std::move(relation));
            }
            for (std::size_t column = 0; column + 1 < lists.front().size(); ++column) {
                std::vector<H::ExprPtr> left, right;
                for (const auto& row : lists) {
                    left.push_back(row[column]);
                    right.push_back(row[column + 1]);
                }
                H::ExprPtr relation = lexPair(
                    left, right, op_tokens.front(), e, diags);
                if (!relation) { return false; }
                relations.push_back(std::move(relation));
            }
            addFormula(conjunction(std::move(relations), e), e);
            return true;
        }
        for (const Elem& child : e.children) {
            if (child.name != "list") { continue; }
            lists.emplace_back();
            if (!termList(child.text, lists.back(), child, diags)) { return false; }
        }
        if (lists.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "lex requires at least two <list> elements", at(e));
            return false;
        }
        std::vector<H::ExprPtr> chain;
        for (std::size_t i = 0; i + 1 < lists.size(); ++i) {
            H::ExprPtr relation = lexPair(lists[i], lists[i + 1], op_tokens.front(), e, diags);
            if (!relation) { return false; }
            chain.push_back(std::move(relation));
        }
        addFormula(conjunction(std::move(chain), e), e);
        return true;
    }

    bool cardinalityConstraint(const Elem& e, Uir::Diagnostics& diags) {
        const Elem* list = e.child("list");
        const Elem* values_node = e.child("values");
        const Elem* occurs_node = e.child("occurs");
        if (!list || !values_node || !occurs_node) {
            diags.error(ErrorCode::E_PARSE,
                        "cardinality requires <list>, <values> and <occurs>", at(e));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, e, diags)) { return false; }
        std::vector<H::ExprPtr> values;
        if (!termList(values_node->text, values, e, diags)) { return false; }
        const std::vector<std::string> occurs = words(occurs_node->text);
        if (scope.size() < 2 || values.empty() || values.size() != occurs.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "cardinality requires |list|>=2 and equally sized nonempty "
                        "values/occurs lists", at(e));
            return false;
        }
        std::vector<H::ExprPtr> formulas;
        for (std::size_t value_index = 0; value_index < values.size(); ++value_index) {
            std::vector<H::ExprPtr> indicators;
            for (const std::string& variable : scope) {
                H::ExprPtr equal = H::mkOp(
                    H::Op::EQ, {var(variable), values[value_index]}, at(e));
                indicators.push_back(H::mkOp(
                    H::Op::ITE, {equal, num(1), num(0)}, at(e)));
            }
            H::ExprPtr count = H::mkOp(H::Op::ADD, std::move(indicators), at(e));
            if (occurs[value_index].find("..") != std::string::npos) {
                formulas.push_back(condition(
                    count, "(in," + occurs[value_index] + ")", e, diags));
                if (!formulas.back()) { return false; }
            } else {
                H::ExprPtr occurrence = scalar(occurs[value_index], e, diags);
                if (!occurrence) { return false; }
                formulas.push_back(H::mkOp(H::Op::EQ, {count, occurrence}, at(e)));
            }
        }
        // Variable values must themselves be distinct in the distribute form.
        if (!values.empty() && values.front()->kind == H::ExprKind::IDENT) {
            for (std::size_t i = 0; i < values.size(); ++i) {
                for (std::size_t j = i + 1; j < values.size(); ++j) {
                    H::ExprPtr equal = H::mkOp(H::Op::EQ,
                                               {values[i], values[j]}, at(e));
                    formulas.push_back(H::mkOp(H::Op::NOT, {equal}, at(e)));
                }
            }
        }
        const std::string closed = values_node->attr("closed", "false");
        if (closed != "true" && closed != "false") {
            diags.error(ErrorCode::E_PARSE,
                        "cardinality closed must be true or false", at(e));
            return false;
        }
        if (closed == "true") {
            for (const std::string& variable : scope) {
                std::vector<H::ExprPtr> matches;
                for (const H::ExprPtr& value : values) {
                    matches.push_back(H::mkOp(H::Op::EQ,
                                              {var(variable), value}, at(e)));
                }
                formulas.push_back(disjunction(std::move(matches), e));
            }
        }
        addFormula(conjunction(std::move(formulas), e), e);
        return true;
    }

    bool channelConstraint(const Elem& e, Uir::Diagnostics& diags) {
        std::vector<const Elem*> list_nodes;
        for (const Elem& child : e.children) {
            if (child.name == "list") { list_nodes.push_back(&child); }
        }
        if (list_nodes.empty()) {
            diags.error(ErrorCode::E_PARSE, "channel has no <list>", at(e));
            return false;
        }
        std::vector<std::vector<std::string>> lists(list_nodes.size());
        for (std::size_t i = 0; i < list_nodes.size(); ++i) {
            if (!varList(list_nodes[i]->text, lists[i], *list_nodes[i], diags)) { return false; }
            if (lists[i].size() < 2) {
                diags.error(ErrorCode::E_PARSE,
                            "channel lists require at least two variables", at(e));
                return false;
            }
        }
        auto startIndex = [&](const Elem& node, long long& start) {
            start = 0;
            if (node.attr("startIndex").empty()) { return true; }
            if (toInt(node.attr("startIndex"), start)) { return true; }
            diags.error(ErrorCode::E_PARSE, "channel startIndex is not an integer", at(node));
            return false;
        };
        long long x_start = 0;
        if (!startIndex(*list_nodes[0], x_start)) { return false; }
        std::vector<H::ExprPtr> formulas;
        if (const Elem* value_node = e.child("value")) {
            if (list_nodes.size() != 1) {
                diags.error(ErrorCode::E_PARSE,
                            "channel with <value> must contain exactly one list", at(e));
                return false;
            }
            H::ExprPtr value = scalar(value_node->text, e, diags);
            if (!value || value->kind != H::ExprKind::IDENT) { return false; }
            formulas.push_back(H::mkOp(H::Op::GE, {value, num(x_start)}, at(e)));
            formulas.push_back(H::mkOp(
                H::Op::LE,
                {value, num(x_start + static_cast<long long>(lists[0].size()) - 1)},
                at(e)));
            for (std::size_t i = 0; i < lists[0].size(); ++i) {
                const Domain& domain = *sourceVariable(lists[0][i]).domain;
                if (domain.sparse() || domain.lo != 0 || domain.hi != 1) {
                    diags.error(ErrorCode::E_TYPE,
                                "channel 01Var list entries must have domain exactly 0..1",
                                at(e));
                    return false;
                }
                H::ExprPtr bit = H::mkOp(H::Op::EQ,
                                          {var(lists[0][i]), num(1)}, at(e));
                H::ExprPtr position = H::mkOp(
                    H::Op::EQ,
                    {value, num(x_start + static_cast<long long>(i))}, at(e));
                formulas.push_back(H::mkOp(H::Op::EQ, {bit, position}, at(e)));
            }
        } else if (list_nodes.size() == 1) {
            for (std::size_t i = 0; i < lists[0].size(); ++i) {
                formulas.push_back(H::mkOp(
                    H::Op::GE, {var(lists[0][i]), num(x_start)}, at(e)));
                formulas.push_back(H::mkOp(
                    H::Op::LE,
                    {var(lists[0][i]),
                     num(x_start + static_cast<long long>(lists[0].size()) - 1)},
                    at(e)));
                for (std::size_t j = 0; j < lists[0].size(); ++j) {
                    H::ExprPtr antecedent = H::mkOp(
                        H::Op::EQ,
                        {var(lists[0][i]), num(x_start + static_cast<long long>(j))}, at(e));
                    H::ExprPtr consequent = H::mkOp(
                        H::Op::EQ,
                        {var(lists[0][j]), num(x_start + static_cast<long long>(i))}, at(e));
                    formulas.push_back(H::mkOp(H::Op::IMPLIES,
                                               {antecedent, consequent}, at(e)));
                }
            }
        } else if (list_nodes.size() == 2) {
            if (lists[0].size() != lists[1].size()) {
                diags.error(ErrorCode::E_PARSE,
                            "the two channel lists must have the same size", at(e));
                return false;
            }
            long long y_start = 0;
            if (!startIndex(*list_nodes[1], y_start)) { return false; }
            for (std::size_t i = 0; i < lists[0].size(); ++i) {
                formulas.push_back(H::mkOp(
                    H::Op::GE, {var(lists[0][i]), num(y_start)}, at(e)));
                formulas.push_back(H::mkOp(
                    H::Op::LE,
                    {var(lists[0][i]),
                     num(y_start + static_cast<long long>(lists[1].size()) - 1)},
                    at(e)));
                formulas.push_back(H::mkOp(
                    H::Op::GE, {var(lists[1][i]), num(x_start)}, at(e)));
                formulas.push_back(H::mkOp(
                    H::Op::LE,
                    {var(lists[1][i]),
                     num(x_start + static_cast<long long>(lists[0].size()) - 1)},
                    at(e)));
                for (std::size_t j = 0; j < lists[1].size(); ++j) {
                    H::ExprPtr left = H::mkOp(
                        H::Op::EQ,
                        {var(lists[0][i]), num(y_start + static_cast<long long>(j))}, at(e));
                    H::ExprPtr right = H::mkOp(
                        H::Op::EQ,
                        {var(lists[1][j]), num(x_start + static_cast<long long>(i))}, at(e));
                    formulas.push_back(H::mkOp(H::Op::EQ, {left, right}, at(e)));
                }
            }
        } else {
            diags.error(ErrorCode::E_PARSE, "channel accepts at most two lists", at(e));
            return false;
        }
        addFormula(conjunction(std::move(formulas), e), e);
        return true;
    }

    static void replaceAll(std::string& text, const std::string& from,
                           const std::string& to) {
        if (from.empty()) { return; }
        std::size_t position = 0;
        while ((position = text.find(from, position)) != std::string::npos) {
            text.replace(position, from.size(), to);
            position += to.size();
        }
    }

    static int highestFormal(const Elem& element) {
        int highest = -1;
        auto inspect = [&](std::string_view text) {
            for (std::size_t i = 0; i + 1 < text.size(); ++i) {
                if (text[i] != '%'
                    || !std::isdigit(static_cast<unsigned char>(text[i + 1]))) {
                    continue;
                }
                std::size_t end = i + 1;
                unsigned long long value = 0;
                while (end < text.size()
                       && std::isdigit(static_cast<unsigned char>(text[end]))) {
                    value = value * 10 + static_cast<unsigned>(text[end] - '0');
                    if (value > static_cast<unsigned long long>(std::numeric_limits<int>::max())) {
                        return;
                    }
                    ++end;
                }
                highest = std::max(highest, static_cast<int>(value));
                i = end - 1;
            }
        };
        std::vector<const Elem*> pending{&element};
        while (!pending.empty()) {
            const Elem* node = pending.back(); pending.pop_back();
            inspect(node->textView());
            for (const auto& attribute : node->attrs) { inspect(attribute.second); }
            for (const Elem& child : node->children) { pending.push_back(&child); }
        }
        return highest;
    }

    static bool substituteFormals(Elem& element, const std::vector<std::string>& arguments,
                                  int highest) {
        std::string tail;
        const std::size_t tail_start = highest < 0 ? 0 : static_cast<std::size_t>(highest + 1);
        for (std::size_t i = tail_start; i < arguments.size(); ++i) {
            if (!tail.empty()) { tail += ' '; }
            tail += arguments[i];
        }
        auto substitute = [&](std::string& text) {
            replaceAll(text, "%...", tail);
            for (std::size_t i = arguments.size(); i-- > 0;) {
                replaceAll(text, "%" + std::to_string(i), arguments[i]);
            }
            return text.find('%') == std::string::npos;
        };
        bool ok = true;
        std::vector<Elem*> pending{&element};
        while (!pending.empty()) {
            Elem& node = *pending.back(); pending.pop_back();
            if ((node.table_storage || !node.table_text.empty())
                && node.textView().find('%') != std::string_view::npos) {
                node.text = std::string(node.textView());
                node.table_text = {}; node.table_storage.reset();
            }
            ok = substitute(node.text) && ok;
            for (auto& attribute : node.attrs) { ok = substitute(attribute.second) && ok; }
            for (Elem& child : node.children) { pending.push_back(&child); }
        }
        return ok;
    }

    /** Try compiling a fixed-arity extension group into one exact Boolean
     *  helper. Only simple positional-variable templates are eligible; every
     *  other legal group keeps the established expansion path below. */
    bool sharedExtensionGroup(Elem& group, Elem& pattern, int highest,
                              std::size_t argument_count, bool& handled,
                              Uir::Diagnostics& diags) {
        handled = false;
        if (pattern.name != "extension" || highest < 0 || argument_count < 2) {
            return true;
        }

        const Elem* list = nullptr;
        const Elem* table = nullptr;
        bool supports = false;
        if (!pattern.attrs.empty() || pattern.children.size() != 2) { return true; }
        for (const Elem& child : pattern.children) {
            if (child.name == "list" && !list) { list = &child; }
            else if ((child.name == "supports" || child.name == "conflicts") && !table) {
                table = &child;
                supports = child.name == "supports";
            } else {
                return true;
            }
        }
        if (!list || !table || !list->attrs.empty() || !list->children.empty()
            || !table->children.empty() || table->textView().find('%') != std::string_view::npos) {
            return true;
        }
        // Attributes do not participate in the supported table syntax. Keep
        // any formal-bearing form on the established substitution path rather
        // than accidentally treating an attribute reference as irrelevant.
        for (const auto& attribute : table->attrs) {
            if (attribute.second.find('%') != std::string::npos) { return true; }
        }

        const std::vector<std::string> placeholders = words(std::string(list->textView()));
        // Unary extension tables use XCSP's bare-value/range syntax rather
        // than parenthesized tuples; leave them on the established path.
        if (placeholders.size() < 2) { return true; }
        std::vector<std::size_t> formal_slots;
        std::vector<std::size_t> column_parameters;
        std::unordered_map<std::size_t, std::size_t> formal_to_parameter;
        std::size_t list_highest = 0;
        column_parameters.reserve(placeholders.size());
        for (const std::string& token : placeholders) {
            if (token.size() < 2 || token[0] != '%') { return true; }
            std::size_t slot = 0;
            for (std::size_t i = 1; i < token.size(); ++i) {
                const unsigned char ch = static_cast<unsigned char>(token[i]);
                if (!std::isdigit(ch)
                    || slot > (std::numeric_limits<std::size_t>::max() - (ch - '0')) / 10) {
                    return true;
                }
                slot = slot * 10 + (ch - '0');
            }
            if (token != "%" + std::to_string(slot)) { return true; }
            list_highest = std::max(list_highest, slot);
            if (formal_to_parameter.find(slot) == formal_to_parameter.end()) {
                formal_to_parameter.emplace(slot, formal_slots.size());
                formal_slots.push_back(slot);
            }
            column_parameters.push_back(formal_to_parameter.at(slot));
        }
        // The existing expander recognizes formals in attributes and nested
        // elements too. Restrict sharing to the case where the list accounts
        // for every formal, rather than silently dropping any such use.
        if (list_highest != static_cast<std::size_t>(highest)) { return true; }

        // Preflight and retain each row without emitting diagnostics. Sharing
        // the domain-aware ordinary relation is sound only when each formal
        // position has the same exact declared domain and the actual-variable
        // alias pattern is identical in every row. Otherwise the original
        // expansion remains authoritative.
        std::vector<std::string> representative_actuals;
        std::vector<std::size_t> alias_classes;
        std::vector<std::size_t> representative_slots;
        bool first_actual_row = true;
        const auto sameDomain = [](const Domain& left, const Domain& right) {
            return left.lo == right.lo && left.hi == right.hi
                && left.values == right.values && left.product_bound == right.product_bound;
        };
        for (const Elem& argument : group.children) {
            if (argument.name != "args") { continue; }
            Uir::Diagnostics probe;
            std::vector<std::string> actual;
            if (!expandedList(argument.text, actual, argument, probe)
                || actual.size() <= static_cast<std::size_t>(highest)) {
                return true;
            }
            std::vector<std::string> formal_actuals;
            formal_actuals.reserve(formal_slots.size());
            for (const std::size_t slot : formal_slots) {
                std::vector<std::string> resolved;
                Uir::Diagnostics slot_probe;
                if (!varList(actual[slot], resolved, argument, slot_probe)
                    || resolved.size() != 1) {
                    return true;
                }
                formal_actuals.push_back(resolved.front());
            }
            std::vector<std::size_t> row_classes;
            std::vector<std::size_t> row_representatives;
            std::unordered_map<std::string, std::size_t> class_by_variable;
            for (std::size_t i = 0; i < formal_actuals.size(); ++i) {
                const auto inserted = class_by_variable.emplace(
                    formal_actuals[i], class_by_variable.size());
                row_classes.push_back(inserted.first->second);
                if (inserted.second) { row_representatives.push_back(i); }
            }
            if (first_actual_row) {
                alias_classes = std::move(row_classes);
                representative_slots = std::move(row_representatives);
                representative_actuals = formal_actuals;
                first_actual_row = false;
            } else {
                if (row_classes != alias_classes) { return true; }
                for (std::size_t i = 0; i < formal_actuals.size(); ++i) {
                    const auto first_domain = findSource(representative_actuals[i]);
                    const auto current_domain = findSource(formal_actuals[i]);
                    if (first_domain == nullptr || current_domain == nullptr
                        || !sameDomain(*first_domain->domain, *current_domain->domain)) {
                        return true;
                    }
                }
            }
        }

        TupleTable rows{placeholders.size(), {}, {}};
        if (!tuples(table->textView(), rows, *table, diags)) {
            handled = true;
            return false;
        }
        // Preserve the existing empty-table fast path instead of building a
        // helper whose body immediately reduces to false/true.
        if (rows.empty()) { return true; }
        // Share large tables too: falling back expands this same relation at
        // every call. Domain/alias preflight and the factored operator-cost
        // comparison below decide whether sharing is valid and beneficial.

        std::vector<std::string> representative_scope;
        representative_scope.reserve(column_parameters.size());
        for (const std::size_t parameter : column_parameters) {
            representative_scope.push_back(representative_actuals[parameter]);
        }
        bool positive = supports;
        H::ExprPtr representative_relation = extensionRelation(
            representative_scope, rows, positive, pattern);
        if (!representative_relation) { return true; }

        // A relation simplified to a constant by the ordinary domain-aware
        // encoder has the same value for every preflighted row. Keep it as a
        // constant group result instead of wrapping it in an unnecessary
        // helper; all rows were fully validated above.
        if (representative_relation->kind == H::ExprKind::LIT_BOOL) {
            handled = true;
            if (!representative_relation->bool_value) {
                addFormula(H::mkBool(false, at(pattern)), pattern);
            }
            for (auto argument_node = group.children.begin();
                 argument_node != group.children.end();) {
                if (argument_node->name == "args") {
                    argument_node = group.children.erase(argument_node);
                } else {
                    ++argument_node;
                }
            }
            return true;
        }

        const Uir::SourceLoc definition_loc = at(pattern);
        std::vector<H::Binder> binders;
        binders.reserve(representative_slots.size());
        const std::string function_name = freshGroupFunctionName();
        std::unordered_set<std::string> bound_names;
        for (std::size_t i = 0; i < representative_slots.size(); ++i) {
            H::Binder binder;
            binder.name = freshGroupBinderName(function_name, i, bound_names);
            binder.sort = H::Sort::integer();
            bound_names.insert(binder.name);
            binders.push_back(std::move(binder));
        }

        std::unordered_map<std::string, std::string> bound_by_actual;
        for (std::size_t i = 0; i < representative_slots.size(); ++i) {
            bound_by_actual.emplace(representative_actuals[representative_slots[i]],
                                    binders[i].name);
        }
        H::ExprPtr body = bindRelation(representative_relation, bound_by_actual, false);
        if (!body) { return true; }
        const std::size_t body_operators = countOperators(body);
        // Each call replaces the whole body with one APPLY node. Require the
        // estimated shared operator count to be strictly lower; small groups
        // and trivial predicates keep the simpler established lowering.
        if (body_operators <= 1
            || argument_count <= body_operators / (body_operators - 1)) {
            return true;
        }

        H::FunDecl definition;
        definition.name = function_name;
        definition.params.assign(representative_slots.size(), H::Sort::integer());
        definition.result = H::Sort::boolean();
        definition.loc = definition_loc;
        definition.binders = std::move(binders);
        definition.body = std::move(body);
        definition.auxiliary = true;
        model_->funs.push_back(std::move(definition));

        handled = true;
        const bool compact_group = argument_count >= 256;
        std::vector<H::ExprPtr> batch;
        const auto flush = [&]() {
            if (batch.empty()) { return; }
            addFormula(conjunction(std::move(batch), group), group);
            batch.clear();
        };
        for (auto argument_node = group.children.begin(); argument_node != group.children.end();) {
            if (argument_node->name != "args") {
                ++argument_node;
                continue;
            }
            auto current = argument_node++;
            const Elem& argument = *current;
            std::vector<std::string> actual;
            if (!expandedList(argument.text, actual, argument, diags)) { return false; }
            std::vector<H::ExprPtr> call_arguments;
            call_arguments.reserve(representative_slots.size());
            for (const std::size_t slot : representative_slots) {
                std::vector<std::string> resolved;
                if (!varList(actual[formal_slots[slot]], resolved, argument, diags)
                    || resolved.size() != 1) {
                    return false;
                }
                call_arguments.push_back(var(resolved.front()));
            }
            H::ExprPtr call = H::mkApply(function_name, H::Sort::boolean(),
                                         std::move(call_arguments), definition_loc);
            if (compact_group) {
                batch.push_back(std::move(call));
                if (batch.size() >= 1024) { flush(); }
            } else {
                addFormula(std::move(call), pattern);
            }
            group.children.erase(current);
        }
        flush();
        return true;
    }

    static std::string smtSymbolKey(std::string_view name) {
        // SMT-LIB's quoted and bare spellings denote the same symbol when the
        // quoted body is itself a legal simple symbol. Generated helpers are
        // simple symbols, so compare against that canonical spelling.
        if (name.size() >= 2 && name.front() == '|' && name.back() == '|') {
            return std::string(name.substr(1, name.size() - 2));
        }
        return std::string(name);
    }

    static bool sameSmtSymbol(std::string_view left, std::string_view right) {
        return smtSymbolKey(left) == smtSymbolKey(right);
    }

    static bool isGroupGeneratedName(std::string_view name) {
        if (name.size() >= 2 && name.front() == '|' && name.back() == '|') {
            name = name.substr(1, name.size() - 2);
        }
        static constexpr std::string_view prefix = "__somt_xcsp_group_";
        return name.size() >= prefix.size() && name.substr(0, prefix.size()) == prefix;
    }

    void ensureGroupSymbolKeys() const {
        if (group_symbol_keys_ready_) { return; }
        for (const auto& declaration : domains_) {
            if (isGroupGeneratedName(declaration.first)) {
                group_symbol_keys_.insert(smtSymbolKey(declaration.first));
            }
        }
        for (const auto& array : arrays_) {
            if (isGroupGeneratedName(array.first)) {
                group_symbol_keys_.insert(smtSymbolKey(array.first));
            }
        }
        for (const H::VarDecl& declaration : model_->decls) {
            if (isGroupGeneratedName(declaration.name)) {
                group_symbol_keys_.insert(smtSymbolKey(declaration.name));
            }
        }
        for (const H::FunDecl& function : model_->funs) {
            if (isGroupGeneratedName(function.name)) {
                group_symbol_keys_.insert(smtSymbolKey(function.name));
            }
        }
        group_symbol_keys_ready_ = true;
    }

    void rememberGroupSymbol(std::string_view name) const {
        if (group_symbol_keys_ready_ && isGroupGeneratedName(name)) {
            group_symbol_keys_.insert(smtSymbolKey(name));
        }
    }

    std::string freshGroupFunctionName() {
        ensureGroupSymbolKeys();
        for (;;) {
            const std::string candidate = "__somt_xcsp_group_" + std::to_string(group_function_seq_++);
            const std::string key = smtSymbolKey(candidate);
            if (group_symbol_keys_.insert(key).second) { return candidate; }
        }
    }

    std::string freshGroupBinderName(const std::string& function_name,
                                     std::size_t index,
                                     const std::unordered_set<std::string>& local_names) const {
        ensureGroupSymbolKeys();
        const std::string base = function_name + "_p" + std::to_string(index);
        std::string candidate = base;
        std::size_t suffix = 0;
        for (;;) {
            bool used = group_symbol_keys_.find(smtSymbolKey(candidate))
                != group_symbol_keys_.end();
            if (!used) {
                for (const std::string& name : local_names) {
                    if (sameSmtSymbol(candidate, name)) { used = true; break; }
                }
            }
            if (!used) { return candidate; }
            candidate = base + "_" + std::to_string(++suffix);
        }
    }

    // A complete graph of clauses P(x) or P(y) means that at most one
    // vertex falsifies P. Compare actual HIR terms after closing definedness;
    // recognizing only source spelling would miss guards or capture globals.
    static H::ExprPtr symmetricUnaryDisjunction(const H::FunDecl& definition) {
        if (definition.binders.size() != 2 || !definition.body
            || definition.body->kind != H::ExprKind::OP
            || definition.body->op != H::Op::OR || definition.body->args.size() != 2) {
            return nullptr;
        }
        const auto matches = [&](const H::ExprPtr& left, const H::ExprPtr& right) {
            bool uses_parameter = false;
            std::set<std::pair<const H::Expr*, const H::Expr*>> seen;
            std::vector<std::pair<const H::Expr*, const H::Expr*>> pending{
                {left.get(), right.get()}};
            while (!pending.empty()) {
                const auto pair = pending.back(); pending.pop_back();
                const auto* a = pair.first; const auto* b = pair.second;
                if (!a || !b || a->kind != b->kind || !H::sameSort(a->sort, b->sort)
                    || a->op != b->op || a->bool_value != b->bool_value
                    || a->int_value != b->int_value || a->indices != b->indices
                    || !a->binders.empty() || !b->binders.empty()
                    || a->args.size() != b->args.size()) { return false; }
                if (!seen.emplace(a, b).second) { continue; }
                if (a->kind == H::ExprKind::BOUND_VAR) {
                    if (a->name != definition.binders[0].name
                        || b->name != definition.binders[1].name) { return false; }
                    uses_parameter = true;
                } else if (a->name != b->name) { return false; }
                for (std::size_t i = 0; i < a->args.size(); ++i) {
                    pending.emplace_back(a->args[i].get(), b->args[i].get());
                }
            }
            return uses_parameter;
        };
        const auto& args = definition.body->args;
        if (matches(args[0], args[1])) { return args[0]; }
        if (matches(args[1], args[0])) { return args[1]; }
        return nullptr;
    }

    /** Share indexed equality-element groups while retaining every variable
     *  in the list as a free global expression in the helper body. */
    bool sharedElementGroup(Elem& group, Elem& pattern, int highest,
                            std::size_t argument_count, bool& handled,
                            Uir::Diagnostics& diags) {
        handled = false;
        if (pattern.name != "element" || highest != 1 || argument_count < 2
            || !pattern.attrs.empty() || pattern.children.size() != 3) {
            return true;
        }
        const Elem* list = nullptr;
        const Elem* index = nullptr;
        const Elem* value = nullptr;
        for (const Elem& child : pattern.children) {
            if (child.name == "list" && !list) { list = &child; }
            else if (child.name == "index" && !index) { index = &child; }
            else if (child.name == "value" && !value) { value = &child; }
            else { return true; }
        }
        if (!list || !index || !value || !list->attrs.empty() || !value->attrs.empty()
            || !list->children.empty() || !index->children.empty() || !value->children.empty()
            || (index->attrs.size() != 0 &&
                (index->attrs.size() != 1 || index->attr("rank") != "any"))
            || trim(std::string(index->textView())) != "%0"
            || trim(std::string(value->textView())) != "%1"
            || list->textView().find('%') != std::string_view::npos) {
            return true;
        }

        std::vector<std::string> representative;
        std::vector<std::size_t> alias_classes;
        std::vector<std::size_t> representative_slots;
        bool have_representative = false;
        const auto sameDomain = [](const Domain& left, const Domain& right) {
            return left.lo == right.lo && left.hi == right.hi
                && left.values == right.values && left.product_bound == right.product_bound;
        };
        for (const Elem& argument : group.children) {
            if (argument.name != "args") { continue; }
            Uir::Diagnostics probe;
            std::vector<std::string> tokens;
            if (!expandedList(argument.text, tokens, argument, probe) || tokens.size() != 2) {
                return true;
            }
            std::vector<std::string> actual;
            for (const std::string& token : tokens) {
                std::vector<std::string> resolved;
                if (!varList(token, resolved, argument, probe) || resolved.size() != 1
                    || findSource(resolved.front()) == nullptr) {
                    return true;
                }
                actual.push_back(std::move(resolved.front()));
            }
            std::vector<std::size_t> row_classes;
            std::vector<std::size_t> row_representatives;
            std::unordered_map<std::string, std::size_t> class_by_name;
            for (std::size_t slot = 0; slot < actual.size(); ++slot) {
                const auto inserted = class_by_name.emplace(actual[slot], class_by_name.size());
                row_classes.push_back(inserted.first->second);
                if (inserted.second) { row_representatives.push_back(slot); }
            }
            if (!have_representative) {
                representative = std::move(actual);
                alias_classes = std::move(row_classes);
                representative_slots = std::move(row_representatives);
                have_representative = true;
            } else {
                if (row_classes != alias_classes) { return true; }
                for (std::size_t slot = 0; slot < actual.size(); ++slot) {
                    const auto first = findSource(representative[slot]);
                    const auto current = findSource(actual[slot]);
                    if (first == nullptr || current == nullptr
                        || !sameDomain(*first->domain, *current->domain)) {
                        return true;
                    }
                }
            }
        }
        if (!have_representative || representative_slots.empty()) { return true; }

        // Never bind the representative row's source names directly. A name
        // may also occur as a free list cell; fresh operands keep that global
        // occurrence distinct from the positional parameter being abstracted.
        const std::string prefix = freshGroupFunctionName();
        std::unordered_set<std::string> local_names;
        std::vector<std::string> synthetic_scope;
        std::vector<std::string> synthetic_arguments(2);
        for (std::size_t parameter = 0; parameter < representative_slots.size(); ++parameter) {
            const std::size_t slot = representative_slots[parameter];
            const std::string name = freshGroupBinderName(prefix, parameter, local_names);
            local_names.insert(name);
            const Domain& source = *sourceVariable(representative[slot]).domain;
            domains_.emplace(name, SourceVariable{
                std::make_shared<const Domain>(source), {}});
            for (std::size_t formal = 0; formal < synthetic_arguments.size(); ++formal) {
                if (alias_classes[formal] == parameter) { synthetic_arguments[formal] = name; }
            }
        }
        for (const std::string& name : synthetic_arguments) { synthetic_scope.push_back(name); }

        Elem instance = pattern;
        Uir::Diagnostics probe;
        H::ExprPtr body;
        const std::size_t constraint_count = model_->constraints.size();
        bool parsed = substituteFormals(instance, synthetic_arguments, highest);
        if (parsed) {
            compiling_shared_element_ = true;
            parsed = constraintLeaf(instance, probe)
                && model_->constraints.size() == constraint_count + 1;
            compiling_shared_element_ = false;
            if (parsed) { body = model_->constraints.back().formula; }
        }
        model_->constraints.resize(constraint_count);
        for (const std::string& name : local_names) {
            domains_.erase(name);
            variable_exprs_.erase(name);
        }
        if (!parsed || !body || probe.hasErrors()) { return true; }

        H::FunDecl definition;
        std::size_t body_operators = 0;
        if (!makeSharedExtensionDefinition(synthetic_scope, body, at(pattern),
                                           definition, body_operators, true)
            || body_operators <= 1
            || argument_count <= body_operators / (body_operators - 1)) {
            return true;
        }
        const std::string function_name = definition.name;
        model_->funs.push_back(std::move(definition));
        handled = true;
        std::vector<H::ExprPtr> calls;
        const auto flush = [&]() {
            if (calls.empty()) { return; }
            addFormula(conjunction(std::move(calls), group), group);
            calls.clear();
        };
        for (auto argument_node = group.children.begin(); argument_node != group.children.end();) {
            if (argument_node->name != "args") { ++argument_node; continue; }
            auto current = argument_node++;
            std::vector<std::string> tokens;
            std::vector<std::string> actual;
            Uir::Diagnostics row_probe;
            if (!expandedList(current->text, tokens, *current, row_probe)) {
                diags.merge(row_probe);
                return false;
            }
            for (const std::string& token : tokens) {
                std::vector<std::string> resolved;
                if (!varList(token, resolved, *current, diags) || resolved.size() != 1) {
                    return false;
                }
                actual.push_back(std::move(resolved.front()));
            }
            std::vector<std::string> packed_actuals;
            for (const std::size_t slot : representative_slots) { packed_actuals.push_back(actual[slot]); }
            if (!packFunctionCall(function_name, packed_actuals, pattern)) {
                std::vector<H::ExprPtr> actuals;
                actuals.reserve(representative_slots.size());
                for (const std::size_t slot : representative_slots) { actuals.push_back(var(actual[slot])); }
                calls.push_back(H::mkApply(function_name, H::Sort::boolean(),
                                           std::move(actuals), at(pattern)));
            }
            group.children.erase(current);
            if (calls.size() >= 1024) { flush(); }
        }
        flush();
        if (report_) {
            report_->addChoice({file_ + ":" + std::to_string(pattern.line), "element-group",
                "captured-list-indexed-equality-helper", Uir::Fidelity::exact(),
                "The list expression is parsed once and its declared variables remain free globals; "
                "only uniform-domain index/value operands become parameters"});
        }
        return true;
    }

    /** Share a fixed matrix lookup without specializing any operand domain or
     *  alias. Matrix element enumerates all cells independently of the domains
     *  of its row, column and value, so one definition covers every call. */
    bool sharedMatrixElementGroup(Elem& group, const Elem& pattern, int highest,
                                  std::size_t argument_count, bool& handled,
                                  Uir::Diagnostics& diags) {
        handled = false;
        if (pattern.name != "element" || highest != 2 || argument_count < 2
            || !pattern.attrs.empty() || pattern.children.size() != 3) {
            return true;
        }
        const Elem* matrix = pattern.child("matrix");
        const Elem* index = pattern.child("index");
        const Elem* value = pattern.child("value");
        if (!matrix || !index || !value || !index->attrs.empty() || !value->attrs.empty()
            || !matrix->children.empty() || !index->children.empty() || !value->children.empty()
            || words(std::string(index->textView())) != std::vector<std::string>{"%0", "%1"}
            || trim(std::string(value->textView())) != "%2"
            || matrix->textView().find('%') != std::string_view::npos) {
            return true;
        }
        for (const auto& attribute : matrix->attrs) {
            if (attribute.first != "startRowIndex" && attribute.first != "startColIndex") {
                return true;
            }
        }
        const auto operands = [&](const Elem& argument, std::vector<std::string>& actual,
                                  Uir::Diagnostics& diagnostics) {
            std::vector<std::string> tokens;
            if (!expandedList(argument.text, tokens, argument, diagnostics)
                || tokens.size() != 3) { return false; }
            for (const auto& token : tokens) {
                std::vector<std::string> names;
                if (!varList(token, names, argument, diagnostics) || names.size() != 1
                    || findSource(names.front()) == nullptr) { return false; }
                actual.push_back(std::move(names.front()));
            }
            return true;
        };
        for (const auto& argument : group.children) {
            if (argument.name != "args") { continue; }
            std::vector<std::string> actual;
            Uir::Diagnostics probe;
            if (!operands(argument, actual, probe)) { return true; }
        }

        // Fresh, independent operands prevent a representative call from
        // capturing a matrix cell or imposing its particular alias pattern.
        const std::string prefix = freshGroupFunctionName();
        std::unordered_set<std::string> local_names;
        std::vector<std::string> synthetic;
        for (std::size_t slot = 0; slot < 3; ++slot) {
            const std::string name = freshGroupBinderName(prefix, slot, local_names);
            local_names.insert(name);
            Domain domain;
            domain.lo = std::numeric_limits<long long>::min();
            domain.hi = std::numeric_limits<long long>::max();
            domains_.emplace(name, SourceVariable{
                std::make_shared<const Domain>(std::move(domain)), {}});
            synthetic.push_back(name);
        }
        Elem instance = pattern;
        Uir::Diagnostics probe;
        H::ExprPtr body;
        const std::size_t constraint_count = model_->constraints.size();
        const bool parsed = substituteFormals(instance, synthetic, highest)
            && elementConstraint(instance, probe)
            && model_->constraints.size() == constraint_count + 1;
        if (parsed) { body = model_->constraints.back().formula; }
        model_->constraints.resize(constraint_count);
        for (const auto& name : synthetic) {
            domains_.erase(name);
            variable_exprs_.erase(name);
        }
        if (!parsed || !body || probe.hasErrors()) { return true; }
        H::FunDecl definition;
        std::size_t body_operators = 0;
        if (!makeSharedExtensionDefinition(synthetic, body, at(pattern),
                                           definition, body_operators, true)
            || body_operators <= 1
            || argument_count <= body_operators / (body_operators - 1)) {
            return true;
        }
        const std::string function_name = definition.name;
        model_->funs.push_back(std::move(definition));
        handled = true;
        std::vector<H::ExprPtr> calls;
        const auto flush = [&]() {
            if (calls.empty()) { return; }
            addFormula(conjunction(std::move(calls), group), group);
            calls.clear();
        };
        for (auto it = group.children.begin(); it != group.children.end();) {
            if (it->name != "args") { ++it; continue; }
            auto current = it++;
            std::vector<std::string> actual;
            if (!operands(*current, actual, diags)) { return false; }
            if (!packFunctionCall(function_name, actual, pattern)) {
                std::vector<H::ExprPtr> arguments;
                for (const auto& name : actual) { arguments.push_back(var(name)); }
                calls.push_back(H::mkApply(function_name, H::Sort::boolean(),
                                           std::move(arguments), at(pattern)));
            }
            group.children.erase(current);
            if (calls.size() >= 1024) { flush(); }
        }
        flush();
        if (report_) {
            report_->addChoice({file_ + ":" + std::to_string(pattern.line), "element-group",
                "captured-matrix-indexed-equality-helper", Uir::Fidelity::exact(),
                "The fixed matrix keeps its free model variables; independent row, column "
                "and value parameters preserve each call's domains and aliases"});
        }
        return true;
    }

    /** Abstract total variable operands after specializing literals. Independent
     *  synthetic variables prevent actual aliases from folding a shared body. */
    /** Factor a repeated regular-group automaton into one Boolean function.
     *  The function body computes layered state reachability directly from its
     *  word parameters. It uses no existential witness state shared between
     *  calls, so rows may use unrelated or aliased source variables safely.
     */
    bool sharedRegularGroup(Elem& group, const Elem& pattern, int highest,
                            std::size_t argument_count, bool& handled,
                            Uir::Diagnostics& diags) {
        handled = false;
        if (pattern.name != "regular" || highest != -1 || argument_count < 2
            || !pattern.attrs.empty() || pattern.children.size() != 4) {
            return true;
        }
        const Elem* list = nullptr;
        const Elem* transitions_node = nullptr;
        const Elem* start_node = nullptr;
        const Elem* final_node = nullptr;
        for (const Elem& child : pattern.children) {
            if (child.name == "list" && !list) { list = &child; }
            else if (child.name == "transitions" && !transitions_node) {
                transitions_node = &child;
            } else if (child.name == "start" && !start_node) { start_node = &child; }
            else if (child.name == "final" && !final_node) { final_node = &child; }
            else { return true; }
        }
        if (!list || !transitions_node || !start_node || !final_node
            || !list->attrs.empty() || !transitions_node->attrs.empty()
            || !start_node->attrs.empty() || !final_node->attrs.empty()
            || !list->children.empty() || !transitions_node->children.empty()
            || !start_node->children.empty() || !final_node->children.empty()
            || trim(std::string(list->textView())) != "%..."
            || transitions_node->textView().find('%') != std::string_view::npos
            || start_node->textView().find('%') != std::string_view::npos
            || final_node->textView().find('%') != std::string_view::npos) {
            return true;
        }

        std::vector<std::vector<std::string>> rows;
        rows.reserve(argument_count);
        std::size_t word_size = 0;
        for (const Elem& argument : group.children) {
            if (argument.name != "args") { continue; }
            Uir::Diagnostics probe;
            std::vector<std::string> tokens;
            if (!expandedList(argument.text, tokens, argument, probe) || tokens.empty()) {
                return true;
            }
            std::vector<std::string> word;
            for (const std::string& token : tokens) {
                std::vector<std::string> resolved;
                if (!varList(token, resolved, argument, probe) || resolved.size() != 1
                    || findSource(resolved.front()) == nullptr) {
                    return true;
                }
                word.push_back(std::move(resolved.front()));
            }
            if (!word_size) { word_size = word.size(); }
            else if (word.size() != word_size) { return true; }
            rows.push_back(std::move(word));
        }
        if (rows.size() != argument_count || !word_size) { return true; }

        std::vector<Transition> edges;
        Uir::Diagnostics probe;
        if (!transitions(*transitions_node, edges, probe)) { return true; }
        std::set<std::string> state_set;
        for (const Transition& edge : edges) {
            state_set.insert(edge.source);
            state_set.insert(edge.target);
        }
        const std::vector<std::string> starts = words(std::string(start_node->textView()));
        std::vector<std::string> finals = words(std::string(final_node->textView()));
        if (starts.size() != 1 || finals.empty()
            || state_set.find(starts.front()) == state_set.end()) {
            return true;
        }
        std::set<std::string> unique_finals;
        for (const std::string& final : finals) {
            if (state_set.find(final) == state_set.end()) { return true; }
            unique_finals.insert(final);
        }
        finals.assign(unique_finals.begin(), unique_finals.end());
        // Match the established frontend's reachability-variable guard. If
        // this candidate cannot fit the cap, the ordinary lowering remains
        // responsible for its existing diagnostic.
        if (state_set.size() > 250000 / word_size) { return true; }

        const std::vector<std::string> states(state_set.begin(), state_set.end());
        std::unordered_map<std::string, std::size_t> state_index;
        state_index.reserve(states.size());
        for (std::size_t i = 0; i < states.size(); ++i) { state_index.emplace(states[i], i); }
        struct IncomingEdge { std::size_t source; long long label; };
        std::vector<std::vector<IncomingEdge>> incoming(states.size());
        std::vector<std::set<std::pair<std::size_t, long long>>> seen_incoming(states.size());
        for (const Transition& edge : edges) {
            const std::size_t source = state_index.at(edge.source);
            const std::size_t target = state_index.at(edge.target);
            // Repeated transitions have no effect on the recognized language.
            if (seen_incoming[target].emplace(source, edge.value).second) {
                incoming[target].push_back({source, edge.value});
            }
        }

        const std::string function_name = freshGroupFunctionName();
        std::unordered_set<std::string> bound_names;
        std::vector<H::Binder> binders;
        std::vector<H::ExprPtr> word_parameters;
        binders.reserve(word_size);
        word_parameters.reserve(word_size);
        for (std::size_t i = 0; i < word_size; ++i) {
            H::Binder binder;
            binder.name = freshGroupBinderName(function_name, i, bound_names);
            binder.sort = H::Sort::integer();
            bound_names.insert(binder.name);
            word_parameters.push_back(H::mkBoundVar(binder.name, binder.sort, at(pattern)));
            binders.push_back(std::move(binder));
        }

        std::vector<H::ExprPtr> reach(states.size(), H::mkBool(false, at(pattern)));
        reach[state_index.at(starts.front())] = H::mkBool(true, at(pattern));
        for (std::size_t position = 0; position < word_size; ++position) {
            std::vector<H::ExprPtr> next(states.size());
            std::unordered_map<long long, H::ExprPtr> label_tests;
            for (std::size_t target = 0; target < states.size(); ++target) {
                std::vector<H::ExprPtr> alternatives;
                alternatives.reserve(incoming[target].size());
                for (const IncomingEdge& edge : incoming[target]) {
                    const H::ExprPtr& previous = reach[edge.source];
                    if (previous->kind == H::ExprKind::LIT_BOOL && !previous->bool_value) {
                        continue;
                    }
                    auto label = label_tests.find(edge.label);
                    if (label == label_tests.end()) {
                        label = label_tests.emplace(edge.label, H::mkOp(
                            H::Op::EQ, {word_parameters[position], num(edge.label)}, at(pattern))).first;
                    }
                    alternatives.push_back(
                        previous->kind == H::ExprKind::LIT_BOOL && previous->bool_value
                            ? label->second
                            : conjunction({previous, label->second}, pattern));
                }
                next[target] = disjunction(std::move(alternatives), pattern);
            }
            reach = std::move(next);
        }
        std::vector<H::ExprPtr> accepting;
        accepting.reserve(finals.size());
        for (const std::string& final : finals) {
            accepting.push_back(reach[state_index.at(final)]);
        }
        H::ExprPtr body = disjunction(std::move(accepting), pattern);
        const std::size_t body_operators = countOperators(body);
        if (body_operators <= 1
            || argument_count <= body_operators / (body_operators - 1)) {
            return true;
        }

        H::FunDecl definition;
        definition.name = function_name;
        definition.params.assign(word_size, H::Sort::integer());
        definition.result = H::Sort::boolean();
        definition.loc = at(pattern);
        definition.binders = std::move(binders);
        definition.body = std::move(body);
        definition.auxiliary = true;
        model_->funs.push_back(std::move(definition));
        handled = true;
        std::vector<H::ExprPtr> calls;
        calls.reserve(rows.size());
        for (const auto& row : rows) {
            std::vector<H::ExprPtr> actuals;
            actuals.reserve(row.size());
            for (const std::string& name : row) { actuals.push_back(var(name)); }
            calls.push_back(H::mkApply(function_name, H::Sort::boolean(),
                                       std::move(actuals), at(pattern)));
        }
        addFormula(conjunction(std::move(calls), group), group);
        for (auto argument_node = group.children.begin(); argument_node != group.children.end();) {
            if (argument_node->name == "args") { argument_node = group.children.erase(argument_node); }
            else { ++argument_node; }
        }
        if (report_) {
            report_->addChoice({file_ + ":" + std::to_string(pattern.line), "regular-group",
                "shared-dag-reachability-function", Uir::Fidelity::exact(),
                "The NFA reachability recurrence is compiled once as a pure word predicate; "
                "each row has its own actual word and no row shares witness state variables"});
        }
        return true;
    }

    bool sharedIntensionGroup(Elem& group, const Elem& pattern, int highest,
                               bool& handled, Uir::Diagnostics& diags) {
        handled = false;
        if (pattern.name != "intension" || highest < 0 || !pattern.attrs.empty()
            || !pattern.children.empty() || pattern.text.find("%...") != std::string::npos) {
            return true;
        }
        std::set<std::size_t> used_slots;
        for (std::size_t pos = 0; pos < pattern.text.size(); ++pos) {
            if (pattern.text[pos] != '%') { continue; }
            const std::size_t begin = ++pos;
            std::size_t slot = 0;
            while (pos < pattern.text.size()
                   && std::isdigit(static_cast<unsigned char>(pattern.text[pos]))) {
                const unsigned digit = pattern.text[pos] - '0';
                if (slot > (std::numeric_limits<std::size_t>::max() - digit) / 10) { return true; }
                slot = slot * 10 + digit; ++pos;
            }
            if (pos == begin || pattern.text.substr(begin, pos - begin)
                                != std::to_string(slot)) { return true; }
            used_slots.insert(slot); --pos;
        }
        if (used_slots.empty()) { return true; }
        struct Specialization {
            std::size_t count = 0;
            std::vector<std::string> representative;
            std::vector<std::size_t> parameters;
            H::FunDecl definition;
            bool pair_graph = true;
            bool cardinality = false;
            std::map<std::string, std::size_t> vertices;
            std::vector<std::string> vertex_names;
            std::vector<std::uint64_t> adjacency;

            void addPair(const std::vector<std::string>& arguments,
                         const std::vector<std::size_t>& slots) {
                if (!pair_graph) { return; }
                const auto abandon = [&]() {
                    pair_graph = false; vertices.clear(); vertex_names.clear(); adjacency.clear();
                };
                if (slots.size() != 2 || arguments[slots[0]] == arguments[slots[1]]) {
                    abandon(); return;
                }
                std::size_t endpoints[2];
                for (std::size_t i = 0; i < 2; ++i) {
                    const std::string& name = arguments[slots[i]];
                    auto found = vertices.find(name);
                    if (found == vertices.end()) {
                        // One machine word per vertex bounds recognizer memory;
                        // larger scopes retain the ordinary exact call encoding.
                        if (vertices.size() == 64) { abandon(); return; }
                        endpoints[i] = vertices.size();
                        vertices.emplace(name, endpoints[i]);
                        vertex_names.push_back(name); adjacency.push_back(0);
                    } else { endpoints[i] = found->second; }
                }
                adjacency[endpoints[0]] |= std::uint64_t{1} << endpoints[1];
                adjacency[endpoints[1]] |= std::uint64_t{1} << endpoints[0];
            }

            bool completePairGraph() const {
                const std::size_t n = vertices.size();
                if (!pair_graph || n < 2 || count <= 2 * n + 2) { return false; }
                const std::uint64_t all = n == 64 ? ~std::uint64_t{0}
                                                   : (std::uint64_t{1} << n) - 1;
                for (std::size_t i = 0; i < n; ++i) {
                    if (adjacency[i] != (all ^ (std::uint64_t{1} << i))) { return false; }
                }
                return true;
            }
        };
        std::map<std::string, Specialization> specializations;
        const auto classify = [&](const std::vector<std::string>& arguments,
                                   std::string& key, std::vector<std::size_t>& parameters) {
            if (arguments.size() <= static_cast<std::size_t>(highest)) { return false; }
            for (const std::size_t slot : used_slots) {
                long long literal = 0;
                if (toInt(arguments[slot], literal)) {
                    key += "I" + std::to_string(literal) + ";";
                } else {
                    const auto found = findSource(arguments[slot]);
                    // Compound actuals can be partial; ordinary substitution
                    // preserves their non-eager Boolean/conditional evaluation.
                    if (found == nullptr) { return false; }
                    const Domain& d = *found->domain;
                    key += !d.sparse() && d.lo == 0 && d.hi == 1 ? "B;" : "V;";
                    parameters.push_back(slot);
                }
            }
            return true;
        };
        for (const Elem& argument : group.children) {
            if (argument.name != "args") { continue; }
            Uir::Diagnostics probe;
            std::vector<std::string> arguments;
            std::string key;
            std::vector<std::size_t> parameters;
            if (!expandedList(argument.text, arguments, argument, probe)
                || !classify(arguments, key, parameters)) { return true; }
            auto& specialization = specializations[key];
            specialization.addPair(arguments, parameters);
            if (specialization.count++ == 0) {
                specialization.representative = std::move(arguments);
                specialization.parameters = std::move(parameters);
            }
        }
        for (const auto& entry : specializations) {
            if (entry.second.count < 2 || entry.second.parameters.empty()) { return true; }
        }
        // Install nothing until all bodies pass the ordinary expression parser
        // and retain the exact root-definedness formula, including zero divisors.
        for (auto& entry : specializations) {
            Specialization& specialization = entry.second;
            std::vector<std::string> arguments = specialization.representative;
            std::vector<std::string> synthetic;
            std::unordered_set<std::string> local_names;
            const std::string prefix = freshGroupFunctionName();
            for (const std::size_t slot : specialization.parameters) {
                const std::string name = freshGroupBinderName(prefix, slot, local_names);
                local_names.insert(name);
                const Domain& original = *sourceVariable(arguments[slot]).domain;
                Domain domain;
                if (!original.sparse() && original.lo == 0 && original.hi == 1) {
                    domain.lo = 0; domain.hi = 1;
                } else {
                    domain.lo = std::numeric_limits<long long>::min();
                    domain.hi = std::numeric_limits<long long>::max();
                }
                domains_.emplace(name, SourceVariable{std::make_shared<const Domain>(std::move(domain)), {}});
                synthetic.push_back(name); arguments[slot] = name;
            }
            Elem instance = pattern;
            Uir::Diagnostics probe;
            H::ExprPtr expression;
            if (substituteFormals(instance, arguments, highest)) {
                std::size_t position = 0;
                expression = intension(instance.text, position, instance, probe, 0);
                while (position < instance.text.size()
                       && std::isspace(static_cast<unsigned char>(instance.text[position]))) { ++position; }
                if (position != instance.text.size()) { expression.reset(); }
                if (expression && expression->kind == H::ExprKind::IDENT
                    && expression->sort.kind == H::SortKind::INT) {
                    const auto found = findSource(expression->name);
                    if (found != nullptr && !found->domain->sparse()
                        && found->domain->lo == 0 && found->domain->hi == 1) {
                        expression = relational_.value(H::Op::EQ,
                                                       {expression, num(1)}, at(pattern));
                    }
                }
            }
            bool compiled = false;
            std::size_t operators = 0;
            if (expression && expression->sort.kind == H::SortKind::BOOL && !probe.hasErrors()) {
                compiled = makeSharedExtensionDefinition(synthetic, relational_.require(expression),
                    at(pattern), specialization.definition, operators, true);
            }
            for (const std::string& name : synthetic) {
                domains_.erase(name); variable_exprs_.erase(name);
            }
            if (!compiled || (operators <= 1 && model_->scalar_var_ranges.empty())
                || (operators > 1
                    && specialization.count <= operators / (operators - 1))) { return true; }
        }
        std::size_t cardinality_groups = 0;
        for (auto& entry : specializations) {
            Specialization& specialization = entry.second;
            if (specialization.completePairGraph()) {
                H::ExprPtr unary = symmetricUnaryDisjunction(specialization.definition);
                if (unary) {
                    specialization.cardinality = true; ++cardinality_groups;
                    specialization.definition.body = std::move(unary);
                    specialization.definition.params.resize(1);
                    specialization.definition.binders.resize(1);
                }
            }
            model_->funs.push_back(specialization.definition);
        }
        handled = true;
        for (const auto& entry : specializations) {
            const Specialization& specialization = entry.second;
            if (!specialization.cardinality) { continue; }
            std::vector<H::ExprPtr> indicators;
            for (const std::string& name : specialization.vertex_names) {
                H::ExprPtr predicate = H::mkApply(specialization.definition.name,
                    H::Sort::boolean(), {var(name)}, at(pattern));
                indicators.push_back(H::mkOp(H::Op::ITE,
                    {std::move(predicate), num(0), num(1)}, at(pattern)));
            }
            addFormula(H::mkOp(H::Op::LE,
                {H::mkOp(H::Op::ADD, std::move(indicators), at(pattern)), num(1)},
                at(pattern)), group);
        }
        std::vector<H::ExprPtr> calls;
        const auto flush = [&]() {
            if (calls.empty()) { return; }
            addFormula(conjunction(std::move(calls), group), group); calls.clear();
        };
        for (auto it = group.children.begin(); it != group.children.end();) {
            if (it->name != "args") { ++it; continue; }
            auto current = it++;
            std::vector<std::string> arguments;
            std::string key;
            std::vector<std::size_t> parameters;
            if (!expandedList(current->text, arguments, *current, diags)
                || !classify(arguments, key, parameters)) { return false; }
            const Specialization& specialization = specializations.at(key);
            if (specialization.cardinality) {
                group.children.erase(current); continue;
            }
            std::vector<std::string> packed_actuals;
            for (const std::size_t slot : parameters) { packed_actuals.push_back(arguments[slot]); }
            if (!packFunctionCall(specialization.definition.name, packed_actuals, pattern)) {
                std::vector<H::ExprPtr> actuals;
                actuals.reserve(parameters.size());
                for (const std::size_t slot : parameters) { actuals.push_back(var(arguments[slot])); }
                calls.push_back(H::mkApply(specialization.definition.name, H::Sort::boolean(),
                                           std::move(actuals), at(pattern)));
            }
            group.children.erase(current);
            if (calls.size() >= 1024) { flush(); }
        }
        flush();
        if (report_) {
            report_->addChoice({file_ + ":" + std::to_string(pattern.line), "intension-group",
                "literal-specialized-shared-function", Uir::Fidelity::exact(),
                "Total variable operands become independent parameters; literal and "
                "Boolean-domain specializations preserve root definedness and aliases"});
            if (cardinality_groups) {
                report_->addChoice({file_ + ":" + std::to_string(pattern.line), "intension-group",
                    "complete-pairwise-or-cardinality", Uir::Fidelity::exact(),
                    "Verified full pair coverage and alpha-equal unary predicates; "
                    "every pair satisfies P(x) or P(y) iff at most one vertex falsifies P"});
            }
        }
        return true;
    }

    struct GroupWork {
        Elem* group = nullptr;
        std::list<Elem>::iterator pattern, next, current;
        int highest = -1;
        bool compact = false;
        bool awaiting_instance = false;
        std::size_t begin = 0;
        std::vector<H::ExprPtr> positive, negative;
        std::unique_ptr<Elem> instance;
    };

    bool prepareGroup(Elem& group, GroupWork& work, bool& complete,
                      Uir::Diagnostics& diags) {
        auto pattern = group.children.end();
        std::size_t argument_count = 0;
        for (auto child = group.children.begin(); child != group.children.end(); ++child) {
            if (child->name == "args") { ++argument_count; }
            else if (pattern == group.children.end()) { pattern = child; }
            else {
                diags.error(ErrorCode::E_PARSE,
                            "a group contains more than one constraint template", at(group));
                return false;
            }
        }
        if (pattern == group.children.end() || argument_count < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "a group needs one template and at least two <args> elements",
                        at(group));
            return false;
        }
        // The template is intentionally retained until every <args> row has
        // been expanded. Erasing argument rows cannot invalidate this list
        // iterator, and releases their potentially large text immediately.
        const int highest = highestFormal(*pattern);
        bool shared_extension = false;
        if (!sharedExtensionGroup(group, *pattern, highest, argument_count,
                                  shared_extension, diags)) {
            return false;
        }
        if (shared_extension) { complete = true; return true; }
        bool shared_element = false;
        if (!sharedElementGroup(group, *pattern, highest, argument_count,
                                shared_element, diags)) {
            return false;
        }
        if (shared_element) { complete = true; return true; }
        bool shared_matrix_element = false;
        if (!sharedMatrixElementGroup(group, *pattern, highest, argument_count,
                                      shared_matrix_element, diags)) {
            return false;
        }
        if (shared_matrix_element) { complete = true; return true; }
        bool shared_regular = false;
        if (!sharedRegularGroup(group, *pattern, highest, argument_count,
                                shared_regular, diags)) {
            return false;
        }
        if (shared_regular) { complete = true; return true; }
        bool shared_intension = false;
        if (!sharedIntensionGroup(group, *pattern, highest, shared_intension, diags)) {
            return false;
        }
        if (shared_intension) { complete = true; return true; }
        work.group = &group;
        work.pattern = pattern;
        work.next = group.children.begin();
        work.highest = highest;
        work.compact = argument_count >= 256;
        return true;
    }

    void flushGroup(GroupWork& work) {
        if (!work.positive.empty()) {
            addFormula(conjunction(std::move(work.positive), *work.group), *work.group);
            work.positive.clear();
        }
        if (!work.negative.empty()) {
            addFormula(H::mkOp(H::Op::NOT,
                               {disjunction(std::move(work.negative), *work.group)},
                               at(*work.group)), *work.group);
            work.negative.clear();
        }
    }

    void finishGroupInstance(GroupWork& work) {
        work.group->children.erase(work.current);
        work.instance.reset();
        work.awaiting_instance = false;
        if (!work.compact) { return; }
        std::size_t retained = work.begin;
        for (std::size_t i = work.begin; i < model_->constraints.size(); ++i) {
            H::Constraint& constraint = model_->constraints[i];
            // Metadata-bearing constraints retain their individual identity.
            if (constraint.soft || !constraint.group.empty()) {
                if (retained != i) { model_->constraints[retained] = std::move(constraint); }
                ++retained;
                continue;
            }
            const auto& formula = constraint.formula;
            if (formula->kind == H::ExprKind::OP && formula->op == H::Op::NOT
                && formula->args.size() == 1) {
                work.negative.push_back(formula->args.front());
            } else { work.positive.push_back(formula); }
        }
        model_->constraints.resize(retained);
        if (work.positive.size() + work.negative.size() >= 1024) { flushGroup(work); }
    }

    bool slideConstraints(const Elem& slide, Uir::Diagnostics& diags) {
        const Elem* list = nullptr;
        const Elem* pattern = nullptr;
        for (const Elem& child : slide.children) {
            if (child.name == "list" && !list) { list = &child; }
            else if (!pattern) { pattern = &child; }
            else {
                diags.error(ErrorCode::E_PARSE,
                            "slide requires one list and one constraint template", at(slide));
                return false;
            }
        }
        if (!list || !pattern || (pattern->name != "intension"
                                  && pattern->name != "extension")) {
            diags.error(ErrorCode::E_PARSE,
                        "XCSP3-core slide requires one <list> followed by an intension or "
                        "extension template", at(slide));
            return false;
        }
        std::vector<std::string> scope;
        if (!varList(list->text, scope, *list, diags)) { return false; }
        if (scope.size() < 2) {
            diags.error(ErrorCode::E_PARSE,
                        "slide requires at least two variables", at(slide));
            return false;
        }
        const int highest = highestFormal(*pattern);
        if (highest < 0) {
            diags.error(ErrorCode::E_PARSE,
                        "slide template has no formal parameters", at(*pattern));
            return false;
        }
        const std::size_t arity = static_cast<std::size_t>(highest + 1);
        if (arity > scope.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "slide template arity exceeds its variable list", at(slide));
            return false;
        }
        long long offset = 1;
        if (!list->attr("offset").empty()
            && (!toInt(list->attr("offset"), offset) || offset <= 0)) {
            diags.error(ErrorCode::E_PARSE,
                        "slide offset must be a positive integer", at(*list));
            return false;
        }
        const std::string circular_text = slide.attr("circular", "false");
        if (circular_text != "true" && circular_text != "false") {
            diags.error(ErrorCode::E_PARSE,
                        "slide circular must be true or false", at(slide));
            return false;
        }
        const bool circular = circular_text == "true";
        if (circular && offset != 1) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "XCSP3 defines circular slide only with the default offset 1",
                        at(slide));
            return false;
        }
        const std::size_t last_start = circular
            ? scope.size() - arity + 1
            : scope.size() - arity;
        std::size_t instances = 0;
        for (std::size_t start = 0; start <= last_start;) {
            std::vector<std::string> arguments;
            for (std::size_t parameter = 0; parameter < arity; ++parameter) {
                arguments.push_back(scope[(start + parameter) % scope.size()]);
            }
            Elem instance = *pattern;
            if (!substituteFormals(instance, arguments, highest)) {
                diags.error(ErrorCode::E_PARSE,
                            "slide template contains an unsubstituted formal parameter",
                            at(*pattern));
                return false;
            }
            if (!constraintLeaf(instance, diags)) { return false; }
            ++instances;
            const std::size_t step = static_cast<std::size_t>(offset);
            if (step > last_start - start) { break; }
            start += step;
        }
        if (report_) {
            report_->addChoice(
                {file_ + ":" + std::to_string(slide.line), "slide",
                 "finite-template-expansion", Uir::Fidelity::exact(),
                 "expanded " + std::to_string(instances)
                     + " windows using the declared arity, offset and circularity"});
        }
        return true;
    }

    // ---- constraints -----------------------------------------------------

    bool constraintLeaf(Elem& e, Uir::Diagnostics& diags) {
        if (e.name == "intension") {
            std::size_t i = 0;
            H::ExprPtr f = intension(e.text, i, e, diags, 0);
            if (!f) { return false; }
            while (i < e.text.size()
                   && std::isspace(static_cast<unsigned char>(e.text[i]))) { ++i; }
            if (i != e.text.size()) {
                diags.error(ErrorCode::E_PARSE,
                            "trailing text in the intension expression", at(e));
                return false;
            }
            H::Constraint c;
            c.loc = at(e);
            if (f->sort.kind == H::SortKind::INT && f->kind == H::ExprKind::IDENT) {
                const auto domain = findSource(f->name);
                if (domain == nullptr || domain->domain->sparse()
                    || domain->domain->lo != 0 || domain->domain->hi != 1) {
                    diags.error(ErrorCode::E_TYPE,
                                "a root intension 01Var must have domain exactly 0..1",
                                at(e));
                    return false;
                }
                f = relational_.value(H::Op::EQ, {f, num(1)}, at(e));
            }
            c.formula = relational_.require(f);
            model_->constraints.push_back(c);
        } else if (e.name == "extension") {
            if (!extension(e, diags)) { return false; }
        } else if (e.name == "regular" || e.name == "mdd") {
            if (!languageConstraint(e, e.name == "mdd", diags)) { return false; }
        } else if (e.name == "allDifferent") {
            if (!allDifferentConstraint(e, diags)) { return false; }
        } else if (e.name == "allEqual") {
            if (!allEqual(e, diags)) { return false; }
        } else if (e.name == "ordered") {
            if (!orderedConstraint(e, diags)) { return false; }
        } else if (e.name == "precedence") {
            if (!precedenceConstraint(e, diags)) { return false; }
        } else if (e.name == "lex") {
            if (!lexConstraint(e, diags)) { return false; }
        } else if (e.name == "sum") {
            if (!sumConstraint(e, diags)) { return false; }
        } else if (e.name == "count") {
            if (!countConstraint(e, diags)) { return false; }
        } else if (e.name == "nValues") {
            if (!nValuesConstraint(e, diags)) { return false; }
        } else if (e.name == "cardinality") {
            if (!cardinalityConstraint(e, diags)) { return false; }
        } else if (e.name == "minimum" || e.name == "maximum") {
            if (!extremumConstraint(e, e.name == "minimum", diags)) { return false; }
        } else if (e.name == "element") {
            if (!elementConstraint(e, diags)) { return false; }
        } else if (e.name == "channel") {
            if (!channelConstraint(e, diags)) { return false; }
        } else if (e.name == "noOverlap") {
            if (!noOverlapConstraint(e, diags)) { return false; }
        } else if (e.name == "cumulative") {
            if (!cumulativeConstraint(e, diags)) { return false; }
        } else if (e.name == "binPacking") {
            if (!binPackingConstraint(e, diags)) { return false; }
        } else if (e.name == "knapsack") {
            if (!knapsackConstraint(e, diags)) { return false; }
        } else if (e.name == "flow") {
            if (!flowConstraint(e, diags)) { return false; }
        } else if (e.name == "instantiation") {
            if (!instantiationConstraint(e, diags)) { return false; }
        } else if (e.name == "clause") {
            if (!clauseConstraint(e, diags)) { return false; }
        } else if (e.name == "circuit") {
            if (!circuitConstraint(e, diags)) { return false; }
        } else {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "the constraint '" + e.name + "' is not implemented; skipping "
                        "it would drop a constraint and weaken the model", at(e));
            return false;
        }
        return true;
    }

    bool constraints(Elem& cons, Uir::Diagnostics& diags) {
        struct Frame {
            Elem* node;
            bool group = false;
            bool initialized = false;
            bool awaiting_child = false;
            std::list<Elem>::iterator next, current;
            GroupWork work;
            explicit Frame(Elem& element, bool is_group = false)
                : node(&element), group(is_group), next(element.children.begin()) {}
        };
        std::list<Frame> pending;
        pending.emplace_back(cons);
        while (!pending.empty()) {
            auto& frame = pending.back();
            if (frame.group) {
                auto& work = frame.work;
                if (!frame.initialized) {
                    bool complete = false;
                    if (!prepareGroup(*frame.node, work, complete, diags)) { return false; }
                    if (complete) { pending.pop_back(); continue; }
                    frame.initialized = true;
                }
                if (work.awaiting_instance) { finishGroupInstance(work); }
                if (work.next == work.pattern) { ++work.next; }
                if (work.next == work.group->children.end()) {
                    flushGroup(work);
                    pending.pop_back();
                    continue;
                }
                work.current = work.next++;
                const Elem& argument = *work.current;
                std::vector<std::string> arguments;
                if (!expandedList(argument.text, arguments, argument, diags)) { return false; }
                if (work.highest >= 0 && arguments.size() <= static_cast<std::size_t>(work.highest)) {
                    diags.error(ErrorCode::E_PARSE,
                                "group template refers to %" + std::to_string(work.highest)
                                    + " but an <args> element has only "
                                    + std::to_string(arguments.size()) + " argument(s)", at(argument));
                    return false;
                }
                Elem instance = *work.pattern;
                if (!substituteFormals(instance, arguments, work.highest)) {
                    diags.error(ErrorCode::E_PARSE,
                                "group template contains an unsubstituted formal parameter", at(argument));
                    return false;
                }
                work.instance = std::make_unique<Elem>();
                work.instance->name = "constraints";
                work.instance->line = instance.line;
                work.instance->children.push_back(std::move(instance));
                work.begin = model_->constraints.size();
                work.awaiting_instance = true;
                // Resume this group after exactly one instance. This keeps the
                // old per-row release and 1024-formula batching even for nested groups.
                pending.emplace_back(*work.instance);
                continue;
            }
            if (frame.awaiting_child) {
                frame.node->children.erase(frame.current);
                frame.awaiting_child = false;
            }
            if (frame.next == frame.node->children.end()) { pending.pop_back(); continue; }
            frame.current = frame.next++;
            Elem& e = *frame.current;
            if (e.name == "block" || e.name == "group") {
                frame.awaiting_child = true;
                pending.emplace_back(e, e.name == "group");
            } else {
                if (e.name == "slide") {
                    if (!slideConstraints(e, diags)) { return false; }
                } else if (!constraintLeaf(e, diags)) { return false; }
                frame.node->children.erase(frame.current);
            }
        }
        return true;
    }

    // ---- objectives ------------------------------------------------------

    bool objectives(const Elem& objs, Uir::Diagnostics& diags) {
        bool expanded_lex_objective = false;
        for (const Elem& e : objs.children) {
            const bool minimise = e.name == "minimize";
            if (!minimise && e.name != "maximize") {
                diags.error(ErrorCode::E_PARSE,
                            "'" + e.name + "' is not an objective", at(e));
                return false;
            }
            H::ExprPtr term;
            const std::string kind = e.attr("type");
            if (kind.empty() || kind == "expression") {
                std::size_t i = 0;
                term = intension(e.text, i, e, diags, 0);
                if (!term) { return false; }
                while (i < e.text.size()
                       && std::isspace(static_cast<unsigned char>(e.text[i]))) { ++i; }
                if (i != e.text.size()) {
                    diags.error(ErrorCode::E_PARSE,
                                "trailing text in the objective expression", at(e));
                    return false;
                }
            } else if (kind == "sum" || kind == "product" || kind == "minimum"
                       || kind == "maximum" || kind == "nValues" || kind == "lex") {
                std::vector<H::ExprPtr> scope;
                const std::string text = e.child("list") ? e.child("list")->text : e.text;
                if (!expressionList(text, scope, e, diags)) { return false; }
                if (scope.size() < 2) {
                    diags.error(ErrorCode::E_PARSE,
                                "objective type '" + kind
                                    + "' requires at least two variables", at(e));
                    return false;
                }
                std::vector<long long> coeffs(scope.size(), 1);
                if (const Elem* cf = e.child("coeffs")) {
                    coeffs.clear();
                    if (!integerList(cf->text, coeffs, scope.size(), e, diags)) { return false; }
                }
                std::vector<H::ExprPtr> terms;
                for (std::size_t k = 0; k < scope.size(); ++k) {
                    terms.push_back(coeffs[k] == 1
                                        ? scope[k]
                                        : relational_.value(H::Op::MUL,
                                                             {num(coeffs[k]), scope[k]}, at(e)));
                }
                if (kind == "sum") {
                    term = relational_.value(H::Op::ADD, terms, at(e));
                } else if (kind == "product") {
                    term = relational_.value(H::Op::MUL, terms, at(e));
                } else if (kind == "minimum" || kind == "maximum") {
                    term = extremumValue(std::move(terms), kind == "minimum", at(e));
                } else if (kind == "nValues") {
                    std::vector<H::ExprPtr> indicators;
                    for (std::size_t i = 0; i < terms.size(); ++i) {
                        std::vector<H::ExprPtr> first;
                        for (std::size_t j = 0; j < i; ++j) {
                            H::ExprPtr equal = relational_.value(
                                H::Op::EQ, {terms[i], terms[j]}, at(e));
                            first.push_back(relational_.value(H::Op::NOT, {equal}, at(e)));
                        }
                        H::ExprPtr fresh = first.empty() ? H::mkBool(true, at(e))
                            : relational_.value(H::Op::AND, first, at(e));
                        indicators.push_back(relational_.conditional(
                            fresh, num(1), num(0), at(e)));
                    }
                    term = relational_.value(H::Op::ADD, indicators, at(e));
                } else {
                    if (expanded_lex_objective || objs.children.size() != 1
                        || (!objs.attr("combination").empty()
                            && objs.attr("combination") != "lexico")) {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                    "a lex tuple objective cannot be combined with another "
                                    "objective or with a non-lexico outer combination", at(e));
                        return false;
                    }
                    expanded_lex_objective = true;
                    for (const H::ExprPtr& component : terms) {
                        const auto partial = relational_.inspect(component);
                        if (partial.defined && !(partial.defined->kind == H::ExprKind::LIT_BOOL
                                                 && partial.defined->bool_value)) {
                            addFormula(partial.defined, e);
                        }
                        H::Objective component_objective;
                        component_objective.name =
                            "obj" + std::to_string(model_->objectives.size());
                        component_objective.kind = minimise ? H::ObjKind::MINIMIZE
                                                            : H::ObjKind::MAXIMIZE;
                        component_objective.term = component;
                        component_objective.loc = at(e);
                        model_->objectives.push_back(std::move(component_objective));
                    }
                    model_->objective_combination =
                        H::ObjectiveCombination::LEXICOGRAPHIC;
                    continue;
                }
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "objective type '" + kind + "' is not implemented", at(e));
                return false;
            }
            H::Objective o;
            o.name = "obj" + std::to_string(model_->objectives.size());
            o.kind = minimise ? H::ObjKind::MINIMIZE : H::ObjKind::MAXIMIZE;
            o.term = term;
            o.loc = at(e);
            const Uir::Sem::PartialExpr partial = relational_.inspect(term);
            if (partial.defined
                && !(partial.defined->kind == H::ExprKind::LIT_BOOL
                     && partial.defined->bool_value)) {
                H::Constraint defined;
                defined.loc = at(e);
                defined.formula = partial.defined;
                model_->constraints.push_back(std::move(defined));
            }
            model_->objectives.push_back(o);
        }
        // §4.5's obligation was written when the HIR could not say this and
        // recommended refusing; ObjectiveCombination has since landed, so it is
        // recorded instead. typeCheck refuses SINGLE with two or more, which is
        // what stops silence being read as lexicographic.
        const std::string combo = objs.attr("combination");
        if (model_->objectives.size() >= 2) {
            if (combo == "lexico" || combo.empty()) {
                model_->objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
            } else if (combo == "pareto") {
                model_->objective_combination = H::ObjectiveCombination::PARETO;
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "the objective combination '" + combo + "' is not implemented",
                            at(objs));
                return false;
            }
        }
        return true;
    }

    std::string_view src_;
    std::istream* stream_ = nullptr;
    std::string file_;
    H::ConstraintModelPtr model_;
    // These immutable leaves have no occurrence-specific source location.
    // Share them within this model; bound and auxiliary identifiers still use
    // their own constructors and retain their distinct scopes and locations.
    mutable std::unordered_map<std::string, H::ExprPtr> variable_exprs_;
    mutable std::unordered_map<long long, H::ExprPtr> integer_exprs_;
    std::map<std::tuple<int, std::string, std::vector<H::ExprPtr>>, H::ExprPtr> intension_exprs_;
    std::map<std::pair<std::size_t, long long>, std::string> positional_element_helpers_;
    bool compiling_shared_element_ = false;
    std::unordered_map<std::string, std::unordered_map<long long, H::ExprPtr>> table_equalities_;
    std::unordered_map<std::string, SourceVariable> domains_;
    std::unordered_map<std::string, CompactSourceRange> compact_variables_;
    std::shared_ptr<H::PackedFunctionCalls> packed_calls_;
    bool streamed_variables_ = false;
    std::size_t indexed_declarations_ = 0;
    std::unordered_map<std::string, std::size_t> declaration_ids_;
    std::unordered_map<std::string, ArrayInfo> arrays_;
    Uir::TranslationReport* report_ = nullptr;
    Uir::Sem::RelationalBuilder relational_;
    bool said_partiality_ = false;
    std::size_t auxiliary_counter_ = 0;
    std::size_t group_function_seq_ = 0;
    mutable std::unordered_set<std::string> group_symbol_keys_;
    mutable bool group_symbol_keys_ready_ = false;
    std::unordered_map<const Elem*, std::size_t> extension_template_by_element_;
    std::vector<SharedExtensionTemplate> extension_templates_;
};

class Xcsp3Language : public Language {
public:
    Xcsp3Language() {
        // Twenty-seven accepted constraint/meta element names cover the
        // XCSP3-core catalogue plus clause, lifted list/matrix forms and
        // group/block/slide. Generalized intExpr views remain deliberately
        // narrower than full XCSP3 and are counted as one capability family.
        coverage_.total = 28;
        coverage_.supported = 27;
        coverage_.missing = {"generalized intExpr views in every global-list position"};
    }

    std::string id() const override { return "xcsp3"; }
    std::string displayName() const override { return "XCSP3-core"; }
    std::string version() const override { return "3.2-core"; }
    std::vector<std::string> extensions() const override { return {".xml", ".xcsp3"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions&) override {
        ParseOutcome out;
        std::ifstream input;
        if (unit.inline_source.empty()) {
            std::error_code error;
            if (std::filesystem::is_directory(unit.main_path, error)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            input.open(unit.main_path, std::ios::binary);
            if (!input) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        bool constructing_contract = false;
        try {
            std::vector<H::ExprPtr> declaration_terms;
            {
                Xcsp3Parser p(unit.inline_source, name, unit.inline_source.empty() ? &input : nullptr);
                out.model = p.parse(out.diagnostics, out.report);
                if (out.model) { declaration_terms = p.declarationTerms(); }
            }
            // Source-domain and expression lookup caches are needed only for
            // parsing. Preserve only shared identifier handles for bound axioms,
            // then release the lookup tables before constructing the contract.
            if (out.model) {
                constructing_contract = true;
                out.semantics.add(Uir::Sem::xcsp3ToRelationalContract(
                    *out.model, out.report.fidelity(), declaration_terms));
            }
        } catch (const std::bad_alloc&) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_RESOURCE,
                constructing_contract ? "xcsp3 semantic contract construction: memory allocation failed"
                       : "xcsp3 frontend parsing: memory allocation failed");
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("xcsp3 frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkXcsp3Language() { return std::make_shared<Xcsp3Language>(); }

} // namespace SOMTParser::Lang
