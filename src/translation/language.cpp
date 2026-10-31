/* -*- Source -*-
 * LanguageRegistry: extension narrowing plus content sniffing.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/language.h"
#include "somtparser/core/asserting.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <utility>

namespace SOMTParser::Lang {

namespace {

std::string toLower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return s;
}

/** Lowercased extension including the dot, or "" when there is none. */
std::string extensionOf(const std::string& path) {
    const auto slash = path.find_last_of("/\\");
    const auto start = (slash == std::string::npos) ? 0 : slash + 1;
    const auto dot = path.find_last_of('.');
    if (dot == std::string::npos || dot <= start) {
        return {};
    }
    return toLower(path.substr(dot));
}

} // namespace

LanguageRegistry& LanguageRegistry::instance() {
    static LanguageRegistry r;
    return r;
}

void LanguageRegistry::add(LanguagePtr lang) {
    condAssert(lang != nullptr, "LanguageRegistry::add: null language");
    langs_.push_back(std::move(lang));
}

Language* LanguageRegistry::byId(std::string_view id) const {
    for (const auto& l : langs_) {
        if (l->id() == id) {
            return l.get();
        }
    }
    return nullptr;
}

std::string LanguageRegistry::readHead(const std::string& path, std::size_t max_bytes) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        return {};
    }
    std::string buf(max_bytes, '\0');
    in.read(&buf[0], static_cast<std::streamsize>(max_bytes));
    buf.resize(static_cast<std::size_t>(in.gcount()));
    return buf;
}

Language* LanguageRegistry::detect(const SourceUnit& unit) const {
    const std::string ext = extensionOf(unit.main_path);

    std::vector<Language*> candidates;
    for (const auto& l : langs_) {
        for (const auto& e : l->extensions()) {
            if (toLower(e) == ext) {
                candidates.push_back(l.get());
                break;
            }
        }
    }
    if (candidates.empty()) {
        return nullptr;
    }
    if (candidates.size() == 1) {
        return candidates.front();
    }

    const std::string head = unit.inline_source.empty()
                                 ? readHead(unit.main_path)
                                 : unit.inline_source.substr(
                                       0, std::min<std::size_t>(unit.inline_source.size(), 8192));

    Language* best = candidates.front();
    double    best_score = -1.0;
    for (Language* c : candidates) {
        const double s = c->sniff(head);
        if (s > best_score) {
            best_score = s;
            best = c;
        }
    }
    return best;
}

std::vector<Language*> LanguageRegistry::all() const {
    std::vector<Language*> out;
    out.reserve(langs_.size());
    for (const auto& l : langs_) {
        out.push_back(l.get());
    }
    return out;
}

} // namespace SOMTParser::Lang
