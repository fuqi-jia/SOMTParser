/* -*- Source -*-
 * FlatZinc frontend.
 *
 * The format is docs/languages/flatzinc.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/flatzinc/instances.
 *
 * The fourth obligation is the one that governs the whole design:
 *
 *     **An unrecognised builtin is E_UNSUPPORTED_CONSTRUCT, never a skipped
 *     constraint.**
 *
 * FlatZinc's builtin catalogue IS the language, and it is *open* -- a solver may
 * declare support for additional predicates. So a frontend meets names it does
 * not know as a matter of course, and the tempting response is to skip them.
 * Skipping drops a constraint, which weakens the model: more solutions, and the
 * answer looks like success. Refusing costs coverage and says so.
 *
 * The first obligation is the sharpest concrete one. `array_int_element(i, as,
 * x)` becomes an ITE chain, and the chain's final `else` has to denote
 * something -- so without the index constraint `1 <= i <= |as|` it silently
 * defines `as[i]` for out-of-range `i`, which is a value the model never gave it.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/flatzinc.h"
#include "somtparser/translation/module.h"

#include <algorithm>
#include <cctype>
#include <filesystem>
#include <fstream>
#include <memory>
#include <functional>
#include <limits>
#include <set>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <gmpxx.h>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

/** One parsed argument: a literal, an identifier, or an array of either. */
struct Arg {
    bool                     is_array = false;
    std::string              text;        // scalar
    std::vector<std::string> items;       // array
};

struct Decl {
    std::string name;
    H::Sort     sort;
    bool        is_array = false;
    bool        is_variable = false;
    std::vector<std::string> elems;       // array element names or literals
    bool        has_lo = false, has_hi = false;
    bool        real_bounds = false;
    std::string lo, hi;
    std::string set_domain;
    bool has_int_domain = false;
    std::vector<std::string> int_domain;
    int         line = 0;
};

struct PendingInitializer {
    std::string name;
    std::string value;
    H::Sort     sort;
    int         line = 0;
};

bool isIntText(const std::string& s) {
    if (s.empty()) { return false; }
    std::size_t i = (s[0] == '-' || s[0] == '+') ? 1 : 0;
    if (i == s.size()) { return false; }
    for (; i < s.size(); ++i) {
        if (!std::isdigit(static_cast<unsigned char>(s[i]))) { return false; }
    }
    return true;
}

/** A FlatZinc float literal: `1.0`, `-3.5`, `1.0e-9`, `2e10`.
 *
 *  `var float` already mapped to `Sort::real()`, so the SORT was supported and
 *  the LITERAL was not: `constraint float_le(1.0, x)` reported "undeclared
 *  identifier '1.0'" -- an E_PARSE naming a number as if it were a variable the
 *  model forgot to declare. Half a theory is the shape of defect this project
 *  keeps finding, and it reads as malformed input rather than as a gap. */
bool isFloatText(const std::string& s) {
    if (s.empty()) { return false; }
    std::size_t i = (s[0] == '-' || s[0] == '+') ? 1 : 0;
    bool digits = false, dot = false, exp = false;
    for (; i < s.size(); ++i) {
        const char c = s[i];
        if (std::isdigit(static_cast<unsigned char>(c))) { digits = true; continue; }
        if (c == '.' && !dot && !exp) { dot = true; continue; }
        if ((c == 'e' || c == 'E') && digits && !exp) {
            exp = true;
            if (i + 1 < s.size() && (s[i + 1] == '-' || s[i + 1] == '+')) { ++i; }
            digits = false;                  // the exponent needs its own digits
            continue;
        }
        return false;
    }
    // A bare integer is not a float here: it must carry a '.' or an exponent,
    // or `3` would build a Real and stop matching an Int-sorted operand.
    return digits && (dot || exp);
}

class FznParser {
public:
    FznParser(std::string src, std::string file)
        : src_(std::move(src)), file_(std::move(file)) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags) {
        if (!read(diags)) { return nullptr; }
        return model_;
    }

    std::shared_ptr<SourceModule> parseModule(Uir::Diagnostics& diags) {
        module_ = std::make_shared<SourceModule>();
        module_->language = "flatzinc";
        if (!read(diags)) { return nullptr; }
        module_->known = *model_;
        return module_;
    }

    Uir::Sem::ModelProjection modelProjection() const {
        Uir::Sem::ModelProjection projection;
        projection.observables = observables_;
        return projection;
    }

    bool usedRelationalPartiality() const noexcept { return used_partiality_; }

    const std::vector<H::ExprPtr>& implicitAxioms() const noexcept {
        return implicit_axioms_;
    }

private:
    struct Parameter {
        H::Sort sort;
        bool array = false, parameter = true;
    };
    std::unordered_map<std::string, std::vector<std::vector<Parameter>>> predicates_;
    std::shared_ptr<SourceModule> module_;

    static bool plainIdentifier(const std::string& name) {
        if (name.empty() || !(std::isalpha(static_cast<unsigned char>(name[0])) || name[0] == '_')) {
            return false;
        }
        return std::all_of(name.begin() + 1, name.end(), [](char c) {
            return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
        });
    }

    bool predicateItem(const std::string& text, int line, Uir::Diagnostics& diags) {
        const auto lp = text.find('(');
        if (lp == std::string::npos || text.back() != ')') {
            diags.error(ErrorCode::E_PARSE, "malformed predicate declaration", at(line));
            return false;
        }
        const auto name = trim(text.substr(9, lp - 9));
        if (text.rfind("predicate ", 0) != 0 || !plainIdentifier(name)) {
            diags.error(ErrorCode::E_PARSE, "malformed predicate name", at(line)); return false;
        }
        std::vector<Parameter> signature;
        std::unordered_set<std::string> parameter_names;
        for (const auto& field : topCommas(text.substr(lp + 1, text.size() - lp - 2))) {
            const auto colon = field.find(':');
            if (colon == std::string::npos || trim(field.substr(colon + 1)).empty()) {
                diags.error(ErrorCode::E_PARSE, "predicate parameter needs a type and name", at(line));
                return false;
            }
            auto type = trim(field.substr(0, colon));
            const auto equal = field.find('=', colon + 1);
            const auto parameter_name = trim(field.substr(colon + 1,
                equal == std::string::npos ? std::string::npos : equal - colon - 1));
            if (!plainIdentifier(parameter_name) || !parameter_names.insert(parameter_name).second) {
                diags.error(ErrorCode::E_PARSE, "malformed or repeated predicate parameter name", at(line));
                return false;
            }
            Parameter parameter;
            if (type.rfind("array", 0) == 0) {
                const auto of = type.find(" of ");
                if (of == std::string::npos || trim(type.substr(5, of - 5)) != "[int]") {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "external predicate arrays require the [int] index type", at(line));
                    return false;
                }
                parameter.array = true; type = trim(type.substr(of + 4));
            }
            if (type.rfind("var ", 0) == 0) {
                parameter.parameter = false; type = trim(type.substr(4));
            }
            if (type == "int") { parameter.sort = H::Sort::integer(); }
            else if (type == "float") { parameter.sort = H::Sort::real(); }
            else if (type == "bool") { parameter.sort = H::Sort::boolean(); }
            else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "external predicate parameter type '" + type + "' is not supported", at(line));
                return false;
            }
            if (equal != std::string::npos) {
                const auto value = trim(field.substr(equal + 1));
                const bool valid = !parameter.array &&
                    ((parameter.sort.kind == H::SortKind::INT && isIntText(value))
                     || (parameter.sort.kind == H::SortKind::REAL && isFloatText(value))
                     || (parameter.sort.kind == H::SortKind::BOOL && (value == "true" || value == "false")));
                if (!valid) {
                    diags.error(ErrorCode::E_TYPE,
                                "external predicate default must be a literal of its parameter type", at(line));
                    return false;
                }
            }
            signature.push_back(parameter);
        }
        predicates_[name].push_back(std::move(signature));
        return true;
    }

    bool externalCall(const std::string& name, const std::vector<Arg>& args,
                      const std::string& annotations, int line, Uir::Diagnostics& diags) {
        const auto declarations = predicates_.find(name);
        if (declarations == predicates_.end()) {
            diags.error(ErrorCode::E_PARSE,
                        "external predicate '" + name + "' has no declaration", at(line));
            return false;
        }
        std::function<bool(const H::ExprPtr&)> constant = [&](const H::ExprPtr& expression) {
            if (expression->kind == H::ExprKind::IDENT
                || expression->kind == H::ExprKind::BOUND_VAR) { return false; }
            for (const auto& child : expression->args) { if (!constant(child)) { return false; } }
            return true;
        };
        std::vector<ExternalCall> matches;
        for (const auto& signature : declarations->second) {
            if (signature.size() != args.size()) { continue; }
            ExternalCall candidate;
            candidate.predicate = name; candidate.annotations = annotations; candidate.loc = at(line);
            Uir::Diagnostics attempt;
            bool compatible = true;
            for (std::size_t i = 0; i < args.size() && compatible; ++i) {
                const auto& parameter = signature[i];
                ExternalArgument argument;
                argument.sort = parameter.sort; argument.array = parameter.array;
                argument.parameter = parameter.parameter;
                std::vector<std::string> values;
                if (parameter.array) {
                    const auto declared = arrays_.find(args[i].text);
                    if (declared != arrays_.end()) {
                        // An empty array still has its declared element type.
                        // Inspecting only values would accept a wrong sort or
                        // make otherwise distinct overloads ambiguous.
                        if (!H::sameSort(declared->second.sort, parameter.sort)
                            || (parameter.parameter && declared->second.is_variable)) {
                            compatible = false; break;
                        }
                    }
                    if (!arrayItems(args[i], values, line, attempt)) { compatible = false; break; }
                } else if (args[i].is_array) { compatible = false; break; }
                else { values.push_back(args[i].text); }
                for (const auto& spelling : values) {
                    auto value = scalar(spelling, line, attempt);
                    if (!value || !H::sameSort(value->sort, parameter.sort)
                        || (parameter.parameter && !constant(value))) {
                        compatible = false; break;
                    }
                    argument.values.push_back(value);
                }
                candidate.arguments.push_back(std::move(argument));
            }
            if (compatible) { matches.push_back(std::move(candidate)); }
        }
        // Specificity is a partial order, not a count of par positions. Two
        // overloads can constrain different argument positions and neither win.
        std::vector<std::size_t> maximal;
        for (std::size_t i = 0; i < matches.size(); ++i) {
            bool dominated = false;
            for (std::size_t j = 0; j < matches.size(); ++j) {
                if (i == j) { continue; }
                bool at_least = true, stricter = false;
                for (std::size_t k = 0; k < args.size(); ++k) {
                    const bool a = matches[i].arguments[k].parameter;
                    const bool b = matches[j].arguments[k].parameter;
                    at_least = at_least && (!a || b);
                    stricter = stricter || (!a && b);
                }
                dominated = dominated || (at_least && stricter);
            }
            if (!dominated) { maximal.push_back(i); }
        }
        if (maximal.size() != 1) {
            diags.error(ErrorCode::E_TYPE, "external predicate '" + name
                        + (maximal.empty() ? "' has no matching typed signature" : "' has ambiguous overloads"), at(line));
            return false;
        }
        module_->unresolved.push_back(std::move(matches[maximal.front()]));
        return true;
    }

    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        l.column = 1;
        return l;
    }

    /** Statement delimiters and comments inside string annotations are data.
     * External callbacks in particular carry filenames that must survive. */
    bool read(Uir::Diagnostics& diags) {
        model_ = std::make_shared<H::ConstraintModel>();
        int lineno = 1;
        std::string stmt;
        int stmt_line = 1;
        bool quoted = false, escaped = false, comment = false;
        std::vector<char> brackets;
        for (char c : src_) {
            if (c == '\n') { ++lineno; comment = false; }
            if (comment) { continue; }
            if (quoted) {
                stmt += c;
                if (escaped) { escaped = false; }
                else if (c == '\\') { escaped = true; }
                else if (c == '"') { quoted = false; }
                continue;
            }
            if (c == '%') { comment = true; continue; }
            if (stmt.empty() && std::isspace(static_cast<unsigned char>(c))) { continue; }
            if (stmt.empty()) { stmt_line = lineno; }
            if (c == '"') { quoted = true; }
            if (c == '(' || c == '[' || c == '{') { brackets.push_back(c); }
            if (c == ')' || c == ']' || c == '}') {
                const char opening = c == ')' ? '(' : c == ']' ? '[' : '{';
                if (brackets.empty() || brackets.back() != opening) {
                    diags.error(ErrorCode::E_PARSE, "unbalanced FlatZinc delimiters", at(lineno));
                    return false;
                }
                brackets.pop_back();
            }
            if (c == ';' && brackets.empty()) {
                if (!statement(stmt, stmt_line, diags)) { return false; }
                stmt.clear();
            } else {
                stmt += (c == '\n' || c == '\r') ? ' ' : c;
            }
        }
        if (quoted || !brackets.empty()) {
            diags.error(ErrorCode::E_PARSE, "unterminated FlatZinc string or delimiter", at(stmt_line));
            return false;
        }
        if (stmt.find_first_not_of(" \t") != std::string::npos) {
            diags.error(ErrorCode::E_PARSE, "the last item is not terminated by ';'",
                        at(stmt_line));
            return false;
        }
        if (!materializeInitializers(diags)) { return false; }
        if (!solve_seen_) {
            diags.error(ErrorCode::E_PARSE,
                        "the model has no solve item; a FlatZinc model has exactly one",
                        at(1));
            return false;
        }
        // Objective labels bind names in the OMT dialect. Choose them after
        // every declaration, so a legal source variable such as `obj` is safe.
        for (auto& objective : model_->objectives) {
            std::string candidate = "obj";
            std::size_t suffix = 0;
            while (scalars_.count(candidate) || params_.count(candidate)
                   || arrays_.count(candidate)) {
                candidate = "obj" + std::to_string(++suffix);
            }
            objective.name = candidate;
        }
        return true;
    }

    static std::string stripAnnotations(const std::string& s) {
        const std::size_t a = s.find("::");
        return a == std::string::npos ? s : s.substr(0, a);
    }

    /** Remove declaration annotations without discarding a following value.
     *
     * Canonical FlatZinc writes `name :: annotation = value`. The generic
     * stripAnnotations helper intentionally drops everything after `::`, which
     * made a nonempty array declaration look uninitialised and then made every
     * constraint over its elements operate on an empty array. */
    static std::string stripDeclAnnotations(const std::string& s) {
        const std::size_t annotation = s.find("::");
        if (annotation == std::string::npos) { return s; }
        std::size_t assignment = std::string::npos;
        int depth = 0;
        bool quoted = false, escaped = false;
        for (std::size_t i = 0; i < s.size(); ++i) {
            if (quoted) {
                if (escaped) { escaped = false; }
                else if (s[i] == '\\') { escaped = true; }
                else if (s[i] == '"') { quoted = false; }
                continue;
            }
            if (s[i] == '"') { quoted = true; continue; }
            if (s[i] == '(' || s[i] == '[' || s[i] == '{') { ++depth; }
            else if (s[i] == ')' || s[i] == ']' || s[i] == '}') { --depth; }
            else if (s[i] == '=' && depth == 0) { assignment = i; break; }
        }
        if (assignment == std::string::npos || assignment < annotation) {
            return s.substr(0, annotation);
        }
        return s.substr(0, annotation) + " " + s.substr(assignment);
    }

    static bool hasAnnotation(const std::string& text, const std::string& annotation) {
        const std::size_t first = text.find("::");
        return first != std::string::npos
               && text.find(annotation, first + 2) != std::string::npos;
    }

    static std::string trim(const std::string& s) {
        const std::size_t a = s.find_first_not_of(" \t");
        if (a == std::string::npos) { return ""; }
        return s.substr(a, s.find_last_not_of(" \t") - a + 1);
    }

    /** Split on commas at bracket depth zero, so `[1,2],[x,y]` stays two. */
    static std::vector<std::string> topCommas(const std::string& s) {
        std::vector<std::string> out;
        int depth = 0;
        std::string cur;
        bool quoted = false, escaped = false;
        for (char c : s) {
            if (quoted) {
                cur += c;
                if (escaped) { escaped = false; }
                else if (c == '\\') { escaped = true; }
                else if (c == '"') { quoted = false; }
                continue;
            }
            if (c == '"') { quoted = true; cur += c; continue; }
            if (c == '[' || c == '(' || c == '{') { ++depth; }
            if (c == ']' || c == ')' || c == '}') { --depth; }
            if (c == ',' && depth == 0) { out.push_back(trim(cur)); cur.clear(); continue; }
            cur += c;
        }
        if (!trim(cur).empty()) { out.push_back(trim(cur)); }
        return out;
    }

    static Arg toArg(const std::string& text) {
        Arg a;
        const std::string t = trim(text);
        if (!t.empty() && t.front() == '[' && t.back() == ']') {
            a.is_array = true;
            a.items = topCommas(t.substr(1, t.size() - 2));
            return a;
        }
        a.text = t;
        return a;
    }

    bool statement(const std::string& text, int line, Uir::Diagnostics& diags) {
        const std::string s = trim(text);
        if (s.empty()) { return true; }
        if (s.rfind("predicate", 0) == 0) {
            return module_ ? predicateItem(s, line, diags) : true;
        }
        if (s.rfind("solve", 0) == 0
            && (s.size() == 5 || (!std::isalnum(static_cast<unsigned char>(s[5]))
                                 && s[5] != '_'))) {
            return solveItem(s, line, diags);
        }
        if (s.rfind("constraint", 0) == 0) {
            return constraintItem(trim(s.substr(10)), line, diags);
        }
        return declItem(s, line, diags);
    }

    // ---- declarations ----------------------------------------------------

    bool declItem(const std::string& text, int line, Uir::Diagnostics& diags) {
        const bool output_var = hasAnnotation(text, "output_var");
        const bool output_array = hasAnnotation(text, "output_array");
        const std::string s = trim(stripDeclAnnotations(text));
        const std::size_t colon = s.find(':');
        if (colon == std::string::npos) {
            diags.error(ErrorCode::E_PARSE, "unrecognised item", at(line));
            return false;
        }
        std::string type = trim(s.substr(0, colon));
        std::string rest = trim(s.substr(colon + 1));
        std::string name = rest;
        std::string init;
        std::string array_index;
        const std::size_t eq = rest.find('=');
        if (eq != std::string::npos) {
            name = trim(rest.substr(0, eq));
            init = trim(rest.substr(eq + 1));
        }

        Decl d;
        d.name = name;
        d.line = line;
        // `array [1..n] of <elem>` -- index sets are always 1..n in FlatZinc,
        // which is one of the two reasons it costs less than MiniZinc.
        if (type.rfind("array", 0) == 0) {
            const std::size_t of = type.find(" of ");
            if (of == std::string::npos) {
                diags.error(ErrorCode::E_PARSE, "an array type needs `of`", at(line));
                return false;
            }
            d.is_array = true;
            array_index = trim(type.substr(5, of - 5));
            type = trim(type.substr(of + 4));
            if (!init.empty() && init.front() == '[' && init.back() == ']') {
                d.elems = topCommas(init.substr(1, init.size() - 2));
            }
        }
        const bool is_var = type.rfind("var", 0) == 0;
        d.is_variable = is_var;
        if (is_var) { type = trim(type.substr(3)); }

        if (type == "bool") { d.sort = H::Sort::boolean(); }
        else if (type == "int") { d.sort = H::Sort::integer(); }
        else if (type == "float") { d.sort = H::Sort::real(); }
        else if (type.rfind("set of", 0) == 0) {
            d.sort = H::Sort::set(H::Sort::integer());
            d.set_domain = trim(type.substr(6));
            // A scalar decision set needs an explicit finite upper carrier.
            // MiniZinc also emits fully initialized `var set of int` arrays;
            // setArrayDeclaration validates their finite aliases cell by cell.
            if (is_var && d.set_domain == "int" && !d.is_array) {
                diags.error(
                    ErrorCode::E_TYPE,
                    "a FlatZinc decision-set declaration needs a finite upper "
                    "carrier; `var set of int` is only valid in a predicate signature",
                    at(line));
                return false;
            }
        }
        else if (is_var && type.size() >= 2 && type.front() == '{' && type.back() == '}') {
            d.sort = H::Sort::integer();
            d.has_int_domain = true;
            const std::string contents = trim(type.substr(1, type.size() - 2));
            d.int_domain = topCommas(contents);
            if ((!contents.empty() && contents.back() == ',')
                || std::any_of(d.int_domain.begin(), d.int_domain.end(),
                               [](const std::string& value) { return !isIntText(value); })) {
                diags.error(ErrorCode::E_TYPE,
                            "an enumerated integer domain needs integer literals", at(line));
                return false;
            }
        }
        else {
            // A domain: `1..5`, or `{1,3,5}`. §2.2 -- FlatZinc ALWAYS writes the
            // domain, so carrying it is materialisation and not inference, and
            // dropping it widens the variable silently.
            const std::size_t dots = type.find("..");
            const std::string lo = dots == std::string::npos
                                       ? "" : trim(type.substr(0, dots));
            const std::string hi = dots == std::string::npos
                                       ? "" : trim(type.substr(dots + 2));
            const bool int_range = isIntText(lo) && isIntText(hi);
            const bool numeric_range = (isIntText(lo) || isFloatText(lo))
                                       && (isIntText(hi) || isFloatText(hi));
            if (dots != std::string::npos && numeric_range) {
                d.real_bounds = !int_range;
                d.sort = d.real_bounds ? H::Sort::real() : H::Sort::integer();
                d.lo = lo; d.has_lo = true;
                d.hi = hi; d.has_hi = true;
            } else {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "variable type '" + type + "' is not supported yet", at(line));
                return false;
            }
        }

        if (d.is_array) {
            if (d.sort.kind == H::SortKind::SET) {
                return setArrayDeclaration(d, array_index, init, output_array, diags);
            }
            arrays_[d.name] = d;
            // A par array (`array [1..3] of int: a = [1,2,3];`) declares
            // nothing; a var array declares each element.
            if (is_var) {
                for (std::size_t k = 0; k < d.elems.size(); ++k) {
                    declareScalar(d.elems[k], d, line);
                    if (!addIntegerDomain(d.elems[k], d, line, diags)) { return false; }
                    if (!d.set_domain.empty() && d.set_domain != "int"
                        && scalars_.count(d.elems[k]) != 0) {
                        H::ExprPtr domain = setExpr(d.set_domain, line, diags);
                        if (!domain) { return false; }
                        H::ExprPtr variable = H::mkIdent(
                            d.elems[k], d.sort, at(line));
                        H::Constraint membership;
                        membership.loc = at(line);
                        membership.formula = H::mkOp(
                            H::Op::SET_SUBSET, {variable, domain}, at(line));
                        implicit_axioms_.push_back(membership.formula);
                        model_->constraints.push_back(std::move(membership));
                    }
                    if (output_array) {
                        const std::string source = d.name + "["
                            + std::to_string(k + 1) + "]";
                        const bool literal = isIntText(d.elems[k])
                            || isFloatText(d.elems[k]) || d.elems[k] == "true"
                            || d.elems[k] == "false";
                        observables_.push_back(
                            {source, d.elems[k],
                             literal ? Uir::Sem::ProjectionKind::CONSTANT
                                     : Uir::Sem::ProjectionKind::DIRECT});
                    }
                }
            }
            return true;
        }
        if (!is_var) {
            // A parameter: substituted, never declared.
            params_[d.name] = init;
            parameter_sorts_[d.name] = d.sort;
            return true;
        }
        declareScalar(d.name, d, line);
        if (!addIntegerDomain(d.name, d, line, diags)) { return false; }
        if (!d.set_domain.empty() && d.set_domain != "int") {
            std::string carrier = d.set_domain;
            if (!resolveSetParameter(carrier, line, diags)) { return false; }
            H::ExprPtr domain = fixedSetExpr(carrier, line, diags);
            if (!domain) { return false; }
            finite_sets_.insert(d.name);
            H::ExprPtr variable = H::mkIdent(d.name, d.sort, at(line));
            H::Constraint membership;
            membership.loc = at(line);
            membership.formula = H::mkOp(
                H::Op::SET_SUBSET, {variable, domain}, at(line));
            implicit_axioms_.push_back(membership.formula);
            model_->constraints.push_back(std::move(membership));
            finite_set_carriers_[d.name] = domain;
        }
        if (output_var) {
            observables_.push_back(
                {d.name, d.name, Uir::Sem::ProjectionKind::DIRECT});
        }
        if (!init.empty()) {
            pending_initializers_.push_back({d.name, init, d.sort, line});
        }
        return true;
    }

    // Parameter aliases stay constants: array declarations must not introduce
    // a fresh decision symbol under a parameter's name.
    bool resolveSetParameter(std::string& text, int line, Uir::Diagnostics& diags) {
        std::unordered_set<std::string> seen;
        text = trim(text);
        while (params_.count(text) != 0) {
            const auto sort = parameter_sorts_.find(text);
            if (!seen.insert(text).second || sort == parameter_sorts_.end()
                || sort->second.kind != H::SortKind::SET) {
                diags.error(ErrorCode::E_TYPE,
                            "a set value needs an acyclic set parameter", at(line));
                return false;
            }
            text = trim(params_.at(text));
        }
        if (!seen.empty() && scalars_.count(text) != 0) {
            diags.error(ErrorCode::E_TYPE,
                        "a set parameter cannot depend on a decision variable", at(line));
            return false;
        }
        return true;
    }

    bool setArrayDeclaration(Decl& d, const std::string& index,
                             const std::string& init, bool output,
                             Uir::Diagnostics& diags) {
        const std::string range = index.size() >= 2 && index.front() == '['
            && index.back() == ']' ? trim(index.substr(1, index.size() - 2)) : "";
        const std::size_t dots = range.find("..");
        const std::string upper = dots == std::string::npos
            ? "" : trim(range.substr(dots + 2));
        bool shape = dots != std::string::npos && trim(range.substr(0, dots)) == "1"
            && isIntText(upper) && upper.front() != '-'
            && init.size() >= 2 && init.front() == '[' && init.back() == ']';
        if (shape) {
            try { shape = std::stoull(upper) == d.elems.size(); }
            catch (const std::exception&) { shape = false; }
            const std::string body = trim(init.substr(1, init.size() - 2));
            shape = shape && (body.empty() || body.back() != ',');
        }
        if (!shape) {
            diags.error(ErrorCode::E_TYPE,
                        "a set array needs a complete initializer matching [1..n]", at(d.line));
            return false;
        }
        H::ExprPtr carrier;
        if (d.set_domain != "int") {
            std::string text = d.set_domain;
            if (!resolveSetParameter(text, d.line, diags)) { return false; }
            carrier = fixedSetExpr(text, d.line, diags);
            if (!carrier) { return false; }
        }
        for (std::size_t k = 0; k < d.elems.size(); ++k) {
            std::string cell = d.elems[k];
            if (!resolveSetParameter(cell, d.line, diags)) { return false; }
            auto declared = scalars_.find(cell);
            // Preserve the existing finite-domain array shorthand for fresh
            // element names. The unbounded compiler spelling cannot use it.
            const bool identifier = !cell.empty()
                && (std::isalpha(static_cast<unsigned char>(cell.front())) || cell.front() == '_')
                && std::all_of(cell.begin(), cell.end(), [](unsigned char c) {
                    return std::isalnum(c) || c == '_';
                }) && cell != "true" && cell != "false";
            if (declared == scalars_.end() && d.is_variable && carrier && identifier
                && params_.count(d.elems[k]) == 0 && arrays_.count(cell) == 0) {
                declareScalar(cell, d, d.line);
                finite_sets_.insert(cell);
                declared = scalars_.find(cell);
            }
            H::ExprPtr value;
            const bool variable = declared != scalars_.end();
            if (variable) {
                if (!d.is_variable || declared->second.kind != H::SortKind::SET
                    || finite_sets_.count(cell) == 0) {
                    diags.error(ErrorCode::E_TYPE,
                                "a set array alias needs an existing finite decision set", at(d.line));
                    return false;
                }
                value = H::mkIdent(cell, declared->second, at(d.line));
            } else {
                value = fixedSetExpr(cell, d.line, diags);
                if (!value) { return false; }
            }
            d.elems[k] = cell;
            if (carrier) {
                H::Constraint constraint;
                constraint.loc = at(d.line);
                constraint.formula = H::mkOp(H::Op::SET_SUBSET, {value, carrier}, at(d.line));
                implicit_axioms_.push_back(constraint.formula);
                model_->constraints.push_back(std::move(constraint));
                if (variable) { finite_set_carriers_[cell] = carrier; }
            }
            if (output) {
                observables_.push_back(
                    {d.name + "[" + std::to_string(k + 1) + "]", cell,
                     variable ? Uir::Sem::ProjectionKind::DIRECT
                              : Uir::Sem::ProjectionKind::CONSTANT});
            }
        }
        arrays_[d.name] = d;
        return true;
    }

    bool addIntegerDomain(const std::string& name, const Decl& declaration,
                          int line, Uir::Diagnostics& diags) {
        if (!declaration.has_int_domain) { return true; }
        H::ExprPtr value = scalar(name, line, diags);
        if (!value) { return false; }
        if (value->sort.kind != H::SortKind::INT) {
            diags.error(ErrorCode::E_TYPE,
                        "an enumerated integer domain requires an integer value", at(line));
            return false;
        }
        std::vector<H::ExprPtr> choices;
        choices.reserve(declaration.int_domain.size());
        for (const std::string& member : declaration.int_domain) {
            choices.push_back(H::mkOp(H::Op::EQ, {value, H::mkInt(member, at(line))}, at(line)));
        }
        H::ExprPtr domain = choices.empty() ? H::mkBool(false, at(line))
            : choices.size() == 1 ? choices.front()
            : H::mkOp(H::Op::OR, std::move(choices), at(line));
        // An array may restrict an already declared variable or a literal.
        // Keep this axiom even when declareScalar reused its existing symbol.
        H::Constraint constraint;
        constraint.loc = at(line);
        constraint.formula = domain;
        implicit_axioms_.push_back(domain);
        model_->constraints.push_back(std::move(constraint));
        return true;
    }

    bool materializeInitializers(Uir::Diagnostics& diags) {
        for (const PendingInitializer& initializer : pending_initializers_) {
            const auto declaration = scalars_.find(initializer.name);
            if (declaration == scalars_.end()) {
                diags.error(ErrorCode::E_INTERNAL,
                            "initializer refers to an undeclared variable '"
                                + initializer.name + "'",
                            at(initializer.line));
                return false;
            }
            H::ExprPtr value = initializer.sort.kind == H::SortKind::SET
                                   ? setExpr(initializer.value, initializer.line, diags)
                                   : scalar(initializer.value, initializer.line, diags);
            if (!value) { return false; }
            H::ExprPtr variable = H::mkIdent(
                initializer.name, initializer.sort, at(initializer.line));
            H::ExprPtr equality = H::mkOp(
                H::Op::EQ, {std::move(variable), std::move(value)},
                at(initializer.line));
            H::Constraint constraint;
            constraint.loc = at(initializer.line);
            constraint.formula = equality;
            implicit_axioms_.push_back(equality);
            model_->constraints.push_back(std::move(constraint));
        }
        return true;
    }

    void declareScalar(const std::string& name, const Decl& d, int line) {
        if (name.empty() || isIntText(name) || isFloatText(name)
            || name == "true" || name == "false") {
            return;
        }
        if (!scalars_.emplace(name, d.sort).second) { return; }
        H::VarDecl v;
        v.name = name;
        v.sort = d.sort;
        v.loc = at(line);
        if (d.has_lo) {
            v.lower_bound = d.real_bounds ? H::mkReal(d.lo, at(line))
                                          : H::mkInt(d.lo, at(line));
        }
        if (d.has_hi) {
            v.upper_bound = d.real_bounds ? H::mkReal(d.hi, at(line))
                                          : H::mkInt(d.hi, at(line));
        }
        model_->decls.push_back(v);
    }

    bool solveItem(const std::string& text, int line, Uir::Diagnostics& diags) {
        if (solve_seen_) {
            diags.error(ErrorCode::E_PARSE, "more than one solve item", at(line));
            return false;
        }
        solve_seen_ = true;
        // Search annotations precede the goal. Discarding the suffix at
        // the first :: would silently turn an optimisation into satisfaction.
        const std::string body = text.substr(5);
        std::size_t pos = 0;
        const auto whitespace = [&]() {
            while (pos < body.size()
                   && std::isspace(static_cast<unsigned char>(body[pos]))) { ++pos; }
        };
        whitespace();
        while (body.compare(pos, 2, "::") == 0) {
            pos += 2;
            whitespace();
            const std::size_t begin = pos;
            if (pos < body.size()
                && std::isalpha(static_cast<unsigned char>(body[pos]))) {
                ++pos;
                while (pos < body.size()
                       && (std::isalnum(static_cast<unsigned char>(body[pos]))
                           || body[pos] == '_')) { ++pos; }
            }
            const std::string name = body.substr(begin, pos - begin);
            if (name.empty() || name == "minimize" || name == "maximize"
                || name == "satisfy") {
                diags.error(ErrorCode::E_PARSE, "expected a solve annotation", at(line));
                return false;
            }
            whitespace();
            if (pos < body.size() && body[pos] == '(') {
                int depth = 0;
                bool quoted = false, escaped = false;
                do {
                    const char c = body[pos++];
                    if (quoted) {
                        if (escaped) { escaped = false; }
                        else if (c == '\\') { escaped = true; }
                        else if (c == '"') { quoted = false; }
                    } else if (c == '"') { quoted = true; }
                    else if (c == '(' || c == '[' || c == '{') { ++depth; }
                    else if (c == ')' || c == ']' || c == '}') { --depth; }
                } while (pos < body.size() && (depth > 0 || quoted));
                if (depth != 0 || quoted) {
                    diags.error(ErrorCode::E_PARSE, "unterminated solve annotation", at(line));
                    return false;
                }
            }
            whitespace();
        }
        const std::string s = trim(body.substr(pos));
        if (s == "satisfy") { return true; }
        const auto goal = [&](const std::string& keyword) {
            return s.size() > keyword.size() && s.compare(0, keyword.size(), keyword) == 0
                && !std::isalnum(static_cast<unsigned char>(s[keyword.size()]))
                && s[keyword.size()] != '_';
        };
        const bool maxi = goal("maximize");
        const bool mini = goal("minimize");
        if (!maxi && !mini) {
            diags.error(ErrorCode::E_PARSE, "a solve item is satisfy/minimize/maximize",
                        at(line));
            return false;
        }
        const std::string term = trim(s.substr(maxi ? 8 : 8));
        H::Objective o;
        o.kind = maxi ? H::ObjKind::MAXIMIZE : H::ObjKind::MINIMIZE;
        o.term = scalar(term, line, diags);
        o.loc = at(line);
        if (!o.term) { return false; }
        model_->objectives.push_back(o);
        return true;
    }

    // ---- expressions -----------------------------------------------------

    H::Sort sortOf(const std::string& name) const {
        const auto it = scalars_.find(name);
        return it == scalars_.end() ? H::Sort::integer() : it->second;
    }

    H::ExprPtr scalar(const std::string& text, int line, Uir::Diagnostics& diags) {
        const std::string t = trim(text);
        if (t == "true") { return H::mkBool(true, at(line)); }
        if (t == "false") { return H::mkBool(false, at(line)); }
        if (isIntText(t)) { return H::mkInt(t, at(line)); }
        // Kept as text, not parsed to a double: hir.h's LIT_REAL says why --
        // `1.0` and `1` are different terms, and a round trip through a double
        // is not exact.
        if (isFloatText(t)) { return H::mkReal(t, at(line)); }
        const auto p = params_.find(t);
        if (p != params_.end() && scalars_.count(t) == 0) {
            return scalar(p->second, line, diags);
        }
        if (scalars_.count(t) != 0) { return H::mkIdent(t, sortOf(t), at(line)); }
        diags.error(ErrorCode::E_PARSE, "undeclared identifier '" + t + "'", at(line));
        return nullptr;
    }

    /** A fixed set literal/range/parameter or a decision-set identifier. */
    H::ExprPtr setExpr(const std::string& text, int line,
                      Uir::Diagnostics& diags) {
        const std::string t = trim(text);
        std::string value = t;
        if (!resolveSetParameter(value, line, diags)) { return nullptr; }
        const auto declared = scalars_.find(value);
        if (declared != scalars_.end()) {
            if (declared->second.kind != H::SortKind::SET) {
                diags.error(ErrorCode::E_TYPE, "a set expression needs a set value", at(line));
                return nullptr;
            }
            return H::mkIdent(value, declared->second, at(line));
        }
        return fixedSetExpr(value, line, diags);
    }

    H::ExprPtr fixedSetExpr(const std::string& t, int line,
                           Uir::Diagnostics& diags) {
        std::vector<std::string> members;
        if (t.size() >= 2 && t.front() == '{' && t.back() == '}') {
            const std::string body = trim(t.substr(1, t.size() - 2));
            if (!body.empty() && body.back() == ',') {
                diags.error(ErrorCode::E_TYPE, "a set literal cannot end with a comma", at(line));
                return nullptr;
            }
            members = topCommas(body);
        } else {
            const std::size_t dots = t.find("..");
            if (dots == std::string::npos
                || !isIntText(trim(t.substr(0, dots)))
                || !isIntText(trim(t.substr(dots + 2)))) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "set expression '" + t
                                + "' is not a fixed integer set or decision-set variable",
                            at(line));
                return nullptr;
            }
            long long lo = 0, hi = 0;
            try {
                lo = std::stoll(trim(t.substr(0, dots)));
                hi = std::stoll(trim(t.substr(dots + 2)));
            } catch (const std::exception&) {
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "set range '" + t + "' exceeds the finite-set adapter",
                            at(line));
                return nullptr;
            }
            if (hi >= lo) {
                for (long long value = lo;; ++value) {
                    members.push_back(std::to_string(value));
                    if (value == hi) { break; }
                }
            }
        }

        const H::Sort sort = H::Sort::set(H::Sort::integer());
        H::ExprPtr empty = H::mkSetConst("set.empty", sort, at(line));
        if (members.empty()) { return empty; }
        std::vector<H::ExprPtr> values;
        values.reserve(members.size() + 1);
        for (const std::string& member : members) {
            if (!isIntText(member)) {
                diags.error(ErrorCode::E_TYPE,
                            "set member '" + member + "' is not an integer literal",
                            at(line));
                return nullptr;
            }
            values.push_back(H::mkInt(member, at(line)));
        }
        values.push_back(std::move(empty));
        return H::mkOp(H::Op::SET_INSERT, std::move(values), at(line));
    }

    /** An argument that is an array literal, or the name of one.
     *
     *  @p quiet suppresses the diagnostic for a caller that has a better one.
     *  `set_in` had exactly that -- it reported E_UNSUPPORTED_CONSTRUCT after
     *  this function failed -- and the report was defeated by ORDER, because
     *  `firstErrorCode()` takes the first and this one had already filed
     *  E_PARSE. The intent was right and invisible: four upstream files
     *  containing `var set of {1,3,5,7,9}` were counted as malformed input
     *  rather than as the coverage gap the frontend had correctly identified.
     */
    bool arrayItems(const Arg& a, std::vector<std::string>& out, int line,
                    Uir::Diagnostics& diags, bool quiet = false) {
        if (a.is_array) { out = a.items; return true; }
        const auto it = arrays_.find(a.text);
        if (it == arrays_.end()) {
            if (!quiet) {
                // A declared non-array is a construct this subset does not
                // reach, not a malformed file; an unknown name is neither, and
                // both used to read as E_PARSE.
                if (scalars_.count(a.text) != 0) {
                    diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                "'" + a.text + "' is a variable, not an array literal, "
                                "and this subset enumerates an array's elements at parse "
                                "time",
                                at(line));
                } else {
                    diags.error(ErrorCode::E_PARSE,
                                "'" + a.text + "' is not an array", at(line));
                }
            }
            return false;
        }
        out = it->second.elems;
        return true;
    }

    // ---- constraints -----------------------------------------------------

    bool constraintItem(const std::string& text, int line, Uir::Diagnostics& diags) {
        const std::string s = trim(stripAnnotations(text));
        const std::size_t lp = s.find('(');
        if (lp == std::string::npos || s.back() != ')') {
            diags.error(ErrorCode::E_PARSE, "a constraint is `name(args)`", at(line));
            return false;
        }
        std::string name = trim(s.substr(0, lp));
        const std::string source_name = name;
        std::vector<Arg> args;
        for (const auto& a : topCommas(s.substr(lp + 1, s.size() - lp - 2))) {
            args.push_back(toArg(a));
        }
        const auto source_args = args;

        // §4.6: `<base>_reif(args..., b)` is `b <-> base(args...)`. Handled
        // generically, because the catalogue is open and writing one case per
        // reified name would fall behind it.
        bool reified = false;
        bool half_reified = false;
        if (name.size() > 5 && name.compare(name.size() - 5, 5, "_reif") == 0) {
            reified = true;
            name.erase(name.size() - 5);
        } else if (name.size() > 4
                   && name.compare(name.size() - 4, 4, "_imp") == 0) {
            // FlatZinc's half-reified convention is base(args) implied by the
            // final Boolean: b -> base(args). It is not the reverse implication
            // and not equivalence; both alternatives change the feasible set.
            half_reified = true;
            name.erase(name.size() - 4);
        }
        H::ExprPtr b;
        if (reified || half_reified) {
            if (args.empty()) {
                diags.error(ErrorCode::E_PARSE,
                            "a reified constraint needs its final Boolean",
                            at(line));
                return false;
            }
            b = scalar(args.back().text, line, diags);
            if (!b) { return false; }
            if (b->sort.kind != H::SortKind::BOOL) {
                diags.error(ErrorCode::E_TYPE,
                            "the final argument of '" + name
                                + (reified ? "_reif'" : "_imp'")
                                + " must be Bool",
                            at(line));
                return false;
            }
            args.pop_back();
        }

        Uir::Diagnostics builtin_diagnostics;
        H::ExprPtr f = builtin(name, args, line, builtin_diagnostics);
        if (!f && module_ && builtin_diagnostics.size() == 1
            && builtin_diagnostics.firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT
            && builtin_diagnostics.all().front().message.rfind("builtin '" + name + "' is not implemented", 0) == 0) {
            const auto annotation = text.find("::");
            return externalCall(source_name, source_args,
                annotation == std::string::npos ? "" : text.substr(annotation), line, diags);
        }
        diags.merge(builtin_diagnostics);
        if (!f) { return false; }
        H::Constraint c;
        c.loc = at(line);
        c.formula = reified
                        ? H::mkOp(H::Op::EQ, {b, f}, at(line))
                        : half_reified
                              ? H::mkOp(H::Op::IMPLIES, {b, f}, at(line))
                              : f;
        model_->constraints.push_back(c);
        return true;
    }

    bool integerLowerBoundProven(const H::ExprPtr& value, bool strictly_positive) const {
        const auto sufficient = [&](const H::ExprPtr& bound) {
            if (!bound || bound->kind != H::ExprKind::LIT_INT) { return false; }
            const std::string& text = bound->name;
            const bool negative = !text.empty() && text.front() == '-';
            const bool nonzero = std::any_of(text.begin(), text.end(), [](char digit) {
                return digit >= '1' && digit <= '9';
            });
            return !(negative && nonzero) && (!strictly_positive || nonzero);
        };
        if (value->kind == H::ExprKind::LIT_INT) { return sufficient(value); }
        if (value->kind != H::ExprKind::IDENT) { return false; }
        for (const auto& declaration : model_->decls) {
            if (declaration.name == value->name && sufficient(declaration.lower_bound)) {
                return true;
            }
        }
        return false;
    }

    H::ExprPtr linear(const std::vector<Arg>& args, H::Op op, bool negate, int line,
                      Uir::Diagnostics& diags) {
        if (args.size() != 3) {
            diags.error(ErrorCode::E_PARSE, "a linear constraint takes three arguments",
                        at(line));
            return nullptr;
        }
        std::vector<std::string> coeffs, vars;
        if (!arrayItems(args[0], coeffs, line, diags)) { return nullptr; }
        if (!arrayItems(args[1], vars, line, diags)) { return nullptr; }
        if (coeffs.size() != vars.size()) {
            diags.error(ErrorCode::E_PARSE,
                        "a linear constraint's coefficient and variable arrays differ "
                        "in length", at(line));
            return nullptr;
        }
        std::vector<H::ExprPtr> addends;
        for (std::size_t k = 0; k < coeffs.size(); ++k) {
            H::ExprPtr cf = scalar(coeffs[k], line, diags);
            H::ExprPtr v = scalar(vars[k], line, diags);
            if (!cf || !v) { return nullptr; }
            addends.push_back(H::mkOp(H::Op::MUL, {cf, v}, at(line)));
        }
        H::ExprPtr lhs = addends.empty() ? H::mkInt(0, at(line))
                       : addends.size() == 1 ? addends.front()
                                             : H::mkOp(H::Op::ADD, addends, at(line));
        H::ExprPtr rhs = scalar(args[2].text, line, diags);
        if (!rhs) { return nullptr; }
        H::ExprPtr r = H::mkOp(op, {lhs, rhs}, at(line));
        return negate ? H::mkOp(H::Op::NOT, {r}, at(line)) : r;
    }

    H::ExprPtr builtin(const std::string& name, const std::vector<Arg>& args, int line,
                       Uir::Diagnostics& diags) {
        const auto sc = [&](std::size_t i) { return scalar(args[i].text, line, diags); };
        const auto arity = [&](std::size_t n) {
            if (args.size() == n) { return true; }
            diags.error(ErrorCode::E_PARSE,
                        "'" + name + "' takes " + std::to_string(n) + " argument(s), not "
                            + std::to_string(args.size()), at(line));
            return false;
        };
        const auto typed = [&](H::ExprPtr value, H::SortKind kind, bool parameter = false) {
            if (!value) { return H::ExprPtr{}; }
            if (value->sort.kind != kind
                || (parameter && value->kind != H::ExprKind::LIT_INT)) {
                diags.error(ErrorCode::E_TYPE,
                            name + " has an argument with the wrong type or parameter status",
                            at(line));
                return H::ExprPtr{};
            }
            return value;
        };
        const auto cells = [&](std::size_t i, std::vector<H::ExprPtr>& values,
                               H::SortKind kind = H::SortKind::INT,
                               bool parameter = false) {
            std::vector<std::string> items;
            if (!arrayItems(args[i], items, line, diags)) { return false; }
            const auto declaration = arrays_.find(args[i].text);
            if (declaration != arrays_.end() && declaration->second.sort.kind != kind) {
                diags.error(ErrorCode::E_TYPE, name + " has an array with the wrong element type",
                            at(line));
                return false;
            }
            values.reserve(items.size());
            for (const auto& item : items) {
                auto value = typed(scalar(item, line, diags), kind, parameter);
                if (!value) { return false; }
                values.push_back(std::move(value));
            }
            return true;
        };
        const auto conjunction = [&](std::vector<H::ExprPtr> terms) {
            return terms.empty() ? H::mkBool(true, at(line))
                : terms.size() == 1 ? terms.front()
                : H::mkOp(H::Op::AND, std::move(terms), at(line));
        };
        const auto integer = [](const H::ExprPtr& value) {
            std::string text = value->name.empty() ? std::to_string(value->int_value)
                                                    : value->name;
            if (text.front() == '+') { text.erase(text.begin()); }
            return mpz_class(text, 10);
        };
        const auto literal = [&](const mpz_class& value) {
            return H::mkInt(value.get_str(), at(line));
        };

        // Linear.
        if (name == "int_lin_eq" || name == "float_lin_eq") {
            return linear(args, H::Op::EQ, false, line, diags);
        }
        if (name == "int_lin_le" || name == "float_lin_le") {
            return linear(args, H::Op::LE, false, line, diags);
        }
        if (name == "int_lin_lt" || name == "float_lin_lt") {
            return linear(args, H::Op::LT, false, line, diags);
        }
        if (name == "int_lin_ne" || name == "float_lin_ne") {
            return linear(args, H::Op::EQ, true, line, diags);
        }

        // Comparison, in every type. The `_ne` family is a negated equality.
        static const std::unordered_map<std::string, H::Op> kCmp = {
            {"eq", H::Op::EQ}, {"le", H::Op::LE}, {"lt", H::Op::LT},
            {"ge", H::Op::GE}, {"gt", H::Op::GT},
        };
        for (const char* pre : {"int_", "bool_", "float_"}) {
            const std::string p = pre;
            if (name.rfind(p, 0) != 0) { continue; }
            const std::string tail = name.substr(p.size());
            const auto it = kCmp.find(tail);
            if (it != kCmp.end()) {
                if (!arity(2)) { return nullptr; }
                H::ExprPtr l = sc(0), r = sc(1);
                return (l && r) ? H::mkOp(it->second, {l, r}, at(line)) : nullptr;
            }
            if (tail == "ne") {
                if (!arity(2)) { return nullptr; }
                H::ExprPtr l = sc(0), r = sc(1);
                return (l && r) ? H::mkOp(H::Op::NOT,
                                          {H::mkOp(H::Op::EQ, {l, r}, at(line))}, at(line))
                                : nullptr;
            }
        }

        // Arithmetic, written as a relation because FlatZinc is flat:
        // `int_plus(a, b, c)` is `a + b = c`.
        static const std::unordered_map<std::string, H::Op> kArith = {
            {"int_plus", H::Op::ADD}, {"int_minus", H::Op::SUB},
            {"int_times", H::Op::MUL}, {"float_plus", H::Op::ADD},
            {"float_minus", H::Op::SUB}, {"float_times", H::Op::MUL},
            // §4.2: int_div and int_mod mean what MiniZinc's div and mod mean,
            // which is TRUNCATION toward zero with the remainder taking the
            // sign of the dividend -- not SMT-LIB's Euclidean pair. Naming
            // DIV_TRUNC here rather than DIV_EUCLID is the whole of the
            // difference on a negative dividend, and there is no default that
            // would have made this a no-op if it were left out.
            //
            // These are the reason `int_div` is dangerous in a way `int_plus`
            // is not: the name is innocuous, the arity is the same, and a
            // wrong convention shows up only on inputs a positive test does
            // not have.
            {"int_div", H::Op::DIV_TRUNC}, {"int_mod", H::Op::MOD_TRUNC},
            {"float_div", H::Op::DIV_REAL},
        };
        const auto ait = kArith.find(name);
        if (ait != kArith.end()) {
            if (!arity(3)) { return nullptr; }
            H::ExprPtr a = sc(0), b = sc(1), c = sc(2);
            if (!a || !b || !c) { return nullptr; }
            const bool partial = ait->second == H::Op::DIV_TRUNC
                              || ait->second == H::Op::MOD_TRUNC
                              || ait->second == H::Op::DIV_REAL;
            if (!partial) {
                return H::mkOp(H::Op::EQ,
                               {H::mkOp(ait->second, {a, b}, at(line)), c}, at(line));
            }
            used_partiality_ = true;
            const H::ExprPtr zero = ait->second == H::Op::DIV_REAL
                                        ? H::mkReal("0.0", at(line))
                                        : H::mkInt(0, at(line));
            H::ExprPtr domain = H::mkOp(
                H::Op::NOT, {H::mkOp(H::Op::EQ, {b, zero}, at(line))}, at(line));
            H::ExprPtr value = relational_.value(
                ait->second, {a, b}, at(line), std::move(domain));
            return relational_.predicate(H::Op::EQ, {value, c}, at(line));
        }
        if (name == "int_min" || name == "int_max") {
            if (!arity(3)) { return nullptr; }
            H::ExprPtr a = sc(0), b = sc(1), c = sc(2);
            if (!a || !b || !c) { return nullptr; }
            const H::Op pick = name == "int_min" ? H::Op::LE : H::Op::GE;
            return H::mkOp(H::Op::EQ,
                           {c, H::mkOp(H::Op::ITE, {H::mkOp(pick, {a, b}, at(line)), a, b},
                                       at(line))},
                           at(line));
        }
        if (name == "int_abs") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr a = sc(0), b = sc(1);
            if (!a || !b) { return nullptr; }
            return H::mkOp(H::Op::EQ,
                           {b, H::mkOp(H::Op::ITE,
                                       {H::mkOp(H::Op::GE, {a, H::mkInt(0, at(line))}, at(line)),
                                        a,
                                        H::mkOp(H::Op::SUB, {H::mkInt(0, at(line)), a}, at(line))},
                                       at(line))},
                           at(line));
        }

        // Boolean.
        if (name == "bool_not") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr a = sc(0), b = sc(1);
            return (a && b) ? H::mkOp(H::Op::EQ, {b, H::mkOp(H::Op::NOT, {a}, at(line))},
                                      at(line))
                            : nullptr;
        }
        if (name == "bool_and" || name == "bool_or" || name == "bool_xor") {
            if (!arity(3)) { return nullptr; }
            H::ExprPtr a = sc(0), b = sc(1), c = sc(2);
            if (!a || !b || !c) { return nullptr; }
            const H::Op op = name == "bool_and" ? H::Op::AND
                           : name == "bool_or"  ? H::Op::OR : H::Op::XOR;
            return H::mkOp(H::Op::EQ, {c, H::mkOp(op, {a, b}, at(line))}, at(line));
        }
        if (name == "bool_clause") {
            if (!arity(2)) { return nullptr; }
            std::vector<std::string> pos, neg;
            if (!arrayItems(args[0], pos, line, diags)) { return nullptr; }
            if (!arrayItems(args[1], neg, line, diags)) { return nullptr; }
            std::vector<H::ExprPtr> lits;
            for (const auto& v : pos) {
                H::ExprPtr e = scalar(v, line, diags);
                if (!e) { return nullptr; }
                lits.push_back(e);
            }
            for (const auto& v : neg) {
                H::ExprPtr e = scalar(v, line, diags);
                if (!e) { return nullptr; }
                lits.push_back(H::mkOp(H::Op::NOT, {e}, at(line)));
            }
            // An empty clause is FALSE, and mkOp throws on an empty list --
            // dimacs-cnf.md §4.1's trap, met again through a different door.
            if (lits.empty()) { return H::mkBool(false, at(line)); }
            if (lits.size() == 1) { return lits.front(); }
            return H::mkOp(H::Op::OR, std::move(lits), at(line));
        }

        // Coercion. §2.3's obligation: `i` is constrained to {0,1} as well as to
        // equal the coercion. The ITE alone already forces {0,1}; the bounds are
        // written on the declaration so that the *variable* carries the domain
        // and not only this one constraint.
        if (name == "bool2int") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr b = sc(0), i = sc(1);
            if (!b || !i) { return nullptr; }
            boundToUnit(args[1].text, line);
            return H::mkOp(H::Op::EQ,
                           {i, H::mkOp(H::Op::ITE, {b, H::mkInt(1, at(line)),
                                                    H::mkInt(0, at(line))}, at(line))},
                           at(line));
        }

        // Element. §4.3, and the obligation the whole document turns on.
        if (name == "array_int_element" || name == "array_var_int_element"
            || name == "array_bool_element" || name == "array_var_bool_element"
            || name == "array_float_element" || name == "array_var_float_element"
            || name == "array_set_element" || name == "array_var_set_element") {
            if (!arity(3)) { return nullptr; }
            std::vector<std::string> items;
            if (!arrayItems(args[1], items, line, diags)) { return nullptr; }
            const bool set_element = name == "array_set_element" || name == "array_var_set_element";
            if (items.empty() && !set_element) {
                diags.error(ErrorCode::E_PARSE, "an element constraint's array is empty",
                            at(line));
                return nullptr;
            }
            const auto declared_array = arrays_.find(args[1].text);
            if (set_element && declared_array != arrays_.end()
                && declared_array->second.sort.kind != H::SortKind::SET) {
                diags.error(ErrorCode::E_TYPE, "set element requires an array of sets", at(line));
                return nullptr;
            }
            H::ExprPtr idx = sc(0);
            H::ExprPtr out = set_element ? setExpr(args[2].text, line, diags) : sc(2);
            if (!idx || !out) { return nullptr; }
            if (set_element && idx->sort.kind != H::SortKind::INT) {
                diags.error(ErrorCode::E_TYPE, "a set element index must be an integer", at(line));
                return nullptr;
            }
            // With no cells every index is outside the relation. Validate
            // types first, then let reification/implication observe false.
            if (items.empty()) { return H::mkBool(false, at(line)); }
            // The ITE chain, innermost-last.
            H::ExprPtr chain;
            for (std::size_t k = items.size(); k-- > 0;) {
                H::ExprPtr v = set_element ? setExpr(items[k], line, diags)
                                         : scalar(items[k], line, diags);
                if (!v) { return nullptr; }
                if (!chain) { chain = v; continue; }
                chain = H::mkOp(
                    H::Op::ITE,
                    {H::mkOp(H::Op::EQ, {idx, H::mkInt(static_cast<long long>(k + 1),
                                                       at(line))}, at(line)),
                     v, chain},
                    at(line));
            }
            // **The obligation.** Without `1 <= i <= |as|` the chain's final
            // `else` silently defines as[i] for an out-of-range i -- a value the
            // model never gave it, and one a solver is free to choose.
            H::ExprPtr in_range = H::mkOp(
                H::Op::AND,
                {H::mkOp(H::Op::LE, {H::mkInt(1, at(line)), idx}, at(line)),
                 H::mkOp(H::Op::LE, {idx, H::mkInt(static_cast<long long>(items.size()),
                                                   at(line))}, at(line))},
                at(line));
            return H::mkOp(H::Op::AND,
                           {in_range, H::mkOp(H::Op::EQ, {out, chain}, at(line))},
                           at(line));
        }

        // Sets.
        if (name == "set_in") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr x = sc(0);
            if (!x) { return nullptr; }
            if (!args[1].is_array) {
                H::ExprPtr set = setExpr(args[1].text, line, diags);
                return set ? H::mkOp(H::Op::SET_MEMBER, {x, set}, at(line))
                           : nullptr;
            }
            std::vector<std::string> items;
            if (!arrayItems(args[1], items, line, diags, /*quiet=*/true)) {
                // Quiet above so this is the FIRST diagnostic and therefore the
                // one firstErrorCode() reports. The set argument is either a
                // range literal or a set VARIABLE (`var set of {1,3,5,7,9}`),
                // and this subset enumerates the members at parse time, which
                // neither permits.
                diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "set_in needs the set's members at parse time; '"
                                + args[1].text
                                + "' is a range literal or a set variable, and neither "
                                  "can be enumerated here",
                            at(line));
                return nullptr;
            }
            std::vector<H::ExprPtr> eqs;
            for (const auto& v : items) {
                H::ExprPtr e = scalar(v, line, diags);
                if (!e) { return nullptr; }
                eqs.push_back(H::mkOp(H::Op::EQ, {x, e}, at(line)));
            }
            if (eqs.empty()) { return H::mkBool(false, at(line)); }
            if (eqs.size() == 1) { return eqs.front(); }
            return H::mkOp(H::Op::OR, std::move(eqs), at(line));
        }

        if (name == "set_eq" || name == "set_ne" || name == "set_subset"
            || name == "set_superset") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr left = setExpr(args[0].text, line, diags);
            H::ExprPtr right = setExpr(args[1].text, line, diags);
            if (!left || !right) { return nullptr; }
            if (name == "set_subset") {
                return H::mkOp(H::Op::SET_SUBSET, {left, right}, at(line));
            }
            if (name == "set_superset") {
                return H::mkOp(H::Op::SET_SUBSET, {right, left}, at(line));
            }
            H::ExprPtr equality = H::mkOp(H::Op::EQ, {left, right}, at(line));
            return name == "set_ne"
                       ? H::mkOp(H::Op::NOT, {equality}, at(line))
                       : equality;
        }
        if (name == "set_card") {
            if (!arity(2)) { return nullptr; }
            H::ExprPtr set = setExpr(args[0].text, line, diags);
            H::ExprPtr count = sc(1);
            const auto carrier = set && set->kind == H::ExprKind::IDENT
                                     ? finite_set_carriers_.find(set->name)
                                     : finite_set_carriers_.end();
            if (set && carrier != finite_set_carriers_.end()) {
                // The declaration axiom asserts set is a subset of carrier,
                // so this intersection equals set. Carry the finite support
                // into the term for exact Z3 cardinality export, including
                // reified/implication uses whose equality is not asserted.
                set = H::mkOp(H::Op::SET_INTER, {set, carrier->second}, at(line));
            }
            return (set && count)
                       ? H::mkOp(H::Op::EQ,
                                 {count, H::mkOp(H::Op::SET_CARD, {set}, at(line))},
                                 at(line))
                       : nullptr;
        }
        if (name == "set_union" || name == "set_intersect"
            || name == "set_diff" || name == "set_symdiff") {
            if (!arity(3)) { return nullptr; }
            H::ExprPtr left = setExpr(args[0].text, line, diags);
            H::ExprPtr right = setExpr(args[1].text, line, diags);
            H::ExprPtr result = setExpr(args[2].text, line, diags);
            if (!left || !right || !result) { return nullptr; }
            H::ExprPtr value;
            if (name == "set_union") {
                value = H::mkOp(H::Op::SET_UNION, {left, right}, at(line));
            } else if (name == "set_intersect") {
                value = H::mkOp(H::Op::SET_INTER, {left, right}, at(line));
            } else if (name == "set_diff") {
                value = H::mkOp(H::Op::SET_MINUS, {left, right}, at(line));
            } else {
                H::ExprPtr lr = H::mkOp(H::Op::SET_MINUS, {left, right}, at(line));
                H::ExprPtr rl = H::mkOp(H::Op::SET_MINUS, {right, left}, at(line));
                value = H::mkOp(H::Op::SET_UNION, {lr, rl}, at(line));
            }
            return H::mkOp(H::Op::EQ, {result, value}, at(line));
        }

        // Boolean array reductions are relations between the result and the
        // fold. Empty arrays use the logical identities true/false/false.
        if (name == "array_bool_and" || name == "array_bool_or"
            || name == "array_bool_xor") {
            if (!arity(2)) { return nullptr; }
            std::vector<std::string> items;
            if (!arrayItems(args[0], items, line, diags)) { return nullptr; }
            H::ExprPtr result = sc(1);
            if (!result) { return nullptr; }
            std::vector<H::ExprPtr> values;
            for (const std::string& item : items) {
                H::ExprPtr value = scalar(item, line, diags);
                if (!value) { return nullptr; }
                values.push_back(std::move(value));
            }
            H::ExprPtr fold;
            if (values.empty()) {
                fold = H::mkBool(name == "array_bool_and", at(line));
            } else if (values.size() == 1) {
                fold = values.front();
            } else if (name == "array_bool_xor") {
                fold = values.front();
                for (std::size_t i = 1; i < values.size(); ++i) {
                    fold = H::mkOp(H::Op::XOR, {fold, values[i]}, at(line));
                }
            } else {
                const H::Op op = name == "array_bool_and" ? H::Op::AND : H::Op::OR;
                fold = H::mkOp(op, std::move(values), at(line));
            }
            return H::mkOp(H::Op::EQ, {result, fold}, at(line));
        }

        if (name == "array_int_minimum" || name == "array_int_maximum"
            || name == "array_float_minimum" || name == "array_float_maximum") {
            if (!arity(2)) { return nullptr; }
            std::vector<std::string> items;
            if (!arrayItems(args[1], items, line, diags)) { return nullptr; }
            if (items.empty()) {
                diags.error(ErrorCode::E_TYPE,
                            "'" + name + "' is undefined on an empty array", at(line));
                return nullptr;
            }
            H::ExprPtr result = sc(0);
            H::ExprPtr best = scalar(items.front(), line, diags);
            if (!result || !best) { return nullptr; }
            const bool minimum = name.find("minimum") != std::string::npos;
            for (std::size_t i = 1; i < items.size(); ++i) {
                H::ExprPtr value = scalar(items[i], line, diags);
                if (!value) { return nullptr; }
                H::ExprPtr choose_best = H::mkOp(
                    minimum ? H::Op::LE : H::Op::GE, {best, value}, at(line));
                best = H::mkOp(H::Op::ITE, {choose_best, best, value}, at(line));
            }
            return H::mkOp(H::Op::EQ, {result, best}, at(line));
        }

        if (name == "fzn_count_eq" || name == "fzn_count_eq_par") {
            if (!arity(3)) { return nullptr; }
            std::vector<std::string> items;
            if (!arrayItems(args[0], items, line, diags)) { return nullptr; }
            H::ExprPtr searched = sc(1);
            H::ExprPtr count = sc(2);
            if (!searched || !count) { return nullptr; }
            std::vector<H::ExprPtr> indicators;
            for (const std::string& item : items) {
                H::ExprPtr value = scalar(item, line, diags);
                if (!value) { return nullptr; }
                indicators.push_back(H::mkOp(
                    H::Op::ITE,
                    {H::mkOp(H::Op::EQ, {value, searched}, at(line)),
                     H::mkInt(1, at(line)), H::mkInt(0, at(line))},
                    at(line)));
            }
            H::ExprPtr sum = indicators.empty()
                                 ? H::mkInt(0, at(line))
                                 : indicators.size() == 1
                                       ? indicators.front()
                                       : H::mkOp(H::Op::ADD, std::move(indicators),
                                                 at(line));
            return H::mkOp(H::Op::EQ, {count, sum}, at(line));
        }

        if (name == "array_int_lt" || name == "array_int_lq") {
            if (!arity(2)) { return nullptr; }
            std::vector<std::string> left_items, right_items;
            if (!arrayItems(args[0], left_items, line, diags)
                || !arrayItems(args[1], right_items, line, diags)) {
                return nullptr;
            }
            if (left_items.size() != right_items.size()) {
                diags.error(ErrorCode::E_TYPE,
                            "lexicographic arrays must have the same length", at(line));
                return nullptr;
            }
            std::vector<H::ExprPtr> cases;
            std::vector<H::ExprPtr> equal_prefix;
            for (std::size_t i = 0; i < left_items.size(); ++i) {
                H::ExprPtr left = scalar(left_items[i], line, diags);
                H::ExprPtr right = scalar(right_items[i], line, diags);
                if (!left || !right) { return nullptr; }
                std::vector<H::ExprPtr> conjuncts = equal_prefix;
                conjuncts.push_back(H::mkOp(H::Op::LT, {left, right}, at(line)));
                cases.push_back(conjuncts.size() == 1
                                    ? conjuncts.front()
                                    : H::mkOp(H::Op::AND, std::move(conjuncts),
                                              at(line)));
                equal_prefix.push_back(
                    H::mkOp(H::Op::EQ, {left, right}, at(line)));
            }
            if (name == "array_int_lq") {
                cases.push_back(equal_prefix.empty()
                                    ? H::mkBool(true, at(line))
                                    : equal_prefix.size() == 1
                                          ? equal_prefix.front()
                                          : H::mkOp(H::Op::AND,
                                                    std::move(equal_prefix), at(line)));
            }
            if (cases.empty()) { return H::mkBool(false, at(line)); }
            return cases.size() == 1
                       ? cases.front()
                       : H::mkOp(H::Op::OR, std::move(cases), at(line));
        }

        // Offsets are value origins: foff is the first index of invf,
        // while invfoff is the first index of f (Gecode/Chuffed fzn_inverse).
        if (name == "inverse_offsets" || name == "gecode_inverse_offsets") {
            if (!arity(4)) { return nullptr; }
            std::vector<std::string> left, right;
            if (!arrayItems(args[0], left, line, diags)
                || !arrayItems(args[2], right, line, diags)) { return nullptr; }
            H::ExprPtr right_start = sc(1);
            H::ExprPtr left_start = sc(3);
            if (!left_start || !right_start) { return nullptr; }
            if (left_start->kind != H::ExprKind::LIT_INT
                || right_start->kind != H::ExprKind::LIT_INT) {
                diags.error(ErrorCode::E_TYPE,
                            name + " requires constant integer offsets", at(line));
                return nullptr;
            }
            std::vector<H::ExprPtr> terms{left_start, right_start,
                H::mkInt(std::to_string(left.size()), at(line))};
            for (const auto* side : {&left, &right}) {
                for (const auto& item : *side) {
                    H::ExprPtr value = scalar(item, line, diags);
                    if (!value) { return nullptr; }
                    if (value->sort.kind != H::SortKind::INT) {
                        diags.error(ErrorCode::E_TYPE,
                                    name + " requires integer array elements", at(line));
                        return nullptr;
                    }
                    terms.push_back(std::move(value));
                }
            }
            return H::mkGlobal("inverse", std::move(terms), at(line));
        }

        // Gecode's solver-library element keeps the source array's lower index
        // as an explicit offset while the FlatZinc array itself is 1-based.
        if (name == "gecode_int_element" || name == "gecode_bool_element") {
            if (!arity(4)) { return nullptr; }
            const auto kind = name == "gecode_bool_element" ? H::SortKind::BOOL
                                                             : H::SortKind::INT;
            H::ExprPtr index = typed(sc(0), H::SortKind::INT);
            H::ExprPtr offset_expr = typed(sc(1), H::SortKind::INT, true);
            H::ExprPtr result = typed(sc(3), kind);
            std::vector<H::ExprPtr> items;
            if (!index || !offset_expr || !result
                || !cells(2, items, kind)) {
                return nullptr;
            }
            if (items.empty()) { return H::mkBool(false, at(line)); }
            const mpz_class offset = integer(offset_expr);
            const auto zero = kind == H::SortKind::BOOL ? H::mkBool(false, at(line))
                                                         : H::mkInt(0, at(line));
            auto contents = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), zero->sort), zero, at(line));
            for (std::size_t i = 0; i < items.size(); ++i) {
                const mpz_class label = offset + mpz_class(std::to_string(i), 10);
                contents = H::mkOp(H::Op::STORE,
                                  {contents, literal(label), items[i]}, at(line));
            }
            const mpz_class upper = offset + mpz_class(std::to_string(items.size() - 1), 10);
            // The selected default is never observable: out-of-range indices
            // make the whole relation false, including under reification.
            return conjunction({
                H::mkOp(H::Op::LE, {offset_expr, index}, at(line)),
                H::mkOp(H::Op::LE, {index, literal(upper)}, at(line)),
                H::mkOp(H::Op::EQ,
                        {result, H::mkOp(H::Op::SELECT, {contents, index}, at(line))}, at(line))});
        }

        if (name == "gecode_int_element2d") {
            if (!arity(6)) { return nullptr; }
            auto row = typed(sc(0), H::SortKind::INT);
            auto column = typed(sc(1), H::SortKind::INT);
            auto result = typed(sc(5), H::SortKind::INT);
            std::vector<H::ExprPtr> values;
            if (!row || !column || !result || !cells(2, values)) { return nullptr; }
            // MiniZinc's integer array index sets are contiguous. Keep the
            // declared lower bounds, including negative or wide labels.
            const auto indexRange = [&](std::size_t i, mpz_class& lower, mpz_class& upper) {
                std::string text = args[i].text;
                if (!resolveSetParameter(text, line, diags)) { return false; }
                const auto fail = [&]() {
                    diags.error(ErrorCode::E_TYPE,
                                name + " requires constant contiguous integer index sets",
                                at(line));
                    return false;
                };
                const auto dots = text.find("..");
                if (dots != std::string::npos) {
                    const auto lo = trim(text.substr(0, dots));
                    const auto hi = trim(text.substr(dots + 2));
                    if (!isIntText(lo) || !isIntText(hi)) { return fail(); }
                    lower = integer(H::mkInt(lo, at(line)));
                    upper = integer(H::mkInt(hi, at(line)));
                    return true;
                }
                if (text.size() < 2 || text.front() != '{' || text.back() != '}') {
                    return fail();
                }
                const auto body = trim(text.substr(1, text.size() - 2));
                if (!body.empty() && body.back() == ',') { return fail(); }
                std::set<mpz_class> members;
                for (const auto& token : topCommas(body)) {
                    const auto value = trim(token);
                    if (!isIntText(value)) { return fail(); }
                    members.insert(integer(H::mkInt(value, at(line))));
                }
                if (members.empty()) { lower = 1; upper = 0; return true; }
                lower = *members.begin();
                upper = *members.rbegin();
                return upper - lower + 1 == mpz_class(std::to_string(members.size()), 10)
                    ? true : fail();
            };
            mpz_class row_lo, row_hi, column_lo, column_hi;
            if (!indexRange(3, row_lo, row_hi) || !indexRange(4, column_lo, column_hi)) {
                return nullptr;
            }
            mpz_class row_count = 0, column_count = 0;
            if (row_hi >= row_lo) { row_count = row_hi - row_lo + 1; }
            if (column_hi >= column_lo) { column_count = column_hi - column_lo + 1; }
            if (row_count * column_count != mpz_class(std::to_string(values.size()), 10)) {
                diags.error(ErrorCode::E_TYPE, name + " dimensions do not match its flattened array",
                            at(line));
                return nullptr;
            }
            if (values.empty()) { return H::mkBool(false, at(line)); }
            auto contents = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), H::Sort::integer()),
                H::mkInt(0, at(line)), at(line));
            for (std::size_t i = 0; i < values.size(); ++i) {
                contents = H::mkOp(H::Op::STORE,
                    {contents, H::mkInt(std::to_string(i), at(line)), values[i]}, at(line));
            }
            const auto row_index = H::mkOp(H::Op::SUB, {row, literal(row_lo)}, at(line));
            const auto column_index = H::mkOp(H::Op::SUB, {column, literal(column_lo)}, at(line));
            const auto index = H::mkOp(H::Op::ADD,
                {H::mkOp(H::Op::MUL, {row_index, literal(column_count)}, at(line)), column_index}, at(line));
            return conjunction({
                H::mkOp(H::Op::LE, {literal(row_lo), row}, at(line)),
                H::mkOp(H::Op::LE, {row, literal(row_hi)}, at(line)),
                H::mkOp(H::Op::LE, {literal(column_lo), column}, at(line)),
                H::mkOp(H::Op::LE, {column, literal(column_hi)}, at(line)),
                H::mkOp(H::Op::EQ,
                    {result, H::mkOp(H::Op::SELECT, {contents, index}, at(line))}, at(line))});
        }

        if (name == "gecode_maximum_arg_int_offset") {
            if (!arity(3)) { return nullptr; }
            std::vector<H::ExprPtr> values;
            auto offset = typed(sc(1), H::SortKind::INT, true);
            auto result = typed(sc(2), H::SortKind::INT);
            if (!offset || !result || !cells(0, values)) { return nullptr; }
            // Gecode uses the first maximum, not an arbitrary maximizing
            // position. A balanced tournament shares values and indices and
            // keeps ties in the earlier half. Gecode rejects an empty array.
            if (values.empty()) {
                diags.error(ErrorCode::E_TYPE, name + " requires a nonempty array", at(line));
                return nullptr;
            }
            std::vector<H::ExprPtr> positions;
            for (std::size_t i = 0; i < values.size(); ++i) {
                positions.push_back(literal(integer(offset) + mpz_class(std::to_string(i), 10)));
            }
            while (values.size() > 1) {
                std::vector<H::ExprPtr> next_values, next_positions;
                for (std::size_t i = 0; i < values.size(); i += 2) {
                    if (i + 1 == values.size()) {
                        next_values.push_back(values[i]);
                        next_positions.push_back(positions[i]);
                        continue;
                    }
                    auto left = H::mkOp(H::Op::GE, {values[i], values[i + 1]}, at(line));
                    next_values.push_back(H::mkOp(H::Op::ITE,
                        {left, values[i], values[i + 1]}, at(line)));
                    next_positions.push_back(H::mkOp(H::Op::ITE,
                        {left, positions[i], positions[i + 1]}, at(line)));
                }
                values = std::move(next_values);
                positions = std::move(next_positions);
            }
            return H::mkOp(H::Op::EQ, {result, positions.front()}, at(line));
        }

        if (name == "gecode_regular") {
            if (!arity(6)) { return nullptr; }
            std::vector<H::ExprPtr> word, transitions;
            auto states = typed(sc(1), H::SortKind::INT, true);
            auto alphabet = typed(sc(2), H::SortKind::INT, true);
            auto start = typed(sc(4), H::SortKind::INT, true);
            if (!states || !alphabet || !start || !cells(0, word)
                || !cells(3, transitions, H::SortKind::INT, true)) { return nullptr; }
            const auto table_declaration = arrays_.find(args[3].text);
            if (table_declaration != arrays_.end() && table_declaration->second.is_variable) {
                diags.error(ErrorCode::E_TYPE, name + " requires a parameter transition array", at(line));
                return nullptr;
            }
            const auto bad = [&](const std::string& reason) -> H::ExprPtr {
                diags.error(ErrorCode::E_TYPE, name + ": " + reason, at(line));
                return nullptr;
            };
            const mpz_class q = integer(states), symbols = integer(alphabet), q0 = integer(start);
            if (q <= 0 || symbols <= 0 || q0 < 1 || q0 > q) {
                return bad("Q and S must be positive and q0 must be in 1..Q");
            }
            if (q * symbols != mpz_class(std::to_string(transitions.size()), 10)) {
                return bad("transition array must contain exactly Q*S entries");
            }
            for (const auto& destination : transitions) {
                if (integer(destination) < 0 || integer(destination) > q) {
                    return bad("transition destinations must be in 0..Q");
                }
            }
            // Validate finals as a parameter set without narrowing any literal
            // to a machine integer or expanding an unbounded range.
            std::string finals = args[5].text;
            if (!resolveSetParameter(finals, line, diags)) { return nullptr; }
            std::set<mpz_class> final_states;
            const auto dots = finals.find("..");
            if (dots != std::string::npos) {
                const auto lo_text = trim(finals.substr(0, dots));
                const auto hi_text = trim(finals.substr(dots + 2));
                if (!isIntText(lo_text) || !isIntText(hi_text)) {
                    return bad("F must be a parameter integer set");
                }
                const mpz_class lo = integer(H::mkInt(lo_text, at(line)));
                const mpz_class hi = integer(H::mkInt(hi_text, at(line)));
                if (lo <= hi) {
                    if (lo < 1 || hi > q) { return bad("accepting states must be in 1..Q"); }
                    for (mpz_class state = lo; state <= hi; ++state) { final_states.insert(state); }
                }
            } else if (finals.size() >= 2 && finals.front() == '{' && finals.back() == '}') {
                const auto body = trim(finals.substr(1, finals.size() - 2));
                if (!body.empty() && body.back() == ',') { return bad("malformed accepting set"); }
                for (const auto& token : topCommas(body)) {
                    const auto text = trim(token);
                    if (!isIntText(text)) { return bad("F must be a parameter integer set"); }
                    const mpz_class value = integer(H::mkInt(text, at(line)));
                    if (value < 1 || value > q) { return bad("accepting states must be in 1..Q"); }
                    final_states.insert(value);
                }
            } else { return bad("F must be a parameter integer set"); }

            // Every missing edge (including a symbol outside 1..S) reaches
            // the absorbing rejecting state 0. Nested arrays avoid arithmetic
            // key collisions between invalid symbols and another state's row.
            const auto row_sort = H::Sort::array(H::Sort::integer(), H::Sort::integer());
            auto sink = H::mkConstArray(row_sort, H::mkInt(0, at(line)), at(line));
            auto table = H::mkConstArray(H::Sort::array(H::Sort::integer(), row_sort), sink, at(line));
            std::size_t position = 0;
            for (mpz_class state = 1; state <= q; ++state) {
                auto row = sink;
                for (mpz_class symbol = 1; symbol <= symbols; ++symbol) {
                    auto destination = transitions[position++];
                    if (integer(destination) != 0) {
                        row = H::mkOp(H::Op::STORE, {row, literal(symbol), destination}, at(line));
                    }
                }
                table = H::mkOp(H::Op::STORE, {table, literal(state), row}, at(line));
            }
            auto accepting = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), H::Sort::boolean()), H::mkBool(false, at(line)), at(line));
            for (const auto& state : final_states) {
                accepting = H::mkOp(H::Op::STORE,
                    {accepting, literal(state), H::mkBool(true, at(line))}, at(line));
            }
            auto state = start;
            for (const auto& symbol : word) {
                state = H::mkOp(H::Op::SELECT,
                    {H::mkOp(H::Op::SELECT, {table, state}, at(line)), symbol}, at(line));
            }
            return H::mkOp(H::Op::SELECT, {accepting, state}, at(line));
        }

        if (name == "fzn_increasing_int") {
            if (!arity(1)) { return nullptr; }
            std::vector<H::ExprPtr> values, terms;
            if (!cells(0, values)) { return nullptr; }
            for (std::size_t i = 1; i < values.size(); ++i) {
                terms.push_back(H::mkOp(H::Op::LE, {values[i - 1], values[i]}, at(line)));
            }
            return conjunction(std::move(terms));
        }

        if (name == "fzn_nvalue") {
            if (!arity(2)) { return nullptr; }
            auto count = typed(sc(0), H::SortKind::INT);
            std::vector<H::ExprPtr> values, first;
            if (!count || !cells(1, values)) { return nullptr; }
            auto seen = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), H::Sort::boolean()),
                H::mkBool(false, at(line)), at(line));
            const auto zero = H::mkInt(0, at(line));
            const auto one = H::mkInt(1, at(line));
            // Each immutable prefix is shared: one lookup and update per
            // value, without a quadratic expansion of pairwise inequalities.
            for (const auto& value : values) {
                first.push_back(H::mkOp(H::Op::ITE,
                    {H::mkOp(H::Op::SELECT, {seen, value}, at(line)), zero, one}, at(line)));
                seen = H::mkOp(H::Op::STORE,
                              {seen, value, H::mkBool(true, at(line))}, at(line));
            }
            auto total = first.empty() ? zero : first.size() == 1 ? first.front()
                : H::mkOp(H::Op::ADD, std::move(first), at(line));
            return H::mkOp(H::Op::EQ, {count, total}, at(line));
        }

        if (name == "gecode_global_cardinality"
            || name == "fzn_global_cardinality_low_up_closed") {
            const bool closed = name == "fzn_global_cardinality_low_up_closed";
            if (!arity(closed ? 4 : 3)) { return nullptr; }
            std::vector<H::ExprPtr> values, cover, counts, upper;
            if (!cells(0, values) || !cells(1, cover, H::SortKind::INT, true)
                || !cells(2, counts, H::SortKind::INT, closed)
                || (closed && !cells(3, upper, H::SortKind::INT, true))) {
                return nullptr;
            }
            if (cover.size() != counts.size() || (closed && cover.size() != upper.size())) {
                diags.error(ErrorCode::E_TYPE, name + " requires equally sized cover and count arrays",
                            at(line));
                return nullptr;
            }
            std::unordered_set<std::string> distinct;
            std::vector<bool> first_cover;
            for (const auto& value : cover) {
                first_cover.push_back(distinct.insert(integer(value).get_str()).second);
            }
            const auto zero = H::mkInt(0, at(line));
            const auto one = H::mkInt(1, at(line));
            auto histogram = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), H::Sort::integer()), zero, at(line));
            for (const auto& value : values) {
                const auto previous = H::mkOp(H::Op::SELECT, {histogram, value}, at(line));
                const auto next = H::mkOp(H::Op::ADD, {previous, one}, at(line));
                histogram = H::mkOp(H::Op::STORE, {histogram, value, next}, at(line));
            }
            std::vector<H::ExprPtr> terms, covered_counts;
            for (std::size_t i = 0; i < cover.size(); ++i) {
                auto count = H::mkOp(H::Op::SELECT, {histogram, cover[i]}, at(line));
                if (closed) {
                    terms.push_back(H::mkOp(H::Op::LE, {counts[i], count}, at(line)));
                    terms.push_back(H::mkOp(H::Op::LE, {count, upper[i]}, at(line)));
                    if (first_cover[i]) { covered_counts.push_back(count); }
                } else {
                    terms.push_back(H::mkOp(H::Op::EQ, {counts[i], count}, at(line)));
                }
            }
            if (closed) {
                // Distinct cover values partition the counted occurrences.
                // Repeated labels retain all their bounds/count equalities,
                // but contribute once to this membership check.
                // Equality to |x| therefore enforces membership for every x,
                // without constructing |x| times |cover| disjunctions.
                auto covered = covered_counts.empty() ? zero
                    : covered_counts.size() == 1 ? covered_counts.front()
                    : H::mkOp(H::Op::ADD, std::move(covered_counts), at(line));
                terms.push_back(H::mkOp(H::Op::EQ,
                    {covered, H::mkInt(std::to_string(values.size()), at(line))}, at(line)));
            }
            return conjunction(std::move(terms));
        }

        if (name == "gecode_bin_packing_load") {
            if (!arity(4)) { return nullptr; }
            std::vector<H::ExprPtr> loads, bins, weights;
            auto offset_expr = typed(sc(3), H::SortKind::INT, true);
            if (!offset_expr || !cells(0, loads) || !cells(1, bins)
                || !cells(2, weights, H::SortKind::INT, true)) { return nullptr; }
            if (bins.size() != weights.size()) {
                diags.error(ErrorCode::E_TYPE, name + " requires one weight per item", at(line));
                return nullptr;
            }
            for (const auto& weight : weights) {
                if (integer(weight) < 0) {
                    diags.error(ErrorCode::E_TYPE, name + " requires nonnegative weights", at(line));
                    return nullptr;
                }
            }
            if (loads.empty()) { return H::mkBool(bins.empty(), at(line)); }
            const auto offset = integer(offset_expr);
            const mpz_class upper = offset + mpz_class(std::to_string(loads.size() - 1), 10);
            std::vector<H::ExprPtr> terms;
            const auto zero = H::mkInt(0, at(line));
            auto histogram = H::mkConstArray(
                H::Sort::array(H::Sort::integer(), H::Sort::integer()), zero, at(line));
            for (std::size_t i = 0; i < bins.size(); ++i) {
                // Zero-weight items still need valid bin labels.
                terms.push_back(H::mkOp(H::Op::LE, {offset_expr, bins[i]}, at(line)));
                terms.push_back(H::mkOp(H::Op::LE, {bins[i], literal(upper)}, at(line)));
                if (integer(weights[i]) == 0) { continue; }
                const auto previous = H::mkOp(H::Op::SELECT, {histogram, bins[i]}, at(line));
                const auto next = H::mkOp(H::Op::ADD, {previous, weights[i]}, at(line));
                histogram = H::mkOp(H::Op::STORE, {histogram, bins[i], next}, at(line));
            }
            for (std::size_t i = 0; i < loads.size(); ++i) {
                const mpz_class label = offset + mpz_class(std::to_string(i), 10);
                auto load = H::mkOp(H::Op::SELECT, {histogram, literal(label)}, at(line));
                terms.push_back(H::mkOp(H::Op::EQ, {loads[i], load}, at(line)));
            }
            return conjunction(std::move(terms));
        }

        if (name == "gecode_circuit") {
            if (!arity(2)) { return nullptr; }
            auto offset = typed(sc(0), H::SortKind::INT, true);
            std::vector<H::ExprPtr> successors;
            if (!offset || !cells(1, successors)) { return nullptr; }
            if (integer(offset) < 0 || successors.empty()) {
                diags.error(ErrorCode::E_TYPE,
                            name + " requires a nonnegative offset and a nonempty successor array",
                            at(line));
                return nullptr;
            }
            // Gecode permits the singleton self-loop, unlike the shared HIR
            // circuit relation's no-self-loop convention.
            if (successors.size() == 1) {
                return H::mkOp(H::Op::EQ, {successors.front(), offset}, at(line));
            }
            std::vector<H::ExprPtr> normalized{H::mkInt(0, at(line))};
            normalized.reserve(successors.size() + 1);
            for (const auto& successor : successors) {
                normalized.push_back(H::mkOp(H::Op::SUB, {successor, offset}, at(line)));
            }
            return H::mkGlobal("circuit", std::move(normalized), at(line));
        }

        // The official Gecode FlatZinc library uses these solver-specific
        // spellings for standard cumulative and strict two-dimensional diffn.
        if (name == "gecode_cumulatives" || name == "gecode_nooverlap") {
            if (!arity(4)) { return nullptr; }
            const bool cumulative = name == "gecode_cumulatives";
            const std::size_t array_count = cumulative ? 3 : 4;
            std::vector<std::vector<H::ExprPtr>> columns(array_count);
            std::size_t length = 0;
            for (std::size_t column = 0; column < array_count; ++column) {
                std::vector<std::string> items;
                if (!arrayItems(args[column], items, line, diags)) { return nullptr; }
                const auto declared = arrays_.find(args[column].text);
                if (declared != arrays_.end() && declared->second.sort.kind != H::SortKind::INT) {
                    diags.error(ErrorCode::E_TYPE, name + " requires integer arrays", at(line));
                    return nullptr;
                }
                if (column == 0) { length = items.size(); }
                else if (items.size() != length) {
                    diags.error(ErrorCode::E_TYPE, name + " requires arrays of equal length", at(line));
                    return nullptr;
                }
                for (const auto& item : items) {
                    auto value = scalar(item, line, diags);
                    if (!value) { return nullptr; }
                    if (value->sort.kind != H::SortKind::INT) {
                        diags.error(ErrorCode::E_TYPE, name + " requires integer arrays", at(line));
                        return nullptr;
                    }
                    columns[column].push_back(std::move(value));
                }
            }
            std::vector<H::ExprPtr> terms;
            if (cumulative) {
                auto capacity = sc(3);
                if (!capacity) { return nullptr; }
                if (capacity->sort.kind != H::SortKind::INT) {
                    diags.error(ErrorCode::E_TYPE, name + " requires an integer capacity", at(line));
                    return nullptr;
                }
                // Gecode's registry implements these two cardinalities before
                // dispatching to a scheduling propagator. In particular a
                // zero-duration singleton still requires height <= capacity.
                if (length == 0) { return H::mkBool(true, at(line)); }
                if (length == 1) {
                    return H::mkOp(H::Op::LE, {columns[2][0], capacity}, at(line));
                }
                // Positive durations and nonnegative resource demands make
                // the scheduling dispatches agree with the shared cumulative
                // relation. Zero-duration vendor edge cases need a separate
                // certificate; never strengthen them with an assumed domain.
                for (std::size_t row = 0; row < length; ++row) {
                    if (!integerLowerBoundProven(columns[1][row], true)
                        || !integerLowerBoundProven(columns[2][row], false)) {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "gecode_cumulatives with multiple tasks requires declared "
                            "positive durations and nonnegative demands", at(line));
                        return nullptr;
                    }
                }
                terms.push_back(std::move(capacity));
            } else {
                for (std::size_t row = 0; row < length; ++row) {
                    if (!integerLowerBoundProven(columns[1][row], false)
                        || !integerLowerBoundProven(columns[3][row], false)) {
                        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                            "gecode_nooverlap requires declared nonnegative sizes", at(line));
                        return nullptr;
                    }
                }
                terms.push_back(H::mkInt(2, at(line)));
            }
            for (std::size_t row = 0; row < length; ++row) {
                for (std::size_t column = 0; column < array_count; ++column) {
                    terms.push_back(columns[column][row]);
                }
            }
            // Strict diffn preserves separation even when one dimension is
            // zero; diffn_nonstrict would silently weaken these source calls.
            return H::mkGlobal(cumulative ? "cumulative" : "diffn", std::move(terms), at(line));
        }

        // The Gecode table is a row-major flattening of parameter tuples.
        // Share its closed relation, not a formula capturing the first call's
        // variables: generated models reuse large tables with different scopes.
        if (name == "gecode_table_int") {
            if (!arity(2)) { return nullptr; }
            std::vector<H::ExprPtr> variables;
            std::vector<std::string> table;
            if (!cells(0, variables)
                || !arrayItems(args[1], table, line, diags)) {
                return nullptr;
            }
            const auto declaration = arrays_.find(args[1].text);
            if (declaration != arrays_.end()
                && (declaration->second.sort.kind != H::SortKind::INT
                    || declaration->second.is_variable)) {
                diags.error(ErrorCode::E_TYPE,
                            "gecode_table_int requires a parameter integer table", at(line));
                return nullptr;
            }
            if (variables.empty() || table.size() % variables.size() != 0) {
                diags.error(ErrorCode::E_TYPE,
                            "gecode_table_int's flattened table length must be a "
                            "multiple of its tuple width",
                            at(line));
                return nullptr;
            }
            // Resolve parameter aliases and normalize arbitrary-size integers.
            // Length delimiters plus width make the cache key unambiguous;
            // equal flattened values at different tuple widths are not equal
            // relations. Validate all supplied operands even for an empty table.
            std::string key = std::to_string(variables.size()) + ";";
            for (auto& cell : table) {
                const auto value = typed(scalar(cell, line, diags), H::SortKind::INT, true);
                if (!value) { return nullptr; }
                cell = integer(value).get_str();
                key += std::to_string(cell.size()) + ":" + cell;
            }
            if (table.empty()) { return H::mkBool(false, at(line)); }
            const auto shared = table_functions_.find(key);
            if (shared != table_functions_.end()) {
                return H::mkApply(shared->second, H::Sort::boolean(),
                                  std::move(variables), at(line));
            }
            H::FunDecl definition;
            do {
                definition.name = "__somt_fzn_table_" + std::to_string(next_table_function_++);
            } while (src_.find(definition.name) != std::string::npos);
            definition.result = H::Sort::boolean();
            definition.loc = at(line);
            definition.auxiliary = true;
            std::vector<H::ExprPtr> formals;
            for (std::size_t column = 0; column < variables.size(); ++column) {
                const std::string binder = "column_" + std::to_string(column);
                definition.params.push_back(H::Sort::integer());
                definition.binders.push_back({binder, H::Sort::integer()});
                formals.push_back(H::mkBoundVar(binder, H::Sort::integer(), at(line)));
            }
            // A column/value test is also immutable and shared across rows.
            // This keeps repeated values from recreating the same HIR nodes.
            std::vector<std::unordered_map<std::string, H::ExprPtr>> tests(variables.size());
            std::vector<H::ExprPtr> rows;
            rows.reserve(table.size() / variables.size());
            for (std::size_t base = 0; base < table.size(); base += variables.size()) {
                std::vector<H::ExprPtr> row;
                row.reserve(variables.size());
                for (std::size_t column = 0; column < variables.size(); ++column) {
                    const auto& value = table[base + column];
                    auto found = tests[column].find(value);
                    if (found == tests[column].end()) {
                        found = tests[column].emplace(value, H::mkOp(H::Op::EQ,
                            {formals[column], H::mkInt(value, at(line))}, at(line))).first;
                    }
                    row.push_back(found->second);
                }
                rows.push_back(conjunction(std::move(row)));
            }
            definition.body = rows.size() == 1
                       ? rows.front()
                       : H::mkOp(H::Op::OR, std::move(rows), at(line));
            const auto function = definition.name;
            model_->funs.push_back(std::move(definition));
            table_functions_.emplace(std::move(key), function);
            return H::mkApply(function, H::Sort::boolean(), std::move(variables), at(line));
        }

        // Globals. all_different is routed through ExprKind::GLOBAL.
        //
        // It was decomposed here instead, on the stated reason that "the HIR's
        // global takes an ARRAY and a FlatZinc argument is a list of
        // variables". The premise was false: `alldifferent` has had TWO shapes
        // since typecheck.cpp gained the rule, dispatched on the first
        // argument's sort, and the list shape exists precisely because
        // `alldifferent([x, y, z])` has no array to point at.
        //
        // The workaround was honest about its cost -- it recorded in the
        // open-questions log that the profile axis was unreachable from here --
        // which is what makes it worth naming: a documented limitation is still
        // a limitation nobody rechecked, and this one had stopped being true.
        if (name == "all_different_int" || name == "alldifferent"
            || name == "fzn_all_different_int") {
            if (!arity(1)) { return nullptr; }
            std::vector<std::string> items;
            if (!arrayItems(args[0], items, line, diags)) { return nullptr; }
            std::vector<H::ExprPtr> terms;
            terms.reserve(items.size());
            for (const std::string& v : items) {
                H::ExprPtr t = scalar(v, line, diags);
                if (!t) { return nullptr; }
                terms.push_back(std::move(t));
            }
            // The list shape's minimum arity is two (typecheck.cpp). Below it
            // the constraint is vacuous, and FlatZinc permits the scope.
            if (terms.size() < 2) { return H::mkBool(true, at(line)); }
            return H::mkGlobal("alldifferent", std::move(terms), at(line));
        }

        // **The governing obligation.** The catalogue is open, so a frontend
        // meets unknown names as a matter of course, and skipping one drops a
        // constraint: more solutions, and the answer looks like success.
        diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                    "builtin '" + name + "' is not implemented; skipping it would drop "
                    "a constraint and weaken the model",
                    at(line));
        return nullptr;
    }

    /** Give a bool2int output variable its {0,1} domain if it has none. */
    void boundToUnit(const std::string& name, int line) {
        for (auto& d : model_->decls) {
            if (d.name != name) { continue; }
            if (!d.lower_bound) { d.lower_bound = H::mkInt(0, at(line)); }
            if (!d.upper_bound) { d.upper_bound = H::mkInt(1, at(line)); }
            return;
        }
    }

    std::string src_;
    std::string file_;
    H::ConstraintModelPtr model_;
    bool solve_seen_ = false;
    std::unordered_map<std::string, H::Sort>   scalars_;
    std::unordered_map<std::string, Decl>      arrays_;
    std::unordered_map<std::string, std::string> params_;
    std::unordered_map<std::string, H::Sort> parameter_sorts_;
    std::unordered_set<std::string> finite_sets_;
    std::unordered_map<std::string, H::ExprPtr> finite_set_carriers_;
    std::unordered_map<std::string, std::string> table_functions_;
    std::size_t next_table_function_ = 0;
    std::vector<PendingInitializer> pending_initializers_;
    std::vector<Uir::Sem::Observable> observables_;
    std::vector<H::ExprPtr> implicit_axioms_;
    Uir::Sem::RelationalBuilder relational_;
    bool used_partiality_ = false;
};

class FlatZincLanguage : public Language {
public:
    ModuleOutcome parseModule(const SourceUnit& unit) override {
        ModuleOutcome out;
        std::string source;
        if (!readModuleSource(unit, source, out.diagnostics)) { return out; }
        FznParser parser(source, unit.main_path.empty() ? unit.display_name : unit.main_path);
        out.module = parser.parseModule(out.diagnostics);
        return out;
    }

    FlatZincLanguage() {
        // Linear, comparison, arithmetic, Boolean, coercion, element, set_in,
        // all_different, and reification. The catalogue is open, so this number
        // is about the groups flatzinc.md §2.3 tabulates and not about the
        // language -- which has no closed count.
        coverage_.total = 10;
        coverage_.supported = 9;
        coverage_.missing = {"globals outside the documented exact subset"};
    }

    std::string id() const override { return "flatzinc"; }
    std::string displayName() const override { return "FlatZinc"; }
    std::string version() const override { return "1.6"; }
    std::vector<std::string> extensions() const override { return {".fzn"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions&) override {
        ParseOutcome out;
        std::string src = unit.inline_source;
        if (src.empty()) {
            std::error_code ec;
            if (std::filesystem::is_directory(unit.main_path, ec)) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "'" + unit.main_path + "' is a directory");
                return out;
            }
            std::ifstream in(unit.main_path, std::ios::binary);
            if (!in) {
                out.diagnostics.error(ErrorCode::E_IO,
                                      "cannot open '" + unit.main_path + "'");
                return out;
            }
            std::ostringstream ss;
            ss << in.rdbuf();
            src = ss.str();
        }
        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            FznParser p(src, name);
            out.model = p.parse(out.diagnostics);
            if (out.model) {
                if (p.usedRelationalPartiality()) {
                    out.report.addChoice(
                        {name, "partial-expression", "typed-relational-definedness",
                         Uir::Fidelity::exact(),
                         "FlatZinc division is a partial relation; a nonzero divisor "
                         "guard is conjoined with the defining relation"});
                }
                Uir::Sem::TranslationContract contract =
                    Uir::Sem::flatZincToRelationalContract(
                        *out.model, out.report.fidelity(), p.modelProjection());
                contract.target_axioms.insert(contract.target_axioms.end(),
                                              p.implicitAxioms().begin(),
                                              p.implicitAxioms().end());
                out.semantics.add(std::move(contract));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("flatzinc frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkFlatZincLanguage() { return std::make_shared<FlatZincLanguage>(); }

} // namespace SOMTParser::Lang
