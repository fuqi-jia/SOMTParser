/* -*- Source -*-
 * AIGER frontend — ASCII `aag`, bounded model checking of an and-inverter graph.
 *
 * The format is docs/languages/aiger.md; its `implicit-constraints` block is
 * the specification this file implements, and each entry has a fixture in
 * languages/aiger/instances.
 *
 * AIGER is BTOR2 with one-bit words and no arrays, so the unrolling is the same
 * shape (`languages/btor2/src/btor2.cpp`, and option C of
 * `docs/design-transition-system.md`): the transition system lives here, the
 * product is an ordinary ConstraintModel, and an EncodingChoice carrying
 * `underApprox(Bound{BMC_DEPTH, k})` records both the shape and the bound.
 *
 * **The format's one piece of bit-twiddling, and its most likely first bug.** A
 * literal is `2*v` for the positive occurrence of variable `v` and `2*v + 1`
 * for its negation. **The low bit is a negation flag, not part of the index.**
 * A reader that treats literals as indices silently reads a circuit in which
 * every negated occurrence refers to the wrong variable -- a different circuit
 * that parses, unrolls and answers.
 *
 * Literal 0 is constant FALSE and literal 1 is constant TRUE. Variable index 0
 * does not exist, so `0` and `1` are not variables 0 and 0-negated: they are
 * the constants, and reading them as a variable invents one.
 *
 * **Latch reset values are a version question with a recorded answer.** Under
 * 1.9 a latch may declare `0`, `1`, or its own literal meaning *uninitialised*.
 * If the reset column is absent, both the inherited format and 1.9 define the
 * default as 0. This is a language-defined default, not evidence that the file
 * predates 1.9 and not an implementation assumption.
 *
 * **Every latch gets a transition**, not only the ones an encoder finds
 * interesting: `NEXT(l) = <its next literal>` for all of them, or the latch
 * goes free and the property becomes trivially reachable.
 *
 * The binary `aig` encoding is read directly (§2.4 of the format document):
 * inputs and latch literals are implicit, and each AND gate's two right-hand
 * sides are variable-length deltas from the gate's own literal, non-increasing.
 * The non-increasing check is a validity check the encoding gives for free --
 * a file whose deltas do not decrease is corrupt, and saying so beats decoding
 * it into a plausible wrong circuit.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/aiger.h"
#include "somtparser/translation/module.h"

#include <algorithm>
#include <cerrno>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <memory>
#include <limits>
#include <sstream>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
using Uir::ErrorCode;

struct Latch {
    unsigned lit = 0;         // the latch's own literal (always even)
    unsigned next = 0;        // the literal driving it
    bool     has_reset = false;
    unsigned reset = 0;       // 0, 1, or lit for "uninitialised"
};

struct AndGate {
    unsigned lhs = 0, rhs0 = 0, rhs1 = 0;
};

class AigerParser {
public:
    AigerParser(std::string src, std::string file, unsigned depth)
        : src_(std::move(src)), file_(std::move(file)), depth_(depth) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        if (!read(diags)) { return nullptr; }
        return build(diags, report);
    }

    std::shared_ptr<SourceModule> parseModule(Uir::Diagnostics& diags) {
        if (!read(diags)) { return nullptr; }
        auto module = std::make_shared<SourceModule>();
        module->language = "aiger";
        TransitionSystem system;
        system.name = "circuit";
        const auto bit = H::Sort::boolean();
        const auto variable = [&](unsigned lit, const std::string& role) {
            const auto current = stepName(varOf(lit), 0), next = stepName(varOf(lit), 1);
            system.variables.push_back({current, next, role, bit});
            declare(system.context, current, bit);
            declare(system.context, next, bit);
        };
        for (const auto lit : inputs_) { variable(lit, "input"); }
        system.init = H::mkBool(true);
        system.trans = H::mkBool(true);
        system.invariant = H::mkBool(true);
        for (const auto& latch : latches_) {
            variable(latch.lit, "local");
            const auto current = H::mkIdent(stepName(varOf(latch.lit), 0), bit);
            if (!latch.has_reset || latch.reset != latch.lit) {
                const auto reset = H::mkOp(H::Op::EQ, {current, H::mkBool(latch.reset == 1)});
                system.init = H::mkOp(H::Op::AND, {system.init, reset});
            }
            const auto value = term(latch.next, 0, diags);
            if (!value) { return nullptr; }
            const auto update = H::mkOp(H::Op::EQ,
                {H::mkIdent(stepName(varOf(latch.lit), 1), bit), value});
            system.trans = H::mkOp(H::Op::AND, {system.trans, update});
        }
        for (const auto lit : constraints_) {
            const auto value = term(lit, 0, diags);
            if (!value) { return nullptr; }
            system.invariant = H::mkOp(H::Op::AND, {system.invariant, value});
        }
        for (const auto lit : outputs_) {
            const auto value = term(lit, 0, diags);
            if (!value) { return nullptr; }
            system.outputs.push_back(value);
        }
        for (const auto lit : (extended_header_ ? bad_ : outputs_)) {
            const auto value = term(lit, 0, diags);
            if (!value) { return nullptr; }
            system.bad.push_back(value);
        }
        module->systems.push_back(std::move(system));
        return module;
    }

private:
    Uir::SourceLoc at(int line) const {
        Uir::SourceLoc l;
        l.file = file_;
        l.line = line;
        return l;
    }

    bool unsignedToken(const std::string& token, unsigned& out, int line,
                       Uir::Diagnostics& diags) const {
        if (token.empty()) {
            diags.error(ErrorCode::E_PARSE, "expected an unsigned integer", at(line));
            return false;
        }
        for (const char c : token) {
            if (c < '0' || c > '9') {
                diags.error(ErrorCode::E_PARSE,
                            "expected an unsigned integer, got `" + token + "`", at(line));
                return false;
            }
        }
        char* end = nullptr;
        errno = 0;
        const unsigned long long value = std::strtoull(token.c_str(), &end, 10);
        if (errno == ERANGE || end == token.c_str() || *end != '\0'
            || value > std::numeric_limits<unsigned>::max()) {
            diags.error(ErrorCode::E_PARSE,
                        "unsigned integer `" + token + "` is out of range", at(line));
            return false;
        }
        out = static_cast<unsigned>(value);
        return true;
    }

    bool fields(const std::string& raw, std::size_t min_count, std::size_t max_count,
                std::vector<unsigned>& out, int line, const std::string& what,
                Uir::Diagnostics& diags) const {
        std::istringstream in(raw);
        std::vector<std::string> tokens;
        std::string token;
        while (in >> token) { tokens.push_back(token); }
        if (tokens.size() < min_count || tokens.size() > max_count) {
            diags.error(ErrorCode::E_PARSE,
                        what + " needs "
                            + (min_count == max_count
                                   ? std::to_string(min_count)
                                   : std::to_string(min_count) + " or "
                                         + std::to_string(max_count))
                            + " unsigned integer(s)",
                        at(line));
            return false;
        }
        for (const std::string& t : tokens) {
            unsigned value = 0;
            if (!unsignedToken(t, value, line, diags)) { return false; }
            out.push_back(value);
        }
        return true;
    }

    bool structuralLine(std::istringstream& in, std::string& raw, int& line,
                        const std::string& section, Uir::Diagnostics& diags) const {
        if (!std::getline(in, raw)) {
            diags.error(ErrorCode::E_PARSE, "the file ends inside the " + section,
                        at(line + 1));
            return false;
        }
        ++line;
        if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
        return true;
    }

    bool read(Uir::Diagnostics& diags) {
        std::istringstream in(src_);
        std::string raw;
        int lineno = 0;

        if (!std::getline(in, raw)) {
            diags.error(ErrorCode::E_PARSE, "the file is empty", at(1));
            return false;
        }
        ++lineno;
        if (!raw.empty() && raw.back() == '\r') { raw.pop_back(); }
        {
            std::istringstream hs(raw);
            std::vector<std::string> tokens;
            std::string token;
            while (hs >> token) { tokens.push_back(token); }
            const std::string magic = tokens.empty() ? std::string() : tokens[0];
            if (magic == "aig") {
                binary_ = true;
            } else if (magic != "aag") {
                diags.error(ErrorCode::E_PARSE,
                            "expected an `aag` or `aig` header, found '" + magic + "'",
                            at(lineno));
                return false;
            }
            if (tokens.size() < 6 || tokens.size() > 10) {
                diags.error(ErrorCode::E_PARSE,
                            "the header needs `aag M I L O A` followed by at most "
                            "the optional `B C J F` suffix",
                            at(lineno));
                return false;
            }
            std::vector<unsigned> values;
            for (std::size_t i = 1; i < tokens.size(); ++i) {
                unsigned value = 0;
                if (!unsignedToken(tokens[i], value, lineno, diags)) { return false; }
                values.push_back(value);
            }
            max_var_ = values[0];
            num_inputs_ = values[1];
            num_latches_ = values[2];
            num_outputs_ = values[3];
            num_ands_ = values[4];
            extended_header_ = tokens.size() > 6;
            if (values.size() > 5) { num_bad_ = values[5]; }
            if (values.size() > 6) { num_constraints_ = values[6]; }
            if (values.size() > 7) { num_justice_ = values[7]; }
            if (values.size() > 8) { num_fairness_ = values[8]; }

            const unsigned long long definitions =
                static_cast<unsigned long long>(num_inputs_) + num_latches_ + num_ands_;
            if (definitions > max_var_) {
                diags.error(ErrorCode::E_PARSE,
                            "I + L + A exceeds the header maximum variable index M",
                            at(lineno));
                return false;
            }
            if (max_var_ > (std::numeric_limits<unsigned>::max() - 1U) / 2U) {
                diags.error(ErrorCode::E_PARSE,
                            "M is too large for the AIGER unsigned-literal encoding",
                            at(lineno));
                return false;
            }
        }

        if (binary_) {
            // The binary form drops the input and latch literal lists and
            // reconstructs them: inputs are 2, 4, ..., 2I and latch j is
            // 2(I + j + 1), so only the next-state and optional reset columns
            // are in the file (docs/languages/aiger.md §2.4).
            for (unsigned i = 0; i < num_inputs_; ++i) {
                inputs_.push_back(2u * (i + 1));
            }
            for (unsigned j = 0; j < num_latches_; ++j) {
                std::string l;
                if (!structuralLine(in, l, lineno, "latches", diags)) { return false; }
                std::vector<unsigned> value;
                if (!fields(l, 1, 2, value, lineno, "a binary latch line", diags)) {
                    return false;
                }
                Latch lat;
                lat.lit = 2u * (num_inputs_ + j + 1);
                lat.next = value[0];
                if (value.size() == 2) {
                    lat.has_reset = true;
                    lat.reset = value[1];
                }
                latches_.push_back(lat);
            }
        } else {
        for (unsigned i = 0; i < num_inputs_; ++i) {
            std::string line;
            if (!structuralLine(in, line, lineno, "inputs", diags)) { return false; }
            std::vector<unsigned> value;
            if (!fields(line, 1, 1, value, lineno, "an input line", diags)) {
                return false;
            }
            inputs_.push_back(value[0]);
        }
        for (unsigned i = 0; i < num_latches_; ++i) {
            std::string l;
            if (!structuralLine(in, l, lineno, "latches", diags)) { return false; }
            std::vector<unsigned> value;
            if (!fields(l, 2, 3, value, lineno, "a latch line", diags)) {
                return false;
            }
            Latch lat;
            lat.lit = value[0];
            lat.next = value[1];
            if (value.size() == 3) {
                lat.has_reset = true;
                lat.reset = value[2];
            }
            latches_.push_back(lat);
        }
        }
        for (unsigned i = 0; i < num_outputs_; ++i) {
            std::string line;
            if (!structuralLine(in, line, lineno, "outputs", diags)) { return false; }
            std::vector<unsigned> value;
            if (!fields(line, 1, 1, value, lineno, "an output line", diags)) {
                return false;
            }
            outputs_.push_back(value[0]);
        }
        for (unsigned i = 0; i < num_bad_; ++i) {
            std::string line;
            if (!structuralLine(in, line, lineno, "bad properties", diags)) {
                return false;
            }
            std::vector<unsigned> value;
            if (!fields(line, 1, 1, value, lineno, "a bad-property line", diags)) {
                return false;
            }
            bad_.push_back(value[0]);
        }
        for (unsigned i = 0; i < num_constraints_; ++i) {
            std::string line;
            if (!structuralLine(in, line, lineno, "constraints", diags)) { return false; }
            std::vector<unsigned> value;
            if (!fields(line, 1, 1, value, lineno, "a constraint line", diags)) {
                return false;
            }
            constraints_.push_back(value[0]);
        }
        if (num_justice_ != 0 || num_fairness_ != 0) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "justice and fairness are liveness properties, which ask about "
                        "infinite behaviour; a bounded unrolling cannot express them",
                        at(lineno));
            return false;
        }
        if (binary_) {
            return readBinaryAnds(in, lineno, diags) && validate(diags);
        }
        for (unsigned i = 0; i < num_ands_; ++i) {
            std::string l;
            if (!structuralLine(in, l, lineno, "AND gates", diags)) { return false; }
            std::vector<unsigned> value;
            if (!fields(l, 3, 3, value, lineno, "an AND-gate line", diags)) {
                return false;
            }
            AndGate g{value[0], value[1], value[2]};
            if (!ands_.emplace(g.lhs, g).second) {
                diags.error(ErrorCode::E_PARSE,
                            "AND literal " + std::to_string(g.lhs)
                                + " is defined more than once",
                            at(lineno));
                return false;
            }
        }
        return validate(diags);
    }

    /** The binary AND-gate section: everything after the last text line. Gate
     *  i has lhs 2(I+L+i), and each of its two right-hand sides is a
     *  variable-length delta from the previous literal. Symbol tables and
     *  comments may follow the gates; they do not alter the circuit and are
     *  not read. */
    bool readBinaryAnds(std::istringstream& in, int& lineno,
                        Uir::Diagnostics& diags) {
        const std::streampos pos = in.tellg();
        const std::size_t off = pos == std::streampos(-1)
            ? src_.size() : static_cast<std::size_t>(pos);
        const unsigned char* p =
            reinterpret_cast<const unsigned char*>(src_.data()) + off;
        const unsigned char* end =
            reinterpret_cast<const unsigned char*>(src_.data()) + src_.size();
        for (unsigned i = 1; i <= num_ands_; ++i) {
            const unsigned lhs = 2u * (num_inputs_ + num_latches_ + i);
            unsigned delta0 = 0, delta1 = 0;
            if (!decodeDelta(p, end, delta0) || !decodeDelta(p, end, delta1)) {
                diags.error(ErrorCode::E_PARSE,
                            "the file ends inside the binary AND gates (gate "
                                + std::to_string(i) + " of "
                                + std::to_string(num_ands_) + ")",
                            at(lineno + 1));
                return false;
            }
            // The encoding is unambiguous exactly because the literals
            // decrease: lhs > rhs0 >= rhs1. A file that does not is corrupt,
            // and saying so beats decoding it into a plausible wrong circuit
            // (docs/languages/aiger.md §2.4).
            if (delta0 == 0 || delta0 > lhs) {
                diags.error(ErrorCode::E_PARSE,
                            "AND gate " + std::to_string(i) + ": delta "
                                + std::to_string(delta0) + " does not give "
                                + "lhs > rhs0 (lhs is " + std::to_string(lhs) + ")",
                            at(lineno + 1));
                return false;
            }
            const unsigned rhs0 = lhs - delta0;
            if (delta1 > rhs0) {
                diags.error(ErrorCode::E_PARSE,
                            "AND gate " + std::to_string(i) + ": the deltas do "
                                + "not decrease (rhs0 is " + std::to_string(rhs0)
                                + ", delta1 is " + std::to_string(delta1) + ")",
                            at(lineno + 1));
                return false;
            }
            ands_.emplace(lhs, AndGate{lhs, rhs0, rhs0 - delta1});
        }
        return true;
    }

    /** One unsigned variable-length integer: 7 bits per byte, the high bit
     *  continuing. False on truncation or a value that does not fit an
     *  unsigned -- both corrupt, never a plausible circuit. */
    static bool decodeDelta(const unsigned char*& p, const unsigned char* end,
                            unsigned& out) {
        unsigned long long value = 0;
        unsigned shift = 0;
        while (true) {
            if (p == end || shift > 35) { return false; }
            const unsigned char ch = *p++;
            value |= static_cast<unsigned long long>(ch & 0x7f) << shift;
            if ((ch & 0x80) == 0) { break; }
            shift += 7;
        }
        if (value > std::numeric_limits<unsigned>::max()) { return false; }
        out = static_cast<unsigned>(value);
        return true;
    }

    bool validate(Uir::Diagnostics& diags) {
        std::unordered_set<unsigned> definitions;
        unsigned greatest_var = 0;
        const auto define = [&](unsigned lit, const std::string& what) -> bool {
            if (lit == 0 || negated(lit) || varOf(lit) > max_var_) {
                diags.error(ErrorCode::E_PARSE,
                            what + " must be a positive, unnegated literal within M");
                return false;
            }
            if (!definitions.insert(varOf(lit)).second) {
                diags.error(ErrorCode::E_PARSE,
                            "variable " + std::to_string(varOf(lit))
                                + " is defined more than once");
                return false;
            }
            greatest_var = std::max(greatest_var, varOf(lit));
            return true;
        };
        for (const unsigned lit : inputs_) {
            if (!define(lit, "an input literal")) { return false; }
        }
        for (const Latch& latch : latches_) {
            if (!define(latch.lit, "a latch literal")) { return false; }
            if (latch.has_reset && latch.reset != 0 && latch.reset != 1
                && latch.reset != latch.lit) {
                diags.error(ErrorCode::E_PARSE,
                            "latch " + std::to_string(latch.lit)
                                + " reset must be 0, 1, or the latch's own literal");
                return false;
            }
        }
        for (const auto& entry : ands_) {
            if (!define(entry.second.lhs, "an AND left-hand side")) { return false; }
        }
        if (greatest_var != max_var_) {
            diags.error(ErrorCode::E_PARSE,
                        "header M is " + std::to_string(max_var_)
                            + " but the greatest defined variable is "
                            + std::to_string(greatest_var));
            return false;
        }
        const auto reference = [&](unsigned lit, const std::string& what) -> bool {
            if (varOf(lit) > max_var_
                || (varOf(lit) != 0 && definitions.count(varOf(lit)) == 0)) {
                diags.error(ErrorCode::E_PARSE,
                            what + " uses undefined literal " + std::to_string(lit));
                return false;
            }
            return true;
        };
        for (const Latch& latch : latches_) {
            if (!reference(latch.next, "a latch next-state function")) { return false; }
        }
        for (const unsigned lit : outputs_) {
            if (!reference(lit, "an output")) { return false; }
        }
        for (const unsigned lit : bad_) {
            if (!reference(lit, "a bad property")) { return false; }
        }
        for (const unsigned lit : constraints_) {
            if (!reference(lit, "a constraint")) { return false; }
        }
        for (const auto& entry : ands_) {
            if (!reference(entry.second.rhs0, "an AND right-hand side")
                || !reference(entry.second.rhs1, "an AND right-hand side")) {
                return false;
            }
        }

        for (const auto& entry : ands_) {
            if (!checkAcyclic(varOf(entry.second.lhs), diags)) { return false; }
        }
        return true;
    }

    bool checkAcyclic(unsigned var, Uir::Diagnostics& diags) {
        if (acyclic_.count(var) != 0) { return true; }
        if (!checking_.insert(var).second) {
            diags.error(ErrorCode::E_PARSE,
                        "cyclic definition for AND variable " + std::to_string(var));
            return false;
        }
        const auto it = ands_.find(var << 1);
        if (it != ands_.end()) {
            for (const unsigned rhs : {it->second.rhs0, it->second.rhs1}) {
                if (ands_.count(varOf(rhs) << 1) != 0
                    && !checkAcyclic(varOf(rhs), diags)) {
                    return false;
                }
            }
        }
        checking_.erase(var);
        acyclic_.insert(var);
        return true;
    }

    /** The variable a literal names, with the negation flag stripped. This
     *  shift is the whole of §2.2, and getting it wrong reads a different
     *  circuit rather than failing. */
    static unsigned varOf(unsigned lit) { return lit >> 1; }
    static bool negated(unsigned lit) { return (lit & 1u) != 0u; }

    static std::string stepName(unsigned var, unsigned k) {
        return "v" + std::to_string(var) + "@" + std::to_string(k);
    }

    H::ConstraintModelPtr build(Uir::Diagnostics& diags, Uir::TranslationReport& report) {
        auto model = std::make_shared<H::ConstraintModel>();
        const H::Sort bit = H::Sort::boolean();

        // The property. Under 1.9 it is the `bad` section; a 1.0 file has none
        // and its outputs are the properties instead.
        std::vector<unsigned> props = extended_header_ ? bad_ : outputs_;
        const bool from_outputs = !extended_header_;
        if (props.empty()) {
            diags.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        extended_header_
                            ? "the extended header declares no bad property: outputs are "
                              "not safety properties in AIGER 1.9, so an unrolling would "
                              "have no reachability query and be trivially satisfiable"
                            : "no output property: there is nothing to check, and an "
                              "unrolling with no property asserted is trivially satisfiable",
                        at(1));
            return nullptr;
        }

        for (unsigned k = 0; k <= depth_; ++k) {
            for (const unsigned lit : inputs_) {
                declare(*model, stepName(varOf(lit), k), bit);
            }
            for (const Latch& l : latches_) {
                declare(*model, stepName(varOf(l.lit), k), bit);
            }
        }

        // Step 0: the reset values. A latch whose reset is its OWN literal is
        // uninitialised under 1.9 and is left unconstrained; one with no reset
        // column at all takes the language-defined default 0.
        bool used_default_zero = false;
        for (const Latch& l : latches_) {
            H::ExprPtr var = H::mkIdent(stepName(varOf(l.lit), 0), bit);
            if (!l.has_reset) {
                used_default_zero = true;
                add(*model, H::mkOp(H::Op::NOT, {var}));
            } else if (l.reset == 0) {
                add(*model, H::mkOp(H::Op::NOT, {var}));
            } else if (l.reset == 1) {
                add(*model, var);
            }
            // reset == l.lit: uninitialised, so nothing is asserted. Adding a
            // value here would remove initial states and report "safe" for a
            // circuit that is not.
        }
        if (used_default_zero) {
            Uir::EncodingChoice ch;
            ch.site       = file_;
            ch.unified_op = "latch-reset";
            ch.strategy   = "specified-default-zero";
            ch.fidelity   = Uir::Fidelity::exact();
            ch.rationale =
                "at least one latch omits the optional reset column; AIGER defines its "
                "reset as 0, so the emitted initial equation applies the source "
                "language's exact default rather than an implementation assumption";
            report.addChoice(std::move(ch));
        }

        // Steps 0..k-1: every latch takes its next literal. EVERY latch, not
        // only the ones that look interesting -- one left out goes free and the
        // property becomes trivially reachable.
        for (unsigned k = 0; k < depth_; ++k) {
            // All latch updates in one frame share the same combinational DAG.
            // Keep them in one conjunction so HIR checking, lowering and SMT
            // let emission can share fan-in across different latch equations.
            std::vector<H::ExprPtr> updates;
            updates.reserve(latches_.size());
            for (const Latch& l : latches_) {
                H::ExprPtr v = term(l.next, k, diags);
                if (!v) { return nullptr; }
                updates.push_back(H::mkOp(H::Op::EQ,
                    {H::mkIdent(stepName(varOf(l.lit), k + 1), bit), std::move(v)}));
            }
            if (updates.size() == 1) {
                add(*model, updates.front());
            } else if (!updates.empty()) {
                add(*model, H::mkOp(H::Op::AND, std::move(updates)));
            }
        }

        // AIGER 1.9 defines a bad-state witness as c U (c AND bad): invariant
        // constraints hold only through the step at which the bad literal is
        // witnessed. Requiring c at every step of the fixed unrolling would
        // reject a valid shorter witness when c becomes false afterwards.
        H::ExprPtr any;
        H::ExprPtr constraint_prefix = H::mkBool(true);
        for (unsigned k = 0; k <= depth_; ++k) {
            for (const unsigned c : constraints_) {
                H::ExprPtr e = term(c, k, diags);
                if (!e) { return nullptr; }
                constraint_prefix = H::mkOp(
                    H::Op::AND, {constraint_prefix, e});
            }
            for (const unsigned p : props) {
                H::ExprPtr e = term(p, k, diags);
                if (!e) { return nullptr; }
                H::ExprPtr witness = constraints_.empty()
                    ? e
                    : H::mkOp(H::Op::AND, {constraint_prefix, e});
                any = any ? H::mkOp(H::Op::OR, {any, witness}) : witness;
            }
        }
        add(*model, any);

        Uir::EncodingChoice ch;
        ch.site       = file_;
        ch.unified_op = "transition-system";
        ch.strategy   = from_outputs ? "bmc-unrolling-outputs-as-properties"
                                     : "bmc-unrolling";
        Uir::Fidelity::Bound b;
        b.kind  = Uir::Fidelity::Bound::BMC_DEPTH;
        b.value = static_cast<int64_t>(depth_);
        b.site  = file_;
        ch.fidelity = Uir::Fidelity::underApprox(b);
        ch.rationale =
            std::string("an and-inverter graph unrolled to depth ")
            + std::to_string(depth_)
            + "; SAT is a real trace to the property and comparable to the "
              "competition's answer, UNSAT means NO COUNTEREXAMPLE WITHIN "
            + std::to_string(depth_) + " STEPS and must not be reported as safe"
            + (from_outputs ? "; the file declares no `bad` section, so its OUTPUTS are "
                              "read as the safety properties, which is the pre-1.9 "
                              "convention"
                            : "");
        report.addChoice(std::move(ch));
        return model;
    }

    void declare(H::ConstraintModel& m, const std::string& name, const H::Sort& s) {
        if (!declared_.insert(name).second) { return; }
        H::VarDecl d;
        d.name = name;
        d.sort = s;
        m.decls.push_back(std::move(d));
    }
    static void add(H::ConstraintModel& m, const H::ExprPtr& e) {
        H::Constraint c;
        c.formula = e;
        m.constraints.push_back(c);
    }

    /** The Bool a literal denotes at step @p k. */
    H::ExprPtr term(unsigned lit, unsigned k, Uir::Diagnostics& diags) {
        // 0 and 1 are the CONSTANTS, not variables. Reading them as variable 0
        // positive and negated would invent a variable the format says does not
        // exist.
        if (lit == 0) { return H::mkBool(false); }
        if (lit == 1) { return H::mkBool(true); }

        const unsigned v = varOf(lit);
        const bool neg = negated(lit);
        H::ExprPtr base;

        const auto key = std::make_pair(v, k);
        const auto mi = memo_.find(key);
        if (mi != memo_.end()) {
            base = mi->second;
        } else {
            const auto gi = ands_.find(v << 1);
            if (gi != ands_.end()) {
                if (depth_guard_.count(v) != 0) {
                    diags.error(ErrorCode::E_PARSE,
                                "AND gate " + std::to_string(v)
                                    + " is defined in terms of itself");
                    return nullptr;
                }
                depth_guard_.insert(v);
                H::ExprPtr a = term(gi->second.rhs0, k, diags);
                H::ExprPtr b = a ? term(gi->second.rhs1, k, diags) : nullptr;
                depth_guard_.erase(v);
                if (!a || !b) { return nullptr; }
                base = H::mkOp(H::Op::AND, {a, b});
            } else {
                // An input or a latch: a declared variable at this step.
                base = H::mkIdent(stepName(v, k), H::Sort::boolean());
            }
            memo_[key] = base;
        }
        return neg ? H::mkOp(H::Op::NOT, {base}) : base;
    }

    struct PairHash {
        std::size_t operator()(const std::pair<unsigned, unsigned>& p) const {
            return (static_cast<std::size_t>(p.first) << 20) ^ p.second;
        }
    };

    std::string src_, file_;
    unsigned    depth_;
    unsigned    max_var_ = 0, num_inputs_ = 0, num_latches_ = 0, num_outputs_ = 0;
    unsigned    num_ands_ = 0, num_bad_ = 0, num_constraints_ = 0;
    unsigned    num_justice_ = 0, num_fairness_ = 0;
    bool        extended_header_ = false;
    bool        binary_ = false;
    std::vector<unsigned> inputs_, outputs_, bad_, constraints_;
    std::vector<Latch>    latches_;
    std::unordered_map<unsigned, AndGate> ands_;
    std::unordered_map<std::pair<unsigned, unsigned>, H::ExprPtr, PairHash> memo_;
    std::unordered_set<unsigned> depth_guard_;
    std::unordered_set<unsigned> checking_, acyclic_;
    std::unordered_set<std::string> declared_;
};

class AigerLanguage : public Language {
public:
    ModuleOutcome parseModule(const SourceUnit& unit) override {
        ModuleOutcome out;
        std::string source;
        if (!readModuleSource(unit, source, out.diagnostics)) { return out; }
        AigerParser parser(source, unit.main_path.empty() ? unit.display_name : unit.main_path, 0);
        out.module = parser.parseModule(out.diagnostics);
        return out;
    }

    AigerLanguage() {
        coverage_.total = 8;
        coverage_.supported = 7;
        coverage_.missing = {
            "liveness (justice and fairness)",
        };
    }

    std::string id() const override { return "aiger"; }
    std::string displayName() const override { return "AIGER"; }
    std::string version() const override { return "1.9"; }
    std::vector<std::string> extensions() const override { return {".aag", ".aig"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) override {
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

        const auto it = opts.options.find("bmc_depth");
        if (it == opts.options.end()) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "no unrolling depth: pass bmc_depth=<k>. There is "
                                  "deliberately no default, because the depth is the "
                                  "bound the translation's fidelity is stated against");
            return out;
        }
        char* end = nullptr;
        errno = 0;
        const long long k = std::strtoll(it->second.c_str(), &end, 10);
        if (errno == ERANGE || end == it->second.c_str() || *end != '\0') {
            out.diagnostics.error(ErrorCode::E_PARSE,
                                  "bmc_depth must be a base-10 integer");
            return out;
        }
        if (k < 0) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth must not be negative");
            return out;
        }
        if (static_cast<unsigned long long>(k)
            >= static_cast<unsigned long long>(std::numeric_limits<unsigned>::max())) {
            out.diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "bmc_depth is too large for the unroller");
            return out;
        }

        const std::string name =
            unit.main_path.empty() ? unit.display_name : unit.main_path;
        try {
            AigerParser p(src, name, static_cast<unsigned>(k));
            out.model = p.parse(out.diagnostics, out.report);
            if (out.model) {
                out.semantics.add(Uir::Sem::directLanguageToRelationalContract(
                    *out.model, "aiger", out.report.fidelity()));
            }
        } catch (const std::exception& e) {
            out.model = nullptr;
            out.diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string("aiger frontend: ") + e.what());
        }
        return out;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkAigerLanguage() { return std::make_shared<AigerLanguage>(); }

} // namespace SOMTParser::Lang
