// Extension alone cannot pick a language: CHC-COMP files are .smt2, exactly
// like plain SMT-LIB. Content sniffing breaks the tie.
#include "somtparser/translation/language.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Lang;

namespace {

class FakeLang : public Language {
public:
    FakeLang(std::string id, std::vector<std::string> exts, std::string marker)
        : id_(std::move(id)), exts_(std::move(exts)), marker_(std::move(marker)) {}

    std::string id() const override { return id_; }
    std::string displayName() const override { return id_; }
    std::string version() const override { return "0.1"; }
    std::vector<std::string> extensions() const override { return exts_; }

    double sniff(std::string_view head) const override {
        if (marker_.empty()) { return 0.0; }
        return head.find(marker_) != std::string_view::npos ? 0.9 : 0.0;
    }

    const OpCoverage& coverage() const override { return coverage_; }

    ParseOutcome parse(const SourceUnit&, const ParseOptions&) override {
        ParseOutcome o;
        o.model = std::make_shared<Uir::Hir::ConstraintModel>();
        return o;
    }

private:
    std::string id_;
    std::vector<std::string> exts_;
    std::string marker_;
    OpCoverage coverage_;
};

} // namespace

int main() {
    LanguageRegistry reg;
    reg.add(std::make_shared<FakeLang>("minizinc", std::vector<std::string>{".mzn"}, ""));
    reg.add(std::make_shared<FakeLang>("smtlib", std::vector<std::string>{".smt2"}, ""));
    reg.add(std::make_shared<FakeLang>("chc", std::vector<std::string>{".smt2"}, "declare-rel"));

    assert(reg.all().size() == 3);
    assert(reg.byId("minizinc") != nullptr);
    assert(reg.byId("nope") == nullptr);

    // Unambiguous extension.
    {
        SourceUnit u;
        u.main_path = "model.mzn";
        u.inline_source = "var int: x;";
        const Language* l = reg.detect(u);
        assert(l != nullptr);
        assert(l->id() == "minizinc");
    }

    // Contested extension, no marker: the non-sniffing candidate wins.
    {
        SourceUnit u;
        u.main_path = "f.smt2";
        u.inline_source = "(set-logic QF_LIA)(assert (> x 0))";
        const Language* l = reg.detect(u);
        assert(l != nullptr);
        assert(l->id() == "smtlib");
    }

    // Contested extension with the marker: sniffing wins. Without this, every
    // CHC-COMP benchmark would be silently eaten as plain SMT.
    {
        SourceUnit u;
        u.main_path = "f.smt2";
        u.inline_source = "(set-logic HORN)(declare-rel inv (Int))";
        const Language* l = reg.detect(u);
        assert(l != nullptr);
        assert(l->id() == "chc");
    }

    // Unknown extension: no guess.
    {
        SourceUnit u;
        u.main_path = "x.unknown";
        u.inline_source = "whatever";
        assert(reg.detect(u) == nullptr);
    }

    // Bare dotfile: the only dot is the first character, so there is no
    // extension, not the whole filename. dot == start must not pass the
    // "has extension" guard.
    {
        SourceUnit u;
        u.main_path = ".bashrc";
        u.inline_source = "export PATH=$PATH:/usr/local/bin";
        assert(reg.detect(u) == nullptr);
    }

    // The discriminating case: a file literally named ".smt2" (no basename).
    // Its only dot coincides with a *registered* extension, so a guard using
    // "dot < start" instead of "dot <= start" would misread the whole
    // filename as the extension ".smt2" and wrongly hand it to smtlib/chc.
    // ".bashrc" alone cannot catch this bug, since nothing claims ".bashrc"
    // as an extension either way -- this case is load-bearing.
    {
        SourceUnit u;
        u.main_path = ".smt2";
        u.inline_source = "(set-logic QF_LIA)(assert (> x 0))";
        assert(reg.detect(u) == nullptr);
    }

    // A dot only in a directory component is not a file extension either.
    {
        SourceUnit u;
        u.main_path = "dir.v1/model";
        u.inline_source = "whatever";
        assert(reg.detect(u) == nullptr);
    }

    // Contrast: a real extension after that same directory component still
    // detects normally, so the boundary fix did not break the ordinary case.
    {
        SourceUnit u;
        u.main_path = "dir.v1/model.mzn";
        u.inline_source = "var int: x;";
        const Language* l = reg.detect(u);
        assert(l != nullptr);
        assert(l->id() == "minizinc");
    }

    // Case-insensitive extension matching, since benchmark archives are messy.
    {
        SourceUnit u;
        u.main_path = "MODEL.MZN";
        u.inline_source = "var int: x;";
        const Language* l = reg.detect(u);
        assert(l != nullptr);
        assert(l->id() == "minizinc");
    }

    // ParseOutcome reports success by the presence of a model.
    {
        SourceUnit u;
        ParseOptions po;
        ParseOutcome o = reg.byId("minizinc")->parse(u, po);
        assert(o.ok());
        ParseOutcome bad;
        assert(!bad.ok());
    }

    // Adding a null language is a caller bug, not a recoverable condition: it
    // must fail loudly rather than silently drop the language.
    {
        bool threw = false;
        try {
            reg.add(LanguagePtr{});
        } catch (const std::runtime_error&) {
            threw = true;
        }
        assert(threw);
        assert(reg.all().size() == 3); // the failed add left the registry unchanged
    }

    std::cout << "All LanguageRegistry tests passed." << std::endl;
    return 0;
}
