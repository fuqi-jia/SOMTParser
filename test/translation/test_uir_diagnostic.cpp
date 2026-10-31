// Errors are return values, not exceptions: one bad frontend must not take
// down a batch of ten thousand benchmarks.
#include "somtparser/translation/diagnostic.h"
#include <cassert>
#include <iostream>
#include <stdexcept>
#include <string>

using namespace SOMTParser::Uir;

int main() {
    Diagnostics d;
    assert(!d.hasErrors());
    assert(d.size() == 0);
    assert(d.firstErrorCode() == ErrorCode::OK);

    // Warnings do not make the outcome a failure.
    d.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT, "circuit is not implemented",
           SourceLoc{"m.mzn", 12, 3});
    assert(!d.hasErrors());
    assert(d.size() == 1);
    assert(d.all()[0].severity == Severity::WARNING);
    assert(d.all()[0].loc.line == 12);
    assert(d.all()[0].loc.column == 3);
    assert(d.all()[0].loc.file == "m.mzn");

    // The first error code is the one reported; later ones do not overwrite it.
    d.error(ErrorCode::E_TYPE, "expected int, got bool", SourceLoc{"m.mzn", 20, 1});
    d.error(ErrorCode::E_PARSE, "unexpected ')'");
    assert(d.hasErrors());
    assert(d.firstErrorCode() == ErrorCode::E_TYPE);
    assert(d.size() == 3);

    // Merging preserves order and error state, which is how a frontend's
    // diagnostics get folded into the translation's.
    Diagnostics other;
    other.note(ErrorCode::OK, "using profile bv32");
    Diagnostics combined;
    combined.merge(other);
    assert(!combined.hasErrors());
    assert(combined.size() == 1);
    combined.merge(d);
    assert(combined.hasErrors());
    assert(combined.size() == 4);
    assert(combined.all()[0].severity == Severity::NOTE);
    assert(combined.firstErrorCode() == ErrorCode::E_TYPE);

    // Test the merge guard: clean source into dirty destination must not clear
    // the destination's error state. A naive implementation that unconditionally
    // assigns first_error_ = source.first_error_ would fail here.
    Diagnostics dirty;
    dirty.error(ErrorCode::E_TYPE, "type mismatch");
    assert(dirty.hasErrors());
    assert(dirty.firstErrorCode() == ErrorCode::E_TYPE);
    assert(dirty.size() == 1);

    Diagnostics clean_source;
    clean_source.note(ErrorCode::OK, "clean info");
    dirty.merge(clean_source);
    assert(dirty.hasErrors());  // error state must persist
    assert(dirty.firstErrorCode() == ErrorCode::E_TYPE);  // must not be overwritten
    assert(dirty.size() == 2);  // both entries present
    assert(dirty.all()[0].code == ErrorCode::E_TYPE);
    assert(dirty.all()[0].message == "type mismatch");
    assert(dirty.all()[1].code == ErrorCode::OK);
    assert(dirty.all()[1].message == "clean info");

    // Test the merge guard with both sources dirty: destination's first error
    // must not be overwritten by source's first error.
    Diagnostics dest_dirty;
    dest_dirty.error(ErrorCode::E_TYPE, "destination error");
    assert(dest_dirty.firstErrorCode() == ErrorCode::E_TYPE);

    Diagnostics src_dirty;
    src_dirty.error(ErrorCode::E_PARSE, "source error");
    assert(src_dirty.firstErrorCode() == ErrorCode::E_PARSE);

    dest_dirty.merge(src_dirty);
    assert(dest_dirty.hasErrors());
    assert(dest_dirty.firstErrorCode() == ErrorCode::E_TYPE);  // destination's first error wins
    assert(dest_dirty.size() == 2);
    assert(dest_dirty.all()[0].code == ErrorCode::E_TYPE);
    assert(dest_dirty.all()[0].message == "destination error");
    assert(dest_dirty.all()[1].code == ErrorCode::E_PARSE);
    assert(dest_dirty.all()[1].message == "source error");

    // hasErrors() reports what was recorded, not what the code happens to be.
    // Deriving it from first_error_ != OK made it disagree with the recorded
    // severity, and it is the gate on translate()'s failure paths.
    {
        Diagnostics e;
        e.error(ErrorCode::E_IO, "cannot open 'm.mzn'");
        assert(e.hasErrors());
        assert(e.firstErrorCode() == ErrorCode::E_IO);
        assert(e.all()[0].severity == Severity::ERROR);

        // A merged ERROR sets it too, even when it arrives from another
        // Diagnostics rather than through error().
        Diagnostics dest;
        assert(!dest.hasErrors());
        dest.merge(e);
        assert(dest.hasErrors());
        assert(dest.firstErrorCode() == ErrorCode::E_IO);
    }

    // Filing an error under ErrorCode::OK is an impossible state, not a
    // runtime condition: the evaluation buckets failures by code, so an error
    // recorded as "no error" would be counted as a success cause -- and it is
    // exactly the input that used to leave hasErrors() false. It must throw.
    {
        Diagnostics e;
        bool threw = false;
        try {
            e.error(ErrorCode::OK, "an error with no code");
        } catch (const std::runtime_error&) {
            threw = true;
        }
        assert(threw);
        // NOTE and WARNING under OK stay legal: they are not failures.
        e.note(ErrorCode::OK, "using profile bv32");
        e.warn(ErrorCode::OK, "nothing to optimise");
        assert(!e.hasErrors());
        assert(e.size() == 2);
    }

    // Names are stable: the evaluation groups failures by them.
    assert(std::string(errorCodeName(ErrorCode::E_NO_ENCODING)) == "E_NO_ENCODING");
    assert(std::string(errorCodeName(ErrorCode::OK)) == "OK");
    assert(std::string(errorCodeName(ErrorCode::E_PASS_PIPELINE)) == "E_PASS_PIPELINE");

    // A value outside ErrorCode must throw rather than silently return a
    // stand-in name (which would quietly corrupt the failure-cause breakdown).
    {
        bool threw = false;
        try {
            errorCodeName(static_cast<ErrorCode>(9999));
        } catch (const std::runtime_error&) {
            threw = true;
        }
        assert(threw);
    }

    std::cout << "All Diagnostics tests passed." << std::endl;
    return 0;
}
