// BoundIntsPass gives every unbounded Int variable a finite domain so the
// fidelity pipeline has a real, honestly-lossy pass to run end to end. The
// easiest way to get this wrong: recording an under-approximation for a
// variable that already carried a bound, which would misreport a variable
// this pass never touched as a loss in the experiment data. That is what the
// second block below pins down.
#include "somtparser/lowering/bound_ints_pass.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace {

/** Reads back an ExprPtr's literal int value. A bound this pass sets is
 *  always a LIT_INT, never null or a compound expression, so failing loudly
 *  here on anything else is the point, not a defensive nicety. */
long long litValue(const ExprPtr& e) {
    assert(e != nullptr);
    assert(e->kind == ExprKind::LIT_INT);
    return e->int_value;
}

} // namespace

int main() {
    Lower::BoundIntsPass pass;
    assert(pass.id() == "bound-ints");

    // Traits: no precondition, nothing eliminated, nothing introduced. The
    // variable stays Int -- there is no BV sort yet for it to become.
    {
        const PassTraits t = pass.traits();
        assert(t.requires_absent.empty());
        assert(t.eliminates.empty());
        assert(t.introduces.empty());
    }

    // 1 & 3 & 5 (w = 8 case): an unbounded Int variable is bounded to
    // [-(2^(w-1)), 2^(w-1)-1], and the recorded EncodingChoice carries exactly
    // the fields the experiment data relies on.
    long long lo8 = 0, hi8 = 0;
    {
        ConstraintModel m;
        VarDecl d;
        d.name = "x";
        d.sort = Sort::integer();
        m.decls.push_back(d);

        PassSpec spec;
        spec.pass_id = "bound-ints";
        spec.params["width"] = "8";

        TranslationReport report;
        Diagnostics diags;
        LowerContext ctx;
        ctx.report = &report;
        ctx.diagnostics = &diags;
        ctx.spec = &spec;

        assert(pass.run(m, ctx));
        assert(!diags.hasErrors());

        assert(m.decls[0].lower_bound != nullptr);
        assert(m.decls[0].upper_bound != nullptr);
        lo8 = litValue(m.decls[0].lower_bound);
        hi8 = litValue(m.decls[0].upper_bound);
        assert(lo8 == -128);
        assert(hi8 == 127);

        assert(report.choices().size() == 1);
        const auto& c = report.choices()[0];
        assert(c.strategy == "bound-ints");
        assert(c.unified_op == "int-var");
        assert(c.site == "x");
        assert(c.fidelity.sound == true);
        assert(c.fidelity.complete == false);
        assert(c.fidelity.bounds.size() == 1);
        assert(c.fidelity.bounds[0].kind == Fidelity::Bound::BV_WIDTH);
        assert(c.fidelity.bounds[0].value == 8);
        assert(c.fidelity.bounds[0].site == "x");

        // The pass's own report-level fidelity reflects the same choice.
        assert(report.fidelity().sound == true);
        assert(report.fidelity().complete == false);
    }

    // 2. Variables that already carry a bound in either direction are left
    //    completely alone, and get no choice recorded -- they lost nothing.
    {
        ConstraintModel m;

        // Only the lower bound is set: the pass's own condition is "both
        // bounds absent", so a single present bound must already suppress it,
        // including filling in the missing side.
        VarDecl lo_only;
        lo_only.name = "lo_bounded";
        lo_only.sort = Sort::integer();
        lo_only.lower_bound = mkInt(0);
        m.decls.push_back(lo_only);

        VarDecl both;
        both.name = "both_bounded";
        both.sort = Sort::integer();
        both.lower_bound = mkInt(1);
        both.upper_bound = mkInt(9);
        m.decls.push_back(both);

        PassSpec spec;
        spec.pass_id = "bound-ints";     // width absent -> default 32, irrelevant here

        TranslationReport report;
        Diagnostics diags;
        LowerContext ctx;
        ctx.report = &report;
        ctx.diagnostics = &diags;
        ctx.spec = &spec;

        assert(pass.run(m, ctx));
        assert(!diags.hasErrors());

        assert(litValue(m.decls[0].lower_bound) == 0);
        assert(m.decls[0].upper_bound == nullptr);   // still absent: not filled in
        assert(litValue(m.decls[1].lower_bound) == 1);
        assert(litValue(m.decls[1].upper_bound) == 9);

        assert(report.choices().empty());
        assert(report.fidelity().sound && report.fidelity().complete && report.fidelity().preserves_optimum && report.fidelity().bounds.empty() && report.fidelity().count_status == CountStatus::UNASSESSED);
    }

    // 4. Bool and Real variables are never touched, bounded or not.
    {
        ConstraintModel m;
        VarDecl b;
        b.name = "flag";
        b.sort = Sort::boolean();
        m.decls.push_back(b);

        VarDecl r;
        r.name = "ratio";
        r.sort = Sort::real();
        m.decls.push_back(r);

        PassSpec spec;
        spec.pass_id = "bound-ints";

        TranslationReport report;
        Diagnostics diags;
        LowerContext ctx;
        ctx.report = &report;
        ctx.diagnostics = &diags;
        ctx.spec = &spec;

        assert(pass.run(m, ctx));
        assert(!diags.hasErrors());
        assert(m.decls[0].lower_bound == nullptr);
        assert(m.decls[0].upper_bound == nullptr);
        assert(m.decls[1].lower_bound == nullptr);
        assert(m.decls[1].upper_bound == nullptr);
        assert(report.choices().empty());
        assert(report.fidelity().sound && report.fidelity().complete && report.fidelity().preserves_optimum && report.fidelity().bounds.empty() && report.fidelity().count_status == CountStatus::UNASSESSED);
    }

    // 5. width actually changes the bound produced (w = 32 case), and its
    //    result differs from the w = 8 case above. Also covers the default:
    //    an absent "width" behaves exactly like an explicit "32".
    {
        ConstraintModel m;
        VarDecl d;
        d.name = "y";
        d.sort = Sort::integer();
        m.decls.push_back(d);

        PassSpec spec;
        spec.pass_id = "bound-ints";
        spec.params["width"] = "32";

        TranslationReport report;
        Diagnostics diags;
        LowerContext ctx;
        ctx.report = &report;
        ctx.diagnostics = &diags;
        ctx.spec = &spec;

        assert(pass.run(m, ctx));
        const long long lo32 = litValue(m.decls[0].lower_bound);
        const long long hi32 = litValue(m.decls[0].upper_bound);
        assert(lo32 == -2147483648LL);
        assert(hi32 == 2147483647LL);
        assert(lo32 != lo8);
        assert(hi32 != hi8);
        assert(report.choices()[0].fidelity.bounds[0].value == 32);

        // Default width (no "width" param at all) must match the explicit-32
        // case exactly: intParam("width", 32) is the pass's only source of w.
        ConstraintModel m2;
        VarDecl d2;
        d2.name = "z";
        d2.sort = Sort::integer();
        m2.decls.push_back(d2);
        PassSpec default_spec;
        default_spec.pass_id = "bound-ints";
        TranslationReport report2;
        Diagnostics diags2;
        LowerContext ctx2;
        ctx2.report = &report2;
        ctx2.diagnostics = &diags2;
        ctx2.spec = &default_spec;
        assert(pass.run(m2, ctx2));
        assert(litValue(m2.decls[0].lower_bound) == lo32);
        assert(litValue(m2.decls[0].upper_bound) == hi32);
    }

    std::cout << "All BoundIntsPass tests passed." << std::endl;
    return 0;
}
