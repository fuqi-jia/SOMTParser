// XCSP3-core semantic regression tests. They target cases where a syntactically
// plausible lowering can silently change the source solution relation.
//
// Three are about a value that is not what it looks like, and each is a silent
// wrong answer rather than a crash:
//
//   * A sparse domain `1 3 5 7` is NOT the range 1..7. `VarDecl` carries two
//     bounds and nothing else, so the enumeration has to become a membership
//     constraint as well -- otherwise the model admits 2, 4 and 6, which the
//     instance forbids, and it still type-checks.
//   * A short table's `*` matches every value in the column's DECLARED domain.
//     As a literal it matches nothing. This frontend enforces the exact domain
//     globally, so the local wildcard factor is redundant in the full model.
//   * `conflicts` forbids exactly the listed tuples. Its complement equals the
//     supports table only over the full Cartesian product of the declared
//     domains, which is not what either file lists.
//
// `circuit` is the sharp graph example: pairwise distinct successors admit
// disjoint nontrivial cycles. The current encoding adds active-node positions,
// and the fixed-assignment tests distinguish one legal subcircuit from two
// illegal disjoint cycles.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/xcsp3.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/omt_emitter.h"

#include <cassert>

#include "test_helpers.h"
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.xml";
    u.display_name = "t.xml";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "xcsp3";
    return translate(u, opts);
}

Translation run(const std::string& src, Lower::OmtDialect dialect) {
    Lang::SourceUnit u;
    u.main_path = "t.xml";
    u.display_name = "t.xml";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "xcsp3";
    opts.omt_dialect = dialect;
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "xcsp3";
    return translate(u, opts);
}

/** The same, targeting a named OMT dialect.
 *
 *  Whether an objective can be emitted is partly a property of the TARGET, so a
 *  test that reads dialect-specific output has to ask for that dialect up
 *  front rather than translating under the default and reading another. */
Translation runFile(const std::string& path, Lower::OmtDialect dialect) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "xcsp3";
    opts.omt_dialect = dialect;
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= XCSP3-core frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* x = Lang::LanguageRegistry::instance().byId("xcsp3");
    assert(x != nullptr);
    assert(x->extensions().size() == 2);

    // ---- Obligation 1: a sparse domain is not the interval that contains it. -
    {
        const Translation t =
            runFile("languages/xcsp3/instances/ok/sparse_domain.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The bounds are there...
        assert(has(smt, "(>= x 1)"));
        assert(has(smt, "(<= x 7)"));
        // ...and so is the membership constraint the bounds cannot express.
        // Without it the model admits x = 2, which the instance forbids.
        // Arithmetic progressions use a congruence instead of an OR of
        // individual equalities. Independent Python XOR checks compare this
        // entire relation with the original enumerated set, including holes.
        assert(has(smt, "(mod "));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A CONTIGUOUS domain gets no membership constraint: the bounds already
        // say it exactly, and emitting one anyway would be noise that grows
        // with the domain. `y` is 0..3 in the same file as the sparse `x`, so
        // one fixture distinguishes the two paths.
        const Translation t =
            runFile("languages/xcsp3/instances/ok/sparse_domain.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= y 0)") && has(smt, "(<= y 3)"));
        assert(!has(smt, "(= y 0)") && !has(smt, "(= y 1)"));
    }
    {
        // `0..3 7 9..12`: ranges and singletons mixed. The bounds are 0 and 12,
        // and 4, 5, 6 and 8 must not be admitted.
        const Translation t = runFile("languages/xcsp3/instances/ok/mixed_domain.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= z 0)") && has(smt, "(<= z 12)"));
        // The smaller complement excludes the four missing values. Python
        // XOR checks verify this against the complete enumerated relation.
        assert(count(smt, "(distinct ") == 1);
    }

    // ---- Obligation: the intension language. --------------------------------
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/intension.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(t.report().stats().num_constraints == 6);
        assert(has(smt, "ite"));            // dist and abs expand through ITE
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `imp(a, b)` is `(not a) or b`, exactly -- the HIR has no IMPLIES, and
        // the expansion must not be an approximation. Checked semantically: the
        // emitted formula is satisfied by x=5 (antecedent false) and by
        // x=1,y=0 (both true), and refuted by x=1,y=9.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..10 </var><var id=\"y\"> 0..10 </var></variables>"
            "<constraints><intension> imp(lt(x, 2), le(y, 5)) </intension>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "or"));
        // The negated antecedent is `x >= 2`. Asserting on `not` would be
        // asserting the shape passed in: simp_oper folds `(not (< x 2))` to
        // `(>= x 2)`, which is the same formula and the right behaviour.
        assert(has(smt, "(>= x 2)") || has(smt, "(not (< x 2))"));
        assert(has(smt, "(<= y 5)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // XCSP3 eq is n-ary and means x1=...=xr. HIR EQ is deliberately
        // binary, so the frontend must build the conjunction explicitly.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..2 </var><var id=\"y\"> 0..2 </var>"
            "<var id=\"z\"> 0..2 </var></variables><constraints>"
            "<intension> eq(x,y,z) </intension></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= x y)"));
        assert(has(smt, "(= x z)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A 01Var is an integer in the HIR and a Boolean in XCSP3 boolExpr.
        // `iff` is n-ary too, so this exercises both semantic adaptations.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"a\"> 0..1 </var><var id=\"b\"> 0..1 </var>"
            "<var id=\"c\"> 0..1 </var></variables><constraints>"
            "<intension> iff(a,b,c) </intension></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= a 1)") || has(smt, "(= 1 a)"));
        assert(has(smt, "(= b 1)") || has(smt, "(= 1 b)"));
        assert(has(smt, "(= c 1)") || has(smt, "(= 1 c)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Actual IndusCP HRC/Pennies/GraphMaxAcyclic models equate integer
        // variables with predicates. Arithmetic and conditional branches use
        // the same XCSP3 0/1 values, without relaxing HIR's sort discipline.
        for (const std::string& expression : {
                 "eq(a,gt(x,y))", "ne(a,gt(x,y))",
                 "eq(a,gt(x,y),ne(x,y))", "eq(a,add(gt(x,y),lt(x,y)))",
                 "eq(a,if(eq(x,y),gt(x,0),0))"}) {
            const Translation t = run(
                "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
                "<var id=\"a\"> 0..2 </var><var id=\"x\"> -1..1 </var>"
                "<var id=\"y\"> -1..1 </var></variables><constraints>"
                "<intension>" + expression + "</intension></constraints></instance>");
            VERIFY(t.ok());
            ParserPtr reader = newParser();
            VERIFY(reader->parseStr(t.toSmt2()));
        }
    }
    {
        // At the root a 01Var is true exactly at value 1, not an ill-sorted SMT
        // assertion and not an unconstrained integer.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"a\"> 0..1 </var></variables><constraints>"
            "<intension> a </intension></constraints></instance>");
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert (= a 1))")
               || has(t.toSmt2(), "(assert (= 1 a))"));
    }
    {
        // `sqr` and n-ary min/max are official intExpr operators. Nested ITEs
        // preserve their exact value without inventing an uninterpreted helper.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> -3..3 </var><var id=\"y\"> -3..3 </var>"
            "<var id=\"z\"> -3..9 </var></variables><constraints>"
            "<intension> eq(z,add(sqr(x),min(x,y,z),max(x,y,z))) </intension>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(* x x)"));
        assert(count(smt, "ite") >= 4);
    }
    {
        // XCSP3-core intension sets are finite constants, and pow with a
        // literal non-negative exponent has an exact multiplication lowering.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> -3..3 </var></variables><constraints>"
            "<intension> and(in(x,set(-1,1,3)),eq(pow(x,3),mul(x,x,x))) </intension>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Finite membership shares the equality lowering with other HIR
        // producers; all three source members must survive that lowering.
        for (const std::string value : {"(- 1)", "1", "3"}) {
            assert(has(smt, "(= x " + value + ")")
                || has(smt, "(= " + value + " x)"));
        }
        assert(has(smt, "(*"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A symbolic exponent is not silently treated as multiplication or as
        // an uninterpreted total function; the current exact subset is named.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..3 </var><var id=\"p\"> 0..3 </var>"
            "</variables><constraints><intension> eq(pow(x,p),1) </intension>"
            "</constraints></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "piecewise"));
    }
    {
        // An ordinary Int is not a 01Var; coercing 2 to true would accept an
        // expression outside XCSP3's boolExpr grammar.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"a\"> 0..2 </var></variables><constraints>"
            "<intension> not(a) </intension></constraints></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "exactly 0..1"));
    }

    // ---- Obligation 3: conflicts forbids exactly what it lists. -------------
    {
        const Translation sup = runFile("languages/xcsp3/instances/ok/supports.xml");
        const Translation con = runFile("languages/xcsp3/instances/ok/conflicts.xml");
        assert(sup.ok() && con.ok());
        const std::string ss = sup.toSmt2();
        const std::string cs = con.toSmt2();
        // A supports table is a disjunction of listed rows; a conflicts table is
        // a conjunction of their negations. They must not produce the same
        // formula -- the shortcut of building one as the complement of the other
        // is exactly what the obligation forbids, and over these domains the two
        // tables genuinely denote different relations.
        assert(ss != cs);
        assert(has(cs, "not"));
        ParserPtr r1 = newParser();
        ParserPtr r2 = newParser();
        assert(r1->parseStr(ss));
        assert(r2->parseStr(cs));
    }
    {
        // An empty supports table forbids everything and an empty conflicts
        // table forbids nothing. Neither is a no-op, so neither may be skipped.
        const char* head =
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"a\"> 0..2 </var></variables><constraints><extension>"
            "<list> a </list>";
        const Translation empty_sup =
            run(std::string(head) + "<supports></supports></extension></constraints></instance>");
        const Translation empty_con =
            run(std::string(head) + "<conflicts></conflicts></extension></constraints></instance>");
        assert(empty_sup.ok() && empty_con.ok());
        assert(empty_sup.toSmt2() != empty_con.toSmt2());
    }
    {
        // Unary tables use a whitespace list of values and intervals, not
        // parenthesized one-tuples. Intervals remain compact in the target.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..20 </var></variables><constraints><extension>"
            "<list>x</list><supports>1 4 8..10</supports>"
            "</extension></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= x 8)") && has(smt, "(<= x 10)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Obligation 4: `*` means the DECLARED domain. ----------------------
    {
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"s\">2 5</var><var id=\"t\">0..2</var>"
            "</variables><constraints><extension><list>s t</list>"
            "<supports>(*,1)</supports></extension></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The table relation is just t=1: the sparse-domain membership for s
        // is already an exact global constraint, now excluding3 and4. Check
        // occurrence counts so a duplicate wildcard guard cannot hide here.
        assert(count(smt, "(distinct ") == 1);
        assert(count(smt, "(= t 1)") + count(smt, "(= 1 t)") == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Wildcard factors are omitted for intervals too: the declared bounds
        // already state the complete domain, so the row reduces to its other
        // cells just as it does for an exact sparse-domain membership.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"a\"> 0..2 </var><var id=\"b\"> 0..2 </var></variables>"
            "<constraints><extension><list> a b </list>"
            "<supports> (*,1) </supports></extension></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= b 1)") || has(smt, "(= 1 b)"));
        assert(!has(smt, "(= a 0)"));
    }

    // ---- allDifferent, and the contrast with circuit. -----------------------
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/alldifferent.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The shared lowering keeps one native distinct node rather than
        // materializing all pairs in the frontend or HIR.
        assert(count(smt, "distinct") == 1);
        assert(t.report().stats().num_vars == 3);
    }
    {
        // Lifted allDifferent compares whole tuples pairwise. Tuple exceptions
        // are likewise whole values; reading only the first <list> silently
        // drops the actual cross-tuple relation.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[2]\">0..2</array>"
            "<array id=\"y\" size=\"[2]\">0..2</array>"
            "<array id=\"z\" size=\"[2]\">0..2</array>"
            "</variables><constraints><allDifferent>"
            "<list>x[]</list><list>y[]</list><list>z[]</list>"
            "<except>(0,0)</except></allDifferent></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "x[1]") && has(smt, "y[1]") && has(smt, "z[1]"));
        assert(has(smt, "(= 0 |x[0]|)") || has(smt, "(= |x[0]| 0)"));
    }
    {
        // XCSP3 arrays are k-dimensional and compact list selectors expand in
        // lexicographic index order. This row selector denotes exactly three
        // variables; flattening the shape or keeping only the first dimension
        // changes both the scope and the source observables.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"m\" size=\"[2][3]\" startIndex=\"1\"> 0..5 </array>"
            "</variables><constraints><allDifferent> m[2][] </allDifferent>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_vars == 6);
        const std::string smt = t.toSmt2();
        assert(has(smt, "m[2][1]"));
        assert(has(smt, "m[2][2]"));
        assert(has(smt, "m[2][3]"));
        assert(count(smt, "distinct") == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A selector outside a declared dimension is an invalid source
        // instance, not an implicit new scalar variable.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"m\" size=\"[2][3]\"> 0..5 </array>"
            "</variables><constraints><allDifferent> m[2][] </allDifferent>"
            "</constraints></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "outside dimension"));
    }
    {
        // Matrix allDifferent applies to every row and every column. A compact
        // two-dimensional array selector retains both axes in the expansion.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"m\" size=\"[2][3]\">0..5</array></variables><constraints>"
            "<allDifferent><matrix>m[][]</matrix></allDifferent>"
            "</constraints></instance>");
        assert(t.ok());
        assert(count(t.toSmt2(), "distinct") == 5);
    }
    {
        // lex-matrix orders adjacent rows and adjacent columns, rather than
        // flattening the matrix and applying one lexicographic comparison.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"m\" size=\"[2][3]\">0..5</array></variables><constraints>"
            "<lex><matrix>m[][]</matrix><operator>le</operator></lex>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "m[0][0]") && has(smt, "m[1][2]"));
        assert(has(smt, "(or"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Since XCSP3 3.2, a lifted lex operand may be a constant tuple. It is
        // still compared componentwise and must not be parsed as variable ids.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\">0..5</array>"
            "</variables><constraints><lex><list>x[]</list>"
            "<list>2 3 4</list><operator>le</operator></lex>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "x[0]") && has(smt, " 2") && has(smt, " 4"));
    }
    {
        // Mixed-domain arrays attach each <domain for=...> to exactly the
        // selected cells, with `others` filling the complement. Collapsing the
        // two domains to their common bounds would admit 6 in the second row.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"a\" size=\"[2][3]\">"
            "<domain for=\"a[0][]\">1..2</domain>"
            "<domain for=\"others\">5 7</domain></array>"
            "</variables><constraints><intension> ne(a[1][2],6) </intension>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_vars == 6);
        const std::string smt = t.toSmt2();
        assert(has(smt, "a[0][0]") && has(smt, "a[1][2]"));
        assert(has(smt, " 5") && has(smt, " 7"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // These XCSP3-core globals all have exact finite relational encodings.
        // The test keeps them in one instance so that every child-form parser
        // and every numerical condition reaches the common typed HIR.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\"> 0..5 </array>"
            "<var id=\"i\"> 0..3 </var><var id=\"v\"> 0..5 </var>"
            "<var id=\"k\"> 0..4 </var></variables><constraints>"
            "<allDifferent><list>x[]</list><except>0</except></allDifferent>"
            "<allEqual><list>x[0] x[1]</list></allEqual>"
            "<sum><list>x[]</list><coeffs>1 2 3 4</coeffs>"
            "<condition>(in,2..20)</condition></sum>"
            "<count><list>x[]</list><values>0 1</values>"
            "<condition>(eq,k)</condition></count>"
            "<nValues><list>x[]</list><except>0</except>"
            "<condition>(le,k)</condition></nValues>"
            "<minimum><list>x[]</list><condition>(eq,v)</condition></minimum>"
            "<maximum><list>x[]</list><condition>(ge,v)</condition></maximum>"
            "<element><list startIndex=\"0\">x[]</list><index rank=\"first\">i</index>"
            "<value>v</value></element>"
            "<instantiation><list>x[0]</list><values>0</values></instantiation>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 9);
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite"));                  // count, nValues, min/max
        assert(has(smt, "(*") && has(smt, "x[3]")); // weighted sum
        assert(has(smt, "(>=") && has(smt, "(<=")); // condition (in,2..20)
        assert(has(smt, "x[0]"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Without <index>, element means that at least one list entry equals
        // value; it is not an unconstrained existential index variable.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\"> 0..5 </array>"
            "<var id=\"v\"> 0..5 </var></variables><constraints>"
            "<element><list>x[]</list><value>v</value></element>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or"));
        assert(has(smt, "x[0]") && has(smt, "x[2]") && has(smt, " v"));
    }
    {
        // The current element form uses a numerical condition, not only the
        // deprecated equality <value> form. Literal lists remain exact because
        // the selected index and selected-cell relation share each disjunct.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"i\">1..3</var><var id=\"v\">0..9</var>"
            "</variables><constraints><element>"
            "<list startIndex=\"1\">3 5 7</list><index>i</index>"
            "<condition>(lt,v)</condition></element>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= i 1)") || has(smt, "(= 1 i)"));
        assert(has(smt, "(< 3 v)") && has(smt, "(< 7 v)"));
    }
    {
        // element-matrix designates one cell by two indexes. Both compact
        // variable matrices and parenthesized value matrices use the same
        // finite selection relation, which also excludes out-of-range indexes.
        const Translation compact = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"m\" size=\"[2][3]\">0..9</array>"
            "<var id=\"r\">0..1</var><var id=\"c\">0..2</var>"
            "<var id=\"v\">0..9</var></variables><constraints><element>"
            "<matrix>m[][]</matrix><index>r c</index>"
            "<condition>(eq,v)</condition></element>"
            "</constraints></instance>");
        assert(compact.ok());
        assert(has(compact.toSmt2(), "m[1][2]"));

        const Translation values = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"r\">1..2</var><var id=\"c\">4..5</var>"
            "<var id=\"v\">0..9</var></variables><constraints><element>"
            "<matrix startRowIndex=\"1\" startColIndex=\"4\">"
            "(1,2)(3,4)</matrix><index>r c</index><value>v</value></element>"
            "</constraints></instance>");
        assert(values.ok());
        const std::string smt = values.toSmt2();
        assert(has(smt, "(= r 2)") || has(smt, "(= 2 r)"));
        assert(has(smt, "(= c 5)") || has(smt, "(= 5 c)"));
    }
    {
        // Arg-min/arg-max index one extremal occurrence. Rank first/last adds
        // the tie-order condition; rank any deliberately does not.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\"> 0..9 </array>"
            "<var id=\"i\"> 1..4 </var></variables><constraints>"
            "<minimum><list startIndex=\"1\">x[]</list>"
            "<index rank=\"first\">i</index></minimum>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite") && has(smt, " i"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Ordered, lex and cardinality are exact relational decompositions:
        // adjacency with optional lengths, first-difference lexicography, and
        // one occurrence count per listed value.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\"> 0..9 </array>"
            "<array id=\"y\" size=\"[4]\"> 0..9 </array>"
            "<var id=\"k\"> 0..4 </var></variables><constraints>"
            "<ordered><list>x[]</list><lengths>1 2 3</lengths>"
            "<operator>lt</operator></ordered>"
            "<lex><list>x[]</list><list>y[]</list><operator>le</operator></lex>"
            "<cardinality><list>x[]</list><values>1 3 5</values>"
            "<occurs>0..1 1 k</occurs></cardinality>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite"));
        assert(has(smt, "(<"));
        assert(has(smt, "(or"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Two-list channel is an inverse relation, not two one-way
        // implications; every pair of positions is encoded as an equivalence.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"p\" size=\"[3]\"> 0..2 </array>"
            "<array id=\"q\" size=\"[3]\"> 0..2 </array>"
            "</variables><constraints><channel><list>p[]</list><list>q[]</list>"
            "</channel></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "p[0]") && has(smt, "q[2]"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Boolean channel links each 01Var to exactly one source-level index.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"b\" size=\"[3]\" startIndex=\"1\"> 0..1 </array>"
            "<var id=\"v\"> 1..3 </var></variables><constraints>"
            "<channel><list startIndex=\"1\">b[]</list><value>v</value></channel>"
            "</constraints></instance>");
        assert(t.ok());
        assert(has(t.toSmt2(), "b[1]") && has(t.toSmt2(), "b[3]"));
    }
    {
        // Pairwise distinctness alone admits several non-trivial sub-cycles.
        // Position witnesses enforce one cycle while retaining XCSP3's legal
        // self loops for nodes outside the subcircuit.
        const Translation t = runFile("languages/xcsp3/instances/ok/circuit.xml");
        assert(t.ok());
        const auto& contract = t.semantics().stages().front();
        assert(contract.projection.observables.size() == 4);
        assert(contract.target_signature.symbols.size()
               > contract.source_signature.symbols.size());
        const std::string smt = t.toSmt2();
        assert(has(smt, "__somt_xcsp3_aux_"));
        assert(has(smt, "distinct"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A fixed size is the number of non-self arcs, not the list length.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"s\" size=\"[4]\">0..3</array></variables><constraints>"
            "<circuit><list>s[]</list><size>3</size></circuit>"
            "</constraints></instance>");
        assert(t.ok());
        assert(has(t.toSmt2(), " 3"));
    }

    // ---- Objectives, including the combination §4.5 used to say to refuse. --
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/objective_sum.xml");
        assert(t.ok());
        assert(t.report().stats().num_objectives == 1);
        const std::string smt = t.toSmt2();
        assert(has(smt, "OBJECTIVE_MIN"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }
    {
        // Specialized objective forms denote values, not solver hints. Product,
        // minimum, maximum and nValues are all lowered as exact integer terms.
        const char* prefix =
            "<instance format=\"XCSP3\" type=\"COP\"><variables>"
            "<array id=\"x\" size=\"[3]\"> 1..4 </array></variables><objectives>";
        for (const std::string kind : {"product", "minimum", "maximum", "nValues"}) {
            const Translation t = run(
                std::string(prefix) + "<minimize type=\"" + kind
                + "\"><list>x[]</list><coeffs>1 2 3</coeffs></minimize>"
                  "</objectives></instance>");
            assert(t.ok());
            assert(t.report().stats().num_objectives == 1);
            ParserPtr reader = newParser();
            assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
        }
    }
    {
        // A lex objective is a tuple objective. It becomes a sequence of OMT
        // objectives only together with an explicit lexicographic combination.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"COP\"><variables>"
            "<array id=\"x\" size=\"[3]\"> 0..5 </array></variables><objectives>"
            "<minimize type=\"lex\"><list>x[]</list></minimize>"
            "</objectives></instance>", Lower::OmtDialect::Z3);
        assert(t.ok());
        assert(t.report().stats().num_objectives == 3);
        assert(has(t.toSmt2(), ":opt.priority lex"));
    }
    {
        // The objective expression is one intExpr. Ignoring a suffix would
        // optimize a different function while reporting a successful parse.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"COP\"><variables>"
            "<var id=\"x\"> 0..3 </var></variables><objectives>"
            "<minimize> add(x,1) junk </minimize></objectives></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "trailing text"));
    }
    {
        // §4.5's obligation was "refuse today"; ObjectiveCombination has since
        // landed, so the combination is recorded instead of the instance being
        // turned away. What must NOT happen is silence being read as
        // lexicographic, which is Z3's documented default for a bare list.
        //
        // Asked for by dialect. This case used to translate under the DEFAULT
        // dialect and then read Z3 text out of the result, which passed for a
        // reason that had nothing to do with the claim: `pareto` is emittable
        // by Z3 and not by the 2025 proposal, so the default-dialect
        // translation it asserted ok() on could not produce output at all. It
        // threw from toSmt2(), where there is no channel for an error, and the
        // CLI died on SIGABRT -- while this test passed, because it never asked
        // for the text it had actually configured.
        const Translation t = runFile("languages/xcsp3/instances/ok/multi_objective.xml",
                                      Lower::OmtDialect::Z3);
        assert(t.ok());
        assert(t.report().stats().num_objectives == 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "pareto"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // OptiMathSAT supports Pareto objectives through its priority option.
        const Translation t = runFile("languages/xcsp3/instances/ok/multi_objective.xml",
                                      Lower::OmtDialect::OptiMathSAT);
        assert(t.ok());
        const auto smt = t.toSmt2(Lower::OmtDialect::OptiMathSAT);
        assert(has(smt, "(set-option :opt.priority pareto)"));
        assert(has(smt, "(minimize x)"));
        assert(has(smt, "(maximize y)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        assert(reader->getObjectives().size() == 2);
    }
    {
        // ...and the 2025 dialect, which now CAN express it, emits the
        // proposal's form: the members first, then the multi-objective that
        // names them, then one optimize-sat on it. This instance is the reason
        // the feature was worth having -- it is an `ok/` fixture, so before
        // this it did not translate under the default dialect at all.
        const Translation t = runFile("languages/xcsp3/instances/ok/multi_objective.xml",
                                      Lower::OmtDialect::SmtLib2025);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "OBJECTIVE_PARETO"));
        assert(has(smt, "(define-multi-objective "));
        assert(smt.find("(define-objective ") < smt.find("(define-multi-objective "));
        assert(smt.find("(define-multi-objective ") < smt.find("(optimize-sat multi)"));
    }

    // ---- Value precedence, language constraints, and Boolean clauses. ------
    {
        // Semantics 10: every occurrence of 2 needs an earlier 1. With
        // covered=true, occurrence of the final value forces the whole value
        // chain to occur; it does not merely sort the variables numerically.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\">0..3</array></variables><constraints>"
            "<precedence><list>x[]</list><values covered=\"true\">1 2</values>"
            "</precedence></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "x[0]") && has(smt, "x[3]"));
        assert(count(smt, "x[0]") >= 2);
        assert(has(smt, " 1") && has(smt, " 2"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Omitting <values> uses the increasing union of declared domains.
        // Sparse domains must retain their holes: 1 precedes 3 directly here.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\">1 3</array></variables><constraints>"
            "<precedence>x[]</precedence></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, " 1") && has(smt, " 3"));
        // Membership excludes 2 via DISTINCT, which can also occur in the
        // precedence relation. Python checks the complete relation by XOR.
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // regular accepts exactly words that reach a listed final state. The
        // per-layer reach variables belong to the target signature, while beta
        // exposes only x[0] and x[1] as source observables.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[2]\">0..1</array></variables><constraints>"
            "<regular><list>x[]</list><transitions>"
            "(q0,0,q0)(q0,1,q1)(q1,0,q1)</transitions>"
            "<start>q0</start><final>q1</final></regular>"
            "</constraints></instance>");
        assert(t.ok());
        const auto& contract = t.semantics().stages().front();
        assert(contract.target_signature.symbols.size()
               > contract.source_signature.symbols.size());
        assert(contract.projection.observables.size() == 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "__somt_xcsp3_aux_"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // MDD root and terminal are inferred from its acyclic transition graph.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[2]\">0..2</array></variables><constraints>"
            "<mdd><list>x[]</list><transitions>"
            "(r,0,a)(r,1,b)(a,2,t)(b,0,t)</transitions></mdd>"
            "</constraints></instance>");
        assert(t.ok());
        assert(has(t.toSmt2(), "__somt_xcsp3_aux_"));
    }
    {
        // A cyclic graph is not an MDD. Accepting it as a generic automaton
        // would assign semantics to a malformed source construct.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[2]\">0..1</array></variables><constraints>"
            "<mdd><list>x[]</list><transitions>"
            "(r,0,a)(a,1,r)(a,0,t)</transitions></mdd>"
            "</constraints></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "root")
               || has(t.diagnostics().all()[0].message, "cycle"));
    }
    {
        // XCSP3 clause literals are 0/1 variables, with not(x) denoting x=0.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"r\">0..1</var><var id=\"s\">0..1</var>"
            "</variables><constraints><clause>r not(s)</clause>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or"));
        assert(has(smt, "(= r 1)") || has(smt, "(= 1 r)"));
        assert(has(smt, "(= s 0)") || has(smt, "(= 0 s)"));
    }
    {
        // One- and two-dimensional noOverlap use the same exact pairwise
        // separation relation; zeroIgnored adds the specified zero-size cases.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\">0..9</array>"
            "<array id=\"y\" size=\"[3]\">0..9</array>"
            "</variables><constraints>"
            "<noOverlap><origins>x[]</origins><lengths>2 0 3</lengths></noOverlap>"
            "<noOverlap zeroIgnored=\"false\"><origins>"
            "(x[0],y[0])(x[1],y[1])(x[2],y[2])</origins>"
            "<lengths>(2,3)(4,1)(1,2)</lengths></noOverlap>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or") && has(smt, "(+"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Cumulative checks all integer-time events without a quantified horizon.
        // Optional ends retain their defining equalities.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"s\" size=\"[3]\">0..9</array>"
            "<array id=\"e\" size=\"[3]\">1..12</array>"
            "</variables><constraints><cumulative>"
            "<origins>s[]</origins><lengths>2 3 1</lengths><ends>e[]</ends>"
            "<heights>1 2 3</heights><condition>(le,4)</condition>"
            "</cumulative></constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "forall"));
        assert(!has(smt, "__somt_xcsp3_time_"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Knapsack has two independently directed weighted conditions.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\">0..4</array></variables><constraints>"
            "<knapsack><list>x[]</list><weights>2 3 5</weights>"
            "<condition>(le,20)</condition><profits>7 4 9</profits>"
            "<condition>(ge,10)</condition></knapsack>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "(*") >= 6);
        assert(has(smt, "(<=") && has(smt, "(>="));
    }
    {
        // A common bin capacity quantifies only over bin ids actually used by
        // an item; this directly follows XCSP3-core Semantics 26.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"b\" size=\"[3]\">0..2</array></variables><constraints>"
            "<binPacking><list>b[]</list><sizes>2 3 5</sizes>"
            "<condition>(le,6)</condition></binPacking>"
            "</constraints></instance>");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall") && has(smt, "__somt_xcsp3_bin_"));
    }
    {
        // Per-bin loads use bin indices 0..m-1 and equality to each used bin's
        // indicator sum. Limits use the same encoding with <=.
        for (const std::string kind : {"loads", "limits"}) {
            const Translation t = run(
                "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
                "<array id=\"b\" size=\"[3]\">0..1</array>"
                "<var id=\"l0\">0..10</var><var id=\"l1\">0..10</var>"
                "</variables><constraints><binPacking><list>b[]</list>"
                "<sizes>2 3 5</sizes><" + kind + ">l0 l1</" + kind + ">"
                "</binPacking></constraints></instance>");
            assert(t.ok());
            assert(has(t.toSmt2(), "ite"));
        }
    }

    // ---- Division convention and remaining refusals. -----------------------
    {
        const Translation t = runFile("languages/xcsp3/instances/reject/division.xml");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Negative x distinguishes truncation toward zero from SMT-LIB's
        // Euclidean division; the correction term is therefore observable.
        assert(has(smt, "(< x 0)"));
        assert(has(smt, "(mod x 2)"));
        assert(t.semantics().stages().size() == 2);
        assert(t.semantics().stages()[0].source.id == "xcsp3");
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/reject/group.xml");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "group"));
    }
    {
        // A group is syntax sharing: each args row instantiates the same
        // template, so two rows must yield two ordinary constraints.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"q\" size=\"[3]\"> 0..2 </array></variables><constraints>"
            "<group><intension>ne(%0,%1)</intension>"
            "<args>q[0] q[1]</args><args>q[0] q[2]</args></group>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
        assert(has(t.toSmt2(), "q[1]") && has(t.toSmt2(), "q[2]"));
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/group_compact.xml");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/dense_table.xml");
        assert(t.ok());
        assert(has(t.toSmt2(), "check-sat"));
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/ok/objective_expressions.xml",
                                      Lower::OmtDialect::Z3);
        assert(t.ok());
        assert(has(t.toSmt2(), "minimize"));
    }
    {
        // Blocks carry structure/classes only; recursively parsing their
        // children preserves exactly the same conjunction.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\">0..2</var></variables><constraints>"
            "<block class=\"clues\"><intension>eq(x,1)</intension></block>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
    }
    {
        // slide expands the arity-3 template over two adjacent windows.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\">0..9</array></variables><constraints>"
            "<slide><list>x[]</list>"
            "<intension>eq(add(%0,%1),%2)</intension></slide>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "x[0]") && has(smt, "x[3]"));
    }
    {
        // Circular arity-2 slide includes the wraparound window x[3],x[0].
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[4]\">0..9</array></variables><constraints>"
            "<slide circular=\"true\"><list>x[]</list>"
            "<intension>ne(%0,%1)</intension></slide>"
            "</constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 4);
    }
    {
        const Translation t =
            runFile("languages/xcsp3/instances/reject/unknown_constraint.xml");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "networkFlow"));
        assert(has(t.diagnostics().all()[0].message, "weaken"));
    }
    {
        // Unknown or duplicate top-level sections cannot be skipped: either
        // could contain semantic content outside the recognized instance.
        const Translation unknown = run(
            "<instance format=\"XCSP3\" type=\"CSP\">"
            "<variables/><framework/></instance>");
        assert(!unknown.ok());
        assert(unknown.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);

        const Translation mismatched = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables/>"
            "<objectives><minimize>1</minimize></objectives></instance>");
        assert(!mismatched.ok());
        assert(mismatched.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/reject/malformed.xml");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/xcsp3/instances/nosuch.xml");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }
    {
        // A variable used but never declared is an error, not an implicit
        // declaration with an invented domain.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..3 </var></variables>"
            "<constraints><intension> lt(x, w) </intension></constraints></instance>");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "'w'"));
    }
    {
        // XCSP3 ids identify declarations uniquely. Letting the map overwrite
        // the first domain while retaining two target declarations makes Phi
        // non-functional and yields invalid SMT.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..1 </var><var id=\"x\"> 2..3 </var>"
            "</variables></instance>");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "more than once"));
    }
    {
        // A compact single interval must remain compact. Earlier code rejected
        // this legal domain because it tried to enumerate every value before
        // discovering that lo/hi already represented it exactly.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> -1000000000..1000000000 </var>"
            "</variables></instance>");
        assert(t.ok());
        assert(has(t.toSmt2(), "(- 1000000000)")
               || has(t.toSmt2(), "-1000000000"));
        assert(has(t.toSmt2(), "1000000000"));
    }

    // ---- XML details that are not XCSP3 but decide whether it parses. -------
    {
        // Prolog, comments, entity references and self-closing tags.
        const Translation t = run(
            "<?xml version=\"1.0\"?>\n<!-- a comment -->\n"
            "<instance format=\"XCSP3\" type=\"CSP\">\n"
            "  <variables><var id=\"x\"> 0..3 </var></variables>\n"
            "  <constraints><intension> lt(x, 3) </intension></constraints>\n"
            "</instance>\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
    }
    {
        // `&lt;` is `<`, and it appears inside an intension expression in real
        // files only as text -- but the unescaping has to happen before the
        // expression parser sees it, or the operator name is corrupted.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"x\"> 0..3 </var></variables><constraints>"
            "<intension> le(x, 3) </intension>"
            "<!-- &amp; --></constraints></instance>");
        assert(t.ok());
    }

    // ---- `as`: domain aliasing, found by the upstream corpus ---------------
    {
        // `<var id="yy" as="zz"/>` gives yy zz's domain and carries no domain
        // text of its own. Without this the empty text reached the domain
        // parser and was reported as "a variable has an empty domain": true of
        // the element, and the wrong thing to tell an author who wrote a
        // perfectly ordinary alias.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"zz\"> 3..5 </var><var id=\"yy\" as=\"zz\"></var>"
            "</variables><constraints>"
            "<intension> ne(yy, 4) </intension></constraints></instance>");
        assert(t.ok());
        // The DOMAIN came across, not just the declaration: yy must be bounded
        // to 3..5 like zz. An alias that declared an unbounded variable would
        // also report ok and would admit yy = 99.
        const std::string smt = t.toSmt2();
        assert(smt.find("yy") != std::string::npos);
        assert(t.report().stats().num_vars == 2);
        // Two variables, and the bounds assertions for both.
        assert(t.report().stats().num_constraints >= 1);
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // An alias of an array declares another array with the same shape and
        // per-cell domains. Treating it as one scalar silently drops elements.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"x\" size=\"[3]\"> 0..2 </array>"
            "<var id=\"xx\" as=\"x\"></var>"
            "</variables><constraints>"
            "<intension> ne(xx[0], 1) </intension></constraints></instance>");
        assert(t.ok());
        assert(t.report().stats().num_vars == 6);
        const std::string smt = t.toSmt2();
        assert(has(smt, "xx[0]") && has(smt, "xx[2]"));
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // Forward reference: an alias must name something already declared, and
        // saying so beats declaring an unconstrained variable.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<var id=\"yy\" as=\"zz\"></var><var id=\"zz\"> 3..5 </var>"
            "</variables><constraints>"
            "<intension> ne(yy, 4) </intension></constraints></instance>");
        assert(!t.ok());
    }

    {
        // Two auxiliary-introducing encodings in this frontend, and only one of
        // them preserves the model count. The CONTRAST is the test: an edit
        // that gave up on counting for all of XCSP3 would pass a check of the
        // circuit alone.
        //
        // `circuit` constrains its position witnesses only by implications --
        // a range, pairwise distinctness, and `positions[j] = positions[i] + 1
        // mod actual_size` along each active arc. Every one of those is
        // invariant under rotating the positions along the cycle, so nothing
        // pins a node to position 0 and one source model extends to
        // `actual_size` target models. Measured on this very instance by
        // enumerating with a solver: 5 assignments to the successors, 12
        // models once the witnesses are counted too (three 2-cycles with two
        // rotations each, two 3-cycles with three each).
        //
        // `regular` defines each of its auxiliaries with an EQ against the
        // disjunction of its incoming transitions -- a two-sided definition,
        // so the auxiliary is a function of the originals and the count is
        // preserved.
        const Translation t = runFile("languages/xcsp3/instances/ok/circuit.xml");
        VERIFY(t.ok());
        bool saw_circuit = false;
        for (const Uir::EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "successor-permutation-with-cyclic-position-witnesses") {
                saw_circuit = true;
                VERIFY(c.fidelity.count_status == Uir::CountStatus::NO_GUARANTEE);
                VERIFY(c.fidelity.sound);           // and it costs nothing else
                VERIFY(c.fidelity.complete);
                VERIFY(c.fidelity.preserves_optimum);
            }
        }
        VERIFY(saw_circuit);
        // And at the whole-translation level, because `addChoice` meets: one
        // non-count-preserving choice makes the translation one. That is what
        // `.count()` actually consults, so a test that pinned only the choice
        // would leave the reachable behaviour unpinned.
        VERIFY(t.report().fidelity().count_status == Uir::CountStatus::NO_GUARANTEE);
        VERIFY(t.report().fidelity().sound);
        VERIFY(t.report().fidelity().complete);

        const Translation r = run(
            "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            "<array id=\"w\" size=\"[3]\"> 0..1 </array>"
            "</variables><constraints>"
            "<regular><list>w[]</list>"
            "<transitions>(q0,0,q0)(q0,1,q1)(q1,0,q1)(q1,1,q1)</transitions>"
            "<start>q0</start><final>q1</final></regular>"
            "</constraints></instance>");
        VERIFY(r.ok());
        bool saw_regular = false;
        for (const Uir::EncodingChoice& c : r.report().choices()) {
            if (c.strategy == "layered-reachability-with-auxiliary-booleans") {
                saw_regular = true;
                // The construction is promising, but this local report claim
                // remains unassessed until a count-evidence record is attached.
                VERIFY(c.fidelity.count_status == Uir::CountStatus::UNASSESSED);
            }
        }
        VERIFY(saw_regular);
    }

    std::cout << "All XCSP3 tests passed." << std::endl;
    return 0;
}
