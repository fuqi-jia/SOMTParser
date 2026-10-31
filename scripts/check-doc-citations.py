#!/usr/bin/env python3
"""Check that docs/languages/*.md still describes the code it cites.

These documents are dense with pointers into the tree -- `src/hir/hir.cpp:98`,
`Op::NOT`, `Fidelity::underApprox()`, `docs/languages-scoping.md §3.1` -- and
every one of them is a claim that can quietly stop being true. It does not take
long: two citations in `docs/languages/dimacs-cnf.md` went stale the day after
it was written, from an unrelated edit that inserted comment lines above the
line they pointed at. The reader has no way to notice. The line still exists,
still contains plausible C++, and now says something else.

So the pointers are checked mechanically:

  * `path:line` and `path:line-line` -- the file exists and the line is in range.
  * A fenced code block whose first line is a `// path:line` marker -- the file
    still contains that text at that line. This is the strong form, and the one
    that catches a shifted line rather than a deleted file.
  * *Drift*: a bare `path:line` cannot be compared against a quote, so it is
    compared against its own sentence. If the markdown line holding the citation
    names a code-shaped identifier that the cited file contains, that identifier
    must appear within DRIFT_WINDOW lines of the citation. This is what catches
    a citation that slid off its construct and onto a different, real one --
    which the in-range and blank-line checks cannot see, and which is the normal
    way a citation rots. Adding this check found twelve of them at once.
  * `Ident::member` for the HIR and Fidelity vocabularies -- the identifier
    still exists in the header that defines it.
  * `<doc>.md §N` -- the target document has a section numbered N.

What this cannot check is whether the prose is *right*. It checks that the
things it names still exist and still say what was quoted, which is the part
that rots without anyone touching the document.

Usage:
    scripts/check-doc-citations.py                 # check docs/languages/
    scripts/check-doc-citations.py PATH [PATH...]  # check specific files
Exit code 0 if every citation resolves, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Vocabularies worth checking, and the header that defines each. A name used in
# a document but absent from its header means the document describes an API that
# no longer exists -- which for these docs is the difference between a design
# note and a fiction.
VOCAB = {
    "Op": "include/somtparser/hir/hir.h",
    "SortKind": "include/somtparser/hir/hir.h",
    "ExprKind": "include/somtparser/hir/hir.h",
    "ObjKind": "include/somtparser/hir/hir.h",
    "Bound": "include/somtparser/translation/fidelity.h",
    "Fidelity": "include/somtparser/translation/fidelity.h",
    "ErrorCode": "include/somtparser/translation/diagnostic.h",
    "Severity": "include/somtparser/translation/diagnostic.h",
}

# How far from a cited line a named identifier may be and still count as "this
# citation points at that construct". Ten lines is about one small function or
# struct -- generous enough that citing the first line of a construct and
# mentioning something from its middle still passes, tight enough that a
# citation that slid onto an unrelated function does not.
DRIFT_WINDOW = 10

# path:line or path:line-line, where path looks like a source path we own.
CITE_RE = re.compile(
    r"\b((?:src|include|languages|tools|test|python|scripts|docs|config|cmake)/"
    r"[\w./+-]+?\.(?:cpp|h|hpp|py|md|txt|json|cmake|sh|pyi|yml|yaml))"
    r":(\d+)(?:-(\d+))?\b"
)

# A fenced block opening with a `// path:line` (or `# path:line`) marker.
QUOTE_RE = re.compile(
    r"```(?:cpp|c\+\+|python|py|cmake|bash)?\n"
    r"\s*(?://|#)\s*"
    r"((?:src|include|languages|tools|test|python|scripts)/[\w./+-]+?\.\w+):(\d+)\s*\n"
    r"(.*?)```",
    re.DOTALL,
)

VOCAB_RE = re.compile(r"\b(" + "|".join(VOCAB) + r")::(\w+)")

# Section 5 of every one of these documents is "New HIR surface this format
# forces", so they name APIs on purpose that do not exist yet. A checker that
# treated those as stale would be wrong about the most interesting part of each
# document, and a checker that ignored them would let a genuine typo through.
# So a document declares its proposals, once, in a comment:
#
#     <!-- proposed-hir: ExprKind::NEXT, Op::IMPLIES -->
#
# and the check becomes two-directional. A name that exists is fine. A name that
# does not exist is fine only if it was declared. And a name that was declared as
# proposed but has since *landed* is an error too -- when Plan 2 adds
# ExprKind::NEXT, this document stops being a proposal and has to say so.
PROPOSED_RE = re.compile(r"<!--\s*proposed-hir:\s*(.*?)\s*-->", re.DOTALL)

# A third category, which the documents produced before the checker had a word
# for it: HIR that was **considered and rejected**.
#
#     <!-- rejected-hir: ExprKind::LIT_BIGINT -->
#
# ExprKind::LIT_BIGINT was recommended by three documents and deliberately not
# built: a big integer is the same literal with a bigger value, `long long` is a
# limit of a field rather than of the language, and a second kind would have
# obliged every consumer to handle both forever. The gap was closed by making
# LIT_INT text-backed instead (docs/languages/opb-wbo.md §4.6).
#
# Recording the rejection is more useful than deleting the name. It keeps the
# reasoning findable, and -- because this check fails if the name ever DOES
# appear -- it stops the same design being reintroduced without the document
# that argued against it being revisited.
REJECTED_RE = re.compile(r"<!--\s*rejected-hir:\s*(.*?)\s*-->", re.DOTALL)

# Every language document must declare what its format implies but does not
# write down, and how a frontend has to materialise it:
#
#     <!-- implicit-constraints:
#       a variable with no Bounds entry => VarDecl::lower_bound = 0   (§4.2)
#       a Binary variable => bounds forced to [0,1], overriding Bounds (§2.3)
#     -->
#
# This is required, not optional, and "none" is a legal answer only with a
# reason attached. The reason it is required: a translation is a mapping of
# *semantics*, and the §3 table -- "Construct -> HIR mapping" -- invites a
# reading where each construct becomes its counterpart and the job is done. The
# constructs that are not written down have no row in that table. An LP variable
# is non-negative whether or not the file says so; a PDDL action changes only
# what it names; an OPB variable takes values in {0,1} while being used
# arithmetically. Dropping any of them yields a strictly weaker model that
# parses, type-checks, round-trips, exits 0 and reports Fidelity::exact() --
# there is no value of Fidelity for "I translated a different problem".
#
# Each entry is a frontend obligation and, once that frontend exists, a fixture:
# an instance that is infeasible *only* because of the implicit constraint, so
# the test fails if the constraint is dropped.
IMPLICIT_RE = re.compile(r"<!--\s*implicit-constraints:\s*(.*?)\s*-->", re.DOTALL)

# `other-doc.md §3.1` / `docs/foo.md §12`
SECTION_RE = re.compile(r"([\w./-]+\.md)\s*§\s*(\d+(?:\.\d+)*)")


def read(path: Path) -> list[str] | None:
    try:
        return path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return None


class Checker:
    def __init__(self) -> None:
        self.problems: list[str] = []
        self.counts = {"line": 0, "quote": 0, "vocab": 0, "section": 0,
                       "implicit": 0, "drift": 0}
        self._cache: dict[str, list[str] | None] = {}

    def lines_of(self, rel: str) -> list[str] | None:
        if rel not in self._cache:
            self._cache[rel] = read(REPO / rel)
        return self._cache[rel]

    def problem(self, doc: Path, lineno: int, msg: str) -> None:
        self.problems.append(f"{doc.relative_to(REPO)}:{lineno}: {msg}")

    # --- path:line ---------------------------------------------------------
    def check_line_refs(self, doc: Path, text: str) -> None:
        for m in CITE_RE.finditer(text):
            rel, start, end = m.group(1), int(m.group(2)), m.group(3)
            at = text.count("\n", 0, m.start()) + 1
            lines = self.lines_of(rel)
            if lines is None:
                self.problem(doc, at, f"cites '{rel}', which does not exist")
                continue
            self.counts["line"] += 1
            last = int(end) if end else start
            if start < 1 or last > len(lines):
                self.problem(
                    doc, at,
                    f"cites {rel}:{m.group(2)}"
                    + (f"-{end}" if end else "")
                    + f", but that file has {len(lines)} lines",
                )
                continue
            # In range is a weak claim: a citation can point at a real line and
            # still be aimed at nothing. Eight of the first draft's citations in
            # minizinc.md were in range and wrong, because they were guessed
            # rather than looked up. A first line that is blank or a bare
            # closing brace is the cheap half of that signal -- it is never what
            # anyone meant to cite, and it is what a citation decays into as
            # code is inserted above it.
            head = lines[start - 1].strip()
            if head in ("", "}", "};", "){", ")", "{",
                        "return;", "break;", "continue;", "else", "else {"):
                self.problem(
                    doc, at,
                    f"cites {rel}:{m.group(2)}, which is "
                    + ("blank" if not head else f"just {head!r}")
                    + ". Cite the line the construct starts on.",
                )
                continue
            self.check_drift(doc, at, rel, start, last, text, m.start())

    def check_drift(self, doc: Path, at: int, rel: str, start: int, last: int,
                    text: str, offset: int) -> None:
        """Does the citation still point at the thing its sentence names?

        The blank/brace heuristic above catches a citation that decayed onto
        nothing. It cannot catch one that decayed onto *something else*: when
        `Hir::toString` was inserted into src/hir/hir.cpp, qcir.md's reference to
        mkOp's condAssert slid from line 307 onto `e->name = std::move(name);`,
        which is a real line of real code and passed every check. The quoted-
        snippet form caught the same drift in dimacs-cnf.md, because a quote can
        be compared; a bare path:line cannot.

        What can be compared is the prose. A citation almost always sits in a
        sentence that names the construct -- "`mkOp(Op::AND, {})` throws
        (`src/hir/hir.cpp:363`)". So: take the backticked identifiers near the
        citation, keep those that occur in the cited file at all, and require at
        least one of them within a window of the cited lines. An identifier the
        file never mentions says nothing about where in it to look, and is
        ignored rather than guessed at.
        """
        lines = self.lines_of(rel)
        if lines is None:
            return
        # The containing markdown line, and nothing more. A wider window reaches
        # into the neighbouring paragraph or table row and convicts a citation of
        # not matching prose that was never about it.
        nl_before = text.rfind("\n", 0, offset) + 1
        nl_after = text.find("\n", offset)
        sentence = text[nl_before:nl_after if nl_after != -1 else len(text)]

        names: set[str] = set()
        for tick in re.findall(r"`([^`\n]{1,80})`", sentence):
            for ident in re.findall(r"\b([A-Za-z_]\w{2,})\b", tick):
                # Code-shaped only: an interior capital or an underscore.
                # `cpp`, `include`, `double`, `weight` are English or path
                # fragments, and locate nothing.
                if "_" in ident or any(c.isupper() for c in ident):
                    names.add(ident)
        if not names:
            return

        # Only identifiers this file actually defines or mentions can locate
        # anything in it. `Fidelity` named beside a citation into hir.cpp is
        # about the other file and must not be evidence either way.
        # The cited file's own basename is not evidence: it appears in the
        # header comment and in the include guard, which "locates" line 1
        # whatever the citation was about.
        stem = rel.rsplit("/", 1)[-1].rsplit(".", 1)[0]
        names = {n for n in names if n != stem}
        body = "\n".join(lines)
        present = {n for n in names if n in body}
        if not present:
            return

        window = range(max(0, start - 1 - DRIFT_WINDOW),
                       min(len(lines), last + DRIFT_WINDOW))
        near = "\n".join(lines[i] for i in window)
        if any(n in near for n in present):
            return
        self.counts["drift"] += 1
        found = sorted(present)[:3]
        self.problem(
            doc, at,
            f"cites {rel}:{start}"
            + (f"-{last}" if last != start else "")
            + f", but {', '.join(repr(n) for n in found)} — named beside the "
            f"citation and present in that file — appears nowhere within "
            f"{DRIFT_WINDOW} lines of it. The citation has probably drifted; "
            f"re-point it, or quote the line so the drift is checkable.",
        )

    # --- quoted snippets ---------------------------------------------------
    def check_quotes(self, doc: Path, text: str) -> None:
        for m in QUOTE_RE.finditer(text):
            rel, start, body = m.group(1), int(m.group(2)), m.group(3)
            at = text.count("\n", 0, m.start()) + 1
            lines = self.lines_of(rel)
            if lines is None:
                self.problem(doc, at, f"quotes '{rel}', which does not exist")
                continue
            quoted = [ln for ln in body.splitlines() if ln.strip()]
            if not quoted:
                continue
            self.counts["quote"] += 1
            # The marker names where the FIRST quoted line lives.
            want = quoted[0].strip()
            have = lines[start - 1].strip() if start <= len(lines) else ""
            if want != have:
                where = [
                    i + 1 for i, ln in enumerate(lines) if ln.strip() == want
                ]
                hint = (
                    f" (it is now at line {where[0]})" if len(where) == 1
                    else f" (found at lines {where})" if where
                    else " (that text is no longer in the file)"
                )
                self.problem(
                    doc, at,
                    f"quotes {rel}:{start} as\n"
                    f"        {want!r}\n"
                    f"      but that line now reads\n"
                    f"        {have!r}{hint}",
                )

    # --- API vocabulary ----------------------------------------------------
    def check_vocab(self, doc: Path, text: str) -> None:
        proposed = set()
        for m in PROPOSED_RE.finditer(text):
            for item in re.split(r"[,\s]+", m.group(1)):
                if item:
                    proposed.add(item)
        rejected = set()
        for m in REJECTED_RE.finditer(text):
            for item in re.split(r"[,\s]+", m.group(1)):
                if item:
                    rejected.add(item)

        used_and_proposed = set()
        for m in VOCAB_RE.finditer(text):
            scope, name = m.group(1), m.group(2)
            qualified = f"{scope}::{name}"
            at = text.count("\n", 0, m.start()) + 1
            header = self.lines_of(VOCAB[scope])
            if header is None:
                self.problem(doc, at, f"vocabulary header {VOCAB[scope]} is missing")
                continue
            self.counts["vocab"] += 1
            # A DECLARATION, not a mention. The test was a plain substring
            # search over the header, so a name discussed in a comment counted
            # as existing -- hir.h explains why ExprKind::LIT_BIGINT was
            # deliberately NOT introduced, and that explanation was read as the
            # introduction. An enumerator or a member starts its line; a name in
            # prose does not.
            #
            # Matched forms: `NAME,`  `NAME }`  `NAME = 3,`  `NAME;`
            # and a leading `//` or `*` disqualifies the line, so a commented
            # enumerator does not count either.
            # Enumerators are often several to a line -- `BOOL, INT, REAL,` --
            # so the anchor is the DELIMITER after the name, not the start of
            # the line.
            # The real discriminator is the comment filter below, not the
            # punctuation: an enumerator, a member and a method all end
            # differently -- `INT,`  `Kind {`  `exact();` -- so the delimiter set
            # is generous and the "is this a comment line" test does the work.
            decl = re.compile(rf"\b{re.escape(name)}\b")
            exists = any(
                decl.search(ln) and not ln.lstrip().startswith(("//", "*", "/*"))
                for ln in header
            )
            if exists:
                if qualified in rejected:
                    self.problem(
                        doc, at,
                        f"declares {qualified} as rejected HIR, but it now exists in "
                        f"{VOCAB[scope]}. Either the document's reasoning was "
                        f"overturned and it should say so, or the name was "
                        f"reintroduced without revisiting it.",
                    )
                    continue
                if qualified in proposed:
                    self.problem(
                        doc, at,
                        f"declares {qualified} as proposed HIR, but it now exists in "
                        f"{VOCAB[scope]}. The document describes it as future work and "
                        f"no longer should.",
                    )
                continue
            if qualified in proposed or qualified in rejected:
                used_and_proposed.add(qualified)
                continue
            self.problem(
                doc, at,
                f"names {qualified}, which is not in {VOCAB[scope]}. If this is HIR "
                f"the format would force rather than HIR that exists, declare it: "
                f"<!-- proposed-hir: {qualified} -->",
            )

        # A declaration nothing uses is a leftover from an earlier draft, and it
        # would silently excuse a future typo of the same name.
        for stale in sorted(proposed - used_and_proposed):
            scope = stale.split("::")[0]
            header = self.lines_of(VOCAB.get(scope, ""))
            if header is not None and any(
                re.search(rf"\b{re.escape(stale.split('::')[1])}\b", ln) for ln in header
            ):
                continue    # already reported above as "now exists"
            self.problem(
                doc, 1,
                f"declares {stale} as proposed HIR but never mentions it",
            )

    # --- cross-document sections ------------------------------------------
    def check_sections(self, doc: Path, text: str) -> None:
        for m in SECTION_RE.finditer(text):
            ref, num = m.group(1), m.group(2)
            at = text.count("\n", 0, m.start()) + 1
            target = self.resolve_doc(doc, ref)
            if target is None:
                self.problem(doc, at, f"refers to '{ref}', which does not exist")
                continue
            lines = self.lines_of(target)
            if lines is None:
                continue
            self.counts["section"] += 1
            top = num.split(".")[0]
            # Sub-sections are often discussed without their own heading; only
            # the top-level number is required to exist as a heading.
            if not any(
                re.match(rf"^#+\s*{re.escape(top)}\.?\s", ln) for ln in lines
            ):
                self.problem(
                    doc, at,
                    f"refers to {ref} §{num}, but it has no section {top}",
                )

    def resolve_doc(self, doc: Path, ref: str) -> str | None:
        for cand in (REPO / ref, doc.parent / ref):
            if cand.exists():
                return str(cand.resolve().relative_to(REPO))
        return None

    # --- implicit constraints ---------------------------------------------
    def check_implicit(self, doc: Path, text: str) -> None:
        # Only language references carry this obligation. Other documents may be
        # passed explicitly (the risk register cites code too), and demanding a
        # format's implicit constraints from a document that describes no format
        # would be a check that cannot be satisfied rather than one that cannot
        # fail -- the mirror of the defect class this whole file guards against.
        try:
            in_languages = doc.resolve().parent == (REPO / "docs" / "languages")
        except OSError:
            in_languages = False
        if not in_languages:
            return
        blocks = IMPLICIT_RE.findall(text)
        if not blocks:
            self.problem(
                doc, 1,
                "has no <!-- implicit-constraints: ... --> block. Every language "
                "document must say what its format implies but does not write "
                "down, and how a frontend must materialise it. Write 'none => "
                "<reason>' if the format genuinely implies nothing.",
            )
            return
        if len(blocks) > 1:
            self.problem(doc, 1, "has more than one implicit-constraints block")
            return

        entries = [ln.strip() for ln in blocks[0].splitlines() if ln.strip()]
        if not entries:
            self.problem(doc, 1, "has an empty implicit-constraints block")
            return
        for e in entries:
            # "=>" is what makes an entry an obligation rather than a note: it
            # names the construct on the left and what has to be emitted on the
            # right. An entry without one is an observation nobody can act on.
            if "=>" not in e:
                self.problem(
                    doc, 1,
                    f"implicit-constraints entry has no '=>': {e!r}. Write "
                    f"'<what the format implies> => <what the frontend must emit>'.",
                )
                continue
            lhs, rhs = e.split("=>", 1)
            if not lhs.strip() or not rhs.strip():
                self.problem(doc, 1, f"implicit-constraints entry is half-empty: {e!r}")
                continue
            self.counts["implicit"] += 1

    def check(self, doc: Path) -> None:
        text = doc.read_text(encoding="utf-8", errors="replace")
        self.check_line_refs(doc, text)
        self.check_quotes(doc, text)
        self.check_vocab(doc, text)
        self.check_sections(doc, text)
        self.check_implicit(doc, text)


def main(argv: list[str]) -> int:
    if argv:
        docs = [Path(a).resolve() for a in argv]
    else:
        docs = sorted((REPO / "docs" / "languages").glob("*.md"))

    if not docs:
        # Reporting success over an empty set would make this check look like
        # coverage it does not have.
        print("error: no documents to check", file=sys.stderr)
        return 1

    checker = Checker()
    for doc in docs:
        if not doc.exists():
            print(f"error: {doc} does not exist", file=sys.stderr)
            return 1
        checker.check(doc)

    total = sum(checker.counts.values())
    for p in checker.problems:
        print(p, file=sys.stderr)

    print(
        f"{len(docs)} document(s): {checker.counts['line']} line reference(s), "
        f"{checker.counts['quote']} quoted snippet(s), "
        f"{checker.counts['vocab']} API name(s), "
        f"{checker.counts['section']} cross-reference(s), "
        f"{checker.counts['implicit']} implicit constraint(s) checked"
    )
    if checker.problems:
        print(f"{len(checker.problems)} stale citation(s)", file=sys.stderr)
        return 1
    if total == 0:
        print("error: nothing was actually checked", file=sys.stderr)
        return 1
    print("All citations resolve.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
