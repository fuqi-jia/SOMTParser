# Upstream corpus — OPB (pseudo-Boolean)

Unmodified files from `msakai/QPLIB-PB`, the 25 smallest `.opb` instances (all
at most 300 KB; the repository's largest is 13 MB and is not vendored).

- Source: https://github.com/msakai/QPLIB-PB/tree/main/instances
- Retrieved: 2026-09-21
- Licence: **CC-BY-4.0**, stated in the repository's `LICENSE`. Attribution is
  a condition, and this file is it: the instances are pseudo-Boolean
  optimization problems **converted from QPLIB** (the Quadratic Programming
  Library) by Masahiro Sakai. The conversion is the repository's contribution;
  the underlying models are QPLIB's.

## Audit on 2026-09-21

**25 of 25 translate.** The frontend read every file at its first attempt --
the first corpus in this tree to do so -- which is worth recording rather than
passing over: it means this corpus exercises the accepted path rather than the
refusal path, and the coverage number it supports comes from files nobody here
wrote.

These are optimization instances (`min:` objectives with linear and, after the
conversion, linearised quadratic terms), so they exercise the objective path
and `OmtEmitter`, not only the constraint path that a satisfaction corpus
reaches.
