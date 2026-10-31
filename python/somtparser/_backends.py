"""Solver backends, as subprocesses over a text protocol.

One code path for every backend, and the reason is model counting: d4, ganak
and sharpSAT ship only binaries, as do most MaxSAT and pseudo-Boolean solvers.
An in-process path for z3 and cvc5 alongside would mean two error shapes, two
sets of semantics to keep aligned, and every test written twice.

Each backend declares the OMT dialect its syntax requires. Binding the backend
is therefore what makes a dialect mismatch unrepresentable -- before this a
caller could render OptiMathSAT syntax and hand it to z3.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from typing import Callable, Sequence


@dataclass(frozen=True)
class BackendSpec:
    """How to run one solver and read what it says."""

    name: str
    binary: str
    dialect: str                      # an OmtDialect attribute name
    args: Sequence[str] = ()
    seed_flag: str | None = None
    #: Maps stdout to ("sat"|"unsat"|"unknown", payload). Payload is the model
    #: text for solvers and the count for counters.
    reads: str = "smt"                # "smt" | "count"
    install_hint: str = ""
    #: "stdin" (the text is piped in) or "file" (the text is written to a
    #: temp file and the path is passed on argv). Counting backends read
    #: DIMACS from a file, not stdin.
    input_mode: str = "stdin"         # "stdin" | "file"
    #: The flag that precedes the file path (e.g. "-i"). None means the path
    #: is a bare positional argument.
    file_flag: str | None = None


def _smt_status(stdout: str) -> tuple[str, str]:
    head = stdout.strip().split("\n", 1)
    first = head[0].strip() if head else ""
    rest = head[1] if len(head) > 1 else ""
    if first in ("sat", "unsat", "unknown"):
        return first, rest
    return "unknown", stdout


def _count_status(stdout: str) -> tuple[str, str]:
    """The count a counter reported, or `unknown`.

    The count is looked for on a line the counter MARKED as its answer --
    `s <n>` (the SAT-competition convention d4 and ganak follow) or
    `c s exact arb int <n>` (the Model Counting Competition's own line). Only
    if no marked line exists does a bare numeric line count, and then the
    FIRST one wins, not the last.

    Scanning backwards for any digits looks more tolerant and is worse: every
    one of these tools prints timing and memory after its answer, so the last
    numeric line is routinely a decision count or a millisecond total. A
    wrong count is far more damaging than a refused one, because nothing
    downstream can tell it from a right one.
    """
    marked = None
    bare = None
    for line in stdout.strip().split("\n"):
        text = line.strip()
        if not text:
            continue
        token = None
        if text.startswith("s "):
            token = text[2:].strip()
        elif text.startswith("c s "):
            # `c s exact arb int 1024` -- the answer is the last field.
            fields = text.split()
            token = fields[-1] if fields else None
        if token is not None:
            if _is_count(token) and marked is None:
                marked = token
            continue
        if _is_count(text) and bare is None:
            bare = text
    answer = marked if marked is not None else bare
    return ("sat", answer) if answer is not None else ("unknown", stdout)


def _is_count(token: str) -> bool:
    """A non-negative integer, possibly huge. Counters print exact integers of
    arbitrary size, so `int` is the right predicate and `float` is not: a
    count read through a float would be silently rounded."""
    return token.isdigit()


READERS: dict[str, Callable[[str], tuple[str, str]]] = {
    "smt": _smt_status,
    "count": _count_status,
}


BACKENDS: dict[str, BackendSpec] = {
    "z3": BackendSpec(
        name="z3", binary="z3", dialect="Z3", args=("-in",),
        seed_flag="smt.random_seed=",
        install_hint="pip install z3-solver, or install the z3 binary",
    ),
    "cvc5": BackendSpec(
        name="cvc5", binary="cvc5", dialect="Z3", args=("--lang=smt2",),
        seed_flag="--seed=",
        install_hint="see https://cvc5.github.io for a binary release",
    ),
    "optimathsat": BackendSpec(
        name="optimathsat", binary="optimathsat", dialect="OptiMathSAT",
        install_hint="see https://optimathsat.disi.unitn.it",
    ),
    # `smtlib` renders the SMT 2025 proposal syntax. No solver implements it
    # yet, so it has no binary: it exists to PRODUCE standardised benchmark
    # text, which is the whole argument for the dialect.
    "smtlib": BackendSpec(
        name="smtlib", binary="", dialect="SmtLib2025",
        install_hint="this dialect is for emitting text; no solver reads it yet",
    ),
    # The classic CRIL d4 CLI selects model counting with -mc and takes a
    # positional DIMACS file. Other d4 versions may override args explicitly.
    "d4": BackendSpec(
        name="d4", binary="d4", dialect="NONE", reads="count",
        args=("-mc",), input_mode="file",
        install_hint="see https://github.com/crillab/d4",
    ),
    "ganak": BackendSpec(
        name="ganak", binary="ganak", dialect="NONE", reads="count",
        input_mode="file",
        install_hint="see https://github.com/meelgroup/ganak",
    ),
}


class BackendNotFound(RuntimeError):
    """A backend is unknown, or its binary is not installed."""


def spec(name: str) -> BackendSpec:
    try:
        return BACKENDS[name]
    except KeyError:
        known = ", ".join(sorted(BACKENDS))
        raise BackendNotFound(
            f"unknown backend {name!r}; this build knows: {known}"
        ) from None


def backend_path(name: str) -> str | None:
    """The binary for @p name, or None. Never raises for an unknown name, so a
    `skipif` can ask about a backend that does not exist."""
    if name not in BACKENDS:
        return None
    s = BACKENDS[name]
    if not s.binary:
        return None
    found = shutil.which(s.binary)
    if found is not None:
        return found
    # The pip packages install their executable beside the interpreter, which
    # is on PATH only when the venv is activated -- and this project's own
    # recipe invokes pytest by absolute path. Looking here is what stopped 41
    # natural-language tests silently skipping on 2026-09-20.
    beside = os.path.join(os.path.dirname(sys.executable), s.binary)
    # `os.access(X_OK)` rather than `exists`: a directory, or a file of the
    # right name with no execute bit, satisfies `exists` and would then be
    # handed to subprocess.run, which raises IsADirectoryError or
    # PermissionError. Those escape the BackendNotFound contract that says a
    # missing binary is reported as one specific, explaining exception.
    if os.path.isfile(beside) and os.access(beside, os.X_OK):
        return beside
    return None


def run(name: str, script: str, timeout: float | None, seed: int | None,
        path: str | None, args: Sequence[str] | None = None) -> tuple[str, str, float]:
    """Run the backend over @p script. Returns (status, payload, seconds)."""
    s = spec(name)
    binary = path or backend_path(name)
    if binary is None:
        raise BackendNotFound(
            f"backend {name!r} needs the {s.binary or name!r} binary, which was "
            f"not found on PATH or beside {sys.executable}. {s.install_hint}"
        )
    argv = [binary, *(args if args is not None else s.args)]
    if seed is not None and s.seed_flag:
        argv.append(f"{s.seed_flag}{seed}")

    cnf_path = None
    stdin_input = script
    if s.input_mode == "file":
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
            fh.write(script)
            cnf_path = fh.name
        if s.file_flag:
            argv += [s.file_flag, cnf_path]
        else:
            argv.append(cnf_path)
        stdin_input = None

    started = time.monotonic()
    try:
        try:
            done = subprocess.run(argv, input=stdin_input, text=True,
                                  capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "unknown", "timeout", time.monotonic() - started
    finally:
        if cnf_path is not None:
            os.unlink(cnf_path)
    seconds = time.monotonic() - started
    if done.returncode not in (0, 10, 20):
        # 10/20 are SAT-competition conventions for sat/unsat.
        # Z3 writes SMT-LIB rejection diagnostics to stdout. Keeping only
        # stderr turns a specific unsupported operator into an empty "crash".
        details = "\n".join(part.strip() for part in (done.stderr, done.stdout)
                            if part.strip())
        return "unknown", f"crash: exit {done.returncode}; {details[:1000]}", seconds
    status, payload = READERS[s.reads](done.stdout)
    return status, payload, seconds
