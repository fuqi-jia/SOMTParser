"""No-network bridge to real SOMTParser candidates and isolated Z3 checks."""
import argparse
import hashlib
import inspect
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def reject_constant(value):
    raise ValueError("non-finite JSON number: " + value)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object, parse_constant=reject_constant)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def emit(value, path=None):
    text = json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n"
    if path is None:
        print(text, end="")
    else:
        with Path(path).open("x", encoding="utf-8") as stream:
            stream.write(text)


def request_for(source, context, language="smtlib2"):
    import somtparser as sp
    captured = {}
    class Captured(Exception):
        pass
    def capture(request):
        captured.update(request)
        raise Captured()
    try:
        sp.propose_nl(source, provider=capture, language=language, context=context)
    except Captured:
        pass
    if not captured:
        raise ValueError("public API did not provide a request")
    return captured


def source_link(source, program, quote, fragment, occurrence=None):
    if not quote or not fragment or fragment not in program:
        raise ValueError("quote must be nonempty and fragment must occur in program")
    offsets, start = [], 0
    while True:
        index = source.find(quote, start)
        if index < 0:
            break
        offsets.append(index)
        start = index + 1
    if not offsets:
        raise ValueError("quotation does not occur in source")
    if occurrence is None:
        if len(offsets) != 1:
            raise ValueError("quotation repeats; select --occurrence explicitly")
        occurrence = 0
    if occurrence < 0 or occurrence >= len(offsets):
        raise ValueError("occurrence is out of range")
    start = offsets[occurrence]
    return dict(span=[start, start + len(quote)], fragment=fragment)


def check_worker(args):
    import resource
    limit = args.memory_mib * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    import z3
    started = time.monotonic()
    report = dict(script_sha256=digest(args.script), z3_version=z3.get_version_string(),
                  memory_mib=args.memory_mib, timeout_seconds=args.timeout_seconds,
                  equivalence="not-checked", intent_preservation="not-proved")
    try:
        optimizer = z3.Optimize()
        optimizer.set(timeout=max(1, int(args.timeout_seconds * 1000)))
        optimizer.from_string(args.script.read_text(encoding="utf-8"))
        report.update(status="loaded", load="passed", assertions=len(optimizer.assertions()),
                      objectives=len(optimizer.objectives()))
        if args.solve:
            result = optimizer.check()
            report.update(status="solved" if result != z3.unknown else "solver-unknown",
                          verdict=str(result), optimality="not-certified-by-this-report")
            if result == z3.sat:
                model = optimizer.model()
                report["model_smt2"] = model.sexpr()
                report["normalized_objective_values"] = [
                    dict(expression=obj.sexpr(), value=model.eval(obj, model_completion=False).sexpr())
                    for obj in optimizer.objectives()]
            elif result == z3.unknown:
                report["reason_unknown"] = optimizer.reason_unknown()
    except Exception as exc:
        report.update(status="check-error", diagnostic=type(exc).__name__ + ": " + str(exc))
    report["elapsed_seconds"] = round(time.monotonic() - started, 6)
    emit(report, args.out / "check.json")
    return 0 if report["status"] in ("loaded", "solved") else 2


def run_check(args):
    args.out.mkdir(parents=True, exist_ok=False)
    command = [sys.executable, str(Path(__file__).resolve()), "_check", str(args.script.resolve()),
               "--out", str(args.out.resolve()), "--timeout-seconds", str(args.timeout_seconds),
               "--memory-mib", str(args.memory_mib)]
    if args.solve:
        command.append("--solve")
    started = time.monotonic()
    report = None
    with (args.out / "worker.log").open("w") as log:
        child = subprocess.Popen(command, stdout=log, stderr=log, start_new_session=True)
        try:
            child.wait(timeout=args.timeout_seconds)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            report = dict(status="worker-timeout")
    path = args.out / "check.json"
    if report is None and path.exists():
        report = read_json(path)
    elif report is None:
        report = dict(status="worker-error", returncode=child.returncode)
    if not path.exists():
        report.update(script_sha256=digest(args.script), timeout_seconds=args.timeout_seconds,
                      memory_mib=args.memory_mib, elapsed_seconds=time.monotonic() - started,
                      equivalence="not-checked", intent_preservation="not-proved")
        emit(report, path)
    emit(report)
    return 0 if report["status"] in ("loaded", "solved") else 2


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    catalog = sub.add_parser("catalog")
    catalog.add_argument("--out", type=Path)
    request = sub.add_parser("request")
    validate = sub.add_parser("validate")
    for command in (request, validate):
        command.add_argument("source", type=Path)
        command.add_argument("--context", type=Path)
        command.add_argument("--out", type=Path, required=command is validate)
    validate.add_argument("model", type=Path)
    compile_parser = sub.add_parser("compile")
    compile_parser.add_argument("candidate", type=Path)
    compile_parser.add_argument("--digest", required=True)
    compile_parser.add_argument("--out", type=Path, required=True)
    link = sub.add_parser("link")
    link.add_argument("source", type=Path)
    link.add_argument("program", type=Path)
    link.add_argument("--quote", required=True)
    link.add_argument("--fragment", required=True)
    link.add_argument("--occurrence", type=int)
    for name in ("check", "_check"):
        check = sub.add_parser(name)
        check.add_argument("script", type=Path)
        check.add_argument("--out", type=Path, required=True)
        check.add_argument("--solve", action="store_true")
        check.add_argument("--timeout-seconds", type=float, default=30)
        check.add_argument("--memory-mib", type=int, default=2048)
    args = parser.parse_args(argv)
    if args.command in ("check", "_check"):
        if not math.isfinite(args.timeout_seconds) or args.timeout_seconds <= 0 or args.memory_mib <= 0:
            parser.error("resource budgets must be positive and finite")
        return check_worker(args) if args.command == "_check" else run_check(args)
    if args.command == "link":
        emit(source_link(args.source.read_text(encoding="utf-8"),
                         args.program.read_text(encoding="utf-8"), args.quote,
                         args.fragment, args.occurrence))
        return 0

    import somtparser as sp
    from somtparser.natural_language import Candidate
    if args.command == "catalog":
        import somtparser.natural_language as nl
        import z3
        package = Path(sp.__file__).parent
        files = [Path(sp.__file__), Path(nl.__file__)] + list(package.glob("*.so"))
        emit(dict(apis={name:str(inspect.signature(getattr(sp, name))) for name in
                        ("propose_nl", "propose_nl_with_repair", "compile_candidate")},
                  schema=request_for("Describe a constraint problem.", {})["schema"],
                  runtime={str(p.resolve()):digest(p) for p in files},
                  z3_version=z3.get_version_string(),
                  required_outputs="HIR-only; not accepted for smtlib2"), args.out)
        return 0
    if args.command == "compile":
        candidate = Candidate.from_json(args.candidate.read_text(encoding="utf-8"))
        result = sp.compile_candidate(candidate, accept_digest=args.digest)
        args.out.mkdir(parents=True, exist_ok=False)
        emit(result.report(), args.out / "report.json")
        if result.ok:
            (args.out / "model.smt2").write_text(result.to_smt2(), encoding="utf-8")
        emit(dict(ok=result.ok, digest=candidate.digest, diagnostics=list(result.diagnostics)))
        return 0 if result.ok else 2

    source = args.source.read_text(encoding="utf-8")
    context = read_json(args.context) if args.context else {}
    if args.command == "request":
        emit(request_for(source, context), args.out)
        return 0
    model = read_json(args.model)
    candidate = sp.propose_nl(source, provider=lambda request:model,
                              language="smtlib2", context=context)
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / "candidate.json").write_text(candidate.to_json() + "\n", encoding="utf-8")
    report = dict(valid=candidate.valid, digest=candidate.digest,
                  source_sha256=candidate.source_sha256, diagnostics=list(candidate.diagnostics),
                  diagnostic_details=candidate.diagnostic_details,
                  intent_preservation="not-proved")
    emit(report, args.out / "validation.json")
    emit(report)
    return 0 if candidate.valid else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, TypeError, KeyError) as exc:
        emit(dict(ok=False, error=type(exc).__name__ + ": " + str(exc)))
        raise SystemExit(2)
