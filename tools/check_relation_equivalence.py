#!/usr/bin/env python3
"""Recheck an exact saved XOR obligation using directional entailments.

The input must contain one assertion, (xor LEFT RIGHT), with no objectives.
LEFT and RIGHT are the already-projected relations, including cost coordinates
when applicable. This tool does not infer observables or change either model.
"""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import time


def read_relations(script):
    import z3

    context = z3.Context()
    query = z3.Optimize(ctx=context)
    query.from_string(script)
    if len(query.objectives()):
        raise ValueError("the saved relation query must not contain objectives")
    assertions = query.assertions()
    if (len(assertions) != 1 or not z3.is_app(assertions[0])
            or assertions[0].decl().kind() != z3.Z3_OP_XOR):
        raise ValueError("expected exactly one assertion: (xor LEFT RIGHT)")
    if assertions[0].num_args() != 2:
        raise ValueError("the relation XOR must have exactly two operands")
    return assertions[0].arg(0), assertions[0].arg(1)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="SMT-LIB file with the exact XOR obligation")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout-ms", type=int, default=30000)
    parser.add_argument("--obligation-timeout-ms", type=int, default=1000)
    parser.add_argument("--memory-mib", type=int, default=2048)
    args = parser.parse_args(argv)
    if args.timeout_ms < 0 or args.obligation_timeout_ms <= 0 or args.memory_mib <= 0:
        parser.error("timeouts and memory budget must be positive (total timeout may be zero)")

    import resource

    memory_bytes = args.memory_mib * 1024 * 1024
    _, inherited_hard = resource.getrlimit(resource.RLIMIT_AS)
    if inherited_hard != resource.RLIM_INFINITY:
        memory_bytes = min(memory_bytes, inherited_hard)
    resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))

    import z3
    if __package__:
        from .semantic_checks.directional_equivalence import check_equivalence
    else:
        from semantic_checks.directional_equivalence import check_equivalence

    started = time.monotonic()
    raw = args.input.read_bytes()
    row = {
        "schema": "somt-saved-relation-equivalence-v1",
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "z3_version": z3.get_version_string(),
        "memory_bytes": memory_bytes,
        "checker_timeout_ms": args.timeout_ms,
        "per_obligation_timeout_ms": args.obligation_timeout_ms,
        "scope": "exact projected relations supplied by the caller; no generation or observable inference",
    }
    try:
        left, right = read_relations(raw.decode("utf-8"))
        row["parse_seconds"] = time.monotonic() - started
        comparison = check_equivalence(
            left, right, total_timeout_ms=args.timeout_ms,
            per_obligation_timeout_ms=args.obligation_timeout_ms)
        row.update(asdict(comparison))
        exit_code = 0
    except (ValueError, z3.Z3Exception) as error:
        row.update(status="invalid-input", equivalent=None, error=str(error))
        exit_code = 2
    row["total_seconds"] = time.monotonic() - started
    row["checker_sha256"] = hashlib.sha256(
        Path(check_equivalence.__code__.co_filename).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", encoding="utf-8") as stream:
        json.dump(row, stream, indent=2)
        stream.write("\n")
    print(json.dumps({key: row.get(key) for key in
                      ("status", "equivalent", "total_seconds", "input_sha256")}))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
