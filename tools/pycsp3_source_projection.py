#!/usr/bin/env python3
"""Keep PyCSP3 compiler variables private in reference-model observations.

This is an explicitly executed reference-side adapter, never an NL generator.
It exports the original model unchanged and records object-identity provenance.
Projection changes metadata only: all XML/SMT constraints and costs must remain.
The private PyCSP3 registry layout is intentionally pinned to version 2.6.1.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import runpy
import sys
import xml.etree.ElementTree as ET


SCHEMA = "somt-pycsp3-source-projection-v1"
PY_CSP3_VERSION = "2.6.1"


def _sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def _namespace_bindings(namespace, variable_type):
    """Recognize explicit references without invoking overloaded Var equality."""
    bindings = {}
    seen = set()  # Shared source containers are visited once, including aliases.
    for name, value in namespace.items():
        if not isinstance(name, str) or name.startswith("__"):
            continue
        stack = [(value, name)]
        while stack:
            value, path = stack.pop()
            if isinstance(value, variable_type):
                bindings.setdefault(id(value), set()).add(path)
            elif isinstance(value, (list, tuple, dict)):
                if id(value) in seen:
                    continue
                seen.add(id(value))
                if isinstance(value, dict):
                    stack.extend((v, f"{path}[{k!r}]") for k, v in value.items())
                else:
                    stack.extend((v, f"{path}[{i}]") for i, v in enumerate(value))
    return bindings


def capture_provenance(namespace):
    """Capture the live registry after compilation; no prefix heuristics.

    A source-level ``x = Var()`` uses the same auxiliary factory as compiler
    normalization. Explicit namespace references therefore keep those variables
    public. Ordinary registered declarations remain public even when created in
    a source helper function rather than bound in the model's global namespace.
    """
    version = importlib.metadata.version("pycsp3")
    if version != PY_CSP3_VERSION:
        raise ValueError(f"PyCSP3 provenance requires {PY_CSP3_VERSION}, found {version}")
    from pycsp3.classes.entities import EVar, EVarArray, VarEntities
    from pycsp3.classes.main.constraints import auxiliary
    from pycsp3.classes.main.variables import Variable
    import pycsp3.classes.entities as entities_module
    import pycsp3.classes.main.constraints as constraints_module
    import pycsp3.classes.main.variables as variables_module
    import pycsp3.compiler as compiler_module
    import pycsp3.functions as functions_module

    owner = getattr(auxiliary, "obj", None)  # Do not create an auxiliary registry.
    introduced = [] if owner is None else owner._introduced_variables
    if isinstance(introduced, EVarArray):
        introduced_variables = introduced.flatVars
    elif isinstance(introduced, list) and not introduced:
        introduced_variables = []
    else:
        raise ValueError("Unrecognized PyCSP3 auxiliary registry layout")
    auxiliary_ids = {id(var) for var in introduced_variables}
    bindings = _namespace_bindings(namespace, Variable)
    variables = []
    entities = []
    by_symbol = {}
    by_identity = {}
    for entity in VarEntities.items:
        if isinstance(entity, EVar):
            members = [(entity.variable, [])]
            shape = []
        elif isinstance(entity, EVarArray):
            shape = list(entity.size)
            members = []
            stack = [(entity.variables, [])]
            while stack:
                value, indices = stack.pop()
                if isinstance(value, (list, tuple)):
                    stack.extend((v, indices + [i]) for i, v in reversed(list(enumerate(value))))
                elif value is not None:
                    members.append((value, indices))
        else:
            raise ValueError("Unrecognized PyCSP3 variable entity")
        entry = dict(name=entity.id, shape=shape, elements=[])
        for variable, indices in members:
            if not isinstance(variable, Variable):
                raise ValueError("Variable registry contains a non-variable member")
            symbol = variable.id
            if not isinstance(symbol, str) or not symbol:
                raise ValueError("Registered variable lacks an identifier")
            if symbol in by_symbol or id(variable) in by_identity:
                raise ValueError("Duplicate or aliased registered variable: " + symbol)
            source_bindings = sorted(bindings.get(id(variable), ()))
            introduced_by_compiler = id(variable) in auxiliary_ids
            role = ("compiler-private" if introduced_by_compiler and not source_bindings
                    else "source-public")
            record = dict(source_symbol=symbol, entity=entity.id, index=indices,
                          pycsp3_type=str(variable.dom.type), role=role,
                          auxiliary_registry_member=introduced_by_compiler,
                          explicit_source_bindings=source_bindings)
            by_symbol[symbol] = record
            by_identity[id(variable)] = symbol
            variables.append(record)
            entry["elements"].append(dict(index=indices, source_symbol=symbol, role=role))
        entities.append(entry)
    if not auxiliary_ids.issubset(by_identity):
        raise ValueError("Auxiliary registry contains variables absent from the exported registry")
    modules = [entities_module, constraints_module, variables_module, compiler_module, functions_module]
    return dict(schema=SCHEMA, pycsp3_version=version,
                registry_basis="VarEntities.items and identity membership in auxiliary.obj._introduced_variables",
                source_binding_policy="explicit model namespace references retain factory-created variables",
                package_files={str(Path(m.__file__).resolve()): _sha(m.__file__) for m in modules},
                entities=entities, variables=variables,
                public_source_symbols=[v["source_symbol"] for v in variables if v["role"] == "source-public"],
                compiler_private_symbols=[v["source_symbol"] for v in variables if v["role"] == "compiler-private"])


def project_observables(metadata, provenance, source_to_target=None):
    """Return metadata for the exact source projection, retaining all costs.

    ``source_to_target`` is an explicit full name map when lowering renamed any
    source identifiers. No quoting, suffix, or prefix inference is performed.
    All source-public symbols must be represented once in the input metadata.
    Array shape is retained; elements specify the exact observed coordinates.
    """
    if provenance.get("schema") != SCHEMA or provenance.get("pycsp3_version") != PY_CSP3_VERSION:
        raise ValueError("Unsupported or missing variable provenance")
    records = provenance["variables"]
    roles = {v["source_symbol"]: v["role"] for v in records}
    if len(roles) != len(records) or any(r not in ("source-public", "compiler-private") for r in roles.values()):
        raise ValueError("Ambiguous variable provenance")
    public = {s for s, r in roles.items() if r == "source-public"}
    private = set(roles) - public
    if set(provenance["public_source_symbols"]) != public or set(provenance["compiler_private_symbols"]) != private:
        raise ValueError("Inconsistent provenance role inventories")
    mapping = dict(source_to_target) if source_to_target is not None else {s: s for s in roles}
    if set(mapping) != set(roles) or any(not isinstance(v, str) or not v for v in mapping.values()):
        raise ValueError("Source-to-target map must cover the complete variable registry")
    reverse = {target: source for source, target in mapping.items()}
    if len(reverse) != len(mapping):
        raise ValueError("Ambiguous source-to-target variable map")
    result = copy.deepcopy(metadata)
    kept = []
    removed = []
    seen = set()
    for observable in result["observables"]:
        retained = []
        for element in observable["elements"]:
            target = element["symbol"]
            if target not in reverse:
                raise ValueError("Observable has no captured source variable: " + target)
            source = reverse[target]
            if source in seen:
                raise ValueError("Duplicate observed source variable: " + source)
            seen.add(source)
            if source in public:
                retained.append(element)
            else:
                removed.append(dict(source_symbol=source, target_symbol=target,
                                    observable=observable["name"], index=element["index"]))
        if retained:
            observable["elements"] = retained
            kept.append(observable)
    if public - seen:
        raise ValueError("Source-public variables absent from export metadata: " + repr(sorted(public - seen)))
    result["observables"] = kept
    result["projection"] = "source-public variables; compiler-private variables remain existentially hidden"
    result["source_projection"] = dict(schema=SCHEMA,
        provenance_sha256=hashlib.sha256(json.dumps(provenance, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest(),
        source_to_target=mapping, hidden_compiler_variables=removed,
        constraints_changed=False, objectives_changed=False)
    return result


def export_model(model, data, cwd, xml, provenance_path, options=()):
    """Execute a trusted reference model with its original path and full cwd."""
    model, data, cwd, xml, provenance_path = [Path(p).resolve() for p in (model, data, cwd, xml, provenance_path)]
    if not model.is_file() or not data.is_file() or not cwd.is_dir():
        raise ValueError("Missing original model, data, or problem directory")
    if xml.exists() or provenance_path.exists():
        raise ValueError("Refusing to overwrite a previous export")
    if importlib.metadata.version("pycsp3") != PY_CSP3_VERSION:
        raise ValueError("Unsupported PyCSP3 provenance registry version")
    allowed_flags = {"-accept_and_or_extensional_use", "-force_element_index", "-dont_adjust_indexing",
                     "-dont_run_compactor", "-dont_build_similar_constraints", "-mini", "-sober", "-ev"}
    if any(option not in allowed_flags and not option.startswith("-variant=") for option in options):
        raise ValueError("Unsupported reference compiler option")
    model_sha, data_sha = _sha(model), _sha(data)
    old_argv, old_path, old_cwd = sys.argv[:], sys.path[:], Path.cwd()
    sys.argv = [str(model), "-data=" + str(data), "-output=" + str(xml), *options]
    sys.path.insert(0, str(model.parent))
    os.chdir(cwd)
    try:
        namespace = runpy.run_path(str(model), run_name="__main__")
        from pycsp3.compiler import Compilation
        from pycsp3.tools.utilities import Error
        if Error.errorOccurrence:
            raise ValueError("PyCSP3 reported an error before compilation")
        if not Compilation.done:
            Compilation.compile(disabling_opoverrider=True)
        if not xml.is_file() or ET.parse(xml).getroot().tag != "instance":
            raise ValueError("PyCSP3 did not produce a complete XCSP3 instance")
        provenance = capture_provenance(namespace)
        if _sha(model) != model_sha or _sha(data) != data_sha:
            raise ValueError("Reference source or data changed during export")
        provenance.update(model=dict(path=str(model), sha256=model_sha),
                          data=dict(path=str(data), sha256=data_sha),
                          cwd=str(cwd), compiler_options=list(options),
                          xml=dict(path=str(xml), sha256=_sha(xml), bytes=xml.stat().st_size),
                          model_bytes_changed=False)
        provenance_path.parent.mkdir(parents=True, exist_ok=True)
        with provenance_path.open("x") as stream:
            json.dump(provenance, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
        return provenance
    finally:
        # A failed wrapper must not cause an atexit second export of a partial model.
        compiler = sys.modules.get("pycsp3.compiler")
        if compiler is not None:
            compiler.Compilation.done = True
        sys.argv, sys.path = old_argv, old_path
        os.chdir(old_cwd)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    export = sub.add_parser("export")
    for name in ("model", "data", "cwd", "xml", "provenance"):
        export.add_argument("--" + name, required=True, type=Path)
    export.add_argument("--option", action="append", default=[])
    args = parser.parse_args()
    provenance = export_model(args.model, args.data, args.cwd, args.xml, args.provenance, args.option)
    print(json.dumps(dict(xml_sha256=provenance["xml"]["sha256"],
                          public_variables=len(provenance["public_source_symbols"]),
                          compiler_private_variables=len(provenance["compiler_private_symbols"]))))


if __name__ == "__main__":
    main()
