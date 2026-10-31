"""Materialize selected skill references for providers without filesystem access."""
import argparse
import hashlib
import json
from pathlib import Path

COMMON = ["SKILL.md", "references/api.md", "references/semantics.md",
          "references/routes.md", "references/output-contract.md",
          "references/macro-library.md", "references/fixed-template.md",
          "references/omt-dialects.md", "references/intent-and-logic.md",
          "references/repair.md"]
DOMAINS = {"linear": "references/linear-omt.md", "cp": "references/cp.md",
           "fol": "references/fol.md"}


def candidate_guidance(content, route):
    """Select whole documented sections; preserve the resource hash separately."""
    sections = content.split("\n## ")
    wanted = {"Construction repair", {"hir":"HIR candidate", "smtlib2":"Direct SMT candidate",
                                      "hybrid":"Hybrid candidate"}[route]}
    if route == "hybrid":
        wanted.add("HIR candidate")
    return sections[0] + "".join("\n## " + s for s in sections[1:] if s.split("\n",1)[0] in wanted)


def build_bundle(directory, mode="all", route=None):
    directory = Path(directory).resolve()
    if mode not in ("all", *DOMAINS):
        raise ValueError("unknown bundle mode")
    if route not in (None,"hir","smtlib2","hybrid"):
        raise ValueError("unknown bundle route")
    # An API provider cannot execute CLI steps. Keep its generation instructions
    # focused on candidate shapes and semantics, not the caller's result envelope.
    common = COMMON if route is None else ["references/provider-candidates.md", "references/semantics.md"]
    if route in ("hir","hybrid"):
        common += ["references/macro-library.md"]
    names = common + (list(DOMAINS.values()) if mode == "all" else [DOMAINS[mode]])
    parts, hashes = [], {}
    for name in names:
        path = (directory / name).resolve()
        if not path.is_relative_to(directory):
            raise ValueError("skill resource escapes bundle directory")
        content = path.read_text(encoding="utf-8")
        hashes[name] = hashlib.sha256(content.encode()).hexdigest()
        if name == "references/provider-candidates.md" and route is not None:
            content = candidate_guidance(content,route)
        parts.append("\n--- SKILL RESOURCE: " + name + " ---\n" + content)
    prompt = "\n".join(parts)
    return dict(schema="somt-skill-bundle-v1", mode=mode, route=route, resources=hashes,
                prompt=prompt, sha256=hashlib.sha256(prompt.encode()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["all", *DOMAINS], default="all")
    parser.add_argument("--skill-dir", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--route",choices=["hir","smtlib2","hybrid"])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    bundle = build_bundle(args.skill_dir, args.mode, args.route)
    manifest = args.output.with_suffix(args.output.suffix + ".manifest.json")
    if args.output.exists() or manifest.exists():
        raise ValueError("bundle output already exists; retain frozen versions")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(bundle.pop("prompt"), encoding="utf-8")
    manifest.write_text(json.dumps(bundle, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(dict(output=str(args.output), manifest=str(manifest), **bundle)))


if __name__ == "__main__":
    main()
