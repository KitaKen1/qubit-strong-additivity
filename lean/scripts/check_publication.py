#!/usr/bin/env python3
"""Check that the publication's specification copies and proof packaging agree."""
from pathlib import Path
import json
import re
from make_lean4web import code_mask

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent


def main():
    config = json.loads((LEAN / "ComparatorChallenges/QubitHolevoAdditivity.json").read_text())
    if set(config["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("Unexpected permitted axioms")
    model = (LEAN / "QubitAdditivity/Presentation/Model.lean").read_text()
    vocabulary = model.split("-- BEGIN MODEL\n", 1)[1].split("-- END MODEL", 1)[0].strip()
    fc = (ROOT / "FClikelean/QubitHolevoAdditivity.lean").read_text()
    # The definitions lie between the `open` lines and the docstring of the first theorem.
    fc_definitions = fc.split("open Matrix\n\n", 1)[1]
    fc_vocabulary = fc_definitions[:fc_definitions.rindex(
        "/--", 0, fc_definitions.index("@[category"))].strip()
    if vocabulary != fc_vocabulary:
        raise SystemExit("FC vocabulary differs from the proved model")
    proof = (LEAN / "QubitAdditivity/FCPresentation.lean").read_text()
    for name in ("strong_additivity", "power_additivity"):
        signatures = []
        for text in (fc, proof):
            found = re.search(r"^theorem " + name + r"\b(.*?):=", text, re.M | re.S)
            if not found:
                raise SystemExit(f"Missing public statement: {name}")
            signatures.append(" ".join(found.group(1).split()))
        if signatures[0] != signatures[1]:
            raise SystemExit(f"FC statement differs from the proved theorem: {name}")
    for project in ("lean", "lean4web"):
        if (ROOT / project / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
            raise SystemExit(f"Unexpected toolchain: {project}")
    manifest = json.loads((ROOT / "lean4web/lake-manifest.json").read_text())
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    if mathlib["rev"] != "d13f23b723b8a846827a245b89c10fc7d3f11612":
        raise SystemExit("Unexpected Lean4Web Mathlib revision")
    generated = ROOT / "lean4web/QubitStrongAdditivityLean4Web.lean"
    code = code_mask(generated.read_text())
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
        raise SystemExit("Hole, additional axiom or native_decide in the single-file proof")
    imports = re.findall(r"^import (\S+)\s*$", code, re.M)
    generated_manifest = json.loads((ROOT / "lean4web/sources.json").read_text())
    if imports != generated_manifest["output_imports"] or any(
            not module.startswith(("Mathlib.", "Aesop.", "Lean.", "Batteries."))
            for module in imports):
        raise SystemExit(f"Unexpected single-file imports: {imports}")
    for path in (ROOT / "lean4web/lake-manifest.json", LEAN / "lake-manifest.json"):
        lock = json.loads(path.read_text())
        if any(package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"])
               for package in lock["packages"]):
            raise SystemExit(f"Unpinned or local dependency in {path}")
    print("Publication checks passed: FC vocabulary/signatures, Comparator axioms, pinned dependencies and hole-free single-file proof")


if __name__ == "__main__":
    main()
