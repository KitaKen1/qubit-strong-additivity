#!/usr/bin/env python3
"""Write leanWithoutComparator/: the proof project of lean/ without its Comparator parts.

Proof modules, vendored sources, the axiom audit, the toolchain and the dependency lockfile
are copied byte for byte. The one derived file is lakefile.toml: lean/lakefile.toml with the
ComparatorChallenges library removed. sources.json lists every file with its SHA-256 and names
what was left out. With --check nothing is written; the directory must equal this output.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
CLEAN = ROOT / "leanWithoutComparator"
COPIED = [".gitignore", "LICENSE", "VENDOR.json", "lean-toolchain", "lake-manifest.json",
          "QubitAdditivity.lean", "Audit.lean", "QubitAdditivity", "vendor"]
OMITTED = {
    "ComparatorChallenges": "Comparator challenge with intentional `sorry` proofs, and its configuration",
    "FCAudit.lean": "axiom report for the Comparator targets",
    "scripts": "verification and publication scripts, including the local statement comparison",
    "verification": "verification records of lean/",
    "blueprint": "dependency ledger, rewritten by lean/scripts/verify.py",
    "README.md": "replaced by the README.md of this directory",
}
COMPARATOR_LIBRARY = b'[[lean_lib]]\nname = "ComparatorChallenges"\nglobs = ["ComparatorChallenges.+"]\n\n'
OWN = {"README.md", "sources.json", "verification.json"}
CACHES = {".lake", "__pycache__", ".DS_Store"}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def files_below(directory):
    """Relative POSIX paths of the files under `directory`, without entering build caches."""
    found = []
    for current, directories, names in os.walk(directory):
        directories[:] = [name for name in directories if name not in CACHES]
        found += [(Path(current) / name).relative_to(directory).as_posix()
                  for name in names if name not in CACHES]
    return sorted(found)


def expected():
    """Every generated file of leanWithoutComparator/, as {relative path: bytes}."""
    unclassified = sorted(entry.name for entry in LEAN.iterdir()
                          if entry.name not in {*COPIED, *OMITTED, *CACHES, "lakefile.toml"})
    if unclassified:
        raise SystemExit(f"Decide whether to copy or omit these entries of lean/: {unclassified}")
    copies = {}
    for entry in COPIED:
        source = LEAN / entry
        for path in ([f"{entry}/{name}" for name in files_below(source)] if source.is_dir() else [entry]):
            copies[path] = (LEAN / path).read_bytes()
    for path, data in copies.items():
        if path.endswith(".lean") and re.search(rb"^(?:public )?import ComparatorChallenges\b", data, re.M):
            raise SystemExit(f"{path} imports the Comparator challenge")
    lakefile = (LEAN / "lakefile.toml").read_bytes()
    if lakefile.count(COMPARATOR_LIBRARY) != 1:
        raise SystemExit("lean/lakefile.toml does not declare the ComparatorChallenges library as expected")
    derived = lakefile.replace(COMPARATOR_LIBRARY, b"")
    if b"Comparator" in derived:
        raise SystemExit("The derived lakefile.toml still mentions Comparator")
    manifest = {
        "description": "leanWithoutComparator/ is lean/ without its Comparator parts. Each file under "
                       "identical_to_source has the bytes of the file at the same path in lean/.",
        "generated_by": "lean/scripts/make_lean_without_comparator.py",
        "source_directory": "lean",
        "identical_to_source": {path: sha256(data) for path, data in sorted(copies.items())},
        "derived": {"lakefile.toml": {
            "sha256": sha256(derived),
            "source_sha256": sha256(lakefile),
            "change": "the ComparatorChallenges library declaration is removed; nothing else differs"}},
        "omitted_from_source": OMITTED,
        "own_files": sorted(OWN),
    }
    return {**copies, "lakefile.toml": derived,
            "sources.json": (json.dumps(manifest, indent=2) + "\n").encode()}


def differences(require_current_record=True):
    """The expected files, and how the directory on disk departs from them."""
    wanted = expected()
    present = set(files_below(CLEAN)) if CLEAN.is_dir() else set()
    problems = [f"missing: {path}" for path in sorted({*wanted, "README.md"} - present)]
    problems += [f"not produced from lean/: {path}" for path in sorted(present - set(wanted) - OWN)]
    problems += [f"differs from lean/: {path}" for path in sorted(set(wanted) & present)
                 if (CLEAN / path).read_bytes() != wanted[path]]
    record = CLEAN / "verification.json"
    if require_current_record and record.is_file() and (
            json.loads(record.read_text()).get("sources_sha256") != sha256(wanted["sources.json"])):
        problems.append("verification.json records another file set; "
                        "rerun lean/scripts/verify_lean_without_comparator.py")
    return wanted, problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="write nothing; fail if the directory differs from this script's output")
    args = parser.parse_args()
    if args.check:
        wanted, problems = differences()
        if problems:
            raise SystemExit("leanWithoutComparator differs from lean/:\n  " + "\n  ".join(problems))
        print(f"leanWithoutComparator matches lean/: {len(wanted) - 2} identical files, "
              "lakefile.toml without the ComparatorChallenges library")
        return
    wanted = expected()
    for path in files_below(CLEAN) if CLEAN.is_dir() else []:
        if path not in wanted and path not in OWN:
            (CLEAN / path).unlink()
    for path, data in wanted.items():
        target = CLEAN / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.is_file() or target.read_bytes() != data:
            target.write_bytes(data)
    print(f"Wrote leanWithoutComparator: {len(wanted) - 2} files copied from lean/, "
          "lakefile.toml and sources.json generated")
    for problem in differences()[1]:
        print(f"Still to do: {problem}")


if __name__ == "__main__":
    main()
