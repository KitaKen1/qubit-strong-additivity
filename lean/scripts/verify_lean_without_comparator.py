#!/usr/bin/env python3
"""Check leanWithoutComparator/ against lean/, build it and audit the axioms it reports."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import re
import subprocess
from make_lean_without_comparator import CLEAN, differences, files_below, sha256

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def audit(log, audit_source):
    """Axioms used across all reports of Audit.lean; raises ValueError on anything unexpected."""
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    entries += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    if sorted(name for name, _ in entries) != sorted(re.findall(r"^#print axioms (\S+)", audit_source, re.M)):
        raise ValueError("Missing or unexpected axiom reports")
    if re.search(r"\berror:", log):
        raise ValueError("Lean errors in the axiom audit")
    used = set()
    for name, text in entries:
        axioms = {axiom.strip() for axiom in text.split(",") if axiom.strip()}
        if axioms - ALLOWED:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED)}")
        used |= axioms
    return len(entries), sorted(used)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path,
                        help="build a byte-identical copy in this directory instead of in place, "
                             "for example outside a synchronized folder; its .lake is kept")
    args = parser.parse_args()
    wanted, problems = differences(require_current_record=False)
    if problems:
        raise SystemExit("leanWithoutComparator differs from lean/:\n  " + "\n  ".join(problems))
    project = args.build_dir.resolve() if args.build_dir else CLEAN
    if args.build_dir:
        for path, data in wanted.items():
            (project / path).parent.mkdir(parents=True, exist_ok=True)
            (project / path).write_bytes(data)
        stray = sorted(set(files_below(project)) - set(wanted))
        if stray:
            raise SystemExit(f"Unexpected files in the build directory: {stray}")
    record = {"started_utc": datetime.now(timezone.utc).isoformat(),
              "sources_sha256": sha256(wanted["sources.json"]),
              "identical_files": len(wanted) - 2,
              "lean_toolchain": wanted["lean-toolchain"].decode().strip(),
              "built_in_place": not args.build_dir,
              "project_build_products_present_before": (project / ".lake/build").exists(),
              "steps": [],
              "scope": "Lake build of this file set and the transitive axioms reported by its Audit.lean; "
                       "Mathlib comes from the pinned dependency cache. Statement comparison, kernel "
                       "replay and Comparator belong to lean/ and are not repeated here."}
    try:
        output = ""
        for name, command in [("build", ["lake", "build"]), ("axioms", ["lake", "env", "lean", "Audit.lean"])]:
            step = subprocess.run(command, cwd=project, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT)
            output = step.stdout
            print(output, end="", flush=True)
            record["steps"].append({"step": name, "command": command, "exit_code": step.returncode})
            if step.returncode:
                raise ValueError(f"{name} failed with exit code {step.returncode}")
        record["axiom_reports"], record["axioms_used"] = audit(output, wanted["Audit.lean"].decode())
        if differences(require_current_record=False)[1] or any(
                (project / path).read_bytes() != data for path, data in wanted.items()):
            raise ValueError("Files changed during the build; rerun the check")
        record["status"] = "passed"
    except ValueError as error:
        record["status"] = "failed"
        record["error"] = str(error)
    record["completed_utc"] = datetime.now(timezone.utc).isoformat()
    (CLEAN / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    if record["status"] != "passed":
        raise SystemExit(record["error"])
    print(f"leanWithoutComparator built; {record['axiom_reports']} axiom reports use only {record['axioms_used']}")


if __name__ == "__main__":
    main()
