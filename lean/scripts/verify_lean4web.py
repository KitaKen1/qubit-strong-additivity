#!/usr/bin/env python3
"""Compile the complete Mathlib-only single-file proof and enforce its final axioms."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean4web"
FILE = PROJECT / "QubitStrongAdditivityLean4Web.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = {
    "QubitAdditivity.GeneralResult.generalQubitStrongAdditivity",
    "QubitAdditivity.GeneralResult.generalQubitUpperBound",
    "QubitHolevo.strong_additivity",
    "QubitHolevo.power_additivity",
}


def check_log(log):
    entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    audit = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in entries}
    if set(audit) != THEOREMS:
        raise ValueError("Missing or unexpected final single-file axiom reports")
    for name, axioms in audit.items():
        if set(axioms) - ALLOWED:
            raise ValueError(f"Unexpected axioms for {name}: {axioms}")
    if re.search(r"\berror:", log):
        raise ValueError("Lean errors in the single-file build log")
    return audit


def main():
    subprocess.run([sys.executable, str(ROOT / "lean/scripts/make_lean4web.py"), "--check"], check=True)
    command = ["lake", "env", "lean", FILE.name]
    started = datetime.now(timezone.utc).isoformat()
    input_hash = hashlib.sha256(FILE.read_bytes()).hexdigest()
    with (PROJECT / "build.log").open("w") as log_file:
        process = subprocess.run(command, cwd=PROJECT, text=True, stdout=log_file,
                                 stderr=subprocess.STDOUT)
    log = (PROJECT / "build.log").read_text()
    record = {"started_utc": started, "completed_utc": datetime.now(timezone.utc).isoformat(),
              "command": command, "exit_code": process.returncode,
              "lean_toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
              "source_sha256": input_hash,
              "scope": "Full source elaboration and kernel checking of the generated single file, using only the pinned Mathlib dependency environment; no compiled project or Physlib module imports. Hosted Lean4Web not tested."}
    if process.returncode == 0:
        try:
            if hashlib.sha256(FILE.read_bytes()).hexdigest() != input_hash:
                raise ValueError("Source changed during compilation; rerun the check")
            record["axiom_audit"] = check_log(log)
            record["status"] = "passed"
        except ValueError as error:
            record["status"] = "failed"
            record["error"] = str(error)
    else:
        record["status"] = "failed"
    (PROJECT / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    if process.returncode:
        print(log)
        raise SystemExit(process.returncode)
    if record["status"] != "passed":
        raise SystemExit(record["error"])
    print("Complete single-file proof passed with only the standard three axioms")


if __name__ == "__main__":
    main()
