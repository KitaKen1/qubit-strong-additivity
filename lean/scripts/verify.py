#!/usr/bin/env python3
"""Build the project and reject nonstandard transitive axioms in the audited results."""
from pathlib import Path
import json
import re
import subprocess
import sys
import hashlib
from datetime import datetime, timezone
from check_blueprint import check_blueprint
from make_lean4web import code_mask

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "verification"
LOG.mkdir(exist_ok=True)
allowed = {"propext", "Classical.choice", "Quot.sound"}
results = []
vendors = json.loads((ROOT / "VENDOR.json").read_text())
target_lock = json.loads((LOG / "target-lock.json").read_text())
target_source = ROOT / target_lock["target_file"]
if hashlib.sha256(target_source.read_bytes()).hexdigest() != target_lock["sha256"]:
    raise SystemExit("The frozen original target changed")
provenance = json.loads((LOG / "matrix-calculus-provenance.json").read_text())
original = (ROOT / provenance["original_file"]).read_text()
adapted = (ROOT / provenance["adapted_file"]).read_text()
original_body = original.split(provenance["start_marker"], 1)[1].split(
    provenance["end_marker"], 1)[0]
adapted_body = adapted.split(provenance["start_marker"], 1)[1].split(
    provenance["adapted_end_marker"], 1)[0]
if original_body != adapted_body or hashlib.sha256(original_body.encode()).hexdigest() != provenance["proof_body_sha256"]:
    raise SystemExit("Adapted OpenAI calculus proof bodies differ from the original")
for extraction in provenance.get("additional_extracts", []):
    extracted_original = (ROOT / extraction["original_file"]).read_text().split(
        extraction["start_marker"], 1)[1].split(extraction["end_marker"], 1)[0]
    extracted_adapted = (ROOT / extraction["adapted_file"]).read_text().split(
        extraction["start_marker"], 1)[1].split(extraction["adapted_end_marker"], 1)[0]
    if (extracted_original != extracted_adapted or
            hashlib.sha256(extracted_original.encode()).hexdigest() != extraction["proof_body_sha256"]):
        raise SystemExit("Additional OpenAI calculus proof bodies differ from the original")
entropy_provenance = json.loads((LOG / "entropy-scaling-provenance.json").read_text())
entropy_original = (ROOT / entropy_provenance["original_file"]).read_text().split(
    entropy_provenance["start_marker"], 1)[1].split(entropy_provenance["end_marker"], 1)[0]
entropy_adapted = (ROOT / entropy_provenance["adapted_file"]).read_text().split(
    entropy_provenance["start_marker"], 1)[1].split(entropy_provenance["adapted_end_marker"], 1)[0]
if (entropy_original != entropy_adapted or
        hashlib.sha256(entropy_original.encode()).hexdigest() != entropy_provenance["proof_body_sha256"]):
    raise SystemExit("Adapted OpenAI entropy scaling proof body differs from the original")
for name, directory in [("physlib", "physlib"), ("openai_math", "openai")]:
    for module, expected in vendors[name]["sha256"].items():
        source = ROOT / "vendor" / directory / (module.replace(".", "/") + ".lean")
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Vendored source changed: {source}")
# The Mathlib-only statement must use one vocabulary: the definitions of the solution-side
# model and of the Comparator challenge are the same text, the challenge imports Mathlib
# alone, and each challenge theorem is stated exactly as the one that is proved.
comparator = json.loads((ROOT / "ComparatorChallenges/QubitHolevoAdditivity.json").read_text())
challenge = (ROOT / "ComparatorChallenges/QubitHolevoAdditivity.lean").read_text()
model = (ROOT / "QubitAdditivity/Presentation/Model.lean").read_text()
presentation = (ROOT / "QubitAdditivity/FCPresentation.lean").read_text()


def vocabulary(text):
    return text.split("namespace QubitHolevo\n", 1)[1].split("-- END MODEL", 1)[0]


def statement(text, leaf):
    found = re.search(r"^theorem " + re.escape(leaf) + r"\b(.*?):=", text, re.S | re.M)
    if not found:
        raise SystemExit(f"Statement not found: {leaf}")
    return " ".join(found.group(1).split())


# The challenge is generated from the Formal Conjectures draft and carries no markers.
if not challenge.split("namespace QubitHolevo\n", 1)[1].startswith(
        vocabulary(model).replace("-- BEGIN MODEL\n", "", 1)):
    raise SystemExit("The Comparator challenge and the model define different vocabularies")
model_imports = re.findall(r"^import (\S+)", model, re.M)
challenge_imports = re.findall(r"^import (\S+)", challenge, re.M)
if model_imports != challenge_imports or not model_imports or any(
        not module.startswith("Mathlib.") for module in model_imports):
    raise SystemExit("Both statement vocabularies must use the same explicit Mathlib imports")
if set(comparator["permitted_axioms"]) != allowed:
    raise SystemExit("Unexpected permitted axioms in the Comparator configuration")
if (comparator["challenge_module"] != "ComparatorChallenges.QubitHolevoAdditivity" or
        comparator["solution_module"] != "QubitAdditivity.FCPresentation" or
        comparator["definition_names"]):
    raise SystemExit("Unexpected Comparator configuration")
proved_statements = presentation.split("\nnamespace QubitHolevo\n", 1)[1]
for theorem in comparator["theorem_names"]:
    namespace, leaf = theorem.rsplit(".", 1)
    if namespace != "QubitHolevo" or statement(challenge, leaf) != statement(proved_statements, leaf):
        raise SystemExit(f"Challenge and proved statement differ: {theorem}")

for name, cmd in [("build", ["lake", "build"]),
                  ("challenge", ["lake", "build", "ComparatorChallenges"]),
                  ("axioms", ["lake", "env", "lean", "Audit.lean"]),
                  ("statement", ["lake", "env", "lean", "--run", "scripts/CompareStatement.lean",
                                 "ComparatorChallenges/QubitHolevoAdditivity.json"])]:
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    (LOG / f"{name}.log").write_text(p.stdout)
    print(p.stdout, end="", flush=True)
    results.append({"step": name, "command": cmd, "exit_code": p.returncode})
    if p.returncode:
        sys.exit(p.returncode)

audit = (LOG / "axioms.log").read_text()
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
entries += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", audit)]
expected_names = re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(), re.M)
if sorted(n for n, _ in entries) != sorted(expected_names):
    raise SystemExit("Missing or unexpected transitive axiom reports")
for theorem, text in entries:
    axioms = {v.strip() for v in text.split(",") if v.strip()}
    if axioms - allowed:
        raise SystemExit(f"Unexpected axioms for {theorem}: {sorted(axioms - allowed)}")

blueprint_check = check_blueprint(n for n, _ in entries)

target_proofs = ["QubitAdditivity.GeneralResult.generalQubitStrongAdditivity",
                 "QubitAdditivity.GeneralResult.generalQubitUpperBound"]
target_proved = all(n in dict(entries) for n in target_proofs)
kraus_proved = target_proved and all(n in dict(entries) for n in comparator["theorem_names"])
if target_proved and not kraus_proved:
    raise SystemExit("The Mathlib-only statements are missing from the axiom audit")
if target_proved:
    audit_source = (ROOT / "Audit.lean").read_text()
    for proposition, proof in zip(target_lock["declarations"], target_proofs):
        pattern = r"example\s*:\s*" + re.escape(proposition) + r"\s*:=\s*" + re.escape(proof)
        if not re.search(pattern, audit_source):
            raise SystemExit("Missing compiled example of the exact frozen target type")

# These user-authored modules must never contain holes or extra axioms.
for source in list((ROOT / "QubitAdditivity").rglob("*.lean")) + [ROOT / "QubitAdditivity.lean"]:
    code = code_mask(source.read_text())
    if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
        raise SystemExit(f"Proof hole or axiom in {source.name}")

record = {"verified_utc": datetime.now(timezone.utc).isoformat(),
          "steps": results, "axiom_audit": dict(entries),
          "target_status": ("proved; exact frozen GeneralQubitStrongAdditivity and "
                            "GeneralQubitUpperBound supplied with no additional premises; "
                            "general finite-partner strong Holevo additivity also proved; "
                            "the Mathlib-only Kraus statement and additivity over independent uses "
                            "are proved from it; hosted CI, the leanprover/comparator run and "
                            "publication remain" if target_proved else
                            "unproved; product lower bound and TC4Bound proved; strong Holevo "
                            "additivity proved for every complete normal-form qubit channel and "
                            "every finite partner; singular common branches and rotated normal-form "
                            "Gram data proved; general CPTP normal-form equality and completeness, output rotation "
                            "bridge, and the full general-qubit theorem remain open"),
          "target_lock_matched": True,
          "target_proof_declarations": target_proofs if target_proved else [],
          "exact_target_types_compiled": target_proved,
          "kraus_statement": {
              "proved": kraus_proved,
              "theorems": comparator["theorem_names"],
              "challenge_module": comparator["challenge_module"],
              "solution_module": comparator["solution_module"],
              "vocabulary_text_identical": True,
              "statement_comparison": "passed in scripts/CompareStatement.lean; this follows the "
                                      "checks of leanprover/comparator but is not that tool"},
          "openai_calculus_proof_bodies_matched": True,
          "openai_entropy_scaling_proof_body_matched": True,
          "blueprint_check": blueprint_check,
          "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}
blueprint_path = ROOT / "blueprint/dependencies.json"
blueprint = json.loads(blueprint_path.read_text())
blueprint["last_verified_utc"] = record["verified_utc"]
blueprint["audited_declarations"] = len(entries)
blueprint_path.write_text(json.dumps(blueprint, indent=2, ensure_ascii=False) + "\n")
(LOG / "result.json").write_text(json.dumps(record, indent=2) + "\n")
sources = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "QubitAdditivity.lean", "Audit.lean",
           "FCAudit.lean"]
sources += ["scripts/CompareStatement.lean", "scripts/Replay.lean",
            "ComparatorChallenges/QubitHolevoAdditivity.lean",
            "ComparatorChallenges/QubitHolevoAdditivity.json"]
sources += ["scripts/verify.py", "scripts/check_blueprint.py", "blueprint/dependencies.json",
            "scripts/make_lean4web.py", "scripts/check_publication.py",
            "scripts/verify_lean4web.py", "scripts/fill_links.py", "scripts/make_fc_statement.py",
            "verification/target-lock.json", "verification/matrix-calculus-provenance.json",
            "verification/entropy-scaling-provenance.json"]
sources += sorted(str(f.relative_to(ROOT)) for f in (ROOT / "QubitAdditivity").rglob("*.lean"))
hashes = {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in sources}
(LOG / "source-sha256.json").write_text(json.dumps(
    {"verified_utc": record["verified_utc"], "source_sha256": hashes}, indent=2, ensure_ascii=False) + "\n")
status = ("The exact frozen target propositions and the Mathlib-only Kraus statements are proved."
          if target_proved else "The full conjecture remains unproved.")
print(f"Verified build and {len(entries)} transitive axiom reports. {status}")
