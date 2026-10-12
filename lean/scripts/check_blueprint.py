#!/usr/bin/env python3
"""Check the mathematical DAG and its witnesses against the Lean axiom audit.

The mathematical dependency edges are authored, not extracted Lean imports.
Checking a witness does not close any open mathematical node.
"""
from pathlib import Path
import json
import re
import unicodedata

ROOT = Path(__file__).resolve().parents[1]


def resolve(source):
    """Locate a ledger source below ROOT.

    macOS stores kana with voicing marks decomposed, while Git records them composed, so a
    checkout on another system can spell the same path differently. Both forms are tried.
    """
    for form in (None, "NFC", "NFD"):
        candidate = ROOT / (source if form is None else unicodedata.normalize(form, source))
        if candidate.is_file():
            return candidate
    return None


def check_blueprint(audited_names):
    manifest = ROOT / "blueprint/dependencies.json"
    data = json.loads(manifest.read_text())
    nodes = data["nodes"]
    ids = [n["id"] for n in nodes]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate Blueprint node")
    by_id = {n["id"]: n for n in nodes}
    audited = set(audited_names)
    seen, active, ordered, witnesses = set(), set(), [], set()

    def visit(key):
        if key in active:
            raise ValueError(f"Blueprint cycle at {key}")
        if key in seen:
            return
        if key not in by_id:
            raise ValueError(f"Missing Blueprint dependency: {key}")
        active.add(key)
        node = by_id[key]
        for dep in node["needs"]:
            visit(dep)
        active.remove(key)
        seen.add(key)
        ordered.append(key)
        if node["source"] and resolve(node["source"]) is None:
            raise ValueError(f"Missing Blueprint source: {key}")
        if node["status"].startswith("lean_verified"):
            refs = node.get("lean_declarations", [])
            if not refs:
                raise ValueError(f"No audited Lean witness: {key}")
            code = resolve(node["source"]).read_text()
            for name in refs:
                if name not in audited:
                    raise ValueError(f"Unaudited Lean witness: {name}")
                leaf = name.rsplit(".", 1)[-1]
                if not re.search(r"\b(?:theorem|lemma)\s+" + re.escape(leaf) + r"\b", code):
                    raise ValueError(f"Lean witness not declared in source: {name}")
                witnesses.add(name)
        elif node.get("lean_declarations"):
            raise ValueError(f"Open node incorrectly carries completed witnesses: {key}")

    for key in ids:
        visit(key)
    main = by_id["main"]
    if main["status"] not in {"open", "lean_verified"}:
        raise ValueError("Unexpected main theorem status")
    if main["status"] == "lean_verified":
        required = {"QubitAdditivity.GeneralResult.generalQubitStrongAdditivity",
                    "QubitAdditivity.GeneralResult.generalQubitUpperBound"}
        if not required <= set(main["lean_declarations"]):
            raise ValueError("The main node must witness both frozen target propositions")
    return {"nodes": len(nodes), "audited_lean_witnesses": len(witnesses),
            "acyclic": True, "topological_order": ordered,
            "scope": data["scope"]}


if __name__ == "__main__":
    record = json.loads((ROOT / "verification/result.json").read_text())
    print(json.dumps(check_blueprint(record["axiom_audit"]), indent=2, ensure_ascii=False))
