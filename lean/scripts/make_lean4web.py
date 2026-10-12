#!/usr/bin/env python3
"""Generate a Mathlib-only, single-file edition of the complete proof.

The source graph is visited in dependency order. Each original file is put in a
section to preserve its local instances, options, variables and open namespaces.
Module-system headers are removed; private identifiers are made file-specific.
The Commutes tactic rules use the already-initialized builtin Aesop rule set.
All mathematical definitions and theorem statements are retained.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
OUTPUT = ROOT / "lean4web/QubitStrongAdditivityLean4Web.lean"
MANIFEST = ROOT / "lean4web/sources.json"


def code_mask(text):
    """Blank nested comments and strings, preserving offsets and newlines."""
    result = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text[i:i + 2] == "/-":
                depth += 1
                result[i:i + 2] = "  "
                i += 2
            elif text[i:i + 2] == "-/":
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif text[i:i + 2] == "/-":
            depth = 1
            result[i:i + 2] = "  "
            i += 2
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            result[i] = " "
            i += 1
        else:
            i += 1
    return "".join(result)


def source_path(module):
    relative = Path(*module.split(".")).with_suffix(".lean")
    for directory in (LEAN, LEAN / "vendor/physlib", LEAN / "vendor/openai"):
        candidate = directory / relative
        if candidate.is_file():
            return candidate
    return None


def adapt_proof(module, body):
    """Adapt a few proof tactics to the combined import environment, keeping types."""
    adjustments = []

    def replace_once(old, new, description):
        nonlocal body
        if body.count(old) != 1:
            raise ValueError(f"Expected one packaging adjustment in {module}: {description}")
        body = body.replace(old, new)
        adjustments.append(description)

    if module == "QuantumInfo.ForMathlib.HayataGroup.TraceInequality.HilbertSchmidtOperatorSpace":
        replace_once("    simp [toHSCoordsLinearEquiv, matrixToCoords, matrixToFun, f]\n    rfl",
                     "    simp [toHSCoordsLinearEquiv, matrixToCoords, matrixToFun, f]\n    all_goals rfl",
                     "Guard a final reflexivity step when broader simp rules already close the coordinate goal.")
        replace_once("    simp [inner_smul_left, map_smul]",
                     "    simp [inner_smul_left, map_smul, mul_comm]",
                     "Make commutativity of the complex scalar inner-product factor explicit.")
    elif module == "QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace":
        replace_once("    simp_all only [sub_eq_add_neg, mul_neg, add_apply, rightMulHS_apply, neg_apply]\n    exact h1",
                     "    simp_all only [sub_eq_add_neg, mul_neg, add_apply, rightMulHS_apply, neg_apply]\n    all_goals exact h1",
                     "Guard a final equality step when simp_all already uses the local equality.")
    elif module == "QuantumInfo.ForMathlib.HermitianMat.Rpow":
        pattern = (r"(private lemma trace_conj_rpow_eq_sum_singularValuesSorted\b.*?:= by)\n"
                   r".*?(?=\nprivate lemma lieb_thirring_le_one_posDef)")
        proof = '''
  let M : Matrix d d ℂ := (A ^ (1 / 2 : ℝ)).mat * B.mat
  let H : HermitianMat d ℂ :=
    ⟨M.conjTranspose * M.conjTranspose.conjTranspose,
      Matrix.isHermitian_mul_conjTranspose_self M.conjTranspose⟩
  have hH : H = A.conj B.mat := by
    ext1
    change M.conjTranspose * M.conjTranspose.conjTranspose = (A.conj B.mat).mat
    rw [Matrix.conjTranspose_conjTranspose]
    exact conjTranspose_half_mul_eq_conj (A := A) (B := B) hA
  calc
    ((A.conj B.mat) ^ α).trace = (H ^ α).trace :=
      congrArg (fun X : HermitianMat d ℂ => (X ^ α).trace) hH.symm
    _ = ∑ i, (H.H.eigenvalues i) ^ α := trace_rpow_eq_sum H α
    _ = ∑ i : Fin (Fintype.card d), singularValuesSorted M i ^ (2 * α) := by
      rw [← sum_singularValues_rpow_eq_sum_sorted M (2 * α)]
      refine Finset.sum_congr rfl fun i _ => ?_
      let e : ℝ := (Matrix.isHermitian_mul_conjTranspose_self M.conjTranspose).eigenvalues i
      change e ^ α = (Real.sqrt e) ^ (2 * α)
      have he : 0 ≤ e := Matrix.eigenvalues_self_mul_conjTranspose_nonneg M.conjTranspose i
      calc
        e ^ α = ((Real.sqrt e) ^ (2 : ℕ)) ^ α :=
          congrArg (fun x : ℝ => x ^ α) (Real.sq_sqrt he).symm
        _ = ((Real.sqrt e) ^ (2 : ℝ)) ^ α :=
          congrArg (fun x : ℝ => x ^ α) (Real.rpow_natCast (Real.sqrt e) 2).symm
        _ = (Real.sqrt e) ^ (2 * α) :=
          (Real.rpow_mul (Real.sqrt_nonneg e) (2 : ℝ) α).symm
'''
        body, count = re.subn(pattern, lambda match: match.group(1) + "\n" + proof, body, flags=re.S)
        if count != 1:
            raise ValueError("Expected the singular-value trace-power helper in Rpow")
        adjustments.append("Align the Gram matrix and Hermitian witness with singularValues, then use explicit square-root-square and real-power identities instead of expanding dependent spectral witnesses with simp.")
    elif module == "QuantumInfo.Channels.Unbundled":
        pattern = r"(theorem conj_isCompletelyPositive\b.*?:= by)\n.*?(?=\n/-- `MatrixMap.submatrix`)"
        body, count = re.subn(pattern, r"\1\n  classical\n  exact congruence_CP M\n", body, flags=re.S)
        if count != 1:
            raise ValueError("Expected the duplicate congruence CP proof in Unbundled")
        adjustments.append("Reuse the preceding congruence_CP theorem for its duplicate conj_isCompletelyPositive statement, with classical decidable equality.")
    return body, adjustments


def generate():
    sources, external, seen, active = [], set(), set(), set()

    def visit(module):
        if module in active:
            raise ValueError(f"Import cycle at {module}")
        if module in seen:
            return
        path = source_path(module)
        if path is None:
            if not module.startswith(("Mathlib", "Lean", "Batteries", "Aesop")):
                raise ValueError(f"Missing source for {module}")
            external.add(module)
            return
        active.add(module)
        original = path.read_text()
        masked = code_mask(original)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", masked):
            raise ValueError(f"Proof hole or additional axiom in {path}")
        for dependencies in re.findall(
                r"^(?:(?:public|private) )?import (.+)$", masked, re.M):
            for dependency in dependencies.split():
                visit(dependency)
        active.remove(module)
        seen.add(module)

        body_lines = []
        for line, code in zip(original.splitlines(), masked.splitlines()):
            if re.match(r"^(?:(?:public|private) )?import\b|^module\s*$|"
                        r"^@\[expose\] public section\s*$", code):
                continue
            body_lines.append(line)
        body = "\n".join(body_lines).strip()
        # Unlimited budgets can turn an unsuccessful speculative simplifier match
        # into a very long search when every Mathlib import is present at once.
        body = re.sub(r"^([ \t]*set_option maxHeartbeats )0\b",
                      r"\g<1>2000000", body, flags=re.M)
        body, proof_adjustments = adapt_proof(module, body)
        # Custom rule-set extensions normally initialize when their module is imported.
        # A single file instead adds the Commutes rules to the initialized builtin set.
        body = re.sub(r"^declare_aesop_rule_sets \[Commutes\] \(default := false\)\s*$",
                      "-- Commutes rules are packaged in Aesop's initialized builtin set.",
                      body, flags=re.M)
        body = body.replace("rule_sets := [Commutes]", "rule_sets := [builtin]")
        body = body.replace("[ $(Lean.mkIdent `Commutes):ident, -default]", "[-default]")
        body = body.replace("[$(Lean.mkIdent `Commutes):ident, -default]", "[-default]")
        private_names = re.findall(
            r"\bprivate\s+(?:noncomputable\s+)?(?:def|lemma|theorem|abbrev|instance)\s+(\S+)",
            code_mask(body))
        private_renames = {}
        for name in private_names:
            new = name + "_lean4web_" + str(len(sources))
            private_renames[name] = new
            aliases = {name}
            if name.startswith("_root_."):
                aliases.add(name[len("_root_."):])
            elif "." in name:
                # References in an opened namespace can omit the namespace prefix.
                aliases.add(name.rsplit(".", 1)[-1])
            for alias in sorted(aliases, key=len, reverse=True):
                replacement = alias + "_lean4web_" + str(len(sources))
                body = re.sub(r"(?<![\w'])" + re.escape(alias) + r"(?![\w'])",
                              replacement, body)

        scopes = []
        for line in code_mask(body).splitlines():
            start = re.match(r"^\s*(?:noncomputable )?(section|namespace)\b\s*(.*)$", line)
            if start:
                scopes.append(start.group(2).strip())
            elif re.match(r"^\s*end(?:\s+\S+)?\s*$", line):
                if not scopes:
                    raise ValueError(f"Unmatched end in {path}: {line}")
                scopes.pop()
        closing = "\n".join("end" + (" " + name if name else "")
                            for name in reversed(scopes))
        relative = path.relative_to(LEAN).as_posix()
        content = (f"-- BEGIN SOURCE: {relative}\n"
                   "section\n" + body + "\n" + closing + "\nend\n"
                   f"-- END SOURCE: {relative}\n")
        sources.append({"module": module, "path": relative,
                        "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
                        "private_renames": private_renames,
                        "proof_adjustments": proof_adjustments, "content": content})

    visit("QubitAdditivity")
    output_imports = sorted(external - {"Mathlib"})
    header = "\n".join("import " + module for module in output_imports) + '''

/-!
# Strong Holevo additivity for qubit channels: complete single-file proof

Generated by lean/scripts/make_lean4web.py. All project and Physlib sources
needed by the proof are included below; only Mathlib and its dependencies are
imported. The pinned environment is recorded in lean4web/lean-toolchain and
lean4web/lake-manifest.json. No compatibility with a different Mathlib version
is implied. See lean4web/README.md for the hosted Lean4Web status.

Original copyright and author notices are preserved in each source block.
Changes for this edition: import/module headers removed, file scopes restored,
private identifiers given source-specific suffixes, and Commutes tactic rules
merged into the initialized builtin Aesop rule set. The umbrella Mathlib import
is replaced by the explicit Mathlib imports already used by the proof. Matrix
multiplication is preferred for ambiguous default-instance inference, and the
elaborator transparency setting accommodates Matrix/CStarMatrix aliases. Apache-2.0.
Limited proof-tactic adjustments for the combined imports are listed per source
in sources.json; all definitions and theorem statements are retained.
-/

-- Keep speculative simplifier/unifier searches bounded in the combined environment.
-- Individual source blocks retain finite budgets; unlimited ones are capped.
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
-- Prefer Matrix multiplication when implicit dimensions leave an alias ambiguous.
attribute [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

'''
    audit = '''
#print axioms QubitAdditivity.GeneralResult.generalQubitStrongAdditivity
#print axioms QubitAdditivity.GeneralResult.generalQubitUpperBound
#print axioms QubitHolevo.strong_additivity
#print axioms QubitHolevo.power_additivity

example : QubitAdditivity.GeneralQubitStrongAdditivity :=
  QubitAdditivity.GeneralResult.generalQubitStrongAdditivity
example : QubitAdditivity.GeneralQubitUpperBound :=
  QubitAdditivity.GeneralResult.generalQubitUpperBound
'''
    content = header + "\n".join(source["content"] for source in sources) + audit
    manifest = {"root_module": "QubitAdditivity", "module_count": len(sources),
                "line_count": len(content.splitlines()),
                "external_imports_encountered": sorted(external),
                "output_imports": output_imports,
                "tactic_packaging": "Commutes rules are added to the initialized builtin Aesop set; commutes disables default rules without redundantly activating builtin. Definitional-equality transparency is relaxed and Matrix multiplication's default-instance priority is raised to handle Matrix/CStarMatrix aliases when all imports are present. Recursion depth is bounded at 2048. The default heartbeat budget is 2000000 and source budgets of 0 (unlimited) are capped at 2000000 to prevent excessively long speculative searches; original finite budgets are retained. Qualified, root-qualified and short private-helper references are renamed consistently. No mathematical definitions, statements or axioms are added by these adjustments.",
                "output": OUTPUT.relative_to(ROOT).as_posix(),
                "output_sha256": hashlib.sha256(content.encode()).hexdigest(),
                "sources": [{k: v for k, v in source.items() if k != "content"}
                            for source in sources]}
    return content, json.dumps(manifest, ensure_ascii=False, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check the committed output")
    args = parser.parse_args()
    content, manifest = generate()
    if args.check:
        if OUTPUT.read_text() != content or MANIFEST.read_text() != manifest:
            raise SystemExit("Lean4Web output is stale; run lean/scripts/make_lean4web.py")
        print("Lean4Web source and provenance match the project")
    else:
        OUTPUT.write_text(content)
        MANIFEST.write_text(manifest)
        print(f"Generated {OUTPUT.name}: {len(content.splitlines())} lines")


if __name__ == "__main__":
    main()
