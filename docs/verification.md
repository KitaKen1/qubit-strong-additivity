# Verification scope

Each check has a separate result. A successful local build does not imply that
an external service or a separate kernel has run.

| Check | Evidence / command | Scope |
|---|---|---|
| Modular proof and axiom audit | `lean/verification/result.json`, `python3 lean/scripts/verify.py` | Lean build, original target examples, all listed transitive axiom closures |
| Compiled statement comparison | `lean/verification/statement.log` | Types and recursively dependent definitions in two compiled environments |
| Vendor/source guards | `lean/VENDOR.json`, `lean/verification/source-sha256.json` | Exact vendor hashes, extracted proof bodies and frozen target |
| Local dependency checkouts | `lean/verification/environment.json` | All nine cached dependency revisions match the lockfile; tracked sources are clean |
| Mathematical dependency ledger | `scripts/check_blueprint.py` | Acyclic ledger, real source files, audited theorem witnesses |
| Fresh Lean environment | `lake env lean --run scripts/Replay.lean`; the `replay` job of the Comparator workflow runs `leanchecker --fresh` | Same Lean kernel, all imported and defined constants. No local record is kept; the hosted run is the record |
| Single-file edition | `lean4web/verification.json` | Complete generated file with no project imports, pinned Mathlib |
| Copy without Comparator files | `leanWithoutComparator/sources.json`, `python3 lean/scripts/make_lean_without_comparator.py --check` | Every copied file has the bytes of its `lean/` original; the copy's own build and axiom audit are in `leanWithoutComparator/verification.json` |
| Comparator inputs | `python3 comparator/check-inputs.py`, `comparator/pins.json` | Targets, challenge generated from the FC draft, proof files identical to `leanWithoutComparator/`, toolchain, Mathlib and tool revisions |
| Local Comparator precheck | `python3 comparator/local-precheck.py --receipt-dir DIR` | Declaration equality of challenge and solution with the pinned Comparator's rules, and the solution's axioms; no sandbox, not a Comparator run |
| Lean Comparator | `.github/workflows/comparator.yml`, `comparator/run-check.sh` | Pinned Comparator in a sandbox on a fresh GitHub runner: both targets, permitted axioms, kernel acceptance; then `leanchecker --fresh`. Passed on public `main` on 12 October 2026 (UTC), run 38265719873; records in `ComparatorLog20261012/38265719873-attempt1/` |
| GitHub Actions | `.github/workflows/` | Manual workflows; success requires a hosted run |
| Hosted Lean4Web | `lean4web/hosted-status.json` | Manual browser runs on the public server; the current file was processed to the end on 2026-10-12 (UTC), which is an observation and not a reproducible check |
| Formal Conjectures submission | `FClikelean/README.md` | Draft; compile and lint inside the destination checkout before submitting |

The package's local audit may reuse the pinned Mathlib dependency cache and
existing modular build products. These are recorded honestly in the result
scope. Source changes cause Lake to rebuild the affected modules. A checkout
with no project build products exercises a fresh project/vendor source build;
the committed CI performs that build and downloads the pinned Mathlib cache.

`propext`, `Classical.choice` and `Quot.sound` are the only permitted axioms for
the proved theorems. The challenge and FC draft have intentional proof holes;
they are excluded from the proof-source scan and never imported by the solution.

The earlier working project completed a
[separate-directory source build](historical-verification/original-clean-build.json)
and [fresh Lean kernel replay](historical-verification/original-kernel-replay.json)
for the original theorem. Its [replay log](historical-verification/original-kernel-replay.log)
reports 443,753 declarations. Those records predate the new public Kraus
presentation and publication packaging; they are not current-package or hosted
CI results. Current package results are generated in this directory.

The publication edition narrows the Mathlib imports of the model and challenge.
Their definitions and theorem signatures remain identical. The single-file
generator records additional file-scope, private-name, Aesop and elaborator
adjustments in `lean4web/sources.json`; its full compile is a separate check.

