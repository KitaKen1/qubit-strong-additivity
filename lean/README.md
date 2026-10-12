# Modular Lean proof

Entry point: [`QubitAdditivity.lean`](QubitAdditivity.lean).
Final original theorem: [`GeneralResult.lean`](QubitAdditivity/GeneralResult.lean).
Public Kraus-family statements: [`FCPresentation.lean`](QubitAdditivity/FCPresentation.lean).

```sh
lake exe cache get
python3 scripts/verify.py
lake env lean --run scripts/Replay.lean
```

The target in `Target.lean` is fixed by `verification/target-lock.json`.
The solution supplies both `GeneralQubitStrongAdditivity` and
`GeneralQubitUpperBound` without additional hypotheses.

`Audit.lean` prints transitive axiom dependencies and checks the exact original
and Kraus-family target types. The standard-three axiom whitelist is enforced
by `scripts/verify.py`. `scripts/CompareStatement.lean` compares the separately
compiled Mathlib-only challenge and solution, including all the definitions
their types use. The challenge in `ComparatorChallenges/` is generated from the
Formal Conjectures draft, and `FCAudit.lean` prints the axioms of the Comparator
targets. Comparator instructions are in [`../comparator/`](../comparator/README.md).

The source package includes every reference needed by `check_blueprint.py`; it
does not rely on the author's original workspace. Its graph is a checked
mathematical dependency ledger, rather than an extracted Lean import graph.

Use the committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`
without running `lake update`. Mathlib caches accelerate external dependencies.
The project and vendored Physlib/OpenAI modules still build from their sources.
See the [root README](../README.md) for scope, public statements and status.

