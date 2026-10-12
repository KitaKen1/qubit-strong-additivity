# Complete single-file proof

[`QubitStrongAdditivityLean4Web.lean`](QubitStrongAdditivityLean4Web.lean) includes
the complete project proof and its required Physlib sources. It imports explicit
Mathlib modules and `Aesop.Frontend.Command`, a Mathlib dependency. No locally compiled
`QuantumInfo` or `QubitAdditivity` module is imported.

```sh
python3 ../lean/scripts/make_lean4web.py --check
lake exe cache get
python3 ../lean/scripts/verify_lean4web.py
```

The environment is pinned to Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Source ordering, hashes, private-name
renamings and the output hash are recorded in [`sources.json`](sources.json).
The generator isolates each original module's local options, instances,
variables and namespaces in a section. Definitions and theorem statements are
retained. Proof bodies use renamed private helpers, and a few proof tactics are
adapted to the wider import environment; each adjustment is listed per source
in the manifest. In particular,
custom Commutes rules are added to the already-initialized builtin Aesop set;
the commutes tactic still selects those rules and disables default rules. This
avoids a custom environment extension that would require importing a separate
file. The file collects the explicit Mathlib imports used by the proof.
The generated edition also renames private matrix eigenvalue helpers consistently,
relaxes Lean's definitional-equality transparency setting, and prefers Matrix
multiplication when default-instance inference leaves `Matrix`/`CStarMatrix`
aliases ambiguous. These are elaboration and tactic adjustments;
the kernel still checks the resulting proofs and final axiom dependencies.
The combined file bounds recursion depth at 2048 and uses a default budget
of 2,000,000 heartbeats. Unlimited source budgets are capped at 2,000,000;
original finite budgets remain in place. This avoids excessively long speculative
simplifier searches caused by an unnecessarily large global recursion bound.
The proof adjustments guard already-solved goals, make complex-scalar
commutativity explicit, align the Gram matrix's spectral witness with the
singular-value definition and apply scalar square-root/power identities, and
reuse an earlier theorem for a duplicate completely-positive
congruence statement. They introduce no new assumptions or proof holes.

The four final `#print axioms` commands must list only `propext`,
`Classical.choice` and `Quot.sound`. The two `example` declarations also check
that the original frozen propositions are supplied directly. The verification
script records the source hash, result and axiom reports in `verification.json`
and the compiler output in `build.log`. `lake build` is also available for a
normal library build.

<!-- BEGIN PUBLICATION LINKS -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fqubit-strong-additivity%2Fmain%2Flean4web%2FQubitStrongAdditivityLean4Web.lean) (Lean **v4.34**).
<!-- END PUBLICATION LINKS -->

For a hosted editor, open [Lean4Web](https://live.lean-lang.org/), select the
project **Stable Release (v4.34.0 with mathlib, cslib)** (`project=mathlib-stable`),
then load the complete file. That project is the closest to the pinned
environment: Mathlib's `v4.34.1` tag, pinned here, differs from its `v4.34.0`
tag only in the toolchain file. The default project with the latest Mathlib
stops at the imports. The server's projects are not pinned by this repository
and are replaced as new releases appear, so a later server project may require
a separate port and revalidation. The [server's URL documentation](https://github.com/leanprover-community/lean4web/blob/main/doc/Usage.md)
describes `#url=...` and `project=...`.

This edition is much larger than a small Lean4Web example. On 2026-10-12 (UTC)
the current file, opened through the link above, was processed to the end in
that project: 270 messages, none of them an error, and only the three standard
axioms for the four final theorems. Earlier the same day, with the file as it
was before its last 470 or so lines were regenerated, one manual run completed
in the same way and one lost its connection to the server at about 92% of the
file. These observations and the server's project list are recorded in
[`hosted-status.json`](hosted-status.json).
A local build is the reproducible check; server resource limits and version
compatibility are separate from proof correctness.

