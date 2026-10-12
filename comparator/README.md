# Qubit Holevo additivity proposed FC target verification

The FC-target verification described here has not been run on public `main` yet. No public run
records exist, and no Formal Conjectures PR has been created. The setup follows the verification of
[KitaKen1/smooth-isometric-embeddings-r4](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/tree/main/comparator),
which uses the same Lean and Mathlib versions.

The targets are `QubitHolevo.strong_additivity` and `QubitHolevo.power_additivity`. The complete
proposed FC-style file is in `FClikelean/QubitHolevoAdditivity.lean`; that folder also contains
the statement guide.
`render-target.py` copies its definitions and both statements and generates the trusted file
`lean/ComparatorChallenges/QubitHolevoAdditivity.lean`, with nine pinned Mathlib imports and the
theorems' intended `sorry` holes. The FC import, the module/public declarations and the review
attributes are removed; nothing else changes.
The solution module is `QubitAdditivity.FCPresentation`. It imports the definitions from
`QubitAdditivity/Presentation/Model.lean`, which imports only the same nine Mathlib modules,
retains the same statements and names, and fills the holes from
`QubitAdditivity.GeneralResult.strongHolevoAdditivity`.

This extraction is explicit: **the challenge is not a byte-for-byte copy of an upstream FC file.**
The full draft is preserved and hashed, and the generated file is checked against it. The FC
file is not submitted, so `fc_target_commit` and `fc_pr` are null rather than invented identifiers.

Unlike the R4 setup, the challenge and the solution each elaborate their own copy of the five
definitions. Comparator compares the two copies declaration by declaration, and
`lean/scripts/verify.py` checks that their source text is identical.

Upstream FC uses Lean 4.33.1. This proof uses Lean 4.34.1 / Mathlib `d13f23b…`.
The current draft's compatibility with a real FC checkout remains pending. Do not describe
this candidate as an accepted FC theorem, a validated upstream FC checkout, or an exact
upstream-target Comparator run. First build the proposed statement and definitions in a real
FC checkout. If incompatibilities are found, determine the smallest changes needed, keep the
submitted and external target definitions aligned, and then freeze the submitted FC head/path
for the final exact-target comparison.

## Fixed inputs

`pins.json` fixes the proof release, the proposed draft, the challenge, the toolchain, Mathlib and
three tool revisions. The proof release is [`leanWithoutComparator/`](../leanWithoutComparator/README.md):
`check-inputs.py` checks that all 154 files listed in its `sources.json` are unchanged in `lean/`
and in the copy, and that no proof source is extra or missing. The proof lakefile only adds the
`ComparatorChallenges` review library; its unchanged original is `leanWithoutComparator/lakefile.toml`.

```bash
python3 comparator/render-target.py --check
python3 comparator/check-inputs.py --receipt-dir input-receipt
```

After a deliberate change of the statement or of the proof, regenerate and repin:

```bash
python3 lean/scripts/make_fc_statement.py
python3 comparator/render-target.py
python3 lean/scripts/make_lean_without_comparator.py
python3 comparator/refresh-pins.py
```

For a built proof workspace, the local preflight is:

```bash
python3 comparator/local-precheck.py --receipt-dir local-precheck-receipt
```

It builds the challenge and the solution as separate modules, compares both theorems and all
reachable declarations using the pinned Comparator's equality/traversal rules, and audits the
solution's axioms. Its success status is `LOCAL_PRECHECK_PASS`, **not** `PASS` for a Linux
Comparator run.

## Private CI first, then public main CI

First run `.github/workflows/comparator.yml` in a private verification repository. Check both
FC targets, permitted axioms and kernel acceptance; repair setup or target issues there.
Freeze the successful proof and verification configuration, publish them to public `main`, and
rerun this same workflow in the public repository. Private success alone is not public-run evidence.

The workflow is manual (`workflow_dispatch`), with read-only repository
permissions and three substantive jobs:

1. Build the complete proof on a separate runner. Save the complete or partial build under the
   exact tested commit; if the 300-minute build window expires, rerun the same commit to resume.
   An incomplete round fails the final gate rather than appearing verified.
2. On a fresh checker runner, compile the trusted extracted challenge, install pinned tools,
   restore proof products, restore the separately compiled challenge, and run Comparator through
   landrun under an unprivileged systemd service. AF_UNIX is restricted. The checking job does
   not compile the solution outside the sandbox before Comparator acceptance.
3. Independently replay the whole proof environment using `leanchecker --fresh`.

Comparator success additionally requires exact success lines and exact axiom lines for both FC
targets and for the original theorem `generalQubitStrongAdditivity`. Failed receipts are also
uploaded. All artifact retention is 90 days. The final gate requires all three jobs to succeed.
Runner preparation and swap helpers live in `comparator/prepare-runner.sh` and
`comparator/add-swap.sh`.

To build and inspect the proof locally, from the repository root:

```bash
cd lean
lake exe cache get
lake build QubitAdditivity
lake env lean FCAudit.lean
LEAN_BIN=$(dirname "$(elan which lean)")
lake env "$LEAN_BIN/leanchecker" --fresh QubitAdditivity
```

## Preserve a completed public run

Only after public `main` CI succeeds, archive the completed attempt using its actual IDs:

```bash
python3 comparator/archive-run.py \
  --repo KitaKen1/qubit-strong-additivity \
  --run RUN_ID --attempt ATTEMPT --expected-commit TESTED_COMMIT \
  --public-success-only \
  --output ComparatorLogYYYYMMDD/RUN_ID-attemptATTEMPT
```

Authentication uses `GH_TOKEN` or the existing Git credential helper; credentials are not saved.
The archive preserves original artifact ZIPs, all extracted receipts, original complete workflow
log ZIP, complete job logs, API metadata, artifact IDs/digests/expiry, and `SHA256SUMS`.
The downloaded ZIP digest must equal the GitHub artifact digest. A successful run must contain
`status.txt: PASS`, both Comparator success messages, target axiom lines, and the tested commit.
Existing archive directories are not overwritten. `--public-success-only` rejects a private,
failed or non-main run before writing evidence.

Keep three identities separate: the proof commit, the tested CI commit, and the later archive
commit. The last cannot be embedded as its own commit hash; record it in the README/PR after
committing the archive. Local hashes are file identities, not signed GitHub attestations.

Official references: [Comparator at the pinned revision](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/README.md),
[FC contribution guidance](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md).
