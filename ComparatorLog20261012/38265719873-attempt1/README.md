# Lean Comparator records: run 38265719873, attempt 1

The verification on public `main` completed successfully on 12 October 2026 (UTC).
This folder keeps the original artifacts and workflow logs of that run and GitHub's API records in Git,
so that readers can inspect them after the Actions retention period ends.
The records refer to the tested commit below. The later commit that adds this
folder changes documentation and records only.

| Item | Recorded value |
|---|---|
| Repository | `KitaKen1/qubit-strong-additivity` |
| Workflow | `Qubit Holevo additivity proposed FC target verification` |
| Run / attempt | `38265719873` / `1` |
| Branch / event | `main` / `workflow_dispatch` |
| Tested commit | `00e82103c022243203f9bfc2da428cc32eea3c78` |
| Proof commit | `36cfa17e849e4206fbc6aff30efef414e9c85cb6` (target of the `formal_proof` links; the tested commit has the same proof files) |
| Targets | `QubitHolevo.strong_additivity`, `QubitHolevo.power_additivity` |
| Jobs | `build`, `comparator`, `replay`, `verification_status`: all `success` |
| Receipt status | `PASS` in all three receipts |
| Artifacts | `build-38265719873-1`, `comparator-38265719873-1`, `replay-38265719873-1` |
| GitHub artifact expiry | `2027-01-10T14:49:30Z` |

Original online records:
[run](https://github.com/KitaKen1/qubit-strong-additivity/actions/runs/38265719873),
[tested source](https://github.com/KitaKen1/qubit-strong-additivity/tree/00e82103c022243203f9bfc2da428cc32eea3c78).

## What is saved

| File or directory | Contents |
|---|---|
| [artifacts/](artifacts/) | The three original artifact ZIPs, byte for byte |
| [receipt/](receipt/) | Every member of the three ZIPs, extracted without alteration |
| [github/attempt.json](github/attempt.json) | GitHub API response for the run attempt |
| [github/jobs.json](github/jobs.json) | The four jobs and the conclusion of each of their steps |
| [github/artifacts.json](github/artifacts.json) | Artifact identities, sizes, expiry and the digests reported by GitHub |
| [github/repository.json](github/repository.json) | GitHub API response for the repository |
| [github/workflow-logs.zip](github/workflow-logs.zip) | Complete log archive of the run attempt |
| [github/logs/](github/logs/) | Every member of the log archive: the logs of each job and of its steps |
| `github/job-*.log` | The full log of each of the four jobs, as returned by the job-log endpoint |
| [provenance.json](provenance.json) | Index written during archival: run, commits, artifact digests |
| [SHA256SUMS](SHA256SUMS) | Checksums of every other file in this folder, including this guide |

The artifact ZIPs, the log archive, the job logs and the API responses were retrieved through the
GitHub REST API by [comparator/archive-run.py](../../comparator/archive-run.py), run with
`--public-success-only` in a GitHub Actions job. The requests were authenticated with the temporary
token of that job; no credential is saved here.
The receipts contain the complete output of the build (`build.log`), of Comparator
(`comparator.log`) and of the axiom audit (`axioms.log`), and the report of the kernel replay
(`time.log`). This guide was written afterwards, and `SHA256SUMS` was regenerated to include it.

## How to check the result

1. Read [attempt.json](github/attempt.json) and [jobs.json](github/jobs.json). Match the run ID,
   the attempt, `head_sha`, the branch `main` and the `success` conclusions of the run, of the
   four jobs and of the step `Compare targets, audit all target axioms, replay built-in kernel`.
2. Read [QubitHolevoAdditivity.json](receipt/comparator-38265719873-1/QubitHolevoAdditivity.json), the
   Comparator configuration. The targets are `QubitHolevo.strong_additivity` and
   `QubitHolevo.power_additivity`, the challenge module is `ComparatorChallenges.QubitHolevoAdditivity` and
   the solution module is `QubitAdditivity.FCPresentation`. The permitted axioms are `propext`,
   `Classical.choice` and `Quot.sound`.
3. Read [input-check.json](receipt/comparator-38265719873-1/input-check.json) and
   [pins.json](receipt/comparator-38265719873-1/pins.json). The input check passed for the
   tested commit: the 154 files of the proof release have their recorded hashes.
   [Challenge.lean](receipt/comparator-38265719873-1/Challenge.lean),
   [Model.lean](receipt/comparator-38265719873-1/Model.lean) and
   [FCPresentation.lean](receipt/comparator-38265719873-1/FCPresentation.lean) are the files that
   were compared.
4. Read [comparator.log](receipt/comparator-38265719873-1/comparator.log). Its final output is
   `Lean default kernel accepts the solution`, `Your solution is okay!` and
   `Finished with result: success`.
   [status.txt](receipt/comparator-38265719873-1/status.txt) is `PASS`.
   [axioms.log](receipt/comparator-38265719873-1/axioms.log) reports
   `[propext, Classical.choice, Quot.sound]` for both targets and for
   `QubitAdditivity.GeneralResult.generalQubitStrongAdditivity`.
   The timestamped job log of the `comparator` job contains the same output.
5. Read [time.log](receipt/replay-38265719873-1/time.log). The kernel-only replay
   `leanchecker --fresh QubitAdditivity` ended with `Exit status: 0`.
6. Inspect [comparator.yml](receipt/comparator-38265719873-1/comparator.yml) and the
   [launcher at the tested commit](https://github.com/KitaKen1/qubit-strong-additivity/blob/00e82103c022243203f9bfc2da428cc32eea3c78/comparator/run-check.sh).
   A nonzero exit of Comparator or of the log pipeline fails the job. In
   [the pinned Comparator source](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/Main.lean),
   the comparison and the axiom check must pass before the kernel replay, and
   `Your solution is okay!` is printed only after all three.

These checks verify both statements, with the definitions they use, against the challenge
generated from the Formal Conjectures draft, with the three standard axioms. The run used the
built-in Lean kernel; no external kernel was configured.

## Check the hashes

From a clone of this repository:

```bash
cd ComparatorLog20261012/38265719873-attempt1
shasum -a 256 -c SHA256SUMS
```

On Linux, `sha256sum -c SHA256SUMS` is an alternative. Every entry should report `OK`.
The checksums of the three ZIPs in `artifacts/` equal the `digest` values in
[artifacts.json](github/artifacts.json):

```text
build-38265719873-1          sha256:5f31e10a5945111765cbe88216302ad33b4219aef54722ebb88fb2a78bfaeaff
comparator-38265719873-1     sha256:bb7ad6fbab36a677c190dfd2935308322fe8fb6586146198990771cf45ba0e2b
replay-38265719873-1         sha256:ec0f5075cff83699d75ace1f4363c9f6c1e3f6f7a7bce8ace93568de1efed211
```

`comparator/archive-run.py` compared the checksums of the downloaded ZIPs with these digests
before it wrote this folder. The upload steps in the job logs print the same three digests.

## Limits

The saved API responses are unsigned snapshots. The hashes establish byte identity with the
digests recorded by GitHub and detect later changes of this folder; they are not a
cryptographic attestation of the execution. Readers can inspect the original GitHub record
while it is available, and can rerun the verification from the tested source as described in
[comparator/README.md](../../comparator/README.md).
