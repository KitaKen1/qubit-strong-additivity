# Lean proof without the Comparator files

This directory is [`../lean/`](../lean/README.md) with its Comparator parts left
out. It is a copy for reading and building the proof alone, not a second
development.

- The files listed under `identical_to_source` in [`sources.json`](sources.json)
  have exactly the bytes of the files at the same paths in `lean/`: the proof
  modules, the vendored Physlib and OpenAI math sources, `Audit.lean`, the
  toolchain and the dependency lockfile.
- `lakefile.toml` is `lean/lakefile.toml` without the `ComparatorChallenges`
  library declaration. Nothing else in it differs.
- The Comparator challenge (statements with intentional `sorry`), its
  configuration, and the verification and publication scripts and records of
  `lean/` are not copied. `sources.json` names each omitted entry.

`lean/` remains the edition that carries the full verification: the axiom
whitelist, the statement comparison, the kernel replay and the Comparator
workflow. This directory relies on those through file identity, and adds its own
build and axiom audit.

## Check the copy

From the repository root:

```sh
python3 lean/scripts/make_lean_without_comparator.py --check
```

The command recomputes the copy from `lean/` and fails on any missing, extra or
differing file. Without `--check` it rewrites this directory, which is how to
update it after `lean/` changes.

## Build

```sh
cd leanWithoutComparator
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the transitive axioms of 741 theorems; only `propext`,
`Classical.choice` and `Quot.sound` may appear. To run the identity check, the
build and that audit together, and to record the result in `verification.json`:

```sh
python3 lean/scripts/verify_lean_without_comparator.py
```

Source comments that mention `ComparatorChallenges/` or `scripts/` refer to
`../lean/`. They are kept because the files are identical.
