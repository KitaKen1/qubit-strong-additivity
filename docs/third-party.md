# Third-party sources

The exact vendored file list and SHA-256 hashes are in
[`../lean/VENDOR.json`](../lean/VENDOR.json).

| Project | Commit | Use |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Matrix analysis, calculus, entropy ingredients and Lean tactics |
| [Physlib](https://github.com/leanprover-community/physlib/tree/a4ef46125b32bb2599ab42d9c3a95e1d88ca75ff) | `a4ef46125b32bb2599ab42d9c3a95e1d88ca75ff` | Quantum channels, states and entropy lemmas |
| [OpenAI math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` | General matrix-entropy and differentiation lemmas |

Physlib and OpenAI math are Apache-2.0. Their licenses are retained under
`lean/vendor/`, and source-level author notices are preserved. The adapted OpenAI
excerpts under `lean/QubitAdditivity/Imported/` name their source. Verification
checks the stated calculus and entropy-scaling proof bodies against the pinned
originals. The general theorem is not obtained by treating an amplitude-damping
channel result as a theorem about arbitrary qubit channels.

The generated Lean4Web file preserves original notices. Its file header
documents import/module-header removal, section isolation and private-helper
renaming, and its manifest records every included source hash. See its README
for any additional packaging adjustment.

Comparator, lean4export and landrun are downloaded only when the tool
installer or CI is run; their source repositories are not vendored here.

