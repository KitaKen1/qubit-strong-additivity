# Statement in the format of Formal Conjectures

[QubitHolevoAdditivity.lean](QubitHolevoAdditivity.lean) states strong Holevo additivity for
qubit channels: $`\chi(\Phi\otimes\Omega)=\chi(\Phi)+\chi(\Omega)`$ for every qubit channel
$`\Phi`$ and every finite-dimensional channel $`\Omega`$. Both statements are proved.

- **Main target:** `QubitHolevo.strong_additivity`, for Kraus families `K` of a qubit channel
  and `L` of a channel between systems of positive finite dimension.
- **Consequence:** `QubitHolevo.power_additivity`,
  $`\chi(\Phi^{\otimes n})=n\,\chi(\Phi)`$ for every qubit channel and every $`n\ge0`$.
- **Definitions:** `entropy`, `IsKraus`, `holevo`, `tensorKraus` and `powerKraus` are copied
  verbatim from [Presentation/Model.lean](../lean/QubitAdditivity/Presentation/Model.lean). The
  complete proof in [FCPresentation.lean](../lean/QubitAdditivity/FCPresentation.lean) relates
  them to the project's definitions.
- **Proof links:** both statements use `by sorry`, with `formal_proof` links to the complete
  Lean proofs. Run `fill_links.py` with a public commit to pin these links.

`python3 lean/scripts/check_publication.py` checks that the definitions and both statements
agree with the complete proof. `python3 lean/scripts/make_fc_statement.py` regenerates this
file from the proof sources.

This file has not been compiled inside a Formal Conjectures checkout, which pins another Lean
version than the proof (`v4.33.1`).
