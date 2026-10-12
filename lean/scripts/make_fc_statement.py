#!/usr/bin/env python3
"""Write the Formal Conjectures form of the Mathlib-only statement.

The vocabulary is copied from QubitAdditivity/Presentation/Model.lean and the theorem
statements from QubitAdditivity/FCPresentation.lean, so the file cannot drift from what is
proved. The `formal_proof` links are pinned to the given commit of the public repository and
to the current line numbers of the proved theorems.

The output is a draft until it has been built inside a Formal Conjectures checkout, which pins
another Lean and Mathlib version than this project.
"""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/KitaKen1/qubit-strong-additivity"
PLACEHOLDER = "COMMIT_OF_THE_PUBLIC_REPOSITORY"

HEADER = '''/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import FormalConjecturesUtil

/-!
# Strong Holevo additivity for qubit channels

Is the Holevo information $\\chi$ additive when one factor is a qubit channel? That is, does
$\\chi(\\Phi \\otimes \\Omega) = \\chi(\\Phi) + \\chi(\\Omega)$ hold for every channel
$\\Phi : M_2(\\mathbb{C}) \\to M_2(\\mathbb{C})$ and every channel
$\\Omega : M_n(\\mathbb{C}) \\to M_m(\\mathbb{C})$ with $n, m \\ge 1$? This is the qubit case of the
additivity problem for the Holevo information. It was known for unital $\\Phi$ [King02] and for
$\\Phi$ with a pure output [TZBW26], and additivity fails for some channels of high dimension
[Has09]. Here no unitality, rank or symmetry condition is imposed on $\\Phi$, and the
optimization for $\\Phi \\otimes \\Omega$ includes entangled inputs. Channels are given by finite
Kraus families.

References:
- [King02] C. King, *Additivity for unital qubit channels*, J. Math. Phys. 43 (2002), 4641.
  https://arxiv.org/abs/quant-ph/0103156
- [Has09] M. B. Hastings, *Superadditivity of communication capacity using entangled inputs*,
  Nature Physics 5 (2009), 255. https://arxiv.org/abs/0809.3972
- [TZBW26] Z. Tang, C. Zhu, G. Bai and X. Wang, *Classical Capacity and Entanglement Cost of
  the Amplitude Damping Channel*, arXiv:2609.28592 (2026). https://arxiv.org/abs/2609.28592
- [Ki26] K. Kitamura, *Strong Holevo additivity for qubit channels* (2026).
  Lean proof: lean/QubitAdditivity/FCPresentation.lean.
-/

@[expose] public section

namespace QubitHolevo

noncomputable section
open scoped ComplexOrder Kronecker
open Matrix

'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", default=PLACEHOLDER,
                        help="commit of the public repository that contains the proof")
    parser.add_argument("--repository", default=REPOSITORY,
                        help="public repository URL containing the proof sources")
    parser.add_argument("--output", default=None,
                        help="file to write; the default is the draft next to the issue text")
    args = parser.parse_args()

    model = (ROOT / "QubitAdditivity/Presentation/Model.lean").read_text()
    vocabulary = model.split("-- BEGIN MODEL\n", 1)[1].split("-- END MODEL", 1)[0]
    proof_file = "QubitAdditivity/FCPresentation.lean"
    proof = (ROOT / proof_file).read_text()
    _, statements = proof.split("\nnamespace QubitHolevo\n", 1)

    repository = args.repository.rstrip("/")
    text = HEADER + vocabulary
    for found in re.finditer(r"(/--(?:(?!-/).)*-/\n)theorem (\w+)\b(.*?):=", statements, re.S):
        doc, name, signature = found.groups()
        line = proof[:proof.index("theorem " + name + " ")].count("\n") + 1
        link = f"{repository}/blob/{args.commit}/lean/{proof_file}#L{line}"
        text += (f"\n{doc}@[category research solved, AMS 81 94,\n"
                 f"    formal_proof using lean4 at \"{link}\"]\n"
                 f"theorem {name}{signature.rstrip()} := by\n  sorry\n")
    text += "\nend\n\nend QubitHolevo\n"

    output = Path(args.output) if args.output else ROOT.parent / "FClikelean/QubitHolevoAdditivity.lean"
    output.write_text(text)
    print(f"Wrote {output}")
    if args.commit == PLACEHOLDER:
        print("The formal_proof links still carry the commit placeholder.")


if __name__ == "__main__":
    main()
