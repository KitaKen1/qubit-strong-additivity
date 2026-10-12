#!/usr/bin/env python3
"""Copy the FC definitions and both targets into the trusted Comparator challenge."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]
PATH = 'FClikelean/QubitHolevoAdditivity.lean'
CHALLENGE = 'lean/ComparatorChallenges/QubitHolevoAdditivity.lean'
TARGETS = ['strong_additivity', 'power_additivity']
IMPORTS = """import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic"""

def generated():
    text = (ROOT / PATH).read_text()
    if text.count('  sorry\n') != len(TARGETS):
        raise ValueError('Expected exactly one hole for each target theorem')
    body = text[text.index('namespace QubitHolevo'):]
    # The FC import, the module/public declarations and the review attributes are left out.
    for name in TARGETS:
        if body.count('theorem ' + name + ' ') != 1:
            raise ValueError('Expected exactly one statement of ' + name)
        b = body.index('theorem ' + name + ' ')
        a = body.rindex('@[category research solved', 0, b)
        body = body[:a] + body[b:]
    if '@[' in body or 'formal_proof' in body:
        raise ValueError('Unexpected attribute left in the challenge')
    return {CHALLENGE: IMPORTS + '\n\n' + body}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    for name, content in generated().items():
        path = ROOT / name
        if args.check:
            if path.read_text() != content:
                raise SystemExit('Generated file differs: ' + name)
        else:
            path.write_text(content)
    print('Mathematical-body extraction checked.' if args.check else 'Challenge generated.')
