#!/usr/bin/env python3
"""Rewrite the SHA-256 pins after a deliberate change of the statement or of the proof.

Run `python3 lean/scripts/make_lean_without_comparator.py` and
`python3 comparator/render-target.py` first, then review the diff of pins.json.
"""
from pathlib import Path
from importlib.machinery import SourceFileLoader
import json, sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True

def main():
    check = SourceFileLoader('qubit_check', str(ROOT/'comparator/check-inputs.py')).load_module()
    path = ROOT/'comparator/pins.json'
    pins = json.loads(path.read_text())
    changed = []
    for name, key in check.PINNED:
        digest = check.sha(ROOT/name)
        if pins.get(key) != digest:
            pins[key] = digest
            changed.append(name)
    path.write_text(json.dumps(pins, indent=2) + '\n')
    print('Pins refreshed for: ' + (', '.join(changed) if changed else 'nothing; all pins were current'))

if __name__ == '__main__': main()
