#!/usr/bin/env python3
"""Fail closed on changed targets, dependencies, challenge or pinned proof sources."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, subprocess, sys
from importlib.machinery import SourceFileLoader

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
CHALLENGE = 'lean/ComparatorChallenges/QubitHolevoAdditivity.lean'
CONFIG = 'lean/ComparatorChallenges/QubitHolevoAdditivity.json'
RELEASE = 'leanWithoutComparator/sources.json'
SOURCE_LAKEFILE = 'leanWithoutComparator/lakefile.toml'
# Pinned files and the key of their SHA-256 in pins.json.
PINNED = [(RELEASE, 'proof_release_manifest_sha256'), (SOURCE_LAKEFILE, 'proof_source_lakefile_sha256'),
          ('FClikelean/QubitHolevoAdditivity.lean', 'fc_draft_sha256'), (CHALLENGE, 'challenge_sha256'),
          (CONFIG, 'config_sha256'), ('lean/QubitAdditivity/FCPresentation.lean', 'solution_sha256'),
          ('lean/QubitAdditivity/Presentation/Model.lean', 'definitions_sha256'),
          ('lean/FCAudit.lean', 'audit_sha256')]
# The proof lakefile has only this review library added to the original.
REVIEW_LIBRARY = '[[lean_lib]]\nname = "ComparatorChallenges"\nglobs = ["ComparatorChallenges.+"]\n\n'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, message):
    if not ok: raise SystemExit(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path)
    args = parser.parse_args()
    pins = json.loads((ROOT / 'comparator/pins.json').read_text())
    config = json.loads((ROOT / CONFIG).read_text())
    targets = ['QubitHolevo.strong_additivity', 'QubitHolevo.power_additivity']
    require(config['theorem_names'] == pins['targets'] == targets, 'Target list changed or incomplete')
    require(config['challenge_module'] == 'ComparatorChallenges.QubitHolevoAdditivity'
            and config['solution_module'] == 'QubitAdditivity.FCPresentation', 'Unexpected modules')
    require(sorted(config['permitted_axioms']) == sorted(['propext','Classical.choice','Quot.sound']), 'Unexpected axioms')
    require(not config.get('definition_names') and not config.get('enable_nanoda')
            and not config.get('external_kernels'), 'Unexpected Comparator options')
    require(pins['fc_draft_path'] == PINNED[2][0], 'Unexpected FC draft path')
    for name, key in PINNED:
        require(sha(ROOT/name) == pins[key], 'Pinned file changed: ' + name)
    render = SourceFileLoader('qubit_render', str(ROOT/'comparator/render-target.py')).load_module()
    for name, content in render.generated().items():
        require((ROOT/name).read_text()==content, 'FC mathematical body differs: ' + name)
    # leanWithoutComparator/ is the original proof release: lean/ must hold the same files.
    release = json.loads((ROOT/RELEASE).read_text())
    hashes = {}
    for name, expected in release['identical_to_source'].items():
        for p in (ROOT/'lean'/name, ROOT/'leanWithoutComparator'/name):
            require(p.is_file() and sha(p)==expected, 'Original proof-release input changed: '+str(p.relative_to(ROOT)))
        hashes[name]=expected
    lakefile = (ROOT/'lean/lakefile.toml').read_text()
    require(lakefile.count(REVIEW_LIBRARY)==1 and
            lakefile.replace(REVIEW_LIBRARY, '')==(ROOT/SOURCE_LAKEFILE).read_text(), 'Unexpected lakefile changes')
    expected_sources={n for n in hashes if n.endswith('.lean')}
    actual={p.relative_to(ROOT/'lean').as_posix() for d in ['QubitAdditivity','vendor'] for p in (ROOT/'lean'/d).rglob('*.lean')}
    actual |= {'QubitAdditivity.lean', 'Audit.lean'}
    require(actual==expected_sources, 'Extra or missing proof sources')
    require((ROOT/'lean/lean-toolchain').read_text().strip()==pins['lean_toolchain'], 'Toolchain changed')
    deps={p['name']:p['rev'] for p in json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']}
    require(deps['mathlib']==pins['mathlib_commit'], 'Mathlib changed')
    git=subprocess.run(['git','-C',str(ROOT),'rev-parse','--show-toplevel'],capture_output=True,text=True)
    commit=None
    if git.returncode==0 and Path(git.stdout.strip()).resolve()==ROOT.resolve():
        commit=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','HEAD'],text=True).strip()
    result={'input_check':'passed','checked_at_utc':datetime.now(timezone.utc).isoformat(),
            'tested_commit':commit,'candidate_only':commit is None,'pins':pins,'config':config,
            'unchanged_proof_release_file_count':len(hashes),'unchanged_proof_release_sha256':hashes,
            'scope':pins['challenge_kind'],'fc_checkout_compatibility':pins['fc_checkout_compatibility']}
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True,exist_ok=True)
        (args.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
        (args.receipt_dir/'Challenge.lean').write_bytes((ROOT/CHALLENGE).read_bytes())
    print(f'Input check passed: {len(targets)} targets, {len(hashes)} unchanged release inputs; FC checkout compatibility pending.')

if __name__=='__main__': main()
