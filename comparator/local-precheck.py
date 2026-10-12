#!/usr/bin/env python3
"""Run the local draft comparison on the built proof workspace, without claiming CI."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lean = root/'lean'
    receipt = args.receipt_dir.resolve()
    receipt.mkdir(parents=True, exist_ok=True)
    (receipt/'status.txt').write_text('NOT_RUN\n')
    started = datetime.now(timezone.utc).isoformat()
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    try:
        subprocess.run(['python3', str(root/'comparator/check-inputs.py'), '--receipt-dir', str(receipt/'inputs')], check=True)
        pins = json.loads((root/'comparator/pins.json').read_text())
        # Challenge and solution are elaborated separately, as two modules of the proof project.
        run = subprocess.run(['lake','build','QubitAdditivity','ComparatorChallenges'], cwd=lean, capture_output=True, text=True)
        (receipt/'build.log').write_text(run.stdout+run.stderr)
        if run.returncode != 0: raise ValueError('Local build failed; see build.log')
        compare = root/'comparator/LocalCompare.lean'
        run = subprocess.run(['lake','env','lean','--run',str(compare)], cwd=lean, capture_output=True, text=True)
        text = run.stdout+run.stderr
        (receipt/'local-comparison.log').write_text(text)
        matches = dict(re.findall(r'LOCAL_MATCH target=(\S+) declaration_count=(\d+) mismatches=0', text))
        if run.returncode or sorted(matches) != sorted(pins['targets']):
            raise ValueError('Declaration comparison failed; see local-comparison.log')
        (receipt/'axioms.log').write_text(''.join(line+'\n' for line in text.splitlines() if ' depends on axioms: ' in line))
        hashes = {name: sha(root/name) for name in [pins['fc_draft_path'], 'comparator/render-target.py',
            'comparator/pins.json', 'comparator/LocalCompare.lean',
            'lean/ComparatorChallenges/QubitHolevoAdditivity.lean', 'lean/QubitAdditivity/FCPresentation.lean',
            'lean/QubitAdditivity/Presentation/Model.lean']}
        (receipt/'pins.json').write_bytes((root/'comparator/pins.json').read_bytes())
        result = {'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
            'status':'LOCAL_PRECHECK_PASS','targets':pins['targets'],
            'compared_declaration_count':{target:int(count) for target,count in matches.items()},
            'mismatches':0,'permitted_axioms':['propext','Classical.choice','Quot.sound'],
            'proof_commit':pins['proof_commit'],'fc_draft_sha256':pins['fc_draft_sha256'],
            'input_sha256':hashes,'tested_commit':None,'linux_sandbox':'NOT_RUN','kernel_replay_for_fc_target':'NOT_RUN',
            'public_ci':'NOT_RUN','fc_checkout_compatibility':pins['fc_checkout_compatibility'],
            'note':'Local declaration comparison of the extracted proposed FC mathematical target and a compiled solution. This is not a full Comparator or an upstream FC checkout validation.'}
        (receipt/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        (receipt/'status.txt').write_text('LOCAL_PRECHECK_PASS\n')
        print('LOCAL_PRECHECK_PASS: ' + ', '.join(f'{t}: {c} declarations match' for t,c in matches.items())
              + '; axioms audited. Public Linux CI remains NOT_RUN.')
    except BaseException as error:
        (receipt/'status.txt').write_text('FAIL: '+str(error)+'\n')
        raise
    finally:
        files=sorted(p for p in receipt.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
        (receipt/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.relative_to(receipt).as_posix()+'\n' for p in files))


if __name__=='__main__': main()
