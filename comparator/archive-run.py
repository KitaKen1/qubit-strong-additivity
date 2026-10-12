#!/usr/bin/env python3
"""Archive a completed CI attempt, original ZIPs, complete logs and API metadata locally."""
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, subprocess, urllib.request, urllib.error, zipfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True)
    parser.add_argument('--run', required=True, type=int)
    parser.add_argument('--attempt', required=True, type=int)
    parser.add_argument('--expected-commit', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--public-success-only', action='store_true',
        help='Require a successful run on public main before writing the publication archive.')
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit('Choose a new archive directory; existing evidence will not be overwritten.')
    token = os.environ.get('GH_TOKEN')
    if not token:
        credential = subprocess.run(['git', 'credential', 'fill'],
            input='protocol=https\nhost=github.com\npath='+args.repo+'.git\n\n',
            text=True, capture_output=True, check=True)
        token = dict(line.split('=',1) for line in credential.stdout.splitlines() if '=' in line)['password']
    headers = {'Authorization':'Bearer '+token, 'Accept':'application/vnd.github+json',
        'X-GitHub-Api-Version':'2026-03-10', 'User-Agent':'Qubit-Comparator-Archive'}

    class NoRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, *a, **kw): return None

    def get(endpoint):
        request = urllib.request.Request('https://api.github.com/repos/'+args.repo+endpoint, headers=headers)
        try:
            with urllib.request.build_opener(NoRedirect).open(request, timeout=60) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            if error.code != 302: raise
            # Signed storage links are fetched without forwarding the GitHub credential.
            with urllib.request.urlopen(urllib.request.Request(error.headers['Location'],
                headers={'User-Agent':headers['User-Agent']}), timeout=60) as response:
                return response.read()

    def save(name, data):
        path = args.output/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def extract(path, dest):
        with zipfile.ZipFile(path) as archive:
            if archive.testzip() is not None: raise ValueError('Invalid ZIP checksum')
            for item in archive.infolist():
                if not (dest/item.filename).resolve().is_relative_to(dest.resolve()):
                    raise ValueError('Unsafe ZIP path')
                if (item.external_attr>>16)&0o170000==0o120000:
                    raise ValueError('ZIP contains symbolic link')
            archive.extractall(dest)

    attempt_path = f'/actions/runs/{args.run}/attempts/{args.attempt}'
    endpoints = {'github/attempt.json':attempt_path,
        'github/jobs.json':attempt_path+'/jobs?per_page=100',
        'github/artifacts.json':f'/actions/runs/{args.run}/artifacts?per_page=100',
        'github/workflow-logs.zip':attempt_path+'/logs'}
    with ThreadPoolExecutor(max_workers=4) as pool:
        pending = {name:pool.submit(get,path) for name,path in endpoints.items()}
        downloaded = {name:future.result() for name,future in pending.items()}
    run = json.loads(downloaded['github/attempt.json'])
    if run['status']!='completed' or run['head_sha']!=args.expected_commit:
        raise SystemExit('Attempt is incomplete or tested commit differs.')
    if args.public_success_only:
        repository = json.loads(get(''))
        if repository['private'] or run['conclusion']!='success' or run['head_branch']!='main':
            raise SystemExit('Publication archive requires successful public main CI.')
        downloaded['github/repository.json'] = (json.dumps(repository,indent=2)+'\n').encode()
    for name,data in downloaded.items(): save(name,data)
    jobs = json.loads(downloaded['github/jobs.json'])
    artifacts = json.loads(downloaded['github/artifacts.json'])
    if jobs['total_count']>100 or artifacts['total_count']>100:
        raise SystemExit('Pagination required; no partial archive accepted.')
    suffix = f'-{args.run}-{args.attempt}'
    chosen = [a for a in artifacts['artifacts'] if a['name'].endswith(suffix)]
    if not chosen: raise SystemExit('No attempt-specific artifacts found.')
    records=[]
    for artifact in chosen:
        if artifact['expired']: raise SystemExit('Artifact expired: '+artifact['name'])
        name=f'artifacts/{artifact["id"]}-{artifact["name"]}.zip'
        data=get(f'/actions/artifacts/{artifact["id"]}/zip')
        digest=hashlib.sha256(data).hexdigest()
        if artifact.get('digest')!='sha256:'+digest:
            raise SystemExit('GitHub artifact digest missing or differs: '+artifact['name'])
        save(name,data)
        extract(args.output/name,args.output/'receipt'/artifact['name'])
        records.append({'id':artifact['id'],'name':artifact['name'],'file':name,
            'github_digest':artifact['digest'],'sha256':digest,'digest_matches':True,
            'expires_at':artifact['expires_at']})
    extract(args.output/'github/workflow-logs.zip',args.output/'github/logs')
    for job in jobs['jobs']:
        if job['conclusion']!='skipped':
            save(f'github/job-{job["id"]}.log',get(f'/actions/jobs/{job["id"]}/logs'))
    if run['conclusion']=='success':
        receipt=args.output/'receipt'/f'comparator-{args.run}-{args.attempt}'
        if (receipt/'status.txt').read_text()!='PASS\n': raise SystemExit('Comparator receipt is not PASS')
        check=json.loads((receipt/'input-check.json').read_text())
        if check['tested_commit']!=args.expected_commit: raise SystemExit('Receipt commit differs')
        log=(receipt/'comparator.log').read_text()
        for literal in ['Lean default kernel accepts the solution','Your solution is okay!']:
            if literal not in log: raise SystemExit('Missing success evidence: '+literal)
        axioms=(receipt/'axioms.log').read_text()
        for target in check['pins']['targets']:
            if f"'{target}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in axioms:
                raise SystemExit('Missing target axiom evidence: '+target)
    provenance={'repository':args.repo,'run_id':args.run,'run_attempt':args.attempt,
        'proof_commit':None,'tested_commit':args.expected_commit,'archive_commit':None,
        'run_url':run['html_url'],'conclusion':run['conclusion'],'artifacts':records,
        'retrieved_at_utc':datetime.now(timezone.utc).isoformat(),
        'note':'API metadata, original ZIPs, full job logs and all extracted receipts preserved. SHA256SUMS are local file identities, not a signed GitHub attestation. Record the archive commit after committing.'}
    if run['conclusion']=='success':
        provenance['proof_commit']=check['pins']['proof_commit']
        provenance['target_scope']=check['pins']['challenge_kind']
    save('provenance.json',(json.dumps(provenance,indent=2)+'\n').encode())
    paths=sorted(p for p in args.output.rglob('*') if p.is_file())
    save('SHA256SUMS',(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(args.output).as_posix()+'\n' for p in paths)).encode())
    print(f'Archived {len(records)} artifacts and {len(paths)} files to {args.output}')


if __name__=='__main__': main()
