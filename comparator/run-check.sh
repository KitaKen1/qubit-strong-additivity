#!/usr/bin/env bash
set -euo pipefail
QUBIT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
QUBIT_RECEIPT="$QUBIT_ROOT/comparator-receipt"
QUBIT_CONFIG=ComparatorChallenges/QubitHolevoAdditivity.json
mkdir -p "$QUBIT_RECEIPT"
printf 'NOT_RUN\n' > "$QUBIT_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$QUBIT_RECEIPT/status.txt"; fi' EXIT
python3 "$QUBIT_ROOT/comparator/check-inputs.py" --receipt-dir "$QUBIT_RECEIPT"
test "$(uname -s)" = Linux
python3 - "$QUBIT_ROOT/comparator/pins.json" "$COMPARATOR_TOOLS" "$QUBIT_ROOT/lean/lean-toolchain" <<'PY'
from pathlib import Path
import json, subprocess, sys
pins=json.load(open(sys.argv[1])); tools=Path(sys.argv[2])
for tool,key in [('comparator','comparator_commit'),('landrun','landrun_commit'),('lean4export','lean4export_commit')]:
    actual=subprocess.check_output(['git','-C',str(tools/tool),'rev-parse','HEAD'],text=True).strip()
    if actual!=pins[key]: raise SystemExit('Tool commit differs: '+tool)
if (tools/'lean4export/lean-toolchain').read_bytes()!=Path(sys.argv[3]).read_bytes():
    raise SystemExit('Exporter toolchain differs from proof')
PY
for QUBIT_FILE in "lean/$QUBIT_CONFIG" comparator/pins.json .github/workflows/comparator.yml \
    lean/QubitAdditivity/FCPresentation.lean lean/QubitAdditivity/Presentation/Model.lean; do
  cp "$QUBIT_ROOT/$QUBIT_FILE" "$QUBIT_RECEIPT/$(basename "$QUBIT_FILE")"
done
{
  printf 'run_url=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
  printf 'run_attempt=%s\ntested_commit=%s\n' "${GITHUB_RUN_ATTEMPT:-local}" "$(git -C "$QUBIT_ROOT" rev-parse HEAD)"
  date -u +started_utc=%FT%TZ
  uname -a; id
  (cd "$QUBIT_ROOT/lean" && lake env lean --version)
  for QUBIT_TOOL in comparator landrun lean4export; do
    printf '%s_commit=%s\n' "$QUBIT_TOOL" "$(git -C "$COMPARATOR_TOOLS/$QUBIT_TOOL" rev-parse HEAD)"
  done
  git -C "$COMPARATOR_TOOLS/lean4export" diff -- lean-toolchain
  printf 'sandbox: unprivileged uid/gid, RestrictAddressFamilies=~AF_UNIX, NoNewPrivileges=yes\n'
} > "$QUBIT_RECEIPT/environment.txt"
set +e
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=240min --working-directory="$QUBIT_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" "$QUBIT_CONFIG" \
  2>&1 | tee "$QUBIT_RECEIPT/comparator.log"
QUBIT_PIPE=("${PIPESTATUS[@]}")
set -e
test "${QUBIT_PIPE[0]}" -eq 0
test "${QUBIT_PIPE[1]}" -eq 0
grep -Fxq 'Lean default kernel accepts the solution' "$QUBIT_RECEIPT/comparator.log"
grep -Fxq 'Your solution is okay!' "$QUBIT_RECEIPT/comparator.log"
python3 "$QUBIT_ROOT/comparator/check-inputs.py" --receipt-dir "$QUBIT_RECEIPT/after"
# Inspect the solution only after the sandboxed Comparator has accepted it.
(cd "$QUBIT_ROOT/lean" && lake env lean FCAudit.lean) 2>&1 | tee "$QUBIT_RECEIPT/axioms.log"
python3 - "$QUBIT_RECEIPT/axioms.log" <<'PY'
from pathlib import Path
import sys
text=Path(sys.argv[1]).read_text()
for name in ['QubitHolevo.strong_additivity','QubitHolevo.power_additivity',
             'QubitAdditivity.GeneralResult.generalQubitStrongAdditivity']:
 expected="'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
 if text.count(expected)!=1: raise SystemExit('Missing exact axiom receipt for '+name)
if 'sorryAx' in text or 'error:' in text: raise SystemExit('Axiom audit failed')
PY
printf 'PASS\n' > "$QUBIT_RECEIPT/status.txt"
