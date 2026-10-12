#!/usr/bin/env bash
# Cache a partial build at the 300 minute boundary; rerun the SAME commit to resume.
set -euo pipefail
mkdir -p ../build-receipt
set +e
timeout --kill-after=120 300m lake build QubitAdditivity \
  2>&1 | tee ../build-receipt/build.log
QUBIT_PIPE=("${PIPESTATUS[@]}")
set -e
QUBIT_CODE=${QUBIT_PIPE[0]}
test "${QUBIT_PIPE[1]}" -eq 0
if [[ "$QUBIT_CODE" -eq 0 ]]; then
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "$QUBIT_CODE" -eq 124 || "$QUBIT_CODE" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun same commit to resume cached build\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "$QUBIT_CODE" > ../build-receipt/status.txt
  exit "$QUBIT_CODE"
fi
