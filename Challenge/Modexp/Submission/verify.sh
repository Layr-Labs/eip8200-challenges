#!/usr/bin/env bash
set -euo pipefail

# Fast local MODEXP loop.  --fast only measures the protected scorer; --verify
# additionally runs the Lean universal-correctness check, but keeps generated
# benchmark modules in place so an unchanged candidate is fully incremental.
root="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$root"

readonly submission="Challenge/Modexp/Submission/bytecode.hex"
readonly scorer=".benchmark-tools/trusted/modexpchallenge"
readonly comparator=".benchmark-tools/comparator/.lake/build/bin/comparator"
readonly lean4export=".benchmark-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
readonly fake_landrun=".benchmark-tools/comparator/scripts/fake-landrun.sh"
readonly config="benchmark/comparator-modexp.json"
readonly trusted="benchmark-results/modexp/verified-bytecode.hex"
readonly artifact="Challenge/Modexp/Benchmark/Artifact.lean"
readonly challenge="Challenge/Modexp/Benchmark/Challenge.lean"

usage() {
  echo "usage: $0 [--fast|--verify|--check-bytes] [hex-file]" >&2
  exit 64
}

mode="${1:---fast}"
if [[ "$mode" != --* ]]; then
  mode=--fast
else
  shift
fi
hex="${1:-$submission}"
[[ -f "$hex" ]] || { echo "missing bytecode: $hex" >&2; exit 1; }
[[ -x "$scorer" ]] || { echo "missing scorer; run ./setup.sh modexp" >&2; exit 1; }

# Fail before Lean if the editable artifact and its proof-bound byte literal
# diverge.  This catches stale generated artifacts in milliseconds.
check_bytes() {
  python3 - "$hex" Challenge/Modexp/Submission/Bytes.lean <<'PY'
from pathlib import Path
import re, sys
hex_path, bytes_path = map(Path, sys.argv[1:])
raw = hex_path.read_text(encoding="ascii").strip()
if not re.fullmatch(r"(?:[0-9a-f]{2})+", raw):
    raise SystemExit("bytecode.hex is not one lowercase hex byte string")
expected = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-f]{2})", bytes_path.read_text()))
actual = bytes.fromhex(raw)
if actual != expected:
    first = next((i for i, (a, b) in enumerate(zip(actual, expected)) if a != b), min(len(actual), len(expected)))
    raise SystemExit(f"bytecode.hex does not match Bytes.lean at byte {first} ({len(actual)} vs {len(expected)} bytes)")
print(f"byte-consistent: {len(actual)} bytes")
PY
}

score() {
  local csv
  csv="$(mktemp)"
  trap 'rm -f "$csv"' RETURN
  "$scorer" --hex="$hex" --csv > "$csv"
  python3 - "$csv" <<'PY'
import csv, sys
with open(sys.argv[1], newline="") as f:
    rows = list(csv.DictReader(f))
if len(rows) != 44 or any(r["status"] != "ok" for r in rows):
    raise SystemExit("protected scorer did not return 44 successful MODEXP vectors")
print(f"fast score: {sum(int(r['gas']) for r in rows)} gas over {len(rows)} vectors")
PY
}

case "$mode" in
  --check-bytes)
    check_bytes
    ;;
  --fast|--score)
    score
    ;;
  --verify)
    check_bytes
    # Keep generated files and skip prepare entirely when the candidate bytes
    # are unchanged.  This preserves Lake's dependency timestamps and makes a
    # repeated verification of the same candidate a true incremental build.
    if [[ ! -f "$trusted" ]] || ! cmp -s "$hex" "$trusted" ||
       [[ ! -f "$artifact" || ! -f "$challenge" ]]; then
      python3 scripts/yukon_benchmark.py prepare modexp "$hex" "$trusted" "$artifact" "$challenge"
    else
      echo "reusing generated MODEXP benchmark modules"
    fi
    export COMPARATOR_LEAN4EXPORT="$root/$lean4export"
    export COMPARATOR_LANDRUN="$root/$fake_landrun"
    export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
    # Keep a failed proof build from taking down the workstation.  Override
    # with MODEXP_VMEM_KB=0 to disable this guard on a larger machine.
    if [[ "${MODEXP_VMEM_KB:-16777216}" != 0 ]]; then
      ulimit -v "$MODEXP_VMEM_KB"
    fi
    lake env "$root/$comparator" "$root/$config"
    "$scorer" --hex="$trusted" --csv \
      | python3 -c 'import csv,sys; rows=list(csv.DictReader(sys.stdin)); print(f"verified score: {sum(int(r[\"gas\"]) for r in rows)} gas over {len(rows)} vectors")'
    ;;
  *) usage ;;
esac
