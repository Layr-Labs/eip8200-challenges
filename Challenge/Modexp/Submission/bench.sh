#!/usr/bin/env bash
set -euo pipefail

# Cheap MODEXP iteration loop.
#   --score       run the protected scorer only (milliseconds; no Lean build)
#   --check       score and check bytecode.hex == Bytes.lean
#   --verify      incrementally run the Lean comparator, then score
#   --ranked      run the repository's full ranked benchmark (slow)
#
# --verify deliberately keeps generated benchmark modules and Lake artifacts.
# Repeating it for unchanged bytes therefore does not recompile anything.
root="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$root"

readonly submission="Challenge/Modexp/Submission/bytecode.hex"
readonly scorer=".benchmark-tools/trusted/modexpchallenge"
readonly comparator=".benchmark-tools/comparator/.lake/build/bin/comparator"
readonly lean4export=".benchmark-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
readonly fake_landrun=".benchmark-tools/comparator/scripts/fake-landrun.sh"
readonly config="benchmark/comparator-modexp.json"
readonly result_dir="benchmark-results/modexp"
readonly trusted="$result_dir/verified-bytecode.hex"
readonly artifact="Challenge/Modexp/Benchmark/Artifact.lean"
readonly challenge="Challenge/Modexp/Benchmark/Challenge.lean"

usage() {
  echo "usage: $0 [--score|--check|--verify|--ranked] [hex-file]" >&2
  exit 64
}

mode="${1:---score}"
if [[ "$mode" == --* ]]; then shift; else mode=--score; fi
hex="${1:-$submission}"
[[ -f "$hex" ]] || { echo "missing bytecode: $hex" >&2; exit 1; }
[[ -x "$scorer" ]] || { echo "missing scorer; run ./setup.sh modexp" >&2; exit 1; }

check_bytes() {
  python3 - "$hex" Challenge/Modexp/Submission/Bytes.lean <<'PY'
from pathlib import Path
import re, sys
hex_path, bytes_path = map(Path, sys.argv[1:])
raw = hex_path.read_text(encoding="ascii").strip()
if not re.fullmatch(r"(?:[0-9a-f]{2})+", raw):
    raise SystemExit("bytecode.hex must be one lowercase hex byte string")
actual = bytes.fromhex(raw)
expected = bytes(int(x, 16) for x in re.findall(r"0x([0-9a-f]{2})", bytes_path.read_text()))
if actual != expected:
    first = next((i for i, (a, b) in enumerate(zip(actual, expected)) if a != b), min(len(actual), len(expected)))
    raise SystemExit(f"bytecode/proof mismatch at byte {first}: {len(actual)} vs {len(expected)} bytes")
print(f"byte-consistent: {len(actual)} bytes")
PY
}

score() {
  local csv
  csv="$(mktemp)"
  "$scorer" --hex="$hex" --csv > "$csv"
  python3 - "$csv" <<'PY'
import csv, sys
with open(sys.argv[1], newline="") as f:
    rows = list(csv.DictReader(f))
if len(rows) != 44 or any(r["status"] != "ok" for r in rows):
    raise SystemExit("scorer did not return 44 successful MODEXP vectors")
print(f"score: {sum(int(r['gas']) for r in rows)} gas over {len(rows)} vectors")
PY
  rm -f "$csv"
}

prepare_incrementally() {
  mkdir -p "$result_dir"
  # prepare.py rewrites generated files. Avoid calling it when the bytes and
  # generated inputs are already current, because Lake uses their mtimes.
  if [[ ! -f "$trusted" || ! -f "$artifact" || ! -f "$challenge" ]] ||
     ! cmp -s "$hex" "$trusted"; then
    python3 scripts/yukon_benchmark.py prepare modexp "$hex" "$trusted" "$artifact" "$challenge"
  else
    echo "reusing generated MODEXP inputs"
  fi
}

case "$mode" in
  --score)
    score
    ;;
  --check)
    check_bytes
    score
    ;;
  --verify)
    check_bytes
    prepare_incrementally
    [[ -x "$comparator" && -x "$lean4export" ]] || { echo "missing comparator tools; run ./setup.sh modexp" >&2; exit 1; }
    export COMPARATOR_LEAN4EXPORT="$root/$lean4export"
    export COMPARATOR_LANDRUN="$root/$fake_landrun"
    # One Lean worker is slower per file but avoids the several multi-GB proof
    # processes that can otherwise exhaust RAM. Lake/Lean still reuse oleans.
    export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
    # Bound a failed experiment rather than allowing the host to OOM. Set 0
    # on a machine with more RAM if a particular proof needs a larger address
    # space.
    if [[ "${MODEXP_VMEM_KB:-33554432}" != 0 ]]; then
      ulimit -v "$MODEXP_VMEM_KB"
    fi
    lake env "$root/$comparator" "$root/$config"
    "$scorer" --hex="$trusted" --csv > "$result_dir/scorer.csv"
    python3 scripts/yukon_benchmark.py score modexp "$trusted" "$result_dir/scorer.csv" "$result_dir/score.json" "$result_dir/summary.md"
    cat "$result_dir/summary.md"
    ;;
  --ranked)
    BENCHMARK_INSECURE_LOCAL="${BENCHMARK_INSECURE_LOCAL:-0}" ./benchmark.sh modexp
    ;;
  *) usage ;;
esac
