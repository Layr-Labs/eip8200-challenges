#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."

if [[ "${1:-}" == --fast ]]; then
  exec .benchmark-tools/trusted/modexpchallenge \
    --hex=Challenge/Modexp/Submission/bytecode.hex --csv
fi

# ponytail: serialize the two memory-heavy proof modules; revisit if Lake gains a job limit.
lake build Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesLow
lake build Challenge.Modexp.Submission.Proofs.Bytecode.MainTrampolinesHigh
exec ./benchmark.sh modexp
