#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly challenge_dir="Challenge/Ripemd160"
readonly challenge_module="Challenge.Ripemd160"
readonly challenge_display="RIPEMD-160"
readonly scorer_exe="ripemd160challenge"

source scripts/lib/check-hash-submissions.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
