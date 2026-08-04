#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly challenge_dir="Challenge/Sha256"
readonly challenge_module="Challenge.Sha256"
readonly challenge_display="SHA-256"
readonly scorer_exe="sha256challenge"

source scripts/lib/check-hash-submissions.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
