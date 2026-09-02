#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly challenge_dir="Challenge/Modexp"
readonly challenge_module="Challenge.Modexp"
readonly challenge_display="MODEXP"
readonly scorer_exe="modexpchallenge"

source scripts/lib/check-hash-submissions.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
