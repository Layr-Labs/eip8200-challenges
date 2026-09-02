#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly submission_checker_script="scripts/check-ripemd160-submissions.sh"
readonly challenge_slug="ripemd160"
readonly marker_id="RIPEMD160"
readonly report_script_path="scripts/report-ripemd160-gas.sh"
readonly vector_count=17
readonly expected_rows=34
readonly precompile_base=600
readonly precompile_per_word=120
readonly precompile_name="RIPEMD-160"
readonly report_labels=(
  "empty"
  "abc"
  "55-byte"
  "56-byte"
  "64-byte"
  "1000-byte"
)

source scripts/lib/report-hash-gas.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
