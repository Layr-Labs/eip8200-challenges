#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly submission_checker_script="scripts/check-sha256-submissions.sh"
readonly challenge_slug="sha256"
readonly marker_id="SHA256"
readonly report_script_path="scripts/report-sha256-gas.sh"
readonly vector_count=19
readonly expected_rows=38
readonly precompile_base=60
readonly precompile_per_word=12
readonly precompile_name="current SHA-256"
readonly report_labels=(
  "empty"
  "abc"
  "55-byte (last one-block)"
  "56-byte (length spills)"
  "64-byte (exact block)"
  "1000-byte"
)

source scripts/lib/report-hash-gas.sh

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
