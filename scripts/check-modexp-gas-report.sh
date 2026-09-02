#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

readonly report_script_path="scripts/report-modexp-gas.sh"
readonly challenge_dir="Challenge/Modexp"
readonly challenge_display="MODEXP"
readonly marker_id="MODEXP"

source scripts/lib/check-hash-gas-report.sh

check_hash_gas_report "$@"
