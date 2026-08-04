#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

source scripts/report-sha256-gas.sh
source scripts/lib/check-hash-gas-report.sh

check_hash_gas_report "$@"
