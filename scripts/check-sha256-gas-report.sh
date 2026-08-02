#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

generated="$(scripts/report-sha256-gas.sh)"
current="$(sed -n \
  '/<!-- BEGIN GENERATED SHA256 GAS REPORT -->/,/<!-- END GENERATED SHA256 GAS REPORT -->/p' \
  Challenge/Sha256/README.md)"

if [[ -z "$current" ]]; then
  printf 'error: Challenge/Sha256/README.md has no generated gas report section\n' >&2
  exit 1
fi

if ! diff -u <(printf '%s\n' "$current") <(printf '%s\n' "$generated"); then
  printf 'error: SHA-256 gas report is stale; replace its generated section with:\n\n%s\n' \
    "$generated" >&2
  exit 1
fi

printf 'SHA-256 gas report is current\n'
printf '%s\n' "$generated"
