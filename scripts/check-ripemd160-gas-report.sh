#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

generated="$(scripts/report-ripemd160-gas.sh)"
current="$(sed -n \
  '/<!-- BEGIN GENERATED RIPEMD160 GAS REPORT -->/,/<!-- END GENERATED RIPEMD160 GAS REPORT -->/p' \
  Challenge/Ripemd160/README.md)"

if [[ -z "$current" ]]; then
  printf 'error: Challenge/Ripemd160/README.md has no generated gas report section\n' >&2
  exit 1
fi

if ! diff -u <(printf '%s\n' "$current") <(printf '%s\n' "$generated"); then
  printf 'error: RIPEMD-160 gas report is stale; replace its generated section with:\n\n%s\n' \
    "$generated" >&2
  exit 1
fi

printf 'RIPEMD-160 gas report is current\n'
printf '%s\n' "$generated"
