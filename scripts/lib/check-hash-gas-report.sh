#!/usr/bin/env bash
set -euo pipefail

: "${report_script_path:?report_script_path must name the report command}"
: "${challenge_dir:?challenge_dir must name the challenge directory}"
: "${challenge_display:?challenge_display must name the challenge}"
: "${marker_id:?marker_id must name the generated README section}"

check_hash_gas_report() {
  cd "$(git rev-parse --show-toplevel)"

  local generated current
  generated="$("$report_script_path")"
  current="$(sed -n \
    "/<!-- BEGIN GENERATED $marker_id GAS REPORT -->/,/<!-- END GENERATED $marker_id GAS REPORT -->/p" \
    "$challenge_dir/README.md")"

  if [[ -z "$current" ]]; then
    printf 'error: %s/README.md has no generated gas report section\n' \
      "$challenge_dir" >&2
    return 1
  fi

  if ! diff -u <(printf '%s\n' "$current") <(printf '%s\n' "$generated"); then
    printf 'error: %s gas report is stale; replace its generated section with:\n\n%s\n' \
      "$challenge_display" "$generated" >&2
    return 1
  fi

  printf '%s gas report is current\n' "$challenge_display"
  printf '%s\n' "$generated"
}
