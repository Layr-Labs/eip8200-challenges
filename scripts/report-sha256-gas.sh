#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

cd "$(git rev-parse --show-toplevel)"

# Reuse the axiom-footprint parser used for functional correctness proofs.
source scripts/check-sha256-submissions.sh

readonly gas_module_suffix="Gas"
readonly report_sizes=(0 3 55 56 64 1000)
readonly report_labels=(
  "empty"
  "abc"
  "55-byte (last one-block)"
  "56-byte (length spills)"
  "64-byte (exact block)"
  "1000-byte"
)

declare -a implementation_names=("Reference")
declare -a implementation_links=("Reference/")
declare -a artifact_paths=("Challenge/Sha256/Reference/reference.hex")
declare -a gas_files=("Challenge/Sha256/Reference/Proofs/Gas.lean")
declare -a gas_modules=("Challenge.Sha256.Reference.Proofs.Gas")
declare -a bytecode_names=("Challenge.Sha256.referenceBytecode")
declare -a schedule_names=("Challenge.Sha256.Reference.Proofs.Gas.gasSchedule")
declare -a schedule_theorems=("Challenge.Sha256.Reference.Proofs.Gas.gasSchedule_correct")
reference_clean_total=""
reference_dirty_total=""

discover_submissions() {
  local submission_dir
  for submission_dir in "$submission_root"/*; do
    [[ -d "$submission_dir" ]] || continue
    local name
    name="$(basename "$submission_dir")"
    if [[ ! "$name" =~ ^[A-Z][A-Za-z0-9_]*$ ]]; then
      printf 'error: submission directory %s is not an UpperCamelCase Lean identifier\n' \
        "$name" >&2
      return 1
    fi
    if [[ ! -f "$submission_dir/bytecode.hex" ]]; then
      printf 'error: %s is missing bytecode.hex\n' "$submission_dir" >&2
      return 1
    fi
    local module="$module_prefix.$name"
    implementation_names+=("$name")
    implementation_links+=("Submissions/$name/")
    artifact_paths+=("$submission_dir/bytecode.hex")
    gas_files+=("$submission_dir/Gas.lean")
    gas_modules+=("$module.$gas_module_suffix")
    bytecode_names+=("$module.bytecode")
    schedule_names+=("$module.gasSchedule")
    schedule_theorems+=("$module.gasSchedule_correct")
  done
}

canonical_hex_size() {
  local path="$1"
  local hex
  hex="$(<"$path")"
  if [[ ! "$hex" =~ ^([0-9a-f][0-9a-f])*$ ]]; then
    printf 'error: %s is not canonical lowercase bytecode hex\n' "$path" >&2
    return 1
  fi
  printf '%s' "$(( ${#hex} / 2 ))"
}

display_pair() {
  local clean="$1"
  local dirty="$2"
  if [[ "$clean" == "$dirty" ]]; then
    printf '%s' "$clean"
  else
    printf '%s / %s' "$clean" "$dirty"
  fi
}

format_ratio() {
  local numerator="$1"
  local denominator="$2"
  awk -v numerator="$numerator" -v denominator="$denominator" \
    'BEGIN { printf "%.2f", numerator / denominator }'
  printf '×'
}

display_ratio_pair() {
  local clean_numerator="$1"
  local dirty_numerator="$2"
  local clean_denominator="$3"
  local dirty_denominator="$4"
  local clean_ratio dirty_ratio
  clean_ratio="$(format_ratio "$clean_numerator" "$clean_denominator")"
  dirty_ratio="$(format_ratio "$dirty_numerator" "$dirty_denominator")"
  display_pair "$clean_ratio" "$dirty_ratio"
}

report_measured_row() {
  local index="$1"
  local name="${implementation_names[$index]}"
  local path="${artifact_paths[$index]}"
  local csv
  printf 'measuring Tier-1 gas for %s\n' "$name" >&2
  if ! csv="$(lake exe sha256challenge --hex="$path" --csv)"; then
    printf 'error: Tier-1 scorer rejected %s\n' "$name" >&2
    return 1
  fi

  local -A clean=()
  local -A dirty=()
  local clean_total=0
  local dirty_total=0
  local precompile_total=0
  local rows=0
  local vector bytes state status gas
  while IFS=, read -r vector bytes state status gas; do
    [[ "$vector" == "vector" ]] && continue
    [[ -z "$vector" ]] && continue
    if [[ ! "$status" =~ ^ok ]]; then
      printf 'error: Tier-1 vector %s failed for %s: %s\n' "$vector" "$name" "$status" >&2
      return 1
    fi
    if [[ ! "$gas" =~ ^[0-9]+$ ]]; then
      printf 'error: scorer emitted invalid gas for %s/%s/%s: %s\n' \
        "$name" "$vector" "$state" "$gas" >&2
      return 1
    fi
    if [[ ! "$bytes" =~ ^[0-9]+$ ]]; then
      printf 'error: scorer emitted invalid input size for %s/%s: %s\n' \
        "$name" "$vector" "$bytes" >&2
      return 1
    fi
    case "$state" in
      clean)
        clean["$vector"]="$gas"
        clean_total=$((clean_total + gas))
        precompile_total=$((precompile_total + 60 + 12 * ((bytes + 31) / 32)))
        ;;
      dirty)
        dirty["$vector"]="$gas"
        dirty_total=$((dirty_total + gas))
        ;;
      *)
        printf 'error: scorer emitted unknown state %s\n' "$state" >&2
        return 1
        ;;
    esac
    rows=$((rows + 1))
  done <<< "$csv"

  if [[ "$rows" -ne 38 ]]; then
    printf 'error: expected 38 Tier-1 rows for %s, got %s\n' "$name" "$rows" >&2
    return 1
  fi

  local size
  size="$(canonical_hex_size "$path")"
  if [[ "$index" -eq 0 ]]; then
    reference_clean_total="$clean_total"
    reference_dirty_total="$dirty_total"
  elif [[ -z "$reference_clean_total" || -z "$reference_dirty_total" ]]; then
    printf 'error: reference gas must be measured before submissions\n' >&2
    return 1
  fi
  printf '| [%s](%s) | %s' "$name" "${implementation_links[$index]}" "$size"
  local label
  for label in "${report_labels[@]}"; do
    if [[ -z "${clean[$label]:-}" || -z "${dirty[$label]:-}" ]]; then
      printf '\nerror: scorer did not emit representative vector %s for %s\n' \
        "$label" "$name" >&2
      return 1
    fi
    printf ' | %s' "$(display_pair "${clean[$label]}" "${dirty[$label]}")"
  done
  printf ' | %s' "$(display_pair "$clean_total" "$dirty_total")"
  printf ' | %s' "$(display_ratio_pair "$clean_total" "$dirty_total" \
    "$precompile_total" "$precompile_total")"
  printf ' | %s |\n' "$(display_ratio_pair "$clean_total" "$dirty_total" \
    "$reference_clean_total" "$reference_dirty_total")"
}

cleanup_files() {
  local file
  for file in "$@"; do
    [[ -e "$file" ]] && rm -f -- "$file"
  done
}

report_proved_row() {
  local index="$1"
  local name="${implementation_names[$index]}"
  local gas_file="${gas_files[$index]}"
  local gas_module="${gas_modules[$index]}"
  local bytecode_name="${bytecode_names[$index]}"
  local schedule_name="${schedule_names[$index]}"
  local theorem_name="${schedule_theorems[$index]}"

  if [[ ! -f "$gas_file" ]]; then
    printf '| [%s](%s) | Not provided | — | — | — | — | — | — |\n' \
      "$name" "${implementation_links[$index]}"
    return
  fi

  printf 'checking proved gas schedule for %s\n' "$name" >&2
  local build_output
  if ! build_output="$(lake build "$gas_module" 2>&1)"; then
    printf 'error: gas module failed to build for %s\n%s\n' "$name" "$build_output" >&2
    return 1
  fi

  local proof_check eval_check value_check
  proof_check="$(mktemp /tmp/sha256-gas-proof.XXXXXX.lean)"
  eval_check="$(mktemp /tmp/sha256-gas-eval.XXXXXX.lean)"
  value_check="$(mktemp /tmp/sha256-gas-values.XXXXXX.lean)"
  trap 'cleanup_files "$proof_check" "$eval_check" "$value_check"; trap - RETURN' RETURN

  {
    printf 'import %s\n' "$gas_module"
    printf 'import Challenge.Sha256.AdditionalGoals.GasSchedule\n\n'
    printf 'example : Challenge.Sha256.CorrectWithSchedule %s %s := %s\n\n' \
      "$bytecode_name" "$schedule_name" "$theorem_name"
    printf '#print axioms %s\n' "$theorem_name"
  } > "$proof_check"

  local lean_output
  if ! lean_output="$(lake env lean "$proof_check" 2>&1)"; then
    printf 'error: proved gas check failed for %s\n%s\n' "$name" "$lean_output" >&2
    return 1
  fi
  if ! check_axiom_output "$theorem_name" "$lean_output"; then
    return 1
  fi

  {
    printf 'import %s\n\n' "$gas_module"
    local size
    for size in "${report_sizes[@]}"; do
      printf '#eval IO.println s!"GAS_BOUND,%s,{%s %s}"\n' \
        "$size" "$schedule_name" "$size"
    done
  } > "$eval_check"

  local eval_output
  if ! eval_output="$(lake env lean "$eval_check" 2>&1)"; then
    printf 'error: gasSchedule is not executable for %s\n%s\n' "$name" "$eval_output" >&2
    return 1
  fi

  local -A bounds=()
  local marker size value
  while IFS=, read -r marker size value; do
    [[ "$marker" == "GAS_BOUND" ]] || continue
    if [[ ! "$size" =~ ^[0-9]+$ || ! "$value" =~ ^[0-9]+$ ]]; then
      printf 'error: invalid evaluated gas bound for %s: %s,%s\n' "$name" "$size" "$value" >&2
      return 1
    fi
    bounds["$size"]="$value"
  done <<< "$eval_output"

  {
    printf 'import %s\n\n' "$gas_module"
    for size in "${report_sizes[@]}"; do
      if [[ -z "${bounds[$size]:-}" ]]; then
        printf 'error: no evaluated bound at size %s for %s\n' "$size" "$name" >&2
        return 1
      fi
      printf 'example : %s %s = %s := by decide\n' \
        "$schedule_name" "$size" "${bounds[$size]}"
    done
  } > "$value_check"
  if ! lean_output="$(lake env lean "$value_check" 2>&1)"; then
    printf 'error: evaluated gas values do not kernel-reduce for %s\n%s\n' \
      "$name" "$lean_output" >&2
    return 1
  fi

  printf '| [%s](%s) | [proved](%s)' "$name" "${implementation_links[$index]}" \
    "${gas_file#Challenge/Sha256/}"
  for size in "${report_sizes[@]}"; do
    printf ' | %s' "${bounds[$size]}"
  done
  printf ' |\n'

  cleanup_files "$proof_check" "$eval_check" "$value_check"
  trap - RETURN
}

remove_gas_fixture() {
  local fixture_dir="$1"
  rm -f -- "$fixture_dir/Bytecode.lean" "$fixture_dir/Gas.lean"
  rmdir -- "$fixture_dir"
}

run_axiom_self_test() {
  local name="GasAxiomSelfTest$$"
  local fixture_dir="$submission_root/$name"
  if [[ -e "$fixture_dir" ]]; then
    printf 'error: refusing to overwrite %s\n' "$fixture_dir" >&2
    return 1
  fi

  mkdir -p -- "$fixture_dir"
  {
    printf 'import Challenge.Sha256.Reference.Bytecode\n\n'
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def bytecode : ByteArray := Challenge.Sha256.referenceBytecode\n\n'
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$fixture_dir/Bytecode.lean"
  {
    printf 'import %s.%s.Bytecode\n' "$module_prefix" "$name"
    printf 'import Challenge.Sha256.AdditionalGoals.GasSchedule\n\n'
    printf 'namespace %s.%s\n\n' "$module_prefix" "$name"
    printf 'def gasSchedule : Nat → Nat := fun _ => 0\n\n'
    printf 'axiom gasSchedule_correct :\n'
    printf '  Challenge.Sha256.CorrectWithSchedule bytecode gasSchedule\n\n'
    printf 'end %s.%s\n' "$module_prefix" "$name"
  } > "$fixture_dir/Gas.lean"

  implementation_names=("$name")
  implementation_links=("Submissions/$name/")
  gas_files=("$fixture_dir/Gas.lean")
  gas_modules=("$module_prefix.$name.Gas")
  bytecode_names=("$module_prefix.$name.bytecode")
  schedule_names=("$module_prefix.$name.gasSchedule")
  schedule_theorems=("$module_prefix.$name.gasSchedule_correct")

  local accepted=false
  if report_proved_row 0 >/dev/null; then
    accepted=true
  fi
  remove_gas_fixture "$fixture_dir"

  if [[ "$accepted" == true ]]; then
    printf 'error: gas checker accepted its fake-axiom negative control\n' >&2
    return 1
  fi
  printf 'gas checker negative control: rejected fake proved schedule as expected\n'
}

main() {
  if [[ "${1:-}" == "--self-test" && $# -eq 1 ]]; then
    run_axiom_self_test
    return
  fi
  if [[ $# -ne 0 ]]; then
    printf 'usage: %s [--self-test]\n' "$0" >&2
    return 2
  fi
  discover_submissions

  printf '<!-- BEGIN GENERATED SHA256 GAS REPORT -->\n'
  printf '## 6. Gas report\n\n'
  printf 'Generated by `scripts/report-sha256-gas.sh`; CI checks that this section is current.\n\n'
  printf '### Category 1: Tier-1 measured gas\n\n'
  printf '%s\n' \
    'Gas is measured by concrete execution in the pinned EVM semantics. A' \
    'single number means the clean and dirty initial states agree; `clean /' \
    'dirty` is shown otherwise. The total is the sum across all 19 vectors,' \
    'all of which the script checks. Ratios compare those suite totals against' \
    'the current SHA-256 precompile schedule, `60 + 12 × ceil(bytes / 32)`, and' \
    'against the bundled reference. These measurements are tests, not proofs.'
  printf '\n'
  printf '| implementation | bytes | empty | abc | 55 bytes | 56 bytes | 64 bytes | 1,000 bytes | all vectors | vs precompile | vs reference |\n'
  printf '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n'
  local index
  for index in "${!implementation_names[@]}"; do
    report_measured_row "$index"
  done

  printf '\n### Category 2: proved input-size gas bounds\n\n'
  printf '%s\n' \
    'A proved row supplies an executable `gasSchedule n` and a kernel-checked' \
    '`CorrectWithSchedule bytecode gasSchedule` theorem, meaning the displayed' \
    'initial gas is sufficient for every input of that byte length. The table' \
    'samples the full function at representative sizes; “Not provided” is not' \
    'inferred from measurements.'
  printf '\n'
  printf '| implementation | status | 0 bytes | 3 bytes | 55 bytes | 56 bytes | 64 bytes | 1,000 bytes |\n'
  printf '|---|---|---:|---:|---:|---:|---:|---:|\n'
  for index in "${!implementation_names[@]}"; do
    report_proved_row "$index"
  done
  printf '\n'
  printf '%s\n' \
    'The reference correctness proof currently establishes that a sufficient' \
    'gas threshold exists for each concrete input. It does not yet expose the' \
    'stronger uniform function of input size required for a proved row.'
  printf '<!-- END GENERATED SHA256 GAS REPORT -->\n'
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  main "$@"
fi
