#!/usr/bin/env bash

# Run only already-successful matrix targets.  This deliberately uses a
# separate output namespace so the full matrix can later run independently
# without overwriting these early measurements.
set -u
set -o pipefail

PROJECT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)" || exit 1
BASE_DIR="${BASE_DIR:?Set BASE_DIR to an existing performance matrix directory}"
CORE="${CORE:-40}"
REPETITIONS="${REPETITIONS:-5}"
RANDOM_CYCLES="${RANDOM_CYCLES:-1000000}"
RANDOM_SEED="${RANDOM_SEED:-0}"
MAX_CYCLES="${MAX_CYCLES:-100000000}"
WORKLOAD="$PROJECT_DIR/workload/dhrystone.riscv"
FILTER_LABEL="${FILTER_LABEL:-}"
FILTER_CONFIG="${FILTER_CONFIG:-}"
FILTER_DRIVER="${FILTER_DRIVER:-}"
APPEND_SUMMARY="${APPEND_SUMMARY:-false}"
RUN_NAMESPACE="${RUN_NAMESPACE:-completed-runs}"

RUN_MANIFEST="$BASE_DIR/run-manifest.tsv"
COMPILE_MANIFEST="$BASE_DIR/compile-manifest.tsv"
SUMMARY="${SUMMARY:-$BASE_DIR/completed-run-summary.csv}"
ORCHESTRATION_LOG="${ORCHESTRATION_LOG:-$BASE_DIR/completed-runs.log}"

declare -a TARGETS=()

timestamp() {
  date +"%Y-%m-%dT%H:%M:%S%z"
}

append_log() {
  local file="$1"
  shift
  printf '[%s] ' "$(timestamp)" >> "$file"
  printf "$@" >> "$file"
  printf '\n' >> "$file"
}

compile_succeeded() {
  local out="$1" driver="$2"
  grep -q 'compile end rc=0$' "$out/drivers/$driver/compile.status.log" 2>/dev/null
}

binary_for() {
  local out="$1" driver="$2"
  case "$driver" in
    random) printf '%s\n' "$out/drivers/random/random_driver" ;;
    emulator_essent) printf '%s\n' "$out/drivers/emulator_essent/emulator" ;;
    *) return 1 ;;
  esac
}

load_targets() {
  local label top config driver out
  if [ -f "$RUN_MANIFEST" ]; then
    while IFS=$'\t' read -r label config driver out; do
      [ "$label" = label ] && continue
      TARGETS+=("$label"$'\t'"$config"$'\t'"$driver"$'\t'"$out")
    done < "$RUN_MANIFEST"
  elif [ -f "$COMPILE_MANIFEST" ]; then
    # The compile manifest contains the same run identity plus the unused top
    # name, so it is a stable fallback if the full matrix removes its run
    # manifest after entering execution.
    while IFS=$'\t' read -r label top config driver out; do
      [ "$label" = label ] && continue
      TARGETS+=("$label"$'\t'"$config"$'\t'"$driver"$'\t'"$out")
    done < "$COMPILE_MANIFEST"
  else
    printf 'missing run and compile manifests under: %s\n' "$BASE_DIR" >&2
    return 1
  fi
  [ "${#TARGETS[@]}" -gt 0 ]
}

run_one() {
  local repetition="$1" label="$2" config="$3" driver="$4" out="$5"
  local binary run_dir log start_ns end_ns elapsed_ns elapsed_seconds rc

  [ -z "$FILTER_LABEL" ] || [ "$label" = "$FILTER_LABEL" ] || return 0
  [ -z "$FILTER_CONFIG" ] || [ "$config" = "$FILTER_CONFIG" ] || return 0
  [ -z "$FILTER_DRIVER" ] || [ "$driver" = "$FILTER_DRIVER" ] || return 0

  if ! compile_succeeded "$out" "$driver"; then
    append_log "$ORCHESTRATION_LOG" 'skip label=%s config=%s driver=%s reason=compile_not_complete' \
      "$label" "$config" "$driver"
    return 0
  fi
  binary="$(binary_for "$out" "$driver")" || return 0
  if [ ! -x "$binary" ]; then
    append_log "$ORCHESTRATION_LOG" 'skip label=%s config=%s driver=%s reason=missing_binary path=%s' \
      "$label" "$config" "$driver" "$binary"
    return 0
  fi

  run_dir="$out/$RUN_NAMESPACE/$driver"
  log="$run_dir/core${CORE}_run${repetition}.log"
  mkdir -p "$run_dir"
  {
    printf '[%s] START label=%s config=%s driver=%s repetition=%s core=%s\n' \
      "$(timestamp)" "$label" "$config" "$driver" "$repetition" "$CORE"
    printf 'binary: %s\n' "$binary"
  } > "$log"

  start_ns="$(date +%s%N)"
  if [ "$driver" = random ]; then
    taskset -c "$CORE" "$binary" "$RANDOM_CYCLES" "$RANDOM_SEED" >> "$log" 2>&1
  else
    taskset -c "$CORE" "$binary" -c "--max-cycles=$MAX_CYCLES" "$WORKLOAD" >> "$log" 2>&1
  fi
  rc=$?
  end_ns="$(date +%s%N)"
  elapsed_ns=$((end_ns - start_ns))
  elapsed_seconds="$(awk -v ns="$elapsed_ns" 'BEGIN { printf "%.6f", ns / 1000000000 }')"
  {
    printf '[%s] END\n' "$(timestamp)"
    printf 'exit_code: %s\n' "$rc"
    printf 'wall_ns: %s\n' "$elapsed_ns"
    printf 'wall_seconds: %s\n' "$elapsed_seconds"
  } >> "$log"
  printf '%s,%s,%s,%s,%s,%s,%s\n' \
    "$repetition" "$label" "$config" "$driver" "$rc" "$elapsed_ns" "$elapsed_seconds" \
    >> "$SUMMARY"
  append_log "$ORCHESTRATION_LOG" 'done label=%s config=%s driver=%s repetition=%s rc=%s wall_seconds=%s' \
    "$label" "$config" "$driver" "$repetition" "$rc" "$elapsed_seconds"
}

main() {
  load_targets || exit 1
  if [ "$APPEND_SUMMARY" != true ] || [ ! -f "$SUMMARY" ]; then
    printf 'repetition,design,config,driver,exit_code,wall_ns,wall_seconds\n' > "$SUMMARY"
  fi
  if [ "$APPEND_SUMMARY" != true ]; then
    : > "$ORCHESTRATION_LOG"
  fi
  append_log "$ORCHESTRATION_LOG" 'start core=%s repetitions=%s' "$CORE" "$REPETITIONS"

  local repetition label config driver out target
  for repetition in $(seq 1 "$REPETITIONS"); do
    for target in "${TARGETS[@]}"; do
      IFS=$'\t' read -r label config driver out <<< "$target"
      run_one "$repetition" "$label" "$config" "$driver" "$out"
    done
  done
  append_log "$ORCHESTRATION_LOG" 'complete'
}

main "$@"
