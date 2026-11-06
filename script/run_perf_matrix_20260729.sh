#!/usr/bin/env bash


########################################################
 

# bash script/run_perf_matrix_20260729.sh

########################################################


# Reproducible performance matrix for the six requested designs.  Header
# generation and driver compilation are independent and use up to 64 jobs;
# all measurements remain serialized on one explicitly selected CPU.
set -u
set -o pipefail

PROJECT_DIR="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)" || exit 1
RESULT_ROOT="${RESULT_ROOT:-$PROJECT_DIR/work-dir-cmp}"
BASE_DIR="${BASE_DIR:-}"
ESSENT_JAR="${ESSENT_JAR:-$PROJECT_DIR/utils/bin/essent.jar}"
CPP_COMPILER="${CPP_COMPILER:-${ARMOR_CXX:-clang++-12}}"

JAVA_BIN="${JAVA_BIN:-java}"
JAVA_HEAP="${JAVA_HEAP:-16G}"
PARALLEL_JOBS="${PARALLEL_JOBS:-64}"
CORE="${CORE:-40}"
RANDOM_CYCLES="${RANDOM_CYCLES:-1000000}"
RANDOM_SEED="${RANDOM_SEED:-0}"
MAX_CYCLES="${MAX_CYCLES:-100000000}"
REPETITIONS="${REPETITIONS:-5}"

FESVR_ROOT="$PROJECT_DIR/third_party/fesvr"
FESVR_INCLUDE_DIR="$FESVR_ROOT/include"
FESVR_LIBRARY="$FESVR_ROOT/build/libfesvr.a"
WORKLOAD="$PROJECT_DIR/workload/dhrystone.riscv"

GEN_MANIFEST=""
COMPILE_MANIFEST=""
RUN_MANIFEST=""
RUN_SUMMARY=""
MATRIX_LOG=""

timestamp() {
  date +"%Y-%m-%dT%H:%M:%S%z"
}

reserve_base_dir() {
  local parent stem candidate suffix=0
  if [ -n "$BASE_DIR" ]; then
    parent="$(dirname "$BASE_DIR")"
    mkdir -p "$parent" || return 1
    if ! mkdir "$BASE_DIR" 2>/dev/null; then
      printf 'error: BASE_DIR already exists or cannot be created: %s\n' "$BASE_DIR" >&2
      return 1
    fi
    return 0
  fi

  parent="$RESULT_ROOT/$(date +%Y%m%d)"
  stem="perf_matrix_$(date +%H%M%S)"
  mkdir -p "$parent" || return 1
  while :; do
    candidate="$parent/$stem"
    if [ "$suffix" -gt 0 ]; then
      candidate="${candidate}_$suffix"
    fi
    if mkdir "$candidate" 2>/dev/null; then
      BASE_DIR="$candidate"
      return 0
    fi
    if [ ! -e "$candidate" ]; then
      printf 'error: cannot create automatic BASE_DIR: %s\n' "$candidate" >&2
      return 1
    fi
    suffix=$((suffix + 1))
  done
}

initialize_output_paths() {
  GEN_MANIFEST="$BASE_DIR/generate-manifest.tsv"
  COMPILE_MANIFEST="$BASE_DIR/compile-manifest.tsv"
  RUN_MANIFEST="$BASE_DIR/run-manifest.tsv"
  RUN_SUMMARY="$BASE_DIR/run-summary.csv"
  MATRIX_LOG="$BASE_DIR/matrix.log"
}

quote_cmd() {
  printf '%q ' "$@"
}

append_log() {
  local log="$1"
  shift
  mkdir -p "$(dirname "$log")"
  printf '[%s] ' "$(timestamp)" >> "$log"
  printf "$@" >> "$log"
  printf '\n' >> "$log"
}

run_logged() {
  local stage="$1"
  local log="$2"
  shift 2
  mkdir -p "$(dirname "$log")"
  {
    printf '[%s] [%s] START\n' "$(timestamp)" "$stage"
    printf 'cwd: %s\n' "$PWD"
    printf 'command: '
    quote_cmd "$@"
    printf '\n'
  } >> "$log"

  local start_ns end_ns elapsed_ns rc
  start_ns="$(date +%s%N)"
  "$@" >> "$log" 2>&1
  rc=$?
  end_ns="$(date +%s%N)"
  elapsed_ns=$((end_ns - start_ns))
  {
    printf '[%s] [%s] END\n' "$(timestamp)" "$stage"
    printf 'exit_code: %s\n' "$rc"
    printf 'wall_ns: %s\n' "$elapsed_ns"
  } >> "$log"
  return "$rc"
}

read_top_name() {
  local fir="$1"
  if [ ! -f "$fir" ]; then
    printf 'error: FIRRTL input not found: %s\n' "$fir" >&2
    return 1
  fi
  if [ "$(head -n 1 "$fir")" = 'version https://git-lfs.github.com/spec/v1' ]; then
    printf 'error: FIRRTL input is a Git LFS pointer: %s\n' "$fir" >&2
    printf 'Fetch it with: git -C "%s" lfs pull --include="designs/%s" --exclude=""\n' \
      "$PROJECT_DIR" "$(basename "$fir")" >&2
    return 1
  fi
  awk '/^[[:space:]]*circuit[[:space:]]+/ { gsub(":", "", $2); print $2; found=1; exit }
       END { if (!found) exit 1 }' "$fir"
}

write_manifests() {
  printf 'label\tdesign\ttop\tconfig\topt\tslp_mode\tphase2\tout\tdrivers\n' > "$GEN_MANIFEST"
  printf 'label\ttop\tconfig\tdriver\tout\n' > "$COMPILE_MANIFEST"
  printf 'label\tconfig\tdriver\tout\n' > "$RUN_MANIFEST"

  local circuits=(
    'gemm|GEMM_16_16_8|random'
    'conv2d|Conv2D_16_16_8|random'
    'gemmini-full|gemmini-full-32x32mesh-1x1-all-uint8|random'
    'MediumRocket-8C|MediumRocket-8C|random,emulator_essent'
    'SmallBoom-8C|SmallBoom-8C|random,emulator_essent'
    # 'LargeBoom-8C|LargeBoom-8C|random,emulator_essent'
    # 'MegaBoom-8C|MegaBoom-8C|random,emulator_essent'
    # 'MegaBoom-8C|MegaBoom-8C|emulator_essent'
  )
  local configs=(
    'O0|O0|off|none'
    'O2_no_slp|O2|off|none'
    'O2_slp_phase1|O2|lowering|false'
    'O2_slp_phase2|O2|lowering|true'
  )

  local circuit config label design drivers top config_name opt slp_mode phase2 out driver
  for circuit in "${circuits[@]}"; do
    IFS='|' read -r label design drivers <<< "$circuit"
    if ! top="$(read_top_name "$PROJECT_DIR/designs/$design.fir")"; then
      printf 'error: unable to identify top for %s\n' "$design" >&2
      printf '[%s] unable to identify top for %s\n' "$(timestamp)" "$design" >> "$MATRIX_LOG"
      return 1
    fi
    for config in "${configs[@]}"; do
      IFS='|' read -r config_name opt slp_mode phase2 <<< "$config"
      out="$BASE_DIR/$label/$config_name"
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$label" "$design" "$top" "$config_name" "$opt" "$slp_mode" "$phase2" "$out" "$drivers" \
        >> "$GEN_MANIFEST"
      IFS=',' read -r -a driver_list <<< "$drivers"
      for driver in "${driver_list[@]}"; do
        printf '%s\t%s\t%s\t%s\t%s\n' "$label" "$top" "$config_name" "$driver" "$out" \
          >> "$COMPILE_MANIFEST"
        printf '%s\t%s\t%s\t%s\n' "$label" "$config_name" "$driver" "$out" \
          >> "$RUN_MANIFEST"
      done
    done
  done
}

generate_case() {
  local label="$1" design="$2" top="$3" config="$4" opt="$5"
  local slp_mode="$6" phase2="$7" out="$8" drivers="$9"
  local log="$out/essent.log"
  local status="$out/generate.status.log"
  local fir="$PROJECT_DIR/designs/$design.fir"
  local args=(
    "$JAVA_BIN" "-Xmx$JAVA_HEAP" -Xss128m -XX:+ExitOnOutOfMemoryError
    -cp "$ESSENT_JAR" essent.Driver "$fir" "-$opt"
    --output-dir "$out" --essent-log-level info
    --slp-mode "$slp_mode" --slp-packer ict
  )
  if [ "$phase2" != 'none' ]; then
    args+=(--slp-phase2 "$phase2")
  fi

  mkdir -p "$out"
  append_log "$status" 'generate start label=%s config=%s top=%s drivers=%s' \
    "$label" "$config" "$top" "$drivers"
  run_logged "generate_${label}_${config}" "$log" "${args[@]}"
  local rc=$?
  if [ "$rc" -eq 0 ] && [ -f "$out/$top.h" ]; then
    append_log "$status" 'generate success'
    return 0
  fi
  append_log "$status" 'generate failure rc=%s header_present=%s' "$rc" \
    "$(test -f "$out/$top.h" && echo true || echo false)"
  return 1
}

compile_random_driver() {
  local top="$1" out="$2"
  local driver_dir="$out/drivers/random"
  local source="$driver_dir/random_driver.cpp"
  mkdir -p "$driver_dir"
  run_logged 'generate_random_driver' "$driver_dir/random-driver-generate.log" \
    python3 "$PROJECT_DIR/script/gen_random_driver.py" "$out/$top.h" "$top" "$source" || return 1
  run_logged 'compile_random_driver' "$driver_dir/compile.log" \
    "$CPP_COMPILER" -O2 -std=c++20 -fbracket-depth=10240 -mbmi2 \
    "-I$out" "-I$PROJECT_DIR/include" "$source" -o "$driver_dir/random_driver"
}

compile_emulator_driver() {
  local out="$1"
  local driver_dir="$out/drivers/emulator_essent"
  mkdir -p "$driver_dir"
  run_logged 'compile_emulator_essent' "$driver_dir/compile.log" \
    "$CPP_COMPILER" -O2 -std=c++20 -fbracket-depth=10240 -mbmi2 \
    "-I$out" "-I$PROJECT_DIR/include" "-I$FESVR_INCLUDE_DIR" \
    "$PROJECT_DIR/driver/emulator_essent.cc" "$FESVR_LIBRARY" -lpthread \
    -o "$driver_dir/emulator"
}

compile_target() {
  local label="$1" top="$2" config="$3" driver="$4" out="$5"
  local status="$out/drivers/$driver/compile.status.log"
  if [ ! -f "$out/$top.h" ]; then
    append_log "$status" 'compile skipped: missing header %s' "$out/$top.h"
    return 1
  fi
  append_log "$status" 'compile start label=%s config=%s driver=%s' "$label" "$config" "$driver"
  local rc=0
  case "$driver" in
    random) compile_random_driver "$top" "$out" || rc=$? ;;
    emulator_essent) compile_emulator_driver "$out" || rc=$? ;;
    *) append_log "$status" 'compile failure: unknown driver %s' "$driver"; return 1 ;;
  esac
  append_log "$status" 'compile end rc=%s' "$rc"
  return "$rc"
}

parallel_generate() {
  local active=0 failed=0
  local label design top config opt slp_mode phase2 out drivers
  while IFS=$'\t' read -r label design top config opt slp_mode phase2 out drivers; do
    [ "$label" = 'label' ] && continue
    while [ "$active" -ge "$PARALLEL_JOBS" ]; do
      if wait -n; then :; else failed=1; fi
      active=$((active - 1))
    done
    generate_case "$label" "$design" "$top" "$config" "$opt" "$slp_mode" "$phase2" "$out" "$drivers" &
    active=$((active + 1))
  done < "$GEN_MANIFEST"
  while [ "$active" -gt 0 ]; do
    if wait -n; then :; else failed=1; fi
    active=$((active - 1))
  done
  return "$failed"
}

parallel_compile() {
  local active=0 failed=0
  local label top config driver out
  while IFS=$'\t' read -r label top config driver out; do
    [ "$label" = 'label' ] && continue
    while [ "$active" -ge "$PARALLEL_JOBS" ]; do
      if wait -n; then :; else failed=1; fi
      active=$((active - 1))
    done
    compile_target "$label" "$top" "$config" "$driver" "$out" &
    active=$((active + 1))
  done < "$COMPILE_MANIFEST"
  while [ "$active" -gt 0 ]; do
    if wait -n; then :; else failed=1; fi
    active=$((active - 1))
  done
  return "$failed"
}

run_one() {
  local repetition="$1" label="$2" config="$3" driver="$4" out="$5"
  local binary log rc start_ns end_ns elapsed_ns elapsed_seconds
  local driver_dir="$out/drivers/$driver"
  local run_dir="$out/runs/$driver"
  mkdir -p "$run_dir"
  log="$run_dir/core${CORE}_run${repetition}.log"
  case "$driver" in
    random) binary="$driver_dir/random_driver" ;;
    emulator_essent) binary="$driver_dir/emulator" ;;
    *) binary='' ;;
  esac
  if [ -z "$binary" ] || [ ! -x "$binary" ]; then
    printf '%s,%s,%s,%s,missing_binary,\n' "$repetition" "$label" "$config" "$driver" \
      >> "$RUN_SUMMARY"
    append_log "$log" 'run skipped: missing binary %s' "$binary"
    return 0
  fi

  start_ns="$(date +%s%N)"
  if [ "$driver" = random ]; then
    run_logged "run_${label}_${config}_${driver}_r${repetition}_core${CORE}" "$log" \
      taskset -c "$CORE" "$binary" "$RANDOM_CYCLES" "$RANDOM_SEED"
  else
    run_logged "run_${label}_${config}_${driver}_r${repetition}_core${CORE}" "$log" \
      taskset -c "$CORE" "$binary" -c "--max-cycles=$MAX_CYCLES" "$WORKLOAD"
  fi
  rc=$?
  end_ns="$(date +%s%N)"
  elapsed_ns=$((end_ns - start_ns))
  elapsed_seconds="$(awk -v ns="$elapsed_ns" 'BEGIN { printf "%.6f", ns / 1000000000 }')"
  printf '%s,%s,%s,%s,%s,%s\n' "$repetition" "$label" "$config" "$driver" "$rc" "$elapsed_seconds" \
    >> "$RUN_SUMMARY"
  return 0
}

run_serial() {
  local repetition label config driver out
  for repetition in $(seq 1 "$REPETITIONS"); do
    while IFS=$'\t' read -r label config driver out; do
      [ "$label" = 'label' ] && continue
      run_one "$repetition" "$label" "$config" "$driver" "$out"
    done < "$RUN_MANIFEST"
  done
}

main() {
  cd "$PROJECT_DIR" || exit 1
  reserve_base_dir || exit 1
  initialize_output_paths
  printf 'Using BASE_DIR: %s\n' "$BASE_DIR"
  printf 'repetition,design,config,driver,exit_code,wall_seconds\n' > "$RUN_SUMMARY"
  {
    printf 'started_at=%s\n' "$(timestamp)"
    printf 'base_dir=%s\n' "$BASE_DIR"
    printf 'result_root=%s\n' "$RESULT_ROOT"
    printf 'project_dir=%s\n' "$PROJECT_DIR"
    printf 'essent_jar=%s\n' "$ESSENT_JAR"
    printf 'java_heap=%s\n' "$JAVA_HEAP"
    printf 'cpp_compiler=%s\n' "$CPP_COMPILER"
    printf 'parallel_jobs=%s\n' "$PARALLEL_JOBS"
    printf 'core=%s\n' "$CORE"
    printf 'random_cycles=%s\n' "$RANDOM_CYCLES"
    printf 'random_seed=%s\n' "$RANDOM_SEED"
    printf 'max_cycles=%s\n' "$MAX_CYCLES"
    printf 'repetitions=%s\n' "$REPETITIONS"
  } > "$BASE_DIR/matrix-config.txt"
  : > "$MATRIX_LOG"
  append_log "$MATRIX_LOG" 'matrix start'

  write_manifests || exit 1

  append_log "$MATRIX_LOG" 'header generation start jobs=%s' "$PARALLEL_JOBS"
  if parallel_generate; then
    append_log "$MATRIX_LOG" 'header generation complete'
  else
    append_log "$MATRIX_LOG" 'header generation completed with failures'
  fi

  append_log "$MATRIX_LOG" 'driver compilation start jobs=%s' "$PARALLEL_JOBS"
  if parallel_compile; then
    append_log "$MATRIX_LOG" 'driver compilation complete'
  else
    append_log "$MATRIX_LOG" 'driver compilation completed with failures'
  fi

  append_log "$MATRIX_LOG" 'serialized core%s execution start repetitions=%s' "$CORE" "$REPETITIONS"
  run_serial
  append_log "$MATRIX_LOG" 'matrix complete'
}

main "$@"
