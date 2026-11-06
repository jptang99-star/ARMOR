#!/usr/bin/env sh

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

build_fesvr() {
    FESVR_DIR="$SCRIPT_DIR/third_party/fesvr"
    SOURCE_DIR="$FESVR_DIR/src"
    INCLUDE_DIR="$FESVR_DIR/include"
    BUILD_DIR="$FESVR_DIR/build"
    OBJECT_DIR="$BUILD_DIR/obj"
    LIBRARY_PATH="$BUILD_DIR/libfesvr.a"

    # Armor requires Clang 12. Set ARMOR_CXX to an absolute Clang 12 path when
    # it is not available as clang++-12 on PATH.
    CXX="${ARMOR_CXX:-${CXX:-clang++-12}}"
    CXX_STANDARD="${ARMOR_CPP_STANDARD:-c++20}"
    # FESVR only uses this for bare payload names. Armor passes an explicit
    # workload path, so the portable default is intentionally empty.
    FESVR_PREFIX="${FESVR_PREFIX:-}"

    if ! command -v "$CXX" >/dev/null 2>&1; then
        printf 'error: Clang 12 compiler not found: %s\n' "$CXX" >&2
        printf 'set ARMOR_CXX to the path of clang++-12.\n' >&2
        exit 1
    fi

    case "$("$CXX" --version 2>&1 | sed -n '1p')" in
        *"clang version 12."*) ;;
        *)
            printf 'error: Armor requires Clang 12: %s\n' "$CXX" >&2
            exit 1
            ;;
    esac

    for required_dir in "$SOURCE_DIR" "$INCLUDE_DIR"; do
        if [ ! -d "$required_dir" ]; then
            printf 'error: required FESVR directory not found: %s\n' "$required_dir" >&2
            exit 1
        fi
    done

    if ! command -v ar >/dev/null 2>&1; then
        printf 'error: static-library archiver not found: ar\n' >&2
        exit 1
    fi

    mkdir -p "$OBJECT_DIR"

    # Upstream FESVR normally obtains this header from autotools. The
    # minimized vendored source only needs its host-endianness definition, so
    # generate it as a build artifact instead of carrying full autotools data.
    cat > "$BUILD_DIR/config.h" <<'EOF'
#ifndef ARMOR_FESVR_CONFIG_H
#define ARMOR_FESVR_CONFIG_H

#if defined(__BYTE_ORDER__) && (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__)
#define WORDS_BIGENDIAN 1
#endif

#endif
EOF

    FESVR_SOURCES='
context.cc
device.cc
dtm.cc
dummy.cc
elfloader.cc
htif.cc
htif_hexwriter.cc
htif_pthread.cc
memif.cc
option_parser.cc
rfb.cc
syscall.cc
term.cc
tsi.cc
'

    for source_name in $FESVR_SOURCES; do
        source_path="$SOURCE_DIR/$source_name"
        object_path="$OBJECT_DIR/${source_name%.cc}.o"
        if [ ! -f "$source_path" ]; then
            printf 'error: required FESVR source not found: %s\n' "$source_path" >&2
            exit 1
        fi

        "$CXX" \
            -O2 \
            -fPIC \
            "-std=$CXX_STANDARD" \
            "-DPREFIX=\"$FESVR_PREFIX\"" \
            -I"$BUILD_DIR" \
            -I"$INCLUDE_DIR" \
            -c "$source_path" \
            -o "$object_path"
    done

    ar rcs "$LIBRARY_PATH" "$OBJECT_DIR"/*.o
    printf 'built FESVR static library: %s\n' "$LIBRARY_PATH"
}

build_essent() {
    SBT_BIN="${ARMOR_SBT:-sbt}"
    ESSENT_JAR="$SCRIPT_DIR/utils/bin/essent.jar"

    if ! command -v "$SBT_BIN" >/dev/null 2>&1; then
        printf 'error: sbt not found: %s\n' "$SBT_BIN" >&2
        printf 'set ARMOR_SBT to the sbt executable path.\n' >&2
        exit 1
    fi

    mkdir -p "$(dirname "$ESSENT_JAR")"
    (
        cd "$SCRIPT_DIR"
        "$SBT_BIN" assembly
    )

    if [ ! -f "$ESSENT_JAR" ]; then
        printf 'error: Essent build did not produce: %s\n' "$ESSENT_JAR" >&2
        exit 1
    fi
    printf 'built Essent JAR: %s\n' "$ESSENT_JAR"
}

usage() {
    printf '%s\n' "Usage: $0 [all|fesvr|essent]"
}

main() {
    if [ "$#" -gt 1 ]; then
        usage >&2
        exit 1
    fi

    case "${1:-all}" in
        all)
            build_fesvr
            build_essent
            ;;
        fesvr)
            build_fesvr
            ;;
        essent)
            build_essent
            ;;
        -h|--help)
            usage
            ;;
        *)
            printf 'error: unknown build target: %s\n' "$1" >&2
            usage >&2
            exit 1
            ;;
    esac
}

main "$@"
