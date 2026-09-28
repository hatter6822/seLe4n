#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP8.2: the one way this tree builds a kernel image for QEMU's `virt`
# machine, cuts the raw image QEMU boots, and runs it.
#
# `scripts/test_qemu.sh` (the boot lane), `scripts/test_qemu_smp_bringup.sh`
# (the four-PE bring-up gate) and, through `scripts/qemu_exerciser_lib.sh`, every
# Tier-4 exerciser gate (WS-BP BP8.4) boot the kernel, and they must boot the
# same image the same way: an image built one way here and another way there is two
# answers to "what does the kernel do under QEMU".  Sourced, never executed;
# the caller sources `test_lib.sh` first, for `log_section`, `record_failure`
# and `finalize_report`.
#
# Configuration (environment, all optional):
#   QEMU_BIN      the emulator            (default qemu-system-aarch64)
#   QEMU_CPU      the PE model            (default cortex-a76)
#   QEMU_MEMORY   the RAM size            (default 1G)
#   REQUIRE_QEMU  1: an absent QEMU fails rather than skips
#   KERNEL_BIN    a pre-built HAL-only image to boot instead of building one

QEMU_BIN="${QEMU_BIN:-qemu-system-aarch64}"
QEMU_CPU="${QEMU_CPU:-cortex-a76}"
QEMU_MEMORY="${QEMU_MEMORY:-1G}"
REQUIRE_QEMU="${REQUIRE_QEMU:-0}"
RUST_DIR="${REPO_ROOT}/rust"
RUST_TARGET="aarch64-unknown-none-softfloat"
# WS-BP BP5.1: the bare-metal image is the `sele4n-kernel` binary behind the
# `kernel_image` feature; `sele4n-hal` itself is a library and builds no file
# QEMU could boot.  WS-BP BP8.1: built for `virt` (`board_qemu_virt`).
# Both `virt` images build into target directories of their own: the archive
# lane uploads `target/<target>/release/sele4n-kernel` as the Raspberry Pi 5
# image, and it runs both bring-up modes after packaging it, so a `virt` build
# there would be uploaded in the board image's place.
HAL_TARGET_DIR="${RUST_DIR}/target/qemu-virt"
KERNEL_BIN_DEFAULT="${HAL_TARGET_DIR}/${RUST_TARGET}/release/sele4n-kernel"
KERNEL_BIN="${KERNEL_BIN:-${KERNEL_BIN_DEFAULT}}"
LEAN_TARGET_DIR="${RUST_DIR}/target/qemu-virt-lean"
LEAN_ARCHIVE="${REPO_ROOT}/.lake/build/${RUST_TARGET}/libsele4n.a"

QEMU_TEMP_FILES=()
qemu_cleanup() {
    if [[ "${#QEMU_TEMP_FILES[@]}" -gt 0 ]]; then
        rm -f "${QEMU_TEMP_FILES[@]}"
    fi
}
trap qemu_cleanup EXIT

# qemu_temp_file VAR PREFIX: a temporary file, removed on exit, named in VAR.
qemu_temp_file() {
    local path
    path=$(mktemp "/tmp/${2}_XXXXXX")
    QEMU_TEMP_FILES+=("${path}")
    printf -v "$1" '%s' "${path}"
}

# qemu_require_tools: QEMU, cargo and the cross target, or exit
# SELE4N_SKIP_EXIT (77) -- a gate that cannot run certifies nothing -- unless
# REQUIRE_QEMU=1, which makes an absent QEMU a failure.
qemu_require_tools() {
    if ! command -v "${QEMU_BIN}" &>/dev/null; then
        if [[ "${REQUIRE_QEMU}" -eq 1 ]]; then
            record_failure "META" "QEMU not found: ${QEMU_BIN} (REQUIRE_QEMU=1)"
            finalize_report
        fi
        log_section "META" "SKIP: ${QEMU_BIN} not found — QEMU tests skipped"
        log_section "META" "       Install: apt install qemu-system-arm  (Debian/Ubuntu)"
        log_section "META" "       Install: brew install qemu            (macOS)"
        if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
            echo "QEMU_TESTS_SKIPPED=true" >> "${GITHUB_OUTPUT}"
        fi
        exit "${SELE4N_SKIP_EXIT:-77}"
    fi
    log_section "META" "QEMU found: $("${QEMU_BIN}" --version | head -1)"
    if ! command -v cargo &>/dev/null; then
        log_section "META" "SKIP: cargo not found — cannot build kernel binary"
        exit "${SELE4N_SKIP_EXIT:-77}"
    fi
    if ! rustup target list --installed 2>/dev/null | grep -q "${RUST_TARGET}"; then
        log_section "BUILD" "Installing Rust target: ${RUST_TARGET}"
        rustup target add "${RUST_TARGET}" 2>/dev/null || {
            log_section "META" "SKIP: Cannot install ${RUST_TARGET} target"
            exit "${SELE4N_SKIP_EXIT:-77}"
        }
    fi
}

# qemu_build_image LEAN [EXERCISERS] [PROBE]: build the `virt` image -- the
# Lean-linked one when LEAN is 1, else the HAL alone; with the Tier-4 in-image
# exercisers (`smp_exercisers`, WS-BP BP8.4) when EXERCISERS is 1; with the Lean
# initialization refusal probe (`lean_init_refusal_probe`, v0.36.31) when PROBE
# is 1, which needs LEAN -- and name it in KERNEL_BIN.  A HAL-only KERNEL_BIN
# the caller named is booted as it is.
#
# Each of the four images builds into a target directory of its own (the
# reason above), and each is named by the features that build it:
#   HAL-only            kernel_image,board_qemu_virt
#   Lean-linked         hw_target,kernel_image,board_qemu_virt
#   + the exercisers    ...,smp_exercisers
#   + the refusal probe ...,lean_init_refusal_probe
# `qemu_require_tools` has verified cargo and the cross target, so a build
# that fails here is a failure of the tree, not of the environment.
EXERCISER_FEATURE="smp_exercisers"
PROBE_FEATURE="lean_init_refusal_probe"
qemu_build_image() {
    local lean="$1" exercisers="${2:-0}" probe="${3:-0}" build_log features target_dir label
    qemu_temp_file build_log qemu_build
    features="kernel_image,board_qemu_virt"
    target_dir="${HAL_TARGET_DIR}"
    label="HAL-only"
    if [[ "${lean}" -eq 1 ]]; then
        features="hw_target,${features}"
        target_dir="${LEAN_TARGET_DIR}"
        label="Lean-linked"
    fi
    if [[ "${exercisers}" -eq 1 ]]; then
        features="${features},${EXERCISER_FEATURE}"
        target_dir="${target_dir}-exercisers"
        label="${label} exerciser"
    fi
    if [[ "${probe}" -eq 1 ]]; then
        if [[ "${lean}" -ne 1 ]]; then
            record_failure "BUILD" "the refusal probe drives the Lean library's initialization; it needs the Lean-linked image"
            finalize_report
        fi
        features="${features},${PROBE_FEATURE}"
        target_dir="${target_dir}-init-probe"
        label="${label} refusal-probe"
    fi
    if [[ "${lean}" -eq 1 || "${exercisers}" -eq 1 ]]; then
        KERNEL_BIN="${target_dir}/${RUST_TARGET}/release/sele4n-kernel"
        # Asked for by name, so a missing archive or a failed link is a
        # failure, not a skip: the archive lane that runs the Lean mode has
        # just built both.
        if [[ "${lean}" -eq 1 && ! -f "${LEAN_ARCHIVE}" ]]; then
            record_failure "BUILD" "--lean-kernel needs ${LEAN_ARCHIVE}; run scripts/test_lean_aarch64_archive.sh"
            finalize_report
        fi
        log_section "BUILD" "Building the ${label} kernel image for QEMU virt (${features})..."
        if ! (cd "${RUST_DIR}" && cargo build --release --target "${RUST_TARGET}" -p sele4n-hal \
                --features "${features}" --bin sele4n-kernel \
                --target-dir "${target_dir}") 2>"${build_log}"; then
            tail -20 "${build_log}"
            record_failure "BUILD" "the ${label} virt image did not build"
            finalize_report
        fi
    elif [[ "${KERNEL_BIN}" == "${KERNEL_BIN_DEFAULT}" ]]; then
        log_section "BUILD" "Building the kernel image (sele4n-kernel) for ${RUST_TARGET} (${features})..."
        if ! (cd "${RUST_DIR}" && cargo build --release --target "${RUST_TARGET}" -p sele4n-hal \
                --features "${features}" --bin sele4n-kernel \
                --target-dir "${target_dir}") 2>"${build_log}"; then
            # WS-BP BP8.4: a failure, where it used to be a skip.  `qemu_require_tools`
            # has verified cargo and the cross target, so a build that fails here is
            # the tree's, and a gate that reports it NOT RUN reads a broken image as
            # an absent emulator.
            tail -20 "${build_log}"
            record_failure "BUILD" "the HAL-only virt image did not build"
            finalize_report
        fi
    else
        log_section "BUILD" "Using the kernel image named by KERNEL_BIN: ${KERNEL_BIN}"
    fi
    if [[ ! -f "${KERNEL_BIN}" ]]; then
        log_section "META" "SKIP: Kernel image not found at ${KERNEL_BIN}"
        exit "${SELE4N_SKIP_EXIT:-77}"
    fi
    log_section "BUILD" "Kernel image: $(wc -c < "${KERNEL_BIN}") bytes"
}

# qemu_cut_image: the raw image QEMU boots, named in QEMU_IMAGE.  QEMU passes
# the device tree in x0 only to an image carrying the arm64 Image header, so it
# is handed the raw binary cut from the ELF, never the ELF.
qemu_cut_image() {
    local objcopy
    objcopy=$(python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); from check_fp_simd_free_objects import rust_llvm_tool; print(rust_llvm_tool("llvm-objcopy"))' "${REPO_ROOT}/scripts")
    qemu_temp_file QEMU_IMAGE qemu_image
    if ! "${objcopy}" -O binary "${KERNEL_BIN}" "${QEMU_IMAGE}"; then
        record_failure "BUILD" "${objcopy} could not cut a raw image from ${KERNEL_BIN}"
        finalize_report
    fi
}

# qemu_run LABEL LOG MACHINE SMP TIMEOUT UNTIL_FRAGMENT UNTIL_COUNT [QEMU_ARG...]:
# boot QEMU_IMAGE on MACHINE with SMP PEs, the serial console written to LOG.
# With an empty UNTIL_FRAGMENT it runs for TIMEOUT seconds; otherwise until LOG
# carries UNTIL_COUNT lines holding UNTIL_FRAGMENT, or the TIMEOUT deadline.
# Carriage returns are stripped.  Returns 1 when LOG could not be read.
qemu_run() {
    local label="$1" log="$2" machine="$3" smp="$4" deadline="$5" until="$6" count="$7"
    shift 7
    : > "${log}"
    local qemu_cmd=("${QEMU_BIN}"
        -machine "${machine}"
        -cpu "${QEMU_CPU}"
        -smp "${smp}"
        "$@"
        -m "${QEMU_MEMORY}"
        -kernel "${QEMU_IMAGE}"
        -serial "file:${log}"
        -monitor none
        -display none
        -no-reboot)
    local status=0
    if [[ -z "${until}" ]]; then
        timeout "${deadline}" "${qemu_cmd[@]}" || true
    else
        # `grep -c` exits 1 for "no match" and above 1 for a read failure,
        # which is a gate failure rather than a count of zero.
        timeout "${deadline}" "${qemu_cmd[@]}" &
        local qemu_pid=$! waited=0 seen=0 rc
        while (( waited < deadline * 10 )); do
            rc=0
            seen=$(grep -c -F -- "${until}" "${log}") || rc=$?
            if (( rc > 1 )); then
                record_failure "TRACE" "${label}: could not read ${log}"
                status=1
                break
            fi
            (( seen >= count )) && break
            kill -0 "${qemu_pid}" 2>/dev/null || break
            sleep 0.1
            waited=$((waited + 1))
        done
        kill "${qemu_pid}" 2>/dev/null || true
        wait "${qemu_pid}" 2>/dev/null || true
        log_section "TRACE" "${label}: ${seen} of ${count} '${until}' line(s) after $((waited / 10))s"
    fi
    tr -d '\r' < "${log}" > "${log}.txt"
    mv "${log}.txt" "${log}"
    return "${status}"
}
