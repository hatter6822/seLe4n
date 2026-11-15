#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-BP BP8.2: the one way this tree builds a kernel image for an emulated
# board, cuts the raw image QEMU boots, and runs it -- the Raspberry Pi 5 image
# on rpi5_machine's `raspi5b` (WS-RB) or the `virt` image on QEMU's `virt`.
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
#   QEMU_BOARD    the board the image is built for and booted on: `rpi5`, the
#                 Raspberry Pi 5 image on rpi5_machine's `raspi5b` (WS-RB), or
#                 `virt`, the `board_qemu_virt` image on QEMU's `virt`
#                 (default virt; a caller may also `qemu_select_board`)
#   QEMU_BIN      the emulator for `virt`  (default qemu-system-aarch64)
#   QEMU_RPI5_BIN the emulator for `rpi5`  (default: the one
#                 `scripts/setup_rpi5_machine.sh` builds at its pin)
#   QEMU_CPU      the PE model            (default cortex-a76)
#   QEMU_MEMORY   the RAM size            (default 1G)
#   REQUIRE_QEMU  1: an absent QEMU fails rather than skips
#   KERNEL_BIN    a pre-built HAL-only image to boot instead of building one,
#                 on the board QEMU_BOARD names alone (`qemu_gate_boards`)

QEMU_VIRT_BIN="${QEMU_BIN:-qemu-system-aarch64}"
QEMU_RPI5_BIN="${QEMU_RPI5_BIN:-}"
QEMU_CPU="${QEMU_CPU:-cortex-a76}"
QEMU_MEMORY="${QEMU_MEMORY:-1G}"
REQUIRE_QEMU="${REQUIRE_QEMU:-0}"
RUST_DIR="${REPO_ROOT}/rust"
RUST_TARGET="aarch64-unknown-none-softfloat"
KERNEL_BIN_NAMED="${KERNEL_BIN:-}"
QEMU_BOARD_NAMED="${QEMU_BOARD:-}"

# qemu_select_board BOARD: build for and boot on BOARD (`rpi5` or `virt`).
# Sets the emulator (QEMU_BIN), the machine the image's board is
# (QEMU_BOARD_MACHINE), the cargo board feature (QEMU_BOARD_FEATURES, empty for
# the Raspberry Pi 5, the HAL's default board) and the target directories.
#
# WS-BP BP5.1: the bare-metal image is the `sele4n-kernel` binary behind the
# `kernel_image` feature; `sele4n-hal` itself is a library and builds no file
# QEMU could boot.  Every image here builds into a target directory of its own,
# named by its board: the archive lane uploads
# `target/<target>/release/sele4n-kernel` as the Raspberry Pi 5 image, and it
# runs these lanes after packaging it, so an image built there would be
# uploaded in the board image's place.
#
# `rpi5` boots the Raspberry Pi 5 image itself -- the board the kernel ships
# for, built with no board feature -- on rpi5_machine's `raspi5b`, which enters
# at EL2 with PSCI over SMC as the Pi 5's firmware does.  `virt` boots the
# `board_qemu_virt` image (WS-BP BP8.1), whose device map and RAM base are
# QEMU `virt`'s.
# shellcheck disable=SC2034  # QEMU_BOARD_MACHINE and LEAN_TARGET_DIR are the callers'
qemu_select_board() {
    QEMU_BOARD="$1"
    case "${QEMU_BOARD}" in
        rpi5)
            QEMU_BOARD_FEATURES=""
            QEMU_BOARD_MACHINE="raspi5b"
            QEMU_BOARD_LABEL="rpi5_machine raspi5b"
            QEMU_BIN="${QEMU_RPI5_BIN}"
            ;;
        virt)
            QEMU_BOARD_FEATURES="board_qemu_virt"
            QEMU_BOARD_MACHINE="virt,gic-version=2,virtualization=on"
            QEMU_BOARD_LABEL="QEMU virt"
            QEMU_BIN="${QEMU_VIRT_BIN}"
            ;;
        *)
            echo "qemu_boot_lib.sh: unknown board: ${QEMU_BOARD} (rpi5 or virt)" >&2
            exit 2
            ;;
    esac
    HAL_TARGET_DIR="${RUST_DIR}/target/qemu-${QEMU_BOARD}"
    KERNEL_BIN_DEFAULT="${HAL_TARGET_DIR}/${RUST_TARGET}/release/sele4n-kernel"
    KERNEL_BIN="${KERNEL_BIN_NAMED:-${KERNEL_BIN_DEFAULT}}"
    LEAN_TARGET_DIR="${RUST_DIR}/target/qemu-${QEMU_BOARD}-lean"
}

# qemu_image_features BASE: BASE and the selected board's feature.
qemu_image_features() {
    if [[ -n "${QEMU_BOARD_FEATURES}" ]]; then
        echo "$1,${QEMU_BOARD_FEATURES}"
    else
        echo "$1"
    fi
}

qemu_select_board "${QEMU_BOARD:-virt}"
LEAN_ARCHIVE="${REPO_ROOT}/.lake/build/${RUST_TARGET}/libsele4n.a"
# WS-ZA ZA5.13: the allocation exerciser's archive, which the same builder
# writes.  Only the exerciser image links it; every other Lean-linked image is
# checked to define none of its symbols.
LEAN_EXERCISER_ARCHIVE="${REPO_ROOT}/.lake/build/${RUST_TARGET}/libsele4n_exerciser.a"

QEMU_TEMP_FILES=()
QEMU_TEMP_DIRS=()
qemu_cleanup() {
    if [[ "${#QEMU_TEMP_FILES[@]}" -gt 0 ]]; then
        rm -f "${QEMU_TEMP_FILES[@]}"
    fi
    if [[ "${#QEMU_TEMP_DIRS[@]}" -gt 0 ]]; then
        rm -rf "${QEMU_TEMP_DIRS[@]}"
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
    # WS-RB RB1: the Raspberry Pi 5 machine is built from the pinned
    # rpi5_machine, once per pin; a build that cannot run is an absent QEMU.
    if [[ "${QEMU_BOARD}" == "rpi5" && -z "${QEMU_BIN}" ]]; then
        log_section "META" "Resolving rpi5_machine's raspi5b (scripts/setup_rpi5_machine.sh)"
        QEMU_BIN=$("${REPO_ROOT}/scripts/setup_rpi5_machine.sh" | tail -n 1) || QEMU_BIN="rpi5_machine (scripts/setup_rpi5_machine.sh failed)"
        # Kept, so selecting the board again boots the machine resolved here.
        QEMU_RPI5_BIN="${QEMU_BIN}"
    fi
    if ! command -v "${QEMU_BIN}" &>/dev/null; then
        if [[ "${REQUIRE_QEMU}" -eq 1 ]]; then
            record_failure "META" "QEMU not found: ${QEMU_BIN} (REQUIRE_QEMU=1)"
            finalize_report
        fi
        log_section "META" "SKIP: ${QEMU_BIN} not found — QEMU tests skipped"
        if [[ "${QEMU_BOARD}" == "rpi5" ]]; then
            log_section "META" "       Build:   ./scripts/setup_rpi5_machine.sh (needs QEMU's build dependencies)"
        fi
        log_section "META" "       Install: apt install qemu-system-arm  (Debian/Ubuntu)"
        log_section "META" "       Install: brew install qemu            (macOS)"
        if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
            echo "QEMU_TESTS_SKIPPED=true" >> "${GITHUB_OUTPUT}"
        fi
        exit "${SELE4N_SKIP_EXIT:-77}"
    fi
    log_section "META" "QEMU found: $("${QEMU_BIN}" --version | head -1)"
    # WS-RB RB4: the Raspberry Pi 5 lanes also boot an SD card, written with
    # mtools and read by rpi5_machine's rpi5-boot.
    if [[ "${QEMU_BOARD}" == "rpi5" ]]; then
        local tool
        for tool in mformat mcopy; do
            if ! command -v "${tool}" &>/dev/null; then
                if [[ "${REQUIRE_QEMU}" -eq 1 ]]; then
                    record_failure "META" "${tool} not found: the SD card cannot be written (REQUIRE_QEMU=1)"
                    finalize_report
                fi
                log_section "META" "SKIP: ${tool} not found — install mtools (Debian/Ubuntu: apt install mtools)"
                exit "${SELE4N_SKIP_EXIT:-77}"
            fi
        done
    fi
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

# qemu_gate_boards LEAN: the boards a gate that boots both boards boots, in
# order, into QEMU_GATE_BOARDS -- `rpi5` (rpi5_machine's `raspi5b`) then `virt`
# (WS-RB) -- with every board's tools required before any board runs, so a
# board that cannot run (exit 77 without REQUIRE_QEMU=1) is found before a
# failure is recorded on another, never after it, where its skip would hide
# that failure.  A HAL-only image the caller named (KERNEL_BIN, LEAN 0) is one
# board's image, since the board is chosen at build time (`src/board.rs`), so
# it is booted on the board QEMU_BOARD names (`virt` when unnamed), alone.
qemu_gate_boards() {
    local lean="$1" board
    if [[ -n "${KERNEL_BIN_NAMED}" && "${lean}" -ne 1 ]]; then
        QEMU_GATE_BOARDS=("${QEMU_BOARD_NAMED:-virt}")
    else
        QEMU_GATE_BOARDS=(rpi5 virt)
    fi
    for board in "${QEMU_GATE_BOARDS[@]}"; do
        qemu_select_board "${board}"
        qemu_require_tools
    done
}

# qemu_build_image LEAN [EXERCISERS] [PROBE]: build the selected board's image -- the
# Lean-linked one when LEAN is 1, else the HAL alone; with the Tier-4 in-image
# exercisers (`smp_exercisers`, WS-BP BP8.4) when EXERCISERS is 1; with the Lean
# initialization refusal probe (`lean_init_refusal_probe`, v0.36.31) when PROBE
# is 1, which needs LEAN -- and name it in KERNEL_BIN.  A HAL-only KERNEL_BIN
# the caller named is booted as it is.
#
# Each of the four images builds into a target directory of its own (the
# reason above), and each is named by the features that build it, the board's
# feature (`qemu_select_board`; none for the Raspberry Pi 5) beside them:
#   HAL-only            kernel_image
#   Lean-linked         hw_target,kernel_image
#   + the exercisers    ...,smp_exercisers
#   + the refusal probe ...,lean_init_refusal_probe
# `qemu_require_tools` has verified cargo and the cross target, so a build
# that fails here is a failure of the tree, not of the environment.
EXERCISER_FEATURE="smp_exercisers"
PROBE_FEATURE="lean_init_refusal_probe"
qemu_build_image() {
    local lean="$1" exercisers="${2:-0}" probe="${3:-0}" build_log features target_dir label
    qemu_temp_file build_log qemu_build
    features=$(qemu_image_features "kernel_image")
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
        if [[ "${lean}" -eq 1 && ! -f "${LEAN_EXERCISER_ARCHIVE}" ]]; then
            record_failure "BUILD" "--lean-kernel needs ${LEAN_EXERCISER_ARCHIVE}; run scripts/test_lean_aarch64_archive.sh"
            finalize_report
        fi
        # Nothing here rebuilds the archive, so an image linked from one built
        # before the last Lean edit runs a kernel the tree no longer holds and
        # every reading taken from it describes that older kernel.  The
        # builder owns the provenance it wrote and decides freshness.
        if [[ "${lean}" -eq 1 ]] \
            && ! python3 "${REPO_ROOT}/scripts/build_lean_aarch64_archive.py" --check-fresh; then
            record_failure "BUILD" "--lean-kernel refuses a stale ${LEAN_ARCHIVE}; run scripts/test_lean_aarch64_archive.sh"
            finalize_report
        fi
        log_section "BUILD" "Building the ${label} kernel image for ${QEMU_BOARD_LABEL} (${features})..."
        if ! (cd "${RUST_DIR}" && cargo build --release --target "${RUST_TARGET}" -p sele4n-hal \
                --features "${features}" --bin sele4n-kernel \
                --target-dir "${target_dir}") 2>"${build_log}"; then
            tail -20 "${build_log}"
            record_failure "BUILD" "the ${label} ${QEMU_BOARD} image did not build"
            finalize_report
        fi
        # WS-ZA ZA5.13: a Lean-linked image without the exercisers is a
        # shipped kernel, so it must carry nothing of the exerciser's
        # archive: not its boot entry, its labeling or its declassification
        # policy.  The image's own symbol table decides it.
        if [[ "${lean}" -eq 1 && "${exercisers}" -ne 1 ]] \
            && ! python3 "${REPO_ROOT}/scripts/check_kernel_image.py" --exclusion-only \
                --excludes "${LEAN_EXERCISER_ARCHIVE}" "${KERNEL_BIN}"; then
            record_failure "BUILD" "the ${label} ${QEMU_BOARD} image defines symbols of ${LEAN_EXERCISER_ARCHIVE}, which only the exerciser image links"
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
            record_failure "BUILD" "the HAL-only ${QEMU_BOARD} image did not build"
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
#
# WS-RB RB4: on `raspi5b` the image is the Raspberry Pi 5 boot files' own
# `kernel8.img`, packaged and checked against the ELF by
# `scripts/rpi5_boot_files.py`, and the machine loads it, and writes the device
# tree, at the addresses their `config.txt` gives the firmware
# (`kernel-address`, `dtb-address`, `dtb-end`): the boot the lane runs is the
# one the firmware would make from those files.
qemu_cut_image() {
    local objcopy
    if [[ "${QEMU_BOARD}" == "rpi5" ]]; then
        local boot_files options
        boot_files=$(mktemp -d /tmp/qemu_rpi5_boot_XXXXXX)
        QEMU_TEMP_DIRS+=("${boot_files}")
        if ! python3 "${REPO_ROOT}/scripts/rpi5_boot_files.py" package "${KERNEL_BIN}" "${boot_files}" >/dev/null \
            || ! options=$(python3 "${REPO_ROOT}/scripts/rpi5_boot_files.py" machine-options "${boot_files}"); then
            record_failure "BUILD" "could not package the Raspberry Pi 5 boot files from ${KERNEL_BIN}"
            finalize_report
        fi
        QEMU_IMAGE="${boot_files}/kernel8.img"
        QEMU_RPI5_BOOT_FILES="${boot_files}"
        QEMU_BOARD_MACHINE="raspi5b,${options}"
        return
    fi
    objcopy=$(python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); from check_fp_simd_free_objects import rust_llvm_tool; print(rust_llvm_tool("llvm-objcopy"))' "${REPO_ROOT}/scripts")
    qemu_temp_file QEMU_IMAGE qemu_image
    if ! "${objcopy}" -O binary "${KERNEL_BIN}" "${QEMU_IMAGE}"; then
        record_failure "BUILD" "${objcopy} could not cut a raw image from ${KERNEL_BIN}"
        finalize_report
    fi
}

# qemu_rpi5_card ARMSTUB: an SD card for `raspi5b`, named in QEMU_CARD, holding
# the boot files `qemu_cut_image` packaged and the Raspberry Pi firmware's
# device tree, as a Pi 5 boots from one (WS-RB RB4).  ARMSTUB `firmware` leaves
# the firmware's own BL31 to enter the kernel (rpi5_machine stands in for it
# with QEMU's PSCI); `tf-a` names TF-A's `rpi5` BL31 as the armstub, which then
# provides PSCI itself.  `qemu_run` with QEMU_CARD set boots the card with
# rpi5_machine's `rpi5-boot`, which reads its `config.txt` as the firmware does;
# QEMU_CARD="" goes back to booting QEMU_IMAGE.
qemu_rpi5_card() {
    local machine_root tf_a=()
    machine_root=$(dirname "${QEMU_BIN}")
    case "$1" in
        firmware) ;;
        tf-a) tf_a=(--tf-a) ;;
        *) echo "qemu_boot_lib.sh: unknown armstub: $1 (firmware or tf-a)" >&2; exit 2 ;;
    esac
    qemu_temp_file QEMU_CARD qemu_rpi5_card
    if ! python3 "${REPO_ROOT}/scripts/rpi5_boot_files.py" card "${QEMU_RPI5_BOOT_FILES}" \
        "${machine_root}/firmware" "${QEMU_CARD}" "${tf_a[@]}"; then
        record_failure "BUILD" "could not write the Raspberry Pi 5 SD card"
        finalize_report
    fi
}
QEMU_CARD=""

# qemu_run LABEL LOG MACHINE SMP TIMEOUT UNTIL_FRAGMENT UNTIL_COUNT [QEMU_ARG...]:
# boot QEMU_IMAGE on MACHINE with SMP PEs, the serial console written to LOG.
# With an empty UNTIL_FRAGMENT it runs for TIMEOUT seconds; otherwise until LOG
# carries UNTIL_COUNT lines holding UNTIL_FRAGMENT, or the TIMEOUT deadline.
# Carriage returns are stripped.  Returns 1 when LOG could not be read.
#
# `-nic none`: `virt`'s default NIC is a virtio-net-pci device whose option ROM
# (`efi-virtio.rom`) ships in `ipxe-qemu`, a Recommends of `qemu-system-arm` that
# CI's `--no-install-recommends` install omits, and QEMU refuses to start when
# the ROM is missing.  The kernel drives no NIC, and `-nic none` leaves the
# device tree byte-identical (`scripts/qemu_dtb_fixture.py` asks the same).
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
        -nic none
        -kernel "${QEMU_IMAGE}"
        -serial "file:${log}"
        -monitor none
        -display none
        -no-reboot)
    if [[ -n "${QEMU_CARD}" ]]; then
        # The card names the machine, the kernel and the device tree; rpi5-boot
        # runs QEMU without a display of its own (`-nographic`).
        if [[ -n "${machine}" ]]; then
            echo "qemu_boot_lib.sh: a card boot takes its machine from the card, not ${machine}" >&2
            exit 2
        fi
        local machine_root
        machine_root=$(dirname "${QEMU_BIN}")
        qemu_cmd=(python3 "${machine_root}/rpi5-boot"
            --qemu "${QEMU_BIN}"
            --dtmerge "${machine_root}/dtmerge"
            --no-reboot
            "${QEMU_CARD}" --
            -cpu "${QEMU_CPU}"
            -smp "${smp}"
            "$@"
            -m "${QEMU_MEMORY}"
            -nic none
            -serial "file:${log}"
            -monitor none)
    fi
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
