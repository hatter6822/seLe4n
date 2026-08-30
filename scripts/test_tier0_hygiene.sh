#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

# Scan for forbidden markers (axiom, sorry, TODO) in production proof surface.
# Lines annotated with a TPI-D* reference are explicitly tracked proof obligations
# and are excluded from this check (see AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md).
if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n -w "axiom|sorry|TODO" SeLe4n Main.lean | grep -v "TPI-D[0-9]"; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
else
  log_section "HYGIENE" "ripgrep (rg) not found; using grep fallback for marker scan."
  run_check "HYGIENE" bash -lc 'if (find SeLe4n -name "*.lean" -print0; printf "Main.lean\0") | xargs -0 grep -nwE "axiom|sorry|TODO" | grep -v "TPI-D[0-9]"; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
fi


if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n "SeLe4n\.Testing\.RuntimeContractFixtures|SeLe4n\.Testing\.runtimeContract(AcceptAll|DenyAll)" SeLe4n/Kernel; then echo "Test-only runtime contract fixtures leaked into production kernel modules (SeLe4n/Kernel)." >&2; exit 1; fi'
else
  run_check "HYGIENE" bash -lc 'if find SeLe4n/Kernel -name "*.lean" -print0 | xargs -0 grep -nE "SeLe4n\.Testing\.RuntimeContractFixtures|SeLe4n\.Testing\.runtimeContract(AcceptAll|DenyAll)"; then echo "Test-only runtime contract fixtures leaked into production kernel modules (SeLe4n/Kernel)." >&2; exit 1; fi'
fi

if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n "abbrev (DomainId|Priority|Irq|Badge|ASID|VAddr|PAddr) := Nat" SeLe4n/Prelude.lean; then echo "WS-B4 regression: remaining scalar wrappers must stay structure-based." >&2; exit 1; fi'
else
  run_check "HYGIENE" bash -lc 'if grep -nE "abbrev (DomainId|Priority|Irq|Badge|ASID|VAddr|PAddr) := Nat" SeLe4n/Prelude.lean; then echo "WS-B4 regression: remaining scalar wrappers must stay structure-based." >&2; exit 1; fi'
fi

# L-08 (WS-E1): spot-check theorem-body validation.
# Verify that sampled key preservation theorems have non-trivial proof bodies.
# A theorem is flagged if its body is only `:= by rfl`, `:= rfl`, or contains sorry.
THEOREM_CHECK_TARGETS=(
  "SeLe4n/Kernel/Scheduler/Operations/Preservation.lean"
  "SeLe4n/Kernel/Capability/Invariant/Preservation.lean"
  "SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean"
  "SeLe4n/Kernel/IPC/Invariant/Structural.lean"
  "SeLe4n/Kernel/Lifecycle/Invariant.lean"
  "SeLe4n/Kernel/Service/Invariant/Acyclicity.lean"
  "SeLe4n/Kernel/Architecture/VSpaceInvariant.lean"
  "SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean"
  "SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean"
)
if command -v python3 >/dev/null 2>&1; then
  run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_proof_depth.py" "${THEOREM_CHECK_TARGETS[@]}"
else
  log_section "HYGIENE" "python3 not found; using regex fallback for L-08 theorem-body validation."
  L08_FAIL=0
  for target in "${THEOREM_CHECK_TARGETS[@]}"; do
    if [[ ! -f "${target}" ]]; then
      continue
    fi
    if command -v rg >/dev/null 2>&1; then
      if rg -n '\bsorry\b' "${target}" | grep -v 'TPI-D[0-9]' | grep -v '^--' | grep -v '/-' | head -5 | grep -q '.'; then
        log_section "HYGIENE" "L-08 FAIL: sorry found in ${target}"
        L08_FAIL=1
      fi
      if rg -n 'theorem.*preserves.*:=\s*(by\s+)?rfl\s*$' "${target}" | head -5 | grep -q '.'; then
        log_section "HYGIENE" "L-08 FAIL: trivial rfl-only preservation theorem in ${target}"
        L08_FAIL=1
      fi
    fi
  done
  if [[ "${L08_FAIL}" -eq 1 ]]; then
    record_failure "HYGIENE" "L-08: sorry or trivial rfl-only proof found in invariant proof surface (see details above)"
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      finalize_report
    fi
  else
    log_section "HYGIENE" "L-08: theorem-body spot-check passed for invariant proof surface."
  fi
fi

# L-08 supplemental: verify that SHA-pinned GitHub Actions have not regressed to tag-only refs.
if command -v rg >/dev/null 2>&1; then
  # shellcheck disable=SC2016
  run_check "HYGIENE" bash -lc 'if rg -n "uses: [a-zA-Z]+/[a-zA-Z-]+@v[0-9]" .github/workflows/ | rg -v "@[0-9a-f]{40}"; then echo "F-14 regression: GitHub Actions must be SHA-pinned (see docs/CI_POLICY.md)." >&2; exit 1; fi'
fi

# The three CodeQL workflow invariants, each of which independently leaves the
# code-scanning merge requirement waiting for results that never arrive:
# `init`+`analyze` must both exist; every `github/codeql-action/*` reference
# must pin the same commit (`init` stamps its config with its own version and
# `analyze` rejects a config from a different one); and analyze must not be
# masked by `continue-on-error` at step or job level — masking is why the
# #858/#859 breakage went unseen.  Unconditional (no `command -v` guard): a
# gate that skips itself when a tool is absent is a gate that fails open.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_codeql_workflow_policy.py"

# ... and its witness, since a scanner that stops reaching the misconfiguration
# it exists to catch would otherwise go silent rather than loud.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_codeql_workflow_policy.py" --self-test

if command -v shellcheck >/dev/null 2>&1; then
  # AN11-F (LOW): comprehensive shell lint — covers every `.sh` under the
  # repo (currently only `scripts/`, but enforced at find-time so any
  # future shell script outside `scripts/` is caught automatically).
  # `--exclude=SC1090,SC1091` covers dynamic source paths that shellcheck
  # cannot statically resolve (e.g. user-supplied env files).
  shell_files_args=()
  while IFS= read -r f; do
    shell_files_args+=("$f")
  done < <(find scripts -type f -name "*.sh" | sort)
  if [[ "${#shell_files_args[@]}" -eq 0 ]]; then
    log_section "HYGIENE" "no .sh files found under scripts/ — skipping shellcheck"
  else
    run_check "HYGIENE" shellcheck --exclude=SC1090,SC1091 "${shell_files_args[@]}"
  fi
else
  log_section "HYGIENE" "shellcheck unavailable; optional shell lint not executed in this environment."
fi

# Website link protection: verify that all paths referenced by sele4n.org
# (hatter6822.github.io) still exist in the repository tree.  A failure here
# means a rename or deletion would produce 404s on the project website.
run_check "HYGIENE" "${SCRIPT_DIR}/check_website_links.sh"

# AH4-F: Version sync — validate all version-bearing files match lakefile.toml.
run_check "HYGIENE" "${SCRIPT_DIR}/check_version_sync.sh"

# A plan's numbering, counts and cross-references are relational data kept in
# prose.  They drifted in five consecutive cuts -- declared totals of
# 126/143/145/146/149 against the real row count, references to rows that a
# renumber had moved, and a phase whose acceptance arithmetic (46 + 4 = 49)
# could not be satisfied -- each found by review and fixed by hand.  The same
# failure mode for code is why check_version_sync.sh exists; a plan gets the
# same treatment.  Self-test first: a scanner that under-reaches fails silently.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_workstream_plan.py" --self-test
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_workstream_plan.py"

# WS-RR RR0.6: the SMP completion-phase theorem manifest.  The release-closure
# plan carried its theorem total as a hand-summed literal that ran SM8 -> SM10
# with no SM9 term, so the marker theorem and the "verify all 210 SM theorems
# land at HEAD" gate would both have certified a number computed as if a landed
# phase never happened -- and nothing would have broken when it did.  Lean now
# derives the total from per-phase entries, which stops a *count* going stale;
# it cannot see an inventory the manifest never mentions, which is exactly the
# shape that produced the defect.  This gate discovers every theorem inventory
# in the tree, over the comment-free code view, and fails when one is claimed
# by no phase, claimed twice, or claimed with a count the tree does not
# measure.  `run_check`, not `run_gate_check`: it reads the tree and has no
# legitimate skip, so "could not run" would be a defect rather than an absent
# emulator.  Self-test first, for the same reason the plan gate runs one: a
# scanner that under-reaches reports PASS, and the whole point of this gate is
# that a number nobody was checking looked fine for two minor versions.  The
# suite witnesses both directions — every defect reproduced and caught, and a
# witness surviving only inside a comment NOT discovered.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/generate_smp_theorem_manifest.py" --self-test
run_check "HYGIENE" python3 "${SCRIPT_DIR}/generate_smp_theorem_manifest.py" --check

# Every deferral cites the one register — the *Registered debt index* in
# docs/WORKSTREAM_HISTORY.md.  A comment saying "no currently-active plan file
# tracks it" is a deferral that opted out of it: self-describing and
# unfindable at once.  Keeping that true by hand did not work —
#
# (These lines name the register, which is what the gate below requires; a
# comment explaining what a check forbids must not trip the check, and citing
# the register is the same remedy every real site takes rather than an
# exemption carved out for the explanation.)
# three review rounds on the cut that built the register each found the sweep
# incomplete, every time because it matched one phrasing and the tree used
# another.  `run_prose_check`, not `run_check`: the subject genuinely IS the
# comment text, so this one must read the real tree rather than the
# comment-free code view, which would strip the very sentences it looks for.
# Self-test first, and it witnesses both directions: every phrasing the hand
# sweep missed is caught, and `currently-active ASID` — the tree's one honest
# false positive — is not.
run_prose_check "HYGIENE" python3 "${SCRIPT_DIR}/check_deferral_registration.py" --self-test
run_prose_check "HYGIENE" python3 "${SCRIPT_DIR}/check_deferral_registration.py"

# WS-SM SM8.B: no live syscall arm may reach a boot-pinned scheduler primitive.
# PR #861 review rounds 10 and 12 found this defect three times, one syscall per
# round — `.tcbResume`, `.send`, `.tcbSetPriority`/`.tcbSetMCPriority` — each
# fixed on discovery, none found by a gate.  Running the check here found three
# more (`.schedContextBind`, `.schedContextConfigure`, `.schedContextUnbind`)
# that no review round had reached.  The self-test runs first: it re-walks the
# pre-SMP operations and fails if the gate no longer detects them, so a gate
# that has lost its reach fails loudly instead of passing everything.
# MOVED TO TIER 1 (PR #861 review round 29).  This gate now detects against
# Lean's *elaborated environment* rather than the source text, which means it
# needs a built toolchain — and Tier 0 is deliberately build-free and
# toolchain-free, so the ARM64 Fast Gate lane (which runs Tier 0 alone, with no
# elan) died on `FileNotFoundError: 'lake'`.  A gate's tier has to match its
# dependencies.  Tier 1 runs on every PR through `test_fast.sh`, so enforcement
# is unchanged; see `test_tier1_build.sh`, after the builds.

# Internal-first naming: no workstream IDs, audit IDs, or phase codes in
# identifiers (CLAUDE.md).  Scans every identifier token — any visibility,
# fields, params, locals — rather than enumerating declaration forms, so
# there is no declaration syntax it can fail to think of.  Rust is held at
# zero; Lean ratchets against its grandfathered baseline.  Prose is exempt
# — cite workstreams in docstrings, not in names.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_identifier_naming.py"

# The gate above has shipped under-enforced five times, always because a
# hand-written piece of its scope was narrower than the rule, and its
# failure mode is silence.  This pins each mechanism with a check that
# provably fails against the version that lacked it.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/test_identifier_naming_gate.py"

# WS-SM SM8.B (PR #861 review round 43): the code view every source-scanning
# gate now reads.  Pinned here for the same reason as the gate above — a
# stripper that quietly stopped stripping would hand 1500 surface anchors and
# the AK7 counters raw text again, with nothing failing.  The suite checks the
# lexical cases and re-verifies over the whole tree that stripping moves no
# byte, which is what keeps `rg -n` line numbers pointing at real lines.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/lean_code_view.py" --self-test

# ... and the wiring, which fails differently: a `test_lib.sh` refactor that
# dropped the routing would leave every anchor green while 1500 of them went
# back to reading prose.  This drives `run_check` itself over a fixture whose
# symbol exists only in a comment.
run_check "HYGIENE" "${SCRIPT_DIR}/test_code_view_wiring.sh"

# ... and the acceptance-gate skip accounting, whose failure mode is the
# same shape: a sub-test that cannot run used to `exit 0`, `run_check`
# scored it PASS, and tier 4 printed "All checks passed" over fourteen
# QEMU gates that had never executed — so SM1/SM3/SM5/SM6/SM7 read as
# hardware-validated on a machine with no emulator.  A regression stays
# green by construction, so the mechanism is pinned rather than trusted:
# the suite drives `run_gate_check` over skip/pass/fail fixtures and
# re-asserts at the source that no QEMU sub-test exits 0 from a [SKIP]
# branch.
run_check "HYGIENE" "${SCRIPT_DIR}/test_gate_skip_accounting.sh"

# PR #873: the anchor set must be SATISFIABLE.  `run_check` asserts a pattern is
# present and `run_negative_check` asserts it is absent, and nothing compared the
# two — so a cut that deleted a theorem, added the negative pin forbidding its
# return, and left the original positive anchor produced a suite no tree can
# satisfy.  It surfaced only in the Full lane, several commits later, and read as
# "the invariant surface regressed" rather than "two anchors disagree".
#
# The check is static, so it belongs here in the fast lane rather than beside the
# anchors it reads: it fires on the PR that introduces the contradiction.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_anchor_consistency.py"
run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_anchor_consistency.py" --self-test

# AN10-D: AK7 cascade monotonicity gate. Reads docs/dev_history/audits/AL0_baseline.txt
# and rejects regressions on any AK7 cascade metric (raw-match site count,
# typed-helper adoption, storeObjectKindChecked adoption, sentinel guard
# coverage, AN10 regression test count).
run_check "HYGIENE" "${SCRIPT_DIR}/ak7_cascade_check_monotonic.sh"

# WS-RC R12.B (closes DEEP-ARCH-01 false positive structurally): verify
# the production/staged module partition. The gate computes the transitive
# `^import SeLe4n.` closure from `SeLe4n.lean` and from
# `Platform/Staged.lean`, and checks that the staged-only set matches
# `scripts/staged_module_allowlist.txt` exactly. Also verifies no
# "STATUS: staged" marker has leaked into a production-reachable file.
run_check "HYGIENE" "${SCRIPT_DIR}/check_production_staging_partition.sh"

# WS-RC R12.D (closes DEEP-ARCH-02 false positive structurally): verify
# every `*_fields : List StateField` definition in CrossSubsystem.lean
# has at least one consumer somewhere in the SeLe4n tree (in-file or
# out-of-file). Detects orphan metadata; file-local helpers pass.
run_check "HYGIENE" "${SCRIPT_DIR}/check_no_orphan_fields.sh"

run_check "HYGIENE" python3 -m unittest scripts.tests.test_generate_codebase_map

# WS-I1/R-03: Scenario registry validation — every fixture ID must be in the registry and vice versa.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate-registry \
  --extra-fixtures tests/fixtures/robin_hood_smoke.expected \
  tests/fixtures/two_phase_arch_smoke.expected

# AN4-A (H-02): enforce `SeLe4n.Kernel.Internal.lifecycleRetypeObject` consumer allowlist.
# The internal retype primitive bypasses `lifecyclePreRetypeCleanup` and
# `scrubObjectMemory`; production dispatch must use `lifecycleRetypeWithCleanup`.
# Any `.lean` file that references `Internal.lifecycleRetypeObject` or opens
# `SeLe4n.Kernel.Internal` must appear in `scripts/lifecycle_internal_allowlist.txt`.
run_check "HYGIENE" "${SCRIPT_DIR}/check_lifecycle_internal_allowlist.sh"

# AN7-A (H-14/PLT-M04): enforce that no consumer outside DeviceTree.lean itself
# references the deprecated legacy `findMemoryRegProperty` /
# `classifyMemoryRegion` Option-returning variants.  Callers must use the
# `Checked` variants that propagate DeviceTreeParseError / Option MemoryKind.
run_check "HYGIENE" "${SCRIPT_DIR}/check_devicetree_legacy_consumers.sh"

# AN7-B (H-15): audit every `physicalAddressWidth := N` binding so that
# platform-specific values are explicit and correct (RPi5 = 44, Sim = 52,
# defaults = 52; no `:= 48` VA/PA confusion anywhere).
run_check "HYGIENE" "${SCRIPT_DIR}/check_physical_address_width.sh"

# AN7-F (PLT-L): BCM2712 datasheet reference freshness marker.  Warns (not
# fatal) when the `BCM2712_DATASHEET_VERIFIED` marker in RPi5/Board.lean is
# older than one calendar year.
run_check "HYGIENE" "${SCRIPT_DIR}/check_bcm2712_freshness.sh"

# WS-SM SM2.D.5 (verified-lock FFI symmetry): verify the Lean side
# (`SeLe4n/Platform/FFI.lean`) and the Rust side (`ffi.rs` +
# `lock_bridge.rs`) agree on the SM2.D FFI symbol list, and that
# the SM2 theorem count constant agrees between the Lean
# `lockPrimitives.length` and Rust `LOCK_THEOREM_COUNT`.  A drift
# on either side without updating the other fails the gate.
run_check "HYGIENE" "${SCRIPT_DIR}/check_lock_ffi_symmetry.sh"

finalize_report
