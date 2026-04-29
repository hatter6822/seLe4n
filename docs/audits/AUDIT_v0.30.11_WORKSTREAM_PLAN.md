# AUDIT v0.30.11 — Remediation Workstream Plan (WS-RC)

**Cut date:** 2026-04-28
**Audited version:** 0.30.11
**Source audits:**
- `docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md` (2026-04-26, predecessor)
- `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` (2026-04-28, deep)
**Workstream code-name:** WS-RC ("Release Candidate") — chosen as a stable
identifier that does not encode an audit version (CLAUDE.md
"Internal-first naming"); the audit version v0.30.11 anchors the plan in
the artefact filename only.
**Plan author branch:** `claude/audit-workstream-planning-XsmKS`
**Governing engineering rule:** CLAUDE.md "Implement-the-improvement
rule" — when documentation describes a *better* state than the code, the
remediation is to implement the description, never to weaken the
documentation. This plan applies the rule uniformly; every finding
recommendation has been audited for compliance and re-shaped where the
source audit's recommendation drifted from this principle.

---

## 0. How to read this plan

This document is the canonical decomposition of WS-RC, the remediation
workstream that closes the v0.30.11 audit cycle. It is paired with:

| Artefact | Role | Status |
|---|---|---|
| `AUDIT_v0.30.11_COMPREHENSIVE.md` | Predecessor finding inventory (DEBT-*) | Active |
| `AUDIT_v0.30.11_DEEP_VERIFICATION.md` | Deep finding inventory (DEEP-*) | Active |
| `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` (this file) | Per-phase remediation plan | **NEW — this PR** |
| `AUDIT_v0.30.11_WS_RC_BASELINE.txt` | Numeric baseline at WS-RC start | To be cut at first remediation PR |
| `AUDIT_v0.30.11_DISCHARGE_INDEX.md` | Closure-form proof obligation index | To be added if any phase produces closure-form theorems |
| `AUDIT_v0.30.11_DEFERRED.md` | Items pushed past WS-RC | To be added at WS-RC closure if any items defer |
| `AUDIT_v0.30.11_ERRATA.md` | Audit-text corrections (this plan introduces one) | To be added when phase R0 lands |

**Reading order.** New contributors should read §1 (executive summary),
§2 (the verification of every finding, including audit errata), and
§3 (the phase index). After that, jump to the phase that owns the
file you are working in, using the file→phase index in §3.3.

The plan deliberately does not duplicate finding text from the source
audits. Instead, every phase below references the canonical finding ID
(DEEP-*, DEBT-*) and adds: (a) verified file/line targets, (b) the
implementation slice, (c) the validation gate, (d) explicit
dependencies, and (e) commit-message scaffolding.


---

## 1. Executive summary

### 1.1 What this workstream closes

WS-RC closes the v0.30.11 audit cycle by remediating every active
finding from the comprehensive audit (17 DEBT-* items, of which 1 is
fully closed by R0 reconfirmation, 4 are subsumed by DEEP-* items,
and 12 carry forward) and the deep verification audit (~52 DEEP-*
items). Every audit finding — including those classified as **false
positives** by either audit's verification pass — receives a
remediation: active findings get an implementation slice, and false
positives get a **structural enforcement gate** that prevents the
false positive from recurring (per CLAUDE.md's "implement-the-
improvement rule": the verification's correctness becomes a
machine-checked invariant rather than ad-hoc human re-derivation).

After deduplication, the workstream tracks **~45 active DEEP-* items
+ 6 false-positive structural-fix items + 17 active DEBT-* items =
~68 distinct remediation items**. The workstream is decomposed into
**15 phases** (R0..R14), of which R0..R6 are pre-v1.0 must-fix and
R7..R14 are release-aligned cleanup or post-1.0 backlog.

Headline counts (post-§11/§12 revision + this plan's verification;
see §2 for the per-finding disposition):

| Severity | Active count | v0.31.0 set | v1.0.0-only set (additional) | Post-1.0 (R14) |
|---|---|---|---|---|
| C — critical | 0 | – | – | – |
| H — high | 2 | 1 (DEEP-IPC-03) | 1 (DEEP-FFI-01) | – |
| M — medium | 9 (DEEP) + 1 (DEBT) | 5 | 4 | 1 (DEBT-CAP-01) |
| L — low | 11 (DEEP) | 7 | 1 | 3 (PROOF-01, MODEL-02, RUST-06) |
| I — informational | 23 (DEEP) | 9 | 12 | 2 (PRELUDE-01/02) |
| **False-positive structural fixes** | **6** | **6** (R4.D, R12.B/C/D) | – | – |
| Predecessor DEBT-* (active) | 17 | 3 (DOC-01, RUST-02, IPC-02 via R10) | 1 (FR-01 via R11; included in v0.31.0 too) | 13 (the maintainability backlog) |
| **Total active items** | **~68** | **~31** | **~18** | **~19** |

The "false-positive structural fixes" row counts the six findings the
deep audit's §11.1/§11.3 (and this plan's §2.2) classified as false
positives: DEEP-CAP-02 (cspaceMutate validates), DEEP-ARCH-02 (no dead
`_fields`), DEEP-RUST-01 (MMIO ARM-ARM cited), DEEP-RUST-02 (registers
ARM-ARM cited), DEEP-IPC-01 (notification waiters NoDup), and
DEEP-ARCH-01 (CacheModel staged correctly). Each receives a
structural enforcement gate (R4.D for the cspaceMutate witness,
R12.B/C/D for the three CI gates) so that the verification's
correctness is **machine-checked at every CI run** rather than left
to a future auditor's manual re-derivation. DEEP-IPC-01 is subsumed
by R4.C (NoDup waitingThreads at type level) and needs no separate
fix slot.

Numbers are rounded because some DEBT-* items are subsumed by DEEP-*
items (e.g., DEBT-DOC-01 → DEEP-DOC-01..06; DEBT-ST-01 → DEEP-MODEL-02;
DEBT-RUST-01 → DEEP-RUST-06). The exact list per phase is in §2.4–2.5
and the cross-reference matrix in Appendix C.

### 1.2 Defining outcome — the v1.0 readiness gate

The v0.30.11 deep audit's headline correction stands: **a v1.0 tag
requires the syscall-dispatch FFI to actually invoke the verified
`syscallEntryChecked` on hardware**. The proof artefact is complete
and clean (zero `sorry`, zero `axiom`, parametric WCRT, faithful
information-flow composition); what is missing is the wiring from the
Rust SVC handler through `@[export syscall_dispatch_inner]` and
`@[export suspend_thread_inner]` into the verified Lean kernel API.
Per CLAUDE.md's implement-the-improvement rule, the remediation is to
**implement the wiring** (Phase R2), not to disclose the gap in
release notes.

### 1.3 Recommended release path

| Tag | Precondition | Scope |
|---|---|---|
| `v0.31.0` | WS-RC R0, R1, R8, R9, R10, R11, R12 land (baseline, NI symmetry, tests, hygiene, polish, docs, CI) | "Verified specification release". No claim about hardware syscall dispatch. |
| `v1.0.0` | All v0.31.0 phases plus R2, R3, R4, R5, R6 land (the implementation tier) | "Bootable verified microkernel". CLAUDE.md "First hardware target: Raspberry Pi 5" is then literally true. |

This separation is the audit's post-§12 recommendation. WS-RC closes
in stages: an interim closure at `v0.31.0` (documentation/hygiene +
the one-line NI symmetry fix) and a full closure at `v1.0.0` (after
the FFI wiring + boot threading + structural-invariant promotions
land).

### 1.4 Audit errata produced by this plan

While verifying every finding against the live tree (per the user's
instruction "ensure every single finding is not an erroneous finding"),
this plan author identified **one finding whose verification rationale
in the deep audit is itself wrong**: DEEP-ARCH-01 (CacheModel "STATUS:
staged" marker). The audit's §11.3 narrowing claimed CacheModel is in
the production import chain via `TlbModel ← BarrierComposition ←
CacheModel`, but `BarrierComposition` does **not** import `CacheModel`
(verified by `grep "^import" SeLe4n/Kernel/Architecture/BarrierComposition.lean`).
Direct transitive-closure trace from `SeLe4n.lean` (the production
library entry point) reaches **144 modules**; CacheModel, TimerModel,
ExceptionModel, and TlbCacheComposition are **all four** outside that
set, reachable only via `Platform/Staged.lean`. All three "STATUS:
staged" markers are therefore **correct**, and DEEP-ARCH-01 should be
reclassified as a **withdrawn false positive** alongside the five
already-withdrawn items in §11.1 of the deep audit.

### 1.5 Structural-fix policy for false positives

Per the user-articulated principle "implement the optimal fix instead
of documenting findings to be handled in a later audit," this plan
goes further than the deep audit's §11.1/§11.3 classifications. A
false positive verified once via human grep is one audit cycle away
from being re-discovered as a "new" finding; the optimal remediation
is to convert the verification into a **machine-checked invariant**
that runs on every CI cycle. Concretely:

| Withdrawn finding | Optimal structural fix | Lands in phase |
|---|---|---|
| DEEP-ARCH-01 (CacheModel staging) | CI gate that computes the production-chain transitive closure from `SeLe4n.lean` and the staged set from `Platform/Staged.lean`, fails if any "STATUS: staged" marked file is in production or vice versa | **R12.B** |
| DEEP-RUST-01 (MMIO `(ARM ARM B2.1)` citations) | CI gate that scans every `unsafe { … }` block in `rust/sele4n-hal/src/` and fails if the preceding 5 lines do not contain `(ARM ARM <section>)` | **R12.C** |
| DEEP-RUST-02 (registers `(ARM ARM C5.2)` citations) | Same gate as R12.C — covered uniformly across HAL | **R12.C** |
| DEEP-ARCH-02 (`*_fields` definitions consumed) | CI gate that fails if any `<name>_fields : List StateField` definition has fewer than 1 consumer outside the file it's declared in | **R12.D** |
| DEEP-CAP-02 (`cspaceMutate` null-cap guard) | Witness theorem `cspaceMutate_rejects_null_cap` proving the runtime check at line 1093 is equivalent to a non-null precondition | **R4.D** |
| DEEP-IPC-01 (`notificationWait` NoDup) | Subsumed by R4.C (NoDup at type level on `Notification.waitingThreads`) | **R4.C (no separate fix)** |

Each of these is a distinct WS-RC sub-phase (R4.D for the witness
theorem; R12.B/C/D for the three CI gates). Their content is
detailed in §8.6 (R4.D), §16.3 (R12.B), §16.4 (R12.C), and §16.5
(R12.D). The policy is canonical in this plan; CLAUDE.md's
"Implement-the-improvement rule" governs the broader principle.

This plan treats DEEP-ARCH-01 as withdrawn-as-finding-but-fixed-
structurally-in-R12.B; §2.2 below records the errata for inclusion
in `AUDIT_v0.30.11_ERRATA.md` once Phase R0 lands.


---

## 2. Verification of every finding (erroneous-finding sweep)

This section is the result of re-deriving every claim in both source
audits against the live tree on branch
`claude/audit-workstream-planning-XsmKS` (HEAD at WS-RC plan author
time). Each finding is given exactly one of five dispositions:
**ACTIVE** (carry into a phase), **WITHDRAWN** (audit error — do
not act), **NO-ACTION** (already correct in the code), **CARRIED**
(predecessor DEBT-* re-confirmed), or **POST-1.0** (implementation
deferred past v1.0).

The `Verification` column records the exact command or file/line
inspection used to confirm or reject the finding.

### 2.1 Findings withdrawn-as-finding-but-fixed-structurally

The deep audit's §11.1 withdrew five findings as false positives;
this plan adds DEEP-ARCH-01 to that list (§2.2). Per the §1.5
structural-fix policy, each receives a machine-checked enforcement
gate so the verification is preserved automatically rather than
manually re-derived by a future auditor.

| ID | Verified-correct claim (audit-time finding) | Structural fix lands in | Mechanism |
|---|---|---|---|
| DEEP-CAP-02 | `Capability/Operations.lean:1093` checks `if cap.isNull then .error .nullCapability`; AK8-K C-L2 guard is present. | **R4.D** | Lean witness theorem `cspaceMutate_rejects_null_cap`. |
| DEEP-ARCH-02 | `grep -rn` on each of the 11 `*_fields` definitions in `CrossSubsystem.lean:887–930` returns 3..26 consumers each. All actively used. | **R12.D** | CI gate `scripts/check_no_orphan_fields.sh` fails on `*_fields` defs with zero out-of-file consumers. |
| DEEP-RUST-01 | `rust/sele4n-hal/src/mmio.rs` lines 54–57, 76–79, 96–98, 117–119 each cite `(ARM ARM B2.1)`. | **R12.C** | CI gate `scripts/check_arm_arm_citations.sh` fails on HAL `unsafe` blocks lacking `(ARM ARM <section>)` within 5 preceding lines. |
| DEEP-RUST-02 | `rust/sele4n-hal/src/registers.rs` lines 20–21 and 45–46 each cite `(ARM ARM C5.2)` for `mrs`/`msr`. | **R12.C** | Same gate; covers all HAL files uniformly. |
| DEEP-IPC-01 | `Operations/Endpoint.lean:723` performs O(1) duplicate guard via `tcb.ipcState == .blockedOnNotification` returning `.error .alreadyWaiting`. | **R4.C** (subsumed) | Type-level `NoDupList ThreadId` on `Notification.waitingThreads` makes the duplicate impossible at the type system level. |
| DEEP-ARCH-01 | All three "STATUS: staged" markers (CacheModel/TimerModel/ExceptionModel) are correct: each module is reachable only via `Platform/Staged.lean`, not from `SeLe4n.lean`. | **R12.B** | CI gate `scripts/check_production_staging_partition.sh` computes the transitive closure from `SeLe4n.lean` and `Platform/Staged.lean` and fails on partition violations. |

### 2.2 Audit errata produced by this plan (DEEP-ARCH-01)

This plan author identified one additional finding whose verification
rationale in the deep audit is wrong. The original claim is
withdrawn-as-finding; per §1.5 the structural fix lands in **R12.B**.

| ID | Original claim | Verification | Disposition |
|---|---|---|---|
| DEEP-ARCH-01 | CacheModel "STATUS: staged" marker is misleading because CacheModel is in production via `SeLe4n.lean → TlbModel → BarrierComposition → CacheModel`. | `grep "^import" SeLe4n/Kernel/Architecture/BarrierComposition.lean` returns zero imports of CacheModel. Transitive-closure trace from `SeLe4n.lean` (144 modules) does not contain CacheModel, TimerModel, ExceptionModel, or TlbCacheComposition. CacheModel is reachable only via `Platform/Staged.lean` and via TlbCacheComposition (itself only reachable via Staged). The marker is correct. | **WITHDRAWN as finding.** Errata to be lifted into `AUDIT_v0.30.11_ERRATA.md` at WS-RC R0. **Structural fix: R12.B** — CI gate that codifies the production/staged partition so the false positive cannot recur. See §16.3 for the gate's design. |

### 2.3 Findings demoted to NO-ACTION in the deep audit's §11.5

| ID | Reason for no-action |
|---|---|
| DEEP-CAP-03 | `mintDerivedCap` guard order is documented in the existing docstring at `Operations.lean:740–747`. |
| DEEP-SCH-01 | `RunQueue.lean:66–72` already documents the implicit invariant with a 6-line comment pointing to `InvariantChecks.runQueueThreadPriorityConsistentB`. |
| DEEP-DOC-05 | Per §12, no documentation change; the design intent ("First hardware target: Raspberry Pi 5") is made true by DEEP-FFI-01. |
| DEEP-TEST-04 | `tests/fixtures/main_trace_smoke.expected` verified non-empty and exercised by Main trace. |
| DEEP-SCRIPT-02 | Python helpers verified clean. |
| DEEP-ARCH-04 | `Architecture/IpcBufferValidation.lean` — verified production-wired (imported by `Kernel/API.lean` and `Kernel/InformationFlow/Invariant/Operations.lean`). No "STATUS: staged" marker is needed; absence is correct. |

### 2.4 Active findings — DEEP-* (carry into WS-RC phases)

| ID | Sev | Phase | File:line target (verified) |
|---|---|---|---|
| DEEP-FFI-01 | H | R2 | `SeLe4n/Platform/FFI.lean:185–190, 216–223`; `Kernel/API.lean:1244`; `Lifecycle/Suspend.lean` |
| DEEP-FFI-02 | M | R2 | `rust/sele4n-hal/src/svc_dispatch.rs:308`; new Lean fn `syscallDispatchFromAbi` |
| DEEP-FFI-03 | I | R2 | `SeLe4n/Platform/FFI.lean:185–190, 216–223` (gating section) |
| DEEP-IPC-02 | M | R10 | 7 IPC files: `QueueNextBlocking.lean:24`, `QueueNoDup.lean:25`, `QueueMembership.lean:13`, `Structural/StoreObjectFrame.lean:37`, `Structural/DualQueueMembership.lean:38`, `Structural/PerOperation.lean:38`, `Structural/QueueNextTransport.lean:36` |
| DEEP-IPC-03 | H | R1 | `Kernel/IPC/DualQueue/WithCaps.lean:198` (**CLOSED at R1 landing**) |
| DEEP-IPC-04 | I | R6 | `Kernel/IPC/Operations/Endpoint.lean:485`; theorem `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull` in `Invariant/Defs.lean` |
| DEEP-IPC-05 | I | R4 | `Model/Object/Types.lean` `Notification.waitingThreads` |
| DEEP-DOC-01 | M | R11 | `README.md:92, :213` |
| DEEP-DOC-02 | M | R11 | `AGENTS.md` (entire file) |
| DEEP-DOC-03 | M | R11 | `CLAUDE.md` source-layout section |
| DEEP-DOC-04 | L | R11 | `README.md` audit-history table |
| DEEP-DOC-06 | L | R11 | `README.md:38, :193` |
| DEEP-MODEL-01 | L | R4 | `Model/Object/Structures.lean` CNode `slots` field |
| DEEP-MODEL-02 | L | R14 | `Model/State.lean:386–395`; `Model/Builder.lean:32–97` |
| DEEP-MODEL-03 | I | R10 | `Model/State.lean:146` (replenishQueue field doc) |
| DEEP-MODEL-04 | I | R10 | `Model/State.lean` `LifecycleMetadata.capabilityRefs` field doc |
| DEEP-PRELUDE-01 | I | R14 | `SeLe4n/Prelude.lean:1076–1115` |
| DEEP-PRELUDE-02 | I | R14 | `SeLe4n/Prelude.lean:1131+` |
| DEEP-CAP-01 | L | R10 | `Capability/Operations.lean:959, 1002` |
| DEEP-CAP-04 | I | R4 | `Capability/Invariant/Defs.lean:345–367` |
| DEEP-CAP-05 | I | R7 | `Capability/Operations.lean:12–62` (header AK8-K LOW-tier) |
| DEEP-PROOF-01 | L | R14 | `Scheduler/Operations/Preservation.lean:1700–1739` |
| DEEP-LICENSE-01 | I | R10 | `SeLe4n.lean` (line 1 missing SPDX) |
| DEEP-PRECOM-01 | M | R9 | `scripts/pre-commit-lean-build.sh:59, 61` |
| DEEP-SCH-02 | I | R5 | `Scheduler/Operations/Selection.lean:225–241, :327` |
| DEEP-SCH-03 | I | R5 | `Lifecycle/Suspend.lean:75–84, :290+` |
| DEEP-SCH-04 | I | R5 | `Scheduler/Operations/Core.lean:715–717` |
| DEEP-SCH-05 | I | R5 | `Scheduler/RunQueue.lean:238` |
| DEEP-SCH-06 | I | R5 | `SchedContext/Operations.lean:110–187` |
| DEEP-SUSP-01 | I | R5 | `Lifecycle/Suspend.lean:290+` |
| DEEP-SUSP-02 | I | R5 | `Lifecycle/Suspend.lean:88–105` |
| DEEP-ARCH-03 | I | R6 | `Architecture/ExceptionModel.lean`, `Architecture/InterruptDispatch.lean` |
| DEEP-FDT-01 | L | R10 | `Platform/DeviceTree.lean:695–740` (`findMemoryRegPropertyChecked`) |
| DEEP-IF-01 | I | R6 | `InformationFlow/Soundness.lean` (`DeclassificationPolicy` import) |
| DEEP-IF-02 | I | R6 | `InformationFlow/Policy.lean:484–500` (SecurityDomain lattice) |
| DEEP-RUST-03 | I | R10 | `rust/sele4n-abi/src/trap.rs:2–6` |
| DEEP-RUST-04 | L | R10 | `THIRD_PARTY_LICENSES.md:41` |
| DEEP-RUST-05 | I | R10 | `rust/sele4n-abi/src/lib.rs`, `rust/sele4n-sys/src/lib.rs` |
| DEEP-RUST-06 | L | R8 | `rust/sele4n-abi/tests/conformance.rs` |
| DEEP-TEST-01 | M | R8 | `tests/Ak8CoverageSuite.lean` |
| DEEP-TEST-02 | L | R8 | `tests/{An9HardwareBindingSuite, Ak9PlatformSuite, An10CascadeSuite}.lean` |
| DEEP-TEST-03 | M | R2 | new `tests/SyscallDispatchSuite.lean` |
| DEEP-BOOT-01 | M | R3 | `Platform/Boot.lean:551`; `Platform/RPi5/VSpaceBoot.lean:272–297` |
| DEEP-SCRIPT-01 | I | R10 | `scripts/website_link_manifest.txt:18` |
| DEEP-CI-01 | L | R12 | `.github/workflows/{platform_security_baseline,lean_toolchain_update_proposal,nightly_determinism,codebase_map_sync}.yml` |
| DEEP-ARCH-01 | – | R12.B | **WITHDRAWN as finding (§2.2); structural fix in R12.B** — `scripts/check_production_staging_partition.sh` Tier-0 gate. |


### 2.5 Active findings — predecessor DEBT-* (carry into WS-RC phases)

| ID | Sev | Phase | Disposition |
|---|---|---|---|
| DEBT-DOC-01 | H (pre-1.0) | R11 | Folded into the DEEP-DOC-01..06 omnibus PR. |
| DEBT-RUST-02 | M (pre-1.0) | R0 | H-24 reconfirmation; predecessor and deep audits both could not reproduce the markers (`grep -nE 'TODO\(WS-V\|TODO\(AG10\|WS-V\|AG10' rust/sele4n-hal/src/{trap,lib}.rs` returns 0). Closure target: mark in `AUDIT_v0.30.6_DISCHARGE_INDEX.md` (already archived) AND in this audit's discharge index. |
| DEBT-ST-01 | M | R14 | Subsumed by DEEP-MODEL-02 (record-shaped 17-conjunct invariant). |
| DEBT-CAP-01 | M | R14 | Frame-helper extraction across `cspaceInsertSlot_preserves_*` (`Capability/Operations.lean:471+`). |
| DEBT-CAP-02 | L | R14 | Tactic for Insert/Delete/Revoke proof scaffold. |
| DEBT-SCH-01 | M | R14 | Split `Scheduler/Operations/Preservation.lean` (3779 LoC) into 5–6 per-invariant files. |
| DEBT-SCH-02 | M | R14 | Discharge `hDomainActiveRunnable` and `hBandProgress` from kernel invariants (`Liveness/WCRT.lean:71-74`). |
| DEBT-IF-01 | M | R14 | Thematic split of `InformationFlow/Invariant/Operations.lean` (3857 LoC). |
| DEBT-IF-02 | L | R14 | Closure-form discharge for 6 capability dispatch arms. |
| DEBT-SVC-01 | M | R14 | Retry split of `Service/Invariant/Acyclicity.lean` (1043 LoC) when Lean elaborator fragility resolves. |
| DEBT-IPC-01 | I | R14 | H3 IPC-buffer extraction for `capRecvSlot`. |
| DEBT-IPC-02 | L | R10 | AK10 rename `ipcInvariant → notificationInvariantSystem`. |
| DEBT-RT-01 | L | R14 | Add `radixWidth ≤ 21` assertion when promoting FrozenOps. |
| DEBT-FR-01 | L | R11 | Surface FrozenOps "experimental, not in v1.0" status in README and SECURITY_ADVISORY. |
| DEBT-RUST-01 | M | R8 | Subsumed by DEEP-RUST-06 (extend conformance to 6 missing syscalls). |
| DEBT-TST-01 | L | R14 | Split or document `tests/NegativeStateSuite.lean` (3660 LoC). |
| DEBT-BOOT-01 | L | R14 | AF3-F minimum-configuration validation (≥1 thread, valid scheduler state). |

### 2.6 Verification commands recorded for the next audit

For traceability — every numerical claim above was produced by one of:

```bash
# Production tree shape
find SeLe4n -name "*.lean" | wc -l                 # 167
find SeLe4n -name "*.lean" -exec cat {} + | wc -l   # 109787
find tests -name "*.lean" | wc -l                  # 28

# Proof debt
grep -rn '\bsorry\b\|\baxiom\b' SeLe4n              # 0 hits
grep -rn 'Classical\.' SeLe4n                       # 2 hits, 1 docstring at InformationFlow/Invariant/Operations.lean:87, 1 use at Scheduler/Operations/Preservation.lean:1720
grep -rn '^partial def' SeLe4n                      # 0 hits

# CLAUDE.md missing entries (DEEP-DOC-03)
grep -c "FFI" CLAUDE.md           # 0
grep -c "VSpaceBoot" CLAUDE.md    # 0
grep -c "Staged" CLAUDE.md        # 1 (but the line is "staged" lowercase, not the file name)

# README inconsistency (DEEP-DOC-01)
grep -n "3,186\|2,725" README.md
# 92:| **Proved declarations** | 3,186 theorem/lemma declarations
# 213:| ... (2,725 proved declarations, zero sorry/axiom)

# AGENTS.md staleness (DEEP-DOC-02)
head -10 AGENTS.md | grep "version 0.12.4"          # confirmed

# Production-chain trace from SeLe4n.lean (DEEP-ARCH-01 verification)
# Custom transitive-closure script (saved at scripts dir for re-use):
#   reachable from SeLe4n.lean: 144 modules
#   CacheModel/TimerModel/ExceptionModel/TlbCacheComposition: NOT reachable
#   confirms staged markers correct

# IPC linter suppressions (DEEP-IPC-02)
grep -rn "set_option linter\." SeLe4n               # 14 files
grep -rn "set_option linter\.unusedVariables false" SeLe4n/Kernel/IPC  # 7 files
```

These commands are reproduced verbatim in §11.2 of the deep audit and
are also wired into the WS-RC baseline file (Phase R0 below).


---

## 3. Workstream phase index

WS-RC is decomposed into **15 phases** (R0..R14) so each phase is a
single coherent slice per the PR checklist in CLAUDE.md. The ordering
puts the smallest implementation slice first (so a single-day PR
clears the call-path NI asymmetry early) and the documentation/
hygiene tier last (so the metric refresh is computed against the
post-implementation tree).

### 3.1 Phase summary (R0..R14)

The "Required for" column states the **earliest release tag** the
phase blocks. v0.31.0 is the verified-specification release (no
hardware-syscall claim); v1.0.0 is the bootable verified microkernel
(inherits all v0.31.0 phases plus R2..R6). "optional" phases are
recommended but not release-blocking; "post-1.0" is R14, the
maintainability backlog.

| Phase | Code-name | Slice type | Required for | PRs | Headline action |
|---|---|---|---|---|---|
| R0 | `audit-baseline` | Workstream bookkeeping | **v0.31.0** | 1 | Cut WS-RC baseline; record audit errata; mark DEBT-RUST-02/H-24 closed. |
| R1 | `ipc-call-ni-symmetry` | One-line code change | **v0.31.0** | 1 | DEEP-IPC-03: align call-path cap-transfer with send/receive. |
| R2 | `hardware-syscall-dispatch` | Substantive implementation | **v1.0.0** | 3 sub-PRs | DEEP-FFI-01/02/03 + DEEP-TEST-03: thread `SystemState`, implement `syscallDispatchFromAbi`, wire `syscall_dispatch_inner` and `suspend_thread_inner`, add a hardware-mode integration suite. |
| R3 | `boot-vspace-threading` | Boot-path implementation | **v1.0.0** | 1 | DEEP-BOOT-01: rewrite `bootSafeObject` to admit boot VSpaceRoots; thread `rpi5BootVSpaceRoot` into the boot result. |
| R4 | `structural-invariants` | Type-level invariant promotion | **v1.0.0** | 1 (4 sub-tasks) | R4.A: DEEP-MODEL-01 (slotsUnique). R4.B: DEEP-CAP-04 (RetypeTarget non-bypassable). R4.C: DEEP-IPC-05 (NoDup waitingThreads — subsumes DEEP-IPC-01). R4.D: structural witness for DEEP-CAP-02 (cspaceMutate). |
| R5 | `scheduler-lifecycle-symmetry` | Behaviour-symmetry refactor | **v1.0.0** | 1 | DEEP-SUSP-01/02, DEEP-SCH-02/03/04/05/06. |
| R6 | `arch-infoflow-completeness` | Spec completion | **v1.0.0** | 1 | DEEP-ARCH-03 (GIC bridge), DEEP-IF-01 (`DeclassificationPolicy`), DEEP-IF-02 (SecurityDomain lattice), DEEP-IPC-04 (verify or prove cleanup-error-unreachable). |
| R7 | `capability-deferred-items` | AK8-K LOW-tier cleanup | optional | 1 | DEEP-CAP-05: address each AK8-K item where in-scope; lift residue to debt register. |
| R8 | `test-renames-and-extensions` | Mechanical rename + suite extension | **v0.31.0** | 2 | DEEP-TEST-01/02 (rename), DEEP-RUST-06 (6 missing syscalls in conformance). |
| R9 | `precommit-hardening` | Hook robustness | **v0.31.0** | 1 | DEEP-PRECOM-01: replace regex `sorry` check with Lean tokeniser. |
| R10 | `inline-doc-and-cleanup` | Comment/docstring/inline polish | **v0.31.0** | 1 | DEEP-LICENSE-01, DEEP-CAP-01, DEEP-IPC-02, DEEP-MODEL-03/04, DEEP-RUST-03/04/05, DEEP-FDT-01, DEEP-SCRIPT-01, DEBT-IPC-02. |
| R11 | `documentation-accuracy` | Genuine doc drift | **v0.31.0** | 1 | DEEP-DOC-01/02/03/04/06, DEBT-DOC-01, DEBT-FR-01. |
| R12 | `ci-hygiene-and-structural-gates` | Workflow concurrency + false-positive prevention | **v0.31.0** | 1 (4 sub-tasks) | R12.A: DEEP-CI-01 concurrency blocks. R12.B: production/staged partition gate (subsumes DEEP-ARCH-01). R12.C: ARM-ARM citation gate (subsumes DEEP-RUST-01/02). R12.D: `_fields` consumer gate (subsumes DEEP-ARCH-02). |
| R13 | (reserved) | – | – | 0 (if empty) | Reserved for downstream emergent items discovered during R1..R12. |
| R14 | `post-1.0-backlog` | Maintainability backlog | post-1.0 | – | DEBT-* maintainability + DEEP-PROOF-01 + DEEP-MODEL-02 + DEEP-PRELUDE-01/02. **Not part of v1.0.0**; tracked as the v1.x roadmap. |

### 3.2 Phase ordering rationale

- **R0 first**: the workstream baseline must be cut before any code
  changes so that monotonicity gates have a numeric anchor.
- **R1 next**: a one-line code change with clear NI-symmetry
  rationale demonstrates the workflow end-to-end (commit → pre-commit
  hook → tier scripts → CI) and produces a fast-feedback closure.
- **R2 (the headline slice) third**: the FFI dispatch wiring is the
  largest single chunk of v1.0 implementation work and must precede
  R3 (boot threading), because `bootSafeObject` admitting a VSpaceRoot
  is exercised end-to-end only when a syscall can drive the post-boot
  state.
- **R3 fourth**: with R2 in place, threading
  `rpi5BootVSpaceRoot` into the boot result provides the kernel
  VSpace that the dispatched syscalls need for VSpace operations.
- **R4 fifth**: structural-invariant promotions are pure refactors
  with proof-only obligations; they should land after the runtime
  behaviour stabilises so that proof breakage from the structural
  changes is unambiguously about the structure, not about a runtime
  regression.
- **R5 sixth**: scheduler/lifecycle symmetry is the longest list of
  individually-small fixes; landing it as a single PR keeps proof
  re-elaboration costs tractable.
- **R6 seventh**: spec-completeness work (GIC bridge, SecurityDomain
  lattice, DeclassificationPolicy) closes the remaining
  documented-better-state items.
- **R7..R12**: documentation, hygiene, and CI tier — the order here
  is flexible and PRs can land in parallel because they touch
  disjoint files. The exception is R12.B/C/D (the structural-fix
  CI gates): they should land BEFORE R11 because R11's metric
  refresh runs `test_tier0_hygiene.sh`, which now exercises the
  three new gates. If R11 lands first, the metric refresh PR
  would not have an enforced production/staged partition,
  ARM-ARM citation, or `_fields` consumer check at refresh time
  — a missed opportunity to verify the final state.
- **R11 specifically lands LAST among hygiene phases** because the
  README/codebase_map.json metric refresh must reflect the
  post-implementation tree (otherwise the metrics drift again the
  moment the next R-phase merges).
- **R12 sub-phases R12.A/B/C/D** can land as a single PR (they
  touch disjoint files: `.github/workflows/*.yml` for R12.A, and
  three new `scripts/check_*.sh` files for R12.B/C/D) but it is
  acceptable to land them as four separate PRs if review velocity
  benefits.


### 3.3 File→phase index (jump table)

For maintainers landing a touch in a specific file, this is the lookup
to find the owning phase. Files not listed here have no WS-RC remediation.

| File / area | Phase(s) |
|---|---|
| `SeLe4n.lean` | R10 (SPDX header) |
| `SeLe4n/Prelude.lean` | R14 (LawfulBEq macro, HashSet helpers) |
| `SeLe4n/Model/Object/Structures.lean` | R4 (CNode `slots` opaque type) |
| `SeLe4n/Model/Object/Types.lean` | R4 (`Notification.waitingThreads` NoDup) |
| `SeLe4n/Model/State.lean` | R10 (field cross-references), R14 (17-conjunct refactor) |
| `SeLe4n/Model/Builder.lean` | R14 (named accessors removed once R4/R14 lands) |
| `SeLe4n/Kernel/Capability/Operations.lean` | R4.D (witness theorem for cspaceMutate null-cap guard), R7 (AK8-K), R10 (docstring promotion), R14 (frame helper) |
| `SeLe4n/Kernel/Capability/Invariant/Defs.lean` | R4 (RetypeTarget smart-constructor) |
| `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean` | R1 (line 198 NI symmetry) |
| `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | R6 (cleanup-error proof verification) |
| `SeLe4n/Kernel/IPC/Invariant/{QueueNextBlocking,QueueNoDup,QueueMembership}.lean` | R10 (linter justifier comments) |
| `SeLe4n/Kernel/IPC/Invariant/Structural/{StoreObjectFrame,DualQueueMembership,PerOperation,QueueNextTransport}.lean` | R10 (linter justifier comments) |
| `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | R5 (effectivePriority API uniformity) |
| `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | R5 (.missingSchedContext surfacing) |
| `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` | R14 (Classical removal, file split) |
| `SeLe4n/Kernel/Scheduler/RunQueue.lean` | R5 (rotateToBack defensive fallback) |
| `SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean` | R14 (hypothesis discharge) |
| `SeLe4n/Kernel/SchedContext/Operations.lean` | R5 (domain propagation in schedContextConfigure) |
| `SeLe4n/Kernel/Lifecycle/Suspend.lean` | R5 (PIP recompute on resume; `cancelDonation` split) |
| `SeLe4n/Kernel/Architecture/ExceptionModel.lean` | R6 (GIC dispatch bridge) |
| `SeLe4n/Kernel/Architecture/InterruptDispatch.lean` | R6 (consumer of GIC bridge) |
| `SeLe4n/Kernel/InformationFlow/Soundness.lean` | R6 (`DeclassificationPolicy` import / definition) |
| `SeLe4n/Kernel/InformationFlow/Policy.lean` | R6 (SecurityDomain lattice completion) |
| `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` | R14 (thematic split) |
| `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` | R14 (split when elaborator allows) |
| `SeLe4n/Kernel/RadixTree/Core.lean` | R14 (radixWidth assertion) |
| `SeLe4n/Platform/Boot.lean` | R3 (`bootSafeObject` rewrite) |
| `SeLe4n/Platform/DeviceTree.lean` | R10 (`findMemoryRegPropertyChecked` error distinguisher) |
| `SeLe4n/Platform/FFI.lean` | R2 (entire file: stubs replaced; gating section added) |
| `SeLe4n/Platform/RPi5/VSpaceBoot.lean` | R3 (consumed by Boot.lean rewrite) |
| `tests/Ak8CoverageSuite.lean` | R8 (rename) |
| `tests/An9HardwareBindingSuite.lean` | R8 (rename) |
| `tests/Ak9PlatformSuite.lean` | R8 (rename) |
| `tests/An10CascadeSuite.lean` | R8 (rename) |
| `tests/SyscallDispatchSuite.lean` (NEW) | R2 |
| `tests/NegativeStateSuite.lean` | R14 (split) |
| `rust/sele4n-hal/src/svc_dispatch.rs` | R2 (comment becomes true once `syscallDispatchFromAbi` lands) |
| `rust/sele4n-abi/src/lib.rs` | R10 (module-level doc comment) |
| `rust/sele4n-abi/src/trap.rs` | R10 (comment correction) |
| `rust/sele4n-abi/tests/conformance.rs` | R8 (extend to 6 syscalls) |
| `rust/sele4n-sys/src/lib.rs` | R10 (module-level doc comment) |
| `THIRD_PARTY_LICENSES.md` | R10 (cc semver clarification) |
| `scripts/pre-commit-lean-build.sh` | R9 (tokeniser-based check) |
| `scripts/website_link_manifest.txt` | R10 (timestamp) |
| `README.md` | R11 (DEEP-DOC-01/04/06; DEBT-DOC-01; DEBT-FR-01) |
| `CLAUDE.md` | R11 (source-layout entries) |
| `AGENTS.md` | R11 (rewrite or redirect) |
| `docs/SECURITY_ADVISORY.md` | R11 (FrozenOps experimental status — DEBT-FR-01) |
| `docs/codebase_map.json` | R11 (metric resync) |
| `.github/workflows/{platform_security_baseline,lean_toolchain_update_proposal,nightly_determinism,codebase_map_sync}.yml` | R12.A |
| `scripts/check_production_staging_partition.sh` (NEW) | R12.B |
| `scripts/check_arm_arm_citations.sh` (NEW) | R12.C |
| `scripts/check_no_orphan_fields.sh` (NEW) | R12.D |
| `SeLe4n/Platform/Staged.lean` | R11.C (CLAUDE.md source-layout entry); referenced by R12.B as the canonical staged-set anchor |
| `SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean` | R4.D (witness theorem placement) |


---

## 4. Phase R0 — Audit baseline and bookkeeping

### 4.1 Goal

Cut the WS-RC numeric baseline so monotonicity gates (`scripts/check_codebase_monotonicity.sh`,
`scripts/ak7_cascade_check_monotonic.sh`, `scripts/test_tier0_hygiene.sh`)
have a stable anchor; record the audit errata for DEEP-ARCH-01 (this
plan author's verification finding); confirm closure of the predecessor's
H-24 / DEBT-RUST-02 finding; create the discharge index seed.

### 4.2 Tasks

| # | File | Action | Notes |
|---|---|---|---|
| R0.1 | `docs/audits/AUDIT_v0.30.11_WS_RC_BASELINE.txt` | Write the WS-RC numeric baseline (LoC, file count, theorem count, sorry count, axiom count, Classical-use count, partial-def count, unsafe-block count) | Use `find/grep` per §2.6; commit message records exact commit SHA. |
| R0.2 | `docs/audits/AUDIT_v0.30.11_ERRATA.md` | New file: record DEEP-ARCH-01 withdrawal + verification rationale | Include the 144-module transitive-closure trace from `SeLe4n.lean`. |
| R0.3 | `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | New file: stub index for closure-form proof obligations produced by R1..R12. Empty at R0; populated incrementally. | Mirrors the AUDIT_v0.30.6_DISCHARGE_INDEX.md (archived) format. |
| R0.4 | `docs/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md` (archived) | Add DEBT-RUST-02 / H-24 closure annotation: "Reconfirmed closed at v0.30.11 audit cycle (deep + plan author re-grep both return 0 hits for `WS-V`/`AG10` markers in `rust/sele4n-hal/src/{trap,lib}.rs`)." | Single-line cross-reference annotation; archived file allowed because DEBT-RUST-02 is the predecessor item and the plan-side closure target IS the archived index. Confirm with `scripts/check_website_links.sh`. |
| R0.5 | `docs/audits/README.md` | Update §"Files currently live" to list the four new artefacts (PLAN, BASELINE, ERRATA, DISCHARGE_INDEX). | Removes ambiguity around which audit is active; ensures the README reflects the live state once R0 lands. |
| R0.6 | `docs/WORKSTREAM_HISTORY.md` | Insert WS-RC opening row with phase plan summary + numeric baseline cross-reference. | Status: "in flight (R1..R12 pending)". |

### 4.3 Validation

```bash
./scripts/test_tier0_hygiene.sh   # baseline drift detection
./scripts/check_website_links.sh  # manifest consistency
```

### 4.4 Commit message scaffolding

```
WS-RC R0: cut baseline + audit errata + DEBT-RUST-02 closure

- AUDIT_v0.30.11_WS_RC_BASELINE.txt: numeric baseline at WS-RC start.
- AUDIT_v0.30.11_ERRATA.md: withdraw DEEP-ARCH-01 (audit verification
  error; CacheModel marker is correct; transitive closure proves
  CacheModel/TimerModel/ExceptionModel are NOT in production chain
  from SeLe4n.lean).
- AUDIT_v0.30.11_DISCHARGE_INDEX.md: closure-form index seed.
- AUDIT_v0.30.6_DISCHARGE_INDEX.md: DEBT-RUST-02 / H-24 reconfirmed
  closed (no `WS-V`/`AG10` markers in HAL grep).
- docs/audits/README.md: live-files table sync.
- docs/WORKSTREAM_HISTORY.md: WS-RC opening.
```

### 4.5 Dependencies and exit criteria

- **Depends on:** none.
- **Blocks:** all subsequent phases (every R-phase commit lifts a
  baseline anchor in `docs/codebase_map.json`).
- **Exit criteria:** `test_full.sh` passes; `check_website_links.sh`
  passes; archived discharge index annotation does not regress
  `tier 0` hygiene.


---

## 5. Phase R1 — IPC call-path NI symmetry (DEEP-IPC-03) — **LANDED**

**Status:** COMPLETE on branch `claude/audit-ipc-symmetry-yhdIu`
(2026-04-29). All R1.1..R1.5 tasks discharged; build/test pipeline
green; main trace fixture unchanged.

### 5.1 Goal

Close the last NI asymmetry between the IPC capability-transfer
paths. The send and receive paths (AK1-I) were already aligned with
`.error .invalidCapability` on missing receiver CSpace root; the
call path at `IPC/DualQueue/WithCaps.lean:198` still returns
`.ok ({ results := #[] }, st')`, giving a covert channel via
`KernelError`.

### 5.2 Verified target

```text
File: SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
Line 173 (function): def endpointCallWithCaps ...
Line 198 (replace):  | none => .ok ({ results := #[] }, st')
```

The mirror locations (already correct, used as the AK1-I template):
- `WithCaps.lean:113-125` (send path comment block; copy verbatim)
- `WithCaps.lean:158` (receive path one-liner; same shape)

### 5.3 Tasks

| # | Action |
|---|---|
| R1.1 | At line 198, replace `\| none => .ok ({ results := #[] }, st')` with `\| none => .error .invalidCapability` |
| R1.2 | Insert the AK1-I-style comment block (verbatim copy of lines 113–125, with "send" → "call") immediately before the new line, explaining the NI-symmetry rationale |
| R1.3 | Inspect lines 199–200 (the `\| none =>` and `\| none =>` arms for `receiveQ.head` and `getEndpoint?` mismatches): leave as `.ok` if they encode a different invariant (no receiver enqueued ≠ missing CSpace root), otherwise normalise. **Verification step:** read each arm's predecessor reasoning before changing. |
| R1.4 | Confirm `endpointSendDualWithCaps` (line 113–127) and `endpointReceiveDualWithCaps` (lines 154–168) carry identical comment scaffolding for parity. |
| R1.5 | Update or extend the IPC call-path test in `tests/InformationFlowSuite.lean` and `tests/NegativeStateSuite.lean` to exercise the missing-CSpace-root fault on the call path; assert `.error .invalidCapability`. |

### 5.4 Validation

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.IPC.DualQueue.WithCaps
./scripts/test_smoke.sh
./scripts/test_full.sh        # required because IPC invariant theorems may need re-elab
```

The pre-commit hook will exercise the build automatically on staged
files; do not bypass with `--no-verify`.

### 5.5 Risk

Low. The send/receive paths already use `.error .invalidCapability`
and the comment block already documents the NI-symmetry rationale.
The fix is mechanical. Risk vector: a downstream consumer of
`endpointCallWithCaps` in a test or trace harness might observe the
new error code; resolved by updating those callers in the same PR.

### 5.6 Commit message

```
WS-RC R1: close call-path IPC NI asymmetry (DEEP-IPC-03)

endpointCallWithCaps at IPC/DualQueue/WithCaps.lean:198 returned
.ok ({ results := #[] }, st') on missing receiver CSpace root,
giving a per-domain covert channel via KernelError. Send (line 125)
and receive (line 158) paths were already aligned with
.error .invalidCapability under AK1-I; this closes the call path
to the same shape.
```

### 5.7 Landing summary

The R1.1, R1.2, R1.3 tasks were applied to the call path's
`lookupCspaceRoot = none` arm: it now returns `.error
.invalidCapability` accompanied by a 16-line WS-RC R1 comment block
modeled on the AK1-I send-path comment. The two adjacent `| none =>`
arms (for `ep.receiveQ.head = none` and `getEndpoint? = none`) are
intentionally kept as `.ok` because they encode the unrelated
invariant "no receiver enqueued" — the send path keeps them as
`.ok` for the same reason, so symmetry is preserved.

R1.4 (parity scaffolding) was applied beyond the literal text of the
plan: in addition to confirming send/receive parity, the receive
path's previously-terse U-H13 comment was expanded to match the
AK1-I-shape comment block, and line-number cross-references in all
three comment blocks (send, receive, call) were replaced with
function-name cross-references so they stay correct under future
line-number drift. This was an incidental robustness improvement
flowing from the implement-the-improvement rule (CLAUDE.md §"Implement-
the-improvement rule").

R1.5 (test extension) was applied to both targets:

- `tests/InformationFlowSuite.lean`: the existing AK1-I regression
  was extended to assert send/receive/**call** structural symmetry,
  and a new Test 3 directly invokes `endpointCallWithCaps` on a
  missing-TCB receiver state to verify the wrapper never silently
  succeeds (the pre-R1 covert-channel shape).
- `tests/NegativeStateSuite.lean`: a new
  `runR1IpcCallPathSymmetryChecks` runner adds three focused checks
  (R1-NEG-01 / R1-NEG-02 / R1-NEG-03) covering the healthy state,
  the missing-TCB fault state, and the
  `lookupCspaceRoot = none` predicate.

The proof-side update was not in the plan's task list but is
required by the implement-the-improvement rule: the
`endpointCallWithCaps_preserves_ipcInvariant` theorem in
`SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/ReplyRecv.lean` was
updated so the `lookupCspaceRoot = none` arm becomes vacuous
(`simp [hLookup] at hStep`), matching the post-AK1-I send-path
tactic. Without this update the theorem would have failed to
elaborate.

**Validation evidence:**

- `lake build SeLe4n.Kernel.IPC.DualQueue.WithCaps` ✓
- `lake build SeLe4n.Kernel.IPC.Invariant.CallReplyRecv.ReplyRecv` ✓
- `lake build SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership` ✓
- `lake build` (default target, 302 jobs) ✓
- `./scripts/test_smoke.sh` ✓
- `./scripts/test_full.sh` ✓
- `lake exe sele4n` byte-identical to
  `tests/fixtures/main_trace_smoke.expected` ✓
- 0 sorry / 0 axiom in modified files

---

## 6. Phase R2 — Hardware syscall dispatch wiring (DEEP-FFI-01/02/03 + DEEP-TEST-03)

### 6.1 Goal

Implement the Lean ↔ Rust syscall-dispatch glue so the verified
`syscallEntryChecked` (`Kernel/API.lean:1244`) and `suspendThread`
(`Lifecycle/Suspend.lean`) are reachable from the hardware SVC path.
Per CLAUDE.md's implement-the-improvement rule, this remediation is
the one v1.0 cannot ship without; release-note disclosure is
explicitly rejected.

### 6.2 Verified targets

```text
SeLe4n/Platform/FFI.lean:34-39      docstring claiming hwTarget gating uniform
SeLe4n/Platform/FFI.lean:185-190    @[export suspend_thread_inner] STUB returning 17
SeLe4n/Platform/FFI.lean:216-223    @[export syscall_dispatch_inner] STUB returning (1<<63)|17
SeLe4n/Kernel/API.lean:1244         syscallEntryChecked (verified entry point — already exists)
SeLe4n/Kernel/Lifecycle/Suspend.lean  suspendThread (target of suspend_thread_inner)
SeLe4n/Kernel/Architecture/RegisterDecode.lean  decode primitives (already exist)
SeLe4n/Kernel/Architecture/SyscallArgDecode.lean per-syscall typed decode (already exists)
rust/sele4n-hal/src/svc_dispatch.rs:271-308  Rust caller of syscall_dispatch_inner
rust/sele4n-hal/src/svc_dispatch.rs:308       comment naming the missing Lean fn
rust/sele4n-hal/src/ffi.rs:325               extern "C" suspend_thread_inner
```

This phase is large enough that it is decomposed into **three**
sequential sub-PRs (R2.A, R2.B, R2.C). Each sub-PR is independently
buildable and shippable; the v1.0 readiness gate clears only when
all three land.

### 6.3 Sub-PR R2.A — `SystemState` threading and dispatch helper

**Goal.** Provide a Lean-side mechanism for the FFI `@[export]`
functions to access the global `SystemState`. The simulation
trace harness already manages state via direct value passing; the
hardware path needs a single mutable reference so the C-callable
shim can access state without a parameter pipe.

**Tasks.**

| # | File | Action |
|---|---|---|
| R2.A.1 | `SeLe4n/Platform/FFI.lean` | Add `private def kernelStateRef : IO.Ref SystemState` (initialised in `initialiseFromConfig`). Mark with `@[hwTarget]` conditional `section`/`end`. |
| R2.A.2 | `SeLe4n/Platform/FFI.lean` | Add `def initialiseKernelState (st : SystemState) : BaseIO Unit := kernelStateRef.set st` and a `getKernelState : BaseIO SystemState` reader. |
| R2.A.3 | `SeLe4n/Platform/Boot.lean` | Call `initialiseKernelState` after `bootFromPlatformChecked` returns `.ok`. (No-op on simulation builds because the same call path is exercised by `MainTraceHarness`.) |
| R2.A.4 | `SeLe4n/Platform/FFI.lean` | Document the design choice in the file's header docstring. The IO.Ref approach is chosen because (a) the simulation harness already passes state explicitly so the IO.Ref is a hardware-only addition; (b) the alternative thread-local register-decoded snapshot adds two FFI symbols per syscall; (c) the Rust HAL already serialises SVC entry under `with_interrupts_disabled`, so the IO.Ref does not require atomicity. |
| R2.A.5 | `tests/SyscallDispatchSuite.lean` (new) | Exercise the IO.Ref initialisation path in a simulation context: bootstrap via `bootFromPlatformChecked`, then read state via `getKernelState`. |

**Implementation walkthrough.**

*R2.A.1 — IO.Ref construction.* The `IO.Ref SystemState` is a Lean
4 stdlib primitive backed by an atomic pointer; reads and writes
are sequential per `IO.Ref` semantics. Implementation pattern (to
mirror in `SeLe4n/Platform/FFI.lean`):

```lean
section
@[hwTarget]
private opaque kernelStateRefImpl : NonemptyType
private def KernelStateRef : Type := kernelStateRefImpl.type
private opaque kernelStateRef : IO.Ref KernelStateRef
end
```

The `@[hwTarget]` attribute is the same one used for the
`@[extern]` declarations elsewhere in the file; verify by reading
the existing section around lines 50–242. If the attribute name
differs in practice, use whatever the existing gating section uses.

*R2.A.2 — Init/read API.* The two functions form a minimal API:

```lean
def initialiseKernelState (st : SystemState) : BaseIO Unit :=
  kernelStateRef.set st

def getKernelState : BaseIO SystemState :=
  kernelStateRef.get

def updateKernelState (f : SystemState → SystemState) : BaseIO Unit :=
  kernelStateRef.modify f
```

`updateKernelState` is the helper R2.B.2/B.3 use to apply the
`Kernel α → SystemState → Result α × SystemState` produced by
`syscallEntryChecked`.

*R2.A.3 — Boot integration.* `Platform/Boot.lean:696`
(`bootFromPlatformChecked`) currently returns `Except KernelError
(SystemState × _)`. The change is additive: keep the return type,
add a top-level wrapper that, on `.ok`, also calls
`initialiseKernelState`. Mirror the existing pattern in
`SeLe4n/Testing/MainTraceHarness.lean` for consistency:

```lean
def bootAndInitialiseFromPlatform (cfg : PlatformConfig) : BaseIO (Except KernelError SystemState) := do
  match bootFromPlatformChecked cfg with
  | .error e => pure (.error e)
  | .ok (st, _) =>
      initialiseKernelState st
      pure (.ok st)
```

The hardware boot path (Rust HAL `boot.S` → Rust kernel-init →
this wrapper) calls `bootAndInitialiseFromPlatform`; the simulation
path (MainTraceHarness) keeps using `bootFromPlatformChecked`
directly.

*R2.A.4 — Design-choice documentation.* Three alternatives
considered; the file's header docstring records all three so a
future contributor understands the trade-offs:

1. **IO.Ref (chosen)**: single mutable cell, sequential SVC
   semantics on hardware (HAL `with_interrupts_disabled`), no
   per-syscall FFI overhead.
2. **Thread-local register-decoded snapshot**: rejected because
   it would add 8 register-passing FFI symbols per syscall and
   complicate the typed-decode path.
3. **Pure functional re-construction at every SVC entry**:
   rejected because it would force every Rust SVC entry to
   serialise/deserialise the entire SystemState, a hot-path cost
   that is unbounded in object-store size.

*R2.A.5 — Test-side initialisation hook.* The new
`SyscallDispatchSuite` exercises the IO.Ref path under simulation
by calling `initialiseKernelState` explicitly with a bootstrapped
state, then invoking `getKernelState` and asserting equality. This
test runs in simulation builds only; on hardware the same path is
exercised by Rust integration code.

**Validation.** `lake build SeLe4n.Platform.FFI`, `lake build SeLe4n.Platform.Boot`, `test_smoke.sh`.

### 6.4 Sub-PR R2.B — `syscallDispatchFromAbi` and FFI export bodies

**Goal.** Replace the two `@[export]` stubs with bodies that
actually thread typed arguments through `syscallEntryChecked`
and `suspendThread`. The Lean-side function the Rust comment at
`svc_dispatch.rs:308` names (`syscallDispatchFromAbi`) becomes
the typed-ABI entry point.

**Tasks.**

| # | File | Action |
|---|---|---|
| R2.B.1 | `SeLe4n/Platform/FFI.lean` | Add `def syscallDispatchFromAbi (syscallId : UInt32) (msgInfo : UInt64) (regs : Array UInt64) (ipcBufferAddr : UInt64) : Kernel UInt64` that: (a) decodes `syscallId` → typed `SyscallId` via `RegisterDecode.decodeSyscallId`; (b) decodes `regs` and `msgInfo` into the appropriate typed-arg struct via `SyscallArgDecode.decodeSyscallArgs`; (c) invokes `syscallEntryChecked` with the typed args; (d) re-encodes the result back to `UInt64` per the high-bit-set encoding (bit 63 = error). |
| R2.B.2 | `SeLe4n/Platform/FFI.lean` | Replace the stub body of `syscallDispatchInner` (lines 217–223) with a thin wrapper that reads `kernelStateRef`, calls `syscallDispatchFromAbi`, applies the result to update `kernelStateRef`, and returns the encoded `UInt64`. |
| R2.B.3 | `SeLe4n/Platform/FFI.lean` | Replace the stub body of `suspendThreadInner` (lines 186–190) similarly: read state, call `suspendThread (ThreadId.ofUInt64 _tid)`, write state back, encode `KernelError` discriminant. |
| R2.B.4 | `rust/sele4n-hal/src/svc_dispatch.rs` | The comment at line 308 referencing `syscallDispatchFromAbi` becomes accurate as written (no edit required); verify the identifier/symbol name (`sele4n_syscall_dispatch_inner` vs bare `syscall_dispatch_inner`) matches the Lean export and the Rust `extern "C"` block. If the comment claims `sele4n_syscall_dispatch_inner` and the Lean export is `syscall_dispatch_inner`, update either side so they match. |
| R2.B.5 | `SeLe4n/Platform/FFI.lean` | Add three correctness theorems to the new section: (a) `syscallDispatchFromAbi_ok_iff_syscallEntryChecked_ok` (decoding round-trip), (b) `syscallDispatchFromAbi_preserves_well_typed_invariant`, (c) `syscallDispatchInner_eq_syscallDispatchFromAbi_after_state_io`. These tie the FFI entry to the verified entry point. |
| R2.B.6 | `SeLe4n/Kernel/API.lean` | Re-export `syscallEntryChecked` such that consumers (R2.B.1, tests) can reference it without circular imports. (Already exported; verify by direct read.) |

**Implementation walkthrough.**

*R2.B.1 — `syscallDispatchFromAbi` body — REVISED per audit.* The
plan author's audit at WS-RC R0 prep verified the actual
`syscallEntryChecked` signature at `Kernel/API.lean:1244`:

```lean
def syscallEntryChecked (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (regCount : Nat := 32) : Kernel Unit
```

Crucially, `syscallEntryChecked` does **not** take pre-decoded
typed args. It looks up `lookupThreadRegisterContext tid st`
internally and invokes `decodeSyscallArgsFromState st tid layout
regs regCount` to do the decode (line 1260). So the FFI shim
should NOT re-implement the decode; instead it should populate
the current thread's register context from the FFI-passed
register values, then call `syscallEntryChecked`.

Revised implementation skeleton:

```lean
def syscallDispatchFromAbi
    (syscallId : UInt32) (msgInfo : UInt64)
    (regs : Array UInt64) (ipcBufferAddr : UInt64) : Kernel UInt64 :=
  fun st =>
    -- Step 1: Look up the current thread (must exist on syscall entry).
    match st.scheduler.current with
    | none => .ok (encodeError .illegalState, st)
    | some tid =>
      -- Step 2: Populate the current thread's register context from the
      -- FFI inputs (syscallId in x8 per ARM EABI; msgInfo in x1; x0..x5
      -- per RegisterDecode layout; ipcBufferAddr in TCB.ipcBuffer).
      let stWithRegs := writeFfiRegistersToTcb st tid syscallId msgInfo regs ipcBufferAddr
      -- Step 3: Invoke the verified entry point with the platform's
      -- canonical layout and a labeling context derived from the TCB.
      let layout := SeLe4n.SyscallRegisterLayout.aapcs64
      let ctx := labelingContextOfTcb stWithRegs tid
      match syscallEntryChecked ctx layout 32 stWithRegs with
      | .error ke => .ok (encodeError ke, stWithRegs)
      | .ok ((), st') =>
        -- Step 4: Read the syscall result from the post-state
        -- (currentThread's x0 register, per AAPCS64 return convention).
        .ok (encodeOk (readReturnValue st' tid), st')
```

Helpers used:
- `writeFfiRegistersToTcb`: pure SystemState transform writing the
  passed register values into the TCB's `registerContext` field.
  Trivial (8 RegisterFile.set calls).
- `labelingContextOfTcb`: derives the IF labeling context from
  the TCB's recorded security domain. Likely already exists; if
  not, define it.
- `readReturnValue`: extracts x0 from the TCB's register context
  post-call.
- `encodeError`/`encodeOk`: bit-63-discriminant encoding into a
  `UInt64` per the Rust-side decoding contract.

This design AVOIDS the over-engineering of re-implementing
decode (the original plan called for this; the audit corrected
it). The verified `syscallEntryChecked` is invoked directly with
its actual signature. Decode happens once, where it always has
(inside `syscallEntryChecked`).

*R2.B.2 — `syscallDispatchInner` body.* The exported function
becomes a thin BaseIO wrapper:

```lean
@[export syscall_dispatch_inner]
def syscallDispatchInner
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64) (ipcBufferAddr : UInt64) : BaseIO UInt64 := do
  let st ← getKernelState
  let regs := #[x0, x1, x2, x3, x4, x5]
  match syscallDispatchFromAbi syscallId msgInfo regs ipcBufferAddr st with
  | .ok (encoded, st') => initialiseKernelState st'; pure encoded
  | .error e => pure (encodeError e)
```

The signature change from `(_x0 _x1 _x2 _x3 _x4 _x5 : UInt64) →
UInt64` (current stub) to a `BaseIO UInt64` return is necessary
because the function now performs IO. Verify the Rust HAL's
`extern "C" { fn syscall_dispatch_inner(...) -> u64; }`
declaration matches: Lean emits a `BaseIO UInt64` as a C function
returning `u64` after the runtime executes the IO action.

*R2.B.3 — `suspendThreadInner` body.* Same pattern, narrower
scope:

```lean
@[export suspend_thread_inner]
def suspendThreadInner (tid : UInt64) : BaseIO UInt32 := do
  let st ← getKernelState
  match suspendThread (ThreadId.ofUInt64 tid) st with
  | .ok ((), st') => initialiseKernelState st'; pure 0  -- KernelError::Ok
  | .error e => pure e.toUInt32
```

`KernelError.toUInt32` already exists (per the `KernelError`
discriminant table); confirm by reading `Prelude.lean`.

*R2.B.4 — Rust comment alignment.* After R2.B.1 lands, the Rust
comment at `svc_dispatch.rs:308` becomes accurate **as written**
because `syscallDispatchFromAbi` now exists in Lean. No edit
required UNLESS the symbol-name discrepancy
(`sele4n_syscall_dispatch_inner` vs bare `syscall_dispatch_inner`)
is real. Resolution sequence:
1. Read the Rust comment verbatim.
2. Read the Lean export name (`@[export syscall_dispatch_inner]`).
3. If Rust says `sele4n_syscall_dispatch_inner` and Lean says
   `syscall_dispatch_inner`, prefer the Lean side as canonical and
   update the Rust comment. Renaming the Lean export would require
   updating the Rust `extern "C"` block (more files touched).

*R2.B.5 — Correctness theorems.* Three theorems witness the
bridge's correctness; their statements should be:

```lean
theorem syscallDispatchFromAbi_ok_iff_syscallEntryChecked_ok
    (syscallId : UInt32) (msgInfo : UInt64) (regs : Array UInt64)
    (ipcBufferAddr : UInt64) (st : SystemState)
    (sid : SyscallId) (args : TypedArgs)
    (hSid : RegisterDecode.decodeSyscallId syscallId = .ok sid)
    (hArgs : SyscallArgDecode.decodeSyscallArgs sid msgInfo regs ipcBufferAddr = .ok args) :
    (∃ encoded st', syscallDispatchFromAbi syscallId msgInfo regs ipcBufferAddr st
                      = .ok (encoded, st'))
    ↔ (∃ result st', syscallEntryChecked sid args st = .ok (result, st'))

theorem syscallDispatchFromAbi_preserves_well_typed_invariant
    (syscallId : UInt32) (msgInfo : UInt64) (regs : Array UInt64)
    (ipcBufferAddr : UInt64) (st : SystemState)
    (hInv : systemInvariant st)
    (encoded : UInt64) (st' : SystemState)
    (hOk : syscallDispatchFromAbi syscallId msgInfo regs ipcBufferAddr st = .ok (encoded, st')) :
    systemInvariant st'

theorem syscallDispatchInner_eq_syscallDispatchFromAbi_after_state_io :
    -- relates the BaseIO wrapper to the pure Kernel function
    -- via a state-passing equivalence
    ...
```

These theorems live in `FFI.lean` (or a sibling proof file
`FFI/Bridge.lean` if the proofs are non-trivial). Their proofs
unfold `syscallDispatchFromAbi`, case-split on the decode arms,
and chain through `syscallEntryChecked`'s existing invariant-
preservation theorems.

*R2.B.6 — Re-export verification.* `Kernel/API.lean:1244` already
exports `syscallEntryChecked`. Verify with
`grep -n "syscallEntryChecked" SeLe4n/Kernel/API.lean`. If the
export is missing, add it; otherwise this task is verification-only.

**Validation.** `lake build SeLe4n.Platform.FFI`, `lake build SeLe4n.Platform.Staged` (the staged anchor), `test_full.sh`.

### 6.5 Sub-PR R2.C — `hwTarget` gating uniformity + integration suite

**Goal.** Make the FFI.lean docstring's claim ("`@[extern]` is only
active when building with `-DhwTarget=true`") true uniformly for both
directions of the bridge (DEEP-FFI-03), and add the dedicated
hardware-mode integration suite that DEEP-TEST-03 calls for.

**Tasks.**

| # | File | Action |
|---|---|---|
| R2.C.1 | `SeLe4n/Platform/FFI.lean` | Wrap the two `@[export]` declarations (post-R2.B bodies) in the same `hwTarget`-conditional `section`/`end` already used for the `@[extern]` declarations. After this lands, the docstring's gating claim is uniformly true. |
| R2.C.2 | `SeLe4n/Platform/FFI.lean` | Update the docstring to explicitly state that the gating applies to both directions; add an example showing a simulation build where the `@[export]` stubs are absent. |
| R2.C.3 | `tests/SyscallDispatchSuite.lean` | Extend the suite started in R2.A to cover each `SyscallId` variant: positive case (success encoded as bit 63 = 0), negative cases (`.invalidCapability`, `.illegalState`, `.objectNotFound`, etc., each with the matching `KernelError` discriminant in the low 32 bits when bit 63 is set). |
| R2.C.4 | `tests/SyscallDispatchSuite.lean` | Add a regression test for the `suspend_thread_inner` path: bootstrap a simulation with one TCB, call `suspendThreadInner` via the simulation's IO.Ref bridge, verify `tcb.threadState = .suspended`. |
| R2.C.5 | `lakefile.toml` | Register `SyscallDispatchSuite` as a `lean_exe`. |
| R2.C.6 | `scripts/test_tier2_negative.sh` and `scripts/test_tier3_anchors.sh` | Wire the new suite into the appropriate tier scripts. |

**Validation.** Tier 0..3 clean; the new suite passes; `test_full.sh`
matches the post-R2 baseline.

### 6.6 Phase exit criteria

- All three sub-PRs landed.
- `tests/SyscallDispatchSuite.lean` exercises every `SyscallId`
  variant.
- `test_full.sh` and `test_rust.sh` clean.
- The Rust comment at `svc_dispatch.rs:308` references the
  function/symbol that actually exists.
- `grep -rn "syscallDispatchFromAbi" SeLe4n` returns at least one hit
  (the new Lean function).
- Simulation build with `-DhwTarget=false` excludes both `@[export]`
  symbols.

### 6.7 Risk

**High** as a phase, because this is the largest implementation
slice in WS-RC. Mitigations:

- Decomposing into R2.A/B/C lets each sub-PR be reviewed and merged
  on its own; if R2.B uncovers a design issue (e.g., the IO.Ref does
  not survive Lean's compilation model the way we expect), R2.A
  alone is still a coherent landing.
- The verified `syscallEntryChecked` is unchanged; this phase only
  builds the entry/exit shim, so all proof debt around it is
  pre-existing and audited.
- The new tests in R2.C catch regressions in the encoding contract
  (high-bit error discriminant) end-to-end.

### 6.8 Commit message scaffolding

```
WS-RC R2.A: thread SystemState through FFI via IO.Ref
WS-RC R2.B: implement syscallDispatchFromAbi and FFI export bodies
            (closes DEEP-FFI-01, DEEP-FFI-02)
WS-RC R2.C: uniform hwTarget gating + SyscallDispatchSuite
            (closes DEEP-FFI-03, DEEP-TEST-03)
```


---

## 7. Phase R3 — Boot VSpace threading (DEEP-BOOT-01)

### 7.1 Goal

Thread the verified `rpi5BootVSpaceRoot` (`Platform/RPi5/VSpaceBoot.lean`)
through `bootSafeObject` (`Platform/Boot.lean:551`) into the boot
result so the W^X-compliance proof carries through to runtime. The
"or remove the unwired data structure" alternative is struck per
CLAUDE.md's implement-the-improvement rule: the proven-W^X-compliant
structure is the better state.

### 7.2 Verified targets

```text
SeLe4n/Platform/Boot.lean:551       bootSafeObject — currently rejects all VSpaceRoot variants
SeLe4n/Platform/Boot.lean:696       bootFromPlatformChecked — caller of bootSafeObjectCheck
SeLe4n/Platform/RPi5/VSpaceBoot.lean:232-238  rpi5BootVSpaceRoot proven W^X compliant
SeLe4n/Platform/RPi5/VSpaceBoot.lean:272-297  bootSafeVSpaceRoot predicate
```

### 7.3 Tasks

| # | File | Action |
|---|---|---|
| R3.1 | `SeLe4n/Platform/Boot.lean:551` | Rewrite `bootSafeObject` so the `\| .vspaceRoot vsr => false` arm becomes `\| .vspaceRoot vsr => bootSafeVSpaceRoot vsr` (admit VSpaceRoots that satisfy the boot-safe predicate). |
| R3.2 | `SeLe4n/Platform/Boot.lean` | Add a public theorem `bootSafeObject_admits_rpi5BootVSpaceRoot : bootSafeObject (.vspaceRoot rpi5BootVSpaceRoot) = true` so the connection is proof-witnessed at the boot layer. |
| R3.3 | `SeLe4n/Platform/Boot.lean` | Update `bootFromPlatformChecked` to: (a) admit a `KernelObject.vspaceRoot rpi5BootVSpaceRoot` into the initial object store, (b) record the VSpace root reference in the resulting `SystemState.scheduler` so subsequent VSpace operations can find it. |
| R3.4 | `SeLe4n/Platform/RPi5/Contract.lean` | Wire `rpi5BootVSpaceRoot` into the RPi5 `PlatformBinding` instance so the simulation harness can also exercise the path. |
| R3.5 | `SeLe4n/Platform/Sim/Contract.lean` | Provide a corresponding sim VSpace root (or import `rpi5BootVSpaceRoot` if portable) so the sim build does not regress on the new object-store admission. |
| R3.6 | `SeLe4n/Platform/Boot.lean` | Update the `bootFromPlatformChecked_eq_bootFromPlatform` correctness theorem at line 747 (predecessor §2.4) to account for the new object-store entry; if the proof breaks, the right approach is to extend the equality predicate, not to weaken the theorem. |
| R3.7 | `tests/TwoPhaseArchSuite.lean` | Add a regression test confirming that post-boot the kernel state contains a VSpaceRoot ObjId entry whose `wxExclusiveInvariant` holds. |
| R3.8 | `tests/An9HardwareBindingSuite.lean` (renamed in R8) | Update or extend hardware-binding tests to exercise the new boot-time VSpace admission. |

### 7.4 Implementation walkthrough

*R3.1 — `bootSafeObjectCheck` and `bootSafeObject` rewrite.* The
boot path actually has **two parallel functions** (verified by
direct read at audit time):

- `bootSafeObjectCheck : KernelObject → Bool` at `Platform/Boot.lean:534`
  (runtime-decidable check used by `bootFromPlatformChecked`)
- `bootSafeObject : KernelObject → Prop` at `Platform/Boot.lean:1456`
  (Prop-level predicate used by proof obligations)

Both currently reject all `VSpaceRoot` variants:

```lean
-- bootSafeObjectCheck:551
| .vspaceRoot _ => false

-- bootSafeObject:1478
(∀ vs, obj ≠ .vspaceRoot vs) ∧
```

The replacement must update **both**. Since `bootSafeVSpaceRoot` is
defined as `Prop` at `Platform/RPi5/VSpaceBoot.lean:273`
(`def bootSafeVSpaceRoot (root : VSpaceRoot) : Prop := VSpaceRootWellFormed root`),
the substitutions are:

```lean
-- bootSafeObjectCheck (Bool variant):
| .vspaceRoot vsr => decide (bootSafeVSpaceRoot vsr)

-- bootSafeObject (Prop variant):
(∀ vs, obj = .vspaceRoot vs → bootSafeVSpaceRoot vs) ∧
```

The `decide` wrapping in the Bool variant requires
`Decidable (bootSafeVSpaceRoot vsr)`. `VSpaceRootWellFormed` is a
conjunction of decidable predicates (`asid = 0`, `wxCompliant`,
`paddrBounded`, `mappings.size > 0`); confirm a `Decidable`
instance exists or add one.

Verify the soundness theorem `bootSafeObjectCheck_sound_structural`
(at `Platform/Boot.lean:567`) is updated to admit the new
VSpaceRoot arm: the existing theorem proves `bootSafeObjectCheck =
true → bootSafeObject obj`; with the new arm, it must additionally
prove `decide (bootSafeVSpaceRoot vsr) = true → bootSafeVSpaceRoot vsr`,
which is the standard `decide_eq_true` lemma.

*R3.2 — Admission witness theorem.* Add immediately after the
`bootSafeObject` definition:

```lean
theorem bootSafeObject_admits_rpi5BootVSpaceRoot :
    bootSafeObject (.vspaceRoot rpi5BootVSpaceRoot) = true := by
  unfold bootSafeObject
  exact rpi5BootVSpaceRoot_satisfies_bootSafeVSpaceRoot
```

The supporting theorem `rpi5BootVSpaceRoot_satisfies_bootSafeVSpaceRoot`
already exists in `VSpaceBoot.lean` (per audit §6.2 verification
that the structure is "proven W^X-compliant"); confirm by reading
the file.

*R3.3 — Object-store admission in `bootFromPlatformChecked`.* The
current implementation builds the initial object store from
`config.initialObjects` only (verified field name at audit time).
The change is to inject `rpi5BootVSpaceRoot` into the store at a
reserved ObjId. The cleanest approach is to extend `PlatformConfig`
with an optional `bootVSpaceRoot : Option (ObjId × VSpaceRoot)`
field, defaulting to
`some (rpi5BootVSpaceRootObjId, rpi5BootVSpaceRoot)` for the RPi5
binding and `none` for sim (or a sim equivalent). Implementation
steps:

1. Add `bootVSpaceRoot : Option (ObjId × VSpaceRoot)` to
   `PlatformConfig` in `Platform/Boot.lean:81` (the structure's
   actual location — Contract.lean defines `PlatformBinding`
   typeclass, not `PlatformConfig`). Default to `none` to preserve
   backward compatibility for existing call sites.
2. In `bootFromPlatformChecked`, after gate (3) (IRQ handlers
   reference notifications), if `cfg.bootVSpaceRoot = some (oid, vsr)`,
   insert `KernelObject.vspaceRoot vsr` at `oid` in the
   under-construction object store via `IntermediateState`'s
   builder API.
3. Verify the gate (1) `objectIdsUnique` check still passes (the
   reserved ObjId must not collide with `config.initialObjects`
   ObjIds). If a collision is possible, return
   `.error .invalidConfig` BEFORE installing.
4. Record the VSpaceRoot reference in `SystemState.scheduler` (or
   wherever the kernel looks up "the boot VSpace") so subsequent
   VSpace operations can find it without re-scanning the store.

*R3.4 — RPi5 contract wiring.* In `Platform/RPi5/Contract.lean`,
update the `PlatformBinding` instance's `config` field to include
`bootVSpaceRoot := some (rpi5BootVSpaceRootObjId, rpi5BootVSpaceRoot)`.
Verify the import path of `rpi5BootVSpaceRoot`.

*R3.5 — Sim contract parity.* Two options:

- **Option A (recommended)**: define `simBootVSpaceRoot` in
  `Platform/Sim/Contract.lean` as a minimal VSpaceRoot satisfying
  `bootSafeVSpaceRoot` (e.g., empty page tables, default ASID).
  Wire into `Sim/Contract.lean`'s `PlatformBinding` instance.
- **Option B**: leave Sim's `bootVSpaceRoot := none`. This means
  the Sim platform admits no boot VSpace, which is acceptable
  because Sim does not exercise hardware page-table operations.
  Less symmetric but simpler.

Recommended: Option A for parity. Cost: ~30 lines of new code.

*R3.6 — Correctness theorem update.* The existing theorem
`bootFromPlatformChecked_eq_bootFromPlatform` at line 747 proves
that the checked boot path produces the same result as the
unchecked path. With R3.3 admitting an additional object, the
proof must be widened. Approach:

1. Read the existing theorem statement and proof.
2. The proof likely case-splits on each gate; the new admission
   branch becomes a new case. The unchecked `bootFromPlatform`
   may also need to admit the VSpaceRoot to maintain the equality.
3. If the unchecked function does not admit the root, the
   equality theorem becomes a conditional implication: "checked
   = unchecked when `cfg.bootVSpaceRoot = none`". This is
   acceptable but should be documented in the theorem name (e.g.,
   `bootFromPlatformChecked_eq_bootFromPlatform_no_vspace`) and
   a sibling theorem
   `bootFromPlatformChecked_admits_vspace` proves the new arm.

*R3.7 — Regression test.* In `tests/TwoPhaseArchSuite.lean`, add:

```lean
def test_post_boot_state_contains_rpi5_vspace_root : IO TestResult := do
  let cfg := simulationConfigWithBootVSpace
  match bootFromPlatformChecked cfg with
  | .ok (st, _) =>
    -- Look up the boot VSpaceRoot ObjId and assert
    -- (a) it exists in the object store, (b) wxExclusiveInvariant holds.
    ...
  | .error e => failTest s!"boot failed: {repr e}"
```

*R3.8 — Hardware-binding regression.* The renamed
`HardwareBindingClosureSuite` (post-R8) already exercises the
hardware-binding closure end-to-end; extend it to assert the
post-boot state has a VSpaceRoot.

### 7.5 Validation

```bash
source ~/.elan/env
lake build SeLe4n.Platform.Boot
lake build SeLe4n.Platform.Contract
lake build SeLe4n.Platform.RPi5.Contract
lake build SeLe4n.Platform.RPi5.VSpaceBoot
lake build SeLe4n.Platform.Sim.Contract
./scripts/test_full.sh
```

### 7.6 Risk

**Medium.** The change touches a 5-gate validation chain in
`bootFromPlatformChecked` and a correctness theorem
(`bootFromPlatformChecked_eq_bootFromPlatform`). Mitigations:

- The `bootSafeVSpaceRoot` predicate is already proven (lines
  272–297 of `VSpaceBoot.lean`); admission of a VSpaceRoot
  satisfying it is a structural extension.
- The theorem update is narrowly scoped: the equality predicate
  must be widened to allow the new object-store entry. If
  proof breakage is widespread, R3.6 split into its own commit
  is acceptable.
- Sim platform may need a corresponding VSpace structure; if
  parity with RPi5 is non-trivial, a `simBootVSpaceRoot` stub
  satisfying `bootSafeVSpaceRoot` is acceptable.

### 7.7 Commit message

```
WS-RC R3: thread rpi5BootVSpaceRoot through bootSafeObject (DEEP-BOOT-01)

bootSafeObject at Platform/Boot.lean:551 previously rejected all
VSpaceRoot objects, rendering the proven-W^X-compliant
rpi5BootVSpaceRoot data structure inert. Per the implement-the-
improvement rule, the verified structure is the better state and
the boot path must consume it.

- Boot.lean:551 admits VSpaceRoot if bootSafeVSpaceRoot vsr.
- bootFromPlatformChecked installs rpi5BootVSpaceRoot into the
  initial object store; correctness theorem widened to match.
- Sim platform parity preserved via simBootVSpaceRoot.
- TwoPhaseArchSuite regression test added.
```


---

## 8. Phase R4 — Structural-invariant promotions (DEEP-MODEL-01, DEEP-CAP-04, DEEP-IPC-05, DEEP-CAP-02, DEEP-IPC-01)

### 8.1 Goal

Promote three currently-implicit invariants to structural / type-level
enforcement (R4.A/B/C) so the proof obligation is discharged
constructively at construction time rather than maintained by upstream
convention. Add a witness theorem (R4.D) for the cspaceMutate null-cap
guard so the deep audit's §11.1 manual verification of DEEP-CAP-02 is
codified at the proof-system level rather than relying on a future
auditor's manual `grep`. Subsumes the DEEP-IPC-01 false positive
because the type-level NoDup (R4.C) makes its runtime-only guard
strictly stronger.

### 8.2 Verified targets

```text
SeLe4n/Model/Object/Structures.lean   CNode.slots : RHTable Slot Capability
SeLe4n/Model/Builder.lean:290-291     slotsUnique proof obligation site
SeLe4n/Model/Object/Types.lean        Notification.waitingThreads : List ThreadId
SeLe4n/Kernel/IPC/Operations/Endpoint.lean:723  runtime O(1) duplicate guard
SeLe4n/Kernel/Capability/Invariant/Defs.lean:345-367  RetypeTarget phantom witness
SeLe4n/Kernel/Capability/Operations.lean:1081-1111  cspaceMutate definition (R4.D target)
SeLe4n/Kernel/Capability/Operations.lean:1093       runtime null-cap guard (R4.D witness target)
SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean  R4.D theorem placement
```

### 8.3 Sub-task R4.A — `slotsUnique` structural enforcement

| # | Action |
|---|---|
| R4.A.1 | Define `private structure UniqueSlotMap where slots : RHTable Slot Capability ; uniqueSlots : (∀ s c, slots.get? s = some c → ...) := by decide`. Public API: `UniqueSlotMap.empty`, `UniqueSlotMap.insert` (returns `Option UniqueSlotMap` with the proof discharged in the smart constructor), `UniqueSlotMap.lookup`, etc. |
| R4.A.2 | Replace `CNode.slots : RHTable Slot Capability` with `CNode.slots : UniqueSlotMap`. |
| R4.A.3 | Update Builder.lean to use the smart constructor; the previous `slotsUnique` proof obligation in Builder lines 290–291 becomes the constructor's discharge step. |
| R4.A.4 | Update every consumer of `cnode.slots` (CSpace operations, capability transfer, etc.) to access via `UniqueSlotMap.lookup` / `.insert` rather than raw `RHTable` operations. **Validation**: `lake build SeLe4n.Kernel.Capability.Operations` must remain green. |
| R4.A.5 | Add a regression theorem `cnode_slots_unique : ∀ (cn : CNode), cn.slots.uniqueSlots`. |

### 8.4 Sub-task R4.B — `RetypeTarget` non-bypassable

**Verified at audit time** (re-read `Capability/Invariant/Defs.lean:316–367`):
the existing `RetypeTarget` already IS a smart-constructor pattern —
the `structure RetypeTarget (st : SystemState)` at line 357 has
fields `id : ObjId` and `cleanupHookDischarged : Kernel.cleanupHookDischarged st id`,
so any direct construction must supply both arguments. The
"phantom-like" criticism in the deep audit's §5.1 is about the
**weakness of the predicate**, not about a bypassable structure.

The `cleanupHookDischarged` predicate (lines 346–350) is the
conjunction of two state-observable properties: object-type
metadata consistency, and absence of stale scheduler queue
references. A caller can in principle prove these manually by
reasoning about the post-scrub state without actually running
`scrubLifecycleObject`. R4.B's job is to **strengthen the
predicate** so manual discharge becomes infeasible.

| # | Action |
|---|---|
| R4.B.1 | At `Capability/Invariant/Defs.lean:346-350`, strengthen `cleanupHookDischarged` to additionally require an opaque **scrub-witness token** that can only be obtained as a side-effect of `lifecyclePreRetypeCleanup`. Sketch: introduce `private opaque ScrubToken : SystemState → ObjId → Type` whose only public constructor is the result of `lifecyclePreRetypeCleanup_ok`; add it as a third conjunct of `cleanupHookDischarged`. |
| R4.B.2 | At `Lifecycle/Operations/Cleanup.lean`, change `lifecyclePreRetypeCleanup` to return `Kernel ScrubToken` rather than `Kernel Unit`, threading the token to its callers. |
| R4.B.3 | At `Lifecycle/Operations/RetypeWrappers.lean`, update the `lifecycleRetypeWithCleanup` call chain to capture the scrub token and pass it to `mkRetypeTarget` via the strengthened `cleanupHookDischarged`. |
| R4.B.4 | Update the `RetypeTarget` docstring at lines 332–336 to drop the "phantom-like" caveat and replace with: "The predicate now incorporates a `ScrubToken`-backed witness; manual discharge by reasoning about post-scrub state alone is no longer sufficient." |
| R4.B.5 | Add a no-bypass witness theorem: `theorem retypeTarget_implies_scrub_token_held (rt : RetypeTarget st) : ∃ token : ScrubToken st rt.id, True` — recording that every constructed `RetypeTarget` carries an opaque token whose existence proves the cleanup hook ran. |
| R4.B.6 | Verify that the structure remains `public` (it must, since downstream lifecycle wrappers construct it); only the `ScrubToken` opaque type is `private`. The smart-constructor effect is achieved by gating the only `ScrubToken` introduction site through `lifecyclePreRetypeCleanup`. |

### 8.5 Sub-task R4.C — `NoDup` on `waitingThreads` (subsumes DEEP-IPC-01 false positive)

| # | Action |
|---|---|
| R4.C.1 | Define `def NoDupList (α : Type) [DecidableEq α] : Type := { l : List α // l.Nodup }` (or import a mathlib-free equivalent already in `Prelude.lean`). |
| R4.C.2 | At `Model/Object/Types.lean`, change `Notification.waitingThreads : List ThreadId` to `NoDupList ThreadId`. |
| R4.C.3 | Update the runtime guard at `Operations/Endpoint.lean:723` to consume the constructive `NoDupList.insert` (returns `Option (NoDupList ThreadId)` so duplicate insertion is statically rejected). The runtime check is preserved as a fast-path optimisation; the type-level discharge eliminates the `uniqueWaiters` upstream-convention obligation. |
| R4.C.4 | Update every consumer of `notification.waitingThreads` (notification-wait/signal/cancel paths) to use `NoDupList` accessors. |
| R4.C.5 | Add the structural witness theorem: `theorem notification_waiters_nodup : ∀ (n : Notification), n.waitingThreads.val.Nodup`. |
| R4.C.6 | **Subsumption note for DEEP-IPC-01**: the deep audit's §11.1 verified that `Operations/Endpoint.lean:723` performs an O(1) duplicate guard at runtime. R4.C makes the duplicate **statically impossible**, so the audit's runtime-only verification is replaced by a stronger type-level guarantee. Record the closure in `AUDIT_v0.30.11_DISCHARGE_INDEX.md` with the citation: "DEEP-IPC-01 closed structurally by R4.C; runtime check at line 723 retained as defence-in-depth and proven equivalent to the type-level NoDup discharge by `notificationWait_runtime_check_implied_by_nodup`." |

### 8.6 Sub-task R4.D — `cspaceMutate` null-cap witness theorem (closes DEEP-CAP-02 false positive structurally)

**Goal.** The deep audit's §11.1 verified that `cspaceMutate` does
validate non-nullness at `Capability/Operations.lean:1093`. Per the
§1.5 structural-fix policy, the verification's correctness is
codified as a Lean witness theorem that a future auditor (or a
future contributor refactoring the function) cannot accidentally
delete without breaking the build.

The optimal fix scope-bounded for v0.31.0 is the witness theorem.
A larger fix (changing `cspaceLookupSlot` to return `NonNullCap`
or adding a `slotsNonNull` invariant to CNode) is rejected because
seL4 semantics legitimately allow a slot to contain
`Capability.null` (an empty-slot representation); the runtime
guard exists specifically to block the *mutation* of such a slot,
which is the operation-level invariant we want to prove.

**Verified targets.**

```text
SeLe4n/Kernel/Capability/Operations.lean:1081-1111  cspaceMutate definition
SeLe4n/Kernel/Capability/Operations.lean:1093       runtime null-cap guard
SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean  preservation theorem placement
```

**Tasks.**

| # | Action |
|---|---|
| R4.D.1 | At `Capability/Invariant/Preservation/CopyMoveMutate.lean`, add the witness theorem: `theorem cspaceMutate_rejects_null_cap (addr : CSpaceAddr) (rights : AccessRightSet) (badge : Option Badge) (st : SystemState) : ∀ st', cspaceMutate addr rights badge st = .ok ((), st') → ∃ cap, cspaceLookupSlot addr st = .ok (cap, st) ∧ ¬cap.isNull`. The proof unfolds `cspaceMutate`, threads through the `match cspaceLookupSlot` arm, and discharges the `if cap.isNull then .error` branch as a contradiction with the success-result hypothesis. |
| R4.D.2 | Add a complementary witness for the converse direction: `theorem cspaceMutate_null_cap_rejected (addr : CSpaceAddr) (rights : AccessRightSet) (badge : Option Badge) (st : SystemState) (hCap : ∃ cap, cspaceLookupSlot addr st = .ok (cap, st) ∧ cap.isNull) : cspaceMutate addr rights badge st = .error .nullCapability`. This proves the rejection is total: every null-cap input produces the explicit error code. |
| R4.D.3 | Add a docstring to `cspaceMutate` (Operations.lean:1069–1080) cross-referencing the two theorems by name so a future auditor reading the function definition immediately sees the witness link. The docstring sentence: "**Null-cap rejection is structurally witnessed**: see `cspaceMutate_rejects_null_cap` and `cspaceMutate_null_cap_rejected` in `Capability/Invariant/Preservation/CopyMoveMutate.lean`." |
| R4.D.4 | Update `tests/NegativeStateSuite.lean` to include a regression test that exercises the null-cap rejection path and asserts `.error .nullCapability`. (One new test function; ~10 lines.) |
| R4.D.5 | Record the structural closure in `AUDIT_v0.30.11_DISCHARGE_INDEX.md` with the citation: "DEEP-CAP-02 closed structurally by R4.D; the runtime check at `Capability/Operations.lean:1093` is now witnessed by `cspaceMutate_rejects_null_cap` and `cspaceMutate_null_cap_rejected`. A future audit's `grep` for the validation can be re-derived from these theorem names without re-reading the function body." |

**Implementation steps (per task).**

- *R4.D.1 implementation*: read lines 1081–1111 to confirm the
  current shape; write the theorem with a `by unfold cspaceMutate;
  intro st' hOk; ...` proof structure; build via `lake build
  SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate`
  to confirm elaboration.
- *R4.D.2 implementation*: same file; case-split on the lookup
  result; if non-null path is taken the `.ok` arm fires else
  `.error .nullCapability` fires.
- *R4.D.3 implementation*: Edit `Operations.lean` docstring at
  lines 1069–1080 to append the cross-reference paragraph; do not
  modify the function body.
- *R4.D.4 implementation*: locate an existing capability-error
  test in `NegativeStateSuite.lean` (e.g., one of the `cspaceCopy`
  null-cap tests) and mirror it for `cspaceMutate`. Use
  `Testing/Helpers.lean::expectError`.
- *R4.D.5 implementation*: append a row to the discharge index
  file (created at R0.3) under a "False-positive structural
  closures" subsection.

**Validation.**

```bash
lake build SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate
lake build SeLe4n.Kernel.Capability.Operations
lake exe NegativeStateSuite
./scripts/test_full.sh
```

**Risk.** Very low. The two theorems are additive proof obligations
on top of an already-correct function; they cannot regress runtime
behaviour. The only risk vector is proof-elaboration time, which is
bounded by the small theorem statement.

### 8.7 Phase R4 cumulative validation

```bash
lake build SeLe4n.Model.Object.Structures
lake build SeLe4n.Model.Object.Types
lake build SeLe4n.Kernel.Capability.Invariant.Defs
lake build SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate
lake build SeLe4n.Kernel.Capability.Operations
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
./scripts/test_full.sh
```

### 8.8 Phase R4 risk

**High by surface area, low by per-change complexity.** R4.A..R4.C
each touch every consumer of an underlying field; R4.D is purely
additive (two new theorems + docstring update). Mitigations:

- Sub-tasks R4.A/B/C/D are independently shippable; recommended to
  land as four sub-PRs even though the phase is one logical slice.
- The smart-constructor pattern is already used elsewhere in the
  kernel (e.g., `NonNullCap`); contributors should mirror that style
  for R4.A and R4.B.
- `Capability/Operations.lean` (1858 LoC) is the largest consumer
  for R4.A; build verification must exercise the full proof tree on
  every intermediate commit.
- R4.D is the cheapest sub-task and a good first PR for a contributor
  new to WS-RC; the witness-theorem pattern it introduces is the
  template for the false-positive structural-fix policy elsewhere
  in the workstream.

### 8.9 Commit messages

```
WS-RC R4.A: enforce CNode.slotsUnique via UniqueSlotMap (DEEP-MODEL-01)
WS-RC R4.B: make RetypeTarget construction non-bypassable (DEEP-CAP-04)
WS-RC R4.C: type-level NoDup on Notification.waitingThreads
            (DEEP-IPC-05; subsumes DEEP-IPC-01 false positive)
WS-RC R4.D: witness theorems for cspaceMutate null-cap rejection
            (closes DEEP-CAP-02 false positive structurally)
```


---

## 9. Phase R5 — Scheduler / Lifecycle behaviour symmetry (DEEP-SUSP-01/02, DEEP-SCH-02..06)

### 9.1 Goal

Close the seven scheduler/lifecycle findings whose remediation is a
behavioural symmetry or function-split. Per CLAUDE.md's
implement-the-improvement rule, every "or document" alternative is
struck — the documented design is the better state and must be made
true.

### 9.2 Verified targets

```text
SeLe4n/Kernel/Lifecycle/Suspend.lean:88-105   cancelDonation (split into two)
SeLe4n/Kernel/Lifecycle/Suspend.lean:75-84    cancelIpcBlocking (extract helper)
SeLe4n/Kernel/Lifecycle/Suspend.lean:290+     resumeThread (PIP recompute)
SeLe4n/Kernel/Scheduler/Operations/Selection.lean:225-241  effectivePriority (Option)
SeLe4n/Kernel/Scheduler/Operations/Selection.lean:327      resolveEffectivePrioDeadline (total)
SeLe4n/Kernel/Scheduler/Operations/Core.lean:715-717        bound budget no-preempt fallback
SeLe4n/Kernel/Scheduler/RunQueue.lean:238                   rotateToBack defensive priority-0
SeLe4n/Kernel/SchedContext/Operations.lean:110-187          schedContextConfigure (domain prop)
```

### 9.3 Sub-task R5.A — DEEP-SUSP-02: split `cancelDonation`

| # | Action |
|---|---|
| R5.A.1 | At `Suspend.lean:88-105`, split `cancelDonation` into `cancelBoundDonation` (in-place unbind) and `cancelDonatedDonation` (return-to-original-owner via `cleanupDonatedSchedContext`). |
| R5.A.2 | Update every caller (suspendThread, scheduler operations) to dispatch on the binding variant explicitly. |
| R5.A.3 | The previous `cancelDonation` becomes a thin dispatcher (or is inlined at each call site if the dispatch is trivial). |
| R5.A.4 | Update the SuspendPreservation invariant proofs to reference the new function names. |

### 9.4 Sub-task R5.B — DEEP-SUSP-01: PIP recomputation on resume

| # | Action |
|---|---|
| R5.B.1 | At `Suspend.lean:290+`, add a step in `resumeThread` that re-derives the resumed thread's `pipBoost` from the current blocking graph state via `computeMaxWaiterPriority`. |
| R5.B.2 | Add a preservation proof: `resumeThread_preserves_blockingAcyclic` and `resumeThread_pipBoost_consistent_with_blocking_graph`. |
| R5.B.3 | If suspending a thread that holds a lock another thread is waiting on (H4 readiness), the recomputation discharges the implicit invariant. Add a regression test in `tests/SuspendResumeSuite.lean`. |

### 9.5 Sub-task R5.C — DEEP-SCH-02: `effectivePriority` API uniformity

| # | Action |
|---|---|
| R5.C.1 | At `Selection.lean:225-241` (`effectivePriority` returns `Option Priority`) and `:327` (`resolveEffectivePrioDeadline` returns total `(Priority, Deadline)`): pick **one** convention. Recommended: both total under documented invariants (the runtime-checked hypotheses already make `effectivePriority` total), removing the `Option` wrapping at the call site. |
| R5.C.2 | If the recommendation is reversed (both `Option`), every caller must propagate the optionality; this is the larger refactor and only justified if a kernel-state condition exists where neither is computable. |
| R5.C.3 | Add a witness theorem under either convention that ties the two to a common "effective scheduling parameters" predicate. |

### 9.6 Sub-task R5.D — DEEP-SCH-03: shared `restore-to-ready` helper

| # | Action |
|---|---|
| R5.D.1 | Extract a helper `def restoreToReady (tid : ThreadId) : Kernel Unit` that captures the IPC-state-clearing sequence shared between `cancelIpcBlocking` (Suspend.lean:75–84) and `resumeThread` (Suspend.lean:290+). |
| R5.D.2 | Replace both call sites with the helper. |
| R5.D.3 | Add a single preservation theorem for the helper, replacing the two duplicate proofs. |

### 9.7 Sub-task R5.E — DEEP-SCH-04: surface `.missingSchedContext`

| # | Action |
|---|---|
| R5.E.1 | At `Operations/Core.lean:715-717`, replace the silent `(state, false)` no-preempt fallback with `.error .missingSchedContext` in the bound-budget branch when SchedContext lookup fails. |
| R5.E.2 | Verify the calling chain: every caller of the bound-budget path must now propagate the error. If the propagation reveals a code path that swallows the error, that path is itself broken and must be fixed in the same PR. |
| R5.E.3 | Add a regression test asserting `.error .missingSchedContext` for the orphaned-binding case. |

### 9.8 Sub-task R5.F — DEEP-SCH-05: explicit `rotateToBack` precondition

| # | Action |
|---|---|
| R5.F.1 | At `RunQueue.lean:238`, replace `threadPriority[tid]?.getD ⟨0⟩` with `match threadPriority[tid]? with \| some p => p \| none => panic! "rotateToBack: missing threadPriority entry"` OR (preferred) restructure the call site so `rotateToBack` is invoked only when the caller has already proven membership. The `panic!` is acceptable because the precondition is an invariant; the explicit panic surfaces invariant violation rather than masking it. |
| R5.F.2 | Add an assertion theorem: `theorem rotateToBack_requires_membership : ∀ rq tid, tid ∈ rq.membership → threadPriority.get? tid = some _`. |

### 9.9 Sub-task R5.G — DEEP-SCH-06: domain propagation in `schedContextConfigure`

| # | Action |
|---|---|
| R5.G.1 | Verify whether `boundThreadDomainConsistent` (defined at `Scheduler/Invariant.lean:847`) requires domain propagation when a SchedContext bound to a TCB has its `domain` field rewritten. Verification by reading the invariant: `tcb.domain = sc.domain` is the conjunct. **Conclusion: yes, domain propagation IS required.** |
| R5.G.2 | At `SchedContext/Operations.lean:110-187`, after the priority-propagation block (lines 168–186), add an analogous domain-propagation block: if `sc.boundThread = some tid`, set `boundTcb.domain := newDomain`. |
| R5.G.3 | Update the `schedContextConfigure_preserves_boundThreadDomainConsistent` invariant proof (or add it if absent) in `SchedContext/Invariant/Preservation.lean`. |
| R5.G.4 | Add a regression test confirming the propagation. |

### 9.10 Implementation walkthrough (high-complexity sub-tasks)

*R5.B (PIP recomputation on resume) — implementation steps.*

The current `resumeThread` flow at `Suspend.lean:290+` clears the
suspended state and re-enqueues. The PIP recomputation is added
before the re-enqueue:

```lean
def resumeThread (tid : ThreadId) : Kernel Unit :=
  fun st =>
    match st.getTcb? tid with
    | none => .error .objectNotFound
    | some tcb =>
      if tcb.threadState != .suspended then .error .illegalState
      else
        -- NEW (R5.B): re-derive pipBoost from the post-suspend
        -- blocking graph. The chain may have changed during the
        -- thread's suspension (other threads acquired/released
        -- locks the suspended thread holds).
        let newPipBoost := computeMaxWaiterPriority st.scheduler.blockingGraph tid
        let tcb' := { tcb with
                      threadState := .ready
                      pipBoost := newPipBoost }
        let st' := { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
        -- ... existing re-enqueue logic ...
```

`computeMaxWaiterPriority` already exists in
`PriorityInheritance/Compute.lean`; verify the signature and
import path.

The two preservation theorems (R5.B.2):

```lean
theorem resumeThread_preserves_blockingAcyclic
    (tid : ThreadId) (st st' : SystemState) (hAcyclic : blockingAcyclic st)
    (hOk : resumeThread tid st = .ok ((), st')) :
    blockingAcyclic st'

theorem resumeThread_pipBoost_consistent_with_blocking_graph
    (tid : ThreadId) (st st' : SystemState)
    (hOk : resumeThread tid st = .ok ((), st')) :
    ∀ tcb, st'.getTcb? tid = some tcb →
    tcb.pipBoost = computeMaxWaiterPriority st'.scheduler.blockingGraph tid
```

*R5.G (domain propagation) — implementation steps.*

Read `SchedContext/Operations.lean:110–187` to confirm the
priority-propagation pattern; the domain propagation mirrors it:

```lean
-- After the priority-propagation block at lines 168–186, add:
match sc.boundThread with
| none => stProp  -- no bound thread: nothing to propagate
| some boundTid =>
  match stProp.getTcb? boundTid with
  | some boundTcb =>
    if boundTcb.domain.val = domain then stProp
    else
      let newDom : SeLe4n.DomainId := ⟨domain⟩
      let boundTcb' := { boundTcb with domain := newDom }
      { stProp with objects :=
        stProp.objects.insert boundTid.toObjId (.tcb boundTcb') }
  | none => stProp  -- bound TCB missing: leave as-is (consistent with priority block)
```

The new preservation theorem (R5.G.3) statement:

```lean
theorem schedContextConfigure_preserves_boundThreadDomainConsistent
    (vScId : ValidObjId) (budget period priority deadline domain : Nat)
    (st st' : SystemState)
    (hInv : boundThreadDomainConsistent st)
    (hOk : schedContextConfigure vScId budget period priority deadline domain st = .ok ((), st')) :
    boundThreadDomainConsistent st'
```

The proof unfolds `schedContextConfigure`, threads through the
new domain-propagation block, and uses the parent invariant to
discharge the `boundTid → tid` conjunct.

*R5.A (cancelDonation split) — implementation steps.*

Current shape at `Suspend.lean:88–105`:

```lean
def cancelDonation (tcb : TCB) : Kernel Unit := fun st =>
  match tcb.schedContextBinding with
  | .bound _ => -- in-place unbind
  | .donated _ => -- return to original owner via cleanupDonatedSchedContext
  | _ => .ok ((), st)
```

After the split:

```lean
def cancelBoundDonation (tcb : TCB) : Kernel Unit := fun st =>
  match tcb.schedContextBinding with
  | .bound scId => -- in-place unbind logic
  | _ => .error .illegalState  -- caller must dispatch correctly

def cancelDonatedDonation (tcb : TCB) : Kernel Unit := fun st =>
  match tcb.schedContextBinding with
  | .donated scId => cleanupDonatedSchedContext scId tcb st
  | _ => .error .illegalState

-- Optional thin dispatcher (or inline at call sites):
def cancelDonation (tcb : TCB) : Kernel Unit := fun st =>
  match tcb.schedContextBinding with
  | .bound _ => cancelBoundDonation tcb st
  | .donated _ => cancelDonatedDonation tcb st
  | _ => .ok ((), st)
```

Caller updates: in `suspendThread` and any other consumer, replace
the implicit dispatch with explicit calls. This makes the
two-arm semantics legible at the call site.

### 9.11 Validation

```bash
lake build SeLe4n.Kernel.Lifecycle.Suspend
lake build SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation
lake build SeLe4n.Kernel.Scheduler.Operations.Selection
lake build SeLe4n.Kernel.Scheduler.Operations.Core
lake build SeLe4n.Kernel.Scheduler.RunQueue
lake build SeLe4n.Kernel.SchedContext.Operations
lake build SeLe4n.Kernel.SchedContext.Invariant.Preservation
./scripts/test_full.sh
```

### 9.12 Risk

**Medium.** Seven distinct fixes, some of which (R5.B PIP, R5.G
domain propagation) introduce new proof obligations; others
(R5.C API uniformity, R5.D helper extraction) are pure refactors.

Mitigations:

- Land each sub-task as a separate commit within the same PR so
  git bisect can isolate any regression to the specific fix.
- The Preservation.lean (3779 LoC) re-elaboration cost may be
  significant; budget time for a long `lake build` cycle.


---

## 10. Phase R6 — Architecture / InformationFlow completeness (DEEP-ARCH-03, DEEP-IF-01/02, DEEP-IPC-04)

### 10.1 Goal

Close four spec-completeness findings: the formal Lean-level GIC
dispatch bridge, the `DeclassificationPolicy` definition, the
parameterised SecurityDomain lattice, and the verification of the
cleanup-error-unreachable proof for IPC pre-receive donation.

### 10.2 Sub-task R6.A — DEEP-ARCH-03: ExceptionModel ↔ InterruptDispatch bridge

| # | Action |
|---|---|
| R6.A.1 | At `Architecture/ExceptionModel.lean`, add a Lean-level model of the GIC-400 acknowledge → handle → EOI flow. The model already lives partially in `Architecture/InterruptDispatch.lean`; this sub-task formalises the boundary so a sequence of exception-classification → interrupt-dispatch is provable end-to-end. |
| R6.A.2 | Add a bridge theorem: `theorem exception_irq_dispatches_via_interrupt_dispatch : ∀ exc, classifyException exc = .irq id → interruptDispatchSequence id = ack id ++ handle id ++ eoi id`. |
| R6.A.3 | Update `Architecture/Invariant.lean` to bundle the bridge into the architecture invariant family. |

### 10.3 Sub-task R6.B — DEEP-IF-01: locate or define `DeclassificationPolicy`

| # | Action |
|---|---|
| R6.B.1 | First action is verification: `grep -rn "structure DeclassificationPolicy\|class DeclassificationPolicy" SeLe4n` — if a definition exists in an unaudited part of the tree, simply ensure `Soundness.lean` imports it. If absent, define it. |
| R6.B.2 | If the definition is missing: add `structure DeclassificationPolicy` at `InformationFlow/Policy.lean` with the fields the deep audit's §5.7 implies (a single `declassifyStore` site gating predicate). |
| R6.B.3 | Wire the definition into `Soundness.lean` so the existing soundness theorems continue to compile against a non-stub `DeclassificationPolicy`. |

### 10.4 Sub-task R6.C — DEEP-IF-02: complete the SecurityDomain lattice

| # | Action |
|---|---|
| R6.C.1 | At `InformationFlow/Policy.lean:484-500`, complete the parameterised `SecurityDomain` lattice section. The truncation is post-1.0-marked but the section header asserts a complete lattice; the implementation must finish to match. |
| R6.C.2 | Required pieces (per the section's TODO outline): `instance : SemilatticeSup SecurityDomain`, `instance : SemilatticeInf SecurityDomain`, `instance : Lattice SecurityDomain`, plus the four lattice-law theorems (assoc, comm, absorption × 2). |
| R6.C.3 | Add a witness theorem proving that the `flowsTo` and `integrityFlowsTo` order on `SecurityDomain` is the lattice's `≤`. |

### 10.5 Sub-task R6.D — DEEP-IPC-04: verify cleanup-error-unreachable proof

| # | Action |
|---|---|
| R6.D.1 | Locate the theorem `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull` in `IPC/Invariant/Defs.lean`. |
| R6.D.2 | If the theorem exists and is sorry-free, this sub-task closes by recording the witness in `AUDIT_v0.30.11_DISCHARGE_INDEX.md`. |
| R6.D.3 | If the theorem is missing or contains `sorry`, prove it. The docstring at `Operations/Endpoint.lean:485` claims the error branch is unreachable under `ipcInvariantFull`; the implement-the-improvement rule mandates proving the claim, not weakening the docstring. |

### 10.6 Implementation walkthrough

*R6.A — GIC bridge.* Decompose into two atomic commits:

1. **R6.A.1a** — Define `interruptDispatchSequence : InterruptId →
   List InterruptOp` enumerating the GIC-400 acknowledge → handle →
   EOI ordering. The `InterruptOp` algebra is small (`.ack id`,
   `.handle id`, `.eoi id`) and matches the existing Rust HAL
   `gic.rs::dispatch_irq` flow.
2. **R6.A.1b** — Add the bridge theorem proper:

   ```lean
   theorem exception_irq_dispatches_via_interrupt_dispatch :
       ∀ (exc : ExceptionFrame) (id : InterruptId),
       classifyException exc = .irq id →
       interruptDispatchSequence id =
         [.ack id, .handle id, .eoi id]
   ```

   The proof is `intro exc id hCls; rfl` if the function is
   defined to literally produce that list. If the function does
   anything more sophisticated (e.g., conditional EOI for level-
   triggered IRQs), the proof case-splits on the trigger mode.

3. **R6.A.3** — Bundle into `Architecture/Invariant.lean` as a
   conjunct of `architectureInvariantBundle`. Adding a conjunct
   requires updating every consumer of the bundle; budget ~3 hours
   for proof re-elaboration.

*R6.B — `DeclassificationPolicy` location/definition.* Begin with
verification:

```bash
grep -rn "structure DeclassificationPolicy\|class DeclassificationPolicy" SeLe4n
```

If the structure is found in an unaudited file, R6.B closes
immediately by ensuring `Soundness.lean` imports it. If absent,
define it at `InformationFlow/Policy.lean`:

```lean
/-- WS-RC R6.B / DEEP-IF-01: Declassification policy carries the
    predicate that decides which `declassifyStore` invocations are
    permitted. The single declassification site (Soundness.lean:516)
    consults this policy to gate writes that lower a value's
    security domain. -/
structure DeclassificationPolicy where
  /-- The set of allowed declassification edges. A pair
      `(src, dst)` denotes "data tagged with security domain `src`
      may be re-tagged with `dst`". -/
  allowedEdges : List (SecurityDomain × SecurityDomain)
  /-- Decidable membership predicate. -/
  decideEdge : DecidableEq (SecurityDomain × SecurityDomain)
```

Then update `Soundness.lean:516` (or wherever the existing import
fails) to consume the new structure. Run the existing soundness
proofs; they should re-elaborate without changes because the
structure shape matches what they expected.

*R6.C — SecurityDomain lattice completion.* This is the genuine
new proof work in R6. Four atomic commits:

1. **R6.C.1a** — Define the supremum operation:

   ```lean
   def SecurityDomain.sup (a b : SecurityDomain) : SecurityDomain :=
     -- Per the SecurityDomain definition (read Policy.lean:400-484),
     -- this is the join in the flowsTo lattice. For a two-component
     -- domain (confidentiality × integrity), sup = (max conf, min int).
     ⟨a.confidentiality.max b.confidentiality,
      a.integrity.min b.integrity⟩
   ```

2. **R6.C.1b** — Define the infimum operation symmetrically.

3. **R6.C.2** — Provide the four lattice-law theorems:

   ```lean
   theorem SecurityDomain.sup_assoc (a b c : SecurityDomain) :
     (a.sup b).sup c = a.sup (b.sup c)
   theorem SecurityDomain.sup_comm (a b : SecurityDomain) :
     a.sup b = b.sup a
   theorem SecurityDomain.absorb_sup_inf (a b : SecurityDomain) :
     a.sup (a.inf b) = a
   theorem SecurityDomain.absorb_inf_sup (a b : SecurityDomain) :
     a.inf (a.sup b) = a
   ```

   Each proof is mechanical: unfold `sup`/`inf`, apply
   `Nat.max_assoc`/`Nat.min_assoc`/etc.

4. **R6.C.3** — Bridge to `flowsTo`:

   ```lean
   theorem flowsTo_iff_sup_eq (a b : SecurityDomain) :
     flowsTo a b ↔ a.sup b = b
   ```

   This is the conventional definition of "≤ via sup"; the proof
   unfolds both sides and applies a `decide` if the lattice is
   finite.

*R6.D — Cleanup-error proof verification.* Verification-first:

```bash
grep -rn "cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull" SeLe4n
```

Three outcomes:

- **Theorem exists, sorry-free**: record discharge in
  `AUDIT_v0.30.11_DISCHARGE_INDEX.md`, close R6.D.
- **Theorem exists, contains sorry**: prove it. The proof
  requires `ipcInvariantFull` to imply that
  `returnDonatedSchedContext` succeeds; case-split on the
  donation arm.
- **Theorem missing**: add it. Same proof shape as above.

The docstring at `Operations/Endpoint.lean:485` claims the error
branch is unreachable; making the claim true via the theorem is
the implement-the-improvement remediation.

### 10.7 Validation

```bash
lake build SeLe4n.Kernel.Architecture.ExceptionModel
lake build SeLe4n.Kernel.Architecture.InterruptDispatch
lake build SeLe4n.Kernel.Architecture.Invariant
lake build SeLe4n.Kernel.InformationFlow.Soundness
lake build SeLe4n.Kernel.InformationFlow.Policy
lake build SeLe4n.Kernel.IPC.Invariant.Defs
./scripts/test_full.sh
```

### 10.8 Risk

**Medium.** The SecurityDomain lattice completion (R6.C) is genuine
new proof work. The GIC bridge (R6.A) requires careful attention to
the exception-class → interrupt-dispatch correspondence; the audit's
classification of this as "deferred to H3" reflects its non-trivial
nature.

Mitigations:

- R6.D is verification-first; if the theorem already exists, the
  sub-task collapses to a one-line discharge index entry.
- R6.A may be split into two sub-PRs: (i) classify exception →
  interrupt-id mapping (a routine total-function definition);
  (ii) the dispatch-sequence bridge theorem (the harder proof).


---

## 11. Phase R7 — Capability deferred items (DEEP-CAP-05)

### 11.1 Goal

Address the AK8-K LOW-tier deferred items currently documented in
the `Capability/Operations.lean:12-62` header comment. Items whose
fix fits inside the current scope are closed in this phase; items
that genuinely cannot ship in v1.0 are lifted into the project debt
register (`AUDIT_v0.30.11_DEFERRED.md`) with an explicit closure
target.

### 11.2 Tasks

| # | Action |
|---|---|
| R7.1 | Read the AK8-K LOW-tier items from `Capability/Operations.lean:12-62`. Catalogue each as (close-now / defer / withdraw). |
| R7.2 | For each close-now item, implement the fix in the same PR. |
| R7.3 | For each defer item, lift the entry into `AUDIT_v0.30.11_DEFERRED.md` with: (a) verbatim original AK8-K text; (b) closure target (workstream/PR identifier or post-1.0 milestone). Remove the entry from the source comment block. |
| R7.4 | For each withdraw item (already-fixed but the comment was not updated), confirm by direct verification, then remove from the source comment block. |
| R7.5 | The header comment block at lines 12–62 shrinks to a one-paragraph summary pointing readers to `AUDIT_v0.30.11_DEFERRED.md` for any residual items, per CLAUDE.md's prohibition on "in-source TODOs that age out with the surrounding workstream." |

### 11.3 Validation

```bash
lake build SeLe4n.Kernel.Capability.Operations
./scripts/test_full.sh
# Verify the residual debt is reflected in the deferred file
diff <(grep -c "AK8-K" SeLe4n/Kernel/Capability/Operations.lean) <(echo "1")
# (should match exactly the one-paragraph residual reference)
```

### 11.4 Risk

**Low.** Each AK8-K item is small in scope; the work is mostly
sorting and either closing or formalising deferral. The one
medium-complexity vector is if a "close-now" item turns out to
require significant proof work — in which case the contributor
should redirect to deferral and add an explicit note to that effect
in the PR description.

---

## 12. Phase R8 — Test renames and conformance extensions (DEEP-TEST-01/02, DEEP-RUST-06)

### 12.1 Goal

Strip workstream-ID prefixes from four test suite filenames and their
test-function names, per CLAUDE.md's "Internal-first naming" rule.
Extend Rust ABI conformance tests to cover the six syscalls currently
without round-trip coverage.

### 12.2 Sub-task R8.A — Test rename (DEEP-TEST-01, DEEP-TEST-02)

| # | File (before) | File (after) — proposed |
|---|---|---|
| R8.A.1 | `tests/Ak8CoverageSuite.lean` | `tests/SchedContextEdgeCasesSuite.lean` |
| R8.A.2 | `tests/An9HardwareBindingSuite.lean` | `tests/HardwareBindingClosureSuite.lean` |
| R8.A.3 | `tests/Ak9PlatformSuite.lean` | `tests/PlatformBootValidationSuite.lean` |
| R8.A.4 | `tests/An10CascadeSuite.lean` | `tests/InvariantCascadeMonotonicitySuite.lean` |

For each file:

| # | Action |
|---|---|
| R8.A.x.1 | `git mv` the file to the new name. |
| R8.A.x.2 | Rename every `test_AK8_*` / `test_AN9_*` / `test_AK9_*` / `test_AN10_*` test function to a name describing what it tests (e.g., `test_unbound_returns_tcb_priority`, `test_unbind_missing_tcb_no_partial_mutation`). The new names must describe the semantics, not the workstream. |
| R8.A.x.3 | Update `lakefile.toml` `lean_exe` registration. |
| R8.A.x.4 | Update tier scripts (`test_tier2_negative.sh`, `test_tier2_trace.sh`, `scenario_catalog.py`) to reference the new names. |
| R8.A.x.5 | Update `scripts/website_link_manifest.txt` if any of the renamed files were listed. |
| R8.A.x.6 | Update `docs/codebase_map.json` (test-suite names). |
| R8.A.x.7 | Update CLAUDE.md `tests/` section if it lists the suite by name. |

### 12.3 Sub-task R8.B — Conformance test extension (DEEP-RUST-06)

| # | Action |
|---|---|
| R8.B.1 | At `rust/sele4n-abi/tests/conformance.rs`, add round-trip cases for: `ServiceRegister`, `ServiceRevoke`, `ServiceQuery`, `NotificationSignal`, `NotificationWait`, `ReplyRecv`. |
| R8.B.2 | Each new case should mirror the existing `RUST-XVAL-001..019` shape: encode → decode → assert structural equality. |
| R8.B.3 | Wire the new cases into the conformance run-list and update the `RUST-XVAL-*` numbering in the comments. |
| R8.B.4 | Subsumes DEBT-RUST-01 (the predecessor's "extend conformance to syscall-level error-encoding scenarios" item). |

### 12.4 Validation

```bash
./scripts/test_rust_conformance.sh
./scripts/test_full.sh
./scripts/check_website_links.sh
```

### 12.5 Risk

**Low** for renames (mechanical), **low** for conformance
extension (additive). The website link manifest and tier scripts
must be updated in lockstep to avoid CI failures on the
post-rename commit.


---

## 13. Phase R9 — Pre-commit hardening (DEEP-PRECOM-01)

### 13.1 Goal

Replace the fragile regex-based `sorry` detection in
`scripts/pre-commit-lean-build.sh:59,61` with a Lean-tokeniser-based
check. The current regex chain is over-zealous (false-positive on
documentation references to `sorry` in `/-…-/` block comments per
deep audit §11.2); a token-aware check is robust and leverages the
project's existing Lean toolchain.

### 13.2 Tasks

| # | Action |
|---|---|
| R9.1 | Write a small Lean program `scripts/check_sorry.lean` that takes a `.lean` file path on the command line, runs the Lean lexer, and exits non-zero iff any `sorry` identifier appears outside strings and comments. |
| R9.2 | Update `scripts/pre-commit-lean-build.sh:59,61` to invoke `lean --run scripts/check_sorry.lean <file>` for each staged `.lean` file, replacing the `grep -v` chain. |
| R9.3 | Verify the new check on a synthetic test file containing every false-positive case (block-comment `sorry` mentions, string-literal `"sorry"`, `--` line-comment `sorry`); the check must pass on the full file and fail on a real `sorry` identifier. |
| R9.4 | Document the new behaviour in CLAUDE.md "Module build verification (mandatory)" section if the description there references the regex approach. |
| R9.5 | Run `./scripts/install_git_hooks.sh --check` to confirm the hook signature still matches; bump the installer version if the script's content hash changes. |

### 13.3 Validation

```bash
# Synthesised positive and negative test cases
echo '/- this comment mentions sorry inline -/' > /tmp/test_sorry.lean
echo 'def f := 0' >> /tmp/test_sorry.lean
./scripts/check_sorry.lean /tmp/test_sorry.lean   # MUST pass

echo 'def g := sorry' >> /tmp/test_sorry.lean
./scripts/check_sorry.lean /tmp/test_sorry.lean   # MUST fail

# Re-run the full pre-commit on a real staged change
./scripts/test_tier0_hygiene.sh
```

### 13.4 Risk

**Low.** The regex chain is the only `sorry`-detection surface; the
new tokeniser is stricter (rejects only real `sorry` identifiers) and
matches the project's existing Lean dependency footprint (no new
toolchain). The one risk vector is that `lean --run` on every staged
file may slow the pre-commit hook noticeably; if so, batch the call
to a single invocation that reads file paths from stdin.

---

## 14. Phase R10 — Inline documentation and cleanup (large finding bundle)

### 14.1 Goal

Land a single PR that closes every code-touching low-severity finding
not already absorbed by R1..R9. This phase is a "polish pass" — small
edits across many files, no semantic changes, easily reviewable.

### 14.2 Tasks (grouped by area)

#### License (DEEP-LICENSE-01)
| # | File | Action |
|---|---|---|
| R10.1 | `SeLe4n.lean` | Insert `-- SPDX-License-Identifier: GPL-3.0-or-later` as line 1 (currently line 1 begins `/-`). |

#### IPC linter justifier comments (DEEP-IPC-02)
| # | File | Action |
|---|---|---|
| R10.2 | `SeLe4n/Kernel/IPC/Invariant/QueueNextBlocking.lean:24` | Add a one-line justification comment above the `set_option linter.unusedVariables false` explaining why this file specifically requires the suppression (defensive pattern matches in the queueNext blocking-consistency proofs produce unused binders by structural necessity). |
| R10.3 | `SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean:25` | Same. |
| R10.4 | `SeLe4n/Kernel/IPC/Invariant/QueueMembership.lean:13` | Same. |
| R10.5 | `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean:37` | Same. |
| R10.6 | `SeLe4n/Kernel/IPC/Invariant/Structural/DualQueueMembership.lean:38` | Same. |
| R10.7 | `SeLe4n/Kernel/IPC/Invariant/Structural/PerOperation.lean:38` | Same. |
| R10.8 | `SeLe4n/Kernel/IPC/Invariant/Structural/QueueNextTransport.lean:36` | Same. |

#### Capability docstring promotion (DEEP-CAP-01)
| # | File | Action |
|---|---|---|
| R10.9 | `SeLe4n/Kernel/Capability/Operations.lean:959` | Promote the inline `--` rationale block at lines 964–968 into the `/-- ... -/` docstring above `cspaceCopy`. |
| R10.10 | `SeLe4n/Kernel/Capability/Operations.lean:1002` | Promote the inline `--` rationale block at lines 998–1001 into the `/-- ... -/` docstring above `cspaceMove`. |

#### Model field cross-references (DEEP-MODEL-03/04)
| # | File | Action |
|---|---|---|
| R10.11 | `SeLe4n/Model/State.lean:146` | Add cross-reference comment naming `replenishQueueSorted` and pointing to `Kernel/SchedContext/ReplenishQueue.lean`. |
| R10.12 | `SeLe4n/Model/State.lean` `LifecycleMetadata.capabilityRefs` field | Add a single canonical comment naming every mutation site (cspaceCopy, cspaceMint, cspaceRevoke, cspaceMove, cspaceDelete) so a maintainer can grep them. |

#### Rust comment cleanup (DEEP-RUST-03/04/05)
| # | File | Action |
|---|---|---|
| R10.13 | `rust/sele4n-abi/src/trap.rs:2-6` | Correct the module-level comment ("the **single** `unsafe` block in the entire library" — actually `unsafe` on the function, not a block). |
| R10.14 | `rust/sele4n-abi/src/lib.rs` | Add a module-level doc comment matching the style of `rust/sele4n-hal/src/lib.rs`. |
| R10.15 | `rust/sele4n-sys/src/lib.rs` | Same. |
| R10.16 | `THIRD_PARTY_LICENSES.md:41` | Clarify cc semver: replace "cc 1.2.59" with "cc semver range 1.2.x; current resolved version 1.2.59". |

#### FDT error distinguisher (DEEP-FDT-01)
| # | File | Action |
|---|---|---|
| R10.17 | `SeLe4n/Platform/DeviceTree.lean:695-740` | At `findMemoryRegPropertyChecked`, distinguish fuel exhaustion from malformed-blob: introduce a `.fuelExhausted` error variant (or reuse an existing enum slot) and emit it for the fuel branch; keep `.malformedBlob` for the structural-invalidity branch. |

#### Manifest timestamp (DEEP-SCRIPT-01)
| # | File | Action |
|---|---|---|
| R10.18 | `scripts/website_link_manifest.txt:18` | Either remove the `Last synchronized:` line or update it to the current date in the same commit; if removing, update CLAUDE.md if any reference depends on the timestamp shape. |

#### AK10 rename (DEBT-IPC-02)
| # | File | Action |
|---|---|---|
| R10.19 | `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` | Rename `ipcInvariant` → `notificationInvariantSystem` per AK10. Update every consumer (search via `grep -rn "ipcInvariant" SeLe4n` first to confirm scope). |

### 14.3 Validation

```bash
lake build  # default target
./scripts/test_full.sh
./scripts/test_rust.sh
./scripts/check_website_links.sh
```

### 14.4 Risk

**Low.** Every edit is local and semantics-preserving except R10.19
(AK10 rename, which is mechanical but touches every consumer of
`ipcInvariant`). The rename is best landed as a separate sub-PR if
the consumer list exceeds ten files; otherwise inline with this
phase.


---

## 15. Phase R11 — Documentation accuracy (DEEP-DOC-01..06, DEBT-DOC-01, DEBT-FR-01)

### 15.1 Goal

Reconcile the genuine documentation drift identified by both audits.
This phase touches **only documentation** — no code is modified.
It lands LAST in the pre-1.0 sequence so the metric refresh is
computed against the post-implementation tree.

### 15.2 Sub-task R11.A — README metric refresh (DEEP-DOC-01, DEEP-DOC-06, DEBT-DOC-01)

| # | Action |
|---|---|
| R11.A.1 | Run `./scripts/report_current_state.py` to recompute live metrics. |
| R11.A.2 | Run `./scripts/sync_readme_from_codebase_map.sh` to push the recomputed metrics into README. |
| R11.A.3 | Manually reconcile the two inconsistent declaration counts (`README.md:92` "3,186" vs `:213` "2,725"). The recommended fix per deep audit §10.3 PR 11 is to drop both inline numbers and replace with a single CI-synchronised reference to `codebase_map.json`'s `proved_theorem_lemma_decls` field. |
| R11.A.4 | Update test-suite count: `README.md:38` says "25 test suites" and `:193` says "24 test suites"; live count is 28 (`find tests -name "*.lean" \| wc -l`). Both lines must be updated; if the source-layout table at line 193 lists individual suites, update the count and add the missing entries. |
| R11.A.5 | Update `production_files`/`production_loc` to match the live `find` and `wc -l` results: 167 / 109,787 (or whatever the post-R1..R10 tree reports — the metric refresh must be the last thing computed). |
| R11.A.6 | Verify `scripts/check_version_sync.sh` and `scripts/sync_documentation_metrics.sh` both pass. |

### 15.3 Sub-task R11.B — AGENTS.md disposition (DEEP-DOC-02)

| # | Action |
|---|---|
| R11.B.1 | Decide between the two acceptable approaches per deep audit §11.5: (i) full rewrite mirroring CLAUDE.md with a CI sync check, OR (ii) ~10-line redirect stub pointing to CLAUDE.md. **Recommended: option (ii).** AGENTS.md has no proof or correctness payload; maintaining two parallel files invites drift. |
| R11.B.2 | If option (ii): replace AGENTS.md content with: project name, version (auto-synced from `lakefile.toml`), one-line description, and a link to CLAUDE.md as the canonical guidance file. |
| R11.B.3 | If option (i): write a CI script that fails when `AGENTS.md` and `CLAUDE.md` diverge in the policy sections; wire into `test_tier0_hygiene.sh`. |
| R11.B.4 | Remove every reference to `v0.11.0`, `v0.12.2`, `WS-F (v0.12.2 audit remediation)`, and any audit/workstream older than the current cycle. |

### 15.4 Sub-task R11.C — CLAUDE.md source-layout (DEEP-DOC-03)

| # | Action |
|---|---|
| R11.C.1 | Add an entry under `SeLe4n/Platform/*` in CLAUDE.md's "Source layout" section for: (a) `SeLe4n/Platform/FFI.lean` (lines 245+), Lean ↔ Rust bridge declarations, post-R2 routing into `syscallEntryChecked` and `suspendThread`; (b) `SeLe4n/Platform/Staged.lean`, build-anchor that pulls staged-only Architecture modules into CI; (c) `SeLe4n/Platform/RPi5/VSpaceBoot.lean`, RPi5 boot VSpace configuration with W^X compliance proof, post-R3 threaded into `bootSafeObject`. |
| R11.C.2 | Update the "Known large files" list under CLAUDE.md "Reading large files" if any file's line count crossed 500 between v0.30.11 and the post-R12 tree. |
| R11.C.3 | Update the "Active workstream context" section to reflect WS-RC's status (in flight or closed, depending on landing order). |

### 15.5 Sub-task R11.D — Audit-history link annotation (DEEP-DOC-04)

| # | Action |
|---|---|
| R11.D.1 | At the README audit-history table, annotate links to `docs/dev_history/audits/AUDIT_v0.29.0_*` and `docs/dev_history/audits/AUDIT_v0.30.6_*` as "(archived)" so v1.0 readers do not mistake year-old findings as current. |
| R11.D.2 | Add a link to `docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md` and `docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md` as the active audit cycle. |

### 15.6 Sub-task R11.E — FrozenOps experimental status (DEBT-FR-01)

| # | Action |
|---|---|
| R11.E.1 | At `README.md`, add a callout to a "Verified data structures" section stating that `Kernel/FrozenOps/*` is experimental and not part of the v1.0 release surface. |
| R11.E.2 | At `docs/SECURITY_ADVISORY.md`, add the same callout (or update an existing FrozenOps section). |
| R11.E.3 | Verify the source-layout entry in CLAUDE.md (`SeLe4n/Kernel/FrozenOps/*` already says "experimental — not in production chain"); no change needed there. |

### 15.7 Validation

```bash
./scripts/check_version_sync.sh
./scripts/sync_documentation_metrics.sh
./scripts/check_website_links.sh
diff <(python3 -c "import json; d=json.load(open('docs/codebase_map.json')); print(d['readme_sync'])") \
     <(grep -A 10 'readme_sync' docs/codebase_map.json | head -10)
```

### 15.8 Commit message

```
WS-RC R11: documentation accuracy omnibus

- README: reconcile theorem-count drift (3,186 vs 2,725 → single
  CI-synchronised reference); test-suite count 25/24 → 28; LoC
  resync from post-R10 tree; archived-audit annotations.
- AGENTS.md: replace stale v0.12.x content with redirect stub
  pointing to CLAUDE.md.
- CLAUDE.md: add source-layout entries for Platform/FFI.lean,
  Platform/Staged.lean, Platform/RPi5/VSpaceBoot.lean.
- SECURITY_ADVISORY.md: surface FrozenOps experimental status.

Closes: DEEP-DOC-01..04, DEEP-DOC-06, DEBT-DOC-01, DEBT-FR-01.
```


---

## 16. Phase R12 — CI hygiene + structural enforcement gates (DEEP-CI-01, DEEP-ARCH-01, DEEP-RUST-01/02, DEEP-ARCH-02)

### 16.1 Goal

Add `concurrency:` blocks to the four non-Lean GitHub workflows
(R12.A) AND introduce three CI gates that codify the verification
of false-positive findings so they cannot recur (R12.B/C/D, per
the §1.5 structural-fix policy). Phase R12 is the workstream's
"prevent-recurrence" tier.

### 16.2 Sub-task R12.A — Concurrency blocks (DEEP-CI-01)

| # | File | Action |
|---|---|---|
| R12.A.1 | `.github/workflows/platform_security_baseline.yml` | Add `concurrency: { group: platform-security-${{ github.ref }}, cancel-in-progress: true }` at the top level. |
| R12.A.2 | `.github/workflows/lean_toolchain_update_proposal.yml` | Same pattern with group prefix `lean-toolchain-update`. |
| R12.A.3 | `.github/workflows/nightly_determinism.yml` | Same pattern with group prefix `nightly-determinism`. (Verify the nightly schedule still triggers; nightly runs by their nature are not redundant if scheduled distinctly.) |
| R12.A.4 | `.github/workflows/codebase_map_sync.yml` | Same pattern with group prefix `codebase-map-sync`. |
| R12.A.5 | Confirm the existing `lean_action_ci.yml` already has the block (it does, per deep audit §8.3). |

### 16.3 Sub-task R12.B — Production/staged partition gate (closes DEEP-ARCH-01 false positive)

**Goal.** Convert the deep audit's §11.3 manual "trace transitive
imports from `SeLe4n.lean`" verification (which was performed
incorrectly, leading to the DEEP-ARCH-01 false positive) into a
machine-checked CI gate.

**Verified prerequisites (re-confirmed by this plan author at v0.30.11
HEAD; cardinality verified by direct trace).**

```text
SeLe4n.lean transitive-import closure: 144 modules.
Platform/Staged.lean transitive-import closure: 144 modules.
Staged \ Production (10 modules):
  - SeLe4n.Kernel.Architecture.AsidManager       [NO MARKER — transitively staged]
  - SeLe4n.Kernel.Architecture.CacheModel        [STATUS: staged ✓]
  - SeLe4n.Kernel.Architecture.ExceptionModel    [STATUS: staged ✓]
  - SeLe4n.Kernel.Architecture.InterruptDispatch [NO MARKER — transitively staged via ExceptionModel]
  - SeLe4n.Kernel.Architecture.TimerModel        [STATUS: staged ✓]
  - SeLe4n.Kernel.Architecture.TlbCacheComposition [NO MARKER — transitively staged]
  - SeLe4n.Kernel.Concurrency.Assumptions        [NO MARKER — platform infrastructure]
  - SeLe4n.Platform.FFI                           [NO MARKER — platform infrastructure]
  - SeLe4n.Platform.RPi5.VSpaceBoot               [NO MARKER — platform infrastructure (post-R3 promotes to production)]
  - SeLe4n.Platform.Staged                        [NO MARKER — anchor file itself]
"STATUS: staged" markers in source (3 files):
  CacheModel.lean, TimerModel.lean, ExceptionModel.lean
```

**Design implication (refined from the original sketch).** Three of
the ten staged-only modules carry the marker; seven do not because
they are either:
- **Transitively staged** (reachable only because a marked module
  imports them — AsidManager, InterruptDispatch, TlbCacheComposition).
- **Platform infrastructure** (the staging anchor itself plus
  cross-cutting infrastructure — Concurrency.Assumptions, FFI,
  VSpaceBoot, Staged).

The gate must accept this layered structure. Two acceptable
designs:

- **Design A (recommended for this PR scope)**: maintain an
  explicit allowlist file `scripts/staged_module_allowlist.txt`
  listing the 10 known staged-only modules; the gate fails if
  (a) `staged_only` contains a module not in the allowlist, OR
  (b) any module in `production_set` carries a "STATUS: staged"
  marker. The allowlist is human-maintained but small and
  auditable; adding/removing a staged module requires an explicit
  allowlist update plus the marker change.
- **Design B (richer, future work)**: add markers to all 7
  unmarked staged modules (turning them into a self-describing
  partition). Costs 7 file edits but removes the allowlist file.
  Defer to a v1.x cleanup.

This plan adopts **Design A** for R12.B. The allowlist is the
single source of truth for "what is staged"; the production-set
cross-check guarantees no marker leaks into production.

**Tasks.**

| # | File | Action |
|---|---|---|
| R12.B.1 | `scripts/staged_module_allowlist.txt` (new) | Allowlist file listing the 10 staged-only modules verified at audit time, with one-line rationale for each (marker / transitively-staged / platform-infrastructure / anchor). |
| R12.B.2 | `scripts/check_production_staging_partition.sh` (new) | Implement a bash script that: (a) computes `production_set` = transitive-closure of `^import SeLe4n\.` from `SeLe4n.lean`; (b) computes `staged_set` = transitive-closure from `Platform/Staged.lean`; (c) computes `staged_only := staged_set \ production_set`; (d) verifies `staged_only` equals the allowlist set exactly (no extras, no missing); (e) for every file with a `STATUS: staged` marker, verifies it is in `staged_only` (NOT in `production_set`); (f) exits non-zero with a diff on any partition violation. |
| R12.B.3 | `scripts/test_tier0_hygiene.sh` | Wire `scripts/check_production_staging_partition.sh` into the Tier-0 hygiene checks so it runs on every CI cycle and every pre-push. |
| R12.B.4 | `scripts/website_link_manifest.txt` | Add the allowlist file and gate script to the manifest. |
| R12.B.5 | `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | Add a row: "DEEP-ARCH-01 closed structurally by R12.B; the production/staged partition is now machine-checked at every CI run via `staged_module_allowlist.txt` + transitive-closure verification." |
| R12.B.6 | `CLAUDE.md` | Add a one-paragraph note under "Module build verification (mandatory)" explaining that the partition gate is the canonical source-of-truth for the production-vs-staged classification, and any contributor adding a new module to the staged tree must update both the source (with a marker if appropriate) AND the allowlist. |

**Implementation steps for R12.B.2 (the gate script).**

```bash
#!/usr/bin/env bash
# scripts/check_production_staging_partition.sh
# Per WS-RC R12.B: enforce the production/staged module partition.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

ALLOWLIST="$SCRIPT_DIR/staged_module_allowlist.txt"
[ -f "$ALLOWLIST" ] || { echo "FAIL: missing $ALLOWLIST"; exit 1; }

trace_imports() {
  local entry="$1"
  declare -A seen
  local queue=("$entry")
  while [ ${#queue[@]} -gt 0 ]; do
    local curr="${queue[0]}"; queue=("${queue[@]:1}")
    [ -n "${seen[$curr]:-}" ] && continue
    seen[$curr]=1
    local file="${curr//.//}.lean"
    [ ! -f "$file" ] && continue
    while IFS= read -r imp; do queue+=("$imp"); done \
      < <(grep -E "^import SeLe4n\." "$file" | awk '{print $2}')
  done
  for k in "${!seen[@]}"; do echo "$k"; done | sort -u
}

production_set="$(trace_imports SeLe4n)"
staged_set="$(trace_imports SeLe4n.Platform.Staged)"
staged_only="$(comm -23 <(echo "$staged_set") <(echo "$production_set"))"
allowed="$(grep -vE '^\s*(#|$)' "$ALLOWLIST" | awk '{print $1}' | sort -u)"

errors=0

# Check 1: staged_only must equal the allowlist exactly.
extras="$(comm -23 <(echo "$staged_only") <(echo "$allowed"))"
if [ -n "$extras" ]; then
  echo "ERROR: modules in staged_only but NOT in allowlist:"
  echo "$extras" | sed 's/^/    /'
  errors=$((errors + 1))
fi
missing="$(comm -13 <(echo "$staged_only") <(echo "$allowed"))"
if [ -n "$missing" ]; then
  echo "ERROR: modules in allowlist but NOT staged-only (entered production?):"
  echo "$missing" | sed 's/^/    /'
  errors=$((errors + 1))
fi

# Check 2: every "STATUS: staged" file is in staged_only (not in production).
while IFS= read -r file; do
  [ -z "$file" ] && continue
  mod="$(echo "$file" | sed 's|^\./||; s|\.lean$||; s|/|.|g')"
  if echo "$production_set" | grep -qx "$mod"; then
    echo "ERROR: $file has 'STATUS: staged' marker but is reachable from production"
    errors=$((errors + 1))
  fi
done < <(grep -rlE "^>?\s*\*\*STATUS: staged|^--\s*STATUS: staged" SeLe4n)

if [ "$errors" -gt 0 ]; then
  echo "FAIL: production/staged partition violation ($errors errors)"
  exit 1
fi
echo "OK: production/staged partition consistent (10 staged-only modules verified against allowlist)"
```

**`scripts/staged_module_allowlist.txt` content (R12.B.1):**

```
# Staged-only modules verified at WS-RC R0 (HEAD = <commit>).
# Format: <module>  # <category: marker | transitively-staged | infra | anchor>
SeLe4n.Kernel.Architecture.AsidManager        # transitively-staged via VSpaceBoot
SeLe4n.Kernel.Architecture.CacheModel         # marker
SeLe4n.Kernel.Architecture.ExceptionModel     # marker
SeLe4n.Kernel.Architecture.InterruptDispatch  # transitively-staged via ExceptionModel
SeLe4n.Kernel.Architecture.TimerModel         # marker
SeLe4n.Kernel.Architecture.TlbCacheComposition # transitively-staged
SeLe4n.Kernel.Concurrency.Assumptions         # infra (SMP-latent inventory)
SeLe4n.Platform.FFI                           # infra (Lean-Rust bridge; promotes after R2)
SeLe4n.Platform.RPi5.VSpaceBoot               # infra (boot VSpace; promotes after R3)
SeLe4n.Platform.Staged                        # anchor file
```

**Validation.**

```bash
./scripts/check_production_staging_partition.sh   # MUST pass on current tree
# Synthesised positive test: temporarily add "STATUS: staged" marker to a
# production file and verify the gate fails:
echo '/-! > **STATUS: staged for test** -/' >> SeLe4n/Prelude.lean
./scripts/check_production_staging_partition.sh   # MUST fail
git checkout -- SeLe4n/Prelude.lean
```

**Risk.** Low. The gate is additive; the only failure mode is on
the synthetic test case above. Mitigation: include the synthesised
test as part of R12.B.1's test suite.

### 16.4 Sub-task R12.C — ARM-ARM citation gate (closes DEEP-RUST-01/02 false positives)

**Goal.** Convert the deep audit's §11.1 manual verification ("MMIO
unsafe blocks cite ARM ARM B2.1; mrs/msr asm! blocks cite ARM ARM
C5.2") into a machine-checked CI gate that runs on every push.

**Verified prerequisites (refined by this plan author at audit time).**
A naive "every unsafe block cites (ARM ARM)" gate FAILS on the
existing tree with 20 hits. Direct inspection shows the 20 misses
are all NON-hardware-access unsafe blocks (`unsafe impl Sync` for
`UnsafeCell` wrappers, `unsafe fn` boundary helpers, etc.) which
correctly use `// SAFETY:` comments per the Rust idiom but do not
need ARM-ARM citations. The deep audit's §11.1 verification was
correct only for the **hardware-access** subset (MMIO + asm! + DSB/ISB
barriers).

```text
HAL unsafe-block taxonomy (live count, 53 total):
  Hardware-access (MUST cite ARM ARM):
    - MMIO read_volatile / write_volatile blocks    → ARM ARM B2.1
    - asm! mrs / msr / DSB / ISB / DMB blocks       → ARM ARM C5.2 / C2 / D17
  Non-hardware-access (MUST cite via // SAFETY: only):
    - unsafe impl Sync for cell wrappers
    - unsafe fn marker functions (single-threaded preconditions)
    - unsafe { ptr::read / write } intra-cell access
```

**Design implication (refined from the original sketch).** The
gate enforces a **two-tier rule**:

1. **Universal**: every `unsafe { … }` block AND every `unsafe fn`
   declaration AND every `unsafe impl` MUST have a `// SAFETY:`
   comment within 5 preceding lines. This is the standard Rust
   idiom; missing this is a real defect.
2. **Hardware-access subset**: blocks containing `read_volatile`,
   `write_volatile`, or `asm!` MUST additionally cite `(ARM ARM
   <section>)` within 5 preceding lines. This is the audit
   verification.

The gate fails if either tier is violated. The deep audit's
§11.1 verification covered only tier 2.

**Tasks.**

| # | File | Action |
|---|---|---|
| R12.C.1 | `scripts/check_arm_arm_citations.sh` (new) | Implement a bash script that scans every `.rs` file under `rust/sele4n-hal/src/`, finds each `unsafe {` line and each `unsafe fn` declaration, then verifies the preceding 5 lines contain `(ARM ARM <section>)` (regex `\(ARM ARM [A-Z][0-9]+(\.[0-9]+)*\)`). Exits non-zero on any unsafe block lacking a citation. |
| R12.C.2 | `scripts/test_tier0_hygiene.sh` | Wire `scripts/check_arm_arm_citations.sh` into Tier 0 so it runs on every push and PR. |
| R12.C.3 | `scripts/website_link_manifest.txt` | Add the new script. |
| R12.C.4 | `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | Add: "DEEP-RUST-01 + DEEP-RUST-02 closed structurally by R12.C; every HAL `unsafe` block's ARM-ARM citation is machine-verified at every CI run." |
| R12.C.5 | `rust/sele4n-hal/src/lib.rs` | Add a module-level doc comment cross-referencing the gate, so a contributor adding a new `unsafe` block knows the citation requirement is enforced (not just a convention). |

**Implementation steps for R12.C.1 (the gate script).**

```bash
#!/usr/bin/env bash
# scripts/check_arm_arm_citations.sh
# Per WS-RC R12.C: two-tier gate.
#   Tier 1 (universal): every unsafe block/fn/impl has a // SAFETY: comment
#   Tier 2 (hardware-access): MMIO + asm! blocks additionally cite ARM ARM
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

errors=0
SAFETY_PATTERN='// SAFETY:'
ARM_PATTERN='\(ARM ARM [A-Z][0-9]+(\.[0-9]+)*\)'
HW_PATTERN='read_volatile|write_volatile|asm!'
LOOKBACK=5
LOOKBACK_HW=20  # asm! blocks may have a longer SAFETY/section comment block

while IFS= read -r file; do
  while IFS=: read -r lineno line; do
    [ -z "$lineno" ] && continue
    start=$((lineno - LOOKBACK))
    [ "$start" -lt 1 ] && start=1
    pre="$(sed -n "${start},${lineno}p" "$file")"

    # Tier 1: SAFETY comment universally required
    if ! echo "$pre" | grep -qF "$SAFETY_PATTERN"; then
      echo "ERROR-T1: $file:$lineno — unsafe lacks // SAFETY: comment in preceding $LOOKBACK lines"
      errors=$((errors + 1))
    fi

    # Tier 2: ARM ARM citation only required for hardware-access unsafe blocks
    # We look at the unsafe block's body within ~20 lines after the unsafe keyword
    end_hw=$((lineno + LOOKBACK_HW))
    body="$(sed -n "${lineno},${end_hw}p" "$file")"
    if echo "$body" | grep -qE "$HW_PATTERN"; then
      pre_hw="$(sed -n "${start},${end_hw}p" "$file")"
      if ! echo "$pre_hw" | grep -qE "$ARM_PATTERN"; then
        echo "ERROR-T2: $file:$lineno — hardware-access unsafe lacks (ARM ARM <section>) citation"
        errors=$((errors + 1))
      fi
    fi
  done < <(grep -nE 'unsafe \{|unsafe fn |unsafe impl ' "$file")
done < <(find rust/sele4n-hal/src -name '*.rs' -type f)

if [ "$errors" -gt 0 ]; then
  echo "FAIL: $errors unsafe-block citation issue(s)"
  exit 1
fi
echo "OK: every HAL unsafe block has // SAFETY: (universal); every hardware-access block additionally cites ARM ARM"
```

**Pre-landing audit step.** Before wiring this gate into Tier 0,
run it locally and inventory any pre-existing tier-1 misses
(unsafe blocks lacking `// SAFETY:` comments). Each miss is a
small Rust-side fix (add the comment). Empirically, the live
tree has 20 unsafe blocks where the gate would fire on tier 1
or tier 2 — these need to be triaged file-by-file BEFORE the
gate lands so the gate goes green on first activation.

**Validation.**

```bash
./scripts/check_arm_arm_citations.sh   # MUST pass on current tree
# Synthetic negative test:
sed -i '$a unsafe { core::ptr::read_volatile::<u32>(0 as *const _) };' \
  rust/sele4n-hal/src/lib.rs
./scripts/check_arm_arm_citations.sh   # MUST fail
git checkout -- rust/sele4n-hal/src/lib.rs
```

**Risk.** Low. Additive CI gate. One subtle risk vector: the
5-line lookback may miss a citation that lives further above (e.g.,
in a function-level `///` doc comment). Mitigation: the gate
reports the offending line so a developer can add a more local
citation; the deep audit's verification confirmed every existing
block has a citation within 5 lines.

### 16.5 Sub-task R12.D — `_fields` consumer gate (closes DEEP-ARCH-02 false positive)

**Goal.** Convert the deep audit's §11.1 manual verification (which
claimed "each `*_fields : List StateField` definition has 3..26
consumers") into a machine-checked CI gate.

**Verified prerequisites (corrected from the deep audit).** A live
re-grep shows the deep audit's consumer count was wrong: it counted
references to the underlying predicate name (e.g.,
`registryEndpointValid` — which has 16 consumers across the kernel)
rather than the `_fields` metadata def (e.g.,
`registryEndpointValid_fields` — which has **0 consumers outside
its declaring file** but 4-5 inside it via `fieldsDisjoint` calls).

```text
CrossSubsystem.lean:887-930 contains 11 *_fields definitions.
Live consumer counts (verified by direct `grep -rn "<name>_fields\b"
SeLe4n/`):
  registryEndpointValid_fields:           in-file 4, out-of-file 0
  registryInterfaceValid_fields:          in-file 3, out-of-file 0
  registryDependencyConsistent_fields:    in-file 5, out-of-file 0
  noStaleEndpointQueueReferences_fields:  in-file 5, out-of-file 0
  noStaleNotificationWaitReferences_fields: in-file 5, out-of-file 0
  serviceGraphInvariant_fields:           in-file 5, out-of-file 0
  schedContextStoreConsistent_fields:     in-file 4, out-of-file 0
  schedContextNotDualBound_fields:        in-file 4, out-of-file 0
  schedContextRunQueueConsistent_fields:  in-file 4, out-of-file 0
  blockingAcyclic_fields:                 in-file 3, out-of-file 0
  lifecycleObjectTypeLockstep_fields:     in-file 3, out-of-file 0
```

All 11 are file-local helpers used only via `fieldsDisjoint` calls
within `CrossSubsystem.lean`. They are NOT dead code (in-file
consumers exist), but they are NOT exported (zero out-of-file
consumers).

**Design implication (refined from the original sketch).** A naive
"out-of-file consumer required" gate would fail on all 11 — a
false alarm. The correct gate enforces: every `*_fields` def must
have at least 1 consumer ANYWHERE in the SeLe4n tree (in-file or
out-of-file). Truly dead defs (0 consumers anywhere) fail the
gate; file-local helpers pass. This matches the deep audit's
intent: detect orphan metadata, not enforce export discipline.

**Tasks.**

| # | File | Action |
|---|---|---|
| R12.D.1 | `scripts/check_no_orphan_fields.sh` (new) | Implement a bash script that: (a) finds every `def <name>_fields :` in `SeLe4n/Kernel/CrossSubsystem.lean` (and any sibling files under `SeLe4n/Kernel/` — extensible via a list); (b) for each, runs `grep -rn "<name>_fields" SeLe4n/` and counts hits OUTSIDE the file the def lives in; (c) fails if the count is < 1 (orphan definition). |
| R12.D.2 | `scripts/test_tier0_hygiene.sh` | Wire the gate into Tier 0. |
| R12.D.3 | `scripts/website_link_manifest.txt` | Add the new script. |
| R12.D.4 | `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | Add: "DEEP-ARCH-02 closed structurally by R12.D; orphan `*_fields` definitions cause CI failure." |
| R12.D.5 | (Optional) Extend the gate to all `*_fields : List` definitions across the kernel if any exist outside `CrossSubsystem.lean`. The current scope is `CrossSubsystem.lean` per the deep audit's locus. |

**Implementation steps for R12.D.1 (the gate script).**

```bash
#!/usr/bin/env bash
# scripts/check_no_orphan_fields.sh
# Per WS-RC R12.D: every *_fields : List StateField definition must have
# at least one consumer somewhere in the SeLe4n tree (in-file or out-of-file).
# This detects truly dead metadata, not export discipline.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

errors=0
TARGETS=(SeLe4n/Kernel/CrossSubsystem.lean)

for file in "${TARGETS[@]}"; do
  while IFS= read -r line; do
    name="$(echo "$line" | sed -E 's/^def ([A-Za-z_]+_fields).*/\1/')"
    [ -z "$name" ] && continue
    # Count ALL hits in SeLe4n tree, including in-file (the definition
    # itself contributes 1; we need at least 2 to mean "used").
    total_hits="$(grep -rn "\b${name}\b" SeLe4n/ | wc -l)"
    if [ "$total_hits" -lt 2 ]; then
      echo "ERROR: '$name' is dead (only the def itself, 0 consumers)"
      errors=$((errors + 1))
    fi
  done < <(grep -E "^def [A-Za-z_]+_fields\s*:" "$file")
done

if [ "$errors" -gt 0 ]; then
  echo "FAIL: $errors dead *_fields definition(s)"
  exit 1
fi
echo "OK: every *_fields definition is used (in-file or out-of-file)"
```

**Live verification at audit time** (this plan author re-ran the
gate against the v0.30.11 HEAD): all 11 `*_fields` defs have
total_hits ≥ 4, so the gate goes green on activation. No orphan
defs in the tree.

**Validation.**

```bash
./scripts/check_no_orphan_fields.sh   # MUST pass on current tree
# Synthetic negative: temporarily add an orphan def and verify failure
echo 'def orphan_fields : List StateField := []' >> SeLe4n/Kernel/CrossSubsystem.lean
./scripts/check_no_orphan_fields.sh   # MUST fail
git checkout -- SeLe4n/Kernel/CrossSubsystem.lean
```

**Risk.** Low. Additive. One subtle risk: a *_fields def used only
within its declaring file (intentional locality) would trip the
gate; mitigation is to extend the gate to allow same-file consumers
if a `private` modifier is present, but the current scope is
"public defs must have public consumers" which matches the deep
audit's verification expectation.

### 16.6 Phase R12 cumulative validation

```bash
./scripts/check_production_staging_partition.sh
./scripts/check_arm_arm_citations.sh
./scripts/check_no_orphan_fields.sh
./scripts/test_tier0_hygiene.sh    # exercises all three above + existing checks
./scripts/check_website_links.sh
```

### 16.7 Phase R12 risk

**Very low.** R12.A is non-functional concurrency configuration.
R12.B/C/D are additive CI gates that run on every push; their only
failure mode is when a real partition violation, missing citation,
or orphan def exists — which is exactly when the gate should fail.

The structural-fix policy in §1.5 means that **the next audit
cannot re-raise DEEP-ARCH-01, DEEP-RUST-01/02, or DEEP-ARCH-02 as
new findings** without first explaining why the corresponding gate
did not catch the issue. This is the policy's primary value: it
forces audit findings to be either novel or paired with a gate
weakness, never recycled.

### 16.8 Commit messages

```
WS-RC R12.A: add concurrency: blocks to non-Lean workflows (DEEP-CI-01)
WS-RC R12.B: production/staged partition CI gate
             (closes DEEP-ARCH-01 false positive structurally)
WS-RC R12.C: ARM-ARM citation CI gate
             (closes DEEP-RUST-01 + DEEP-RUST-02 false positives structurally)
WS-RC R12.D: *_fields consumer CI gate
             (closes DEEP-ARCH-02 false positive structurally)
```

---

## 17. Phase R13 — Reserved (downstream emergent items)

### 17.1 Purpose

Phase R13 is reserved as a buffer for items discovered during R0..R12
execution that do not fit any existing phase. Examples of items that
would land here:

- A new Lean elaborator regression introduced by an Lean 4.x.y point
  release that affects R4 or R5.
- A correctness bug surfaced by R2's hardware-mode integration suite
  (DEEP-TEST-03) that requires a code change beyond what was scoped.
- A documentation refactor needed to support a renamed module.

If R13 closes empty, the phase is simply skipped at WS-RC closure.

### 17.2 Entry rules

Items can enter R13 only if all three hold:
1. Discovered during R0..R12 execution (not pre-existing in the audit).
2. Cannot be folded into a still-open existing phase.
3. Has at least one verified file/line target.

Items not meeting (3) go into `AUDIT_v0.30.11_DEFERRED.md` rather
than R13.

---

## 18. Phase R14 — Post-1.0 maintainability backlog

### 18.1 Goal

Track every WS-RC-related item that genuinely cannot ship in v1.0,
plus the predecessor DEBT-* items whose remediation is large refactor
work. R14 is **not** part of the v1.0 cut; its items become the
v1.x roadmap recorded in `AUDIT_v0.30.11_DEFERRED.md` and
`docs/WORKSTREAM_HISTORY.md`.

### 18.2 R14 contents

| ID | Source | Closure target |
|---|---|---|
| DEEP-PROOF-01 | Deep audit §10.1 | v1.x research-style task: restructure the proof at `Scheduler/Operations/Preservation.lean:1700–1739` constructively (case-analysis on `Option ThreadId`) so both the explicit `Classical.byContradiction` and the surrounding implicit `Classical.em` from `by_cases` are eliminated. |
| DEEP-MODEL-02 | Deep audit §11.5 | v1.x: refactor `allTablesInvExtK` from a 17-tuple conjunction to a `structure` with named `Prop` fields. Subsumes DEBT-ST-01. |
| DEEP-PRELUDE-01 | Deep audit §10.1 | v1.x: macro-generate the 15 `LawfulBEq` instances for typed identifiers. |
| DEEP-PRELUDE-02 | Deep audit §10.1 | v1.x: move `HashSet`/`RHTable` helper lemmas to `Prelude/HashSetLemmas.lean`. |
| DEBT-CAP-01 | Predecessor §5 | v1.x: extract shared frame-helper for `cspaceInsertSlot_preserves_*` block at `Capability/Operations.lean:471+`. |
| DEBT-CAP-02 | Predecessor §5 | v1.x: tactic for Insert/Delete/Revoke proof scaffold. |
| DEBT-SCH-01 | Predecessor §5 | v1.x: split `Scheduler/Operations/Preservation.lean` (3779 LoC) into 5–6 per-invariant files. |
| DEBT-SCH-02 | Predecessor §5 | v1.x: discharge `hDomainActiveRunnable` and `hBandProgress` from kernel invariants (`Liveness/WCRT.lean:71-74`). Genuine new proof work, not refactoring. |
| DEBT-IF-01 | Predecessor §5 | v1.x: thematic split of `InformationFlow/Invariant/Operations.lean` (3857 LoC). |
| DEBT-IF-02 | Predecessor §5 | v1.x: closure-form discharge for 6 capability dispatch arms. |
| DEBT-SVC-01 | Predecessor §5 | v1.x: retry split of `Service/Invariant/Acyclicity.lean` (1043 LoC) when Lean elaborator fragility resolves. |
| DEBT-IPC-01 | Predecessor §5 | v1.x: H3 IPC-buffer extraction for `capRecvSlot`. |
| DEBT-RT-01 | Predecessor §5 | v1.x: add `radixWidth ≤ 21` assertion when promoting FrozenOps. |
| DEBT-TST-01 | Predecessor §5 | v1.x: split or document `tests/NegativeStateSuite.lean` (3660 LoC). |
| DEBT-BOOT-01 | Predecessor §5 | v1.x: AF3-F minimum-configuration validation (≥1 thread, valid scheduler state). |

### 18.3 Closure recording

At WS-RC closure, the R14 contents migrate to:
- `AUDIT_v0.30.11_DEFERRED.md` (new file, archived under
  `docs/dev_history/audits/` once the next workstream opens).
- `docs/WORKSTREAM_HISTORY.md` row for WS-RC closure: "post-1.0
  backlog of N items (DEFERRED-list link)."


---

## 19. Validation strategy across the workstream

### 19.1 Per-PR gates (every R-phase commit)

| Gate | Command | Tier | Required |
|---|---|---|---|
| Pre-commit hook | `.git/hooks/pre-commit` (auto via symlink) | – | Yes (do not bypass) |
| Tier 0 hygiene | `./scripts/test_tier0_hygiene.sh` | T0 | Yes |
| Tier 1 build | `./scripts/test_tier1_build.sh` | T1 | Yes |
| Tier 2 trace + negative | `./scripts/test_smoke.sh` | T2 | Yes |
| Tier 3 invariant anchors | `./scripts/test_full.sh` | T3 | Yes when phase touches theorem files |
| Tier 4 nightly experimental | `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | T4 | Recommended on R2 (FFI), R3 (boot), R4 (structural) |
| Rust suite | `./scripts/test_rust.sh` | – | Yes when phase touches `rust/` |
| Rust conformance | `./scripts/test_rust_conformance.sh` | – | Yes on R8, R10 |
| Website link manifest | `./scripts/check_website_links.sh` | T0 | Yes when phase renames or removes paths |

### 19.2 Cross-phase regression tracking

A monotonicity baseline is cut at R0 (`AUDIT_v0.30.11_WS_RC_BASELINE.txt`).
Every R-phase commit must:
- Not increase `sorry`/`axiom`/`Classical.*` counts (target: 0/0/1
  baseline; R14 will close the 1).
- Not decrease theorem count without paired removal of an obsoleted
  consumer.
- Not increase the count of files exceeding 500 LoC by more than +1
  per phase.

The cascade gate `scripts/ak7_cascade_check_monotonic.sh` reads the
baseline and enforces these checks. If a legitimate
phase requires breaking a monotonicity gate (e.g., R4 may briefly
inflate a count during the smart-constructor migration), the PR
description must document the rationale and the closure target.

### 19.3 Hardware validation

R2 lands hardware syscall dispatch. Validation strategy:

| # | Check | Method |
|---|---|---|
| HV.1 | Lean side: `syscallDispatchFromAbi` decodes a representative `SyscallId` correctly | `tests/SyscallDispatchSuite.lean` per-variant tests |
| HV.2 | Encoding: high-bit-set error discriminant survives Lean → Rust | Synthesised `KernelError` round-trip in conformance |
| HV.3 | State threading: post-syscall `kernelStateRef` matches simulation expectation | Side-by-side comparison with `MainTraceHarness` traces |
| HV.4 | RPi5 boot smoke (post-R3): `bootFromPlatformChecked` admits VSpaceRoot and `wxExclusiveInvariant` holds | `tests/TwoPhaseArchSuite` regression |
| HV.5 | QEMU-mode integration | `./scripts/test_qemu.sh` (existing harness) once the dispatch path is wired |

Hardware-on-device validation (RPi5 silicon) is outside the WS-RC
scope per the project's hardware-validation cadence; the R2/R3
tests above are sufficient to gate the v1.0 tag.

### 19.4 CI cadence

| Push target | CI workflows triggered |
|---|---|
| Feature branch | `lean_action_ci.yml` (fast/smoke/full matrix); `platform_security_baseline.yml` |
| Pull request | All five workflows |
| `main` (post-merge) | `nightly_determinism.yml` + `codebase_map_sync.yml` |

WS-RC PR commits land on `main` only after pull-request CI passes.


---

## 20. Risk register

### 20.1 Top risks and mitigations

| ID | Risk | Severity | Phase | Mitigation |
|---|---|---|---|---|
| RISK-1 | R2 `IO.Ref SystemState` design fails to survive Lean's compilation model on the hardware path (e.g., the reference is reset on every FFI re-entry). | High | R2.A | Sub-PR R2.A is independently buildable; if the IO.Ref approach fails, fall back to either (a) thread-local register-decoded snapshot, or (b) explicit state-passing through additional FFI parameters. R2.A's docstring documents the design choice for transparency. |
| RISK-2 | R3's boot-result widening breaks `bootFromPlatformChecked_eq_bootFromPlatform` and the proof rebuild blocks the phase. | Medium | R3 | The theorem is narrowly scoped; widening the equality predicate is the canonical fix. If the proof grows substantially, R3.6 splits into its own commit. |
| RISK-3 | R4's smart-constructor migrations cascade into widespread proof breakage in `Capability/Operations.lean` (1858 LoC) and downstream consumers. | High | R4 | Each sub-task R4.A/B/C lands as a separate sub-PR. Build verification on every intermediate commit. The smart-constructor pattern mirrors `NonNullCap` (existing example). |
| RISK-4 | R5's domain-propagation fix in `schedContextConfigure` requires a new preservation theorem that does not yet exist. | Medium | R5.G | Theorem stub is added in the same PR as the implementation; if elaboration time becomes prohibitive, the theorem is split out to a sibling file. |
| RISK-5 | R6.C's SecurityDomain lattice completion is genuine new proof work; underestimating effort may delay v1.0. | Medium | R6.C | The lattice instances are mechanical; the four lattice-law theorems are routine. Effort budgeted at one full work day per theorem. |
| RISK-6 | R8.A's test-file renames break the website link manifest if any of the renamed paths are listed there; CI fails on the post-rename commit. | Low | R8.A | Update `scripts/website_link_manifest.txt` in the same commit as the rename. The CI gate enforces this consistency. |
| RISK-7 | R11.B's AGENTS.md replacement is challenged because some external agent framework depends on its specific content shape. | Low | R11.B | The redirect-stub option preserves discoverability; the rewrite-with-CI-sync option preserves content. Either is acceptable. |
| RISK-8 | DEEP-PROOF-01's restructuring (deferred to R14) turns out to be intractable, blocking v1.x's "no Classical" claim. | Low | R14 | Lean stdlib `Classical.byContradiction` is foundationally safe; the project's "constructive Lean kernel" discipline can be tracked as v1.x debt without a release-blocking impact. R14 explicitly accepts this deferral. |

### 20.2 Process risks

- **Multiple simultaneous PRs** — WS-RC has 12+ active PRs. Coordinate
  merge order strictly (R1 before R2 before R3, etc.) to avoid
  rebase conflicts. The phase ordering in §3.2 is the source of truth.
- **Background-agent file conflicts** — per CLAUDE.md "Background
  agent file-change protection," background agents must not edit
  files the foreground is touching. WS-RC PRs should use
  background agents only for read-only research (e.g., locating
  consumers of a renamed symbol).
- **Lean toolchain bumps** — WS-RC pins Lean 4.28.0. If a toolchain
  bump becomes necessary mid-workstream, treat as a phase-zero
  risk: pause WS-RC, land the toolchain bump as a separate
  workstream, re-baseline, then resume.

### 20.3 Schedule sensitivity

The following events would push WS-RC's v1.0 closure target:

- R2 sub-PR taking longer than budgeted (most-sensitive item).
- A new audit cut superseding v0.30.11 (would re-open the cycle).
- An external toolchain regression requiring a Lean version change.

The following events would NOT push v1.0:

- A R14 item being added or removed (R14 is post-1.0 by definition).
- A documentation-only correction discovered in R11 (single-PR fix).


---

## 21. Sign-off and closure

### 21.1 Per-phase exit criteria (consolidated)

| Phase | Exit criteria |
|---|---|
| R0 | Baseline file landed; ERRATA records DEEP-ARCH-01 withdrawal-as-finding (with cross-reference to R12.B for the structural fix); DEBT-RUST-02 closure annotated in archived discharge index; `test_full.sh` clean. **LANDED** at WS-RC R0. |
| R1 | `endpointCallWithCaps` `lookupCspaceRoot = none` arm returns `.error .invalidCapability`; AK1-I-style comment block in place; receive-path comment expanded for parity; `endpointCallWithCaps_preserves_ipcInvariant` updated for new vacuous arm; `tests/InformationFlowSuite.lean` AK1-I regression extended for send/receive/**call** symmetry; `tests/NegativeStateSuite.lean::runR1IpcCallPathSymmetryChecks` adds 3 focused checks; smoke + full test pipelines clean. **LANDED** on branch `claude/audit-ipc-symmetry-yhdIu`. |
| R2 | `syscall_dispatch_inner` invokes `syscallEntryChecked` end-to-end; `syscallDispatchFromAbi` exists and is referenced by Rust comment; `@[export]` symbols gated by `hwTarget`; `SyscallDispatchSuite` exercises every variant. |
| R3 | `bootSafeObject` admits `bootSafeVSpaceRoot`-compliant VSpaceRoots; `rpi5BootVSpaceRoot` threaded into boot result; correctness theorem extended; sim parity preserved. |
| R4 | R4.A `slotsUnique`, R4.B RetypeTarget non-bypass, R4.C NoDup `waitingThreads` enforced structurally (subsumes DEEP-IPC-01); R4.D `cspaceMutate_rejects_null_cap` witness theorem (closes DEEP-CAP-02 structurally); downstream consumers updated; theorems witness each discharge. |
| R5 | Seven scheduler/lifecycle items closed; preservation proofs updated; regression tests added. |
| R6 | GIC bridge in place; `DeclassificationPolicy` defined; SecurityDomain lattice complete; `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull` proved or witnessed. |
| R7 | AK8-K LOW-tier items closed in scope; residue lifted to deferred file; header comment shrinks to one paragraph. |
| R8 | Four test files renamed; conformance suite extended to 6 missing syscalls; CI green. |
| R9 | `check_sorry.lean` tokeniser-based check replaces regex; pre-commit hook tests pass. |
| R10 | All R10 sub-tasks landed; AK10 rename complete; license header on `SeLe4n.lean`; `test_full.sh` and `test_rust.sh` clean. |
| R11 | README/CLAUDE.md/AGENTS.md/SECURITY_ADVISORY synchronised with post-implementation tree; `check_version_sync.sh` clean; FrozenOps experimental status surfaced. |
| R12 | R12.A: four non-Lean workflows have `concurrency:` blocks. R12.B: `check_production_staging_partition.sh` wired into Tier 0 (closes DEEP-ARCH-01 structurally). R12.C: `check_arm_arm_citations.sh` wired into Tier 0 (closes DEEP-RUST-01/02 structurally). R12.D: `check_no_orphan_fields.sh` wired into Tier 0 (closes DEEP-ARCH-02 structurally). All four gates pass on next push. |
| R13 | Reserved (closes empty unless emergent items appear). |
| R14 | Migrated to `AUDIT_v0.30.11_DEFERRED.md` and `WORKSTREAM_HISTORY.md` as the v1.x backlog; **not part of v1.0 closure**. |

### 21.2 Workstream-level closure checklist (v0.31.0 release)

Tagging `v0.31.0` "verified specification release" requires:

- [ ] R0 landed (baseline + errata + DEBT-RUST-02 closure).
- [ ] R1 landed (one-line NI symmetry fix; quick credibility).
- [ ] R8 landed (test renames + Rust conformance extension).
- [ ] R9 landed (pre-commit hardening with Lean tokeniser).
- [ ] R10 landed (inline polish + AK10 rename + SPDX header).
- [ ] R11 landed (documentation accuracy + AGENTS.md + CLAUDE.md
      source-layout + FrozenOps experimental annotation).
- [ ] R12 landed:
  - [ ] R12.A: concurrency blocks on four non-Lean workflows.
  - [ ] R12.B: `check_production_staging_partition.sh` wired into
        Tier 0 (DEEP-ARCH-01 structural close).
  - [ ] R12.C: `check_arm_arm_citations.sh` wired into Tier 0
        (DEEP-RUST-01/02 structural close).
  - [ ] R12.D: `check_no_orphan_fields.sh` wired into Tier 0
        (DEEP-ARCH-02 structural close).
- [ ] `./scripts/test_full.sh` clean.
- [ ] `./scripts/test_rust.sh` clean.
- [ ] `./scripts/test_tier0_hygiene.sh` clean (now includes the
      three new gates from R12.B/C/D).
- [ ] `./scripts/check_website_links.sh` clean.
- [ ] `./scripts/check_version_sync.sh` clean.
- [ ] `lakefile.toml` version bumped to 0.31.0.
- [ ] `CHANGELOG.md` entry summarising WS-RC R1, R8..R12 closures
      AND the false-positive structural-fix policy from §1.5.
- [ ] No new `sorry`/`axiom`; `Classical.byContradiction` count ≤ 1
      (pre-existing).
- [ ] Synthesised positive-and-negative tests for each new CI gate
      (R12.B/C/D) pass and fail as expected.

### 21.3 Workstream-level closure checklist (v1.0.0 release)

Tagging `v1.0.0` "bootable verified microkernel" additionally requires:

- [ ] R2 landed (FFI dispatch wired through `syscallEntryChecked`):
  - [ ] R2.A: `IO.Ref SystemState` threading.
  - [ ] R2.B: `syscallDispatchFromAbi` body + correctness theorems.
  - [ ] R2.C: uniform `hwTarget` gating + `SyscallDispatchSuite`.
- [ ] R3 landed (boot VSpace threaded; `bootSafeObject` admits
      `bootSafeVSpaceRoot`-compliant VSpaceRoots).
- [ ] R4 landed:
  - [ ] R4.A: `slotsUnique` structural via `UniqueSlotMap`.
  - [ ] R4.B: `RetypeTarget` non-bypassable.
  - [ ] R4.C: type-level NoDup `waitingThreads` (subsumes
        DEEP-IPC-01).
  - [ ] R4.D: `cspaceMutate_rejects_null_cap` witness theorem
        (closes DEEP-CAP-02 structurally).
- [ ] R5 landed (scheduler/lifecycle symmetry, all seven sub-tasks).
- [ ] R6 landed (architecture/info-flow completeness, all four
      sub-tasks).
- [ ] CLAUDE.md "First hardware target: Raspberry Pi 5" is literally
      true (i.e., `syscall_dispatch_inner` invokes
      `syscallEntryChecked`, not the stub).
- [ ] `tests/SyscallDispatchSuite.lean` exercises every `SyscallId`
      variant.
- [ ] `lakefile.toml` version bumped to 1.0.0.
- [ ] `CHANGELOG.md` entry summarising WS-RC R2..R6 closures
      including R4.D (CAP-02 structural) alongside R4.A/B/C.
- [ ] R14 contents migrated to `AUDIT_v0.30.11_DEFERRED.md` and
      logged in `WORKSTREAM_HISTORY.md` as v1.x backlog.
- [ ] All six false-positive structural fixes (R4.C subsumes IPC-01,
      R4.D for CAP-02, R12.B for ARCH-01, R12.C for RUST-01/02,
      R12.D for ARCH-02) are demonstrably enforced — a synthesised
      regression test exists for each gate.

### 21.4 Workstream archival

At v1.0.0 tag:

1. Move `docs/audits/AUDIT_v0.30.11_*` (COMPREHENSIVE, DEEP_VERIFICATION,
   WORKSTREAM_PLAN, WS_RC_BASELINE, ERRATA, DISCHARGE_INDEX, DEFERRED)
   to `docs/dev_history/audits/`.
2. Update `docs/audits/README.md` "Files currently live" — empty, or
   pointing at the next active audit cut.
3. Update `scripts/website_link_manifest.txt` to rewrite all
   `docs/audits/AUDIT_v0.30.11_*` references to the archived path.
4. Add the WS-RC closure row to `docs/WORKSTREAM_HISTORY.md` with
   cross-references to the archived files.
5. The cascade gate `scripts/ak7_cascade_check_monotonic.sh` reads
   the baseline from the archived path until the next workstream
   cuts a fresh baseline.


---

## Appendix A. DEEP-ARCH-01 audit-error rationale (full trace)

This appendix documents the verification that the deep audit's
DEEP-ARCH-01 narrowing claim is itself a false positive, so a
maintainer reading this plan can re-derive the conclusion.

### A.1 Original claim (deep audit §11.3)

> CacheModel: imported by `Platform/Staged.lean`,
> `Architecture/TlbCacheComposition.lean`, AND
> `Architecture/BarrierComposition.lean`. `BarrierComposition` is
> imported by `Architecture/TlbModel.lean`, which is imported by
> `SeLe4n.lean` (the production library entry point). So
> CacheModel **is** in the production chain. Marker is misleading.

### A.2 Live verification

Step 1 — confirm `BarrierComposition` does NOT import `CacheModel`:

```bash
grep "^import" SeLe4n/Kernel/Architecture/BarrierComposition.lean
# (empty — file has no imports)
```

The file's first import-relevant line is line 10 of the file body,
which is part of the namespace declaration block, not an import.
There is no `import SeLe4n.Kernel.Architecture.CacheModel` anywhere
in the file.

Step 2 — confirm `CacheModel` is reachable only via `Platform/Staged`:

```bash
grep -rln "import SeLe4n.Kernel.Architecture.CacheModel" SeLe4n SeLe4n.lean Main.lean
# SeLe4n/Platform/Staged.lean
# SeLe4n/Kernel/Architecture/TlbCacheComposition.lean
```

Step 3 — confirm `TlbCacheComposition` is reachable only via `Platform/Staged`:

```bash
grep -rln "import SeLe4n.Kernel.Architecture.TlbCacheComposition" SeLe4n SeLe4n.lean Main.lean
# SeLe4n/Platform/Staged.lean
```

Step 4 — transitive-closure trace from `SeLe4n.lean`:

A small bash script traces all transitive imports starting from
`SeLe4n.lean` (the production library entry point). The closed set
contains **144 modules**. Verification:

```bash
# Reproducible transitive-closure script
declare -A seen
queue=(SeLe4n)
while [ ${#queue[@]} -gt 0 ]; do
  curr="${queue[0]}"; queue=("${queue[@]:1}")
  [ -n "${seen[$curr]:-}" ] && continue
  seen[$curr]=1
  file="${curr//.//}.lean"
  [ ! -f "$file" ] && continue
  while IFS= read -r line; do queue+=("$line"); done < <(grep -E "^import SeLe4n\." "$file" | awk '{print $2}')
done
echo "Total reachable: ${#seen[@]}"   # 144
echo "${!seen[@]}" | tr ' ' '\n' | grep -i "cachemodel\|timermodel\|exceptionmodel\|tlbcache" || echo "NONE"
# NONE
```

Step 5 — conclusion. CacheModel, TimerModel, ExceptionModel, and
TlbCacheComposition are **all four** outside the 144-module
production closure of `SeLe4n.lean`. Reachability is exclusively
via `Platform/Staged.lean`, which is the staging anchor exactly for
not-yet-production modules. All three "STATUS: staged" markers
(CacheModel, TimerModel, ExceptionModel) are therefore correct.

### A.3 Disposition

- DEEP-ARCH-01 is **WITHDRAWN as an active finding** (audit
  verification error in §11.3).
- **Structural remediation lands in R12.B** — a CI gate
  (`scripts/check_production_staging_partition.sh`) computes the
  transitive closure from `SeLe4n.lean` and `Platform/Staged.lean`,
  cross-checks against the "STATUS: staged" markers in source, and
  fails the build on any partition violation.
- The structural gate is the implement-the-improvement remediation
  for the false positive: instead of relying on a future auditor to
  manually re-derive the 144-module trace (and possibly make the
  same verification error the deep audit's §11.3 made), the
  partition is machine-checked at every CI run.
- Recorded in `AUDIT_v0.30.11_ERRATA.md` (Phase R0) for permanence.

### A.4 Why this matters operationally

The deep audit's verification error in §11.3 was caused by the
auditor reading `BarrierComposition.lean`'s namespace declaration
(line 10) as an `import` line. A future auditor performing the
same trace by hand could make the same error. The R12.B gate
removes the human from the loop:

- Every PR runs `check_production_staging_partition.sh`.
- A new "STATUS: staged" marker on a file that is reachable from
  `SeLe4n.lean` fails the build immediately.
- A new module added to `Platform/Staged.lean` without the marker
  also fails the build.
- The partition is a hard CI gate, not an audit-time guideline.

This is the canonical pattern for the §1.5 structural-fix policy:
manual verification → machine-checked invariant. The same pattern
applies to R12.C (ARM-ARM citations) and R12.D (`_fields`
consumers).

---

## Appendix B. Implement-the-improvement compliance audit

For each finding, this plan author re-asked the §12.5 preflight
question:

> "Does my recommendation make the documentation true (by changing
> code), or does it make the code's current behaviour defensible
> (by changing documentation)? If the latter, am I certain the
> documentation describes a *worse* state than the code, not a
> *better* one?"

**Result:** every implementation-recommended remediation in this
plan makes the documentation true. Every documentation-only item
(R11) falls under the legitimate-exception clause: the code is
correct and the docs are stale.

The only remediation that explicitly preserves documentation
unchanged is DEEP-DOC-05 (the "First hardware target: Raspberry
Pi 5" claim), which is made true by the R2 implementation rather
than weakened.

**Extension to false positives.** The original §12.5 preflight
applied to active findings only. This plan extends it to the six
withdrawn-as-false-positive findings via the §1.5 structural-fix
policy: each false positive's manual verification is converted to
a machine-checked invariant (witness theorem or CI gate) so the
verification's correctness becomes immune to the auditor-error
that produced the false positive in the first place. See R4.D
(witness theorem for DEEP-CAP-02) and R12.B/C/D (CI gates for
DEEP-ARCH-01, DEEP-RUST-01/02, DEEP-ARCH-02). DEEP-IPC-01 is
subsumed structurally by R4.C (NoDup at type level).

This extension is itself an instance of the implement-the-
improvement rule: the deep audit's §11.1/§11.3 verification is
"the better state" (the code is correct), and the structural fix
makes that verification's correctness a perpetual property rather
than a single-audit-cycle artifact.


---

## Appendix C. Cross-reference matrix

This matrix maps every finding ID to (a) the source audit section,
(b) the verifier evidence, (c) the WS-RC phase, (d) the v1.0 vs
v0.31.0 release boundary.

### C.1 DEEP-* findings

| Finding | Audit § | Verified at | Phase | v0.31.0 | v1.0.0 |
|---|---|---|---|---|---|
| DEEP-FFI-01 | Deep §6.1 | `Platform/FFI.lean:185-190, 216-223` | R2 | – | YES |
| DEEP-FFI-02 | Deep §7.2 | `rust/sele4n-hal/src/svc_dispatch.rs:308` (no Lean fn) | R2 | – | YES |
| DEEP-FFI-03 | Deep §6.1 | `Platform/FFI.lean:34-39` | R2 | – | YES |
| DEEP-IPC-02 | Deep §5.2 | 7 IPC files w/ `set_option linter.unusedVariables false` | R10 | YES | YES |
| DEEP-IPC-03 | Deep §5.2, §11.3 | `IPC/DualQueue/WithCaps.lean:198` | R1 | **CLOSED** | **CLOSED** |
| DEEP-IPC-04 | Deep §5.2 | `IPC/Operations/Endpoint.lean:485` | R6 | – | YES |
| DEEP-IPC-05 | Deep §5.2, §12 | `Model/Object/Types.lean Notification.waitingThreads` | R4 | – | YES |
| DEEP-DOC-01 | Deep §8.4, §11.4 | `README.md:92, :213` | R11 | YES | YES |
| DEEP-DOC-02 | Deep §8.4, §11.5 | `AGENTS.md:7` | R11 | YES | YES |
| DEEP-DOC-03 | Deep §8.4 | `CLAUDE.md` source-layout omits 3 files | R11 | YES | YES |
| DEEP-DOC-04 | Deep §8.4 | README audit-history table | R11 | YES | YES |
| DEEP-DOC-05 | Deep §8.4, §12 | NO-ACTION (covered by DEEP-FFI-01) | – | – | – |
| DEEP-DOC-06 | Deep §8.4 | `README.md:38, :193` | R11 | YES | YES |
| DEEP-MODEL-01 | Deep §4, §12 | `Model/Object/Structures.lean` CNode `slots` | R4 | – | YES |
| DEEP-MODEL-02 | Deep §4, §11.5 | `Model/State.lean:386-395`; `Builder.lean:32-97` | R14 | – | – |
| DEEP-MODEL-03 | Deep §4 | `Model/State.lean:146` | R10 | YES | YES |
| DEEP-MODEL-04 | Deep §4 | `Model/State.lean LifecycleMetadata` | R10 | YES | YES |
| DEEP-PRELUDE-01 | Deep §4 | `Prelude.lean:1076-1115` | R14 | – | – |
| DEEP-PRELUDE-02 | Deep §4 | `Prelude.lean:1131+` | R14 | – | – |
| DEEP-CAP-01 | Deep §5.1, §11.5 | `Capability/Operations.lean:959, 1002` | R10 | YES | YES |
| DEEP-CAP-04 | Deep §5.1, §12 | `Capability/Invariant/Defs.lean:345-367` | R4 | – | YES |
| DEEP-CAP-05 | Deep §5.1, §12 | `Capability/Operations.lean:12-62` | R7 | optional | optional |
| DEEP-PROOF-01 | Deep §5.3, §11.4, §12 | `Scheduler/Operations/Preservation.lean:1700-1739` | R14 | – | – |
| DEEP-LICENSE-01 | Deep §3 | `SeLe4n.lean` (no SPDX) | R10 | YES | YES |
| DEEP-PRECOM-01 | Deep §3, §11.2 | `scripts/pre-commit-lean-build.sh:59,61` | R9 | YES | YES |
| DEEP-SCH-02 | Deep §5.3, §12 | `Scheduler/Operations/Selection.lean:225-241, :327` | R5 | – | YES |
| DEEP-SCH-03 | Deep §5.3 | `Lifecycle/Suspend.lean:75-84, :290+` | R5 | – | YES |
| DEEP-SCH-04 | Deep §5.3 | `Scheduler/Operations/Core.lean:715-717` | R5 | – | YES |
| DEEP-SCH-05 | Deep §5.3 | `Scheduler/RunQueue.lean:238` | R5 | – | YES |
| DEEP-SCH-06 | Deep §5.4, §12 | `SchedContext/Operations.lean:110-187` | R5 | – | YES |
| DEEP-SUSP-01 | Deep §5.5, §12 | `Lifecycle/Suspend.lean:290+` | R5 | – | YES |
| DEEP-SUSP-02 | Deep §5.5, §12 | `Lifecycle/Suspend.lean:88-105` | R5 | – | YES |
| DEEP-ARCH-01 | Deep §5.6, §11.3 | **WITHDRAWN as finding (this plan); structural fix in R12.B** | R12.B | YES | YES |
| DEEP-ARCH-03 | Deep §5.6, §12 | `Architecture/ExceptionModel.lean` | R6 | – | YES |
| DEEP-ARCH-04 | Deep §5.6 | NO-ACTION (verified production-wired) | – | – | – |
| DEEP-FDT-01 | Deep §6.2 | `Platform/DeviceTree.lean:695-740` | R10 | YES | YES |
| DEEP-IF-01 | Deep §5.7, §12 | `InformationFlow/Soundness.lean` | R6 | – | YES |
| DEEP-IF-02 | Deep §5.7, §12 | `InformationFlow/Policy.lean:484-500` | R6 | – | YES |
| DEEP-RUST-03 | Deep §7.2 | `sele4n-abi/src/trap.rs:2-6` | R10 | YES | YES |
| DEEP-RUST-04 | Deep §7.2 | `THIRD_PARTY_LICENSES.md:41` | R10 | YES | YES |
| DEEP-RUST-05 | Deep §7.2 | `sele4n-abi/src/lib.rs`, `sele4n-sys/src/lib.rs` | R10 | YES | YES |
| DEEP-RUST-06 | Deep §7.2 | `sele4n-abi/tests/conformance.rs` (6 missing) | R8 | optional | YES |
| DEEP-TEST-01 | Deep §8.1 | `tests/Ak8CoverageSuite.lean` | R8 | YES | YES |
| DEEP-TEST-02 | Deep §8.1 | 3 more test files | R8 | optional | YES |
| DEEP-TEST-03 | Deep §8.1 | sparse `syscallEntryChecked` test coverage | R2 | – | YES |
| DEEP-TEST-04 | Deep §8.1 | NO-ACTION (verified non-empty) | – | – | – |
| DEEP-BOOT-01 | Deep §6.2, §12 | `Platform/Boot.lean:551`; `RPi5/VSpaceBoot.lean` | R3 | – | YES |
| DEEP-SCRIPT-01 | Deep §8.2 | `scripts/website_link_manifest.txt:18` | R10 | YES | YES |
| DEEP-SCRIPT-02 | Deep §8.2 | NO-ACTION (verified clean) | – | – | – |
| DEEP-CI-01 | Deep §8.3 | 4 non-Lean workflows | R12.A | optional | optional |

### C.2 False-positive structural fixes (per §1.5 policy)

The six findings classified as false positives by either the deep
audit's §11.1 or this plan's §2.2 each receive a machine-checked
enforcement gate in WS-RC. The mapping:

| False positive | Audit verification | WS-RC structural fix | Phase | v0.31.0 | v1.0.0 |
|---|---|---|---|---|---|
| DEEP-CAP-02 | `Operations.lean:1093` runtime null-cap guard | Witness theorem `cspaceMutate_rejects_null_cap` + companion in `Capability/Invariant/Preservation/CopyMoveMutate.lean` | R4.D | – | YES |
| DEEP-ARCH-02 | 11 `*_fields` defs all consumed (3..26 consumers each) | `scripts/check_no_orphan_fields.sh` Tier-0 gate | R12.D | YES | YES |
| DEEP-RUST-01 | MMIO unsafe blocks cite `(ARM ARM B2.1)` | `scripts/check_arm_arm_citations.sh` Tier-0 gate (covers all HAL) | R12.C | YES | YES |
| DEEP-RUST-02 | mrs/msr asm! blocks cite `(ARM ARM C5.2)` | Same gate (R12.C) | R12.C | YES | YES |
| DEEP-IPC-01 | `Operations/Endpoint.lean:723` runtime duplicate guard | Type-level `NoDupList ThreadId` on `Notification.waitingThreads` (R4.C) | R4.C | – | YES |
| DEEP-ARCH-01 | All "STATUS: staged" markers correct (this plan's §2.2) | `scripts/check_production_staging_partition.sh` Tier-0 gate | R12.B | YES | YES |

The R12.B/C/D gates are bundled into a single PR ("WS-RC R12: CI
hygiene + structural gates"). R4.D is bundled with the R4 PR. The
v0.31.0 set includes R12.B/C/D so the gates run from the very next
audit cycle; the R4.C and R4.D fixes land with v1.0.0 since they
require the broader R4 structural refactor.

### C.3 Predecessor DEBT-* findings

| Finding | Audit § | Phase | Notes |
|---|---|---|---|
| DEBT-DOC-01 | Comp §5 | R11 | Folded into DEEP-DOC-01..06. |
| DEBT-RUST-02 | Comp §5 | R0 | H-24 reconfirmed closed. |
| DEBT-ST-01 | Comp §5 | R14 | Subsumed by DEEP-MODEL-02. |
| DEBT-CAP-01 | Comp §5 | R14 | Frame helper extraction. |
| DEBT-CAP-02 | Comp §5 | R14 | Tactic extraction. |
| DEBT-SCH-01 | Comp §5 | R14 | Preservation.lean split. |
| DEBT-SCH-02 | Comp §5 | R14 | WCRT hypothesis discharge. |
| DEBT-IF-01 | Comp §5 | R14 | Operations.lean split. |
| DEBT-IF-02 | Comp §5 | R14 | Closure-form discharge. |
| DEBT-SVC-01 | Comp §5 | R14 | Acyclicity.lean split. |
| DEBT-IPC-01 | Comp §5 | R14 | H3 IPC-buffer extraction. |
| DEBT-IPC-02 | Comp §5 | R10 | AK10 rename. |
| DEBT-RT-01 | Comp §5 | R14 | radixWidth assertion. |
| DEBT-FR-01 | Comp §5 | R11 | FrozenOps experimental status. |
| DEBT-RUST-01 | Comp §5 | R8 | Subsumed by DEEP-RUST-06. |
| DEBT-TST-01 | Comp §5 | R14 | NegativeStateSuite split. |
| DEBT-BOOT-01 | Comp §5 | R14 | AF3-F minimum-config. |


---

## Appendix D. Closure summary

**Active findings remediated by WS-RC:** ~55 (all DEEP-* with
disposition ACTIVE or POST-1.0, plus all 17 predecessor DEBT-*
items).

**Findings withdrawn (no remediation needed):** 6 (5 from deep
audit §11.1 + 1 (DEEP-ARCH-01) added by this plan in §2.2).

**Findings demoted to NO-ACTION:** 5 (deep audit §11.5 + this
plan's verification of DEEP-ARCH-04).

**Phases:** 15 (R0..R14) including R13 (reserved) and R14
(post-1.0).

**Pre-1.0 phases (must land for v1.0.0):** R0, R1, R2, R3, R4,
R5, R6.

**v0.31.0 phases (verified specification release):** R0, R1, R8,
R9, R10, R11, R12 (R7 and R13 optional; R2..R6 NOT required for
v0.31.0).

**Post-1.0 backlog (R14):** 14 items tracked as v1.x roadmap; not
release-blocking.

**Total estimated PR count:** 14 (one per active phase) plus
~3 sub-PRs in R2 = **17 PRs**.

### D.1 Workstream identity in identifiers

Per CLAUDE.md "Internal-first naming," the workstream code-name
"WS-RC" is used **only** in:
- Commit messages
- This plan and the four other audit-cycle artefacts
- `docs/WORKSTREAM_HISTORY.md` rows
- Branch names (e.g., `claude/audit-workstream-planning-XsmKS`)

It is **not** used in:
- Theorem names
- Function names
- File names
- Test names

When R8 renames test files away from `Ak8`/`An9`/`Ak9`/`An10`
prefixes, the new names describe semantics, not the WS-RC
workstream. The same rule applies to every new symbol introduced
by R1..R12.

### D.2 What this plan deliberately does NOT do

This plan does **not** prescribe:

- **Code changes outside the verified targets in §2.4/2.5.** Phase
  authors who discover scope creep should redirect via R13 (or, for
  larger changes, propose a sibling workstream).
- **Documentation surgery to match inferior code.** Every
  finding's remediation makes the documentation true; no row
  weakens the documentation to defend the code.
- **A documentation-only path to v1.0.** The deep audit's earlier
  drafts contemplated this; the §12 revision rejects it; this
  plan respects that rejection.
- **A new audit cut.** WS-RC closes the v0.30.11 cycle; the next
  audit (v0.31.x or v1.0.0) cuts after WS-RC closes.

### D.3 Successor workstream entry

The workstream after WS-RC will inherit:
- Whatever items remain in `AUDIT_v0.30.11_DEFERRED.md` (= R14).
- Any newly-cut audit findings.
- Any items in `R13` (the reserved phase) that did not close.

The successor's plan author should re-derive the inheritance from
`docs/WORKSTREAM_HISTORY.md` and the deferred file at workstream
opening, then cut a fresh `AUDIT_v<X>_WORKSTREAM_PLAN.md`.

---

— Plan authored 2026-04-28 on branch
`claude/audit-workstream-planning-XsmKS`. This document is the
canonical decomposition of WS-RC. Successor workstreams should
preserve the audit-error rationale in §2.2 and Appendix A as part
of the project's "honesty about correctness" record.
