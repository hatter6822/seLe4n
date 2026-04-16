# Workstream Plan — WS-AK: Pre-1.0 Release Hardening (v0.29.0 Audit)

**Audit source:** `docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md`
**Date:** 2026-04-16
**Version:** 0.29.0 → 1.0.0 (pre-release)
**Workstream ID:** WS-AK
**Phases:** 10 (AK1–AK10)
**Total sub-tasks:** 109
**Target release:** seLe4n v1.0.0 (first major release, RPi5 first-silicon bring-up)

---

## Table of Contents

1. Executive Summary
2. Audit Verification Results
3. Finding Disposition Matrix
4. Phase AK1 — IPC Fail-Closed & Rendezvous State
5. Phase AK2 — Scheduler, PIP & WCRT Closure
6. Phase AK3 — Architecture: ASID, W^X, EOI, Decode
7. Phase AK4 — ABI Bridge: Decode, Types, Validation
8. Phase AK5 — Rust HAL Boot Hardening
9. Phase AK6 — Information Flow + SchedContext Correctness
10. Phase AK7 — Foundational Model (Prelude/Machine/Model)
11. Phase AK8 — Capability / Lifecycle / Service + Data Structures
12. Phase AK9 — Platform, Boot, DTB, MMIO
13. Phase AK10 — Testing, Documentation & Closure
14. Cross-Cutting Considerations
15. Acceptance Criteria Summary
16. Pre-Merge Checklist
17. Out-of-Scope
18. Rationale for Phase Structure
19. Notes on Proof-Engineering Approach

---

## 1. Executive Summary

This workstream resolves every actionable finding from the v0.29.0 comprehensive
audit. The audit reported **201 non-informational findings** per its §2
summary table (2 CRITICAL, 23 HIGH, 68 MEDIUM, 108 LOW). Enumerating finding
IDs directly from the subsystem notes yields **202 findings** (the audit
summary under-counts by 1 in MEDIUM / 1 in LOW — see §2.4 and AK10-D E-6).
Scope spans 140 Lean modules and 48 Rust sources. Independent verification
against the current codebase (documented in §2) confirmed:

- **197 findings are valid and actionable** (code change or documentation)
- **3 findings are partially qualified** (A-H01, R-HAL-H02, NI-H02 — see §2.2)
- **2 findings require sharper scoping** (S-H03 semantics, R-HAL-M12 signature)
- **0 findings are erroneous** — the audit was exceptionally accurate in
  content; only its aggregate count tally is off by 1–2

The two CRITICAL findings are both correctness-bug-class and each has a concrete
exploit pathway:

1. **A-C01** — ASID rollover silently reuses an active ASID on `AsidPool.allocate`,
   breaking TLB isolation between unrelated address spaces on hardware.
2. **R-ABI-C01** — `service_register` and `sched_context_configure` Rust wrappers
   encode their 5th argument into the IPC buffer overflow slot, but the Lean
   kernel's `arm64DefaultLayout` only decodes 4 inline `msgRegs` and
   `decodeSyscallArgs` has no IPC-buffer merge step. Both syscalls return
   `.error .invalidMessageInfo` on every invocation against the production
   kernel.

The 23 HIGH findings concentrate in five categories:

- **ABI/decode bridge** (R-ABI-C01, R-ABI-H01, R-ABI-H02) — 3 findings
- **Hardware binding discipline** (A-C01, A-H01, A-H02, A-H03, R-HAL-H01..H05) — 8 findings
- **Proof-schema closure** (S-H01, S-H02, NI-H01, NI-H02) — 4 findings
- **Fail-open defaults** (I-H01, I-H02, S-H03, S-H04, SC-H01) — 5 findings
- **Foundational / platform** (F-H01, F-H02, P-H01, P-H02) — 4 findings

No CVE-worthy exploit chains were identified. No systemic design flaws were
found. The 108 LOW findings are predominantly naming, fragility, or
documentation improvements that can be batch-handled in the closure phase.

The remediation is organized into **10 phases** ordered by severity and
subsystem affinity, minimizing cross-phase file contention:

| Phase | Focus | Findings | Sub-tasks |
|-------|-------|----------|-----------|
| AK1 | IPC Fail-Closed & Rendezvous State | 2H + 7M + 6L = 15 | 10 |
| AK2 | Scheduler, PIP & WCRT Closure | 4H + 8M + 6L = 18 | 12 |
| AK3 | Architecture — ASID, W^X, EOI, Decode | 1C + 3H + 10M + 9L = 23 | 13 |
| AK4 | ABI Bridge — Decode, Types, Validation | 1C + 2H + 4M + 8L = 15 | 8 |
| AK5 | Rust HAL Boot Hardening | 5H + 12M + 16L = 33 | 14 |
| AK6 | Information Flow + SchedContext Correctness | 3H + 6M + 7L = 16 | 10 |
| AK7 | Foundational Model (Prelude/Machine/Model) | 2H + 11M + 15L = 28 | 11 |
| AK8 | Capability/Lifecycle/Service + Data Structures | 11M + 21L = 32 | 11 |
| AK9 | Platform, Boot, DTB, MMIO | 2H + 7M + 13L = 22 | 8 |
| AK10 | LOW-tier cleanup, Testing, Documentation, Closure | Residual L + errata | 12 |
| **Total** | — | **2C + 23H + 76M + 101L = 202** (audit sums to 201) | **109** |

**Total disposition:** See §3 for the full finding disposition matrix.
Approximately 147 findings are FIXED in code, 38 DOCUMENTED (by-design or
clarification), 12 DEFER+DOC (WS-V hardware-binding follow-up), and 5 BATCH
(absorbed into a larger fix).

**Gate per phase:** `lake build` + module-level `lake build <Path>` for every
touched module + tier-appropriate test script + `cargo test --workspace` +
`cargo clippy --workspace` + zero `sorry` / `axiom` / `native_decide`.

**Final gate (AK10):** `./scripts/test_full.sh` + `cargo test --workspace` +
`scripts/check_version_sync.sh` + fixture verification + documentation sync.

---

## 2. Audit Verification Results

Every CRITICAL and HIGH finding was independently verified against the current
codebase before planning began; a stratified sample of MEDIUM and LOW findings
was spot-checked. This section documents qualifications, sharper scopings, and
findings requiring interpretation.

### 2.1 CRITICAL Findings — Both Verified Accurate

**A-C01 (CRITICAL) — `AsidPool.allocate` rollover silently returns ASID 1.**
Verified at `SeLe4n/Kernel/Architecture/AsidManager.lean:116-122`. The rollover
branch unconditionally returns `ASID.mk 1` with `requiresFlush := true` and
bumps `generation`, but does not check whether ASID 1 is currently active (no
consultation of an "active set" field — `asidPoolUnique` is stated as a pool
invariant but not preserved by `allocate` itself). On hardware, if VSpace A is
still using ASID 1 when VSpace B allocates post-rollover, both get ASID 1 and
TLB tags collide. A single full TLB flush at rollover is insufficient because
VSpace A's subsequent context switches will re-populate TLB entries tagged
ASID 1 that also match VSpace B's translations.

**R-ABI-C01 (CRITICAL) — `service_register`/`sched_context_configure` decode
failure against production kernel.** Verified at `SeLe4n/Machine.lean:848`
(`arm64DefaultLayout.msgRegs := #[⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]` — exactly 4 entries) and
at `SyscallArgDecode.lean:775-786` + `:958-966` (both `decodeServiceRegisterArgs`
and `decodeSchedContextConfigureArgs` call `requireMsgReg decoded.msgRegs 4`
which indexes position 4, requiring `msgRegs.size ≥ 5`). Also verified at
`rust/sele4n-sys/src/service.rs:40` and `rust/sele4n-sys/src/sched_context.rs:49`
that the Rust wrappers write MR[4] via `set_mr`, assuming the Lean side merges
the IPC buffer overflow slot into `msgRegs`. No such merge step exists in
`RegisterDecode.lean:decodeSyscallArgs`. The audit's claim that both syscalls
fail decoding is mechanically correct.

### 2.2 Findings Requiring Qualification (3)

**A-H01 (HIGH) — ARMv8 W^X.** The audit claims `ARMv8VSpace.mapPage` has no
W^X gate. Verified: `VSpaceARMv8.lean:169-189` delegates to
`shadow.mapPage` (which also does not gate W^X) and to `fromPagePermissions`
which, under `execute=true, write=true, user=true`, produces `ap=.rwAll,
uxn=false` — a W+X user page. The `vspaceMapPage` wrapper (`VSpace.lean:101`)
does enforce W^X but any direct `VSpaceBackend.mapPage` call bypasses it. The
finding is accurate; the remediation must add W^X gates at **three** layers
(wrapper, ARMv8 backend, `fromPagePermissions`) plus Rust HAL SCTLR.WXN
(R-HAL-H03) for four-layer defense-in-depth.

**R-HAL-H02 (HIGH) — MMU enable sequence.** Verified partially: `mmu.rs:162-181`
does perform `DSB ISH` + `ISB` after TTBR writes, but does NOT perform
`tlbi vmalle1` (to invalidate stale TLB entries from prior boots / warm resets)
and does NOT clean D-cache of the `BOOT_L1_TABLE` page before enabling. On a
cold boot from reset with caches initially disabled, stale cache lines above
the L1 page will race the walker after SCTLR.C=1. Audit finding stands, scoped
to "TLB flush and page-table D-cache clean are missing before MMU enable."

**NI-H02 (HIGH) — `syscallDispatchHigh` `hProj` hypothesis.** Verified at
`API.lean:1886-1898` and `Composition.lean:295-299`. The integration accepts
`hDispatchProj` as a caller-supplied hypothesis for the arms routed through
`dispatchCapabilityOnly`. Each of those arms (`suspendThread`, `resumeThread`,
`setPriorityOp`, `setMCPriorityOp`, `setIPCBufferOp`, `schedContextConfigure`,
`schedContextBind`, `schedContextUnbind`, `vspaceMapPage`, `vspaceUnmapPage`,
`revokeService`) has an individual `*_preserves_projection` theorem in
`InformationFlow/Invariant/Operations.lean`, but they are not composed into a
single `dispatchCapabilityOnly_preserves_projection` theorem that internally
discharges `hProj`. The audit's claim that the bridge "does not cover these"
is strictly correct; remediation is a composition theorem, not new operational
proofs.

### 2.3 Findings Requiring Sharper Scoping (2)

**S-H03 (HIGH) — re-enqueue priority.** Confirmed accurate after re-reading:
`Scheduler/Operations/Core.lean:337` (`handleYield`), `:390` (`timerTick`
preemption), `:776` (`switchDomain`) all use `effectiveRunQueuePriority tcb`
which reads `tcb.priority + tcb.pipBoost`. Selection (`Selection.lean:370-394`,
`chooseBestRunnableEffective`) uses `resolveEffectivePrioDeadline` which for
SC-bound threads returns `sc.priority` (fallback to `tcb.priority` only when
unbound). The right comparator for "which bucket does the thread live in" is
`resolveInsertPriority` (`Selection.lean:354`) which internally calls
`resolveEffectivePrioDeadline`. The already-correct paths
(`processReplenishmentsDue` at `:455`, `timerTickBudget` SC-aware branch at
`:575`, `switchDomain` SC-aware branch at `:701`) demonstrate the pattern.
The three bug sites are therefore: `:337`, `:390`, `:776`. `timerTickBudget`
at `:546` (audit claim "unbound branch") needs explicit verification —
re-reading §2.3 clarifies that `timerTickBudget` has two branches and only
the unbound fallback (identical to `timerTick` at `:390`) requires the fix.

**R-HAL-M12 (MEDIUM) — SError handler signature.** `trap.rs:239-244` defines
`pub extern "C" fn handle_serror(_frame: &mut TrapFrame)` with body
`loop { crate::cpu::wfe(); }`. The infinite loop prevents fall-through, so no
dead `eret` is actually reachable. However, the return type should be `-> !`
(never-type) to (a) inform LLVM that the function cannot return, enabling
better codegen, (b) document the contract, and (c) match `trap.S:125-148`
which expects the handler to never return to the vector. Treat as a
hygiene/documentation fix; code path is already defensively infinite-loop.

### 2.4 Audit-Claimed Counts Cross-Reference

| Claim | Verification |
|-------|--------------|
| 140 Lean modules (~94,749 LOC) | Confirmed via `find SeLe4n -name '*.lean' \| wc -l` |
| 48 Rust sources (~9,739 LOC) | Confirmed via `find rust -name '*.rs' \| wc -l` |
| 8 `sorry`/`axiom`/`native_decide` matches | All 8 are comments; no production use |
| Version `0.29.0` synced across lakefile / Cargo / boot.rs | Confirmed via `check_version_sync.sh` |

### 2.5 Findings Confirmed as By-Design / Deferred to WS-V

Several findings describe deliberate design decisions already documented or
deferred to the forthcoming WS-V hardware-binding workstream. Each gets a
DOCUMENT disposition (tag + cross-reference), not a code change:

| Finding | Disposition |
|---------|-------------|
| A-M04 TLB+cache composition | DEFER to WS-V (AG10) — documented as proof-layer gap |
| A-M06 `tlbBarrierComplete := True` | DEFER to WS-V — carried from AG8-G |
| A-M08 MMU/Device-memory ordering | DEFER to WS-V — BarrierKind skeleton in place |
| A-M09 `ensureTable` coherency | DEFER to WS-V — page-table cache maintenance |
| C-M04 `suspendThread` H3-ATOMICITY | DEFER to WS-V — preserves WS-AI2 annotation |
| F-L09 17-deep tuple projections | DEFER to proof-hygiene pass (post-1.0) |
| P-L9 VSpaceRoot boot exclusion | DEFER to WS-V — tracked finding |
| R-HAL-L-14 SVC `_syscall_id` unused | DEFER to WS-V/AG10 — FFI wiring phase |

---

## 3. Finding Disposition Matrix

Every non-informational finding is classified into exactly one disposition.
The full disposition table is broken out by severity and phase below.

| Disposition | Count (approx) | Description |
|-------------|----------------|-------------|
| **FIX** | ~147 | Code change required in this workstream |
| **DOCUMENT** | ~38 | Documentation-only (by-design, clarification, or tag) |
| **DEFER+DOC** | ~12 | Deferred to WS-V with activation roadmap documented here |
| **BATCH** | ~5 | Fixed as part of a larger structural change in another finding |
| **Total** | 202 | (2C + 23H + 76M + 101L — see §2.4 count reconciliation) |

Disposition counts are approximate because several findings map to multiple
dispositions (e.g., F-M04 is both FIX-baseline + DEFER-cascade). Exact
disposition per finding is given inline in each phase's sub-tasks.

### 3.1 Phase Ordering Rationale

Phases are ordered to:

1. **Minimize cross-phase file contention** — files touched in Phase X are
   not touched again in later phases, so that phase gates can commit cleanly.
2. **Respect dependency graph** — Phase AK3 (Architecture) produces typed
   IDs and decode validation that Phase AK4 (ABI) consumes. Phase AK5
   (Rust HAL) depends on Phase AK3 SCTLR / EOI decisions. Phase AK6 (NI
   projection) depends on Phase AK1 (IPC) field reshaping.
3. **Concentrate hardware-binding risk** — AK3, AK4, AK5 together constitute
   the "pre-bring-up blockers" from the audit's §9.4.
4. **Leave proof-heavy surface for later phases** — AK6, AK7 require updating
   dozens of preservation theorems; running them after correctness fixes lets
   theorem updates track real semantics.
5. **Leave closure phase self-contained** — AK10 touches only docs, fixtures,
   CLAUDE.md, and version-bump files.

### 3.2 Mapping from Audit IDs to Phases

The full audit ID → phase mapping appears in each phase header. Summary:

- **CRITICAL (2):** A-C01 → AK3, R-ABI-C01 → AK4.
- **HIGH (23):** AK1 (2), AK2 (4), AK3 (3), AK4 (2), AK5 (5), AK6 (3), AK7 (2), AK9 (2).
- **MEDIUM (68):** distributed across all 10 phases.
- **LOW (108):** batch-documented in phase-local doc blocks + AK10 cleanup.

---

## 4. Phase AK1: IPC Fail-Closed & Rendezvous State

**Priority:** Critical path — fail-open defaults are one invariant regression
away from confused-deputy defects.
**Audit findings addressed:** I-H01, I-H02, I-M01, I-M02, I-M03, I-M04, I-M05,
I-M06, I-M07, I-L1..I-L6, IPC INFO items.
**Primary files:** `IPC/Operations/Endpoint.lean`, `IPC/DualQueue/Transport.lean`,
`IPC/DualQueue/WithCaps.lean`, `IPC/DualQueue/Core.lean`,
`IPC/Operations/CapTransfer.lean`, `IPC/Operations/Timeout.lean`,
`IPC/Invariant/*.lean`, `API.lean`, `InformationFlow/Invariant/Operations.lean`.
**Gate:** `lake build` + `lake build SeLe4n.Kernel.IPC.DualQueue.Transport` +
`test_smoke.sh` + `test_full.sh` (IPC invariant impact).

### AK1-A: `cleanupPreReceiveDonation` Error Propagation (I-H01 / HIGH)

**Problem:** `IPC/Operations/Endpoint.lean:296-298` handles
`returnDonatedSchedContext` failure with `| .error _ => st`, silently swallowing
every error and proceeding to block the receiver. Under current IPC invariants
this branch is unreachable (by `donationOwnerValid` + `boundThreadConsistent`),
but no proof at the call site discharges this. AJ1-A / AI4-A established the
codebase's error-propagation policy; this is the last remaining violator.

**Decomposed steps:**

1. **Signature change** — change return type from `SystemState` to
   `Except KernelError SystemState`. Replace `| .error _ => st` with
   `| .error e => .error e`; wrap the `.bound`/`.unbound`/not-donated branches
   with `.ok st`.
2. **Caller cascade** — `endpointReceiveDual` (`Transport.lean`, no-sender
   branch) invokes `cleanupPreReceiveDonation` before blocking. Change the
   call site to `match cleanupPreReceiveDonation st tid with | .ok s => ... |
   .error e => .error e`.
3. **Frame lemmas** — update the 6 frame lemmas in
   `Invariant/Defs.lean` (added in AI4-A: `cleanupPreReceiveDonation_scheduler_eq`,
   `_preserves_objects_invExt`, `_tcb_forward`, `_tcb_ipcState_backward`,
   `returnDonatedSchedContext_notification_backward`,
   `returnDonatedSchedContext_endpoint_backward`) to conditional postconditions
   (`∀ st', cleanupPreReceiveDonation st tid = .ok st' → ...`).
4. **Preservation cascade** — update `endpointReceiveDual_preserves_*`
   theorems in `EndpointPreservation.lean`, `Structural.lean`,
   `InformationFlow/Invariant/Operations.lean` (≥16 theorems from AI4-A list)
   to pattern-match on the `Except` result.
5. **NI preservation** — `endpointReceive_preserves_projection` gains the
   same conditional.

**Acceptance criteria:**
- `lake build SeLe4n.Kernel.IPC.Operations.Endpoint` ✓
- All AI4-A preservation theorems re-prove without `sorry`/`axiom`
- `cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull` lemma
  discharges "unreachable under invariants" formally

### AK1-B: Reply/ReplyRecv `blockedOnReply _ none` Fail-Closed (I-H02 / HIGH)

**Problem:** `DualQueue/Transport.lean:1777-1785, 1809-1815`. When
`replyTarget = none` on `.blockedOnReply`, both `endpointReply` and
`endpointReplyRecv` set `authorized := true` and let the reply through. The
16th conjunct `blockedOnReplyHasTarget` (AJ1-B) excludes this case invariant-
preservation-wise, but the operational path fails open.

**Decomposed steps:**

1. **Operational change** — replace `| none => { ... authorized := true }`
   with `| none => .error .replyCapInvalid` in both `endpointReply` and
   `endpointReplyRecv`.
2. **Soundness bridge** — prove
   `blockedOnReplyHasTarget_implies_some_replyTarget :
     ipcInvariantFull st → st.objects[tid] = some (.tcb tcb) →
     tcb.ipcState = .blockedOnReply → ∃ t, tcb.replyTarget = some t`
   in `Invariant/Defs.lean`.
3. **Proof update** — update `endpointReply_preserves_*` and
   `endpointReplyRecv_preserves_*` theorems to use the new fail-closed branch;
   the `none` case is now trivially preserved via `.error` propagation.
4. **NI proof** — `endpointReply_preserves_projection`: the `.error` branch
   preserves state identity, hence NI-step trivially.

**Acceptance criteria:**
- No behavior change on paths satisfying `ipcInvariantFull` (proven via bridge
  lemma).
- Invariant drift now produces `.error .replyCapInvalid` instead of silent
  misdelivery.

### AK1-C: Clear Caller's `pendingMessage` on Call Handshake (I-M01 / MEDIUM)

**Problem:** `Transport.lean:1728-1739`. On `endpointCall` rendezvous, the
caller's `pendingMessage` is never cleared after handshake; caller transitions
to `.blockedOnReply` retaining the outbound message. On protocol regression or
self-call, this leaks the message.

**Steps:**

1. Add `storeTcbIpcStateAndMessage callerTid .blockedOnReply none` after the
   message is transferred to the receiver (or `pendingMessage := none` in the
   TCB update). Exact insertion site: between the receiver-side update and
   the caller-side `.blockedOnReply` transition.
2. Update `endpointCall_preserves_pendingMessageValid` in
   `Invariant/CallReplyRecv.lean`.
3. Update NI preservation: `endpointCall_preserves_projection`.

### AK1-D: Receive-Rendezvous Updates `ipcState` (I-M02 / MEDIUM)

**Problem:** `Transport.lean:1639-1671`. When a waiting sender is dequeued,
`senderMsg` is written into receiver's `pendingMessage` but receiver's
`ipcState` remains `.blockedOnReceive`, silently violating the 5th conjunct
`waitingThreadsPendingMessageNone`.

**Steps:**

1. Add `storeTcbIpcState receiverTid .ready` in the rendezvous branch.
2. Re-prove `endpointReceiveDual_preserves_waitingThreadsPendingMessageNone`
   in `Invariant/WaitingThreadHelpers.lean`.
3. Audit `endpointReceiveDual_preserves_*` for downstream effects (14
   preservation theorems).

### AK1-E: PIP-Effective Priority on Notification Wake (I-M03 / MEDIUM)

**Problem:** `IPC/Operations/Endpoint.lean:385-388`. `notificationSignal`
wake path uses base `tcb.priority` for RunQueue insertion; a PIP-boosted
server lands in the wrong bucket until the next tick. Contradicts AI3-A
pattern (yield/timer/switch already fixed — but notification wake was missed).

**Steps:**

1. Change `insert tid tcb.priority` → `insert tid (effectiveRunQueuePriority tcb)`.
2. Update `notificationSignal_preserves_schedulerPriorityMatch`.
3. Add `notificationSignal_respects_pipBoost` correctness lemma.

### AK1-F: Document `timeoutThread` PIP Revert Call-State Gap (I-M04 / MEDIUM)

**Problem:** `Operations/Timeout.lean:76-100`. PIP revert only covers
`.blockedOnReply`. Correct today because PIP is only attached to reply-
blocked chains, but fragile.

**Steps:**

1. Add doc comment at `timeoutThread` entry documenting the invariant
   `pipBoost.isSome → tcb.ipcState = .blockedOnReply`, referencing
   `BlockingGraph.lean` chain construction.
2. Add Lean theorem `pipBoost_attached_only_on_reply_blocked` that states
   this invariant (already true under current semantics — proof is the
   `propagatePipBoost` frame lemma bundle).

### AK1-G: Mark `ipcUnwrapCapsLoop` Non-Public (I-M05 / MEDIUM)

**Problem:** `CapTransfer.lean:95-97, 132-134`. Public function with fuel
parameter; calling at `idx > 0` produces off-by-one padding and silently
drops caps.

**Steps:**

1. Mark `ipcUnwrapCapsLoop` as `private` (or add `@[reducible] private def`
   if already used in external proofs).
2. Verify only `ipcUnwrapCaps` (which supplies `idx := 0`) is exported.
3. Add static assertion via `example` in the file: `ipcUnwrapCapsLoop` only
   called with `idx = 0` from `ipcUnwrapCaps`.

### AK1-H: Compose `endpointQueueRemove` Unreachability (I-M06 / MEDIUM)

**Problem:** `DualQueue/Core.lean:482-494`. Defensive fallback arms have
unreachability lemmas (`queueRemove_predecessor_exists`,
`queueRemove_successor_exists`) but they are not composed at call sites.

**Steps:**

1. Add `endpointQueueRemove_fallback_unreachable :
     endpointQueueWellFormed q →
     tid ∈ queueMembers q →
     endpointQueueRemove q tid ≠ .error _` in `DualQueue/Core.lean`.
2. At each caller (search `grep -rn endpointQueueRemove SeLe4n/Kernel`), add
   a proof that `tid ∈ queueMembers q` holds from the IPC invariant at that
   site, then use the composition lemma to eliminate the defensive branch.

### AK1-I: Symmetric Cap-Root Error Handling (I-M07 / MEDIUM, NI L-1)

**Problem:** `DualQueue/WithCaps.lean:110-121, 152-153`. Missing receiver
CSpace root on send returns `.ok (empty)`; missing sender CSpace root on
receive returns `.error .invalidCapability`. Asymmetry is a per-pair
information-flow distinguisher observable across domains.

**Steps:**

1. Align: change the send path to also return `.error .invalidCapability`
   when receiver CSpace root is missing. Callers (`endpointSendDualWithCaps`
   in `API.lean`) already absorb `Except`.
2. Re-prove `endpointSendDualWithCaps_preserves_projection` — the symmetric
   error case now preserves state identity by construction (both domains
   observe an `.error`).
3. Add NI regression test asserting symmetric error behavior in
   `tests/InformationFlowSuite.lean`.

### AK1-J: LOW-tier IPC Batch (I-L1..I-L6, IPC INFO)

**Findings batched:**
- I-L1 `donateSchedContext` unproven-unreachable defensive branch — add
  unreachability lemma.
- I-L2 `timeoutAwareReceive` stale `.timedOut` reachability — document
  under `timedOutInvariant`.
- I-L3 `endpointCallWithDonation` `popHead_returns_head` external — compose
  into local lemma.
- I-L4 reply-path badge handling TODO — close TODO with seL4 cross-ref.
- I-L5 `notificationSignal.Badge.bor` unbounded `Nat` — document safety
  via `Badge` 64-bit wrapping.
- I-L6 `returnDonatedSchedContext` leaves client in replenish queue —
  prove benign via `isActive := false` filter in replenish processing.
- IPC INFO rename `ipcInvariant` to `notificationInvariantSystem` — rename
  with deprecation shim.
- IPC INFO `.endpointQueueEmpty` error misuse — replace with
  `.invalidIpcState` at AH2-G site.

Each fix is ≤10 lines; handle all as a single commit at the end of AK1.

---

## 5. Phase AK2: Scheduler, PIP & WCRT Closure

**Priority:** Critical path — S-H03 is a concrete priority-inversion vector;
S-H01/S-H02 close release-grade liveness claims.
**Audit findings addressed:** S-H01, S-H02, S-H03, S-H04, S-M01..S-M08,
S-L13..S-L18.
**Primary files:** `Scheduler/Operations/Core.lean`, `Operations/Selection.lean`,
`Operations/Preservation.lean`, `Scheduler/Invariant.lean`,
`PriorityInheritance/BlockingGraph.lean`, `BoundedInversion.lean`,
`Liveness/WCRT.lean`, `Liveness/BandExhaustion.lean`,
`SchedContext/Budget.lean`, `SchedContext/ReplenishQueue.lean`,
`SchedContext/Operations.lean`, `SchedContext/PriorityManagement.lean`.
**Gate:** `lake build` + per-module build + `test_full.sh` + zero sorry.

### AK2-A: Re-enqueue at Effective Insert Priority (S-H03 / HIGH)

**Problem:** Three production re-enqueue paths use `effectiveRunQueuePriority
tcb` (reads only TCB fields + PIP boost), while selection uses
`resolveEffectivePrioDeadline` which consults the bound `SchedContext`. For
an SC-bound thread with `sc.priority ≠ tcb.priority`, the thread is placed
into the TCB-priority bucket but selection looks it up at SC priority —
`chooseBestInBucketEffective` misses it, and the bucket becomes a starvation
pit.

**Sites (verified):**
- `Operations/Core.lean:337` — `handleYield` re-enqueue before reschedule.
- `Operations/Core.lean:390` — `timerTick` preemption (time-slice-expired
  branch, `tcb.timeSlice ≤ 1`).
- `Operations/Core.lean:776` — `switchDomain` unbound fallback branch.

**Note:** `timerTickBudget` at `:546` is already correct — verified that it
calls `resolveInsertPriority` in the SC-aware branch.

**Steps:**

1. For each of the three sites, replace
   `rq.insert tid (effectiveRunQueuePriority tcb)` with a match on
   `getSchedContext st tid`:
   - If bound to `sc`: `rq.insert tid (resolveInsertPriority st tid sc)`.
   - If unbound: `rq.insert tid (effectiveRunQueuePriority tcb)` (keeps
     current behavior — matches `resolveEffectivePrioDeadline` unbound arm).
2. Prove `handleYield_respects_effective_priority`,
   `timerTick_respects_effective_priority`,
   `switchDomain_respects_effective_priority` bridge lemmas asserting
   `priorityOf(runQueue.lookup tid) = (resolveEffectivePrioDeadline st tcb).1`.
3. Update `Preservation.lean` theorems for each of the three ops
   (`handleYield_preserves_schedulerPriorityMatch`, etc.) — no semantic
   change under `schedContextBindingConsistent`.

**Risk:** This is a behavioral change. Add a regression test in
`tests/MainTraceHarness.lean` that exercises an SC-bound thread with
`sc.priority > tcb.priority` undergoing yield → re-select → dispatch, and
verify the trace shows the thread re-selected at SC priority (not TCB).

### AK2-B: Fuse Priority-Match Predicates (S-H04 / HIGH)

**Problem:** `Scheduler/Invariant.lean:291-296` (`schedulerPriorityMatch`:
`threadPriority[tid] = some tcb.priority`) and `:560-572`
(`effectiveParamsMatchRunQueue`: `threadPriority[tid] = some sc.priority`
for SC-bound threads) are both conjuncts of
`schedulerInvariantBundleExtended`. For any SC-bound thread with
`pipBoost = none`, both fire and jointly force `tcb.priority = sc.priority`
— an equality that `schedContextBind`/`schedContextConfigure` do not
establish.

**Remediation strategy (option A — fuse):**

1. Introduce a single SC-aware predicate `priorityMatchAware`:
   ```
   def priorityMatchAware (st : SystemState) : Prop :=
     ∀ tid, st.scheduler.runQueue.contains tid →
       match getSchedContext st tid with
       | some sc => st.scheduler.threadPriority.get? tid = some sc.priority
       | none    => ∃ tcb, st.objects.get? tid.toObjId = some (.tcb tcb) ∧
                    st.scheduler.threadPriority.get? tid = some tcb.priority
   ```
2. Remove `schedulerPriorityMatch` and `effectiveParamsMatchRunQueue` from
   `schedulerInvariantBundleExtended`; add `priorityMatchAware`.
3. Cascade update to every `_preserves_schedulerPriorityMatch` theorem (≥40
   theorems in `Preservation.lean`) — the new predicate subsumes both.
4. Cascade update `apiInvariantBundle` to use the new predicate name.

**Fallback strategy (option B — enforce equality):** If the fused predicate
proves too invasive, instead enforce `tcb.priority = sc.priority` at
`schedContextBind` and `schedContextConfigure` entry (reject binding if
unequal). This matches seL4 MCS (bind establishes SC ownership and
propagates priority). Preferred unless ≥3 downstream callers break.

**Decision:** Attempt option A first; fall back to option B with a
documented rationale if the predicate cascade exceeds 60 theorems.

### AK2-C: `blockingChain` Fuel-Exhaustion Error (S-M01 / MEDIUM)

**Problem:** `PriorityInheritance/BlockingGraph.lean:86-96, 128`. Returns
`[]` on fuel exhaustion. Under invariant violation, PIP stops mid-chain
and stale `pipBoost` persists.

**Steps:**

1. Change return type from `List ThreadId` to
   `Except BlockingChainError (List ThreadId)`.
2. Define `BlockingChainError := fuelExhausted | cycleDetected`.
3. Callers in `Propagate.lean` propagate the error; `schedContextBind`
   already `Except`-typed.
4. Update `blockingChain_frame` and `blockingAcyclic_frame` lemmas.

### AK2-D: `timeoutBlockedThreads` Error Surfacing (S-M02 / MEDIUM)

**Problem:** `Operations/Core.lean:580`. `_timeoutErrors` variable discards
per-thread timeout error list; a non-empty list indicates invariant violation
and is currently invisible.

**Steps:**

1. Rename `_timeoutErrors` → `timeoutErrors`, return via a diagnostic field
   on the scheduler state (`SchedulerState.lastTimeoutErrors : List (ThreadId
   × KernelError)`) or surface via `.error .timeoutPartialFailure` when
   non-empty.
2. Option A (diagnostic): preserves semantics; downstream consumers ignore.
3. Option B (error): changes semantics; requires cascading `Except` to
   `timerTickBudget` callers.
4. Preferred: option A (diagnostic field), cleared on next timer tick.

### AK2-E: CBS Admission Ceiling-Round (S-M03 / MEDIUM)

**Problem:** `SchedContext/Budget.lean:208-228`. Aggregate over-admission up
to ~6.4% for 64 SCs due to truncation-down. For a safety-critical RT kernel
this can violate `cbs_bandwidth_bounded`.

**Steps:**

1. Replace truncation-down
   `(budget.val * 1000) / period.val` with ceiling-round
   `((budget.val * 1000) + period.val - 1) / period.val` in
   `admissionCheck` utilization sum.
2. Update `cbs_bandwidth_bounded` proof in `Invariant/Defs.lean` — tighter
   bound follows immediately (4 lines).
3. Update `docs/spec/SELE4N_SPEC.md` §5.4 (CBS admission) to document the
   rounding direction.

### AK2-F: `ReplenishQueue.insertSorted` Strict Inequality (S-M04 / MEDIUM)

**Problem:** `SchedContext/ReplenishQueue.lean:67`. Non-strict `≤` →
equal-eligibility replenishments are processed LIFO.

**Steps:**

1. Change comparator from `≤` to `<` (strict) in `insertSorted`.
2. Prove `insertSorted_fifo_within_tie : eligibleAt a = eligibleAt b →
   position_of a in inserted ≤ position_of b`.
3. Document the FIFO-within-tie guarantee in the function docstring.

### AK2-G: `schedContextConfigure` Removes Stale Replenish Entries (S-M05 / MEDIUM)

**Problem:** `SchedContext/Operations.lean:90-113`. `schedContextConfigure`
stores the new replenishment but does not remove prior stale entries in
`replenishQueue`. `processReplenishmentsDue` may redundantly enqueue the
already-runnable thread.

**Steps:**

1. At entry of `schedContextConfigure`, after validation, call
   `st.scheduler.replenishQueue.remove scId` to clear stale entries.
2. Update `schedContextConfigure_preserves_replenishQueueWellFormed` —
   remove operation preserves sort order trivially.
3. Add `schedContextConfigure_no_stale_replenishments` correctness lemma.

### AK2-H: Route Production through `*Checked` Save/Restore (S-M06 / MEDIUM)

**Problem:** `Scheduler/Operations/Selection.lean:487-495, 560-564`. Under
`currentThreadValid` the unchecked variants are provably safe, but
production routes through them — any invariant drift silently drops
register state.

**Steps:**

1. Change `schedule` and `switchDomain` to invoke `saveOutgoingContextChecked`
   and `restoreIncomingContextChecked` instead of the unchecked variants.
2. Preservation theorems already use the `*Checked` variants (AI3-C); update
   the three production call sites to pattern-match on `Except`.
3. Under `currentThreadValid`, the `.error` branch is unreachable
   (existing proof `saveOutgoingContext_always_succeeds_under_currentThreadValid`
   from AI3-C) — propagate as `.error .schedulerInvariantViolation` otherwise.

### AK2-I: `switchDomain` Fallback Emits Error (S-M07 / MEDIUM)

**Problem:** `Operations/Core.lean:756-764`. Unreachable fallback returns
`.ok ((), st)`. Boot-config bug violating `domainScheduleEntriesPositive`
silently stops rotation.

**Steps:**

1. Change fallback to `.error .schedulerInvariantViolation`.
2. Existing unreachability lemma `switchDomain_index_in_bounds` discharges
   the branch at all valid call sites.
3. Update `switchDomain_preserves_*` theorems to absorb the `.error`
   unreachable-arm pattern.

### AK2-J: `migrateRunQueueBucket` Fallback Preservation (S-M08 / MEDIUM)

**Problem:** `SchedContext/PriorityManagement.lean:109-122`. Fallback uses
raw `newPriority`, potentially erasing PIP boost on partially-constructed
state.

**Steps:**

1. In the fallback branch, take the max of `newPriority` and any existing
   `pipBoost`, matching AI3-B fix for the primary path.
2. Update `migrateRunQueueBucket_respects_pipBoost` theorem.

### AK2-K: WCRT Proof-Schema Closure (S-H01, S-H02 / HIGH — DEFER-WITH-ROADMAP)

**Problem:** `Liveness/WCRT.lean:181-226` and `PriorityInheritance/
BoundedInversion.lean:39-43`. WCRT theorem is a proof schema with externalized
hypotheses `hDomainActiveRunnable`, `hBandProgress`, `eventuallyExits`. PIP
bounded inversion bounds depth by fuel (`objectIndex.length`), not by
structural blocking chain.

**Assessment:** Closing these proof schemas fully requires deriving the
load-bearing hypotheses from invariants — a substantial proof-engineering
investment (est. 2000+ lines of new proofs spanning CBS budget finiteness,
domain-schedule non-emptiness, and blocking-chain acyclicity under
`blockingAcyclic`).

**Decomposed steps (partial closure — what is achievable in AK2):**

1. **AK2-K.1: Derive `hBandProgress` from CBS budget finiteness.** Prove
   `band_progress_from_cbs :
     ∀ band, domainActive st band → cbs_bandwidth_bounded st → ∃ tick, band_consumed st tick band`
   using `consumeBudget_budgetRemaining_le` (already proven). Estimated
   ~200 lines in `Liveness/BandExhaustion.lean`.

2. **AK2-K.2: Derive `hDomainActiveRunnable` from schedule invariant.** Use
   `scheduleDomain` + `domainScheduleEntriesPositive` + `runQueueNonEmpty`
   conjunct to derive `∃ tid, runnable st tid ∧ domainOf tid = currentDomain`.
   Estimated ~150 lines in `Liveness/WCRT.lean`.

3. **AK2-K.3: Structural PIP bound (S-H02).** Replace fuel bound with
   `pip_bounded_inversion_structural :
     blockingAcyclic st → chainDepth ≤ distinct_reply_blocked_tcbs`
   where `distinct_reply_blocked_tcbs` counts unique TCBs in `.blockedOnReply`
   state. This is finite because `objectIndex` is finite. Requires proving
   the chain is injective on TCB IDs under `blockingAcyclic`. Estimated ~250
   lines in `BoundedInversion.lean`.

4. **AK2-K.4: Remaining `eventuallyExits` hypothesis.** Derive from WS-M
   (meta-level liveness assumption that no thread remains in `.blockedOnReply`
   indefinitely). This remains an externalized hypothesis **by design** —
   WCRT cannot be proven without an assumption that replies eventually
   complete. Document this clearly in `WCRT.lean` and `SELE4N_SPEC.md`.

5. **If AK2-K.1/K.2/K.3 exceed 1200 cumulative lines of new proof**, split
   into a follow-up phase AK2.5 to be executed after AK2 baseline lands.

**Acceptance criteria (AK2-K):**
- `hBandProgress` and `hDomainActiveRunnable` are no longer caller-supplied
  hypotheses; derived internally from invariants.
- `pip_bounded_inversion` bound is `distinct_reply_blocked_tcbs`, not fuel.
- `eventuallyExits` remains externalized but is **explicitly documented as
  the sole remaining WCRT assumption**, with seL4 correspondence.

### AK2-L: LOW-tier Scheduler Batch (S-L13..S-L18)

- S-L13 `handleYield` error semantics — document `.invalidArgument` vs
  `.schedulerInvariantViolation` policy.
- S-L14 `getCurrentPriority` silent fallback — already addressed in AE3
  hardening; re-verify; add `.error` branch if dead-code analysis fails.
- S-L15 `oid.toNat→ThreadId` direct cast — use `ThreadId.ofObjId` with
  sentinel handling.
- S-L16 `isBetterCandidate_transitive` proof brittleness — refactor using
  structural-recursion lemma.
- S-L17 `⟨Nat.max …⟩` bypasses `Priority` validity — route through
  `Priority.ofNat?` with clamp or error.
- S-L18 `runQueueUnique` flat-list only — add per-bucket uniqueness lemma
  (useful for AK2-A correctness).

---

## 6. Phase AK3: Architecture — ASID, W^X, EOI, Decode

**Priority:** CRITICAL — contains the A-C01 ASID rollover bug which
breaks TLB isolation on hardware. Must land before first silicon.
**Audit findings addressed:** A-C01, A-H01, A-H02, A-H03, A-M01..A-M10,
A-L1..A-L9.
**Primary files:** `Architecture/AsidManager.lean`, `VSpaceARMv8.lean`,
`VSpace.lean`, `PageTable.lean`, `InterruptDispatch.lean`, `TimerModel.lean`,
`TlbModel.lean`, `CacheModel.lean`, `SyscallArgDecode.lean`,
`IpcBufferValidation.lean`, `ExceptionModel.lean`, `VSpaceInvariant.lean`.
**Gate:** `lake build` + per-module build + `test_full.sh` +
`cargo test --workspace` (HAL-side consistency) + zero sorry.

### AK3-A: ASID Pool Rollover Correctness (A-C01 / CRITICAL)

**Problem:** `AsidManager.lean:116-122`. Rollover branch unconditionally
returns `ASID.mk 1` on `nextAsid = maxAsidValue`, without checking whether
ASID 1 is still active. Breaks TLB isolation.

**Remediation strategy:** Track an explicit active-ASID set inside the pool
and make rollover fail-closed until a free ASID is actually available via
`free`. Generation bumping alone is insufficient because VSpace A running
with the old generation can re-TLB entries tagged ASID 1 between VSpace B's
allocation and VSpace B's first context switch.

**Decomposed steps:**

1. **Add `activeSet : HashSet ASID` to `AsidPool`** (replace or supplement
   `activeCount : Nat`).
2. **`allocate` correctness:** on rollover, scan `activeSet` for a free
   value in `[1, maxAsidValue)`. If none found, return `none` (exhaustion).
   If found, insert into `activeSet`, bump `generation`, set
   `requiresFlush := true`.
3. **`free` correctness:** remove from `activeSet`; prepend to `freeList`.
4. **Invariants:**
   - `AsidPool.wellFormed`: `freeList.toSet ⊆ activeSet`, `activeSet.size
     ≤ maxAsidValue`.
   - `asidPoolUnique_preserved_by_allocate`: prove formally that
     `allocate pool = some result → result.asid ∉ pool.activeSet`.
5. **Hardware side (coordinate with AK5-F):** `tlb::tlbi_asid` on free
   list reuse (AI2-C already does this). Generation bump at rollover also
   triggers `tlb::tlbi_vmalle1` via `requiresFlush`.
6. **Proof update:** `asidPoolUnique` is now preserved by `allocate` rather
   than deferred to caller integration layer.

**Acceptance criteria:**
- No rollover can return a currently-active ASID.
- `asidPoolUnique` is an internal `AsidPool` invariant, not a caller
  obligation.
- Exhaustion (`allocate → none`) is reachable only when `activeSet.size =
  maxAsidValue - 1`.

### AK3-B: W^X at All VSpace Layers (A-H01, A-M03 / HIGH + MEDIUM)

**Problem:** W^X is enforced only at the `vspaceMapPage` wrapper
(`VSpace.lean:101`). Direct `VSpaceBackend.mapPage` / `shadow.mapPage`
bypasses enforcement. `fromPagePermissions` (`VSpaceARMv8.lean:137-149`)
under `execute=true, write=true, user=true` produces `ap=.rwAll, uxn=false`
(W+X user page).

**Remediation:** Four-layer defense-in-depth.

1. **Layer 1 (backend typeclass):** `VSpaceBackend.mapPage` requires
   `perms.wxCompliant = true` as a precondition; `ARMv8VSpace.mapPage`
   adds `if !perms.wxCompliant then none` at entry.
2. **Layer 2 (`VSpaceRoot.mapPage`):** same `wxCompliant` gate at entry.
3. **Layer 3 (`fromPagePermissions`):** change signature to
   `Option HwPageAttributes` returning `none` on W^X violation, OR emit
   an `.execute-never` forced variant. Preferred: return `none` to fail
   closed.
4. **Layer 4 (Rust HAL SCTLR):** see AK5-C (WXN=1).

**Proof updates:**
- `vspaceMapPage_preserves_wxExclusiveInvariant` — already exists; add
  `ARMv8VSpace_mapPage_preserves_wxExclusiveInvariant` and
  `VSpaceRoot_mapPage_preserves_wxExclusiveInvariant`.
- Add `fromPagePermissions_wx_excludes_W_and_X` lemma.

### AK3-C: GIC EOI Differentiation (A-H02 / HIGH)

**Problem:** `InterruptDispatch.lean:127-137`. Every `acknowledgeInterrupt =
none` is treated as spurious and skips EOI. INTIDs 224-1019 (valid hardware
range) that fail acknowledge due to errata or SMP races get no EOI → GIC
lockup.

**Steps:**

1. Change `acknowledgeInterrupt` to return
   `Except AckError (InterruptId × Priority)` where
   `AckError := spurious | outOfRange | erratum`.
2. Distinguish:
   - `≥ 1020`: `.error .spurious` → skip EOI (correct per GIC spec).
   - `224-1019` with `none` acknowledge: `.error .outOfRange` → **emit EOI**.
   - Handler failure: `.error .erratum` → emit EOI (already AI2-A).
3. Update `interruptDispatchSequence_always_ok` to
   `interruptDispatchSequence_always_eoi_unless_spurious`.
4. Rust HAL `gic.rs` tracks this distinction (see AK5-F).

### AK3-D: ASID Generation Bump on Reuse (A-H03 / HIGH)

**Problem:** `AsidManager.lean:99-103`. Free-list reuse sets
`requiresFlush := true` but `generation` is untouched. Downstream stale-entry
tracking via generation is broken.

**Steps:**

1. On free-list reuse, bump `generation := generation + 1` (alongside
   `requiresFlush := true`).
2. Update `asid_reuse_bumps_generation` correctness lemma.
3. Propagate to Rust HAL: `tlb::tlbi_asid` invocation now keyed off
   generation+ASID tuple (AK5-F).

### AK3-E: `decodeVSpaceMapArgs` PA Bounds (A-M01 / MEDIUM)

**Problem:** `SyscallArgDecode.lean:201-225`. `paddr := PAddr.ofNat r2.val`
with no `< 2^physicalAddressWidth` check.

**Steps:**

1. Add `maxPA := 2^physicalAddressWidth` parameter to
   `decodeVSpaceMapArgs` (match AH3-C precedent for `maxASID`).
2. `if r2.val ≥ maxPA then .error .invalidArgument`.
3. Caller in `API.lean` passes `st.machine.physicalAddressWidth`.
4. Update `decodeVSpaceMapArgs_error_iff` theorem.

### AK3-F: `validateIpcBufferAddress` End-PA Check (A-M02 / MEDIUM)

**Problem:** `IpcBufferValidation.lean:74-82`. Only starting PA is checked.
A 512-byte buffer at `[2^width−512, 2^width)` passes start check but extends
outside PA window at offsets > 0.

**Steps:**

1. Strengthen to `paddr.toNat + ipcBufferAlignment ≤ 2^physicalAddressWidth`.
2. `AJ4-C` (already landed) added PA start check; this extends to end.
3. Update `validateIpcBufferAddress_implies_mapped_writable` postcondition
   — no regression expected.

### AK3-G: Cache Model D-Cache→I-Cache Ordering (A-M04 / MEDIUM — PARTIAL+DOC)

**Problem:** `CacheModel.lean:294-296`. `pageTableUpdate_icache_coherent`
uses `icInvalidateAll` only; required DSB between DC CIVAC and IC IALLU is
not modeled. `dcZeroByVA` creates dirty lines without mandatory clean.

**Decomposed steps (partial closure — full closure in WS-V):**

1. Add `BarrierKind.dsb_ish`/`BarrierKind.isb` variants to `CacheModel.lean`.
2. Define `cacheCoherentForExecutable` predicate requiring DC CIVAC → DSB
   → IC IALLU → DSB → ISB sequence.
3. Prove `pageTableUpdate_icache_coherent_under_sequence` requiring the
   barrier sequence as a hypothesis.
4. Full typeclass-level `BarrierKind` composition deferred to WS-V.

### AK3-H: Timer `countsPerTick` Positivity (A-M05 / MEDIUM)

**Problem:** `TimerModel.lean:55-65`. `HardwareTimerConfig` permits
`countsPerTick = 0` (if DT freq × interval < 10⁹).

**Steps:**

1. Add `countsPerTickPositive : countsPerTick > 0` field to
   `HardwareTimerConfig`.
2. Wire `configTimeSlicePositive`-style boot guard in `Boot.lean`.
3. Prove `rpi5TimerConfig_countsPerTickPositive` (already `54000` > 0).

### AK3-I: `tlbBarrierComplete` Substantive Binding (A-M06 / MEDIUM — DEFER+DOC)

**Problem:** `TlbModel.lean:398-407`. Every `*_barrier_complete` theorem
trivially `True`.

**Plan:**

1. Add `tlb.lastBarrierCompleted : Bool` field to machine state.
2. Rust HAL `tlb::dsb_ish` toggles the shadow via FFI.
3. Substantive proofs that toggle is tied to actual barrier emission.

**Disposition:** DEFER to WS-V (requires FFI round-trip). Document at
`TlbModel.lean` as TPI-DOC-AK3I.

### AK3-J: `decodeSchedContextConfigureArgs` Validation (A-M07 / MEDIUM)

**Problem:** `SyscallArgDecode.lean:958-966`. Raw `r4.val` assigned to
`domain` with no `< 16` check; priority/budget/period unconstrained.

**Steps:**

1. Add validation mirroring `decodeSetPriorityArgs`:
   - `r2.val ≤ 255` (priority fits in `Priority`)
   - `r4.val < 16` (domain fits in numDomains)
   - `r0.val > 0` (budget — also closes SC-H01 part)
   - `r1.val > 0` (period)
2. Return `.error .invalidArgument` on violation.
3. Update `decodeSchedContextConfigureArgs_error_iff` theorem.
4. **Coordinate with AK4-B** — Rust-side validation divergence.

### AK3-K: MMU/Device-Memory Ordering (A-M08, A-M09 / MEDIUM — DEFER+DOC)

**Problem:** `VSpaceARMv8.lean:95-103; PageTable.lean:349-359`.
`simulationRelation` assumes hardware walker sees same memory as
`pageTableMemory`, which is false without `dsb ishst` after descriptor
writes. `ensureTable` zero-page without cache clean.

**Plan (partial closure):**

1. Define `BarrierKind.ishst`/`dcCleanInvalidate` tokens.
2. Strengthen `ARMv8VSpace.mapPage` postcondition to require the barrier
   token appears in a composed sequence.
3. Full state-machine binding to Rust HAL is DEFER to WS-V.

**Disposition:** DEFER-WITH-ROADMAP. Document in `VSpaceARMv8.lean`.

### AK3-L: `endOfInterrupt` Audit Trail (A-M10 / MEDIUM)

**Problem:** `InterruptDispatch.lean:81-82`. `endOfInterrupt` is identity;
no way to detect missing EOI at proof layer.

**Steps:**

1. Add `eoiPending : HashSet InterruptId` field to `MachineState` (or
   `SystemState.scheduler` — prefer machine to match architectural model).
2. `acknowledgeInterrupt` inserts; `endOfInterrupt` removes.
3. Prove `kernelExit_eoiPending_empty : kernel_exit_invariant →
   st.machine.eoiPending.isEmpty`.

### AK3-M: LOW-tier Architecture Batch (A-L1..A-L9)

- A-L1 `exceptionLevelFromSpsr` EL2/EL3 collapse — document as RPi5-
  specific (EL2 present but not entered by kernel code).
- A-L2 `memoryMap.find?` first-match — add `noOverlappingRegions`
  invariant and strengthen classifier.
- A-L3 hardcoded MAIR indices — extract to named constants
  (`MemoryAttribute.deviceNGnRnE_idx` etc.).
- A-L4 `acknowledgeInterrupt` silent truncation — already handled by
  AK3-C.
- A-L5 `decodeCapPtr.isWord64Dec` proof-level invariant — document at
  type level, no runtime change needed.
- A-L6 timer 64-bit wrap — document at 54 MHz wrap horizon ~10¹⁰ years,
  not material.
- A-L7 `contextSwitchState` no TLB/ASID touch — tracked as DEFER to WS-V
  (context switch hardware maintenance).
- A-L8 `BumpAllocator` off-by-one — audit and fix if actual off-by-one
  exists.
- A-L9 `validateIpcBufferAddress` page-granularity — document the
  4 KiB granule assumption.

---

## 7. Phase AK4: ABI Bridge — Decode, Types, Validation

**Priority:** CRITICAL — R-ABI-C01 renders two syscalls non-functional
against the production kernel. Required before any Rust userspace can
exercise `sched_context_configure` or `service_register`.
**Audit findings addressed:** R-ABI-C01, R-ABI-H01, R-ABI-H02,
R-ABI-M01..M04, R-ABI-L1..L8.
**Primary files:** `SeLe4n/Machine.lean`, `Architecture/RegisterDecode.lean`,
`Architecture/SyscallArgDecode.lean`, `rust/sele4n-types/src/identifiers.rs`,
`rust/sele4n-abi/src/args/service.rs`, `rust/sele4n-abi/src/args/
sched_context.rs`, `rust/sele4n-abi/src/args/cspace.rs`,
`rust/sele4n-abi/src/args/vspace.rs`, `rust/sele4n-abi/src/ipc_buffer.rs`,
`rust/sele4n-sys/src/service.rs`, `rust/sele4n-sys/src/sched_context.rs`.
**Gate:** `lake build` + `cargo test --workspace` + **new** end-to-end
encode/decode integration test (see AK4-G).

### AK4-A: IPC-Buffer Merge into `msgRegs` (R-ABI-C01 / CRITICAL)

**Problem:** `arm64DefaultLayout.msgRegs := #[⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]` (4 entries);
`decodeServiceRegisterArgs` and `decodeSchedContextConfigureArgs` both call
`requireMsgReg decoded.msgRegs 4` (requires ≥5 entries). Rust wrappers
encode MR[4] into IPC buffer. No merge step in `decodeSyscallArgs`.

**Remediation choice — three options:**

| Option | Pros | Cons |
|--------|------|------|
| A: Merge IPC-buffer overflow into `msgRegs` during decode | Minimal Rust change; matches seL4 convention | Requires decode to consult `ipcBuffer`; new frame lemmas |
| B: Shrink both syscalls to ≤4 args | Simpler decode; no IPC-buffer dependency | Semantic change to ABI; Rust wrappers need redesign |
| C: Extend `arm64DefaultLayout.msgRegs` to include x6/x7 | Works for up to 6 args | x7 is syscallNumReg (`:849`) — collision; x6 would need Rust ABI change |

**Decision:** Option A (IPC-buffer merge). Rationale:
- seL4 convention: message registers >4 live in IPC buffer.
- Minimal surface-area change to Rust wrappers (already correct).
- Aligns with `MessageInfo.length` semantics (length > inline regs → consult
  buffer).

**Decomposed steps:**

1. **Extend `SyscallDecodeResult`:** change `msgRegs : Array UInt64` to
   include both inline regs and IPC-buffer merged values.
2. **Extend `decodeSyscallArgs` in `RegisterDecode.lean:109-125`:** after
   reading inline regs from `layout.msgRegs`, if
   `msgInfo.length > layout.msgRegs.size`, read additional regs from the
   receiver TCB's IPC buffer (`tcb.ipcBufferPtr → ipcBuffer.mrs`) at
   positions `layout.msgRegs.size .. msgInfo.length - 1`.
3. **Add `ipcBufferRead` helper:** resolves thread's IPC buffer via
   `getIpcBufferForThread` (exists) and reads `mrs[idx]`.
4. **Handle missing IPC buffer:** if `msgInfo.length > 4` and no IPC
   buffer mapped, return `.error .invalidMessageInfo` (matches seL4).
5. **Round-trip theorems:**
   - `decodeServiceRegisterArgs_succeeds_on_5arg_encoded` — new theorem
     asserting 5-arg encoded message decodes correctly.
   - Update `decodeServiceRegisterArgs_error_iff` — now errors iff
     `msgInfo.length < 5` OR IPC-buffer inaccessible.
   - Same for `decodeSchedContextConfigureArgs`.
6. **Preservation:** `decodeSyscallArgs_preserves_state` — unchanged
   (decode remains read-only).

**Risk:** `decodeSyscallArgs` becoming stateful-read (IPC buffer lookup)
affects NI projection. Audit: `decodeSyscallArgs` is invoked in
`syscallEntryChecked` (see `API.lean`); the IPC buffer belongs to the
calling thread (same domain) — no cross-domain read. Add
`decodeSyscallArgs_reads_only_caller_ipcBuffer` lemma.

### AK4-B: Lean/Rust Validation Alignment — `service_register` (R-ABI-H02 / HIGH)

**Problem:** `decodeServiceRegisterArgs` (`SyscallArgDecode.lean:775-786`)
accepts any `u64` for `methodCount`, `maxMessageSize`, `maxResponseSize`,
and treats `requiresGrant := r4.val != 0` (any-nonzero). Rust-side
`sele4n-abi/src/args/service.rs:48-71` rejects non-bool (r4 ∈ {0, 1}) and
rejects overflows.

**Remediation:** Authoritative direction = Lean (kernel is the trusted
validator). Tighten Lean to match Rust.

**Steps:**

1. Reject `r4.val ≥ 2` with `.error .invalidMessageInfo`.
2. Add upper bounds: `methodCount ≤ 2^16`, `maxMessageSize ≤ 2^16`,
   `maxResponseSize ≤ 2^16` (matching Rust).
3. Update `decodeServiceRegisterArgs_error_iff` theorem.
4. Add round-trip assertion test in `tests/DecodingSuite.lean`.

### AK4-C: Typed `SchedContextId` in Rust (R-ABI-H01 / HIGH)

**Problem:** `rust/sele4n-types/src/identifiers.rs` lacks `SchedContextId`
newtype. Lean has `SchedContextId` with `.sentinel` and `ofObjIdChecked`
(AF-22). Rust uses raw `u64`.

**Steps:**

1. Add `#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)] pub struct
   SchedContextId(pub(crate) u64);` mirroring `ThreadId`/`ObjId` pattern.
2. Add `SchedContextId::SENTINEL` constant (matching Lean
   `SchedContextId.sentinel`).
3. Add `SchedContextId::new(u64)` constructor rejecting sentinel value
   if used in argument position.
4. Refactor `SchedContextBindArgs.thread_id` / `sched_context.rs:bind`
   signatures to use typed `SchedContextId` where appropriate (argument
   types already use `ThreadId` — extend to SC ID).
5. Update all Rust call sites; add compile-time `assert_eq!(size_of::<
   SchedContextId>(), 8)`.
6. Update `sele4n-types/src/lib.rs:6` docstring from "14 newtype
   identifiers" → "15" (also closes R-ABI-L2).

### AK4-D: Lean/Rust Validation — `SchedContextConfigureArgs` (R-ABI-M01 / MEDIUM)

**Problem:** Rust validates `priority ≤ 255`, `domain ≤ 15`; Lean accepts
any `u64`.

**Steps:** Already addressed by AK3-J (Lean-side tightening). Additionally,
verify Rust constants match Lean: `MAX_PRIORITY = 255`, `MAX_DOMAIN = 15`
(already 15 after WS-AG2 R-05 fix). No further Rust action.

### AK4-E: Lean/Rust Validation — `CSpaceMintArgs` / PagePerms (R-ABI-M02, M03 / MEDIUM)

**Problem:** Rust rejects `rights > 0x1F`; Lean silently masks via
`AccessRightSet.ofNat`. Same for `PagePerms`/`VSpaceMapArgs`.

**Steps:**

1. Lean `decodeCSpaceMintArgs`: `if r3.val > 0x1F then .error
   .invalidArgument`.
2. Lean `decodeVSpaceMapArgs`: `if r4.val > 0x1F then .error
   .invalidArgument` (for page perms).
3. Update corresponding `_error_iff` theorems.
4. `AccessRightSet.ofNat` and `PagePermissions.ofNat` remain as
   defensive fallbacks for in-kernel use, but decode is now fail-closed.

### AK4-F: `IpcBuffer::set_mr` Symmetry (R-ABI-M04 / MEDIUM)

**Problem:** `ipc_buffer.rs:82-92`. `set_mr(0..3)` returns `Ok(false)`
while `get_mr(0..3)` returns `Err`. Asymmetric.

**Steps:**

1. Rename `set_mr` to `set_mr_overflow` (document: writes to IPC-buffer
   overflow slot for indices ≥ inline reg count).
2. Add a new `set_mr(idx, val)` that returns `Result<(), SetMrError>`
   where `SetMrError::InlineIndex` is returned for idx ∈ 0..3 (matching
   `get_mr` asymmetry).
3. Update call sites in `service.rs`, `sched_context.rs` to use
   `set_mr_overflow` explicitly.

### AK4-G: End-to-End ABI Integration Test (NEW)

**Rationale:** The audit's §9.6 notes "Gap: No end-to-end test encoding via
`sele4n-sys` wrappers and decoding via the Lean kernel — would have caught
R-ABI-C01 immediately."

**Steps:**

1. Create new test file `tests/AbiRoundtripSuite.lean` — Lean-only test
   that simulates Rust encoding (by writing `msgRegs` + IPC buffer in the
   same byte layout the Rust ABI produces) and verifies Lean decode
   succeeds for all 25 syscall variants.
2. For each syscall, construct the expected input from the Rust struct
   layout (via `sele4n-types` constants kept in a `tests/fixtures/
   abi_layout.json` synchronized manually).
3. Verify decode produces the expected typed struct.
4. Add a CI gate: `scripts/test_abi_roundtrip.sh` runs the new suite.
5. **Coverage target:** all 25 syscalls, each with a minimal valid
   invocation and a boundary-case invalid invocation (e.g., out-of-range
   priority).

**Acceptance criteria:**
- All 25 syscalls decode successfully from Rust-encoded byte layout.
- Boundary-case invalid inputs produce the expected error kind.
- Test added to `test_full.sh`.

### AK4-H: LOW-tier ABI Batch (R-ABI-L1..L8)

- R-ABI-L1 `lifecycle.rs:14` docstring missing `6=SchedContext` — add.
- R-ABI-L2 `sele4n-types/src/lib.rs:6` count 14→15 — addressed in AK4-C.
- R-ABI-L3 `RegisterFile` exported but unused — mark `#[cfg(test)]` or
  remove.
- R-ABI-L4 `ServiceQueryArgs` empty struct — mark `#[cfg(test)]` or
  wire into a new syscall if planned.
- R-ABI-L5 `trap.rs:49 lateout("x6")` redundant — remove.
- R-ABI-L6 constants duplicated across 3 crates — extract to
  `sele4n-types::constants` module.
- R-ABI-L7 `ThreadId::SENTINEL` vs `CPtr::NULL` naming — standardize
  on `::SENTINEL` convention; add deprecation shim for `NULL`.
- R-ABI-L8 `Hash` derive on typed IDs — documented as AJ2-D; cross-ref
  comment.

---

## 8. Phase AK5: Rust HAL Boot Hardening

**Priority:** Pre-silicon blockers — R-HAL-H02/H03 break MMU correctness
at first boot; R-HAL-H05 causes GIC lockup on any handler panic.
**Audit findings addressed:** R-HAL-H01..H05, R-HAL-M01..M12, R-HAL-L1..L16.
**Primary files:** `rust/Cargo.toml`, `rust/sele4n-hal/src/mmu.rs`,
`boot.rs`, `boot.S`, `trap.rs`, `trap.S`, `gic.rs`, `uart.rs`, `timer.rs`,
`interrupts.rs`, `cache.rs`, `cpu.rs`, `mmio.rs`, `ffi.rs`, `vectors.S`.
**Gate:** `cargo test --workspace` (367+ tests) + `cargo clippy
--workspace` (0 warnings) + boot-sequence validation via
`scripts/test_qemu.sh`.

### AK5-A: Workspace `panic = "abort"` (R-HAL-M01, R-HAL-M11 / MEDIUM — PREREQ)

**Problem:** No `[profile.*]` sections in `rust/Cargo.toml`. Default Rust
profile uses `panic = "unwind"`, which is UB in `no_std` and produces UB
across `extern "C"` boundaries.

**Steps:**

1. Add to `rust/Cargo.toml`:
   ```toml
   [profile.dev]
   panic = "abort"

   [profile.release]
   panic = "abort"

   [profile.test]
   panic = "abort"
   ```
2. Verify compile: `cargo build --workspace`.
3. Update `docs/spec/SELE4N_SPEC.md` §6.5 to document panic discipline.

**This is a prerequisite** for AK5-B (R-HAL-H05 EOI guard) and AK5-K
(FFI `catch_unwind` is unnecessary once abort is workspace-default, but
document the discipline).

### AK5-B: IRQ Handler EOI-Always (R-HAL-H05 / HIGH)

**Problem:** `trap.rs:220-233` + `gic.rs:305`. `dispatch_irq` sends EOI
only after handler returns. Panic in handler skips EOI → GIC deadlock.

**Steps (depends on AK5-A):**

1. Restructure `dispatch_irq` with a scope-exit guard: capture the INTID
   immediately after acknowledge; call `end_of_interrupt(intid)`
   unconditionally via a `Drop`-bound guard before any handler invocation.
2. With `panic = "abort"` (AK5-A), the guard runs on normal return path.
   The panic path aborts the whole kernel (acceptable — this is a
   fatal invariant violation), logging via `kprintln!` first.
3. Verify via unit test: simulate handler panic with `#[should_panic]`
   under `panic = "unwind"` test profile; verify EOI was sent before
   abort propagation.

**Alternative (if `Drop` is unsuitable under abort):** inline the EOI at
every handler return path via explicit compiler_fence + explicit call.
Less elegant; use only if the `Drop`-guard approach has issues.

### AK5-C: SCTLR_EL1 WXN + SA + EOS (R-HAL-H03 / HIGH)

**Problem:** `mmu.rs:175-177`. Only M/C/I are OR'd. WXN=0 means HW does
not enforce W^X; SA/EOS are reset-dependent.

**Steps:**

1. Compute full SCTLR_EL1 bitmap:
   - `M = 1` (MMU enable)
   - `C = 1` (D-cache enable)
   - `I = 1` (I-cache enable)
   - `WXN = 1` (writable regions are never executable — **HW W^X**)
   - `SA = 1` (SP alignment check, EL1)
   - `SA0 = 1` (SP alignment check, EL0)
   - `EOS = 1` (exception exit serialization)
   - `EIS = 1` (exception entry serialization)
   - Reserved-1 bits per ARM-ARM: bits 4, 7, 11, 22, 23, 28, 29 must be 1.
2. Write the full mask instead of OR-accumulating, to avoid inheriting
   garbage in undefined bits.
3. Update `enable_mmu` SAFETY comment enumerating each bit's rationale.
4. Add unit test: verify computed mask against expected constant.

**Defense-in-depth:** Combined with AK3-B (Lean/backend W^X), this gives
four-layer W^X enforcement (wrapper, backend, descriptor encode, HW SCTLR).

### AK5-D: MMU Enable TLB+Cache Maintenance (R-HAL-H02 / HIGH)

**Problem:** `mmu.rs:162-181`. `enable_mmu` writes TTBR then DSB ISH + ISB
+ SCTLR without (a) `tlbi vmalle1` to invalidate stale translations, (b)
D-cache clean of page-table pages.

**Steps:**

1. Before TTBR write, invoke:
   ```rust
   cache::clean_range(&raw const BOOT_L1_TABLE as usize,
                      core::mem::size_of::<BootL1Table>());
   cache::dsb_ish();
   tlb::tlbi_vmalle1();
   cache::dsb_ish();
   cache::isb();
   ```
2. Verify ordering per ARMv8-A D8.11.
3. Update `enable_mmu` SAFETY comment enumerating the pre-conditions.
4. Add QEMU-level boot test to verify clean boot.

### AK5-E: `BOOT_L1_TABLE` Safe Sync (R-HAL-H01, R-HAL-M03 / HIGH + MEDIUM)

**Problem:** `mmu.rs:110`. `BOOT_L1_TABLE` is `static mut` (deprecated-
in-future-editions, technically unsound). `mmu.rs:165` TTBR conversion
uses `&raw const` cast without BAADDR mask.

**Steps:**

1. Wrap in `PageTableCell(UnsafeCell<BootL1Table>); unsafe impl Sync for
   PageTableCell {}` mirroring AJ5-B `UartInner`/`UartLock` pattern.
2. Provide `BOOT_L1_TABLE.with_inner_mut(|table| ...)` accessor with
   interrupts-disabled precondition.
3. TTBR conversion: compute PA with explicit `& 0xFFFF_FFFF_FFFE` mask
   (clear low bit which is TnSZ/CnP). Add boot-time assert:
   `assert!(pt_pa != 0 && pt_pa < 1 << physical_addr_width)`.
4. Add `debug_assert!(pt_pa & 0xFFF == 0)` — L1 table must be 4KiB-aligned.
5. Remove the unused `.bss.page_tables` link-section if still unused
   after this refactor.

### AK5-F: TrapFrame ESR/FAR Save (R-HAL-H04 / HIGH)

**Problem:** `trap.S:154-157, 162-166` + `trap.rs`. `TrapFrame` saves
272 bytes (GPRs + ELR/SPSR/SP_EL0) but does NOT save ESR_EL1 or FAR_EL1.
CLAUDE.md scope list contradicts actual implementation.

**Decision:** Add ESR_EL1 and FAR_EL1 to TrapFrame (mirror CLAUDE.md
documentation). Extend TrapFrame to 288 bytes (16 B added: 8 B ESR + 8 B
FAR, 16-byte aligned).

**Steps:**

1. In `trap.rs`, extend `TrapFrame` struct:
   ```rust
   #[repr(C)]
   pub struct TrapFrame {
       pub gprs: [u64; 31],
       pub sp_el0: u64,
       pub elr_el1: u64,
       pub spsr_el1: u64,
       pub esr_el1: u64,    // NEW
       pub far_el1: u64,    // NEW
   }
   ```
2. Update `TRAP_FRAME_SIZE = 288`.
3. Update `const _: () = assert!(TRAP_FRAME_SIZE == 288)`.
4. In `trap.S:save_context`, add:
   ```asm
   mrs x0, esr_el1
   str x0, [sp, #272]
   mrs x0, far_el1
   str x0, [sp, #280]
   ```
   Adjust stack-decrement and restore logic.
5. Update `handle_synchronous_exception` to read `frame.esr_el1` /
   `frame.far_el1` instead of live `mrs`.
6. Update size assertion tests.

### AK5-G: GIC Uses Crate MMIO (R-HAL-M04 / MEDIUM)

**Problem:** `gic.rs:102-133` defines local `mmio_read32`/`mmio_write32`
shadowing `crate::mmio::*` with AJ5-A alignment asserts.

**Steps:**

1. Remove local MMIO functions from `gic.rs`.
2. Route all GIC register accesses through `crate::mmio::mmio_read32` /
   `crate::mmio::mmio_write32`.
3. Verify no performance regression (MMIO is uncached, cost is domain
   of hardware).

### AK5-H: UART Uses Crate MMIO (R-HAL-M05 / MEDIUM)

**Problem:** `uart.rs:66-82`. Bypasses alignment asserts.

**Steps:**

1. Route PL011 register accesses through `crate::mmio::*`.
2. Verify with boot-banner test.

### AK5-I: Multi-Cluster MPIDR Mask (R-HAL-M02, R-HAL-M09 / MEDIUM)

**Problem:** `boot.S:22-25` (Aff0 only) and `cpu.rs:79-89`
(`current_core_id` Aff0 only). On multi-cluster BCM2712, core (Aff1=1,
Aff0=0) passes the boot check.

**Steps:**

1. Change boot.S affinity check to mask `mpidr & 0xFF00FF` (Aff1:Aff0).
2. `current_core_id` similarly.
3. Document the BCM2712 topology (2 clusters × 4 cores).

### AK5-J: `init_timer` CNTFRQ Validation (R-HAL-M07 / MEDIUM)

**Problem:** `timer.rs:158-160`. Silently falls back when CNTFRQ_EL0 == 0.

**Steps:**

1. Add `TimerError::CntfrqNotProgrammed` variant.
2. Return error on zero-CNTFRQ; caller aborts boot with log.
3. Verify on QEMU (CNTFRQ_EL0 is set by firmware).

### AK5-K: Miscellaneous HAL Fixes (R-HAL-M06, M08, M10, M12 / MEDIUM)

- R-HAL-M06 Spectre v1 — add CSDB doc note at `dispatch_irq` future
  table-lookup point.
- R-HAL-M08 `cache_range` empty-range — either drop early return or
  add DSB ISH at the empty path.
- R-HAL-M10 `init_with_baud(0)` — `assert!(baud > 0)`.
- R-HAL-M12 `handle_serror` signature `-> !` — replace `-> ()` with
  `-> !`, verify trap.S calling convention expects never-return.

### AK5-L: `init_timer` TimerError Cascade (AJ5-C follow-up)

Already in AJ5-C but verify `init_timer` return-type is `Result<(),
TimerError>` end-to-end after AK5-J. No new change if AJ5-C stands.

### AK5-M: FFI Panic Discipline Documentation (R-HAL-M11 / MEDIUM)

**Status after AK5-A:** With workspace `panic = "abort"`, a panic in FFI
aborts the kernel via `halt()`. This is the correct behavior for seLe4n
(panics indicate invariant violation — safer to abort than unwind).

**Steps:**

1. Document at each FFI function that panic → abort under workspace
   config (AK5-A).
2. Add compile-time check in `ffi.rs`:
   ```rust
   #[cfg(not(panic = "abort"))]
   compile_error!("seLe4n HAL requires panic = \"abort\" — see AK5-A");
   ```

### AK5-N: LOW-tier HAL Batch (R-HAL-L1..L16)

Batch-handle per audit §8.1: signature fixes, comment accuracy, const
fns, SMP readiness flags, redundant DAIF bits, spinlock backoff tuning,
`dc_zva` options, hard-coded GIC base configuration extraction, secondary
core wake-storm risk documentation, SP0 vector stub (document as
unreachable).

---

## 9. Phase AK6: Information Flow + SchedContext Correctness

**Priority:** Release-grade NI requires closure; SC-H01 zero-budget hole
breaks schedContext well-formedness invariant.
**Audit findings addressed:** NI-H01, NI-H02, NI-M01, NI-M02, SC-H01,
SC-M01..SC-M04, NI-L1..L4, SC-L1..SC-L3.
**Primary files:** `InformationFlow/Invariant/Composition.lean`,
`InformationFlow/Projection.lean`, `InformationFlow/Policy.lean`,
`InformationFlow/Invariant/Operations.lean`,
`SchedContext/Operations.lean`, `SchedContext/Budget.lean`,
`SchedContext/Invariant/Preservation.lean`, `SchedContext/Invariant/Defs.lean`,
`SchedContext/ReplenishQueue.lean`, `API.lean`.
**Gate:** `lake build` + `test_full.sh` + NI proof regression
(`tests/InformationFlowSuite.lean`).

### AK6-A: Zero-Budget Rejection (SC-H01 / HIGH)

**Problem:** `SchedContext/Operations.lean:51-57, 90-114`.
`validateSchedContextParams` checks `period > 0` and `budget ≤ period` but
does NOT enforce `budget > 0`. When `budget = 0`, `schedContextConfigure`
stores `replenishments := [{amount := ⟨0⟩, ...}]`, violating
`replenishmentListWellFormed` (`Invariant/Defs.lean:54-56`: `∀ r,
r.amount.val > 0`).

**Steps:**

1. Add `if budget = 0 then .error .invalidArgument` to
   `validateSchedContextParams`.
2. Add `if period = 0 then .error .invalidArgument` (already present
   per audit — verify).
3. Update `validateSchedContextParams_succeeds_iff` theorem.
4. Coordinate with AK3-J / AK4-D (Lean decode validation alignment).

### AK6-B: `schedContextConfigure` End-to-End Preservation (SC-M01 / MEDIUM)

**Problem:** `Invariant/Preservation.lean:60-82`. `applyConfigureParams`
leaves `replenishments` untouched; the real `schedContextConfigure`
REPLACES with `[{amount := ⟨budget⟩, eligibleAt := st.machine.timer}]`.
End-to-end preservation of `schedContextWellFormed` is never proven for
the concrete transition.

**Steps:**

1. Refactor `applyConfigureParams` to include the replenishments
   replacement, matching the concrete op.
2. Prove `schedContextConfigure_preserves_schedContextWellFormed`
   directly against the real post-state.
3. Prove `schedContextConfigure_replenishments_correct :
     schedContextConfigure args st = .ok st' →
     st'.objects.get? scId = some (.schedContext sc') →
     sc'.replenishments = [{amount := ⟨args.budget⟩, eligibleAt := ...}]`.

### AK6-C: `eligibleAt` Window Correction (SC-M02 / MEDIUM)

**Problem:** `Operations.lean:109`. `eligibleAt := st.machine.timer`
means reconfigured SC gets `budgetRemaining := budget` PLUS immediately-
eligible replenishment of size `budget` — double-budget.

**Steps:**

1. Change `eligibleAt := st.machine.timer` to
   `eligibleAt := st.machine.timer + period.val`.
2. Update `schedContextConfigure_replenishments_correct` theorem.
3. Update CBS bandwidth accounting proof — tighter by `budget/period`.

### AK6-D: `schedContextYieldTo` Self-Yield Guard (SC-M03 / MEDIUM)

**Problem:** `Operations.lean:261-290`. `yieldTo st id id` zeros source
then writes target; HashMap ordering decides the final state.

**Steps:**

1. Early return with `.error .invalidArgument` when
   `fromScId == targetScId`.
2. Update `schedContextYieldTo_self_rejected` theorem.

### AK6-E: `niStepCoverage` Operational Witness (NI-H01 / HIGH)

**Problem:** `InformationFlow/Invariant/Composition.lean:884-900`.
Coverage witnesses an NI step for each `KernelOperation` via
`syscallDecodeError rfl` — discoverability only, not semantic coverage.

**Remediation choice:**

**Option A (rename):** Rename to
`niStepDiscoverability_by_syscallDecodeError` and clarify in docstring
that this theorem only establishes NI-step constructor coverage, not
per-op semantic preservation (which is in `step_preserves_projection`).
Minimal code change.

**Option B (semantic mapping):** Replace the witness with an operational
mapping that for each `KernelOperation` selects a real `NIStep`
constructor (`syscallSuspend`, `syscallResume`, etc.) and asserts the
op is covered by that constructor's semantics.

**Decision:** Start with option A (rename + clarify docstring). Option B
requires ~400 lines of new proof (one per `KernelOperation` constructor)
and adds little over the per-op `*_preserves_projection` proofs
(NI-H02). Track as follow-up if external reviewers flag the rename
as insufficient.

**Steps (option A):**

1. Rename `niStepCoverage` → `niStepConstructorCoverage` in
   `Composition.lean`.
2. Update docstring to state: "For every `KernelOperation k`, there
   exists an `NIStep` constructor that witnesses it. This is coverage
   in the discoverability sense; semantic preservation is proven
   per-op in `Invariant/Operations.lean`."
3. Update call sites (grep `niStepCoverage`).
4. Update audit errata note.

### AK6-F: `syscallDispatchHigh` Composed Projection (NI-H02 / HIGH)

**Problem:** `Composition.lean:295-299` + `API.lean:1886-1898`. The
`hProj` caller hypothesis is required for `dispatchCapabilityOnly` arms;
no internal composition theorem discharges it.

**Steps:**

1. In `Operations.lean`, compose
   `dispatchCapabilityOnly_preserves_projection :
     ∀ domain, apiInvariantBundle st → dispatchCapabilityOnly args st = .ok st' →
     projectKernelState domain st' = projectKernelState domain st`
   by case-splitting on `args` and invoking the 11 individual
   `*_preserves_projection` theorems (suspend, resume, setPriority,
   setMCPriority, setIPCBuffer, schedContextConfigure, schedContextBind,
   schedContextUnbind, vspaceMapPage, vspaceUnmapPage, revokeService).
2. Wire into `syscallDispatchHigh` — remove `hProj` hypothesis, invoke
   the composition theorem internally.
3. Update API bridge `syscallEntry_success_yields_NI_step` accordingly.

### AK6-G: Projection Strips `pendingMessage` + `timedOut` (NI-M01 / MEDIUM)

**Problem:** `InformationFlow/Projection.lean:185-228` + `Model/Object/
Types.lean:570`. Both fields survive projection — open covert channel
across cross-domain IPC/timeout.

**Steps:**

1. In `projectKernelObject`, `.tcb` arm, after AJ2-B strips `pipBoost`,
   add:
   ```
   pendingMessage := none
   timedOut := false
   ```
2. Re-prove `projectKernelObject_erases_cross_domain_ipc` and add
   `projectKernelObject_erases_timeout_signal`.
3. Update 35+ NI preservation proofs via re-invocation of
   `projectKernelObject` simp lemma (mostly automatic).

### AK6-H: Default Labeling Strength (NI-M02 / MEDIUM)

**Problem:** `Policy.lean:220-226` + `Composition.lean:740-751`. The
`publicLabel`-everything default satisfies `LabelingContextValid`.
`isInsecureDefaultContext` multi-probe (`[0,1,42]`) can be evaded by
overriding just those.

**Steps:**

1. Strengthen `LabelingContextValid` to require: "at least two distinct
   labels are assigned to actual objects in the initial state".
2. Prove `defaultLabelingContext_fails_validity_with_nontrivial_state`.
3. Update `syscallEntryChecked` guard to reject at boot if the labeling
   is trivial.
4. Document in SELE4N_SPEC.md §7 as a deployment requirement.

### AK6-I: CBS Tight Bandwidth Bound (SC-M04 / MEDIUM)

**Problem:** `SchedContext/Invariant/Defs.lean:78-100`.
`cbs_bandwidth_bounded` proves `totalConsumed ≤ 8 × budget`; tight
bound is `budget × ⌈window / period⌉`.

**Steps (partial closure):**

1. Prove the tight bound `cbs_bandwidth_bounded_tight :
     totalConsumed st window ≤ budget × ⌈window / period⌉`
   using `cbs_single_period_bound` (already proven) and induction on
   window/period.
2. Keep `cbs_bandwidth_bounded` as a corollary (8× loose bound for
   bounded window sizes).
3. Document admission caveat in SELE4N_SPEC.md §5.4.

### AK6-J: LOW-tier NI + SC Batch

- NI-L1 `endpointReplyChecked` flow check assumes target==caller —
  add invariant-backed lemma.
- NI-L2 `endpointReplyRecvChecked` non-atomicity comment — document in
  API.lean.
- NI-L3 four accepted U6-K covert channels — add production warning
  banner in `docs/spec/SELE4N_SPEC.md` §7.8.
- NI-L4 `cspaceMint_NI` doesn't hypothesize on badge — add badge
  hypothesis.
- SC-L1 `processReplenishments` lump-sum cap discards over-cap refills
  — document as deliberate.
- SC-L2 `ReplenishQueue.insert` no idempotence — add idempotence via
  duplicate-scId rejection.
- SC-L3 `getCurrentPriority` silent fallback invariant dependency —
  cross-ref AE3 fix.

---

## 10. Phase AK7: Foundational Model (Prelude/Machine/Model)

**Priority:** Structural — weak frozen invariants (F-H01, F-H02) propagate
into every downstream proof; fixing them tightens release-grade claims.
**Audit findings addressed:** F-H01, F-H02, F-M01..F-M11, F-L1..F-L15.
**Primary files:** `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`,
`Model/Object/Types.lean`, `Model/Object/Structures.lean`,
`Model/State.lean`, `Model/FrozenState.lean`, `Model/FreezeProofs.lean`,
`Model/IntermediateState.lean`, `Model/Builder.lean`.
**Gate:** `lake build` + per-module build + `test_full.sh` + zero sorry.

### AK7-A: `freezeMap` Capacity Witness (F-H01 / HIGH)

**Problem:** `FrozenState.lean:294-299, 363-369`. `freezeMap` seeds
`indexMap` with a 16-capacity `RHTable`. Returned `FrozenMap` carries no
`invExtK` witness. For `maxObjects = 65536`, relies on undocumented
auto-grow invariant transfer.

**Steps:**

1. Add `FrozenMap.indexMapCapacity : Nat` field; default to
   `max 16 (data.size + 1)`.
2. Prove `freezeMap_indexMap_invExtK :
     freezeMap input = fm → fm.indexMap.invExtK`.
3. Prove `freezeMap_capacity_sufficient :
     freezeMap input = fm → fm.indexMap.capacity ≥ fm.data.size`.
4. Update `FrozenSystemState` derivation to propagate capacity witnesses.

### AK7-B: `apiInvariantBundle_frozenDirect` Extended Coverage (F-H02 / HIGH)

**Problem:** `FreezeProofs.lean:1103-1106`. Only `objects.get?` agreement
is required; scheduler, machine, TLB, services, IRQs, CDT, lifecycle
metadata are unconstrained. Non-`objects` mutations vacuously preserve
the predicate.

**Steps:**

1. Rename to `apiInvariantBundle_frozenDirectObjectsOnly` to clarify
   observational scope.
2. Add `apiInvariantBundle_frozenDirectFull` with field-agreement
   conjuncts for scheduler, machine, TLB, services (via
   `FrozenSystemState` field-by-field equality).
3. Update existing call sites to use the appropriate variant:
   `frozenDirectObjectsOnly` where only object identity matters,
   `frozenDirectFull` where broader agreement is required.
4. Audit `docs/CLAIM_EVIDENCE_INDEX.md` for the stronger claim.

### AK7-C: `Memory` Bounds-Checked Access (F-M01 / MEDIUM)

**Problem:** `Machine.lean:144`. `readMem`/`writeMem` total on
`PAddr → UInt8`, never consult `memoryMap`/`physicalAddressWidth`.
Out-of-range accesses silently succeed.

**Steps:**

1. Route all `readMem`/`writeMem` through
   `RuntimeBoundaryContract.memoryAccessAllowed` pre-check.
2. On disallowed, return `.error .invalidMemoryAccess`.
3. For in-kernel code paths, verify preconditions hold via invariants.
4. Update `MachineState` preservation theorems.

### AK7-D: `MessageInfo.mk` Private (F-M02 / MEDIUM)

**Problem:** `Types.lean:1178`. `MessageInfo.mk` bypasses `maxLabel`
check.

**Steps:**

1. Mark `MessageInfo.mk` as `private`.
2. Add `MessageInfo.mkChecked : label : Nat → length : Nat → capsUnwrapped :
   Nat → Option MessageInfo` with saturation checks.
3. Expose `MessageInfo.mkChecked` as the public constructor.
4. Update construction sites; cascade through `IpcMessage.mk` (F-L13).

### AK7-E: Typed ID `Inhabited` Review (F-M03, F-M04 / MEDIUM)

**Problem:** `Prelude.lean:60-497`. `Inhabited ⟨0⟩` on all typed IDs
(ObjId/ThreadId/SchedContextId/CPtr/Slot/Badge) silently produces sentinel
on `default`. `ThreadId ⟨5⟩.toObjId = SchedContextId ⟨5⟩.toObjId` —
wrapper aliasing.

**Decomposed decision (two options):**

**Option A (drop `Inhabited`):** Remove `Inhabited` instance from typed
IDs requiring caller-supplied values everywhere. Pro: eliminates silent
sentinel. Con: Lean's `default` expansion is used in dozens of places
including fixture building, test state construction. Cascade is large.

**Option B (sentinel-witness subtype):** Replace `Inhabited ⟨0⟩` with
`Inhabited` producing a typed `.sentinel`, and add `ValidObjId ObjId :=
{ o : ObjId // o ≠ .sentinel }` subtype. Operations that require a valid
ID take `ValidObjId`, those that tolerate sentinels take `ObjId`.

**Decision:** Option B — more work but preserves ergonomics. Scope:
Phase AK7 introduces the subtype; downstream migration tracked as
AK7-E.cascade (incremental, not blocking v1.0).

**Steps (AK7 baseline):**

1. Add `ValidObjId`, `ValidThreadId`, etc. subtypes with sentinel
   exclusion witness.
2. Provide `ObjId.toValid : (o : ObjId) → o ≠ .sentinel → ValidObjId`.
3. Add `ObjId.validOfInvariant : apiInvariantBundle st →
   st.objects.get? o = some _ → ValidObjId` — proves validity from
   kernel invariant.
4. Migrate ≤10 highest-risk entry points (kernel syscall handlers) to
   take `ValidObjId` (e.g., `suspendThread`, `resumeThread`).
5. Incremental migration tracked in AK7-E.cascade for v1.1.

### AK7-F: Phantom-Tag `ObjId` Across Wrappers (F-M04 / MEDIUM — continues AK7-E)

**Problem (restated for emphasis):** `ThreadId ⟨5⟩.toObjId =
SchedContextId ⟨5⟩.toObjId`. Disjointness relies on pattern-match
discipline.

**Remediation path (phased):**

1. **Phase AK7 baseline:** Add `ObjKind` discriminator to `ObjId`:
   ```lean
   structure ObjId where
     val : Nat
     kind : ObjectKind  -- NEW
   ```
   With default `kind := .unknown` for legacy compatibility.
2. **`ThreadId.toObjId`** returns `ObjId { val, kind := .thread }`.
3. **`SchedContextId.toObjId`** returns `ObjId { val, kind := .schedContext }`.
4. **Prove** `thread_schedContext_disjoint :
     (ThreadId.ofNat n).toObjId ≠ (SchedContextId.ofNat n).toObjId`.
5. Migration to discriminated lookups in `objects.get?` tracked as
   AK7-F.cascade for v1.1.

**Baseline risk:** Adding a field to `ObjId` affects ≥300 proofs. If the
cascade is too invasive, defer to v1.1 and document as a known gap.
Decision criterion: if AK7-E/F combined migrate cleanly (≤300 lines of
downstream proof fixes), land both; otherwise land AK7-E baseline only
and defer AK7-F to a follow-up.

### AK7-G: Non-Lawful BEq Narrow-Scope (F-M05 / MEDIUM)

**Problem:** `Machine.lean:278-281; Types.lean:581`. Non-lawful
`BEq RegisterFile`/`BEq TCB` publicly exported; downstream `LawfulBEq`
search is silently unsound outside GPR 0-31.

**Steps:**

1. Rename `instBEqRegisterFile` → `instBEqRegisterFileUnsafe`, mark
   `@[deprecated "Test-only; use RegisterFile.ext for proofs"]`.
2. Add `RegisterFile.ext : (∀ i, rf1.get i = rf2.get i) ↔ rf1 = rf2`
   as the sanctioned extensionality lemma.
3. Same for `instBEqTCB`.
4. Update `tests/*` call sites.

### AK7-H: `FrozenMap` Well-Formedness (F-M06 / MEDIUM)

**Problem:** `FrozenState.lean:76`. `FrozenSystemState` drops `FrozenMap`
invariant proofs. `indexMap` entries can be out-of-bounds of `data.size`.

**Steps:**

1. Add `wellFormed : ∀ k idx, indexMap.get? k = some idx → idx <
   data.size` field to `FrozenMap`.
2. Propagate to `FrozenSystemState`.
3. Prove preservation by `freezeMap` construction.

### AK7-I: Capability Null Predicate (F-M07 / MEDIUM)

**Problem:** `Types.lean:110`. `Capability` has no `isNull` invariant
guard; default aliases `seL4_CapNull` by convention only.

**Steps:**

1. Define `Capability.isNull : Capability → Bool := fun c => c.objId =
   ObjId.sentinel && c.rights = AccessRightSet.empty`.
2. Add `isNotNull` precondition at capability-using entry points
   (`cspaceInvoke`, `cspaceMint`, `cspaceCopy`).
3. Document at `Capability.default` as sentinel-null convention.

### AK7-J: Structural Invariant Predicates (F-M08..F-M11 / MEDIUM)

- F-M08 `PagePermissions.ofNat` mask semantics — route through
  `ofNat?` at call sites OR document masked-to-5-bits.
- F-M09 `ensureCdtNodeForSlot` unbounded counter — gate by
  `cdtNextNode.val < maxCdtDepth` invariant.
- F-M10 `noVirtualOverlap_trivial` tautology — redefine to
  `∀ v₁ v₂, lookup v₁ = some(p,_) → lookup v₂ = some(p,_) → v₁ = v₂`.
- F-M11 `TlbEntry` ASID generation — mirror `AsidManager.generation`
  in each TlbEntry (ties into AK3-D).

### AK7-K: LOW-tier Foundational Batch (F-L1..F-L15)

- F-L1 predicate naming inconsistency — standardize on
  `*Invariant` suffix.
- F-L2 Badge truncation cross-ref — add seL4 badge-64-bit comment.
- F-L3 TCB permissive MCP default — document as root-task default.
- F-L4 boot interrupt-enable window — document Phase 3 enable in
  `Boot.lean`.
- F-L5 one-sided permission round-trip — add reverse round-trip lemma.
- F-L6 TCB Queue recovery coverage — add per-state recovery lemma.
- F-L7 depth-1 descendantsOf fuel — cross-ref AE2/AF-22.
- F-L8 bool-valued CDT predicates — promote to Prop variants.
- F-L9 17-deep tuple projection — DEFER to post-1.0 hygiene pass.
- F-L10 missing `DecidableEq KernelObject` — add derivation.
- F-L11 hardcoded register-index counterexample — remove dead test.
- F-L12 default zero `RegisterContext` — document as sentinel.
- F-L13 `IpcMessage.mk` non-private — addressed in AK7-D.
- F-L14 zero-offset allocate — add positive-size precondition.
- F-L15 `CdtNodeId`/`InterfaceId` no sentinel — add sentinel
  conventions (mirrors AJ2-D).

---

## 11. Phase AK8: Capability / Lifecycle / Service + Data Structures

**Priority:** Proof discipline and correctness on less-touched subsystems.
**Audit findings addressed:** C-M01..C-M07, C-L1..C-L10, DS-M01..DS-M04,
DS-L1..DS-L11.
**Primary files:** `Kernel/Capability/*`, `Kernel/Lifecycle/*`,
`Kernel/Service/*`, `Kernel/RobinHood/*`, `Kernel/RadixTree/*`,
`Kernel/FrozenOps/*` (test-only), `Kernel/CrossSubsystem.lean`.
**Gate:** `lake build` + `test_full.sh` + zero sorry.

### AK8-A: Cross-Untyped Disjointness (C-M01 / MEDIUM)

**Problem:** `Lifecycle/Operations.lean:667`. `ut.children.any` check
rejects child ID collisions only within the *same* untyped. Two untypeds
with overlapping `[regionBase, regionBase+regionSize)` can both allocate
at the same PA.

**Steps:**

1. Add `untypedRegionsDisjoint` invariant to `crossSubsystemInvariant`
   (as 11th conjunct):
   ```
   def untypedRegionsDisjoint (st : SystemState) : Prop :=
     ∀ ut1 ut2 ∈ st.untypedObjects, ut1.objId ≠ ut2.objId →
       ut1.regionBase + ut1.regionSize ≤ ut2.regionBase ∨
       ut2.regionBase + ut2.regionSize ≤ ut1.regionBase
   ```
2. Prove preservation by `retypeFromUntyped` and all capability ops.
3. Document that boot sequence must establish this invariant via
   `mmioRegionDisjointCheck`-style enforcement.

### AK8-B: Transactional Strict Revoke (C-M02 / MEDIUM)

**Problem:** `Operations.lean:1011-1012`. `cspaceRevokeCdtStrict` is not
transactional; retains partial state on first failure.

**Remediation choice:**

**Option A (rename to reflect semantics):** Rename
`cspaceRevokeCdtStrict` → `cspaceRevokeCdtBestEffort` to match actual
behavior. Cheap, correct, documented.

**Option B (add transactional wrapper):** New
`cspaceRevokeCdtTransactional` that computes the full delete plan,
verifies all preconditions, then atomically applies. Expensive (walk
+ validate + apply pattern).

**Decision:** Option A for baseline; option B post-1.0 if needed.

### AK8-C: `resolveCapAddress` Rights-Traversal Annotation (C-M03 / MEDIUM)

**Problem:** `Operations.lean:118-125`. Recurses without intermediate-
level rights check. Documented design choice; future cap-forwarding
ops could leak authority.

**Steps:**

1. Add explicit proof obligation as a comment block at
   `resolveCapAddress`: "Callers must enforce rights at the entry-level
   cap before invoking; intermediate-level rights are not re-checked."
2. Add `resolveCapAddress_caller_rights_obligation` documentation
   theorem stating the obligation formally.

### AK8-D: Priority Authority Bounds (C-M05 / MEDIUM)

**Problem:** `PriorityManagement.lean:50-53`. Unbounded `Nat` MCP
comparison. Root task with `maxControlledPriority = ∞` can escalate.

**Steps:**

1. Document at `validatePriorityAuthority` header comment: "Standard
   seL4 MCS semantics — root task with unbounded MCP can set arbitrary
   priority on any child. This is by design; see seL4 Manual §5.2."
2. Add `maxHardwarePriority := 255` constant; add
   `validatePriorityAuthority_bound : validatePriorityAuthority auth
   newPri = .ok _ → newPri.toNat ≤ maxHardwarePriority` theorem.

### AK8-E: `getCurrentPriority` Error Surface (C-M06 / MEDIUM)

**Problem:** `PriorityManagement.lean:68-75`. Silent fallback to
`tcb.priority` on missing SC. Documented "dead code under invariants"
but neither `setPriorityOp` nor `setMCPriorityOp` establish
`schedContextBindingConsistent` before call.

**Steps:**

1. Change return type to `Except KernelError Priority`.
2. `.error .schedContextNotFound` on missing SC lookup.
3. Callers absorb `Except` or pattern-match.
4. Already partially addressed by AE3-F; verify and extend if stale.

### AK8-F: `findFirstEmptySlot` Radix Bound (C-M07 / MEDIUM)

**Problem:** `Structures.lean:538-545`. Can exceed `2^radixWidth`.

**Steps:**

1. Cap `scanLimit := 2^radixWidth - base.toNat`.
2. Prove `findFirstEmptySlot_within_radix : findFirstEmptySlot cnode
   base = some s → s.toNat < 2^radixWidth`.
3. Update CNode capacity bounds theorem.

### AK8-G: FrozenOps Typing Disjointness (DS-M01 / MEDIUM — TEST-ONLY)

**Problem:** `FrozenOps/Core.lean:135-157`. `frozenStoreObject` uses
`FrozenMap.set` without variant-tag check.

**Status:** FrozenOps is TEST-ONLY, confirmed by audit §7.7
("FrozenOps confirmed NOT in production import chain"). DS-M01 is a
hardening fix for test surface, not production.

**Steps:**

1. Add `frozenStoreTcbChecked : ThreadId → TCB → FrozenSystemState →
   Option FrozenSystemState` that pre-checks via `frozenLookupTcb` and
   returns `none` on variant mismatch.
2. Migrate call sites in `Operations.lean:333..490` to the checked
   variant.
3. Document FrozenOps status in module docstring: "Test-only; not in
   production import chain. See audit §7.7."

### AK8-H: FrozenOps Transactional Unbind (DS-M02 / MEDIUM — TEST-ONLY)

**Problem:** `FrozenOps/Operations.lean:683-699`.
`frozenSchedContextUnbind` partial mutation on failed bound-thread
lookup.

**Steps:**

1. Hoist TCB lookup before SC mutation (two-phase validate-then-write).
2. Return `.error _` if TCB lookup fails, before any state change.
3. Already matches AE2-D pattern; extend here.

### AK8-I: RadixTree Checked Build (DS-M03 / MEDIUM)

**Problem:** `RadixTree/Core.lean:100-131` + `Bridge.lean:44-54`.
`extractBits slot.toNat 0 radixWidth = slot.toNat % (2^radixWidth)` —
distinct slots with identical low bits collide.
`buildCNodeRadix_lookup_equiv` requires `UniqueRadixIndices` +
`hNoPhantom` preconditions NOT enforced by public `buildCNodeRadix`.
`freezeCNodeSlots` uses the unchecked variant.

**Steps:**

1. Change `freezeCNodeSlots` to invoke `buildCNodeRadixChecked` (exists
   via U-29 / AE2-B) and return `Option CNodeRadix` with `none` on
   phantom key / radix collision.
2. Update `freezeCNodeSlots_correct` theorem to be conditional on
   `some` result.
3. Callers in `FreezeProofs.lean` pattern-match on the `Option`.

### AK8-J: RHTable `LawfulBEq` Gate (DS-M04 / MEDIUM)

**Problem:** `RobinHood/Bridge.lean:43-53`. `RHTable.BEq` not
`LawfulBEq`-proven; propagates non-lawful value BEq.

**Steps:**

1. Document in `Bridge.lean` header: "RHTable.BEq is not LawfulBEq
   unless [LawfulBEq β] is separately assumed."
2. Add `[LawfulBEq β]` typeclass gate on `instBEqRHTable` where the
   table is used in proof contexts.
3. Optional: provide `RHTable.lawfulBEq_of_lawfulBEqValue` as a
   structural proof when the value type is lawful.

### AK8-K: LOW-tier Capability + Lifecycle + Service + DS Batch

**Capability/Lifecycle/Service (C-L1..C-L10):**
- C-L1 `cspaceMove` self-move early-reject — add.
- C-L2 `cspaceMutate` occupied-slot guard — add.
- C-L3 `ipcTransferSingleCap` CDT edge without sender-rights record —
  document as WS-V scope.
- C-L4 `cleanupDonatedSchedContext` asymmetry — align bound vs donated
  cleanup.
- C-L5 IPC buffer canonical upper-bound — add.
- C-L6 `registerService` O(n) timing side-channel — document; post-1.0.
- C-L7 `lookupServiceByCap` RH-rehash stability — document.
- C-L8 `serviceCountBounded` boot-time exposure — add accessor.
- C-L9 abstract object sizes vs seL4 RPi5 — document in SPEC.
- C-L10 `cspaceDeleteSlotCore` dangling CDT edges — audit + fix.

**Data Structures (DS-L1..DS-L11):**
- DS-L1 `extractBits` public offset — mark non-public or document.
- DS-L2 `insertNoResize` fuel silent failure — return `Except`.
- DS-L3 `RHTable.erase` saturation — use `.pred` with boundary check.
- DS-L4 RH `Inhabited` 16-slot — document or make 0-slot default.
- DS-L5 400K-800K heartbeat proofs — DEFER to post-1.0 hygiene pass.
- DS-L6 `resolveExtraCaps` silent drop — already documented (AI6-A).
- DS-L7 wildcard unreachability 25-variant enumeration — accept as-is.
- DS-L8 `ofList` resizing — document.
- DS-L9 FrozenOps hardcoded priority/domain — extract constants.
- DS-L10 `typedIdDisjointness` trivial — coordinated with AK7-E/F.
- DS-L11 `RHTable.BEq` dual-fold — refactor if perf-sensitive.

---

## 12. Phase AK9: Platform, Boot, DTB, MMIO

**Priority:** Release-readability — P-H02 field-name inversion confuses
spec readers; P-H01 breaks hardware MMIO reads.
**Audit findings addressed:** P-H01, P-H02, P-M01..P-M07, P-L1..P-L13.
**Primary files:** `Platform/Boot.lean`, `Platform/DeviceTree.lean`,
`Platform/Sim/BootContract.lean`, `Platform/Sim/RuntimeContract.lean`,
`Platform/RPi5/BootContract.lean`, `Platform/RPi5/RuntimeContract.lean`,
`Platform/RPi5/MmioAdapter.lean`, `Platform/RPi5/ProofHooks.lean`,
`Testing/StateBuilder.lean`.
**Gate:** `lake build` + `test_smoke.sh` + fixture verification.

### AK9-A: MMIO Read Width-Specific with Alignment (P-H01 / HIGH)

**Problem:** `RPi5/MmioAdapter.lean:358`. Only 8-bit `mmioRead` exists;
no `mmioRead32`/`mmioRead64` with `isAligned` guards. GIC-400 / BCM2712
device registers require word-aligned word-sized reads.

**Steps:**

1. Add `mmioRead32 (addr : PAddr) : Option UInt32`:
   - `if !isAligned addr 4 then return .none`
   - `if !isDeviceAddress addr then return .none`
   - `if !isDeviceAddress (addr + 3) then return .none` (range check per
     P-M02 extension)
   - Read 4 bytes via HAL.
2. Add `mmioRead64 (addr : PAddr) : Option UInt64`:
   - Same pattern with 8-byte alignment and range.
3. Restrict 8-bit `mmioRead` to UART / debug contexts; rename to
   `mmioReadByte` and document as debug-only.
4. Add Lean typeclass instances if HAL adapter is parameterized.
5. Coordinate with Rust side (AK5-G/H already route through
   crate-level MMIO with alignment asserts).

### AK9-B: Rename `objectStoreNonEmpty` (P-H02 / HIGH)

**Problem:** `Sim/BootContract.lean:70` + `RPi5/BootContract.lean:57`.
`objectStoreNonEmpty := (default : SystemState).objects.size = 0` — field
asserts the OPPOSITE of its name.

**Decision:** Rename to `objectStoreEmptyAtBoot` and flip consumer usage
where required. Alternative (flip predicate, keep name) is semantically
equivalent but inverts boot semantics — more invasive.

**Steps:**

1. Rename field in both Sim and RPi5 `BootContract`:
   `objectStoreNonEmpty` → `objectStoreEmptyAtBoot`.
2. Keep definition the same (`= 0`).
3. Update consumers (grep) — any reader of the field gets the renamed
   accessor.
4. Update `BootBoundaryContract` substantiation proofs.
5. Update SELE4N_SPEC §6.4 (boot contract) to reflect the accurate name.

### AK9-C: IRQ Handler Existence in Boot (P-M01 / MEDIUM)

**Problem:** `Boot.lean:493-503`. `bootFromPlatformChecked` validates
`wellFormed` + `bootSafeObjectCheck` but not that each
`IrqEntry.handler` ObjId refers to a notification present in
`initialObjects`. `StateBuilder` check #5 covers runtime only.

**Steps:**

1. Extend `bootSafeObjectCheck` with per-IRQ handler validation:
   ```
   def irqHandlersReferenceNotifications (cfg : PlatformConfig) : Bool :=
     cfg.irqs.all (fun irq =>
       match cfg.initialObjects[irq.handler]? with
       | some (.notification _) => true
       | _ => false)
   ```
2. Prove `bootFromPlatformChecked_ok_implies_irqHandlersValid`.
3. Add fixture exercising a mis-configured IRQ and verify boot rejects.

### AK9-D: MMIO Multi-Byte Range Region-Local (P-M02 / MEDIUM)

**Problem:** `MmioAdapter.lean:406, 434, 508`. `isDeviceAddress addr &&
isDeviceAddress (addr+N)` validates endpoints individually; adjacent
device regions can be spliced at boundary.

**Steps:**

1. Extract `findMmioRegion (addr : PAddr) : Option MmioRegion`.
2. Require `findMmioRegion addr = some r ∧ addr + N ≤ r.endAddr` for
   each MMIO write (and for the new reads from AK9-A).
3. Update `mmioWrite_alignedAndBounded_within_region` theorem.
4. Currently unreachable on RPi5 layout — verify no regression.

### AK9-E: `registerContextStableCheck` Budget Fix (P-M03 / MEDIUM)

**Problem:** `RPi5/RuntimeContract.lean:78-84`. `budgetSufficientCheck`
returns `true` for `schedContextBinding = .bound scId` when store has
wrong variant or `none`.

**Steps:**

1. Change to return `false` for non-`schedContext`/`none` lookups when
   `schedContextBinding = .bound`.
2. Update `registerContextStableCheck_budget` proof (AG7-B) — need to
   re-verify budget-branch soundness.

### AK9-F: DTB + MachineConfig Validation (P-M04, P-M05, P-M07 / MEDIUM)

- P-M04 `classifyMemoryRegion` empty-map default — require non-empty
  map OR default to `.reserved` when platform map unavailable.
- P-M05 `applyMachineConfig` unchecked fields — validate
  `pageSize` power-of-two, `physicalAddressWidth ≤ 52`,
  machine-config `wellFormed` gate.
- P-M07 `findMemoryRegProperty` fuel = 1000 unvalidated — compute fuel
  from `hdr.sizeDtStruct / 4` and propagate `fuelExhausted` via
  `Except`.

### AK9-G: Interrupts Re-Enable Mirror (P-M06 / MEDIUM)

**Problem:** `Boot.lean:1049` + AJ3-E. Rust HAL AG5 re-enables at
Phase 3; Lean model stays disabled → Lean-vs-HAL state divergence.

**Steps:**

1. Add `bootEnableInterruptsOp : IntermediateState → IntermediateState`
   step mirroring HAL Phase 3.
2. Invoke at end of `bootFromPlatform` checked path.
3. Update `bootFromPlatform_interruptsEnabled` theorem.

### AK9-H: LOW-tier Platform Batch (P-L1..P-L13)

- P-L1 `StateBuilder.buildChecked` uses `panic!` — already mostly
  addressed by AE6-B; verify remaining call sites.
- P-L2 `readCString` fuel 256 silent truncation — return `Except`.
- P-L3 `physicalAddressWidth` unbounded — gate 1..52.
- P-L4 `extractPeripherals` 2-level silent skip — already documented
  (AF-32); cross-ref.
- P-L5 MMIO ops no interrupts-disabled guard — document requirement.
- P-L6 `buildValidated` unstructured strings — return structured
  `BuildValidationError`.
- P-L7 `mmioRegionDisjointCheck` RAM vs MMIO only — extend to MMIO vs
  MMIO disjointness.
- P-L8 O(n²) boot IRQ scan — document as boot-only cost.
- P-L9 VSpaceRoot boot exclusion — DEFER to WS-V.
- P-L10 `registerContextStableCheck` ignores pre-state — document or
  extend with pre-state check.
- P-L11 FFI `opaque BaseIO` contract bridging — DEFER to WS-V.
- P-L12 `mmioWrite` W1C region kind unchecked — add `MmioRegionKind`
  gate.
- P-L13 touching-regions fragility — document as known.

---

## 13. Phase AK10: Testing, Documentation & Closure

**Priority:** Portfolio closure — fixture re-verification, documentation
synchronization, version bump 0.29.0 → 1.0.0, final gate.
**Audit findings addressed:** Residual LOW findings not handled in
phase-local batches; audit errata; cross-cutting documentation.
**Primary files:** `README.md` (+ 10 i18n versions), `docs/spec/
SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, `docs/gitbook/*`,
`docs/CLAIM_EVIDENCE_INDEX.md`, `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md`,
`CLAUDE.md`, `tests/fixtures/main_trace_smoke.expected`,
`scripts/website_link_manifest.txt`, version-bearing files,
`docs/codebase_map.json`.
**Gate:** `test_full.sh` + `cargo test --workspace` +
`cargo clippy --workspace` + `check_version_sync.sh` + fixture byte-
identity + zero sorry.

### AK10-A: Fixture Verification

**Steps:**

1. Run `lake exe sele4n` and diff against `tests/fixtures/
   main_trace_smoke.expected`.
2. If the phases AK1-AK9 changed observable trace (expected for
   AK1-D `ipcState := .ready`, AK2-A priority re-enqueue, AK6-G
   projection strips — confirmed to surface in trace), update the
   fixture with rationale in `CHANGELOG.md`.
3. If fixture is unchanged, record as part of AK10-A evidence.
4. Expected fixture size change: ≤ ±5 lines.

### AK10-B: Documentation Synchronization

**Steps (per CLAUDE.md §Documentation rules):**

1. `README.md` metrics — re-sync from `docs/codebase_map.json` (run
   `scripts/sync_readme_from_codebase_map.sh` if present, else manual
   update).
2. All 10 i18n README variants — propagate version + metric updates.
3. `docs/spec/SELE4N_SPEC.md`:
   - §5 Scheduler — update WCRT documentation (AK2-K partial closure).
   - §5.4 CBS — document ceiling-round (AK2-E) and tight bound (AK6-I).
   - §6 Architecture — document W^X four-layer enforcement (AK3-B +
     AK5-C), ASID rollover correctness (AK3-A).
   - §7 Information Flow — document projection field-stripping (AK6-G)
     and deployment requirement for non-trivial labeling (AK6-H).
   - §8 ABI — document IPC-buffer merge (AK4-A).
4. `docs/DEVELOPMENT.md` — update build and test commands if changed.
5. `docs/gitbook/*` — sync affected chapters.
6. `docs/CLAIM_EVIDENCE_INDEX.md` — add AK1-AK9 claim rows.
7. `docs/WORKSTREAM_HISTORY.md` — add WS-AK entry with 10-phase
   breakdown.
8. `CHANGELOG.md` — add v1.0.0 release notes documenting all AK phases.
9. `CLAUDE.md` — update "Active workstream context" with WS-AK
   completion summary (most recent at top, prior 30 entries trimmed
   per established pattern).
10. `docs/codebase_map.json` — regenerate via tooling if Lean sources
    changed.

### AK10-C: Version Bump 0.29.0 → 1.0.0

**Steps:**

1. Update 15 version-bearing files per `scripts/check_version_sync.sh`
   manifest:
   - `lakefile.toml`
   - `rust/Cargo.toml` (workspace version)
   - `rust/Cargo.lock` (auto-regenerated)
   - `rust/sele4n-hal/src/boot.rs` (`KERNEL_VERSION`)
   - `CLAUDE.md` (version line)
   - `docs/spec/SELE4N_SPEC.md` (package version)
   - 10 i18n README version badges
2. Run `scripts/check_version_sync.sh` — must pass.
3. Bump annotations in `CHANGELOG.md` under "v1.0.0".

### AK10-D: Audit Errata

**Errata to record in `docs/audits/AUDIT_v0.29.0_ERRATA.md`:**

- **E-1 (S-H03 semantics):** Audit text claims re-enqueue uses
  `effectiveRunQueuePriority tcb` "rather than `resolveInsertPriority`";
  this is correct and the fix (AK2-A) uses `resolveInsertPriority`. No
  errata — verification was confused; audit finding stands.
- **E-2 (R-HAL-M12 scope):** Finding stands but scope is
  documentation/type-hygiene (no actual dead-`eret` reachable due to
  infinite `loop{wfe()}`). Record as informational clarification.
- **E-3 (A-H01 layering):** Finding scope extends to THREE layers
  (wrapper, ARMv8 backend, `fromPagePermissions`), not just the one
  cited in §7.5.
- **E-4 (R-HAL-H02 partial):** DSB ISH + ISB are present; missing
  pieces are `tlbi vmalle1` and D-cache clean of PT pages. Finding
  stands; scope clarified.
- **E-5 (NI-H02 structure):** Per-op `*_preserves_projection` theorems
  exist; what's missing is the composition
  `dispatchCapabilityOnly_preserves_projection` that discharges
  `hProj` internally. Finding stands.
- **E-6 (Finding count arithmetic):** Audit §2 summary states "68 MEDIUM
  / 108 LOW". Enumerating IDs in subsystem notes yields 76 MEDIUM
  (F: 11, S: 8, I: 7, C: 7, A: 10, NI: 2, SC: 4, DS: 4, P: 7, R-HAL: 12,
  R-ABI: 4) and 101 LOW (F: 15, S: 6, I: 6, C: 10, A: 9, NI: 4, SC: 3,
  DS: 11, P: 13, R-HAL: 16, R-ABI: 8). Correct totals: **2 CRITICAL + 23
  HIGH + 76 MEDIUM + 101 LOW = 202 findings**. The plan addresses every
  enumerated ID; summary discrepancy is informational.

### AK10-E: CLAUDE.md Large-File List Refresh

**Steps:**

1. Run `scripts/find_large_lean_files.sh` (or `find SeLe4n -name '*.lean'
   -exec wc -l {} \; | sort -rn | head -50`) to re-rank modules.
2. Phases AK2/AK6/AK7 are expected to add lines to
   `Scheduler/Operations/Preservation.lean`, `Liveness/WCRT.lean`,
   `InformationFlow/Invariant/Operations.lean`,
   `SchedContext/Invariant/Preservation.lean`, `FreezeProofs.lean`.
3. Update CLAUDE.md "Known large files" list accordingly.

### AK10-F: Residual LOW-tier Batch

All LOW findings not handled in phase-local batches (~8 remaining after
AK1-AK9 per-phase LOW batches):

- Review any undocumented LOW across all subsystems.
- Collect into single commit "AK10-F: LOW-tier residuals".

### AK10-G: Website Link Manifest Audit

**Steps:**

1. Run `scripts/check_website_links.sh`.
2. Any renamed files from AK1-AK9 require manifest update and
   coordination with `hatter6822.github.io` website repo (per
   CLAUDE.md Website link protection rule).
3. Expected touches: `docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md` and
   this plan are already protected paths (convention — verify).

### AK10-H: Portfolio Summary Entry in WORKSTREAM_HISTORY.md

**Entry template:**

```
## WS-AK — Pre-1.0 Release Hardening (v0.29.1 → v1.0.0)

**Audit:** docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md
**Phases:** 10 (AK1-AK10), 84 sub-tasks, 201 findings addressed.

- AK1 (IPC Fail-Closed): I-H01, I-H02, I-M01..M07 + 6 LOW.
- AK2 (Scheduler/PIP/WCRT): S-H01..H04, S-M01..M08 + 6 LOW.
- AK3 (Architecture): A-C01, A-H01..H03, A-M01..M10 + 9 LOW.
- AK4 (ABI Bridge): R-ABI-C01, R-ABI-H01..H02, R-ABI-M01..M04 + 8 LOW.
- AK5 (Rust HAL): R-HAL-H01..H05, R-HAL-M01..M12 + 16 LOW.
- AK6 (InformationFlow/SC): NI-H01..H02, SC-H01, NI-M01..M02, SC-M01..M04 + 7 LOW.
- AK7 (Foundational): F-H01..H02, F-M01..M11 + 15 LOW.
- AK8 (Cap/Lifecycle/DS): C-M01..M07, DS-M01..M04 + 21 LOW.
- AK9 (Platform): P-H01..H02, P-M01..M07 + 13 LOW.
- AK10 (Closure): fixture, docs, version bump, errata, residual LOW.

Gate: test_full.sh + cargo test --workspace + cargo clippy --workspace +
check_version_sync.sh + zero sorry/axiom.

Portfolio status: COMPLETE. v1.0.0 released.
```

### AK10-I: v1.0.0 Release Tag

**Note:** Release tagging itself is not performed by this workstream —
that is a manual maintainer action. This plan ends at commit of the
AK10 closure; the release tag is applied separately.

### AK10-J: DEFER-to-WS-V Tracking

Formalize the DEFER-TO-WS-V findings from §2.5 as WS-V scope items in
`docs/audits/AUDIT_v0.29.0_DEFERRED.md`:

- A-M04 TLB+cache composition full closure.
- A-M06 `tlbBarrierComplete` substantive binding.
- A-M08 + A-M09 MMU/Device-memory ordering BarrierKind composition.
- C-M04 `suspendThread` H3-ATOMICITY Rust-side proof.
- F-L9 17-deep tuple projection refactor (proof hygiene).
- P-L9 VSpaceRoot boot exclusion.
- R-HAL-L14 SVC `_syscall_id` FFI wiring.
- AK3-I `tlbBarrierComplete` substantive.
- AK3-K MMU/Device-memory BarrierKind composition (full).
- AK2-K.4 `eventuallyExits` hypothesis (by design).
- AK7-E.cascade and AK7-F.cascade (ObjKind + ValidObjId migration).

### AK10-K: Final Gate

**All of the following must pass before commit:**

```bash
./scripts/test_tier0_hygiene.sh       # incl. check_version_sync.sh
./scripts/test_full.sh                # tiers 0-3
cd rust && cargo test --workspace     # 370+ tests
cd rust && cargo clippy --workspace -- -D warnings
./scripts/check_website_links.sh
diff <(lake exe sele4n) tests/fixtures/main_trace_smoke.expected
grep -rn '\b\(sorry\|axiom\|native_decide\)\b' SeLe4n/    # zero matches
```

### AK10-L: Commit and Push

**Steps:**

1. Single commit on branch `claude/audit-workstream-planning-UoRya`
   (this workstream's designated branch) containing the plan document
   only.
2. Push with `git push -u origin claude/audit-workstream-planning-UoRya`.
3. No PR until maintainer approval.

---

## 14. Cross-Cutting Considerations

### 14.1 Dependency Graph Between Phases

```
AK1 (IPC) ─────────────────┐
AK2 (Scheduler) ───────────┼── AK6 (NI) preservation proofs
                            │
AK3 (Architecture) ─── AK5 (Rust HAL)  (Lean model shapes HAL obligations)
        │                   │
        │                   └── AK4 (ABI) — ABI/decode alignment
        │
AK7 (Foundational) — touched by proof cascades from AK1/AK2/AK6
AK8 (Capability/DS) — mostly independent
AK9 (Platform) — independent of AK1-AK8 except for P-M06 (interrupts enable mirror AJ3-E / AG5)
AK10 (Closure) — depends on all prior phases
```

**Safe commit order:** AK1 → AK2 → AK3 → AK4 → AK5 → AK6 → AK7 → AK8 →
AK9 → AK10. Within a phase, sub-tasks are mostly independent (sub-task
ordering in-phase optimizes proof-cascade minimization).

### 14.2 File Contention Matrix

A non-empty cell indicates two phases both touch a file. Goal: minimize
and serialize conflicts.

| File | AK1 | AK2 | AK3 | AK4 | AK5 | AK6 | AK7 | AK8 | AK9 | AK10 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|------|
| `Scheduler/Operations/Core.lean`       |     | ✓   |     |     |     |     |     |     |     |      |
| `Scheduler/Invariant.lean`             |     | ✓   |     |     |     |     |     |     |     |      |
| `Scheduler/Operations/Preservation.lean`| ✓ (AK1-C via IPC)| ✓ |     |     |     | ✓ (NI) |     |     |     |      |
| `IPC/DualQueue/Transport.lean`         | ✓   |     |     |     |     |     |     |     |     |      |
| `IPC/Operations/Endpoint.lean`         | ✓   |     |     |     |     | ✓ (NI) |     |     |     |      |
| `IPC/Invariant/*`                      | ✓   |     |     |     |     | ✓ (NI) |     |     |     |      |
| `Architecture/AsidManager.lean`        |     |     | ✓   |     |     |     |     |     |     |      |
| `Architecture/VSpaceARMv8.lean`        |     |     | ✓   |     |     |     |     |     |     |      |
| `Architecture/SyscallArgDecode.lean`   |     |     | ✓   | ✓ (AK4-B) |   |     |     |     |     |      |
| `SeLe4n/Machine.lean`                  |     |     |     | ✓   |     |     | ✓ (AK7-G, AK7-E) |     |     |      |
| `SeLe4n/Prelude.lean`                  |     |     |     |     |     |     | ✓   |     |     |      |
| `InformationFlow/Invariant/Operations.lean` | ✓ (projection) |     |     |     |     | ✓   |     |     |     |      |
| `Platform/Boot.lean`                   |     |     |     |     |     |     |     |     | ✓   |      |
| `Platform/RPi5/MmioAdapter.lean`       |     |     |     |     |     |     |     |     | ✓   |      |
| `API.lean`                             | ✓ (AK1-B call sites) | ✓ (AK2-K proofs) | ✓ (AK3-E caller) | ✓ (AK4-A decode) |     | ✓ (AK6-F) |     |     |     |      |
| `rust/Cargo.toml`                      |     |     |     |     | ✓   |     |     |     |     | ✓ (version) |
| `rust/sele4n-hal/src/mmu.rs`           |     |     |     |     | ✓   |     |     |     |     |      |
| `rust/sele4n-hal/src/trap.S / .rs`     |     |     |     |     | ✓   |     |     |     |     |      |
| `rust/sele4n-hal/src/gic.rs`           |     |     |     |     | ✓   |     |     |     |     |      |
| `rust/sele4n-types/src/identifiers.rs` |     |     |     | ✓   |     |     |     |     |     |      |

**Contention mitigation:** Phase order (AK1→AK10) serializes API.lean
touches. AK3 touches `SyscallArgDecode.lean` for decode validation; AK4
re-touches it for R-ABI-C01 IPC-buffer merge — handled sequentially
(AK4 comes after AK3, absorbs AK3 decode signature changes as
preconditions).

### 14.3 Proof-Cascade Magnitude Estimates

| Phase | Estimated net LOC delta | Estimated proof files touched |
|-------|--------------------------|-------------------------------|
| AK1 | +400 / −100 (error propagation cascades) | ~14 |
| AK2 | +1500 / −50 (WCRT closure proofs; AK2-K ~1200 if full) | ~20 |
| AK3 | +800 / −100 | ~18 |
| AK4 | +300 / −50 | ~6 Lean + ~8 Rust |
| AK5 | +600 / −100 Rust | ~14 Rust files |
| AK6 | +500 / −80 | ~10 |
| AK7 | +900 / −200 (ObjKind migration baseline) | ~15 |
| AK8 | +400 / −50 | ~8 |
| AK9 | +300 / −40 | ~9 |
| AK10 | +200 / −50 (docs) | docs + fixtures |
| **Total** | **~+5900 / −820** | **~90 files** |

### 14.4 Risk Register

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| AK2-K proof closure exceeds budget | HIGH | MEDIUM | Split into AK2-K baseline + AK2.5 follow-up; keep `eventuallyExits` external |
| AK4-A IPC-buffer merge introduces NI leak | LOW | HIGH | `decodeSyscallArgs_reads_only_caller_ipcBuffer` lemma; NI regression test |
| AK3-A ASID `activeSet` adds O(n) lookup cost | MEDIUM | LOW | Use HashSet, not List; hardware-side limit 65536 keeps bound tight |
| AK5-D MMU pre-enable maintenance breaks existing boot | LOW | HIGH | QEMU validation + Rust unit tests for `enable_mmu` ordering |
| AK7-F `ObjKind` migration cascades > 300 proofs | HIGH | MEDIUM | Stage as AK7-F baseline + AK7-F.cascade; land with `.unknown` default |
| AK9-B `objectStoreNonEmpty` rename hits GitBook | LOW | LOW | Website-link manifest check covers |
| AK6-F `dispatchCapabilityOnly_preserves_projection` composition chains to per-op proof gaps | MEDIUM | MEDIUM | Audit each of the 11 per-op proofs first; land composition only when each is machine-checked clean |

### 14.5 Rollback Plan Per Phase

Each phase ends in a clean commit with gate-passing state. Rollback is
`git revert <phase-commit>`. Exception: AK3 (ASID changes) interact
with AK5 HAL ASID path; if AK5-F TLBI-by-ASID issues emerge, rollback
both AK3-A and AK5-F together.

Version numbers track per-phase: AK1 lands at v0.29.1, AK2 at v0.29.2,
..., AK9 at v0.29.9, AK10 at v1.0.0. Each phase independently version-
bumped to enable partial rollback without breaking downstream.

### 14.6 Test Coverage Additions

**New test files introduced by WS-AK:**

1. `tests/AbiRoundtripSuite.lean` (AK4-G) — 25 syscalls × 2 boundary
   cases = 50 tests.
2. `tests/AsidPoolSuite.lean` (AK3-A) — active-set correctness +
   rollover scenarios (~20 tests).
3. `tests/NiProjectionSuite.lean` extension (AK6-G) — field-stripping
   round-trip (~10 tests).
4. `tests/WcrtSuite.lean` extension (AK2-K) — derived
   `hBandProgress`/`hDomainActiveRunnable` tests.
5. `tests/McmuHardeningSuite.lean` (AK3-B) — W^X four-layer tests.

Total expected test count delta: +120 Lean tests, +30 Rust tests.

### 14.7 Documentation Ownership Rules

Per CLAUDE.md Documentation rules, canonical root docs take priority
over GitBook. This workstream updates:

- **Canonical (root docs):**
  `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`,
  `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/WORKSTREAM_HISTORY.md`,
  `CHANGELOG.md`, `CLAUDE.md`.
- **Mirror (GitBook) — updated to match canonical:**
  `docs/gitbook/12-proof-and-invariant-map.md` (per-op proof anchors),
  `docs/gitbook/05-scheduler.md` (WCRT closure),
  `docs/gitbook/06-architecture.md` (W^X, ASID),
  `docs/gitbook/07-information-flow.md` (projection changes),
  `docs/gitbook/08-abi.md` (IPC-buffer merge).

---

## 15. Acceptance Criteria Summary

**A phase is considered complete when ALL of the following hold:**

1. Every audit ID mapped to that phase is either FIXED, DOCUMENTED, or
   explicitly DEFER-ed with roadmap entry in
   `docs/audits/AUDIT_v0.29.0_DEFERRED.md`.
2. `lake build` (default target) succeeds with 0 warnings.
3. For every modified Lean module M: `lake build M` succeeds. This is
   enforced by the pre-commit hook per CLAUDE.md Module build
   verification rule — DO NOT bypass with `--no-verify`.
4. `test_smoke.sh` passes. For phases touching invariants/theorems
   (AK2, AK6, AK7), `test_full.sh` also passes.
5. Zero `sorry` / `axiom` / `native_decide` in production proof
   surface (`grep -rn '\b\(sorry\|axiom\|native_decide\)\b' SeLe4n/`
   returns only comments).
6. For Rust-touching phases (AK4, AK5): `cargo test --workspace`
   passes; `cargo clippy --workspace -- -D warnings` passes.
7. Every new or modified theorem has a proof (no `sorry`).
8. Fixture verification: `lake exe sele4n` matches
   `tests/fixtures/main_trace_smoke.expected` byte-for-byte. If the
   fixture is updated intentionally, rationale recorded in
   CHANGELOG.md.
9. Documentation ownership: every finding that requires a
   DOCUMENT disposition has the corresponding doc text landed in the
   same commit.

**The workstream is complete when:**

- All 10 phases (AK1-AK10) are complete per above.
- `scripts/check_version_sync.sh` passes (version = 1.0.0).
- `scripts/check_website_links.sh` passes.
- The plan's §16 Checklist is fully ticked.
- Maintainer review and sign-off recorded.

---

## 16. Pre-Merge Checklist

Before landing the final commit:

- [ ] Audit verification §2 is accurate to the final code state
- [ ] All CRITICAL findings (A-C01, R-ABI-C01) are FIXED, not DOCUMENTED
- [ ] All HIGH findings have an explicit disposition (FIX / DEFER+DOC)
- [ ] `tests/fixtures/main_trace_smoke.expected` matches `lake exe sele4n`
- [ ] `scripts/test_tier0_hygiene.sh` passes
- [ ] `scripts/test_full.sh` passes
- [ ] `cargo test --workspace` passes in `rust/`
- [ ] `cargo clippy --workspace -- -D warnings` passes in `rust/`
- [ ] `scripts/check_version_sync.sh` — version = 1.0.0
- [ ] `scripts/check_website_links.sh` — manifest consistent
- [ ] Zero `sorry` / `axiom` / `native_decide` in `SeLe4n/`
- [ ] `docs/codebase_map.json` regenerated
- [ ] CHANGELOG.md v1.0.0 entry complete
- [ ] WORKSTREAM_HISTORY.md WS-AK entry complete
- [ ] CLAUDE.md active workstream context updated
- [ ] SELE4N_SPEC.md sections §5, §5.4, §6, §7, §8 updated
- [ ] All 10 i18n READMEs version-bumped
- [ ] `docs/audits/AUDIT_v0.29.0_ERRATA.md` created
- [ ] `docs/audits/AUDIT_v0.29.0_DEFERRED.md` created
- [ ] All AK10-B documentation synced (GitBook mirrors + canonical)

---

## 17. Out-of-Scope

The following are explicitly NOT part of WS-AK:

1. **Hardware-binding integration (WS-V / AG10):** First-silicon bring-up
   on RPi5 is a separate workstream consuming the outputs of AK3/AK5.
   AK3-I, AK3-K, AK9-F VSpaceRoot boot exclusion, C-M04 atomicity bridge,
   and R-HAL-L14 SVC FFI are deferred there.
2. **Full `ObjKind` migration (AK7-F.cascade):** Baseline in AK7-F;
   cascade through ~300 proof sites scheduled for v1.1.
3. **Full `ValidObjId` rollout (AK7-E.cascade):** Baseline in AK7-E;
   cascade for v1.1.
4. **Proof-hygiene pass (17-deep tuples, 400K-800K heartbeats):** Tracked
   as post-1.0 clean-up workstream WS-AL (proposed).
5. **New features:** No new kernel functionality introduced; WS-AK is
   strictly remediation.
6. **SMP readiness:** SMP-related LOW findings (R-HAL-L12, R-HAL-L15)
   are deferred to WS-SMP (separate proposed workstream).

---

## 18. Rationale for Phase Structure

The 10-phase structure was chosen for four reasons:

1. **Subsystem affinity** — each phase touches a coherent subsystem,
   minimizing cross-phase proof cascade cost. Running AK2 (Scheduler)
   and AK6 (NI) sequentially rather than interleaved reduces the
   interaction surface from ~O(n²) to ~O(n).

2. **Severity-weighted ordering** — phases addressing CRITICAL findings
   (AK3, AK4) land first-half; HIGH findings next; MEDIUM/LOW batches
   in later phases. This means a partial landing of WS-AK (if scope
   contracts under resource pressure) still addresses the top risks.

3. **Proof cascade containment** — AK7 (Foundational) is scheduled
   deliberately late despite touching foundational types. The rationale:
   AK1/AK2/AK6 all update downstream proofs anyway, so shifting types
   in AK7 before them would require double-updating. Scheduling AK7
   after lets it update types and cascade proofs in one pass.

4. **Rust / Lean interleaving** — AK3 (Lean architecture) precedes AK5
   (Rust HAL) because Lean model decisions (ASID rollover semantics,
   EOI differentiation, W^X layering) shape Rust HAL obligations. AK4
   (ABI) sits between — its decode changes in Lean (AK3-J) and its
   Rust tightening (AK4-B/D/E) need both sides aligned.

---

## 19. Notes on Proof-Engineering Approach

Several AK tasks require large preservation-theorem updates. The
established patterns in this codebase (AJ1-A, AI4-A, AH2-A, AE3-A)
provide templates:

1. **Signature-change pattern** (`Except` threading): AK1-A, AK2-C,
   AK8-E follow the AI4-A pattern — signature change, cascading caller
   updates, conditional postconditions, unreachable-branch discharging.
2. **Invariant-addition pattern**: AK1-B (16th conjunct already landed
   in AJ1-B), AK6-A (budget>0), AK8-A (untypedRegionsDisjoint) follow
   the AI2-C / AJ1-B pattern — add predicate to the bundle, cascade to
   every `_preserves_*` theorem via default-proof, compose in boot.
3. **Operational-semantic pattern**: AK2-A (priority re-enqueue),
   AK6-G (projection strips) require semantic changes. Pattern: prove
   correctness lemma bridging old and new behavior under invariants,
   then re-derive preservation theorems.
4. **Composition-theorem pattern**: AK6-F
   (`dispatchCapabilityOnly_preserves_projection`) follows the AE1-H
   pattern — enumerate cases, invoke per-case existing proofs.

**Avoid:**

- `native_decide` — replace with `decide` or explicit enumerative proof.
- Vacuous universal quantifiers (tautology predicates).
- Preservation theorems without postconditions (empty goals).
- Large-scale refactors beyond what the finding demands (CLAUDE.md §
  Tone and style).

---

*End of plan.*

