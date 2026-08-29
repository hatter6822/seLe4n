# WS-RR — SMP Release Readiness (pre-SM10 remediation)

> **Status**: PLANNED — no sub-task started.
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Source register**: [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) (171 confirmed findings)
> **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10) — opens when this phase closes
> **Audited cut**: `v0.34.3`
> **Target releases**: v0.35.0 → v0.99.x (SM10 then cuts v1.0.0)
> **Sub-task count**: 126 across 9 phases (RR0..RR8)

## 1. Phase goal

WS-RR closes everything the pre-SM10 completeness audit found open, so that
SM10 can be the release-closure phase it was scoped as rather than a phase
that discovers its own prerequisites are unmet.

The audit's verdict was that the project is **not** ready to begin SM10: three
findings block starting it, SM10's own scope statement is wrong, and a set of
fail-open latents become reachable exactly when the boot path goes live. None
of that is a "the proofs are missing" problem — SM0..SM9 are substantively
real — so this phase is remediation and completion, not new architecture.

**Concrete deliverables**:

1. Every open workstream carries a durable registry entry with a closure
   target, so no phase can close over work nobody is tracking (RR0).
2. The four live SMP dispatch arms carry `ipcInvariantFull` bundles, and
   cross-core SchedContext donation migrates the CBS replenish queue (RR1).
3. Full seL4-style fault IPC with reply-based restart, so a faulting thread
   can never livelock its core (RR2).
4. `ipcInvariantFull` is end-to-end machine-checked: no bundle carries a
   post-state conjunct as a hypothesis, and the top-level dispatch payoff
   theorems exist (RR3).
5. The boot path fails closed: a production labeling context is required, the
   readiness gate covers every seam, idle threads are installed, and the
   kernel entries a linked image needs are production-reachable (RR4).
6. The verified lock primitives match their deployed Rust counterparts —
   refinement against the real locks, not transliterations (RR5).
7. aarch64 code is compiled somewhere, so the 67 cfg-gated blocks and 59
   `asm!` sites SM10.E depends on are not first exercised at image-build
   time (RR6).
8. The medium-severity findings are closed (RR7) and the phase hands SM10 a
   green, registered, accurate starting state (RR8).

## 2. Scope and sequencing

### 2.1 What this phase covers, and what it hands to SM10

The audit produced 171 confirmed findings. They are divided by **who is best
placed to close them**, not by severity alone:

| Finding class | Count | Owner | Rationale |
|---------------|-------|-------|-----------|
| Blockers | 3 | RR0, RR1 | SM10 cannot correctly start over them |
| Security / soundness | 11 | RR2, RR4, RR5, RR7 | Become reachable when the boot path goes live |
| High (other) | 12 | RR1..RR6 | Real incomplete work in phases marked complete |
| Medium | 46 | RR7 (and RR0..RR6 where thematic) | Genuine gaps SM10 would otherwise absorb |
| Low (documentation drift) | 99 | **SM10.A** | Documentation sync is literally SM10.A's assigned job |

The 99 low findings are deliberately **not** duplicated into this phase.
Re-homing a documentation sweep into a remediation phase, and then running
SM10.A's documentation sweep over the same files, is two passes for one
outcome. RR0.H instead hands SM10.A the register section as its work-list.

### 2.2 Why a separate phase rather than SM10 sub-tasks

SM10's acceptance gate is a release checklist: spec rewritten, chapters
published, version bumped, tag cut. Adding a fault-IPC implementation and an
invariant de-threading closure to that gate would make "is the release ready"
and "is the kernel finished" the same question, which is exactly the
conflation that let the tier-4 gates certify phases nothing had run. Keeping
them separate means SM10 can be judged on whether the release is
well-formed, and WS-RR on whether the kernel is complete.

### 2.3 Ordering constraints

RR0 first: registration is cheap and stops further work being lost.
RR1 before RR3 — the top-level payoff theorems (RR3.G/H) quantify over
dispatch arms that must carry bundles first. RR2 and RR4 both touch the
trap and boot seams and should not run concurrently in the same files.
RR6 should run early despite its low position: it is cheap and it de-risks
every later Rust change by compiling the aarch64 paths at all.

Within that, RR2, RR5 and RR7 are independent and may run in parallel.

## 3. Dependencies

- SM0..SM9 landed (they are; see the register's per-plan verified evidence).
- Tier 0..3 green at HEAD — true at `v0.34.3`.
- Tier 4 gate accounting honest — landed at `v0.34.2`; the gates themselves
  still cannot run until SM10.E.D1 produces an image, which is SM10's work
  and deliberately not a WS-RR dependency.
- No dependency on SM10. WS-RR closes first.

## 4. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| RR0 | Registration and plan correction — nothing further is lost | 12 | S–M |
| RR1 | Live-path correctness: dispatch-arm bundles + donation queue migration | 14 | M–L |
| RR2 | Fault handling: full fault IPC with reply-based restart | 27 | XL |
| RR3 | `ipcInvariantFull` de-threading closure (D1, D6, D8) | 18 | L–XL |
| RR4 | Boot-path fail-open closure | 14 | M–L |
| RR5 | Verified lock primitives completion (SM2.C-defer, pre-v1.0.0) | 19 | L |
| RR6 | aarch64 compile coverage | 8 | M |
| RR7 | Medium-severity sweep | 10 | M |
| RR8 | Phase closure and hand-off to SM10 | 4 | S |

## 5. Sub-tasks

Estimates: **T** trivial (<1h) · **S** small (<½ day) · **M** medium (1–2 days)
· **L** large (3–5 days) · **XL** extra-large (>1 week, expect to split further).
Each sub-task is sized to be one coherent PR or less, per the PR checklist.

### RR0 — Registration and plan correction

Cheap, ordered first, and load-bearing: every later phase assumes the
register is accurate. RR0.A closes audit blocker 1's registration half.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR0.A.1 | Add an IPC de-threading workstream row to `docs/WORKSTREAM_HISTORY.md` recording per-slice state (D0/D2/D2′/D3/D4/D5/D7 closed; D1/D6/D8 open) with closure target RR3 | `docs/WORKSTREAM_HISTORY.md` | S |
| RR0.A.2 | Add it to `SMP_RELEASE_CLOSURE_PLAN.md` §2 Dependencies | (1 file) | T |
| RR0.A.3 | Add a CLAUDE.md standing-constraint bullet naming the two still-threaded conjuncts, so new code does not assume `ipcInvariantFull` is end-to-end machine-checked; mirror to `AGENTS.md` | `CLAUDE.md`, `AGENTS.md` | S |
| RR0.B.1 | Rewrite `SMP_RELEASE_CLOSURE_PLAN.md` §1 phase goal against the real SM10.E scope (§2.2 of the register) | (1 file) | S |
| RR0.B.2 | Replace the 4–6 week estimate with one derived from the RR6 compile-coverage result and the SM10.E deliverable list | (1 file) | T |
| RR0.C.1 | Add the missing SM9 term to the §5 theorem tally | (1 file) | T |
| RR0.C.2 | Replace the hand-summed `wsm_theorem_count` literal with a generated manifest, so the marker theorem cannot certify a stale number | `scripts/`, `SeLe4n/Kernel/Concurrency/` | M |
| RR0.D.1 | Correct the SM10.C.4 archive list: add the SM9 plan, this plan, and the register; update the file-move count | (1 file) | T |
| RR0.E.1 | Refresh the SM10.B sub-task table against the tree — five of six suites and two of three fixtures already exist | (1 file) | S |
| RR0.F.1 | Register the remaining unregistered debt the debt sweep found, each with an owner and closure target | `docs/WORKSTREAM_HISTORY.md` | M |
| RR0.G.1 | Fix SM4.C.11's circular closure target (the phase that owns it is marked LANDED); re-home it to a phase that can close it | (2 files) | S |
| RR0.H.1 | Hand SM10.A the register's §7 low-severity table as its documentation work-list, cross-referenced from `SMP_RELEASE_CLOSURE_PLAN.md` SM10.A | (2 files) | T |

**Acceptance**: `grep` for each open workstream name returns a hit in
`docs/WORKSTREAM_HISTORY.md`; no plan in `docs/planning/` lacks a status
header; the SM10 tally arithmetic includes every landed phase.

### RR1 — Live-path correctness

Closes audit blockers 2 and 3. Both are implement-the-improvement cases whose
groundwork is already staged, and RR1 is a prerequisite for RR3's payoff
theorems.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR1.A.1 | Add `applyCallDonationOnCore` threading donor and donee home cores | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | M |
| RR1.A.2 | Call `migrateSchedContextReplenishment` from it (donor home → donee home), mirroring the cancellation path that already does this | (same) | M |
| RR1.A.3 | Prove the call path preserves the SM5.H affinity invariant | `SeLe4n/Kernel/SchedContext/` | M |
| RR1.B.1 | Add the mirror migration inside `applyReplyDonationOnCore` (replier home → original-owner home) | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | M |
| RR1.B.2 | Prove the reply path preserves the affinity invariant | (same) | M |
| RR1.C.1 | Bridge theorem: boot-core instantiation of both migrations reduces to the single-core forms | (2 files) | S |
| RR1.D.1 | `endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull` — use the staged `endpointSendDualOnCore_bootCore_{block,rendezvous}_eq_single` rewrites | `SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean` | L |
| RR1.D.2 | Per-core form `…_preserves_ipcInvariantFull_perCore` | (same) | M |
| RR1.E.1 | `clearWokenReceiverStash` preservation bundle | `SeLe4n/Kernel/IPC/` | M |
| RR1.F.1 | `endpointCallCrossCoreDispatch` preservation bundle | `SeLe4n/Kernel/IPC/CrossCore/` | M |
| RR1.G.1 | `endpointReplyCrossCoreDispatch` preservation bundle | `SeLe4n/Kernel/IPC/CrossCore/` | M |
| RR1.H.1 | Extend the cancellation `ipcInvariant` closure to the operation that actually runs on `.tcbSuspend` — today's claim excludes it | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | L |
| RR1.H.2 | Discharge the `hTeardownProj` hypothesis whose closure form returns its own premise | `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean` | L |
| RR1.I.1 | Tests: donation-migration and dispatch-arm coverage; extend the cross-core IPC suite | `tests/SmpIpcSuite.lean` | M |

**Acceptance**: every arm reachable from `SeLe4n/Kernel/API.lean`'s SMP
dispatch carries a `_preserves_ipcInvariantFull` theorem; the donation paths
migrate the replenish queue; no cancellation theorem rests on an
unproven teardown hypothesis.

### RR2 — Fault handling: full fault IPC with reply-based restart

The largest phase, and the one that closes the audit's most serious security
finding: data and instruction aborts today set `x0` and return to the
faulting instruction with `ELR_EL1` restored verbatim, so any user thread
touching an unmapped page wedges its core forever. It is not exploitable at
`v0.34.3` because nothing boots — it becomes reachable precisely when SM10.E
succeeds, which is the wrong moment to discover it.

**What already exists.** The TCB carries a `faultHandler : Option CPtr`
field with no consumer — an unwired field, so this is an
implement-the-improvement case rather than new architecture.
`SeLe4n/Kernel/Architecture/ExceptionModel.lean` already classifies
exceptions (`classifySynchronousException`), and its abort arms return
`.error .vmFault` as a pure error with no state change. Its only callers are
tests: the Rust `trap.rs` runs a *parallel* `esr_ec` match of its own, so
there are two classification paths and the Lean one is not live.

**What is missing.** A `Fault` type, fault-message encoding, handler
resolution, the delivery transition, reply-based resume and restart, and the
Rust wiring that makes the Lean path the live one.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR2.A.1 | `Fault` inductive: `vmFault` (address, FSR, prefetch flag), `capFault`, `unknownSyscall`, `userException` | `SeLe4n/Kernel/Architecture/Fault.lean` (new) | M |
| RR2.A.2 | `DecidableEq` + `BEq` + congruence lemmas for `Fault` | (same) | S |
| RR2.A.3 | Map `SynchronousExceptionClass` → `Fault`, replacing the `.error .vmFault` arms' classification role | (same) | S |
| RR2.B.1 | Fault message layout: `Fault` → `MessageInfo` label + message registers, at seL4 parity | `SeLe4n/Kernel/Architecture/Fault.lean` | M |
| RR2.B.2 | Round-trip theorem: encoding then decoding a fault is the identity | (same) | M |
| RR2.B.3 | Length theorem: every fault encodes within the message-register budget | (same) | S |
| RR2.C.1 | Resolve `faultHandler : Option CPtr` to an endpoint capability through the thread's CSpace | `SeLe4n/Kernel/IPC/Operations/Fault.lean` (new) | M |
| RR2.C.2 | Rights check: the handler cap must carry send rights; fail closed otherwise | (same) | S |
| RR2.C.3 | Negative: a thread with no `faultHandler`, or an unresolvable one, takes the RR2.H path | (same) | S |
| RR2.D.1 | Fault delivery transition — the faulting thread blocks and a fault IPC is sent to the handler endpoint, reusing the endpoint Call machinery rather than a parallel path | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | L |
| RR2.D.2 | Per-core form `faultDeliverOnCore`, with the cross-core SGI emission the other IPC paths use | `SeLe4n/Kernel/IPC/CrossCore/Fault.lean` (new) | L |
| RR2.E.1 | Reply object creation for the fault, so the handler receives a reply capability | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | M |
| RR2.F.1 | Reply-based **resume**: handler replies, faulted thread resumes at its saved `ELR` | (same) | M |
| RR2.G.1 | Reply-based **restart**: the reply carries a new PC and register values; the thread restarts there | (same) | L |
| RR2.G.2 | Restart register writeback into the TCB register file, reusing the syscall-return writeback rather than a second mechanism | `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | M |
| RR2.H.1 | No-handler policy: the thread is suspended fail-closed, never returned to the faulting instruction | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | M |
| RR2.I.1 | Wire `dispatchSynchronousException`'s `.dataAbort` / `.instrAbort` arms to the delivery transition, retiring the bare `.error .vmFault` | `SeLe4n/Kernel/Architecture/ExceptionModel.lean` | M |
| RR2.J.1 | `faultDeliver_preserves_ipcInvariantFull` (+ per-core form) | `SeLe4n/Kernel/IPC/Invariant/` | L |
| RR2.J.2 | Fault reply preserves `ipcInvariantFull`; scheduler and capability invariants preserved on both paths | (same) | L |
| RR2.K.1 | **Progress theorem**: a faulted thread cannot re-execute the faulting instruction without an intervening handler action — the theorem that makes the livelock unrepresentable | `SeLe4n/Kernel/IPC/Invariant/FaultProgress.lean` (new) | L |
| RR2.L.1 | Non-interference: fault delivery respects the information-flow policy, and a fault message carries no data across a label boundary | `SeLe4n/Kernel/InformationFlow/` | L |
| RR2.M.1 | Rust: `trap.rs` abort arms call the Lean fault entry through a new `@[export]`, inside `with_kernel_entry` | `rust/sele4n-hal/src/trap.rs`, `SeLe4n/Platform/FFI.lean` | M |
| RR2.N.1 | Rust: `ELR_EL1` writeback on resume vs restart — the trap frame gains the mutator it currently lacks | `rust/sele4n-hal/src/trap.rs` | M |
| RR2.O.1 | Retire the duplicate classification path: `trap.rs` classifies via the Lean model rather than its own `esr_ec` match, so the two cannot diverge | `rust/sele4n-hal/src/trap.rs` | M |
| RR2.P.1 | Fault-return arms use the v2 offset-label ABI, not the retired raw-discriminant-in-`x0` convention | `rust/sele4n-hal/src/svc_dispatch.rs` | S |
| RR2.Q.1 | Tests: fault delivery, resume, restart, no-handler suspend, and the negative that a fault never returns to the faulting instruction | `tests/FaultHandlingSuite.lean` (new) | L |
| RR2.Q.2 | Golden fixture: a 4-core trace with a faulting thread and a handler | `tests/fixtures/` | M |

**Acceptance**: no execution path returns to a faulting instruction without
handler action (RR2.K.1); `faultHandler` has consumers; `trap.rs` has one
classification path, not two; Tier 0..3 green.

**Split guidance**: RR2.D.1, RR2.G.1, RR2.J.\*, RR2.K.1, RR2.L.1 and RR2.Q.1
are each an L and should land as their own PR. If RR2.D.1 exceeds a week,
split it into the block-the-sender half and the enqueue-on-handler half.

### RR3 — `ipcInvariantFull` de-threading closure (D1, D6, D8)

Closes [`IPC_INVARIANT_DETHREADING_PLAN.md`](IPC_INVARIANT_DETHREADING_PLAN.md),
whose D1, D6 and D8 slices are open. Two of the twenty conjuncts are still
assumed as post-state hypotheses on nearly every bundle —
`blockedThreadsPendingMessageConsistent` on 33 of 35 and
`replyCallerLinkageReciprocal` on 31 of 35 — so `ipcInvariantFull` is not
today an end-to-end machine-checked property of the live kernel.

The per-transition establishers for all seven base transitions already exist,
so D1's residue is module ordering rather than missing mathematics. RR3.G and
RR3.H depend on RR1: the payoff theorems quantify over dispatch arms that
must carry bundles first.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR3.A.0 | Build the de-threading gate: over the code view, report every `_preserves_ipcInvariantFull` statement that binds a conjunct applied to the **post** state, independent of binder name. Establishes the true baseline and becomes the phase's progress meter | `scripts/check_ipc_invariant_dethreading.py` (new) | M |
| RR3.A.1 | Resolve the module-ordering obstruction blocking `blockedThreadsPendingMessageConsistent` composition | `SeLe4n/Kernel/IPC/Invariant/` | M |
| RR3.A.2 | De-thread `hBTPM'` across the endpoint bundles (send / receive / call) | `SeLe4n/Kernel/IPC/Invariant/Structural/` | L |
| RR3.A.3 | De-thread it across the reply and replyRecv bundles | (same) | L |
| RR3.A.4 | De-thread it across the notification bundles | (same) | M |
| RR3.A.5 | De-thread it across the lifecycle and cancellation bundles | (same) | L |
| RR3.B.1 | Prove the per-transition establishers for `replyCallerLinkageReciprocal`'s forward clause | `SeLe4n/Kernel/IPC/Invariant/` | L |
| RR3.B.2 | De-thread `hRCL'` across the endpoint bundles | (same) | L |
| RR3.B.3 | De-thread it across the reply, notification and lifecycle bundles | (same) | L |
| RR3.B.4 | Decide the `consumeCallerReply` documented exception — close it, or re-record it with the reason it cannot close | (same) | M |
| RR3.C.1 | De-thread `dualQueueSystemInvariant` / `badgeWellFormed` at the eight remaining sites | (same) | M |
| RR3.D.1 | De-thread `donationOwnerValid` at the six remaining sites | (same) | M |
| RR3.E.1 | Build the reachability bundle that discharges the remaining pre-state preconditions | `SeLe4n/Kernel/IPC/Invariant/Reachability.lean` (new) | L |
| RR3.E.2 | Prove the boot state satisfies it, so the bundle is inhabited rather than vacuous | (same) | M |
| RR3.F.1 | Invariant-preservation theorems for the donation primitives on the live `.call` path, which carry none today | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | L |
| RR3.G.1 | `dispatchWithCap_preserves_ipcInvariantFull` (**depends on RR1**) | `SeLe4n/Kernel/API.lean` | L |
| RR3.H.1 | `syscallDispatch_preserves_ipcInvariantFull` — the D8 payoff | (same) | L |
| RR3.I.1 | Retire `IPC_INVARIANT_DETHREADING_PLAN.md`: mark closed, record the closure version, move to `docs/dev_history/planning/` | (file move) | S |

**Acceptance**: the RR3.A.0 gate reports zero post-state bindings of
`blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal`
across the `_preserves_ipcInvariantFull` family; both payoff theorems exist
and are cited from `docs/CLAIM_EVIDENCE_INDEX.md`.

**A note on measuring this.** The ten conjuncts de-threaded by earlier slices
each had a canonical primed binder (`hQNBC'`, `hPRR'`, …), so "de-threaded"
could be checked by grepping the name to zero — and in the comment-free code
view all ten are indeed zero. The two remaining conjuncts have **no such
canonical name**: they appear under `hInv`, `hRecip`, `hWtpmn` and bare `h`
depending on the bundle. A name-based check would therefore report success
without measuring anything, which is the same failure shape as the tier-4
gates that scored a skip as a pass. RR3.A.0 exists so the criterion is
measured rather than assumed.

### RR4 — Boot-path fail-open closure

Three latents that are unreachable today only because nothing boots. Each
becomes live the moment SM10.E succeeds, so each must close before it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR4.A.1 | Define a production `LabelingContext` — none exists; `testLabelingContext` maps every non-zero id to `publicLabel` | `SeLe4n/Kernel/InformationFlow/Policy.lean` | M |
| RR4.B.1 | Make the hardware boot path **require** a labeling context: `bootAndInitialiseFromPlatform`'s `Option` defaulting to `none` currently leaves the all-public test context installed | `SeLe4n/Platform/FFI.lean` | M |
| RR4.B.2 | Fail closed when absent on a hardware build, rather than silently proceeding | (same) | S |
| RR4.C.1 | Strengthen `isInsecureDefaultContext` to catch all-public contexts — it returns `false` for `testLabelingContext` today, so the guard does not fire on the very context the boot path installs | `SeLe4n/Kernel/InformationFlow/Policy.lean` | M |
| RR4.C.2 | Theorem: the production context passes the guard and the test context does not | (same) | S |
| RR4.D.1 | Add the `lean_ready` gate to the SVC dispatch seam, which has none despite `kernel_entry.rs`'s claim that every seam consults it | `rust/sele4n-hal/src/svc_dispatch.rs` | S |
| RR4.E.1 | Add it to the suspend seam | `rust/sele4n-hal/src/ffi.rs` | S |
| RR4.E.2 | Build-time or test-time check that every seam in the five-entry table consults the gate, so a sixth seam cannot be added without one | `rust/sele4n-hal/build.rs` | M |
| RR4.F.1 | Wire `bootFromPlatformWithIdleThreads` into the production boot path — it is proven correct (`…_all_cores_have_idle`) but has no caller, so the proof does not carry through to runtime | `SeLe4n/Platform/Boot.lean` | M |
| RR4.F.2 | Update `bootFromPlatformChecked`'s downstream theorems for the new base | (same) | M |
| RR4.G.1 | Make the three staged state-committing kernel entries production-reachable, so a linked image carries their `@[export]` symbols | `SeLe4n.lean`, `scripts/staged_module_allowlist.txt` | M |
| RR4.G.2 | Verify each expected `@[export]` symbol is present in the built archive | `scripts/` | M |
| RR4.H.1 | Bracket `suspend_thread_inner`, which commits kernel state outside the kernel-entry lock | `SeLe4n/Platform/FFI.lean` | S |
| RR4.I.1 | Replace the two `debug_assert!` lock/vector tripwires, which vanish from the release image, with checks that survive it | `rust/sele4n-hal/src/` | S |

**Acceptance**: a hardware boot without an explicit production labeling
context fails closed; every seam consults the readiness gate; idle threads
are installed on the production path; the staged-module count falls by three.

### RR5 — Verified lock primitives completion (SM2.C-defer, pre-v1.0.0)

[`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md)
scopes itself post-v1.0.0. **This plan moves it before v1.0.0.** Shipping a
verified microkernel whose core concurrency primitive has a known-deferred
completeness story understates what "verified" means on the one component
every other subsystem's serialisability argument rests on.

Most of D-1..D-6 has landed. The residue is not spread evenly across the six
items — it concentrates in one theme: **the refinement bridges connect the
Lean specs to transliterations and to their own assumptions, rather than to
the locks the kernel actually deploys.**

Three verified facts frame the phase:

- `lock_bridge.rs` builds its static pool from `crate::rw_lock::RwLock` — the
  CAS-retry, non-FIFO implementation — while the Lean spec was tightened to
  strict FIFO.
- `QueuedRwLock`, the FIFO-preserving implementation D-5 landed, has **zero**
  consumers outside its own module.
- The Tier-5 oracle's own docstring states it is a software model, not the
  real lock, because the real one blocks under contention.

So the deployed lock is not the one the spec describes, and the harness that
would have caught that drives neither.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR5.A.1 | Add non-blocking `try_acquire_read` / `try_acquire_write` to the real `RwLock`, removing the oracle's stated reason for modelling instead of driving | `rust/sele4n-hal/src/rw_lock.rs` | M |
| RR5.A.2 | Rewrite the Tier-5 oracle to drive the real lock through those entry points | `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` | L |
| RR5.A.3 | Extend the oracle to the queued lock, so both implementations are covered | (same) | M |
| RR5.B.1 | Point `STATIC_RW_LOCK_POOL` and the `ffi_rw_lock_*` entries at `QueuedRwLock`, so the deployed lock is the FIFO one the spec describes | `rust/sele4n-hal/src/lock_bridge.rs` | M |
| RR5.B.2 | Update the FFI and information-flow docs that name the CAS-retry lock as deployed | `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | S |
| RR5.B.3 | Decide and record the fate of `rw_lock.rs`: retained for compatibility, or retired | (2 files) | S |
| RR5.C.1 | `TicketLockConcrete` operational step function, mirroring the RwLock refinement's shape | `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean` | L |
| RR5.C.2 | Trace correspondence (`blockBisim` / `ListBlockBisim` analogue) replacing the counter arithmetic in `rust_ticketLock_refines_lean` | (same) | L |
| RR5.C.3 | Replace the tautological conjunct with a statement that can fail | (same) | M |
| RR5.D.1 | D-4: prove `opCorresponds`-chain plus an explicit load-then-CAS trace-shape predicate implies `ListBlockBisim`, so the twelve discharge lemmas compose into the main theorem instead of it assuming its own conclusion | `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` | XL |
| RR5.D.2 | Corollary against the deployed lock, closing the spec-to-implementation gap end to end | (same) | L |
| RR5.E.1 | Add `loom` as a `cfg(loom)` dev-dependency with bounded exhaustive interleavings | `rust/sele4n-hal/Cargo.toml` | M |
| RR5.E.2 | Add a nightly `miri` job for the queued lock | `.github/workflows/` | M |
| RR5.E.3 | Raise the FIFO and stress iteration counts to the plan's stated thresholds | `rust/sele4n-hal/src/queued_rw_lock.rs` | S |
| RR5.F.1 | Prove the D-2.5 writer-bounded-wait statement as specified — the ingredients exist; only a single-state `_weak` corollary landed | `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` | M |
| RR5.F.2 | Repoint the R-10 aggregator entry at the theorem that proves writer liveness; keep the safety theorem registered under its accurate name | `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` | S |
| RR5.G.1 | Plan corrections: the retired-MCS design section, the D-1.9 landed row, the false §3.2.6.1 theorem statement, and the Appendix A commands that name a nonexistent script | `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` | M |
| RR5.G.2 | Retitle the plan: it is no longer post-v1.0.0; add an SM2.C-defer row to `docs/WORKSTREAM_HISTORY.md` with closure target RR5 | (2 files) | S |

**Acceptance**: the deployed RwLock is the one the Lean spec describes; the
Tier-5 oracle drives real locks; neither refinement theorem assumes its own
conclusion or contains a tautological conjunct; `loom` and `miri` gates run.

**Note on RR5.D.1**: this is the phase's only XL and the likeliest to need
splitting — take the trace-shape predicate and the composition proof as
separate PRs, and land the predicate first so the composition has something
to consume.

### RR6 — aarch64 compile coverage

Cheap, early, and it de-risks every later Rust change. No aarch64 target is
compiled anywhere in the tree or CI today, so 67 cfg-gated blocks, 59 `asm!`
sites and all three `.S` files have **zero** compile coverage. SM10.E would
otherwise be the first thing that ever compiles them, while also being the
first thing that links and boots them.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR6.A.1 | Add the `aarch64-unknown-none` target to the Rust toolchain file | `rust/rust-toolchain.toml` | T |
| RR6.B.1 | Make `cargo check --target aarch64-unknown-none -p sele4n-hal --features hw_target` succeed | `rust/sele4n-hal/` | L |
| RR6.B.2 | Fix what it surfaces in the cfg-gated blocks | (same) | L |
| RR6.B.3 | Fix what it surfaces in the `asm!` sites | (same) | L |
| RR6.C.1 | Assemble the three `.S` files under the cross target | `rust/sele4n-hal/build.rs` | M |
| RR6.D.1 | CI job running the cross check on every PR | `.github/workflows/` | M |
| RR6.D.2 | Tier 0 check that the cross target stays configured, so it cannot be silently dropped | `scripts/test_tier0_hygiene.sh` | S |
| RR6.E.1 | Record the result in the register and use it to size SM10.E (RR0.B.2 consumes this) | (2 files) | S |

**Acceptance**: `cargo check` for aarch64 passes in CI; the `.S` files
assemble; SM10.E's estimate is derived from a real compile rather than a
guess.

### RR7 — Medium-severity sweep

The 46 medium findings, batched by theme rather than by source plan, so each
PR touches one subsystem. The register's §6 table is the authoritative
per-item list; the batches below say who owns what.

| Sub | Description | Findings | Est |
|-----|-------------|----------|-----|
| RR7.A.1 | Boot MMU corrections: 960 MiB of RAM mapped as Device, nothing mapped above 4 GiB | 2 | L |
| RR7.A.2 | Retract or satisfy the FFI unqualified boot identity-map claim, which the boot tables do not provide above 3 GiB — per the implement-the-improvement rule, prefer extending the tables | 1 | M |
| RR7.B.1 | Extend the flagship "syscall entry implies capability held" theorem to the live checked dispatch path; it covers only the legacy path today | 1 | L |
| RR7.C.1 | Implement the missing Tier-0 grep gate banning non-IS TLBI, which §4.4 claims exists | 1 | M |
| RR7.C.2 | Remaining Rust HAL mediums | 3 | M |
| RR7.D.1 | Syscall return ABI mediums | 4 | M |
| RR7.E.1 | Fine-lock migration mediums | 3 | M |
| RR7.F.1 | TLB shootdown mediums | 3 | M |
| RR7.G.1 | Per-object lock mediums | 4 | M |
| RR7.H.1 | Remaining per-plan mediums: declassification, panic-hang, cross-core IPC, foundations, reply objects, master plan, doc-sync, improvement-rule | 12 | L |

**Acceptance**: every medium finding in the register's §6 table is closed or
has an explicit, registered deferral with a closure target. A medium may be
deferred; it may not be dropped.

### RR8 — Phase closure and hand-off to SM10

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR8.A.1 | Walk the RR0..RR7 acceptance gates and record the closing version for each | (1 file) | S |
| RR8.B.1 | Update `UNFINISHED_SMP_WORK.md`: mark each closed finding with its version, leaving open items visible | `docs/planning/UNFINISHED_SMP_WORK.md` | M |
| RR8.C.1 | WS-RR closure entry in `docs/WORKSTREAM_HISTORY.md`; update the CLAUDE.md phase table | (3 files) | S |
| RR8.D.1 | Hand-off: confirm SM10's §2 dependencies are genuinely met, and that its §1 scope statement now matches the tree | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | S |

## 6. Verification strategy

### 6.1 What each phase proves

- **RR1** — every live SMP dispatch arm carries a `_preserves_ipcInvariantFull`
  theorem; both donation paths preserve the SM5.H affinity invariant.
- **RR2** — `faultProgress`: no reachable state returns a thread to its
  faulting instruction without an intervening handler action. This is the
  theorem that makes the livelock unrepresentable rather than merely absent.
- **RR3** — `ipcInvariantFull` holds end to end: the top-level dispatch
  theorems, with no post-state conjunct threaded as a hypothesis anywhere.
- **RR4** — a hardware boot with no production labeling context fails closed;
  every core has an idle thread at boot.
- **RR5** — the deployed Rust locks refine their Lean specs, by trace
  correspondence rather than counter arithmetic.

### 6.2 What each phase validates

Tier 0..3 green after every sub-task, per the PR checklist. RR6 adds an
aarch64 `cargo check` to CI. RR2 and RR5 add executable suites
(`tests/FaultHandlingSuite.lean`, the Tier-5 oracle) with golden fixtures.

### 6.3 Gate discipline

Any new acceptance gate this phase adds is registered with `run_gate_check`,
not `run_check`, so a gate that cannot run is reported NOT RUN rather than
PASS — the contract landed at `v0.34.2` and pinned by
`scripts/test_gate_skip_accounting.sh`.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| RR2 fault IPC is larger than XL and slips the phase | HIGH | HIGH | Split at the sub-task boundaries §RR2 names; the RR2.H no-handler suspend alone removes the livelock, so partial delivery is still safe |
| RR3 de-threading blocks on an ordering cycle between invariant modules | MED | HIGH | RR3.A.1 addresses ordering before any bundle edit; the per-transition establishers already exist |
| RR5.D.1 bisimulation does not close | MED | MED | Land the trace-shape predicate independently; the corollary can follow in a later cut without blocking v1.0.0 |
| RR6 surfaces a large volume of aarch64 compile errors | MED | MED | Expected and desirable — it is cheaper here than at SM10.E; RR6.B.2/.B.3 are sized L for this reason |
| Repointing the FFI pool at `QueuedRwLock` (RR5.B.1) regresses performance | LOW | MED | The Tier-5 oracle covers both implementations after RR5.A.3; keep `rw_lock.rs` until measurements land |
| Two phases edit the trap seam concurrently | MED | MED | §2.3 sequences RR2 and RR4 apart in the same files |
| Medium findings are quietly dropped rather than deferred | MED | LOW | RR7's acceptance gate requires a registered deferral, not silence |

## 8. Acceptance gate

- [ ] Every open workstream has a durable registry entry with a closure target.
- [ ] `SMP_RELEASE_CLOSURE_PLAN.md` §1 scope and estimate match the tree.
- [ ] The SM10 theorem tally includes SM9 and is generated, not hand-summed.
- [ ] Every live SMP dispatch arm carries an `ipcInvariantFull` bundle.
- [ ] Both cross-core donation paths migrate the CBS replenish queue.
- [ ] Fault IPC delivers, resumes and restarts; no path returns to a faulting instruction.
- [ ] `hBTPM'` and `hRCL'` return zero occurrences repo-wide.
- [ ] Both top-level dispatch payoff theorems exist.
- [ ] Hardware boot without a production labeling context fails closed.
- [ ] Idle threads are installed on the production boot path.
- [ ] Every kernel seam consults the readiness gate.
- [ ] The deployed RwLock is the one the Lean spec describes.
- [ ] Neither lock refinement theorem assumes its own conclusion.
- [ ] aarch64 `cargo check` runs in CI and passes.
- [ ] Every medium finding is closed or has a registered deferral.
- [ ] Tier 0..3 green at HEAD; Tier 4 honest about what did not run.
- [ ] `UNFINISHED_SMP_WORK.md` updated with closing versions.

## 9. Cross-references

- **Source register**: [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md)
- **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10)
- **Overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Absorbed by RR3**: [`IPC_INVARIANT_DETHREADING_PLAN.md`](IPC_INVARIANT_DETHREADING_PLAN.md)
- **Absorbed by RR5**: [`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md), [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
- **Canonical status**: [`../WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md)
- **Out of scope**: [`HARDWARE_PARTITION_ISOLATION_PLAN.md`](HARDWARE_PARTITION_ISOLATION_PLAN.md)

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Per-PR minimum
./scripts/test_smoke.sh
# When theorems or invariants change
./scripts/test_full.sh

# Phase-specific
lake build SeLe4n.Kernel.Architecture.Fault              # RR2
lake build SeLe4n.Kernel.IPC.Invariant.FaultProgress     # RR2
lake build SeLe4n.Kernel.IPC.Invariant.Reachability      # RR3
lake exe fault_handling_suite                            # RR2
./scripts/test_tier5_cross_language.sh                   # RR5
cargo check --target aarch64-unknown-none \
  --manifest-path rust/Cargo.toml -p sele4n-hal --features hw_target   # RR6

# Gate honesty — a skipped acceptance gate must fail here
SELE4N_REQUIRE_GATES=1 ./scripts/test_tier4_smp_bootcheck.sh

# Version sync
./scripts/check_version_sync.sh
```

---

*WS-RR exists because the audit found SM10's prerequisites unmet, not because
SM0..SM9 were unsound. The phase closes when SM10's §2 dependency list is true
of the tree rather than of the plan that asserts it.*
