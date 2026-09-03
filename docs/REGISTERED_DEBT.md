# Registered Debt

**This file is the project's single debt register.** Every deferred item in
seLe4n has a row here, with an owner and a closure target. A row leaves only
when the work lands or the deferral is retracted.

`CLAUDE.md`'s deferral rule requires exactly this, and forbids in-source TODOs
that age out with the surrounding workstream. The rule is enforced rather than
asserted: `scripts/check_deferral_registration.py` (Tier 0) fails a source
comment that declares itself untracked and cites nothing, and fails a citation
naming a row number that does not exist here.

**There is one register and it is this one.**
`docs/audits/AUDIT_v0.30.11_DEFERRED.md`, which four authorities once named,
was never created and will not be: a second register competing with the
canonical one is how the first divergence happened.

This file is **not** a record of what was done. What each version changed is in
[`CHANGELOG.md`](../CHANGELOG.md), one entry per merged PR; what is in flight
is in `CLAUDE.md`'s *Active workstream context* and the phase plans under
[`planning/`](planning/); how to work on any of it is
[`DEVELOPMENT.md`](DEVELOPMENT.md).

## How to use it

Three tables, by who can close the item:

| Table | Owner |
|-------|-------|
| **A** | a live WS-RR phase — every row has a numbered sub-task in [`SMP_RELEASE_READINESS_PLAN.md`](planning/SMP_RELEASE_READINESS_PLAN.md) |
| **B** | SM10 — each needs the image or the runtime seam SM10.1 produces |
| **C** | no pre-v1.0.0 owner — each row states why it may wait |

A row in **C** constrains what v1.0.0 may claim; WS-RR's RR8.4 hand-off check
reads that table, and RR8.2 records closing versions.

To add a row: put it in the table whose owner can close it, name the file it
lives in, and give it a closure target. To cite it from source, reference this
file (and the row number, for the §C.1 enumeration) rather than declaring the
item untracked.

### A — owned by a live WS-RR phase

Every row here has a numbered sub-task in
[`docs/planning/SMP_RELEASE_READINESS_PLAN.md`](planning/SMP_RELEASE_READINESS_PLAN.md).
The register exists so the item is visible from this file even when the plan
is archived.

| Debt | Where it lives | Closure target |
|------|----------------|----------------|
| WS-DT slices D1, D6, D8 — two `ipcInvariantFull` conjuncts still threaded as post-state hypotheses; no dispatch payoff theorem — **closed v0.34.43** (the measured baseline was 103 bindings over six conjuncts, all de-threaded; the three payoff theorems landed with the per-arm bundle layer, RR3.15–RR3.26) | `SeLe4n/Kernel/IPC/Invariant/`, `SeLe4n/Kernel/API.lean` | RR3.1–RR3.26 |
| Cross-core SchedContext donation never migrates the CBS replenish queue, breaking the SM5.H affinity invariant on a live path — **closed v0.34.42** (all three live paths, RR2.20 included) | `SeLe4n/Kernel/IPC/Operations/Donation.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | RR2.1–RR2.12, RR2.20 |
| The live `.send` arm carries no `ipcInvariantFull` preservation while SM6.D claims coverage — **closed v0.34.42** (and the `.receive` arm's WithCaps form, which the audit had mismeasured as covered, in the same cut) | `SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean` | RR2.14, RR2.15 |
| Cancellation NI rests on a `hTeardownProj` hypothesis whose closure form returns its own premise — **partially closed v0.34.42** (`.ready` and `.blockedOnReply` arms discharged; the three queue arms wait on the label-uniformity invariant, RR3) | `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean` | RR2.18, then RR3 |
| VM faults are unhandled: a data or instruction abort returns to the faulting instruction, wedging the core.  Unreachable only because nothing boots — **closed v0.34.44** (every non-`SVC` arm delivers; `faultDeliverOnCore_not_dispatchable` says no disposition leaves the thread runnable on the core it faulted on) | `SeLe4n/Kernel/Architecture/ExceptionModel.lean`, `rust/sele4n-hal/src/trap.rs` | RR4.1–RR4.27 |
| `TCB.faultHandler : Option CPtr` has no consumer — **closed v0.34.44** (`resolveFaultHandler` resolves it through the thread's own CSpace and gates it on seL4's `sendFaultIPC` predicate: send, and grant **or** grant-reply) | `SeLe4n/Model/Object/Structures.lean` | RR4.7 |
| `.replyRecv` — the idiomatic fault-handler loop — does not route through the RR4.14 reply seam, so a handler that answers a fault with `seL4_ReplyRecv` reaches the ordinary reply and wakes the faulted thread `.ready` at the instruction that faulted.  `.reply` is closed; the workaround is `.reply` + a separate `.receive`.  `replyRecvBody` composes the reply leg, a receive leg and a donation return in one transition, so the fault branch cannot be substituted for its reply leg without re-deriving what the other two legs are handed | `SeLe4n/Kernel/API.lean` (`replyRecvBody`), `SeLe4n/Kernel/IPC/CrossCore/Fault.lean` | RR7 |
| The staged dispatch payoff's `.reply` arm is confined to unfaulted callers (`syscallDispatchQuiescence.replyNoPendingFault`).  Composing `faultReplyOnCore_preserves_ipcInvariantFull` into it needs a lemma the reply chain does not carry — that `endpointReplyCrossCoreDispatch` leaves its target `.ready`, hence `passiveServerIdleAllowed`, which the fault reply's abandon arm consumes at the **post**-state; threading a post-state hypothesis instead is what the RR3 gate forbids.  The transition-level bundle exists and is proven; only its composition into the payoff waits | `SeLe4n/Kernel/IPC/Invariant/DispatchPayoff.lean`, `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean` | RR7 |
| A core that delivers a fault cannot switch away from the blocked thread: the SM10.1 context restore installs no successor, so `trap.rs::deliver_fault` halts the core instead of `eret`ing back onto the faulting instruction.  Unreachable at v0.34.44 (no core sets `lean_ready`) | `rust/sele4n-hal/src/trap.rs` | SM10.1 |
| A user send's `MessageInfo` label is discarded at delivery: `IpcMessage.label` is set by kernel-originated (fault) messages only, so a thread holding a send capability to a fault endpoint cannot mint a `seL4_Fault_tag` — deliberate, and the pass-through needs its own authority story before it is restored | `SeLe4n/Model/Object/Types.lean`, `SeLe4n/Kernel/API.lean` | RR7 |
| On hardware only `MR0`-`MR3` of a delivered fault message reach the handler's registers: the WS-RA return frame carries four message registers in `x2`-`x5` and no receive path writes `MR4` onward into the receiver's IPC buffer (seL4's `setMRs_fault` does — the buffer write is the WS-RA "4-register return window" residual, which RR4 gave its first consumer).  The model delivers every word (`decodeFault_encodeFault`); an `unknownSyscall` (13 words) or `userException` (5 words) handler on hardware sees its first four.  Closure: the receive-side IPC-buffer write (`Architecture.IpcBufferRead` gains a write twin through the receiver's VSpace), staged at RR7 so the fault path and the `.receive`/`.replyRecv` arms take it together | `SeLe4n/Kernel/Architecture/Fault.lean` (`encodeFault`), `SeLe4n/Kernel/Architecture/SyscallReturn.lean`, `SeLe4n/Kernel/Architecture/IpcBufferRead.lean` | RR7 |
| The RR4.18 row promised scheduler and capability invariant preservation on both fault paths; what landed is `ipcInvariantFull` (delivery, reply, suspend, abandon, restart) and `objects.invExt`.  The cross-core Call and reply chains the fault path composes carry no `schedulerInvariantBundle` / `capabilityInvariantBundle` preservation themselves (`endpointCall_preserves_schedulerInvariantBundle` and `endpointReply_preserves_{scheduler,capability}InvariantBundle` are the single-core forms), so the fault path cannot compose what its substrate lacks.  Closure: lift the two bundles over `endpointCallCrossCoreDispatch` / `endpointReplyCrossCoreDispatch`, then compose `faultDeliverOnCore` / `faultReplyOnCore` (one-TCB rewrites and `removeRunnableOnCore` on top) — an RR7 slice alongside the `.replyRecv` fault branch, which needs the same lift | `SeLe4n/Kernel/IPC/Invariant/FaultPreservation.lean`, `SeLe4n/Kernel/IPC/CrossCore/DispatchInvariant.lean` | RR7 |
| ~~No production `LabelingContext`: the hardware boot path leaves `testLabelingContext`, which maps every non-zero id to `publicLabel`, installed~~ — **CLOSED v0.34.48**: `deploymentLabelingContext` builds a context that is `LabelingContextValid` unconditionally, `confinedLabelingContext` is the two-domain production instance, the boot wrapper's context argument is mandatory and an inadmissible one fails the boot closed *before* any state is committed, and the pre-boot labeling reference is one the guard rejects; the platform binding stores the `DeploymentLabeling` source, so what a hardware boot installs is admitted *and* `LabelingContextValid` by theorem (`PlatformBinding.labeling_valid`, PR #889 review).  The guard itself became exact: a declared separation witness — two admissible threads, neither the sentinel nor an idle thread (`separationWitnessAdmissible`) — the kernel *evaluates*, replacing the three-id sample `testLabelingContext` evaded, so `isInsecureDefaultContext ctx = false` now entails `LabelingContextValid.labelNonTriviality`  **Review round 2 (PR #889)**: the source carries the four policy fields (`memoryOwnership`, `endpointPolicy`, `declassificationPolicy`, `auditMonitorClearance`) with their fail-closed defaults, so a binding configures them where it declares its labeling; before, every hardware boot was forced to the constructor's defaults with no declassification and no audit monitor; **review round 3**: the boot wrapper refuses a boot whose labeling's declared separation witnesses are not installed threads of the boot state (`declaredWitnessesInstalled`, `uninstalledSeparationWitnessBootError`) — the guard decides that two admissible ids are separated, only the boot state can say they are threads; **review round 5**: the family's lower witness is a parameter — thread `1`, the old fixed witness, is the boot VSpace root's object id on every binding, so a boot carrying its own root could never install it — the RPi5 binding declares `rpi5LowerWitnessIndex`, and `PlatformBinding.witnessesOffBootVSpaceRoot` holds every binding's witnesses apart from its root by evaluation | `SeLe4n/Kernel/InformationFlow/Policy.lean`, `SeLe4n/Platform/FFI.lean` | RR5.1–RR5.5 |
| ~~Two kernel seams (SVC dispatch, cross-core suspend) do not consult the per-core `lean_ready` gate, though `kernel_entry.rs` claims every seam does~~ — **CLOSED v0.34.48**: both consult it (`LEAN_UPCALLS_OUTSIDE_THE_GATE` is down to the boot install, which cannot sit behind the gate it establishes), the SVC seam halts — ahead of every prefilter and of the `x7` narrowing, pinned by `svc_arm_readiness_gate_status` (PR #889 review) — and the suspend seam returns `IllegalState`, and RR5.9 added the compile-time half — a Lean `extern` may be declared, defined or exported only under `feature = "hw_target"`, which `cfg(not(test))` did not achieve | `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-hal/src/ffi.rs` | RR5.6–RR5.9 |
| ~~Three `@[export]` runtime-seam modules are staged-only, outside the production import closure, so a linked image would not carry their symbols~~ — **CLOSED v0.34.48**: promoted (with the two closure modules they pull in, so the staged count fell by five), and `scripts/check_kernel_entry_exports.py` verifies every required symbol against the built static archive on each Tier-1 run, over a requirement derived from every HAL `extern "C"` declaration (archive, assembly global, or a reconciled `EXPECTED_UNRESOLVED` entry — the intersection form hid a rename on either side, PR #889 review); **review round 3**: an assembly provider is a *defined* symbol (directive and label) in a source `build.rs` assembles, not a `.global` directive, and the boot entry `lean_kernel_main`, once exported, must call `bootAndInitialisePlatform` in its own body (`boot_entry_binding_failures`) — vacuous until SM10.1 writes it, decisive after; **review round 4**: the provider scan blanks every preprocessor-conditional region, follows the builder chain that reaches `.compile()` in a function reachable from `main`, and intersects with the assembled archive's object symbols when a cross build is present; **review round 5**: the boot-entry gate reads the exporting declaration's statements over the string-free view — an executed top-level call and no other kernel-state installer, the installers derived by closure over the Lean tree (`kernel_state_writers`) — where round 3 accepted an identifier occurrence; **review round 6**: the three inventories read the shared code views with strings blanked, and an `EXPECTED_UNRESOLVED` entry expires the moment the Lean tree exports it (`stale_exported`), so an export outside the import closure is a failure rather than a pass; **review round 7**: the boot entry must execute `bootAndInitialiseRPi5`, the generic entry fixed at `RPi5Platform`; the inventory includes the library root `SeLe4n.lean`; the assembly providers are read off the compile's executed chain; **review round 8**: the archive parsers accept global text (`T`) only — a data object under a function extern's name no longer resolves it (`executable_definitions`) — and the assembled sources follow the compiled builder's binding instance (`rust_code_view.binding_statement_before`), a rebound or unbound receiver counting nothing before the compile | `scripts/staged_module_allowlist.txt`, `SeLe4n.lean` | RR5.15, RR5.16 |
| ~~SM4.G residue: `bootFromPlatformWithIdleThreads` is proven correct and has no production caller, so `idleThreadEnqueuedOnCore` is never established at boot and `schedulerNoStall_smp`'s `hIdle` is discharged by hypothesis only~~ — **CLOSED v0.34.48**: the production wrapper runs `bootFromPlatformCheckedWithIdleThreads`, a thin composition over the checked boot that **enqueues** each core's idle thread (dispatching one, as `bootFromPlatformWithIdleThreads` does, would have left the predicate false and broken `queueCurrentConsistent`), and RR5.10 lifted `inferThreadState` off the boot core first so the resulting state is not re-classified `.Inactive`.  The boot queue is characterised exactly (`bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq`), so the keystone `…_chooseThreadOnCore_succeeds` takes no hypothesis beyond the boot and `…_chooseThreadOnCore_idle` pins each core's first selection; the stored idle TCB is the queued `.Ready` form and the boot state is `threadStateConsistent` (`…_threadStateConsistent`), and `PlatformConfig.wellFormed` reserves the idle slots so the fold overwrites nothing (PR #889 review)  **Review round 2 (PR #889)**: the reservation also covers every object a config entry *references* (`bootObjectReferencesReservedIdleSlot`, total over `KernelObject`) and is refused with its own diagnostic rather than as a duplicate id, and the idle objects are unreachable by user authority at all — `syscallResolveCap`, the one resolution every invoked capability passes through, refuses a capability naming a reserved idle object (`capTargetsReservedIdleObject`, `syscallResolveCap_ok_not_reserved`), so a boot CNode or a transfer that carried one yields a slot that resolves like an empty one and no `.tcbSuspend` can remove a core's only guaranteed runnable thread; **review round 3**: the binding boot installs idle threads on the binding's declared cores (`PlatformBinding.declaredCores`, `bootFromPlatformCheckedWithIdleThreadsFor`), and the RPi5 binding declares every model core (`rpi5_cores_eq_allCores`), so the all-cores theorems are the hardware boot's; **review round 4**: the reference check covers a notification's `boundTCB` and every SchedContext reference; **review round 5**: `PlatformBinding.coreCountLe` bounds the declared count by the model, `declaredCores` is the prefix with exactly `coreCount` members, and the reservation is stated model-wide — an undeclared core's idle slot is absent after the boot (`bootFromPlatformCheckedWithIdleThreadsFor_undeclared_idle_absent`), never free; **review round 6**: the reference check reads an untyped's `children` and `parent`; **review round 7**: a boot TCB is stored under its own thread id (`tcbIdentitiesMatchSlots`, the fourth `wellFormed` conjunct) and the reference check reads its `tid` — a TCB at an ordinary id carrying an idle thread's id would have let a retype dequeue the idle thread; the platform entry boots the bound config (`bindPlatformConfig`), so the binding supplies the machine configuration and the boot VSpace root; **review round 8**: the reference check reads `queuePPrev` and is pinned by constructor arity (per-kind helpers destructure every kernel object, so a new field must be classified), the sweep adding a TCB's reply references and carried capabilities, a Reply's `replyId` and `prev` and a SchedContext's `scId`; `bootSafeObjectCheck` requires all three queue links empty; the identity relation covers SchedContexts and Replies (`embeddedIdentitiesMatchSlots`); and the raw suspend seam refuses idle ids before the transition (`suspendThreadCrossCoreStep_idle_refused`) | `SeLe4n/Platform/Boot.lean` | RR5.10–RR5.14 |
| ~~`suspend_thread_inner` commits kernel state outside the kernel-entry lock~~ — **CLOSED v0.34.48** by retiring the `@[export]` (this row's own remediation offered that or a bracket; retiring removes the hazard rather than mitigating it, and matches WS-RA's treatment of the twin `syscall_dispatch_inner`).  The Lean definition stays as the single-core reference path the dispatch suite exercises; the C symbol is gone, pinned by a Tier-3 negative anchor | `SeLe4n/Platform/FFI.lean` | RR5.17 |
| ~~Two `debug_assert!` lock/vector tripwires vanish from the release image~~ — **CLOSED v0.34.48**: both are unconditional branches to `cpu::fatal_halt()`, and `build.rs`'s `release_surviving_tripwire_status` holds each to that relation on the statement-level view (a halt nested under another condition, or moved above the branch, is refused); the lock-order tripwire asks ownership (`round_lock_held_by(core)`) — a held/free flag halted every innocent core during a shootdown (PR #889 review); **review round 2**: the scanner compares the whole `if` predicate against the declared failure condition rather than looking for a token in it, so a reversed polarity (`if vbar.is_multiple_of(2048)`) is refused; **review round 6**: each tripwire is pinned with the operation it protects and `tripwire_dominates_protected_operation` requires it among the statements dominating every occurrence of that operation — a branch that halts but is deleted from its caller, nested under a dead condition or moved below the operation is refused; **review round 7**: the branch must end in `fatal_halt` (`statement_halts`), not in any divergence — a `return` hands control back to the acquire; **review round 8**: the branch must be a top-level statement of the helper or sit under a block that executes unconditionally on the image (`tripwire_branch_halts`, `unconditional_block_interior`: a bare or `unsafe` block, or one under exactly `#[cfg(target_arch = "aarch64")]`) — an exact-condition `if` nested under a further condition halted only when that condition held | `rust/sele4n-hal/src/` | RR5.18 |
| The scheduler's dispatch and the IPC rendezvous do not write `TCB.threadState`: `scheduleEffectiveOnCore` / `switchToThreadOnCore` move the current slot and the run queue and leave the TCB object alone, and no rendezvous writes a `.Blocked*`, so the full classification `threadStateConsistent` is a **boot-state theorem** (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`) and false after any core's first dispatch; the harness re-establishes it with `syncThreadStates` before checking (PR #889 review round 2).  The relation the live decisions read — `tcbSuspend` / `tcbResume` / the cross-core cancellation / the fault suspend test the field against `.Inactive` only — is `threadInactiveFlagConsistent`, proved of the boot state (`…_threadInactiveFlagConsistent`).  **Owed**: its preservation across the scheduler and IPC surfaces, or the replacement of the stored field by the inferred classification; until then no code may cite `threadStateConsistent` of a post-dispatch state | `SeLe4n/Kernel/Scheduler/Operations/Core.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` | RR7.36 |
| SM2.C-defer (verified RwLock completion) had no durable registration or closure target outside its own plan | [`docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md) | RR6.26 |
| The deployed RwLock is the CAS-retry `rw_lock.rs` while the Lean spec was tightened to strict FIFO; `QueuedRwLock`, the FIFO implementation, has zero consumers | `rust/sele4n-hal/src/lock_bridge.rs`, `rust/sele4n-hal/src/queued_rw_lock.rs` | RR6.4–RR6.10 |
| The Tier-5 oracle models the lock instead of driving it, by its own docstring | `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` | RR6.1–RR6.3 |
| `loom` and `miri` gates the RwLock plan declares mandatory are unmet — neither tool reaches the deployed lock | `rust/sele4n-hal/Cargo.toml`, `.github/workflows/` | RR6.20, RR6.21 |
| Fine-lock migration Tracks B and C: the `capTransferReceiverCnode` footprint closure and SM3.C.9's `withLockSet` wrapping of the `@[export]` bodies — 7 of the plan's 12 PRs (the remaining 3 are Track D's, in section B below) | [`docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md`](planning/SMP_FINE_LOCK_MIGRATION_PLAN.md) | RR7.7–RR7.13; the three lock domains Track C does not itself cover (`schedulerDomain`, `dynamicPipChain`, `cspaceWalkInteriorCnodes`) close in RR7.39–RR7.41 |
| ~~Six production `native_decide` uses, against a release note claiming zero~~ — **CLOSED v0.34.47**: the theorem inventories store packed keys (`SeLe4n/PackedString.lean`) and every distinctness witness is the kernel's `decide` | `SeLe4n/Kernel/Concurrency/Locks/*Inventory.lean` and siblings | RR7.6 |
| Cancellation/timeout error-frame staging, owed before the context-restore seam flips | `SeLe4n/Kernel/IPC/Operations/Timeout.lean` | RR7.14 |
| WS-RA's application-IPC-label follow-on, registered only inside a review narrative | [`docs/planning/SYSCALL_RETURN_ABI_PLAN.md`](planning/SYSCALL_RETURN_ABI_PLAN.md) | RR7.17 |
| SM7's ASID completeness gap — `asidAllocateWithShootdown` is complete and proven with no callers, and the ASIDControl/ASIDPool object family does not exist.  Registered against SM8; **SM8 closed without absorbing it** | `SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean` | RR7.20 |
| SM7.D's four SM10.1-owned deferred cache-maintenance items appear in no SM10 sub-task | [`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md`](planning/SMP_TLB_SHOOTDOWN_PLAN.md) | RR7.20 |
| SM6's tracked debt carries no explicit closure target, and its `schedContextConfigure` entry went stale after the debt closed | [`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md`](planning/SMP_CROSS_CORE_IPC_PLAN.md) | RR7.22 |
| ~~The Tier-0 grep gate banning non-IS TLBI, which the Rust HAL plan §4.4 claims exists, does not exist~~ — **CLOSED v0.34.41** as `scripts/check_tlbi_broadcast_discipline.py`, which also confines the `tlbi` mnemonic to `tlb.rs` and demotes the four local wrappers to `pub(crate)`, making §4.4's "private helpers" true structurally | `scripts/test_tier0_hygiene.sh` | RR1.9 |
| ~~No aarch64 target is compiled anywhere: 67 cfg-gated blocks, 57 `asm!` sites and all three `.S` files have zero compile coverage~~ — **CLOSED v0.34.41**; the `aarch64 Cross Build` CI job builds both profiles, verifies the `.S` sources assembled and lints the cross target.  (The 60 this row carried was a transcription of the register's 59, which counted two docstring mentions of the token; 57 is the measured figure) | `rust/`, `.github/workflows/` | RR1.1–RR1.8 |
| `numCores` is a literal `4` rather than `PlatformBinding.coreCount`, so the Sim binding's `coreCount := 1` can never shape kernel state | `SeLe4n/Kernel/Concurrency/Types.lean` | RR7.30 |

### B — owned by SM10

These cannot close before SM10 opens, because each needs the image or the
runtime seam SM10.1 produces.  WS-RR's obligation is that they are visible
here rather than only inside a phase plan.

| Debt | Where it lives | Closure target |
|------|----------------|----------------|
| The boot path does not exist: no `[[bin]]`, no aarch64 Lean object code, no `libsele4n.a`, no bare-metal runtime hosting, no `@[export] lean_kernel_main` | `rust/`, `lakefile.toml`, `SeLe4n/Platform/FFI.lean` | SM10.1.1 |
| `lean_kernel_main`'s `initialiseKernelState` install would run outside the kernel-entry lock and after the secondaries are released — the lost-commit shape | `rust/sele4n-hal/src/kernel_entry.rs`, `SeLe4n/Platform/FFI.lean` | SM10.1 (order or bracket; §3) |
| WS-RA frame delivery: the staged return frame is not delivered until the context restore goes live | `SeLe4n/Kernel/Concurrency/ContextRestoreSeam.lean` | SM10.1 (§2) |
| Fine-lock migration **Track D** — commit partitioning, which that plan seam-gates to SM10.1; the one part of the fine-lock work WS-RR cannot land | [`docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md`](planning/SMP_FINE_LOCK_MIGRATION_PLAN.md) | SM10.1, registered as a named dependency by RR6.27 |
| `UncoveredLockDomain.taintTablePerKeyStore` names SM10.1 as owner; the SM10 plan carries no sub-task for it | `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | SM10.1 — RR0.11 routes the plan-side row |
| **Eight** WS-SM phases register zero theorems in `smpInventoriedTheoremCount` — six (SM1, SM6..SM10) have no machine-checked inventory at all, and **SM0 and SM4 carry assumption ledgers** (`smpLatentInventory`, `smpRetiredInventory`) which `smpPhaseTheoremCount` excludes by design, leaving their own theorem catalogues unmeasured.  Only SM2, SM3 and SM5 contribute to the 903 | `SeLe4n/Kernel/Concurrency/PhaseTheoremManifest.lean` | SM10.3.13 |
| Hardware-validation scripts SM10.3.14–SM10.3.20 and the SM10.1.1 image build, each a runnable procedure `docs/HARDWARE_TESTING.md` documents with no script | `scripts/` | SM10.3, SM10.1.1 |
| Tier-4 acceptance gates have never executed: they need the bootable image, so `SMP_RELEASE_CLOSURE_PLAN.md` §2's "acceptance gates for SM0..SM9 green" is **unmet**, not merely unverified | `scripts/test_tier4_smp_bootcheck.sh` | SM10.1, immediately after D1 |
| SM10.6.2 archives the WS-RC artefacts; its still-open items (R7, R14) migrate here rather than into the archive | `docs/audits/` | SM10.6.2 |
| **SM10's sub-phases were lettered, and the letters were not execution order** — SM10.3.7 and SM10.3.10 consume the bootable image, and the version bump and tag ran before it existed | Closed at **v0.34.36**: re-sequenced into numbered sub-phases SM10.1..SM10.6 with the image build first and the tag last, and the old boot-path phase split from the validation that consumes it.  Old letters are preserved in historical prose and mapped in the plan's §3 table | **CLOSED** — no longer RR7.5's; found by review on PR #882 (v0.34.27), fixed at v0.34.36 |

### C — deferrals with no pre-v1.0.0 owner

Each row states why it may wait.  "Registered" is not "ignored": a row here
constrains what v1.0.0 may claim, and RR8.4's hand-off check reads this table.

| Debt | Why it may wait | Owner / closure target |
|------|-----------------|------------------------|
| **WS-SL** — the scheduler liveness trace step relation (`stepPrecondition` / `stepPost` / `ValidTrace`) is `bootCoreId`-pinned, so no `ValidTrace` exhibits a step on a secondary core; and `hBandProgress` is an externalized deployment hypothesis whose FIFO/bucket-rotation composition was never built | Model completeness, not soundness: the per-core liveness *predicates* were lifted by SM5.J, and the capstones state their hypothesis explicitly.  v1.0.0 must therefore not claim unconditional SMP starvation-freedom | **WS-SL**, post-v1.0.0 (section below) |
| WS-RC **R7** — CDT `descendantsOf` fuel-sufficiency proofs; `descendantsOf_fuel_sufficient` proves only `edges.length ≥ 0` | Proof hygiene: CDT operations are sound under the fuel-bound discipline; the sufficiency theorem is defence in depth | post-v1.0.0 hardening |
| WS-RC **R14** — the v1.x backlog the WS-RC plan deferred | Explicitly scoped out of v1.0 closure by that plan | post-v1.0.0 |
| WS-RC R4's two deliberate follow-on type-level promotions, registered only inside [`docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md`](planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md), a plan marked COMPLETE | Both are strengthenings of an already-sound surface | post-v1.0.0 hardening; SM10.6.2 archives the plan, so the items must not travel with it |
| `REPLY_OBJECTS_COMPLETION_PLAN.md`'s deferred follow-up item 4 (reply-object lock stress) named a tracking home that carries no entry for it | The plan it named is a live plan; the item simply never arrived there | post-v1.0.0; the reply-object plan's status header now points here |
| Two SM2.C debts raised by SM8.D's review rounds were assigned to a phase already CLOSED and appear in no live plan | Both are completeness strengthenings of the RwLock surface RR6 is already reworking | RR6 — if RR6 does not absorb them, RR6.26 re-registers them here |
| The v0.32.148 queued-lock closure — [`docs/planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md`](planning/SMP_PANIC_HANG_REMEDIATION_PLAN.md)'s SM2.E remediation, whose header and two-thirds of its body still describe the MCS queue that cut deleted — was recorded in an unrelated plan and never reached this file | Bookkeeping, not behaviour: the closure itself is real and in the tree, and the shipped artefact is a ticket lock | recorded here by RR0.9; the plan-side prose is SM10.2's work-list (register §7 row 33) |
| Idle TCBs carry `ObjId.sentinel` cspace/vspace roots | The idle thread never faults a user mapping; it becomes live work when RR5.14 repoints the production boot wrapper at the idle-installing entry, and that row must not close over it | RR5.14 must either give idle TCBs real roots or re-register this row |
| SM9.D.11 — taint propagation at capability transfer shipped as a scope reduction, leaving `capabilityBadgeChannel_out_of_scope`: a registered false-negative channel in the causal detector | A false *negative* in a detector, not a policy bypass | post-v1.0.0; RR0.11 routes the plan-side row |
| The SM8 class-C follow-on: the CC-1 capacity figure is stated in two places rather than single-sourced | Cosmetic duplication of a bound both sites agree on | post-v1.0.0 |
| ARM CCA + MPAM hardware partition isolation | Targets a successor SoC; not RPi5 | [`docs/planning/HARDWARE_PARTITION_ISOLATION_PLAN.md`](planning/HARDWARE_PARTITION_ISOLATION_PLAN.md), unscheduled |
| **R-ABI-L6** — cross-crate duplication of `MAX_METHOD_COUNT`, `MAX_PRIORITY`, `MAX_DOMAIN` and `MAX_SERVICE_MESSAGE_SIZE` between `sele4n-abi` (limits) and `sele4n-types` (identifiers + error enums) | Duplication, not divergence — the values agree and the ABI conformance tests compare them; the risk is that a future edit changes one copy | post-v1.0.0 hardening.  Recorded in [`docs/AUDIT_NOTES.md`](AUDIT_NOTES.md) §R-ABI-L6, which declared itself untracked and is the one v0.29.0 R-ABI item still open — L3, L4, L5, L7 and L8 record settled decisions, not deferrals.  Found during the RR0 review round (v0.34.31), not by the pre-SM10 audit |
| `AsidPool.allocate`'s rollover scan is quadratic: `List.range (maxAsidValue - 1)` filtered by `List` membership in `activeAsids`, so a rollover against a nearly full ASID space walks up to 65,535 × 65,535 comparisons — the compiled fail-closed regression (`tests/AsidPoolSuite.lean` T05) takes ~38 s, which is also what a saturated rollover would cost the live kernel (test-performance audit, v0.34.47) | Correct and proven (`allocate_result_fresh`, `allocate_preserves_wellFormed`); rollover against a saturated space is not on any live path before SM10.1, and the fix is a representation change under existing proofs (a sorted or bitmap `activeAsids`, or the `activeCount` early exit) rather than a semantic one | post-v1.0.0 performance pass; the test keeps exercising the real scan until then |
| The 32 in-source post-1.0 hardening candidates enumerated below | Each is a strengthening of a surface that is already correct; none is a soundness gap | post-v1.0.0 hardening, listed individually so none ages out with its comment |
| `crossSubsystemFieldSets` lists 11 field-sets while `crossSubsystemInvariant` has **12** conjuncts: `untypedRegionsDisjoint` was appended without a matching `_fields` entry, so the pairwise disjointness analysis and every frame lemma derived from it cover 11 of the 12 | Incompleteness, not unsoundness — the uncovered predicate simply gets no frame lemma, so proofs needing it establish it directly; nothing false is proved | post-v1.0.0; closing it means adding `untypedRegionsDisjoint_fields` and redoing the analysis over C(12,2) = 66 pairs.  Found during the RR0 review round (v0.34.27), not by the pre-SM10 audit |

#### C.1 — The 32 in-source post-1.0 hardening candidates

Each of these stated in its own docstring that "no currently-active plan file
tracks it".  That sentence made the deferral self-describing and unfindable at
once: a reader could only meet it by opening the file it lived in.  They are
enumerated here, and the source comments now point at this table instead of
declaring themselves untracked.  Line numbers are the `v0.34.26` positions and
will drift; the identifier beside each is stable.

| # | Site | Deferred item |
|---|------|---------------|
| 1 | `SeLe4n/Platform/Boot.lean` (`applyGicTimerSetup`) | TLB/ASID maintenance for HAL-parity boot |
| 2 | `SeLe4n/Platform/Boot.lean` (`bootFromPlatform`) | Minimum-configuration validation (≥ 1 initial thread, valid scheduler state) |
| 3 | `SeLe4n/Platform/Boot.lean` (bundle bridge) | Builder operations preserve only 4 of the 12 `proofLayerInvariantBundle` components for general configs |
| 4 | `SeLe4n/Platform/RPi5/MmioAdapter.lean` (P-L2) | `readCString` fuel-exhaustion return-type upgrade |
| 5 | `SeLe4n/Platform/RPi5/MmioAdapter.lean` (P-L4) | `extractPeripherals` beyond 2-level DTB nesting |
| 6 | `SeLe4n/Platform/RPi5/MmioAdapter.lean` (P-L5) | Multi-core extension of the MMIO write-sequence atomicity argument |
| 7 | `SeLe4n/Platform/RPi5/MmioAdapter.lean` (P-L11) | FFI `opaque BaseIO` contract bridging |
| 8 | `SeLe4n/Model/Builder.lean` (AF5-F) | Anonymous invariant tuples → named structures (100+ destructuring proof sites) |
| 9 | `SeLe4n/Model/Object/Structures.lean` (`descendantsOf_fuel_sufficient`) | Substantive CDT fuel-sufficiency proof; today it proves `edges.length ≥ 0` |
| 10 | `SeLe4n/Model/Object/Structures.lean` (`CdtChildReachable`) | Transitive-closure bridge from reachability depth to BFS fuel bounds |
| 11 | `SeLe4n/Kernel/Service/Invariant/Acyclicity.lean` | Section-scope split of the acyclicity proof idiom |
| 12 | `SeLe4n/Kernel/Service/Operations.lean` (`serviceBfsFuel`) | Rename to match the DFS-equivalent search it implements (~77 call sites) |
| 13 | `SeLe4n/Kernel/IPC/Invariant/Defs.lean` (`donationChainAcyclic`) | Formal bridge from donation edges to `blockingAcyclic` for cycles of length > 2 |
| 14 | `SeLe4n/Kernel/FrozenOps/Core.lean` | Integration of the frozen-state monad into the production API layer |
| 15 | `SeLe4n/Kernel/FrozenOps/Commutativity.lean` | Promotion of the frozen commutativity proofs into the production chain |
| 16 | `SeLe4n/Kernel/FrozenOps/Invariant.lean` | Promotion of the frozen invariant layer into the production chain |
| 17 | `SeLe4n/Kernel/FrozenOps/Operations.lean` | Promotion of the frozen operations into the production chain |
| 18 | `SeLe4n/Kernel/RobinHood/Bridge.lean` (DS-L2) | `Except`-returning `insertNoResize` (~50 call sites) |
| 19 | `SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean` (`retypeFromUntyped_atomicity_under_sequential_semantics`) | Re-establishing retype atomicity under SMP/preemption on real hardware |
| 20 | `SeLe4n/Kernel/CrossSubsystem.lean` (`collectQueueMembers_fuel_sufficiency_documented`) | `QueueNextPath` → `queueNext` traversal bridge (the IPC subsystem's sole remaining TPI-DOC item) |
| 21 | `SeLe4n/Kernel/CrossSubsystem.lean` (`crossSubsystemInvariant`) | Compositional proof that all **12** predicates hold under arbitrary interleaving of all 34 operations |
| 22 | `SeLe4n/Kernel/Capability/Invariant/Defs.lean` (AF5-F) | Right-associative `∧` chains → named structure |
| 23 | `SeLe4n/Kernel/API.lean` (`resolveExtraCapsDetailed_empty`) | Fold-level induction generalising swap-invariance beyond the empty-input base case |
| 24 | `SeLe4n/Kernel/Architecture/Invariant.lean` (`retypeFromUntyped` disjointness, ~L1800) | Full-coverage proof for transitive multi-level untyped nesting — a richer invariant (root-restricted disjointness or transitive-ancestor exclusion) |
| 25 | `SeLe4n/Kernel/Architecture/Invariant.lean` (`retypeFromUntyped_objectOfKernelType_preserves_untypedRegionsDisjoint`, ~L1884) | The `.untyped` → `.untyped` retype target, the one case the six allowed object types do not exhaust |
| 26 | `SeLe4n/Kernel/Architecture/Invariant.lean` (zero-`regionBase` child, ~L1952) | Full-coverage proof for the zero-`regionBase` child case |
| 27 | `SeLe4n/Kernel/CrossSubsystem.lean` (untyped ancestry, ~L466) | Transitive ancestor/descendant tracking via a CDT-style closure — the standalone model-refinement effort rows 24–26 all reduce to |
| 28 | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` (`blockingChain`) | Formal blocking-cycle detection and removal; today PIP propagation stops at the cycle boundary, leaving stale boosts (conservative — over-promotion, never inversion) |
| 29 | `SeLe4n/Kernel/RobinHood/Bridge.lean` (DS-L5) | Restructuring the 400K–800K-heartbeat `Lookup.lean` / `Preservation.lean` proofs into smaller lemma units |
| 30 | `SeLe4n/Kernel/RobinHood/Bridge.lean` (DS-M04) | Entry-wise correctness proof yielding `LawfulBEq (RHTable α β)`; consumers must supply `[LawfulBEq β]` at the call site until it exists |
| 31 | `SeLe4n/Kernel/Capability/Operations.lean` (`revokeCdtTransactionalTraversal`) | The monotonicity lemma witnessing that the fold never sets `firstFailure` to `some`; the completion test is what keeps the defensive branch honest meanwhile |
| 32 | `SeLe4n/Kernel/Capability/Operations.lean` (C-L3, `ipcTransferSingleCap`) | A sender-rights field on `CdtEdgeKind`, so a transferred capability's CDT edge records the rights the sender held; closing it moves the 14 CDT-edge composition proofs |

**None is a soundness gap.**  Every one strengthens a surface that is already
correct — a tautological witness replaced by a substantive proof, a fuel bound
made structural, a tuple given a name, a validated-elsewhere precondition
internalised.  That is why they may wait; it is not why they may be forgotten.


## WS-SL — scheduler liveness completion

**Owner**: Scheduler subsystem. **Closure target**: post-v1.0.0. Registered as
a row in table C above; the work list is here because it has no plan file.

SM5.J lifted the per-core liveness *predicates* at v0.31.64 —
`eventuallyExitsOnCore`, `higherBandExhaustedOnCore`,
`CanonicalDeploymentProgressOnCore`, `WCRTHypothesesOnCore`, `selectedAtOnCore`
and siblings all read `currentOnCore c` / `runQueueOnCore c`. The trace model
underneath them was not lifted. What remains, in execution order:

| # | Item | Where |
|---|------|-------|
| SL1 | Lift the trace step relation: `stepPrecondition`, `stepPost` and `ValidTrace` read `bootCoreId`, so no `ValidTrace` exhibits a step taken on a secondary core | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` |
| SL2 | Construct `hBandProgress` rather than externalising it — the FIFO/bucket-rotation composition that would discharge the band-progress obligation | `SeLe4n/Kernel/Scheduler/Liveness/Yield.lean` |
| SL3 | Restate the liveness capstones over the lifted traces, so the SMP starvation-freedom result is a statement about multi-core executions | `SeLe4n/Kernel/Scheduler/Operations/PerCoreWcrt.lean` |

None of the three is a soundness defect: the per-core forms are correct and the
capstones state `hBandProgress` explicitly rather than hiding it. The cost is
that v1.0.0's liveness claim is **conditional** and must be stated that way.
**SM10 may not claim unconditional SMP starvation-freedom.**

## Workstream registry

The workstream families this project has run, with the versions each spans.
**This table is machine-read**: `scripts/check_identifier_naming.py` derives
its family grammar from the bold workstream name in each row of this table —
the rows, not this paragraph or any other prose in the file — rather than
from a hand-kept list, because a hand-kept list was the single largest source
of holes in that gate. A workstream added as a row here is covered by the
naming gate without anyone remembering to update it; a workstream that is only
mentioned in prose is not.

Scope, findings and evidence for any of these are in
[`CHANGELOG.md`](../CHANGELOG.md) at the versions named.

| Workstream | Versions |
|------------|----------|
| **WS-RR** | v0.34.26– |
| **WS-SL** | v0.34.26– (closure post-v1.0.0) |
| **WS-DT** | v0.31.157–v0.34.43 |
| **WS-SM** | v0.31.2– |
| **WS-RA** | v0.33.37–v0.33.38 |
| **WS-RC** | v0.30.11–v0.31.2 |
| **WS-AN** | v0.30.6–v0.30.11 |
| **WS-AM** | v0.30.0 |
| **WS-AK** | v0.29.1–v0.30.6 |
| **WS-AL** | v0.29.13–v0.29.14 |
| **WS-AJ** | v0.28.1–v0.29.0 |
| **WS-AI** | v0.27.7–v0.28.0 |
| **WS-AH** | v0.27.2–v0.27.6 |
| **WS-AG** | v0.26.0–v0.27.1 |
| **WS-AF** | v0.25.22–v0.25.27 |
| **WS-AE** | v0.25.15–v0.25.21 |
| **WS-AD** | v0.25.11–v0.25.14 |
| **WS-AC** | v0.25.3–v0.25.10 |
| **WS-AB** | v0.24.0–v0.25.5 |
| **WS-AA** | v0.23.21–v0.23.x |
| **WS-Z** | v0.23.0–v0.23.21 |
| **WS-Y** | v0.22.22–v0.22.x |
| **WS-X** | v0.22.17–v0.22.21 |
| **WS-W** | v0.22.10–v0.22.16 |
| **WS-V** | v0.21.8–v0.22.9 |
| **WS-U** | v0.21.0–v0.21.7 |
| **WS-T** | v0.20.0–v0.20.7 |
| **WS-S** | v0.19.0–v0.19.6 |
| **WS-R** | v0.18.0–v0.18.7 |
| **WS-Q** | v0.17.7–v0.17.14 |
| **WS-N** | v0.17.0–v0.17.5 |
| **WS-M** | v0.16.14–v0.17.0 |
| **WS-M2** | v0.16.15 |
| **WS-L** | v0.16.9–v0.16.13 |
| **WS-K-H** | v0.16.8 |
| **WS-K-G** | v0.16.7 |
| **WS-K-F** | v0.16.5 |
| **WS-K-E** | v0.16.4 |
| **WS-K-D** | v0.16.3 |
| **WS-K-C** | v0.16.2 |
| **WS-K-B** | v0.16.1 |
| **WS-K-A** | v0.16.0 |
| **WS-J1-F** | v0.15.10 |
| **WS-J1-E** | v0.15.9 |
| **WS-J1-D** | v0.15.8 |
| **WS-J1-C** | v0.15.6; refinements v0.15.7 |
| **WS-J1-B** | v0.15.5 |
| **WS-J1-A** | v0.15.4 |
| **WS-I1** | v0.15.0 |
| **WS-F8** | v0.14.9 |
| **WS-F5** | v0.14.9 |
| **WS-H16** | v0.14.8 |
| **WS-H15** | v0.14.7 |
| **WS-H14** | v0.14.6 |
| **WS-H13** | v0.14.4 |
| **WS-H11** | v0.13.7 |
| **WS-H10** | v0.13.6 |
| **WS-H9** | v0.13.4 |
| **WS-H8** | v0.13.2 |
| **WS-H7** | v0.12.21 |
| **WS-H6** | v0.13.1 |
| **WS-H5** | v0.12.19 |
| **WS-H4** | v0.12.18 |
| **WS-H3** | v0.12.17 |
| **WS-H2** | v0.12.16 |
| **WS-H1** | v0.12.16 |
| **WS-G** | v0.12.6-v0.12.15 |
| **WS-E** | v0.11.0-v0.11.6 |
| **WS-D** | v0.11.0 |
| **WS-C** | v0.9.32 |
| **WS-B** | v0.9.0 |

Prior audits (v0.8.0–v0.9.32), milestone closeouts, completed workstream plans
and legacy GitBook chapters are archived in
[`dev_history/`](dev_history/README.md), including the audit plans that scoped
WS-F through WS-N.
