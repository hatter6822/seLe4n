# seLe4n Development Guide

## 1) Purpose

This guide is the day-to-day operating manual for contributors to seLe4n — a
production-oriented microkernel written in Lean 4 with machine-checked proofs.

It is aligned to the **current project state**:

- **active workstream:** **WS-SM (SMP multi-core completion) IN FLIGHT** (v0.31.2 → v1.0.0; closes with a bootable verified SMP microkernel on Raspberry Pi 5).  Interleaved: **WS-RA (Syscall Return ABI) core LANDED (v0.33.37)** — the kernel returns the full seL4 ARM64 frame end to end (`x0` = badge/primary result at full 64-bit width; `x1` = `MessageInfo` whose label carries the error at `discriminant + 1`, so label 0 = success and no error aliases it; `x2`–`x5` = message registers), the bit-63 `encodeOk`/`encodeError` protocol and the vestigial `syscall_dispatch_inner` export are deleted with Tier-3 negative anchors, `syscallReturnShape` is a **total** function (a new syscall cannot omit its return shape), the five value-returning syscalls stage real frames at their dispatch arms (`.notificationWait` the signalled badge, `.receive`/`.replyRecv` the delivered message, `.serviceQuery` the resolved service id it previously discarded), the frame crosses the FFI as a per-core mailbox + outcome tag with `trap.rs` restoring all six registers, and `SYSCALL_ABI_VERSION = 2` is pinned on all three sides; completed at v0.33.38 with RA.B.5b (the blocked orderings staged end to end by the unblocking arms — eleven staging sites, `blockedReturn_staged_in_waiter_frame`, five two-core suite scenarios) and RA.B.8 (the per-arm shape-coherence family); SM10.E owes only frame delivery + cancellation error frames — SM9 is unblocked (plan: [`docs/planning/SYSCALL_RETURN_ABI_PLAN.md`](planning/SYSCALL_RETURN_ABI_PLAN.md)).  **WS-SM SM9.A the audit trail reader LANDED** — SM8.C.8 mounted a durable, bounded, fail-closed declassification trail that nothing could read, so a deployment performing 256 authorized downgrades stopped being able to declassify at all until reboot; SM9.A is the read side (production leaf `InformationFlow/AuditRead.lean`, `SyscallId.auditRead` 31 / `.auditDrain` 32, count 31 → 33, both `.word`-shaped so WS-RA carries the computed word back rather than the caller's preloaded `x0`).  Authority is the dedicated `CapTarget.auditTrail` rather than the `.read`/`.write` right alone, since `syscallLookupCap` never constrains `cap.target` and a rights-only gate would repeat the v0.32.97 confused-deputy class; drain requires dominance over every recorded source (a prefix drain reveals the *positions* of hidden entries), the gate is configuration-derived rather than computed from surviving rows, and `SystemState.declassificationAuditEpoch` lands first because `timestamp := log.length` reuses a timestamp after any prefix removal.  An unconfigured deployment has no audit reader at all (plan: [`docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md) §4 SM9.A).  Preceded by **SM8.C per-core declassification audit COMPLETE (landed v0.33.7; completion cut v0.33.8 — SM8.C.8 mounts the audit trail in `SystemState`, bounded at 256 entries and **fail-closed** at the bound, as the 16th `proofLayerInvariantBundle` conjunct; SM8.C.9 makes `.declassify` a live syscall (`SyscallId` 30, count 31) whose only state effect is one attributed audit entry, with the unchecked dispatch failing closed and the declassification policy defaulting to deny-all).  Current sub-phase: **SM8.E tests + closure LANDED (v0.33.23) — WS-SM phase SM8 is CLOSED**: the SM8 headline surface anchored in `tests/SmpSurfaceAnchors.lean` across all five sub-phases (SM8.C had none there at all, and two theorems the plan's own "what SM8 proves" list names were unanchored); the phase-level golden trace `tests/fixtures/smp_information_flow.expected`, computed from the live projection, transitions and inventories — *what an observer at `(core, label)` sees*, which the SM8.C and SM8.D fixtures do not cover; and the SM3 two-phase-locking bracket `withLockSet` promoted into the canonical `enforcementBoundary` (39 -> 40; 12 policy-gated, 24 capability-only, 4 read-only), appended last so the per-core boundary stays the identical 55 it already was, with `enforcementBoundaryPerCore_entry_is_new` retired in favour of the exactly-once count a duplicate would break.  Along the way: `KernelOperation.all` + `mem_all` replace three 35-element literals whose counts could not have noticed a thirty-sixth constructor, and `declassification_refusal_is_unrecorded`'s `rfl` conjunct is replaced by the structural fact behind it — `Kernel`'s error arm carries no post-state, so the registered audit gap cannot be closed by "a producer on the error arms" and is re-scoped to SM9.  Preceded by **SM8.D information flow under fine locks LANDED (v0.33.9, review cuts v0.33.10, v0.33.12–v0.33.22, completion cut v0.33.11 — the observer's view proven to *factor through* lock erasure (`projectKernelObject_setLock`), reader multiplicity and writer exclusion proven unobservable (the latter for the blocked acquirer itself, refuting the plan's D.3 row rather than reinstating the field), the CC-5 lock-contention timing channel **bounded** (`lockContention_delay_bounded` → alphabet → trace capacity, in the shape SM8.B.9 gave CC-1), Biba integrity under per-core locks in *both* integrity directions, and the 2PL-bracketed live syscall entry's witness with the fail-closed statement sharpened from state equality to `lockWritesOnly`; the v0.33.10 review cut re-keying the CC-5 observation to the acquisition that made it, supplying the missing pacing factor, making the `FairTrace` premise and the placeholder release budget explicit, consuming the declared-footprint hypothesis, and discharging the success path end to end; the v0.33.11 completion cut generalising the SM2.C liveness chain to an arbitrary access mode — `RwLock.lean` §D-3.10, where the writer proof's mode argument becomes the wait queue's own `Nodup` — so the CC-5 bound covers a blocked **reader** on the same terms and proves it admitted *as a reader*, closing SM8.D's last registered debt; the v0.33.12 review cut binding the declared lock-set footprint to the entry's own register decode, parameterizing the bracket's non-interference by the core it runs on, requiring distinct enqueue steps in a contention run, and making the 2PL acquire phase's grant condition a checked fact in both directions)**.  Preceded by **SM8.A per-core observable state COMPLETE (v0.33.3, review cut v0.33.4; landed v0.33.2) — SM8 opens**: the SMP information-flow *observer* is now the pair `(core, clearance)`, and the state it sees is `ObservableState.onCore` (new staged module `InformationFlow/ObservableStatePerCore.lean`, staged-only 54 → 55; SM8.B's `crossCoreNonInterference` is the first consumer).  At the boot core the per-core view is *definitionally* the live single-core `projectState`, so the existing non-interference surface does not move.  The thirteen `ObservableState` components partition into seven shared and six per-core, and `ObservableState.ext_fragments` makes the partition **total** — a fourteenth field registered in neither fragment is a compile error, so the plan's "per-core projection missing a field" risk is structural rather than procedural.  `onCore_perCore_independence` bounds the read set *without mentioning the boot core* (which the SM4.D congruence cannot do, since its hypothesis is equality of the whole global projection and that reads the boot core's slots); `onCore_label_monotone` proves visibility monotone in clearance; `onCore_decidable` decides a strictly weaker slice, with the strictness proved rather than asserted.  112 runtime assertions across 13 groups in `tests/SmpInformationFlowSuite.lean` (fixture carrying a CNode and a configured memory-ownership model so slot redaction and address observability are non-vacuous), anchors verified complete by set difference against the module's 104 declarations, Tier-2 + Tier-3 wired.  **SM8.B per-core NI proofs LANDED (v0.33.5)**: two new staged modules (`InformationFlow/NonInterferencePerCore.lean`, `InformationFlow/CovertChannelPerCore.lean`; staged-only 55 → 57) prove that transitions leave the SM8.A observer alone.  `crossCoreNonInterference` (plan Thm 3.3.1) is proven from *frame* premises — `observableSlotsConfinedToCore` (every per-core slot outside the writing core unchanged, register banks included) plus `sharedViewUnchanged` — rather than from the plan's serializability sketch, which is unavailable while SM3.C.9 defers the fine locks at the `@[export]` bodies; `crossCoreNonInterference_of_disjoint_lockSet` supplies the plan's argument as a bridge for when they land.  `nonInterference_perCore` lifts the release-grade single-core theorem to `lowEquivalent_smp`, and all **35** per-operation variants ship — for **31** of them the confinement premise is *derived* rather than assumed, which discharges the SM4.C/SM4.D `hOtherIdle` obligation for those operations; the 4 catch-all constructors provably cannot derive it (the live cross-core dispatch writes remote cores), so they take it explicitly, with `perCoreConfinementDerived_count` pinning the split and a load-bearing negative in the suite.  `withLockSet_preserves_projection` is **unconditional**, which required erasing each object's `lock : RwLockState` from the projection: the field is three lists of `CoreId`s, so it re-opened through another field — and on every object kind — the per-thread *placement* channel SM5.B closed by stripping `TCB.cpuAffinity`.  With the field erased, CC-5 is a hardware timing channel only.  The seven accepted covert channels CC-1…CC-7 are data (`acceptedCovertChannelsPerCore`) with per-channel witness theorems; `enforcementBoundaryPerCore` stands at 39; `endpointPolicyRestricted_perCore` and the release bridge run both ways; `crossCoreLeakage_bounded` is an `↔`.  167 runtime assertions across 24 groups.  **SM8.B follow-up cut LANDED (v0.33.5)**: a self-audit found `crossCoreNonInterference` had no instantiation at a transition that writes a *remote* core — all thirty-five lifts are boot-core-confined — so the new staged module `InformationFlow/NonInterferenceCrossCore.lean` (staged 57 → 58) supplies six, over set-of-cores write sets computed from the pre-state (an endpoint call writes the receiver's home core **and** the caller's own) on a reusable home-core frame layer.  Strictly stronger than SM6's per-core NI on the per-core half: those need the woken thread non-observable, these hold for a fully visible one.  Also closed: the `endpointFlowCheck_state_independent` tautology (`X = X` by `rfl`, cited in five prose sites) replaced by the genuinely state-and-core-dependent `endpointFlowCheckAtCore` and three real theorems about it; two over-claiming docstrings; `perCoreConfinementDerived`'s wildcard; both theorem-name tables now compile-time-validated by `niName!`; and the axiom sweep replaced by the map-driven, Tier-3-run `scripts/check_module_axioms.py` (the old regex missed three `@[simp] theorem` declarations).  Suite 186 assertions / 28 groups.  **v0.33.5 audit cut**: the live `.call` arm is `endpointCallCrossCoreDispatch` = transition + donation + PIP chain walk, and the chain walk re-buckets on each boosted server's *home* core — so the transition's write set did not bound the live arm, though a docstring said it did; closed with `pipChainWriteSet` (fuel induction), `applyCallDonation_confinedToCores`, and the union `endpointCallLiveWriteSet`.  Also: both marquee write sets had been tested only in their degenerate branches (no waiter / no receiver), so the flagship two-core case had zero runtime coverage — closed with a real rendezvous fixture.  Suite 193 assertions / 29 groups.  **v0.33.5**: the composed cross-core cancellation closed — its blocker was that only a `scheduler` frame existed for the SM6.E teardown, while per-core confinement reads the register banks too; `cancelIpcBlocking_machine_eq` (with a new leaf layer for `restoreToReady`, the reply-link legs and both queue sweeps) unblocks `cancelIpcBlockingOnCore_confinedToCores` and its NI instantiation, taking coverage to 7 cross-core transitions.  Suite 198 assertions / 30 groups.  **SM8.C per-core declassification audit LANDED (v0.33.7)**: one new staged module (`InformationFlow/DeclassificationPerCore.lean`; staged-only 58 → 59).  The plan reads as though the audit trail existed and needed a core added; it did not — nothing in the tree constructed a `DeclassificationEvent`, so `declassifyStore` gated and stored while the record's docstring described a writer that was never written.  Per the implement-the-improvement rule the producer was built: `declassifyStoreOnCore` runs the same gate, threads an append-only log and appends exactly one event per authorized downgrade, with the state effect *provably identical* to the unaudited gate (`declassifyStoreOnCore_ok_inv`), so `declassifyStore_NI` and the enforcement soundness theorems carry over untouched.  `originatingCore : CoreId` is **undefaulted** — a default would attribute every event to the boot core while compiling everywhere — and `authorizationBasis` is typed, so the kernel can check its own records while `render` keeps the strings an external consumer reads byte-identical.  `declassifyStoreFromCore` *reads* the source domain off the subject the executing core is running and fails closed on an idle core, making `declassifyStoreFromCore_event_attributable` unconditional; `declassifyStoreOnCore_admits_unattributable` is the negative that makes the wrapper load-bearing.  `declassificationAuditLog_partitions_by_core` makes the per-core views an exact partition of one global log, and `crossCoreChain_not_within_one_view` is the theorem that decides that design: a declassification chain crossing cores lives in **no** single core's view, so one log per core — the natural SMP implementation — would lose the composed downgrade.  Eight cross-core rules ship as data with dependently-typed evidence (laundering over a *well-formed* policy plus the decidable `chainLaunders`; the endpoint rule consuming SM8.B's `endpointFlowCheck_restricted_subset_perCore`; `authorizationBasis_perCore`; core-is-audit-not-authority).  The same cut closes SM8.B's registered debt (a): WS-E5/H-04 specified `EndpointFlowPolicy` and nothing carried one, so `LabelingContext.endpointPolicy` is now read by the four endpoint-keyed gates through `endpointFlowGate`, which **conjoins** the global lattice check with the endpoint's override — `endpointFlowGate_implies_securityFlowsTo` takes no hypothesis, so V6-G's `endpointPolicyRestricted` is structural and a misconfigured override cannot widen anything.  Suite 316 → 360 assertions (§6.1–§6.8), every group with a load-bearing negative; trace byte-identical; axiom-clean.  Registered follow-on: refused declassifications are not audited (the V6-H record has no outcome field), which is a monitoring gap rather than an enforcement one.  Prior: **SM7 CLOSED at v0.33.0** (SM7.F.5 access-time TLB fill); **SM7.F.3 round-generation-tagged descriptors LANDED (v0.32.105) — SM7.F CLOSED**: a shootdown round's deferred catch-up now drains only the rounds its *own* commit opened, so a concurrently-committed round's freshly-posted descriptors survive for its own catch-up instead of being swallowed (the SM7.B v0.32.79 model-fidelity debt).  Descriptors carry `generation : Nat`, `TlbShootdownState` a monotone `roundGeneration`, and the live seam recovers its window from the same `(pre, post)` diff it already uses; every landed SM7.A/B round theorem carries over through the exactness bridges, since under round serialisation the window drain **is** the whole-queue drain.  The Rust mirror closed a **High**-severity (once bootable) hazard: with a Boolean acknowledgment vector, a `.tlbShootdownReq` SGI left pending by an earlier round could be delivered inside a later round's `reset → publish` window, retire the *previous* round's operands and satisfy the new round's wait with that target's TLB still stale — an under-invalidation.  Acknowledgments now carry the generation they discharged (`acked_gen`, `fetch_max`), the handler latches it before any TLB work, and the reset is gone entirely along with the window it lived in.  **Audit cut (v0.32.110)**: the 12th `proofLayerInvariantBundle` conjunct (`pendingBounded`) is now carried across the live catch-up — SM7.B proved it for the single-view handler, but v0.32.81 swapped the live fold to the per-core handler and v0.32.105 restricted it to the round window, leaving the transition `completeShootdownRounds` runs without a bound proof; the capacity-bound justification ("at most one round's descriptors in flight per target") was false and corrected, since a single multi-ASID retype commit opens several rounds; and `test_rust.sh` now aggregates per-binary results instead of printing the log tail, which surfaced two never-compiled ```ignore doctests and, through them, that all four print macros were `#[macro_export]`ed while expanding to a `pub(crate)` seam.  Prior: **SM7.E tests + fixtures LANDED (v0.32.103)** — the SM7 closure phase: `tests/SmpTlbShootdownSuite.lean` grows to 35 runtime scenario groups (272 assertions) with the four-core concurrent-unmap storm (§6), the cross-cluster mock (§7) and the `[smp-tlb-shootdown]` golden trace fixture (§8); `tests/SmpCacheMaintenanceSuite.lean` §3.15 adds the instruction-cache half of the cross-cluster mock; `scripts/test_qemu_smp_shootdown_stress.sh` reserves the Tier-4 contention slot; and `PerCoreTlbModel.lean` gains the per-core handler commutativity theorem the storm’s order-independence claim rests on (`handleTlbShootdownReqOnCorePerCore_comm` — SM7.B had proven it only for the single-view handler, while the live catch-up fold runs the per-core one).  Prior: **SM7.D cache maintenance broadcast CLOSED — LANDED (v0.32.94), closure cut (v0.32.95), residual closure (v0.32.96), SECURITY fixes (v0.32.97, v0.32.100)** — v0.32.100 makes the re-type clean its scrubbed extent to the Point of Unification before invalidating the instruction caches (the `IC IALLUIS` alone guaranteed the next fetch would re-read the previous owner's code from the stale PoU copy), and v0.32.97 binds VSpace syscall capabilities to their operand address space, closing a High-severity confused deputy in which a thread holding a writable capability to any object could act on any address space — the residual closure adds the `.vspaceUnifyInstruction` code-publication syscall (`SyscallId` 29, count 30), a **pure cache** transition that lets a subject which *writes* instructions publish them (the dual of the destroy-side maintenance, and previously unfulfillable by user code), and corrects the v0.32.95 emission ledger from a single-operand join to a coverage preorder over a list (`iallu` is not a lattice top — it issues no `DC CVAU`, so collapsing a `unifyPage` into it would drop a required clean-to-PoU); the closure cut fixes the `IC IVAU` page-vs-line granularity (64 instructions per page operand) and adds the emission ledger `SystemState.pendingIcacheMaintenance` so the runtime emits the model's exact operand (targeted page loop on an executable unmap, **nothing** on a data-page unmap, `IC IALLUIS` on a retype), plus the data-side clean-to-PoU obligation as a checked tripwire — the cache-side companion of SM7.C, closing the *instruction*-cache half of SMP-C4.  New production module `Architecture/PerCoreCacheModel.lean` mounts `SystemState.perCoreICache : Vector ICacheState numCores` with `icFetchOnCore` / `icInvalidateOnCore` (`IC IALLU` — PE-local, and `…_icacheOnCore_ne` states the SMP hazard) / `icInvalidateBroadcast` (`IC IALLUIS` / `IC IVAU`), headlined by `icInvalidateBroadcast_reaches_all_cores`; `icacheCoherent_perCore` (every cached line still has a live *executable* mapping) is the **14th `proofLayerInvariantBundle` conjunct**.  On the data side `dcMaintenanceAllCores` takes **no target set** (`dcMaintenanceByVA_reaches_all_cores` — "at PoC, already system-wide"), and the DMA scope boundary is a machine-checked tripwire (`modeledCoherentAgents_no_dma_master`).  Live behind `.vspaceUnmap` (targeted `IC IVAU`, executable mappings only) and `.lifecycleRetype` (unconditional `IC IALLUIS`); `CacheModel` promoted staged → production (staged 56 → 55); Rust HAL 789 tests; new `smp_cache_maintenance_suite` (56 runtime assertions / 9 groups).  Prior sub-phase: **SM7.C per-core TLB model LANDED (v0.32.80); operative cut (v0.32.81)** — the new production module `Architecture/PerCoreTlbModel.lean` mounts `SystemState.perCoreTlb : Vector TlbState numCores` (the SMP generalisation of the scalar boot-core `tlb`, added alongside it) and defines the per-core model over it: `tlbInsertOnCore` (the HW walker, local), `tlbInvalidateOnCore` (local invalidation — leaves other cores stale, the precise SMP hazard), and `tlbInvalidateOnAllCores` (runs the SM7.B `tlbShootdownBroadcast` and evolves every core's view via `shootdownRoundViews`, so `perCoreTlb` is a genuine consumer of the shootdown state machine); `tlbInvalidationConsistent_perCore` (every core's view matches the page tables) is the **13th `proofLayerInvariantBundle` conjunct**, `tlbShootdown_invalidates_perCore` mounts Theorem 3.3.1 on the field (SMP-C4 use-after-unmap closure), and `tlbConsistency_cross_subsystem` is the memory-subsystem capstone; carried through freeze / congruence / boot, kept out of the IF projection (a TLB view is a covert timing channel).  **v0.32.81 completion cut**: the model is now **operative on the live shootdown path** — the new operational handler `handleTlbShootdownReqOnCorePerCore` drains each target's posted queue onto *its own* view (the real per-descriptor drain), and the live `SyscallDispatchEntry.completeShootdownRounds` catch-up fold is swapped to it, **trace byte-identical** (the per-core handler's `tlb`/`tlbShootdown` effects are definitionally the single-view's — `foldl_handleTlbShootdownReqOnCorePerCore_agrees`); Theorem 3.3.1 is operative via `shootdownRoundPerCore` (`_perCoreTlb` = `shootdownRoundViews`, `_tlb_eq` the every-round two-model bridge, `_invalidates_perCore`); plus insert-side preservation, the overflow-safe coalescing broadcast, computable consistency checkers, a required (no-default) `FrozenSystemState.perCoreTlb`, and the explicit NI witness `perCoreTlb_write_preserves_projection`.  Prior: **SM7.B shootdown protocol LANDED (v0.32.76) + completion cut (v0.32.77) + debt-closure cut (v0.32.78) — the plan-§3.2 protocol complete and LIVE, every landing deferral closed and every tracked-debt item closed or narrowed**: the production `Architecture/TlbShootdownProtocol.lean` / `TlbShootdownWait.lean` / `TlbShootdownLockSet.lean` trio lands all twelve SM7.B sub-tasks — invalidation-effect semantics on FFI encodings, `tlbShootdownLocal` / `tlbShootdownBroadcast` (+ the total coalescing form) / the `.tlbShootdownReq` handler transitions, **Theorem 3.3.1** (`tlbShootdownBroadcast_invalidatesAllCores`, per-core views + the real-pipeline corollaries), the SM2.A-anchored `shootdownAck_release_acquire`, the constructive `shootdown_wait_loop_terminates` + verdict-exact `shootdown_timeout_handling`, and the cross-domain `lockSet_tlbShootdown_correct` (the SM7.A audit's round-serialisation obligation discharged).  Live wiring: the `.vspaceUnmap`/`.vspaceMap`/`.lifecycleRetype` arms route through the shootdown-aware operations (incl. `asidAllocateWithShootdown`, the previously-missing `requiresFlush` consumer, and the retype wrapper closing the no-TLB-maintenance-on-retype gap), and `SyscallDispatchEntry.completeShootdownRounds` runs the diff-recovered hardware round under the cooperatively-acquired global round try-lock (masked reset, online-target SGIs, `tlbiForSharing` broadcast TLBIs, bounded wait with fail-closed timeout panic, handler catch-up commit).  `TlbiForSharing` promoted to production (staged 57 → 56); Rust HAL 755 → 769 (round try-lock, deadline-exact bounded wait, boot-registered `.tlbShootdownReq` handler, online mask, `dispatch_irq_with_iar` full-IAR SGI dispatch fixing the GICv2 SGI-EOI defect); suite 81 → 150 assertions / 20 groups; golden trace byte-identical.  **v0.32.77 completion cut — every landing deferral closed**: `pendingBounded st.tlbShootdown` joins `proofLayerInvariantBundle` as the **12th conjunct** (boot witness + the three adapter preservation proofs + the Boot general bridge via `bootFromPlatform_tlbShootdown_eq`; carriage proven through every live shootdown-aware transition on a new `…_tlbShootdown_eq` frame family); handler commutativity (`handleTlbShootdownReqOnCore_comm` — catch-up order is a convention) + the coalescing-round capstones (`coalescingRound_restores_quiescent`/`_allAcked`) + the positive diff characterization (`shootdownChangedTargets_coalescing_of_quiescent`) + Theorem 3.3.1's total-posting remote case; remap-only map rounds with the ok-implies-fresh model fact (`vspaceMapPageCheckedWithFlushFromState_ok_fresh` — a successful map is always fresh, so the map path never posts today and the round rides the unmap of unmap-then-map); the least-index wait (`waitAllAckedBounded_least`) + the round-lock CAS model + the cross-round publication chain (`shootdownRoundLock_release_acquire`, with the 4-core multi-pair B.4 witness); entry hardening (named `shootdownRoundLockAcquireFuel`, one `CORE_READY` snapshot per round, the vmalle1-dominance `collapseShootdownOps`, `shootdownSharingDomain` derived from `PlatformBinding.sharingDomain`, the local self-service `tlbiLocalFullFlush`); the CSpaceAddr retype sibling `lifecycleRetypeWithCleanupShootdown` (the storeObject-sweep closure); Rust `_in` handler/lock forms with genuine false→true ack tests + an 8-thread CAS mutex stress (HAL 769 → 772); suite 22 groups / 160 runtime assertions incl. the live `.vspaceUnmap` `dispatchSyscall` scenario; `scripts/test_qemu_smp_shootdown.sh` seeded (Tier-4-registered; SKIPs until the SM10.E image).  **v0.32.78 debt-closure cut — every SM7.B tracked-debt item closed or narrowed**: the `.tlbShootdownReq` handler retires the round's EXACT operands per-descriptor (`tlb::tlbi_local`) instead of a blanket `vmalle1`, matching the Lean `handleTlbShootdownReqOnCore` — the initiator publishes the collapsed operands into a seqlock-guarded `ShootdownOpMailbox` under the round lock before the SGIs, and the handler retires a stable snapshot per-descriptor with a fail-safe local `vmalle1` fallback on any torn read / overflow / undecodable operand (HAL 772 → 780, trace byte-identical); the formal refinement narrows to operand-for-operand (residual: the SM10.E linked-runtime proof); B.10 is a confirmed no-safety-gap completeness deferral (no runtime ASID-reuse path exists) with closure target SM8; step-4d direct-ack is closed by design (the spin wait + masked SVC path make it informationless); the `withLockSet` shootdown slice is closed (`withLockSet_preserves_pendingBounded`); and the host-test starvation flake is closed (host-test yields already present via `cpu::wfe()`; the authoritative `test_rust.sh` builds before testing; the mutex-stress test caps contenders at `available_parallelism()`).  **v0.32.79 PR #839 review-P1 cut**: the shootdown target mask now reads the IRQ-serviceable `smp::CORE_IRQ_READY` flag (published by the secondary after `enable_irq`) for both the round reset and the SGI targets, rather than the primary's `CORE_READY` release handshake — so a released-but-not-IRQ-ready or timer-dead secondary can no longer hang a round into the SM7.B.6 fail-closed panic (HAL 780 → 782; Lean FFI-backed, docstring-only); the concurrent posting/catch-up round-lock finding is recorded as model-fidelity tracked debt (no hardware hazard — each round's TLB maintenance rides its own `(pre,post)` diff + blocking ack wait), closure target the SM7.C round-generation model change.  Prior: **SM7.A shootdown descriptor + state LANDED (v0.32.72); completion cut (v0.32.73)**: the SM7 state layer (all six sub-tasks of [`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md`](planning/SMP_TLB_SHOOTDOWN_PLAN.md) §5).  The v0.32.73 completion cut mounts the state as `SystemState.tlbShootdown` (production; partition 58 → 57; pure `TlbInvalidation` operand module extracted from the staged `TlbiForSharing`), formalises the §4.1 capacity argument (`beginRound_foldlM_enqueueShootdown_isSome` + the round capstone `shootdownRound_restores_quiescent`), adds the total overflow escape hatch `enqueueShootdownOrCoalesce`, the per-core `ShootdownQueueLockId` (SM7.B.7 seam), and the live ack-flag FFI seam (`ffi_shootdown_*` + typed wrappers; HAL 743 → 750).  Suite 51 → 73 assertions / 11 groups.  The v0.32.74 audit cut corrects the round-serialisation contract (system-wide round serialisation via the new provably-unique `ShootdownRoundLockId` — registered SM7.B.7 obligation; the VSpaceRoot lock alone is insufficient) and completes the coalescing coverage (`enqueueShootdownOrCoalesce_pending_covered`); suite 73 → 75 assertions.  The v0.32.75 review-P1 fix keeps offline cores born-acknowledged across a round (Rust `CORE_READY`-masked reset + Lean `beginShootdownRoundFor` with the hypothesis-free masked capstone); suite 75 → 81 assertions / 12 groups, HAL 755.  `SeLe4n/Kernel/Architecture/TlbShootdown.lean`: `TlbShootdownDescriptor` (typed `TlbInvalidation` operand + initiating `CoreId`), `TlbShootdownState` (per-core `pendingShootdowns` queues + `shootdownAck` flags, SM4.B path-a accessors, quiescent boot state), `enqueueShootdown` (FIFO, fail-closed at `maxPendingPerCore = 16`), `drainShootdowns` (whole-queue FIFO drain, exhaustive, ack-free by design), `acknowledgeShootdown` + `beginShootdownRound` + decidable `allAcked`/`shootdownQuiescent`/`pendingBounded`, preservation theorems across every operation, and the SM7.B.5 termination anchor `allCores_foldl_acknowledgeShootdown_allAcked`.  Rust: `rust/sele4n-hal/src/shootdown.rs` `SHOOTDOWN_ACK` per-core cache-line-aligned `AtomicBool` (Release set / Acquire poll / Relaxed round-reset riding SM1.F.8's dsb-before-SGIR), HAL 724 → 743 tests.  Tests: `tests/SmpTlbShootdownSuite.lean` (`smp_tlb_shootdown_suite`, 51 assertions / 7 groups), Tier-2 + Tier-3 wired.  Prior: **SM6.F tests + fixtures LANDED (v0.32.67); depth cut (v0.32.68) — SM6 (A–F) complete** (depth cut v0.32.68: the aggregates add SchedContext donation round trips, capability transfer, info-flow-checked dispatch, the live `dispatchSyscall` `.call` path, cancellation×IPC composition, scheduler contention, a three-waiter drain, and the review-#3 bound-signal badge-leak gate — IPC suite 80→130 assertions/14 groups, notification 58→76/10): the SM6 closure phase (plan §SM6.F, all six sub-tasks), closing the two remaining substantive §8 acceptance-gate items on the live operations.  `tests/SmpIpcSuite.lean` (`smp_ipc_suite`, 130 assertions / 14 scenario groups + the golden-trace check): end-to-end pipelines composing the SM6.A/SM6.C transitions with the SM5 per-core scheduler (`handleRescheduleSgiOnCore` dispatch on the SGI's target core) — the **2-thread cross-core call/reply round trip** and the **4-thread SMP rendezvous** (two interleaved client/server pairs across all four cores, cross-pair framing + payload isolation), plus the cross-core send/receive rendezvous, client-first ordering, the server `endpointReplyRecvOnCore` steady-state loop, fail-closed error paths, state-resolved 2PL footprints, and live-dispatch coherence.  `tests/SmpNotificationSuite.lean` (`smp_notification_suite`, 76 assertions / 10 groups): the wait → cross-core signal → SGI → handler-dispatch round trip, multi-waiter head-first drain (per-waiter home cores + badge isolation), `Badge.bor` accumulation + the non-blocking consume, the remote bound-TCB delivery round trip, the bind/unbind lifecycle, error paths, and independence framing.  `tests/fixtures/smp_ipc_4core.expected` (+ `.sha256`): the deterministic 16-line `[smp-ipc-4core]` golden trace, byte-for-byte verified in-suite and auto-gated by the Tier-2 companion walk.  `scripts/test_qemu_smp_ipc.sh`: the Tier-4 QEMU `-smp 4` handshake exerciser (SKIPs until the SM10.E bootable image, the SM5-sibling discipline).  Surface anchors: in-suite `#check` blocks + Tier-3 grep anchors.  The plan §8 acceptance gate is fully checked.  Prior: **SM6.E cancellation across cores LANDED (v0.32.60; completed v0.32.61; PR-review cuts v0.32.62–65; audit closure v0.32.66)** — the suspend pipeline's cancellation sub-operations lifted to SMP in the production `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean`: `descheduleThread` (the SM5.C `wakeThread` dual — home-core deschedule, `.reschedule` SGI iff the victim was actively current on a remote home core), the cross-core composite `cancelIpcBlockingOnCore` (single-core teardown + home-core deschedule + remote poke), and per-core donation cancellation (`cancelBoundDonationOnCore` purges the SC's replenishments from the victim's home core's queue, fixing the `bootCoreId` hardcode); footprints `lockSet_cancelIpcBlocking` / `lockSet_cancelDonation` state-resolved and member-by-member covered by the reply-extended `lockSet_tcbSuspend` (`permittedKinds .tcbSuspend` += `.reply` — closing the SM6.D reply-fold footprint gap); 2PL atomicity `cancelIpcBlocking_atomic_under_lockSet` / `cancelDonation_atomic_under_lockSet` + OnCore companions; flagship `cancellation_cross_core_correct`; `objects.invExt` preservation across the whole cancellation surface; axiom-clean; `tests/SmpCancellationSuite.lean` (107 assertions, 17 groups).  **Completion cut (v0.32.61)**: live `.tcbSuspend` cross-core dispatch (`suspendThreadOnCore` behind the dispatch arm, the `crossCoreSgiBody_remote_deschedule` diff-seam rule, the `suspend_thread_cross_core` FFI/Rust flip — trace byte-identical); staged `CancellationNI` non-interference module (staged-only 57); `ipcInvariant` preservation across the entire cancellation surface; the closed-form `cancelIpcBlockingOnCore_eq_descheduleThread_closed`; observational atomicity (`cancelIpcBlockingOnCore_observer_atomic`); the donated-arm replenishment migration; and two pre-existing single-core defect fixes (notification sole-waiter invariant break; suspendThread dead G7 guard).  **PR-review cut (v0.32.62)**: the suspend PIP-revert ordering fix (a third pre-existing defect — the revert ran before the teardown, so a server retained the suspended victim's donated boost; now `timeoutThread`'s D4-N capture → clear → revert-from-server order), the per-core revert walk (`propagatePipChainCrossCore`, per-home-core bucket migration), diff-fired suspend-entry SGIs (`computeCrossCoreSgis`), and the `pipChainStart_tcbSuspend` chain-walk marker (inventory 99).  **PR-review cut 2 (v0.32.63)**: disinheritance scheduling points — the gated local preemption point on a deboosted executing-core current (`currentEffectivePrio?`/`currentDeboostedFrom`, G7 factored into `suspendRescheduleOnCore`) and the diff seam's deboosted-current rule (`crossCoreSgiBody_remote_deboost_current`) poking a remote core that keeps running a deboosted server.  **PR-review cut 3 (v0.32.64)**: scheduler-lock footprint closure — the executing-core run-queue lock in `suspendThreadOnCoreSchedLockSet`, the chain-walk contract's per-step TCB + home-core run-queue lock pair, and the preemption gate's documented `boundThreadPriorityConsistent` dependency.  **PR-review cut 4 (v0.32.65)**: the running-core suspend (an unbound victim current on a secondary core is descheduled + poked on THAT core; diff rules re-keyed) and write-set-honest sweeps (+ neighbour-TCB footprint members).  **Audit-closure cut (v0.32.66)**: running-core footprint lock, EDF deadline diff rules, `currentThreadUniqueAcrossCores` slice, NI projection-sketch correction, donation observer capstone; no CVE-class findings.  Prior: **SM6.D IPC across-core invariant bundle LANDED (v0.32.58; completed v0.32.59 — unconditional whole-bundle + per-core closures for every cross-core transition and the WithCaps trio via the `LookupCongruence` transfer layer and per-op agreement dichotomies; `endpointReplyRecvOnCore` closed compositionally with seL4-MCS one-object reuse)** — the twenty-conjunct `ipcInvariantFull` restricted to per-core views: `ipcInvariantFull_perCore` (`SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean`, production; thread-subject conjuncts restricted to the threads homed on core `c` via `threadHomeCore`, provably the operational wake target) with the exact decomposition `ipcInvariantFull_smp_iff_full_and_passive_smp`, per-conjunct exactness for the four plan-named conjuncts (SM6.D.3–D.6), and all six IPC operations (+ `endpointReplyRecv` and the cross-core `endpointCallOnCore` flagship) proven to preserve every core's bundle view (`…_preserves_ipcInvariantFull_perCore`, `PerCoreBundlePreservation.lean` — the per-core `passiveServerIdle` slice via the new `passiveServerIdleFrameOnCore` micro-frame family, **no idle-core assumption**); axiom-clean; `tests/SmpCrossCoreCallSuite.lean` §SM6.D.  Prior: **SM6.C reply path across cores LANDED (v0.31.77)** — live `.reply`/`.replyRecv` cross-core dispatch (`endpointReplyOnCore` / `endpointReplyRecvOnCore`, wake-the-caller on its home core, replay barrier, donation return + cross-core PIP reversion), `tests/SmpCrossCoreReplySuite.lean`.  Prior: **SM6.B notification across cores LANDED (v0.31.68)** — the cross-core IPC phase (SM6) continues: `notificationSignalOnCore` lifts the notification signal to SMP (head-waiter wake via the SM5.C cross-core `wakeThread` with a `.reschedule` SGI to a remote waiter's home core — `notificationSignalOnCore_remote_wake`; the signaller does **not** block) and `notificationWaitOnCore` blocks the caller on its own core via the per-core `removeRunnableOnCore`, with the multi-waiter-discipline / 2PL-atomicity / per-core-wake-locality / notification-↔-TCB-binding-lock-set / cross-core-non-interference (boot-core + per-core/∀-core `lowEquivalent_smp`) theorems, staged (partition 54 → 56), `tests/SmpCrossCoreNotificationSuite.lean` (24 runtime assertions).  Prior: **SM6.A endpoint call across cores LANDED (v0.31.65)** — `endpointCallOnCore` lifts the endpoint `Call` rendezvous to SMP (receiver wake via the SM5.C cross-core `wakeThread` with a `.reschedule` SGI to a remote receiver's home core, plan Theorem 3.2.1; caller block via the per-core `removeRunnableOnCore`), with the lock-set-correctness / donation-extension / 2PL-atomicity / per-core-blocking / reply-state-allocation / WithCaps / cross-core-non-interference theorems, `tests/SmpCrossCoreCallSuite.lean`.  Prior: **SM5.J WCRT-under-fine-locks + SM5.K acceptance tests COMPLETE (v0.31.63; completion audit-pass v0.31.64 — the genuine per-core eventually-scheduled liveness via the production `(c : CoreId)` R5 trace-model generalisation)**.  Canonical per-phase record: [`docs/WORKSTREAM_HISTORY.md`](WORKSTREAM_HISTORY.md); phase plans under `docs/planning/SMP_*.md`.  Prior portfolio: **WS-AJ COMPLETE** (v0.28.1–v0.29.0): Post-Audit Comprehensive Remediation (v0.28.0 audit) — 6 phases (AJ1–AJ6), 30 sub-tasks. Phase AJ6 (v0.29.0): Documentation, Testing & Closure — H-01/H-02/H-03 activation roadmaps in §8.15, by-design finding documentation (10 findings), audit errata (L-01/L-17 false, counts 55→52/24M→21M), deferred finding annotations (4 findings), documentation sync, version bump. Phase AJ5 (v0.28.4): Rust HAL Hardening — M-20 MMIO `assert!`, M-21 `UnsafeCell<Uart>`, L-14 `TimerError`, L-15 `pub(crate)`. Phase AJ4 (v0.28.4): Architecture Model Correctness. Phase AJ3 (v0.28.3): Platform & Boot Pipeline. Phase AJ2 (v0.28.2): Security & Information Flow Hardening. Phase AJ1 (v0.28.1): IPC & Lifecycle Correctness. Gate: `test_full.sh` + `cargo test --workspace` + `check_version_sync.sh`. Zero sorry/axiom. **Next: WS-V (AG10: Hardware Integration).** Plan: [`docs/dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.28.0_WORKSTREAM_PLAN.md). **WS-AI PORTFOLIO COMPLETE** (v0.28.0): Post-Audit Comprehensive Remediation — 7 phases (AI1–AI7), 37 sub-tasks, v0.27.7–v0.28.0. All 60 findings from the v0.27.6 comprehensive audit addressed (5 HIGH, 27 MEDIUM, 28 LOW). Phase AI7: Testing, Closure & Final Gate — L-17 CBS truncation tolerance, L-26 lifecycleRetypeObject visibility, fixture verification, version bump, documentation closure. **WS-AI Phase AI6 COMPLETE** (v0.27.12): Documentation & Proof Gaps. 7 sub-tasks (AI6-A through AI6-G). AI6-A: Scheduler documentation batch (M-02 silent-drop spec cross-reference, M-03 RunQueue.size proof-linking deferral, M-23 blocking chain cycle behavior, M-24 eventuallyExits deployment scope, M-25 WCRT externalized hypotheses). AI6-B: Platform & boot documentation batch (M-07 boot invariant bridge scope, M-08 fromDtb stub status, M-10 MMIO read RAM semantics, M-11 VSpaceRoot exclusion). AI6-C: Architecture documentation batch (M-13 physicalAddressBound proof-layer default, M-16 D-cache→I-cache pipeline ordering, M-17 context switch TLB/ASID gap, M-18 cross-module composition gap). AI6-D: Model & SchedContext documentation batch (M-21 descendantsOf fuel sufficiency TPI-DOC cross-reference, L-02 allTablesInvExtK tuple projection fragility, L-13 schedContextBind thread-state gap design rationale). AI6-E: Stale reference fixes (L-15 maxBlockingDepth→objectIndex.length, L-24 RPi5 RuntimeContract H3-prep stub→substantive). AI6-F: SELE4N_SPEC.md sync (4 new sections: §8.10.4 silent-drop, §8.14.1 WCRT hypotheses, §8.14.2 boot scope, §8.14.3 MMIO limitations). Gate: `test_full.sh` + doc sync. Zero sorry/axiom. **WS-AI Phase AI5 COMPLETE** (v0.27.11). **WS-AI Phase AI4 COMPLETE** (v0.27.10). **WS-AI Phase AI3 COMPLETE** (v0.27.9). **WS-AI Phase AI2 COMPLETE** (v0.27.8). **WS-AI Phase AI1 COMPLETE** (v0.27.7). Plan: [`docs/dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.27.6_WORKSTREAM_PLAN.md). **WS-AH PORTFOLIO COMPLETE** (v0.27.2–v0.27.6): Pre-Release Comprehensive Audit Remediation — 5 phases (AH1–AH5), 27 sub-tasks. Phase AH5 (v0.27.6): Documentation, Testing & Closure. Phase AH4 (v0.27.5): Version Consistency & CI Automation. Phase AH3 (v0.27.4): Capability, Architecture & Decode Hardening. Phase AH2 (v0.27.3): IPC Donation Safety & Boot Pipeline. Phase AH1 (v0.27.2): Critical IPC Dispatch Correctness. Plan: [`docs/dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.27.1_WORKSTREAM_PLAN.md). **WS-AG PORTFOLIO COMPLETE** (v0.26.0–v0.27.1): H3 Hardware Binding Audit Remediation — 10 phases (AG1–AG10), 67 sub-tasks. **Phase AG10 COMPLETE** (v0.27.1): Documentation + Closure. **Phase AG9 COMPLETE** (v0.27.0): Testing + Validation. **Phase AG8 COMPLETE** (v0.26.9): Integration + Model Closure. **Phase AG7 COMPLETE** (v0.26.8): FFI Bridge + Proof Hooks. **Phase AG6 COMPLETE** (v0.26.7): Memory Management (ARMv8 Page Tables). **Phase AG5 COMPLETE** (v0.26.6): Interrupts + Timer. **Phase AG4 COMPLETE** (v0.26.5): HAL Crate + Boot Foundation. **Phase AG3 COMPLETE** (v0.26.4): Platform Model Completion. **Phase AG2 Audit COMPLETE** (v0.26.2). **Phase AG2 COMPLETE** (v0.26.1): Pre-Hardware Rust ABI Fixes. **Phase AG1 COMPLETE** (v0.26.0): Pre-Hardware Lean Code Fixes. Plan: [`docs/dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_H3_HARDWARE_BINDING_WORKSTREAM_PLAN.md). **WS-AF PORTFOLIO COMPLETE** (v0.25.22–v0.25.27). **WS-AE PORTFOLIO COMPLETE** (v0.25.15–v0.25.21). **WS-AD PORTFOLIO COMPLETE** (v0.25.11–v0.25.14). **WS-AC PORTFOLIO COMPLETE** (v0.25.3–v0.25.10). **WS-AB PORTFOLIO COMPLETE** (v0.24.0–v0.25.5). **WS-AA COMPLETE** (v0.23.22–v0.23.23). **WS-Z PORTFOLIO COMPLETE** (v0.23.0–v0.23.21). All prior portfolios complete: WS-Y, WS-X, WS-W, WS-V, WS-U, WS-T, WS-S–WS-B (see `docs/WORKSTREAM_HISTORY.md`),
- **recently completed:** WS-J1-C audit refinements (v0.15.7 — CSpace/lifecycle/VSpace dispatch returns `illegalState` for MR-dependent ops, `syscallEntry` accepts `regCount` parameter, `syscallEntry_implies_capability_held` strengthened to full capability-resolution chain; zero sorry/axiom), WS-J1-C (v0.15.6, syscall entry point and dispatch — `syscallEntry` top-level entry point, `lookupThreadRegisterContext` TCB register extraction, `dispatchSyscall` routing through `SyscallGate`/`syscallInvoke` to 13 internal kernel operations, `dispatchWithCap` per-syscall routing, `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted to field; 5 soundness theorems; zero sorry/axiom), WS-J1-B (v0.15.5, register decode layer — `SyscallId` inductive with 13 syscalls, `MessageInfo` bit-field structure, `SyscallDecodeResult`, total deterministic decode functions in `RegisterDecode.lean`, round-trip/determinism/error-exclusivity theorems, `SyscallRegisterLayout` with ARM64 default, 3 new `KernelError` variants; zero sorry/axiom), WS-J1-A (v0.15.4, typed register wrappers — replaced `abbrev RegName/RegValue := Nat` with typed wrapper structures, full instance suites, all 10 machine lemmas re-proved, downstream compilation fixed across Architecture/Platform/Testing; zero sorry/axiom), WS-H15 (v0.14.7, platform & API hardening — `InterruptBoundaryContract` decidability, RPi5 contract hardening with substantive predicates, 13 capability-gated syscall wrappers, `AdapterProofHooks` concrete instantiation for Sim/RPi5, MMIO disjointness proof; closes A-33, A-41, A-42, M-13), WS-H14 (v0.14.6, type safety & Prelude foundations — `EquivBEq`/`LawfulBEq` for 14 identifier types, `LawfulMonad` for `KernelM`, `isPowerOfTwo` correctness proof, identifier roundtrip/injectivity theorems, `OfNat` instance removal for type-safety enforcement, sentinel predicate completion), Module restructuring (v0.14.5, decomposed 9 monolithic files into 24 focused submodules via re-export hub pattern; zero code loss, 50 new helper theorems extracted, 209 Tier 3 anchor checks updated), WS-H13 (v0.14.4, CSpace/service model enrichment — `cspaceDepthConsistent` invariant, `resolveCapAddress` theorems, `serviceGraphInvariant` preservation, `cspaceMove` atomicity; addresses H-01, A-21, A-29, A-30, M-17/A-31; WS-Q1: `serviceStop` backing-object verification removed), WS-H12f (v0.14.3, test harness update & documentation sync — dequeue-on-dispatch, context switch, and bounded message trace scenarios; legacy `endpointInvariant` comment cleanup; expected fixture updated; Tier 3 anchors added; documentation synchronized), WS-H12e (v0.14.2, cross-subsystem invariant reconciliation), WS-H12d (v0.14.1, IPC message payload bounds — A-09 closed), WS-H12c (v0.14.0, per-TCB register context with inline context switch — H-03 closed), WS-H12b (v0.13.9, dequeue-on-dispatch scheduler semantics — H-04 closed), WS-H12a (v0.13.8, legacy endpoint removal), WS-H11 (v0.13.7, VSpace & architecture enrichment), End-to-end audit (v0.13.6), WS-H10 (v0.13.6, security model foundations), WS-H7/H8/H9 gaps closed (v0.13.5), WS-H9 (v0.13.4, NI coverage >80%), WS-H8 (v0.13.2, enforcement-NI bridge), WS-H6 (v0.13.1, scheduler proof completion), WS-H5 (v0.12.19, IPC dual-queue invariant), WS-H4 (v0.12.18, capability invariant redesign), WS-H3 (v0.12.17, build/CI), WS-H2 (v0.12.16, lifecycle safety), WS-H1 (v0.12.16, IPC call-path fix), WS-G (v0.12.15, kernel performance), WS-F1..F4 (critical audit remediation),
- **findings baseline:** [`AUDIT_CODEBASE_v0.12.2_v1.md`](dev_history/audits/AUDIT_CODEBASE_v0.12.2_v1.md), [`v2`](dev_history/audits/AUDIT_CODEBASE_v0.12.2_v2.md),
- **latest audit:** [`AUDIT_v0.25.3_COMPREHENSIVE`](dev_history/audits/AUDIT_v0.25.3_COMPREHENSIVE.md) — full-kernel Lean + Rust audit (0 CRIT, 3 HIGH, 9 MED, 14 LOW); remediation plan in [`AUDIT_v0.25.3_WORKSTREAM_PLAN`](dev_history/audits/AUDIT_v0.25.3_WORKSTREAM_PLAN.md),
- **hardware target:** Raspberry Pi 5 (ARM64).

Canonical planning sources:
[`docs/dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.22.17_WORKSTREAM_PLAN.md) for WS-X (all 5 phases complete),
[`docs/dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.20.7_WORKSTREAM_PLAN.md) for WS-U (Phase U8 complete — all 8 phases delivered),
[`docs/dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.19.6_WORKSTREAM_PLAN.md) for WS-T (complete),
[`docs/dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md) for WS-S (completed),
[`docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md) for WS-R (completed),
[`docs/dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md) for WS-Q (completed), and
[`docs/dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md) for completed WS-H remediation lineage.

---

## 2) Non-negotiable baseline contracts

Unless a PR explicitly proposes spec-level change control, preserve:

1. deterministic transition semantics (explicit success/failure branches),
2. M3.5 IPC-scheduler handshake coherence semantics and trace anchors,
3. local + composed invariant layering (including `currentThreadInActiveDomain` in the canonical scheduler bundle),
4. domain-aware scheduling semantics (`schedule` only chooses from `activeDomain`; `scheduleDomain` switch/tick behavior is regression-tested),
5. theorem discoverability through stable naming,
6. fixture-backed executable evidence (`Main.lean` + trace fixture),
7. tiered validation command behavior (`test_fast`/`smoke`/`full`/`nightly`),
8. top-level import hygiene: keep `SeLe4n.lean` free of duplicate/redundant subsystem imports by relying on `SeLe4n/Kernel/API.lean` as the canonical aggregate surface.

---

## 3) Next workstreams

### 3.0 Current status

**WS-Z** (Composable Performance Objects) is **COMPLETE** (v0.23.0–v0.23.21) —
10 phases (Z1–Z10, 213 sub-tasks) delivering the full SchedContext subsystem:

- **Z1** (v0.23.0): SchedContext type foundation — 18 sub-tasks. SchedContextId typed wrapper, Budget/Period/Bandwidth types, SchedContext structure, SchedContextBinding enum, TCB schedContextBinding field, 7th KernelObject variant, full codebase ripple fix (24 files).
- **Z2** (v0.23.1–v0.23.4): CBS budget engine — 24 sub-tasks. consumeBudget, replenish, admission control. 4-conjunct `schedContextWellFormed` bundle, 16 per-operation preservation theorems, `cbs_bandwidth_bounded` theorem.
- **Z3** (v0.23.5–v0.23.6): Replenishment queue — 12 sub-tasks. Sorted insert, popDue, remove, peek/hasDue. `pairwiseSortedBy` predicate, 13 preservation/membership theorems.
- **Z4** (v0.23.7–v0.23.8): Scheduler integration — 33 sub-tasks. `effectivePriority`, `hasSufficientBudget`, `timerTickBudget`, `scheduleEffective`. 6 new invariants, `schedulerInvariantBundleExtended` (15-tuple).
- **Z5** (v0.23.9–v0.23.11): Capability-controlled thread binding — 25 sub-tasks. 3 new SyscallId variants, schedContextConfigure/Bind/Unbind/YieldTo operations, 7 preservation theorems, API dispatch wiring.
- **Z6** (v0.23.12–v0.23.14): Timeout endpoints — 26 sub-tasks. Budget-driven IPC timeout, `endpointQueueRemove`, `timeoutThread`, `blockedThreadTimeoutConsistent` invariant (10th conjunct of `ipcInvariantFull`).
- **Z7** (v0.23.15–v0.23.16): SchedContext donation / passive servers — 26 sub-tasks. `donateSchedContext`, `returnDonatedSchedContext`, donation-aware IPC wrappers, 4 new invariants (`donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`, `donationBudgetTransfer`). `ipcInvariantFull` extended to 14 conjuncts.
- **Z8** (v0.23.17–v0.23.18): API surface & syscall wiring — 17 sub-tasks. 3 error-exclusivity theorems, 4 frozen SchedContext operations, enforcement boundary 22→25, `frozenOpCoverage_count` 12→15, 6 budget lifecycle trace scenarios, 8 negative tests.
- **Z9** (v0.23.19–v0.23.20): Invariant Composition & Cross-Subsystem — 20 sub-tasks. 3 new cross-subsystem predicates (`schedContextStoreConsistent`, `schedContextNotDualBound`, `schedContextRunQueueConsistent`). `crossSubsystemInvariant` 5→8 predicates. `proofLayerInvariantBundle` 9→10 conjuncts. 16 pairwise disjointness witnesses, 3 frame lemmas, boot/freeze/operation preservation.
- **Z10** (v0.23.21): Documentation & Closure — 12 sub-tasks. Spec, development docs, workstream history, claims, codebase map, GitBook, README, CLAUDE.md, website manifest synchronized. WS-Z PORTFOLIO COMPLETE.

**WS-AB** (Deferred Operations) Phases D1–D5 are **COMPLETE** (v0.24.0–v0.25.0):

- **D1** (v0.24.0–v0.24.1): Thread Suspension & Resumption — `suspendThread` 7-step pipeline, `resumeThread` 5-step sequence, 2 new `SyscallId` variants, 12 transport lemmas, 21 test cases. Zero sorry/axiom.
- **D2** (v0.24.1): Priority Management — `setPriorityOp`/`setMCPriorityOp`, MCP authority non-escalation, run queue bucket migration, 15 tests. Zero sorry/axiom.
- **D3** (v0.24.2–v0.24.3): IPC Buffer Configuration — `setIPCBufferOp` with 5-step validation, 7 transport lemmas, 17 tests. Zero sorry/axiom.
- **D4** (v0.25.0): Priority Inheritance Protocol — `pipBoost` TCB field, blocking graph with acyclicity/depth bound, `propagatePriorityInheritance`/`revertPriorityInheritance` chain walk, 16 frame preservation theorems, parametric bounded inversion, 22 tests. Zero sorry/axiom.
- **D5** (v0.25.0): Bounded Latency Theorem — proof-only phase, zero kernel code changes. Trace model (`SchedulerStep`, `SchedulerTrace`, `validTrace`), per-mechanism bounds (timer-tick budget, CBS replenishment, FIFO progress, domain rotation), main theorem `wcrtBound_unfold` / `bounded_scheduling_latency_exists`: WCRT = D*L_max + N*(B+P). PIP enhancement: `pip_enhanced_wcrt_le_base`. 58 surface anchor tests. New `Scheduler/Liveness/` directory. Zero sorry/axiom.

**Next major milestone**: WS-SM — multi-core SMP completion (foundations
landed at v0.31.3 in Phase SM0; per-core scheduler / verified locks /
TLB shootdown / cross-core IPC follow in SM1..SM10 through v1.0.0).
Tracked in
[`docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`](planning/SMP_MULTICORE_COMPLETION_PLAN.md).
Companion post-1.0 deferrals: FrozenOps production promotion, CDT fuel
sufficiency proofs, donation chain formal bridge.

### 3.0a Prior completed portfolios (summary)

All portfolios from WS-B through WS-Y are complete. Key milestones:

- **WS-Y** (v0.22.23–v0.22.26): Documentation & cross-subsystem hardening. **PORTFOLIO COMPLETE.**
- **WS-X** (v0.22.18–v0.22.22): Documentation, hardening & low-severity. **PORTFOLIO COMPLETE.**
- **WS-W** (v0.22.11–v0.22.17): Pre-release audit remediation — 6 phases, 52 sub-tasks. **PORTFOLIO COMPLETE.**
- **WS-V** (v0.22.0–v0.22.10): Deep audit remediation — 8 phases. **PORTFOLIO COMPLETE.**
- **WS-U** (v0.21.0–v0.21.7): Comprehensive audit remediation — 8 phases, 97 sub-tasks. **PORTFOLIO COMPLETE.**
- **WS-T** (v0.20.0–v0.20.7): Deep-dive audit remediation — 8 phases, 94 sub-tasks. **PORTFOLIO COMPLETE.**
- **WS-S** (v0.19.0–v0.19.6): Pre-benchmark strengthening — 7 phases, 83 sub-tasks. **PORTFOLIO COMPLETE.**
- **WS-R** (v0.18.0–v0.18.7): Comprehensive audit remediation — 8 phases, 111 sub-tasks. **PORTFOLIO COMPLETE.**
- **WS-Q** (v0.17.7–v0.17.14): Kernel state architecture — 9 phases, 45 atomic units. **PORTFOLIO COMPLETE.**
- **WS-N** (v0.17.0–v0.17.5): Robin Hood hashing — 5 phases, 122 subtasks. **PORTFOLIO COMPLETE.**
- **WS-M** (v0.16.14–v0.17.0): Capability subsystem — 5 phases. **PORTFOLIO COMPLETE.**
- **WS-L** (v0.16.9–v0.16.13): IPC subsystem — 5 phases. **PORTFOLIO COMPLETE.**
- **WS-K** (v0.16.0–v0.16.8): Full syscall dispatch — 8 phases. **PORTFOLIO COMPLETE.**
- **WS-J1** (v0.15.4–v0.15.10): Register-indexed namespaces — 6 phases. **PORTFOLIO COMPLETE.**
- **WS-F–WS-I** (v0.12.2–v0.15.3): Audit remediation, testing, infrastructure. **ALL COMPLETE.**
- **WS-B–WS-E** (historical): Foundation workstreams. **ALL COMPLETE.**

For detailed per-phase descriptions of completed workstreams, see
[`docs/WORKSTREAM_HISTORY.md`](WORKSTREAM_HISTORY.md).

The **WS-Q** portfolio (Kernel State Architecture) is **fully complete**
(v0.17.7–v0.17.14) — a multi-phase plan unifying two-phase state architecture,
service interface simplification, and Rust syscall wrappers into a single execution path.
**WS-Q1** (v0.17.7) — service interface simplification — **COMPLETED**:
stateless registry model replacing lifecycle-based `ServiceStatus`/`ServiceConfig`.
**WS-Q2** (v0.17.8) — universal RHTable migration — **COMPLETED**: replaced
every `Std.HashMap` and `Std.HashSet` in kernel state (16 map fields + 2 set
fields across 6 structures, 30+ files) with formally verified `RHTable`/`RHSet`.
10 atomic subphases (Q2-A through Q2-J) including `RHSet` type definition,
`allTablesInvExt` global invariant predicate, and `invExt` proof threading
across all subsystem invariant files.
**WS-Q3** (v0.17.9) — IntermediateState formalization — **COMPLETED**:
`IntermediateState` type wrapping `SystemState` with four machine-checked
invariant witnesses (`allTablesInvExt`, `perObjectSlotsInvariant`,
`perObjectMappingsInvariant`, `lifecycleMetadataConsistent`). 7 builder
operations (`registerIrq`, `registerService`, `addServiceGraph`,
`createObject`, `deleteObject`, `insertCap`, `mapPage`). Boot sequence
(`bootFromPlatform`) with master validity theorem. Zero sorry/axiom, 1,479
proved declarations, all tests pass.
**WS-Q4** (v0.17.10) — CNode radix tree (verified) — **COMPLETED**:
`CNodeRadix` flat radix array for CNode capability slots with O(1) zero-hash
lookup via `extractBits` + direct array indexing. 24 correctness proofs
(lookup roundtrip, WF preservation, parameter invariance, size bounds,
toList completeness/noDup, fold coverage). `buildCNodeRadix` equivalence
bridge (RHTable → CNodeRadix), `freezeCNodeSlots` Q5 integration, 12-scenario
test suite (43 checks). Zero admitted proofs, 1,527 proved declarations,
all tests pass.
**WS-Q5** (v0.17.11) — FrozenSystemState + freeze — **COMPLETED**:
`FrozenMap`/`FrozenSet` types, per-object frozen representations (`FrozenCNode`
with `CNodeRadix`, `FrozenVSpaceRoot` with `FrozenMap`), `freeze` function
(IntermediateState → FrozenSystemState), capacity planning. 20+ theorems,
15-scenario test suite (49 checks). Zero sorry/axiom, 1,558 proved declarations.
**WS-Q6** (v0.17.12) — Freeze correctness proofs — **COMPLETED**:
machine-checked proofs that `freeze` preserves lookup semantics and kernel
invariants. Core `freezeMap_get?_eq` theorem + 13 per-field lookup equivalence
theorems (Q6-A). CNode radix lookup equivalence via generic fold helpers (Q6-B).
5 structural property theorems (Q6-C). Invariant transfer with keystone
`freeze_preserves_invariants` theorem (Q6-D). 31 theorems in
`SeLe4n/Model/FreezeProofs.lean`, 22-scenario test suite (60 checks). Zero
sorry/axiom.
**WS-Q7** (v0.17.13) — Frozen kernel operations — **COMPLETED**:
`FrozenKernel` monad with 24 per-subsystem frozen operations across 7 subsystems
(Scheduler, IPC, Capability, VSpace, Service, SchedContext, Lifecycle/Architecture).
FrozenMap set/get? commutativity
proofs, 18 frozenStoreObject preservation theorems. 15-scenario test suite
covering TPH-005 through TPH-014. Zero sorry/axiom.
**WS-Q8** (v0.17.13) — Rust syscall wrappers — **COMPLETED**:
`libsele4n` — 3 `no_std` Rust crates (`sele4n-types`, `sele4n-abi`, `sele4n-sys`)
encoding the finalized ABI surface (20 syscalls, V2-A/D + Z5). 14 newtype identifiers,
43-variant `KernelError`, `MessageInfo` bitfield, ARM64 `svc #0` trap (single
`unsafe` block), safe high-level wrappers for all syscalls, phantom-typed
`Cap<Obj, Rts>` handles with sealed traits. 64 unit tests + 25 conformance tests.
Lean trace harness cross-validation (XVAL-001..004). Zero Lean regression.
**WS-Q9** (v0.17.14) — Integration testing + documentation — **COMPLETED**:
`TwoPhaseArchSuite.lean` with 14 integration tests (41 checks) covering the full
builder→freeze→execution pipeline (TPH-001 through TPH-014). Commutativity
property verified. Rust conformance XVAL-001..019 verified. SRG-001..010
verified. Full documentation sync across 15+ files. Scenario registry updated.
**WS-Q portfolio is now COMPLETE** (all 9 phases, 45 atomic units of work).
See [`MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md`](dev_history/audits/MASTER_PLAN_WS_Q_KERNEL_STATE_ARCHITECTURE.md).

The **WS-N** portfolio (Robin Hood hashing verified implementation) is **fully
complete** (v0.17.0–v0.17.5) — 5 phases (N1–N5, 122 subtasks): core types +
operations (N1, v0.17.1), invariant proofs (N2, v0.17.2), kernel API bridge
(N3, v0.17.3), CNode.slots integration (N4, v0.17.4), test coverage +
documentation (N5, v0.17.5). ~4,655 LoC, zero sorry/axiom.
See [`AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md).

The **WS-S** portfolio (Pre-Benchmark Strengthening) is **fully complete**
(v0.19.0–v0.19.6) — 7 phases (S1–S7), 83 sub-tasks addressing all findings from
dual comprehensive v0.18.7 audits (115+ findings, 0 Critical). All 5 High, 29
Medium, and 19 Low findings resolved. Closure report:
[`WS_S_CLOSURE_REPORT.md`](dev_history/audits/WS_S_CLOSURE_REPORT.md).

**WS-S testing practices introduced (S2):**
- **Structural assertions**: test determinism checks use `BEq Except` structural
  equality instead of `toString`-based string comparison. All 101 `reprStr`
  occurrences replaced with `toString`.
- **Builder-based test states**: `buildChecked` enforces 8 runtime invariant
  checks during test state construction; primary test states (`baseState`,
  `f2UntypedState`, `f2DeviceState`) use `buildChecked`.
- **Error-path coverage**: 11 error-path tests covering capability failures
  (rights attenuation, full CNode, deep CDT revoke) and lifecycle failures
  (region exhaustion, child ID collision, device untyped rejection).
- **Golden-output fixture management**: `test_tier2_trace.sh` provides enhanced
  diff reporting when `tests/fixtures/main_trace_smoke.expected` drifts.
- **Shared test helpers**: `Testing/Helpers.lean` module with `expectCond`,
  `expectError`, `expectOk` shared across test suites.
- **SimRestrictive platform variant** (S5-D): substantive contracts with timer
  monotonicity, 256 MiB RAM bound, and register write denial for testing.

The **WS-R** portfolio (Comprehensive Audit Remediation) is **fully complete**
(v0.18.0–v0.18.7) — 8 phases (R1–R8), 111 sub-tasks addressing all 82 findings from
[`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md).

The **next major milestone** is **Raspberry Pi 5 hardware binding**:
populating RPi5 platform stubs with hardware-validated contracts, implementing
ARMv8 multi-level page table walk, GIC-400 interrupt routing, ARM Generic Timer
binding, and verified boot sequence construction.

**S5-F: Pre-hardware-binding gate — BCM2712 address validation.** Before H3
begins, every address constant in `SeLe4n/Platform/RPi5/Board.lean` must be
cross-referenced against the BCM2712 ARM Peripherals datasheet. A validation
checklist is maintained in `Board.lean` (see the "BCM2712 Address Validation
Checklist" section). The gate requires all 14 constants to be marked "Validated"
with exact datasheet references (document title, revision, page number).

**WS-J1 (completed):** register-indexed authoritative
namespace migration with typed register wrappers, syscall argument decode layer,
and `CdtNodeId` cleanup (6 phases: J1-A through J1-F). **WS-J1-A completed (v0.15.4):**
replaced `RegName`/`RegValue` `abbrev Nat` definitions with typed wrapper structures,
added full instance suites, re-proved all machine lemmas, fixed downstream compilation.
**WS-J1-B completed (v0.15.5):** added `SyscallId`, `MessageInfo`, `SyscallDecodeResult`
types, total decode functions in `RegisterDecode.lean`, round-trip and determinism proofs,
`SyscallRegisterLayout` with ARM64 default, `MachineConfig.registerCount`, 3 new `KernelError`
variants.
**WS-J1-C completed (v0.15.6):** added `syscallEntry` top-level user-space entry point,
`lookupThreadRegisterContext` for TCB register context extraction, `dispatchSyscall` routing
through `SyscallGate`/`syscallInvoke`, `dispatchWithCap` per-syscall routing for all 13
syscalls, `syscallRequiredRight` total right mapping, `MachineConfig.registerCount` promoted
to configurable field; 5 soundness theorems proved.
**WS-J1-C audit refinements (v0.15.7):** CSpace/lifecycle/VSpace dispatch returns `illegalState`
for MR-dependent ops (full MR extraction deferred to WS-J1-E), `syscallEntry` accepts
`regCount` parameter for architectural bounds, `syscallEntry_implies_capability_held`
strengthened to full capability-resolution chain.
**WS-J1-D completed (v0.15.8):** invariant and information-flow integration for
decode path; `decodeSyscallArgs_preserves_lowEquivalent` NI theorem; capability
invariant preservation through `syscallEntry`; scheduler invariant preservation
through register decode; bridge theorems in Enforcement/Soundness and
InformationFlow/Invariant/Composition.
**WS-J1-E completed (v0.15.9):** testing and trace evidence — 18 negative
decode tests in `NegativeStateSuite.lean`; 5 register-decode trace scenarios
(RDT-002 through RDT-010) in `MainTraceHarness.lean`; 2 operation-chain tests
(`chain10RegisterDecodeMultiSyscall`, `chain11RegisterDecodeIpcTransfer`) in
`OperationChainSuite.lean`; fixture updates; 13 Tier 3 invariant surface
anchors for RegisterDecode definitions and theorems.
**WS-J1-F completed (v0.15.10):** CdtNodeId cleanup and documentation sync —
replaced `abbrev CdtNodeId := Nat` with `structure CdtNodeId where val : Nat`,
added full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`,
`LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`), fixed downstream
compilation in `SystemState` defaults and test literals, documentation synchronized.
**WS-J1 portfolio fully completed.** All 16 kernel identifiers are now typed wrappers.
WS-I1..WS-I4 are completed; WS-I5 Part A (R-12) is superseded by WS-J1.

### 3.1 WS-H11..H16 — v0.12.15 audit remediation status (completed)

See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-H11** | VSpace & architecture enrichment (PagePermissions, W^X, TLB model) | Medium | **Completed** |
| **WS-H12a** | Legacy endpoint field & operation removal | Medium | **Completed** |
| **WS-H12b** | Dequeue-on-dispatch scheduler semantics | Medium | **Completed** |
| **WS-H12c** | Per-TCB register context with inline context switch | Medium | **Completed** |
| **WS-H12d** | IPC message payload bounds | Medium | **Completed** |
| **WS-H12e** | Cross-subsystem invariant reconciliation | Medium | **Completed** |
| **WS-H12f** | Test harness update & documentation sync | Medium | **Completed** |
| **WS-H13** | CSpace/service model enrichment (multi-level resolution, backing-object verification, serviceCountBounded) | Medium | **Completed** |
| **WS-H14** | Type safety hardening: EquivBEq/LawfulBEq instances, LawfulMonad proofs, isPowerOfTwo verification, OfNat removal, sentinel completion | Low | **Completed** |
| **WS-H15** | Platform & API hardening (RPi5 contracts, syscall capability wrappers, AdapterProofHooks) | Low | **Completed** |
| **WS-H16** | Testing and documentation expansion | Low | Planned |

### 3.2 WS-F5..F8 — Remaining v0.12.2 audit remediation

See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md)
for the full execution plan.

| ID | Focus | Priority | Status |
|----|-------|----------|--------|
| **WS-F5** | Model fidelity (badge bitmask, per-thread regs, multi-level CSpace) | Medium | **Completed** |
| **WS-F6** | Invariant quality (tautology reclassification, adapter proof hooks) | Medium | **Completed** |
| **WS-F7** | Testing expansion (oracle, probe, fixtures) | Low | **Completed** |
| **WS-F8** | Cleanup (dead type constructors, extension labeling, finding closure) | Low | **Completed** |

### 3.3 Completed portfolios

- **WS-I3:** completed (v0.15.2). Test coverage expansion — new `tests/OperationChainSuite.lean` adds 6 multi-operation chain tests (retype→mint→revoke, send/send/receive FIFO, map/lookup/unmap/lookup, service start/stop dependency sequencing, copy/move/delete, notification badge accumulation), scheduler stress coverage (16-thread repeated scheduling, same-priority determinism, multi-domain isolation), and Tier 2 integration via `scripts/test_tier2_negative.sh`; `tests/InformationFlowSuite.lean` now includes declassification runtime checks for authorized downgrade, normal-flow rejection, policy-denied rejection, and 3-domain lattice behavior. Closes R-06/R-07/R-08. Declassification policy denial now reports a distinct `declassificationDenied` error in `declassifyStore` and suite expectations.
- **WS-I4:** completed (v0.15.3). Subsystem coverage expansion — `tests/OperationChainSuite.lean` now includes VSpace multi-ASID shared-page coherency and per-ASID-permission checks (R-09), IPC interleaved send ordering checks with three-sender FIFO + alternating send/receive validation (R-10), and lifecycle cascading revoke/authority-degradation chains over CDT-linked root→child→grandchild caps (R-11).
- **WS-I1:** completed (v0.15.0). Critical testing infrastructure — 17 inter-transition invariant assertions across all 13 trace functions (R-01), mandatory Tier 2 determinism validation (R-02), scenario ID traceability with 121 tagged trace lines, pipe-delimited fixture format, scenario registry YAML with Tier 0 validation (R-03). Phase 1 of the WS-I improvement portfolio. Closes R-01/R-02/R-03.
- **WS-F8:** completed. Cleanup — removed dead `ServiceStatus.failed`/`isolated` constructors, labeled Service subsystem as seLe4n extension with module docstrings (MED-17), closed F-14 (endpointInvariant already removed in WS-H12a), closed F-01 (legacy endpoint fields already removed in WS-H12a), closed MED-04 (domain lattice alive and exercised — finding misidentified). Completes 100% of v0.12.2 audit findings (33/33). Closes MED-04, MED-17, F-01, F-14, F-19.
- **WS-F7:** completed. Testing expansion — 4 new runtime invariant checks (`blockedOnSendNotRunnable`, `blockedOnReceiveNotRunnable`, `currentThreadInActiveDomain`, `uniqueWaiters`) added to `InvariantChecks.lean`; `TraceSequenceProbe` extended from 3 to 7 operation families (+ notification signal/wait, schedule, capability lookup) with blocked-thread guard; `runtimeContractTimerOnly` and `runtimeContractReadOnlyMemory` fixtures exercised in `MainTraceHarness` with 6 deterministic trace assertions; CDT `childMapConsistentCheck` confirmed already delivered. Zero sorry, zero axiom. Closes MED-08, F-24, F-25, F-26.
- **WS-F6:** completed (v0.14.9). Invariant quality — tautology reclassification, cross-subsystem coupling, adapter proof hooks. `capabilityInvariantBundle` reduced from 8-tuple to 6-tuple (removed tautological `cspaceInvariant`/`badgeInvariant`); `blockedOnNotificationNotRunnable` predicate added to `ipcSchedulerContractPredicates` (6-conjunct); `runnableThreadsAreTCBs` predicate added to `schedulerInvariantBundleFull` (6-conjunct) with 4 preservation theorems (`switchDomain`, `schedule`, `handleYield`, `timerTick`); `vspaceCrossAsidIsolation` added to `vspaceInvariantBundle` (6-conjunct) with `mapPage`/`unmapPage` proofs; `default_serviceCountBounded` and `default_serviceGraphInvariant` proved for service graph; bundle coherence verified across all subsystems. Zero sorry, zero axiom.
- **WS-H12f:** completed (v0.14.3). Test harness update & documentation sync — `runDequeueOnDispatchTrace` (dequeue-on-dispatch lifecycle with preemption re-enqueue), `runInlineContextSwitchTrace` (inline context save/restore verification through `handleYield` → `schedule`), `runBoundedMessageExtendedTrace` (zero-length, sub-boundary, max-caps acceptance); legacy `endpointInvariant` comment cleanup; expected fixture updated (108 lines); 9 new Tier 3 anchors; documentation synchronized. Completes WS-H12 composite workstream.
- **WS-H12e:** completed (v0.14.2). Cross-subsystem invariant reconciliation — `coreIpcInvariantBundle` upgraded from `ipcInvariant` to `ipcInvariantFull` (includes `dualQueueSystemInvariant` and `allPendingMessagesBounded`); `schedulerInvariantBundleFull` extended with `contextMatchesCurrent` (5-conjunct); `ipcSchedulerCouplingInvariantBundle` extended with `contextMatchesCurrent` and `currentThreadDequeueCoherent`; `proofLayerInvariantBundle` uses `schedulerInvariantBundleFull` (full bundle) instead of bare `schedulerInvariantBundle`; extraction theorems added; `switchDomain_preserves_contextMatchesCurrent` new preservation theorem; 8 `allPendingMessagesBounded` frame lemmas for primitive ops; 3 compound `*_preserves_allPendingMessagesBounded` theorems (notificationSignal, notificationWait, endpointReply); 7 composed `*_preserves_ipcInvariantFull` theorems for all IPC operations; all `*_preserves_schedulerInvariantBundleFull` theorems updated; default state proofs extended; Tier 3 invariant surface anchors updated. Completes deferred WS-H12d preservation theorems. Closes systemic invariant composition gaps from WS-H12a–d.
- **WS-H12d:** completed (v0.14.1). IPC message payload bounds — `IpcMessage` registers/caps migrated from `List` to `Array` with `maxMessageRegisters`(120)/`maxExtraCaps`(3), bounds enforcement at all 4 send boundaries, 4 `*_message_bounded` theorems, `allPendingMessagesBounded` system invariant, A-09 closed.
- **WS-H12c:** completed (v0.14.0). Per-TCB register context with inline context switch — `registerContext` field on TCB, `saveOutgoingContext`/`restoreIncomingContext` in `schedule`, information-flow projection strips register context, `endpointInvariant` removed, H-03 closed.
- **WS-H12b:** completed (v0.13.9). Dequeue-on-dispatch scheduler semantics — `queueCurrentConsistent` inverted from `current ∈ runnable` to `current ∉ runnable`, matching seL4's `switchToThread`/`tcbSchedDequeue`. `schedule` dequeues chosen thread before dispatch; `handleYield` inserts+rotates current thread before scheduling; `timerTick` re-enqueues on preemption; `switchDomain` re-enqueues before domain switch. Added `currentTimeSlicePositive` predicate to `schedulerInvariantBundleFull`; added `schedulerPriorityMatch` with `RunQueue.insert_preserves_wellFormed` and `insert_threadPriority` theorems. IPC predicates added: `currentThreadIpcReady`, `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, `currentThreadDequeueCoherent`. Helper lemmas `ensureRunnable_not_mem_of_not_mem`, `removeRunnable_not_mem_of_not_mem`, `ThreadId.ext`. ~1800 lines of preservation proofs re-proved. Closes H-04 (HIGH).
- **WS-H11:** completed (v0.13.7). VSpace & architecture enrichment — `PagePermissions` structure with `read`/`write`/`execute`/`user`/`cacheable` fields and `wxCompliant` W^X enforcement; `VSpaceRoot.mappings` enriched from `HashMap VAddr PAddr` to `HashMap VAddr (PAddr × PagePermissions)`; `vspaceMapPage` enforces W^X at insertion (`policyDenied` on violation); `vspaceLookupFull` returns `(PAddr × PagePermissions)`; `vspaceInvariantBundle` extended from 3 to 5 conjuncts (`wxExclusiveInvariant`, `boundedAddressTranslation` integrated); `VSpaceBackend` typeclass enriched with permissions; `MemoryRegion.wellFormed` and `MachineConfig.wellFormed` enforce `endAddr ≤ 2^physicalAddressWidth`; `TlbState`/`TlbEntry` abstract TLB model with `adapterFlushTlb`/`adapterFlushTlbByAsid` operations; `tlbConsistent` invariant with flush-restoration and composition theorems. Closes H-02/A-32 (HIGH), H-10 (HIGH), A-05/M-12 (HIGH), A-12 (HIGH), M-14 (MEDIUM).
- **WS-H10:** completed (v0.13.6). Security model foundations — `ObservableState` extended with `machineRegs` (domain-gated register file projection); machine timer excluded as covert timing channel; `bibaIntegrityFlowsTo`/`bibaSecurityFlowsTo`/`bibaPolicy` standard BIBA alternatives with refl/trans proofs; `DeclassificationPolicy` with `declassifyStore` enforcement operation (5 theorems) and `declassifyStore_NI` non-interference proof; `endpointFlowPolicyWellFormed` predicate with reflexivity/transitivity inheritance proofs; `InformationFlowConfigInvariant` bundle. Closes C-05/A-38 (CRITICAL), A-34 (CRITICAL), A-39 (MEDIUM), M-16 (MEDIUM). 866 proved declarations.
- **WS-H7/H8/H9 gap closure:** completed (v0.13.5). Comprehensive audit remediation — `VSpaceRoot.beq_sound`/`CNode.beq_sound` BEq soundness lemmas (WS-H7), `endpointReceiveDualChecked_NI` enforcement bridge (WS-H8), `endpointReceiveDual_preserves_lowEquivalent`/`endpointCall_preserves_lowEquivalent`/`endpointReplyRecv_preserves_lowEquivalent` hypothesis-based IPC NI theorems (WS-H9), `NonInterferenceStep` extended to 31 constructors with `endpointReceiveDualHigh`/`endpointCallHigh`/`endpointReplyRecvHigh`. 840 proved declarations.
- **WS-H9:** completed (v0.13.4). Non-interference coverage extension >80% of kernel operations — 27 new NI preservation theorems, `NonInterferenceStep` extended from 11 to 28 constructors, scheduler/IPC/CSpace/VSpace/observable-state NI proofs, `switchDomain_preserves_lowEquivalent` two-sided proof, `composedNonInterference_trace` covers all constructors. Closes C-02/A-40 (CRITICAL), M-15 (MEDIUM).
- **WS-H8:** completed (v0.13.2). Enforcement-NI bridge & missing wrappers — enforcement soundness meta-theorems connecting `securityFlowsTo` checks to non-interference; 4 new policy-checked wrappers (`notificationSignalChecked`, `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked`); `ObservableState` extended with domain timing metadata (`domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`); NI bridge theorems for all new wrappers. Closes A-35/H-07 (CRITICAL), H-07 (HIGH), A-36/A-37/H-11 (HIGH). 26 new theorems; 779 total.
- **WS-H6:** completed (v0.13.1). Scheduler proof completion — `timeSlicePositive` preservation proven for all 6 scheduler operations (`setCurrentThread`, `chooseThread`, `schedule`, `handleYield`, `switchDomain`, `timerTick`); `edfCurrentHasEarliestDeadline` fixed to be domain-aware (closing false-assurance gap); `chooseBestRunnableBy_optimal` (fold-based candidate optimality), `noBetter_implies_edf` (bridge to EDF invariant), `isBetterCandidate_not_better_trans` (negation transitivity); `schedulerInvariantBundleFull` (5-tuple bundle with projection and composition); plus earlier Part D/E work (`flat_wf_rev`, `mem_toList_iff_mem`, `isBetterCandidate_transitive`, `bucketFirst_fullScan_equivalence`).
- **WS-H7:** completed (v0.12.21). HashMap equality + state-store migration — `BEq VSpaceRoot`/`BEq CNode` switched from `toList` order-sensitive checks to size+fold order-independent checks; `services`, `irqHandlers`, `lifecycle.capabilityRefs`, `cdtSlotNode`, and `cdtNodeSlot` migrated from closure functions to `Std.HashMap`, removing O(k) closure-chain accumulation.
- **WS-H5:** completed (v0.12.19). IPC dual-queue structural invariant — `intrusiveQueueWellFormed`, `dualQueueSystemInvariant`, `tcbQueueLinkIntegrity`; 13 preservation theorems for all dual-queue operations. Closes C-04/A-22 (CRITICAL), A-23 (HIGH), A-24 (HIGH). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H4:** completed (v0.12.18). Capability invariant redesign — `capabilityInvariantBundle` extended from trivially-true 4-tuple to meaningful 7-tuple with `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`. All preservation theorems re-proved. C-03, M-08/A-20, M-03. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H3:** completed (v0.12.17). Build/CI infrastructure fixes — `run_check` return value fix (H-12), `test_docs_sync.sh` CI integration (M-19), Tier 3 `rg` availability guard with `grep -P` fallback (M-20). See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H2:** completed (v0.12.16). Lifecycle safety guards — childId collision/self-overwrite guards, TCB scheduler cleanup on retype, CNode CDT detach, atomic retype. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-H1:** completed (v0.12.16). IPC call-path semantic fix — `blockedOnCall` variant, reply-target scoping, 5-conjunct `ipcSchedulerContractPredicates`. See [`docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md).
- **WS-G1..G9:** all completed (v0.12.6–v0.12.15). See [`docs/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md`](dev_history/audits/KERNEL_PERFORMANCE_WORKSTREAM_PLAN.md).
- **WS-F1..F4:** completed. See [`docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`](dev_history/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md).
- **WS-E1..E6:** all completed (historical archive).
- **WS-D1..D4:** completed (historical archive).
- **WS-C1..C8:** completed (historical archive).

### 3.4 PR-to-workstream discipline

Every milestone-moving PR should include:

1. workstream ID(s) advanced,
2. objective and exit-criterion delta,
3. command evidence,
4. synchronized docs updates (README/spec/development/GitBook as needed),
5. explicit deferrals (if any) and destination workstream.

---

## 4) Security hardening defaults

- IPC thread-state updates now fail with `objectNotFound` when the target TCB is missing (including reserved thread ID `0`), preventing ghost queue entries in endpoint/notification paths.
- Sentinel ID `0` is rejected at IPC TCB lookup/update boundaries (`lookupTcb`/`storeTcbIpcState`) rather than silently treated as a valid runtime thread identity.
- Trace and probe harnesses now exercise policy-checked wrappers (`endpointSendDualChecked`, `cspaceMintChecked`, `registerServiceChecked`) by default; unchecked operations remain available for research experiments. `enforcementBoundary` classifies 42 operations (12 policy-gated, 26 capability-only, 4 read-only; pinned by `enforcementBoundaryExtended_count`). (WS-Q1: `serviceRestartChecked` removed, `registerServiceChecked` added; WS-Z8: SchedContext ops; D1: thread lifecycle; D2: priority management; D3: IPC buffer; AC4-D: VSpace/service ops; WS-SM SM8.C: the live declassification entry point, policy-gated; WS-SM SM8.E.3: the SM3 two-phase-locking bracket `withLockSet`, capability-only; WS-SM SM9.A.11: the two audit-trail readers `auditReadFromCore` / `auditDrainVisiblePrefix`, capability-only.)
- WS-E4 dual-queue endpoint operations (`endpointSendDual`/`endpointReceiveDual`) use intrusive-list queue boundaries (`sendQ`/`receiveQ`) with per-thread links stored in `TCB.queuePrev`/`TCB.queuePPrev`/`TCB.queueNext`; invariant checks now include `intrusiveQueueWellFormed` validation for both endpoint queues (including head/tail shape, cycle-free traversal, and per-node `queuePrev`/`queuePPrev`/`queueNext` linkage), and `negative_state_suite` adds runtime queue-link assertions for both send-queue and receive-queue FIFO/dequeue paths alongside enqueue/block, rendezvous/dequeue, queue drain, O(1) middle removal via `endpointQueueRemoveDual`, malformed-`queuePPrev` rejection (`illegalState`), and dual-queue double-wait rejection (`alreadyWaiting`).
- WS-E4 CDT representation is node-stable: derivation edges are over stable node IDs and slots map to nodes via bidirectional maps (`cdtSlotNode`, `cdtNodeSlot`). `cspaceMove` updates slot→node ownership/backpointers instead of rewriting every CDT edge, `cspaceDeleteSlot` detaches stale slot↔node mappings on deletion, the observed slot-level CDT is defined as projection of node edges through the slot mapping (`SystemState.observedCdtEdges`), and strict revoke (`cspaceRevokeCdtStrict`) now reports the first descendant deletion failure with offending slot context.

## 5) Daily contributor loop

1. Sync branch and choose one coherent slice from the active plans (currently Raspberry Pi 5 hardware binding — all pre-hardware workstreams WS-B through WS-AB are complete).
2. Implement the minimal semantic/proof/doc delta.
3. Run smallest relevant check first, then higher tiers.
4. Update docs in the same commit range.
5. Re-run validation before commit.

Recommended command loop:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
```

Optional nightly/staged checks:

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Module-specific build targets (SchedContext):

```bash
# SchedContext module
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Types
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Budget
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Invariant.Defs
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Invariant
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Invariant.Preservation
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Operations
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.ReplenishQueue
source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext
# Cross-subsystem (includes SchedContext predicates)
source ~/.elan/env && lake build SeLe4n.Kernel.CrossSubsystem
```

Environment note for `./scripts/setup_lean_env.sh` on apt-based systems:

- if a third-party apt mirror is temporarily unavailable, the setup script now retries `apt-get update` with primary distro sources only so required tool installs (`shellcheck`, `ripgrep`) remain reproducible.
- **AF6-F**: `shellcheck` is now installed explicitly in CI (`lean_action_ci.yml`) so Tier 0 hygiene shell lint is always enforced rather than silently skipped when the tool is unavailable.

---

## 5a) Known performance characteristics (WS-AC/AC2)

The following operations have known complexity characteristics documented for
hardware deployment planning. All are correct but may require optimization
when hardware profiling data is available.

| Operation | Complexity | Trigger Frequency | Location |
|-----------|-----------|-------------------|----------|
| `timeoutBlockedThreads` | O(1) lookup + O(k) per bound threads | Once per CBS period on budget exhaustion | `Core.lean` |
| `RunQueue.insert` | O(n) in queue size | Every enqueue (preemption, unblock) | `RunQueue.lean` |
| `RunQueue.remove` | O(k + n), k = bucket size | Every dequeue (dispatch, block) | `RunQueue.lean` |
| `RunQueue.rotateToBack` | O(k + n) | Round-robin rotation within priority band | `RunQueue.lean` |
| `recomputeMaxPriority` | O(p), p = priority levels | On removal when max-priority bucket empties | `RunQueue.lean` |

All O(n) operations are acceptable for the RPi5 target (n ≤ 256 threads at
steady state, ≤ 65536 objects). A dedicated performance workstream (WS-AD)
will address these with hardware profiling data if needed.

## 5b) Audit-driven coding conventions (WS-AC)

1. **`KernelError` match hygiene (F-04)**: Prefer explicit match arms over
   `| _ =>` catch-all patterns on `KernelError`. Lean's exhaustiveness checker
   flags missing arms, but catch-alls silently swallow new variants. Use
   `| _ =>` only for genuinely uniform error handling (e.g., error-to-string
   conversion).

2. **Multi-step mutation atomicity (I-02)**: Functions that perform multiple
   sequential `storeObject` calls (e.g., `donateSchedContext`) operate within
   the `KernelM` `Except` monad. On `.error`, the monad's bind discards all
   intermediate state — callers receive only the error value, not a partial
   state. Document multi-step mutation sequences with the step order and
   failure semantics.

3. **Identifier `Nat` unboundedness (F-01)**: All typed identifiers (`ThreadId`,
   `ObjId`, etc.) wrap unbounded `Nat`. This is by design for proof ergonomics.
   The ABI boundary (`RegisterDecode.lean` + `SyscallArgDecode.lean`) validates
   all incoming values. Internal kernel code is trusted to produce valid IDs.

4. **`storeObject` vs `storeObjectChecked` (F-03/AC3-E/AF2-A)**: Use
   `storeObjectChecked` in new code paths that are not covered by the
   `retypeFromUntyped` capacity gate. `storeObjectChecked` rejects new object
   insertions when the store reaches `maxObjects` (65536) capacity. Use
   `storeObject` only in proof-layer code where `objectIndexBounded` is an
   established precondition, or for in-place updates of existing objects.
   **Machine-checked capacity safety (AF2-A)**: Two theorems provide full
   assurance: `storeObject_existing_preserves_objectIndex_length` (in-place
   mutations don't grow `objectIndex`) and `retypeFromUntyped_capacity_gated`
   (allocation boundary gates on `maxObjects`). See `storeObject_capacity_safe_of_existing`
   for the composition.

5. **`AccessRightSet` constructor safety (F-02/AC4-B)**: Never use
   `AccessRightSet.mk` or `⟨n⟩` directly in production code. Use `ofNat`
   (masked to 5 bits), `mk_checked` (proof-carrying), `ofList`, `singleton`,
   or `empty`. The `union` and `inter` operations return raw `⟨bits⟩` without
   masking — apply `ofNat` to the result if downstream validity is required.

6. **Physical address bounds (A-04/AC4-A)**: Production VSpace map operations
   must use `vspaceMapPageCheckedWithFlushFromState` (state-aware, reads
   `st.machine.physicalAddressWidth`). The model-level `physicalAddressBound`
   (2^52, ARM64 LPA max) is for proof-layer reasoning only. The syscall
   dispatch path (API.lean) already wires through the state-aware variant.

7. **Enforcement boundary completeness (IF-01/AC4-D)**: When adding a new
   `SyscallId` variant, you must also: (a) add it to `SyscallId.all`, (b)
   add a case to `syscallIdToEnforcementName` in Wrappers.lean, and (c)
   ensure the mapped name appears in `enforcementBoundary`. The compile-time
   `enforcementBoundary_is_complete` theorem (`native_decide`) will fail the
   build if any of these steps are missed.

8. **Cross-subsystem field disjointness (X-05/AC5-A)**: When adding a new
   cross-subsystem predicate to `CrossSubsystem.lean`, you must: (a) declare
   its `_fields` read-set, (b) add pairwise `fieldsDisjoint`/`fieldsShared`
   theorems for every existing predicate (C(n,2) pairs total), and (c) verify
   the `crossSubsystem_pairwise_coverage_complete` summary theorem still
   compiles. The `by decide` / `native_decide` proofs catch field-set errors
   at compile time.

9. **`AccessRightSet` operational safety (F-02/AC5-E)**: `subset` is sound
   even for invalid sets (`subset_sound`); `inter` preserves validity when
   the left operand is valid (`inter_valid`); membership checks are
   bounded to bits 0..4 (`mem_bit_bounded`). These machine-checked theorems
   confirm that bitwise operations on `AccessRightSet` cannot produce
   incorrect results, even when raw `.mk` constructors are used.

10. **Decode layer test coverage (T-03/AC6-A)**: Both decode layers
    (`RegisterDecode.lean` and `SyscallArgDecode.lean`) must have dedicated
    test coverage in `tests/DecodingSuite.lean`. When adding a new syscall
    decode function, add corresponding tests covering: (a) valid decode with
    correct register values, (b) insufficient register count, and (c) any
    domain-specific validation failures (e.g., invalid type tags, out-of-range
    priorities, misaligned addresses). The suite runs as part of Tier 2.

---

## 6) Proof engineering standards

1. Keep proofs local-first; compose afterward.
2. Prefer explicit theorem statements and stable names.
3. Keep invariant bundles factored and named.
   - Current canonical IPC composition names:
     - `coreIpcInvariantBundle`
     - `ipcSchedulerCouplingInvariantBundle`
     - `lifecycleCompositionInvariantBundle`
   - Current canonical trace helper names for these slices:
     - `runCapabilityIpcTrace`
     - `runSchedulerTimingDomainTrace`
4. Avoid hidden global simplification behavior.
5. Never add `axiom`/`sorry` to core proof surfaces.
6. BFS completeness proof (TPI-D07-BRIDGE): formally resolved. The core
   completeness theorem (CP1), its equational lemmas (EQ1-EQ5), and closure
   lemmas (CB1-CB4) are all proved. The prerequisite lemma hierarchy in
   [`M2_BFS_SOUNDNESS.md §6`](dev_history/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md)
   and its sub-documents ([M2A](dev_history/audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)–[M2D](dev_history/audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md))
   is fully discharged. No further work is required for this tracking item.

---

## 7) Documentation synchronization rules

For changes that alter behavior, theorem surfaces, or slice status, update in the same PR:

1. `README.md`
2. `docs/spec/SELE4N_SPEC.md` (and `docs/spec/SEL4_SPEC.md` if seL4 reference material changes)
3. `docs/DEVELOPMENT.md`
4. impacted GitBook chapter(s) and `docs/gitbook/SUMMARY.md` if IA changes
5. any directly affected audit/workstream status document

Use [`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](./DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md)
for cross-document synchronization expectations.

Before touching any `Current state` numbers, run `./scripts/report_current_state.py`
and propagate the output verbatim to README/spec/GitBook mirrors in the same PR.
At minimum keep these attributes synchronized across all three surfaces: version,
Lean toolchain, production/test LoC, theorem+lemma count, build jobs, active
findings/audit references, and completed/next workstream status.

For codebase-map synchronization, run `./scripts/generate_codebase_map.py --pretty`
whenever Lean module/declaration surfaces change, then validate with
`./scripts/generate_codebase_map.py --pretty --check`. The generated
`docs/codebase_map.json` contains:

- **`readme_sync`** — project-level metrics (version, LoC, theorem count,
  hardware target) used by README.md, SELE4N_SPEC.md, and GitBook chapters.
- **`source_sync`** — stable `source_digest` (SHA256 over Lean source paths +
  contents) plus volatile `repository.head` git metadata.
- **`modules`** — per-module declaration inventory. Each declaration record
  includes an additive `called` array listing in-module declaration references
  (or `[]` when none are detected).

Website clients should invalidate local cache entries on
`source_sync.source_digest` changes. `--check` compares only the stable subset,
keeping CI robust across branch/merge-only commits while still detecting real
declaration-surface drift. Post-merge enforcement runs in
`.github/workflows/codebase_map_sync.yml`, which auto-regenerates and commits
the map on `main` when drift is detected.

### Test fixture update process (WS-L5-B)

When adding new trace scenarios to `MainTraceHarness.lean`:

1. Add `IO.println` calls with `[PREFIX-NNN]` scenario IDs.
2. Rebuild: `lake build`.
3. Run `lake exe sele4n` and verify new output lines appear.
4. Add fixture expectations to `tests/fixtures/main_trace_smoke.expected` using
   the format: `PREFIX-NNN | SUBSYSTEM | expected_trace_fragment`.
5. Add scenario registry entries to `tests/fixtures/scenario_registry.yaml` with
   `source`, `function`, `subsystem`, and `description` fields.
6. If the inter-transition invariant check count changes (ITR-001), update the
   count in both the fixture file and the scenario registry.
7. Validate: `./scripts/test_smoke.sh` (includes Tier 0 registry validation +
   Tier 2 fixture comparison).

### Golden-output fixture management (S2-D)

The `tests/fixtures/main_trace_smoke.expected` file is the golden fixture for
the kernel's executable trace output. Changes to this file require explicit
rationale because they indicate behavioral changes in kernel transitions.

**When to update the fixture:**
- Adding new trace scenarios (new kernel operations or test paths)
- Changing kernel transition semantics that affect trace output
- Modifying the trace format (e.g., scenario ID prefixes)

**When NOT to update the fixture:**
- A test fails unexpectedly — investigate the root cause first
- Cosmetic changes to non-trace output (e.g., `Repr` instances)

**Update procedure:**
1. Run `lake exe sele4n > /tmp/actual_trace.log` to capture actual output
2. Compare: `diff tests/fixtures/main_trace_smoke.expected /tmp/actual_trace.log`
3. Review each changed line — every difference should correspond to an
   intentional behavioral change
4. Update the fixture with the new expected output
5. Document the rationale in the commit message (e.g., "Update fixture: added
   S3-F RunQueue.remove well-formedness trace scenario")
6. Run `./scripts/test_smoke.sh` to verify the updated fixture passes

**Test assertions:** All test suites use structural equality (`BEq`/`DecidableEq`)
for comparison logic, not `reprStr` or `toString`. The `reprStr` function is
used only in diagnostic error messages when a test fails, not in the comparison
itself (S2-A). This ensures test stability across `Repr` instance changes.

### Metrics regeneration process (WS-L5-C)

When modifying production Lean source files:

1. Run `./scripts/report_current_state.py` to get updated metrics.
2. Update metrics in `README.md`, `docs/spec/SELE4N_SPEC.md`, and
   `docs/gitbook/05-specification-and-roadmap.md` — all three must match.
3. Run `./scripts/generate_codebase_map.py --pretty --output docs/codebase_map.json`
   to regenerate the machine-readable map.
4. Validate with `./scripts/generate_codebase_map.py --pretty --check`.
5. Verify: `./scripts/test_docs_sync.sh` (checks codebase map freshness).

---

## 8) Definition of done (milestone-moving changes)

A change is done when all are true:

- implementation compiles,
- trace/fixture behavior is intentionally stable or intentionally updated with rationale,
- theorem/invariant surface remains coherent and discoverable,
- tiered checks pass for the claimed scope,
- docs reflect exact current state (not intended future state).

---

## 9) Quick checklist (copy into PRs)

- [ ] Workstream ID(s) identified.
- [ ] Scope is one coherent slice.
- [ ] Transition semantics are explicit and deterministic.
- [ ] Invariant/theorem updates are paired with implementation changes.
- [ ] Required validation commands were run.
- [ ] Documentation was synchronized.
