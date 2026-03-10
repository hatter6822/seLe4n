# Proof and Invariant Map

This chapter summarizes how theorem surfaces are organized and how they compose across milestones.

## 1. Layered invariant philosophy

seLe4n invariants are intentionally layered:

1. **component invariants** describe one focused safety condition,
2. **subsystem bundles** combine related components,
3. **cross-subsystem bundles** compose milestone contracts.

This keeps proof scripts reviewable and reduces blast radius when adding new transitions.

## 2. Scheduler invariants (M1)

Component level:

- `runQueueUnique`
- `currentThreadValid`
- `queueCurrentConsistent` (WS-H12b: inverted to `current ∉ runnable`, matching seL4 dequeue-on-dispatch)
- `currentTimeSlicePositive` (WS-H12b: current thread time slice positive, since current is not in run queue)
- `schedulerPriorityMatch` (WS-H12b: priority consistency for run queue threads)

Data structure:

- `RunQueue` (`Scheduler/RunQueue.lean`, WS-G4 + WS-H6) — priority-bucketed run queue with bidirectional structural invariants `flat_wf` and `flat_wf_rev`, plus bridge lemmas `membership_implies_flat` and `mem_toList_iff_mem` between O(1) `Std.HashSet` membership and `flat : List ThreadId`/`toList` reasoning. `chooseBestInBucket` bucket-first scheduling: O(k) max-priority bucket scan with full-list fallback. `remove` computes filtered bucket once for both `byPriority` and `maxPriority` (v0.12.15 refinement). Implicit `membership` ↔ `threadPriority` consistency maintained by insert/remove API (runtime-verified by `runQueueThreadPriorityConsistentB`).
- 13 bridge lemmas: `mem_insert`, `mem_remove`, `mem_rotateHead`, `mem_rotateToBack`, `not_mem_empty`, `toList_insert_not_mem`, `toList_filter_insert_neg`, `toList_filter_remove_neg`, `not_mem_toList_of_not_mem`, `not_mem_remove_toList`, `mem_toList_rotateToBack_self`, `toList_rotateToBack_nodup`, `mem_toList_rotateToBack_ne`.

Bundle level:

- `schedulerInvariantBundle` (alias over `kernelInvariant`)
- `schedulerInvariantBundleFull` (5-conjunct: `schedulerInvariantBundle ∧ timeSlicePositive ∧ currentTimeSlicePositive ∧ edfCurrentHasEarliestDeadline ∧ contextMatchesCurrent`, WS-H12b + WS-H12e)

Extraction theorem:

- `schedulerInvariantBundleFull_to_contextMatchesCurrent` — extracts `contextMatchesCurrent` from the 5-conjunct bundle (WS-H12e)

Preservation shape:

- `chooseThread_preserves_*`
- `schedule_preserves_*`
- `handleYield_preserves_*`
- `timerTick_preserves_schedulerInvariantBundle` (WS-F4 / F-03)
- `timerTick_preserves_kernelInvariant` (WS-F4 / F-03)
- `isBetterCandidate_transitive` (WS-H6 / A-17)
- `bucketFirst_fullScan_equivalence` (WS-H6 / A-17)

## 3. Capability invariants (M2)

Component level:

- `cspaceSlotUnique` — structural CNode slot-index uniqueness (reformulated in WS-E2; WS-G5: trivially true with `Std.HashMap` key uniqueness),
- `cspaceLookupSound` — lookup completeness grounded in slot membership (reformulated in WS-E2; non-tautological),
- `cspaceAttenuationRule` — minted capabilities attenuate rights,
- `lifecycleAuthorityMonotonicity` — authority only decreases through lifecycle operations.

Bridge theorem: `cspaceLookupSound_of_cspaceSlotUnique` derives lookup soundness from slot uniqueness.

Bundle level:

- `capabilityInvariantBundle` (WS-H4 + WS-H13: 8-tuple conjunction — `cspaceSlotUnique`, `cspaceLookupSound`, `cspaceAttenuationRule`, `lifecycleAuthorityMonotonicity`, `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`, `cspaceDepthConsistent`)
- `capabilityInvariantBundle_of_slotUnique` (constructor; requires all CNodes satisfy `slotsUnique` plus WS-H4 components)

Preservation shape:

- operation-level `*_preserves_capabilityInvariantBundle` for insert/delete/revoke (compositional: pre-state → post-state),
- `cspaceMutate_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- `cspaceRevokeCdt_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- `cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- IPC-level preservation for endpoint send/receive/await-receive/reply (compositional),
- lifecycle preservation with `hNewObjCNodeUniq` + `hNewObjCNodeBounded` hypotheses (WS-H4).

WS-H4 transfer theorems (new):

- `cdtPredicates_through_blocking_path` — storeObject(.endpoint) → storeTcbIpcState → removeRunnable,
- `cdtPredicates_through_handshake_path` — storeObject(.endpoint) → storeTcbIpcState → ensureRunnable,
- `cdtPredicates_through_reply_path` — storeTcbIpcStateAndMessage → ensureRunnable.

Badge routing chain (H-03):

- `mintDerivedCap_badge_propagated` → `cspaceMint_child_badge_preserved` → `notificationSignal_badge_stored_fresh` → `notificationWait_recovers_pending_badge`
- End-to-end: `badge_notification_routing_consistent`
- Merge property: `badge_merge_idempotent`

CDT structural invariants (WS-G8):

- `childMapConsistent` — bidirectional consistency between `edges` and `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed index,
- `empty_childMapConsistent` — empty CDT satisfies `childMapConsistent`,
- `addEdge_childMapConsistent` — `addEdge` preserves `childMapConsistent`,
- `childrenOf` — O(1) HashMap lookup replacing O(E) edge-list scan,
- `descendantsOf` — O(N+E) total via `childrenOf`-backed BFS traversal.
- `cdtChildMapConsistentCheck` — runtime verification of `childMapConsistent` invariant (v0.12.15), checking both forward (childMap→edges) and backward (edges→childMap) directions.

## 4. IPC invariants (M3)

Module structure:

- `IPC/Operations.lean` (re-export hub) — core endpoint/notification ops (`Operations/Endpoint.lean`) and scheduler preservation lemmas (`Operations/SchedulerLemmas.lean`),
- `IPC/DualQueue.lean` (re-export hub) — dual-queue operations (`DualQueue/Core.lean`: queue links, PopHead/Enqueue/RemoveDual, SendDual, ReceiveDual, Call, Reply, ReplyRecv) and transport lemmas (`DualQueue/Transport.lean`),
- `IPC/Invariant.lean` (re-export hub) — definitions (`Invariant/Defs.lean`), endpoint preservation (`Invariant/EndpointPreservation.lean`), call/replyRecv preservation (`Invariant/CallReplyRecv.lean`), notification preservation (`Invariant/NotificationPreservation.lean`), structural invariants and composition (`Invariant/Structural.lean`).

### 4.1 Dual-queue structural invariant (WS-H5)

`dualQueueSystemInvariant st` — system-wide structural invariant for intrusive dual-queue endpoints:

- `dualQueueEndpointWellFormed` — per-endpoint: both `sendQ` and `receiveQ` satisfy `intrusiveQueueWellFormed` (head/tail emptiness iff, head.prev=none, tail.next=none),
- `tcbQueueLinkIntegrity` — per-TCB: forward link consistency (`a.next=b → b.prev=a`) and reverse link consistency (`b.prev=a → a.next=b`).

Primitive preservation:

- `endpointQueuePopHead_preserves_dualQueueSystemInvariant`,
- `endpointQueueEnqueue_preserves_dualQueueSystemInvariant`.

Frame lemmas (non-queue-mutating operations):

- `ensureRunnable_preserves_dualQueueSystemInvariant`, `removeRunnable_preserves_dualQueueSystemInvariant`,
- `storeObject_tcb_preserves_dualQueueSystemInvariant`, `storeObject_endpoint_preserves_dualQueueSystemInvariant`,
- `storeTcbIpcState_preserves_dualQueueSystemInvariant`, `storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant`, `storeTcbPendingMessage_preserves_dualQueueSystemInvariant`.

Composite preservation (all 6 compound IPC operations):

- `endpointSendDual_preserves_dualQueueSystemInvariant`,
- `endpointReceiveDual_preserves_dualQueueSystemInvariant`,
- `endpointCall_preserves_dualQueueSystemInvariant`,
- `endpointReply_preserves_dualQueueSystemInvariant`,
- ~~`endpointAwaitReceive_preserves_dualQueueSystemInvariant`~~ (removed in WS-H12a),
- `endpointReplyRecv_preserves_dualQueueSystemInvariant`.

Helper lemmas: `storeTcbQueueLinks_noprevnext_preserves_linkInteg`, `storeTcbQueueLinks_append_tail_preserves_linkInteg`, `storeTcbQueueLinks_endpoint_backward`.

Bundle level:

- `ipcInvariantFull` (3-conjunct: `ipcInvariant ∧ dualQueueSystemInvariant ∧ allPendingMessagesBounded`, WS-H12c + WS-H12d)

Cross-subsystem composition (WS-H12e):

- `coreIpcInvariantBundle` — upgraded from `ipcInvariant` to `ipcInvariantFull` (3-conjunct), closing the gap where `dualQueueSystemInvariant` and `allPendingMessagesBounded` were defined but not composed into the cross-subsystem proof surface
- Backward-compatible extraction theorems: `coreIpcInvariantBundle_to_ipcInvariant`, `coreIpcInvariantBundle_to_dualQueueSystemInvariant`, `coreIpcInvariantBundle_to_allPendingMessagesBounded`

Component level:

- `ipcInvariant` — notification queue well-formedness across object store,
- `dualQueueSystemInvariant` — per-endpoint dual-queue well-formedness + system-wide TCB link integrity,
- `allPendingMessagesBounded` — all pending IPC messages satisfy payload bounds.

Preservation shape:

- transition-level `endpointSendDual_preserves_ipcInvariant`, etc.
- WS-F1 dual-queue: `endpointSendDual_preserves_ipcInvariant`, `endpointReceiveDual_preserves_ipcInvariant`, `endpointQueueRemoveDual_preserves_ipcInvariant` (TPI-D08).
- WS-F1 compound: `endpointCall_preserves_ipcInvariant`, `endpointReplyRecv_preserves_ipcInvariant`, `endpointReply_preserves_ipcSchedulerContractPredicates` (TPI-D09).
- WS-F4 notification: `notificationSignal_preserves_ipcInvariant`, `notificationSignal_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle` (F-12).
- WS-F4 notification contract predicates: `notificationSignal_preserves_ipcSchedulerContractPredicates`, `notificationWait_preserves_ipcSchedulerContractPredicates` (M3.5 gap closure).
- WS-H5 dual-queue structural invariant: 13 `*_preserves_dualQueueSystemInvariant` theorems covering `endpointQueuePopHead`, `endpointQueueEnqueue`, `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`, plus 5 state-only ops (`ensureRunnable`, `removeRunnable`, `storeTcbIpcState`, `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`).

### 4.2 IPC message payload bounds (WS-H12d)

`IpcMessage` registers and caps bounded to `Array` with `maxMessageRegisters` (120) and `maxExtraCaps` (3), matching seL4's `seL4_MsgMaxLength` and `seL4_MsgMaxExtraCaps`.

Predicate level:

- `IpcMessage.bounded` — `registers.size ≤ maxMessageRegisters ∧ caps.size ≤ maxExtraCaps`,
- `IpcMessage.checkBounds` — decidable runtime check,
- `checkBounds_iff_bounded` — decidability bridge theorem,
- `empty_bounded` — base case theorem.

System invariant:

- `allPendingMessagesBounded` — all pending messages in TCBs satisfy `bounded`.

Bounds enforcement (at all 4 send boundaries):

- `endpointSendDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv` — early-exit with `ipcMessageTooLarge` / `ipcMessageTooManyCaps` errors.

Message-bounded theorems:

- `endpointSendDual_message_bounded`, `endpointCall_message_bounded`, `endpointReply_message_bounded`, `endpointReplyRecv_message_bounded` — any successfully sent message satisfies `bounded`.

Information-flow:

- `endpointSendDualChecked` — bounds checks precede flow checks; `enforcement_sufficiency_endpointSendDual` expanded to 4-way disjunction.

## 5. IPC-scheduler coherence (M3.5)

Component level:

- runnable threads should be IPC-ready,
- blocked-on-send threads should not remain runnable,
- blocked-on-receive threads should not remain runnable,
- blocked-on-call threads should not remain runnable (WS-H1),
- blocked-on-reply threads should not remain runnable (WS-H1).

Bundle level:

- `ipcSchedulerContractPredicates` (5 conjuncts: ready, send, receive, call, reply)
- `ipcSchedulerCoherenceComponent`
- `ipcSchedulerCouplingInvariantBundle` (WS-H12e: extended from 2 to 4 conjuncts — `coreIpcInvariantBundle ∧ ipcSchedulerCoherenceComponent ∧ contextMatchesCurrent ∧ currentThreadDequeueCoherent`)

Preservation shape:

- local component preservation theorem per transition,
- composed contract preservation theorem per transition,
- bundle preservation theorem per transition.

## 6. Naming conventions and why they matter

Preferred shape:

- `<transition>_preserves_<componentOrBundle>`

Why:

- searchable theorem entrypoints,
- stable doc/test anchors,
- predictable maintainability under milestone growth.

## 7. M4 lifecycle invariant layering (M4-A complete, M4-B WS-B complete)

Current M4-A lifecycle invariant structure now follows the existing layered style:

1. identity/aliasing components (`lifecycleIdentityTypeExact`, `lifecycleIdentityNoTypeAliasConflict`),
2. identity bundle (`lifecycleIdentityAliasingInvariant`),
3. capability-reference components (`lifecycleCapabilityRefExact`, `lifecycleCapabilityRefObjectTargetBacked`),
4. capability-reference bundle (`lifecycleCapabilityReferenceInvariant`),
5. composed lifecycle bundle (`lifecycleInvariantBundle`),
6. stale-reference hardening family (`lifecycleStaleReferenceExclusionInvariant`),
7. lifecycle+stale bridge (`lifecycleIdentityStaleReferenceInvariant`).

This explicit split now includes transition-local lifecycle helper lemmas in `Lifecycle/Operations`,
local and composed lifecycle preservation entrypoints (`lifecycleRetypeObject_preserves_lifecycleInvariantBundle`,
`lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant`,
`lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant`,
`lifecycleRetypeObject_preserves_coreIpcInvariantBundle`, and
`lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle`), and fixture-backed executable trace evidence
for unauthorized/illegal-state/success lifecycle retype outcomes plus composed lifecycle+capability behavior.

## 8. M5 policy-surface layering (WS-M5-C complete)

Policy surface entrypoints now live in `SeLe4n/Kernel/Service/Invariant.lean` and are explicitly
kept mutation-free:

- reusable components: `policyBackingObjectTyped`, `policyOwnerAuthorityRefRecorded`,
  `policyOwnerAuthoritySlotPresent`,
- bundle entrypoint: `servicePolicySurfaceInvariant`,
- bridge lemmas: lifecycle/capability assumptions can discharge policy authority obligations,
- composed bridge: `servicePolicySurfaceInvariant_of_lifecycleInvariant` lifts lifecycle contracts
  (plus backing-object existence assumptions) into the service policy bundle,
- check-vs-mutation separation: policy-denial theorem surfaces remain explicit and deterministic.

## 9. M5 proof package layering (WS-M5-D complete)

Proof-package entrypoints now extend the M5 policy surface to full local + composed preservation:

- composed bundle entrypoint: `serviceLifecycleCapabilityInvariantBundle`,
- local preservation entrypoints:
  - `serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_preserves_serviceLifecycleCapabilityInvariantBundle`,
- failure-path preservation entrypoints:
  - `serviceStart_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceStop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_stop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_start_failure_preserves_serviceLifecycleCapabilityInvariantBundle`.

This keeps the M5 theorem surface aligned with the local-first composition rule:
prove per-transition preservation first, then expose cross-subsystem bundle preservation with
explicit failure-path statements.

## 10. VSpace proof completion (WS-D3 / F-08 / TPI-001 complete; WS-G3 / F-P06; WS-G6 / F-P05 updated)

VSpace invariant bundle preservation is now proven for both success and error paths:

- **Error-path preservation** (trivially true, error returns unchanged state):
  - `vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle`
- **Success-path preservation** (substantive — prove invariant preservation over changed state):
  - `vspaceMapPage_success_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`
- **Round-trip / functional-correctness theorems** (TPI-001 closure; WS-G6: re-proved with HashMap bridge lemmas):
  - `vspaceLookup_after_map`: map then lookup yields mapped address
  - `vspaceLookup_map_other`: map at vaddr doesn't affect lookup at different vaddr'
  - `vspaceLookup_after_unmap`: after unmap, lookup fails with translationFault
  - `vspaceLookup_unmap_other`: unmap at vaddr doesn't affect lookup at different vaddr'

Data structure (WS-G6 / F-P05):

- `VSpaceRoot.mappings : Std.HashMap VAddr (PAddr × PagePermissions)` — O(1) amortized lookup/insert/erase (WS-G6, enriched by WS-H11 with per-page permissions). HashMap key uniqueness makes `noVirtualOverlap` trivially true. `BEq VSpaceRoot` uses size + fold containment (order-independent HashMap equality). `hashMapVSpaceBackend` replaces `listVSpaceBackend`.

VSpace invariant bundle structure (5-conjunct, WS-G3/WS-H11):
- `vspaceAsidRootsUnique` — no two VSpaceRoot objects share the same ASID
- `vspaceRootNonOverlap` — VSpaceRoot mapping ranges do not overlap (trivially true with HashMap, WS-G6)
- `asidTableConsistent` — bidirectional soundness + completeness between `asidTable` HashMap and VSpaceRoot objects
- `wxExclusiveInvariant` — no mapping is both writable and executable (W^X, WS-H11)
- `boundedAddressTranslation` — all translated physical addresses are within `[0, bound)` (WS-H11)

Supporting infrastructure in `VSpace.lean`:
- `resolveAsidRoot_some_implies_obj` — extracts asidTable + object-store facts from successful ASID resolution (WS-G3: O(1) HashMap lookup)
- `resolveAsidRoot_of_asidTable_entry` — characterization lemma enabling round-trip proofs (WS-G3: no uniqueness/objectIndex needed)

TLB/cache maintenance model (`TlbModel.lean`, WS-H11/H-10):
- `TlbEntry` — cached `(ASID, VAddr, PAddr, PagePermissions)` translation entry
- `TlbState` — abstract collection of cached entries (list-backed)
- `adapterFlushTlb` — full TLB invalidation (ARM64 `TLBI ALLE1`)
- `adapterFlushTlbByAsid` — per-ASID invalidation (ARM64 `TLBI ASIDE1`)
- `adapterFlushTlbByVAddr` — per-(ASID,VAddr) invalidation (ARM64 `TLBI VAE1`)
- `tlbConsistent` — invariant: all TLB entries match current page tables
- 10 TLB theorems: `tlbConsistent_empty`, `adapterFlushTlb_restores_tlbConsistent`, `adapterFlushTlbByAsid_preserves_tlbConsistent`, `vspaceMapPage_then_flush_preserves_tlbConsistent`, `vspaceUnmapPage_then_flush_preserves_tlbConsistent`, `adapterFlushTlbByAsid_removes_matching`, `adapterFlushTlbByAsid_preserves_other`, `adapterFlushTlbByVAddr_preserves_tlbConsistent`, `adapterFlushTlbByVAddr_removes_matching`, `cross_asid_tlb_isolation`

## 11. Badge-override safety (WS-D3 / F-06 / TPI-D04 complete)

Badge-override safety in `cspaceMint` is now fully proven:

- `mintDerivedCap_rights_attenuated_with_badge_override` — rights attenuation holds regardless of badge
- `mintDerivedCap_target_preserved_with_badge_override` — target identity preserved regardless of badge
- `cspaceMint_badge_override_safe` — composed kernel-operation-level safety witness

The core insight: `mintDerivedCap` checks `rightsSubset` and sets `target := parent.target`
unconditionally — the `badge` parameter only affects the `.badge` field of the child capability,
which is notification-signaling metadata, not authority scope.

## 12. Proof classification docstrings (WS-D3 / F-16 complete)

All seven `Invariant.lean` files now contain module-level `/-! ... -/` docstrings that classify
every theorem into one of these categories:

| Category | Assurance level |
|---|---|
| **Substantive preservation** | High — proves invariant preservation over changed state |
| **Error-case preservation** | Low — trivially true (unchanged state) |
| **Non-interference** | Critical — proves high-domain operations don't leak to low observers |
| **Badge-safety** | High — proves badge override cannot escalate privilege |
| **Structural / bridge** | High — proves decomposition/composition relationships |
| **Round-trip / functional-correctness** | High — proves semantic contracts between operations |

## 13. Kernel design hardening (WS-D4 complete)

### F-07: Service dependency cycle detection

Service dependency registration now includes DFS-based cycle detection (WS-G8: migrated from BFS with `List` visited to DFS with `Std.HashSet` visited for O(n+e) complexity):

- `serviceBfsFuel` — fuel computation for bounded DFS (objectIndex.length + 256)
- `serviceHasPathTo` — bounded DFS reachability check in the dependency graph (WS-G8: `Std.HashSet ServiceId` visited set)
- `serviceRegisterDependency` — deterministic registration with self-loop, idempotency, and cycle checks
- `serviceRegisterDependency_error_self_loop` — self-dependency rejection theorem (no `sorry`)
- `serviceDependencyAcyclic` — acyclicity invariant definition
- `serviceRegisterDependency_preserves_acyclicity` — preservation theorem (no `sorry`; BFS bridge `bfs_complete_for_nontrivialPath` formally proven — TPI-D07-BRIDGE resolved, see §14)

### F-11: serviceRestart partial-failure semantics

serviceRestart uses documented partial-failure semantics (stop succeeds, start fails = service remains stopped):

- `serviceRestart_error_of_stop_error` — stop failure propagated directly
- `serviceRestart_error_of_start_error` — start failure propagated with post-stop state
- `serviceRestart_ok_implies_staged_steps` — success implies both stages succeeded
- `serviceRestart_error_discards_state` — error monad discards intermediate state
- `serviceRestart_error_from_start_phase` — functional decomposition of start-phase errors

### F-12: Double-wait prevention and uniqueness invariant

Notification waiting lists now enforce uniqueness:

- `notificationWait` — checks `waiter ∈ ntfn.waitingThreads` before appending; returns `alreadyWaiting` on duplicate
- `notificationWait_error_alreadyWaiting` — rejection theorem (no `sorry`)
- `notificationWait_badge_path_notification` — decomposition: badge-consumed path post-state notification
- `notificationWait_wait_path_notification` — decomposition: wait path post-state notification
- `uniqueWaiters` — invariant: notification waiting list has no duplicates (`List.Nodup`)
- `notificationWait_preserves_uniqueWaiters` — preservation theorem (no `sorry`)

Supporting infrastructure:

- `storeTcbIpcState_preserves_objects_ne` — storeTcbIpcState preserves objects at other IDs
- `storeTcbIpcState_preserves_notification` — storeTcbIpcState preserves notification objects
- `removeRunnable_preserves_objects` — removeRunnable preserves all objects

## 14. TPI-D07 acyclicity proof infrastructure (Risk 0 resolved, TPI-D07 closed, TPI-D07-BRIDGE resolved)

The vacuous BFS-based acyclicity invariant (Risk 0) has been resolved via Strategy B:
the invariant definition was corrected and a genuine 4-layer proof infrastructure was
implemented in `SeLe4n/Kernel/Service/Invariant.lean`.

**Problem:** The original `serviceDependencyAcyclic` was defined as
`∀ sid, ¬ serviceHasPathTo st sid sid fuel = true`, but `serviceHasPathTo` returns `true`
immediately for self-queries (BFS starts with `[src]` in frontier, immediately finds
`src = target`), making the invariant equivalent to `False` — trivially unsatisfiable.

**Resolution:** Replaced with declarative acyclicity using `serviceNontrivialPath`
(an inductive `Prop`-valued path relation of length ≥ 1).

Implemented proof layers:

- **Layer 0 (Definitions):** `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`,
  revised `serviceDependencyAcyclic` (declarative, non-vacuous)
- **Layer 1 (Structural lemmas):** `serviceReachable_trans`, `serviceReachable_of_edge`,
  `serviceReachable_of_nontrivialPath`, `serviceNontrivialPath_of_edge_reachable`,
  `serviceNontrivialPath_of_reachable_ne`, `serviceNontrivialPath_trans`,
  `serviceNontrivialPath_step_right`. Frame lemmas: `serviceEdge_storeServiceState_ne`,
  `serviceEdge_storeServiceState_updated`, `serviceEdge_post_insert`
- **Layer 2 (BFS bridge):** `bfs_complete_for_nontrivialPath` — BFS completeness
  bridge connecting declarative paths to the executable BFS check. Formally proven
  (TPI-D07-BRIDGE resolved); no `sorry` remains
- **Layer 3 (Path decomposition):** `nontrivialPath_post_insert_cases` — decomposes
  any post-insertion nontrivial path into either a pre-state path or a composition
  using the new edge with pre-state reachability
- **Layer 4 (Closure):** `serviceRegisterDependency_preserves_acyclicity` — genuine
  preservation proof via post-insertion path decomposition and contradiction with the
  BFS cycle-detection check. The main theorem is sorry-free

**Sub-obligation resolved (TPI-D07-BRIDGE):** The `bfs_complete_for_nontrivialPath`
lemma has been formally proven, establishing that the BFS with `serviceBfsFuel` fuel
is complete enough to detect all nontrivial paths between distinct services. No
`sorry` obligations remain in the TPI-D07 proof infrastructure.

### 14.1 BFS completeness proof (TPI-D07-BRIDGE completed)

The formal proof eliminating the `bfs_complete_for_nontrivialPath` sorry has been
completed following the M2 milestone roadmap
([`M2_BFS_SOUNDNESS.md`](../dev_history/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md))
and four sub-documents (M2A–M2D).

**Proof decomposition:**

1. **Equational theory ([M2A](../dev_history/audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)):**
   A `lookupDeps` helper bridges the executable BFS dependency lookup to the
   declarative `serviceEdge` relation (`serviceEdge_iff_lookupDeps`). Five BFS
   unfolding lemmas (EQ1-EQ5) provide rewrite rules for each branch of the `go`
   function.

2. **Completeness invariant ([M2B](../dev_history/audits/execution_plans/milestones/M2B_COMPLETENESS_INVARIANT.md)):**
   A named `bfsClosed` definition captures the visited-set closure property. Four
   lemmas (CB1-CB4) establish the invariant initially, preserve it across skip and
   expansion steps, and prove the critical boundary lemma: if a visited node reaches
   target and target is not visited, some frontier node also reaches target.

3. **Fuel adequacy ([M2C](../dev_history/audits/execution_plans/milestones/M2C_FUEL_ADEQUACY.md)):**
   A `serviceCountBounded` precondition bounds the BFS universe by `serviceBfsFuel st`
   (Approach A). `serviceCountBounded_preserved_by_registerDependency` proves the
   precondition is maintained across dependency registration.

4. **Core completeness ([M2D](../dev_history/audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md)):**
   `go_complete` (CP1) carries the four-part invariant (I1: target not visited,
   I2: closure, I3: frontier witness, I4: fuel adequate) through strong induction
   on fuel with structural induction on the frontier list. The sorry is eliminated.

**Implemented scope:** 17 private lemmas + 4 definitions + 3 public theorems.

Frozen operational files (M0 semantics freeze):

| File | SHA-256 |
|---|---|
| `Operations.lean` | `a61fa6c1...42ffff44` |
| `State.lean` | `6f6f87d8...d1cbc1e6` |
| `Object.lean` | `db228ed6...14594f32` |
| `Prelude.lean` | `bffc93fe...d47b30fe` |

Full execution plan: [`docs/dev_history/audits/execution_plans/00_INDEX.md`](../dev_history/audits/execution_plans/00_INDEX.md)

## 15. Information-flow layering (WS-B7 baseline + WS-D2 enforcement and non-interference)

### IF-M1 baseline (WS-B7 complete)

Policy and projection primitives:

- policy lattice/labels:
  - `Confidentiality`, `Integrity`, `SecurityLabel`,
  - `confidentialityFlowsTo`, `integrityFlowsTo`, `securityFlowsTo`,
  - algebraic lemmas: `securityFlowsTo_refl`, `securityFlowsTo_trans`.
- observer projection helpers:
  - `projectState`, `projectObjects`, `projectRunnable`, `projectCurrent`,
  - relation scaffold: `lowEquivalent` with `refl/symm/trans` lemmas.

### Enforcement layer (WS-D2 / F-02 complete)

Policy checks wired into kernel operations via `Enforcement.lean`:

- `endpointSendDualChecked` — enforces `securityFlowsTo` before IPC send,
- `cspaceMintChecked` — enforces `securityFlowsTo` before capability minting,
- `serviceRestartChecked` — enforces `securityFlowsTo` before service restart.

### Non-interference theorems (WS-D2 baseline + WS-F3 expansion)

Transition-level non-interference proofs in `InformationFlow/Invariant.lean`:

WS-D2 baseline (5 theorems):
- `chooseThread_preserves_lowEquivalent` — scheduler non-interference (TPI-D01),
- `endpointSendDual_preserves_lowEquivalent` — IPC endpoint non-interference,
- `cspaceMint_preserves_lowEquivalent` — capability mint non-interference (TPI-D02),
- `cspaceRevoke_preserves_lowEquivalent` — capability revoke non-interference (TPI-D02),
- `lifecycleRetypeObject_preserves_lowEquivalent` — lifecycle non-interference (TPI-D03).

WS-F3 additions (7 new theorems):
- `notificationSignal_preserves_lowEquivalent` — notification signal NI (F-21),
- `notificationWait_preserves_lowEquivalent` — notification wait NI (F-21),
- `cspaceInsertSlot_preserves_lowEquivalent` — capability insert NI (CRIT-03),
- `serviceStart_preserves_lowEquivalent` — service start NI (CRIT-03),
- `serviceStop_preserves_lowEquivalent` — service stop NI (CRIT-03),
- `serviceRestart_preserves_lowEquivalent` — service restart NI (CRIT-03),
- `storeObject_at_unobservable_preserves_lowEquivalent` — generic infrastructure.

WS-F3 enforcement-NI bridges (3 theorems):
- `endpointSendDualChecked_NI` — bridges checked send to NI,
- `cspaceMintChecked_NI` — bridges checked mint to NI,
- `serviceRestartChecked_NI` — bridges checked restart to NI.

WS-H8 enforcement-NI bridges (4 theorems):
- `endpointSendDualChecked_NI` — bridges dual-queue checked send to NI,
- `notificationSignalChecked_NI` — bridges checked signal to NI,
- `cspaceCopyChecked_NI` — bridges checked copy to NI (underlying NI as hypothesis),
- `cspaceMoveChecked_NI` — bridges checked move to NI (underlying NI as hypothesis).

WS-H8 enforcement soundness (5 theorems):
- `enforcementSoundness_endpointSendDualChecked`,
- `enforcementSoundness_notificationSignalChecked`,
- `enforcementSoundness_cspaceCopyChecked`,
- `enforcementSoundness_cspaceMoveChecked`,
- `enforcementSoundness_endpointReceiveDualChecked`.

### IF-M4 bundle-level non-interference (WS-E5 complete)

**H-04 — Parameterized security labels (≥3 domains):**

- `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with `canFlow`/`isReflexive`/`isTransitive`/`wellFormed`,
- `domainFlowsTo` with `domainFlowsTo_refl`/`domainFlowsTo_trans` proofs,
- Built-in policies: `DomainFlowPolicy.allowAll`, `DomainFlowPolicy.linearOrder` with well-formedness proofs,
- `GenericLabelingContext` with embedded policy field,
- `EndpointFlowPolicy` for per-endpoint flow overrides,
- `embedLegacyLabel` mapping legacy 2x2 lattice to 4-domain system,
- `embedLegacyLabel_preserves_flow` correctness proof,
- `threeDomainExample` with 3 named validation theorems.

**H-05 — Composed bundle-level non-interference:**

- `NonInterferenceStep` inductive (31 constructors; extended from 28 by v0.13.5 audit: added `endpointReceiveDualHigh`, `endpointCallHigh`, `endpointReplyRecvHigh`. Original 28 from WS-H9: `chooseThread`, `endpointSend`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`, `notificationSignal`, `notificationWait`, `cspaceInsertSlot`, `serviceStart`, `serviceStop`, `serviceRestart`, `schedule`, `vspaceMapPage`, `vspaceUnmapPage`, `vspaceLookup`, `cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`, `endpointReply`, `storeObjectHigh`, `setCurrentThread`, `ensureRunnableHigh`, `removeRunnableHigh`, `storeTcbIpcStateAndMessageHigh`, `storeTcbQueueLinksHigh`, `cspaceMutateHigh`, `handleYield`, `timerTick`),
- `step_preserves_projection` — single-step projection preservation (all 31 constructors),
- `composedNonInterference_step` — primary IF-M4 single-step theorem,
- `NonInterferenceTrace` inductive (`nil`/`cons`),
- `trace_preserves_projection`, `composedNonInterference_trace` — multi-step lift,
- `preservesLowEquivalence`, `compose_preservesLowEquivalence` — abstract composition,
- `errorAction_preserves_lowEquiv` — error path preservation.

WS-H9 new NI preservation theorems (21 theorems):
- `schedule_preserves_projection` — scheduler NI (high-current + all-runnable-high conditions),
- `setCurrentThread_preserves_projection` — thread switch NI,
- `ensureRunnable_preserves_projection` / `removeRunnable_preserves_projection` — run queue NI,
- `vspaceMapPage_preserves_projection` / `_lowEquivalent` — VSpace map NI,
- `vspaceUnmapPage_preserves_projection` / `_lowEquivalent` — VSpace unmap NI,
- `vspaceLookup_preserves_state` / `_lowEquivalent` — VSpace lookup NI,
- `cspaceCopy_preserves_projection` / `_lowEquivalent` — CSpace copy NI,
- `cspaceMove_preserves_projection` / `_lowEquivalent` — CSpace move NI,
- `cspaceDeleteSlot_preserves_projection` / `_lowEquivalent` — CSpace delete NI,
- `endpointReply_preserves_projection` / `_lowEquivalent` — IPC reply NI,
- `storeTcbIpcStateAndMessage_preserves_projection` — IPC state NI,
- `storeTcbQueueLinks_preserves_projection` — queue links NI,
- `storeObject_preserves_projection` / `storeCapabilityRef_preserves_projection` — observable-state NI,
- `switchDomain_preserves_lowEquivalent` — domain switch two-sided NI.

v0.13.5 gap closure (3 theorems + 1 bridge):
- `endpointReceiveDualChecked_NI` — enforcement-NI bridge for dual-queue receive (WS-H8 gap),
- `endpointReceiveDual_preserves_lowEquivalent` — IPC receive-dual NI (hypothesis-based),
- `endpointCall_preserves_lowEquivalent` — IPC call NI (hypothesis-based),
- `endpointReplyRecv_preserves_lowEquivalent` — IPC reply-recv NI (hypothesis-based).

**M-07 — Enforcement boundary specification:**

- `EnforcementClass` inductive (`policyGated`/`capabilityOnly`/`readOnly`),
- `enforcementBoundary` — exhaustive 17-entry classification table,
- `enforcementBoundaryExtended` — WS-H8 extended 19-entry table (8 policy-gated),
- `denied_preserves_state_*` — denial preservation for all 7 checked operations,
- `enforcement_sufficiency_*` — complete-disjunction coverage proofs for all 7 checked operations.

**WS-H8/A-36 — Projection hardening:**

- `ObservableState` extended with `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`,
- `projectDomainTimeRemaining`, `projectDomainSchedule`, `projectDomainScheduleIndex` projection helpers,
- All 19 NI theorems updated to handle new fields.

**WS-H10/C-05/A-38 — MachineState projection & security lattice:**

- `ObservableState` extended with `machineRegs : Option RegisterFile` (domain-gated via current thread observability),
- Machine timer deliberately excluded (covert timing channel prevention),
- `projectMachineRegs` projection helper with observability gating,
- `bibaIntegrityFlowsTo` / `bibaSecurityFlowsTo` standard BIBA flow checks,
- `bibaPolicy` generic `DomainFlowPolicy` with standard BIBA ordering,
- `bibaPolicy_reflexive`, `bibaPolicy_transitive`, `bibaPolicy_wellFormed`,
- `securityLattice_reflexive`, `securityLattice_transitive` — legacy lattice pre-order confirmation,
- `DeclassificationPolicy` with `isDeclassificationAuthorized`, `isDeclassificationAuthorized_not_reflexive`,
- `declassifyStore` operation with 5 theorems (authorization, rejection, state preservation, enforcement soundness),
- `endpointFlowPolicyWellFormed` predicate with `endpointFlowCheck_reflexive`, `endpointFlowCheck_transitive`,
- All NI theorems updated for `machineRegs` field.

## 12. Untyped memory invariants (WS-F2)

Component level:

- `untypedWatermarkInvariant` — watermark does not exceed region size,
- `untypedChildrenBoundsInvariant` — all children lie within the watermark,
- `untypedChildrenNonOverlapInvariant` — children do not overlap,
- `untypedChildrenUniqueIdsInvariant` — children have unique object IDs.

Bundle level:

- `untypedMemoryInvariant` (conjunction of all four components)

Object-level theorems:

- `allocate_some_iff` — decomposition biconditional for successful allocation,
- `allocate_watermark_advance` / `allocate_watermark_monotone` — watermark progression,
- `allocate_preserves_watermarkValid` / `allocate_preserves_region` — structural preservation,
- `reset_wellFormed`, `empty_wellFormed`, `canAllocate_implies_fits`.

Operation-level theorems:

- `retypeFromUntyped_ok_decompose` — success decomposition into existential witnesses,
- `retypeFromUntyped_error_typeMismatch` — non-untyped source returns type mismatch,
- `retypeFromUntyped_error_allocSizeTooSmall` — undersized allocation rejected,
- `retypeFromUntyped_error_regionExhausted` — oversized allocation fails,
- `retypeFromUntyped_preserves_lifecycleMetadataConsistent` — metadata preservation,
- `retypeFromUntyped_preserves_lifecycleInvariantBundle` — full bundle preservation,
- `default_systemState_untypedMemoryInvariant` — default state satisfies invariant.

Auto-derivation theorems (WS-H2/B-5 — eliminates manual `hNe`/`hFresh` proof obligations):

- `retypeFromUntyped_ok_childId_ne` — success implies `childId ≠ untypedId` (derived from H-06 self-overwrite guard),
- `retypeFromUntyped_ok_childId_fresh` — success implies childId fresh among untyped's existing children (derived from A-27 collision guard),
- `retypeFromUntyped_preserves_untypedMemoryInvariant_auto` — composed variant that auto-derives both `hNe` and `hFresh` from a success hypothesis; callers need only supply the invariant precondition, new-object well-formedness, and success hypothesis.

## 16. WS-F1 IPC message transfer and dual-queue verification

IPC operations now carry `IpcMessage` payloads (registers, caps, badge):

- `endpointSendDual` / `endpointReceiveDual` — dual-queue IPC with message staging in `TCB.pendingMessage` (errors propagated, never silently swallowed),
- `endpointCall` — send + block-for-reply compound with message,
- `endpointReply` / `endpointReplyRecv` — reply + receive compound with message.

Preservation theorems (TPI-D08/TPI-D09):
- `endpointSendDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReceiveDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointQueueRemoveDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointCall_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReplyRecv_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReply_preserves_ipcSchedulerContractPredicates`.

Supporting lemmas: `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, `storeTcbQueueLinks`
backward-preservation and frame lemmas.

## 17. WS-F3 information-flow completeness

**CRIT-02 — ObservableState extension** (`Projection.lean`):

- `activeDomain` — scheduling transparency, always visible to all observers,
- `irqHandlers` — filtered by target notification object observability,
- `objectIndex` — filtered by object observability.

**F-22 — CNode slot filtering** (`Projection.lean`):

- `capTargetObservable` — observability gate for `.object`, `.cnodeSlot`, `.replyCap` targets,
- `projectKernelObject` — redacts high-domain capability slot contents from CNodes,
- `projectKernelObject_idempotent` — safety: double-filtering is idempotent (WS-G5: reformulated to slot-level lookup equality for `Std.HashMap` compatibility),
- `projectKernelObject_objectType` — safety: filtering preserves object type.

**Enforcement-NI bridges** (`Invariant.lean`):

- `endpointSendDualChecked_NI` — bridges checked send to NI domain-separation,
- `cspaceMintChecked_NI` — bridges checked mint to NI domain-separation,
- `serviceRestartChecked_NI` — bridges checked restart to NI domain-separation.

## 18. WS-F4 proof gap closure

### F-03: timerTick preservation (`Scheduler/Operations.lean`)

`timerTick` now preserves the complete scheduler invariant bundle and kernel invariant:

- `timerTick_preserves_schedulerInvariantBundle` — covers `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`
- `timerTick_preserves_kernelInvariant` — extends to include `currentThreadInActiveDomain`

Proof strategy: case split on `scheduler.current` (none/some), object lookup (none/tcb/other), and time-slice expiry (`tcb.timeSlice ≤ 1`). Expired path delegates to existing `schedule_preserves_*` infrastructure; non-expired path proves scheduler unchanged directly.

### F-06: cspaceMutate, cspaceRevokeCdt, cspaceRevokeCdtStrict preservation (`Capability/Invariant.lean`)

- `cspaceMutate_preserves_capabilityInvariantBundle` — uses `revert/unfold` decomposition pattern; case-splits on capability lookup, rights check, and storeObject
- `cspaceRevokeCdt_preserves_capabilityInvariantBundle` — fold induction via extracted `revokeCdtFoldBody` with error propagation lemmas (`revokeCdtFoldBody_foldl_error`). CDT-only state updates handled by `capabilityInvariantBundle_of_cdt_update`
- `cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle` — `suffices` with inline fold induction over total function; case-splits on `firstFailure`, `lookupCdtSlotOfNode`, `cspaceDeleteSlot`

Supporting infrastructure:
- `capabilityInvariantBundle_of_cdt_update` — CDT-only state changes preserve capability invariants (WS-H4: requires `edgeWellFounded` witness for new CDT)
- `revokeCdtFoldBody` — extracted fold body for named step preservation
- `revokeCdtFoldBody_preserves` — single-step preservation through fold body (WS-H4: uses `CapDerivationTree.edgeWellFounded_sub` + `removeNode_edges_sub` for CDT-shrinking acyclicity)
- `revokeCdtFoldBody_error` / `revokeCdtFoldBody_foldl_error` — error propagation through fold

### WS-H4: Capability invariant bundle redesign (`Capability/Invariant.lean`, `Model/Object.lean`)

Three new predicates added to `capabilityInvariantBundle` (4-tuple → 7-tuple, later extended to 8-tuple by WS-H13):
- `cspaceSlotCountBounded` — every CNode has at most `2^radixBits` occupied slots
- `cdtCompleteness` — every CDT node points to an existing object (node-slot coherence)
- `cdtAcyclicity` — CDT edge-well-foundedness (no cycles via `edgeWellFounded`)

Foundation lemmas in `Model/Object.lean`:
- `CNode.slotCountBounded`, `empty_slotCountBounded`, `remove_slotCountBounded`, `revokeTargetLocal_slotCountBounded`
- `CapDerivationTree.edgeWellFounded`, `empty_edgeWellFounded`, `edgeWellFounded_sub`, `removeNode_edges_sub`

Transfer theorem strategy:
- **Non-CNode stores**: `cspaceSlotCountBounded_of_storeObject_nonCNode` + `cdtCompleteness_of_storeObject` + `cdtAcyclicity_of_cdt_eq`
- **CNode stores**: `cspaceSlotCountBounded_of_storeObject_cnode` with `hSlotCapacity`/`hDstCapacity` hypotheses
- **CDT-modifying ops** (copy/move/mintWithCdt): `hCdtPost` hypothesis pattern defers acyclicity obligation to caller
- **CDT-shrinking ops** (revoke fold): `edgeWellFounded_sub` + `removeNode_edges_sub`

### F-12: Notification ipcInvariant + schedulerInvariantBundle preservation (`IPC/Invariant.lean`)

- `notificationSignal_preserves_ipcInvariant` — wake path (storeObject → storeTcbIpcState → ensureRunnable) and merge path (storeObject only)
- `notificationSignal_preserves_schedulerInvariantBundle` — compositional through `scheduler_unchanged_through_store_tcb` + ensureRunnable helpers
- `notificationWait_preserves_ipcInvariant` — badge-consume path (storeObject → storeTcbIpcState) and wait path (storeObject → storeTcbIpcState → removeRunnable)
- `notificationWait_preserves_schedulerInvariantBundle` — badge-consume scheduler unchanged; wait path through removeRunnable with currentThread safety
- `notificationSignal_preserves_ipcSchedulerContractPredicates` — M3.5 contract predicate closure: wake path follows endpointReply pattern (storeTcbIpcState → ensureRunnable); merge path via `contracts_of_same_scheduler_ipcState` (no TCB/scheduler change)
- `notificationWait_preserves_ipcSchedulerContractPredicates` — M3.5 contract predicate closure: badge-consume path (scheduler unchanged, waiter set to .ready); wait path (.blockedOnNotification not covered by blockedOnSend/blockedOnReceive predicates, waiter removed from runnable)

Supporting infrastructure:
- `storeObject_notification_preserves_ipcInvariant` — dual of `storeObject_endpoint_preserves_ipcInvariant`; new helper for notification-storing operations
- Existing well-formedness lemmas: `notificationSignal_result_wellFormed_wake/merge`, `notificationWait_result_wellFormed_badge/wait`

## 19. WS-G9 information-flow projection optimization (F-P09)

**Precomputed observable set** (`Projection.lean`):

- `computeObservableSet` — builds `Std.HashSet ObjId` via single `foldl` pass over `st.objectIndex`, using `objectObservable` as predicate. All sub-projection functions use O(1) `contains` lookups instead of redundant `objectObservable` re-evaluation (~12,800 comparisons → N lookups).

**`@[csimp]`-ready fast projection** (`Projection.lean`):

- `projectStateFast` — optimized `projectState` using precomputed observable set,
- `projectObjectsFast` — O(1) observability via `observableOids.contains`,
- `projectIrqHandlersFast` — O(1) observability via `observableOids.contains`,
- `projectObjectIndexFast` — O(1) observability via `observableOids.contains`.

**Equivalence proofs** (`Projection.lean`):

- `foldl_observable_set_mem` — core induction lemma: HashSet membership ↔ list membership ∧ predicate,
- `computeObservableSet_mem` — membership in computed set ↔ `objectObservable` for indexed ObjIds,
- `computeObservableSet_not_mem` — non-indexed ObjIds are not in the observable set,
- `projectObjectsFast_eq` — fast variant equals original `projectObjects`,
- `projectIrqHandlersFast_eq` — fast variant equals original `projectIrqHandlers`,
- `projectObjectIndexFast_eq` — fast variant equals original `projectObjectIndex` (via `List.filter_congr`),
- `projectStateFast_eq` — top-level equivalence: `projectStateFast = projectState` under state synchronization invariants.

**HashSet bridge lemmas** (`Prelude.lean`):

- `List.foldl_preserves_contains` — monotonicity: elements already in the set remain after foldl,
- `List.foldl_not_contains_when_absent` — elements not in the list are unaffected by foldl,
- `List.foldl_preserves_when_pred_false` — elements with false predicate are unaffected by foldl.

**Design invariant:** Original `projectState` definition is unchanged — all existing NI theorems in `Invariant.lean` (1448 lines) remain untouched. `projectStateFast` provides the performance path with proven equivalence.

## 21. WS-H14 type safety & Prelude foundations

**Typeclass instance hardening (A-03):**

- `EquivBEq` instances for all 14 typed identifier types (13 in `Prelude.lean` + `SecurityDomain` in `Policy.lean`).
- `LawfulBEq` instances for all 14 typed identifier types.
- These close the gap where HashMap bridge lemmas required `EquivBEq` constraints that identifier types did not satisfy.

**KernelM monad law proofs (A-04/M-11):**

- `KernelM.pure_bind_law` — left identity for the state-error monad.
- `KernelM.bind_pure_law` — right identity (bind with pure is identity).
- `KernelM.bind_assoc_law` — associativity (sequential composition is associative).
- `LawfulMonad (KernelM σ ε)` — registered instance enabling equational reasoning about chained kernel transitions.

**isPowerOfTwo correctness (A-06):**

- `isPowerOfTwo_spec` — definitional unfolding: `isPowerOfTwo n = true → n > 0 ∧ n &&& (n - 1) = 0`.
- `isPowerOfTwo_pos` — positivity extraction.
- `isPowerOfTwo_of_pow2_k` — concrete verification for k = 0..5, 12, 16, 21 (covers all platform page sizes).

**Identifier roundtrip & injectivity proofs (WS-H14d):**

For each of the 14 identifier types:
- `toNat_ofNat` — roundtrip: construct then project yields the original value.
- `ofNat_toNat` — roundtrip: project then reconstruct yields the original identifier.
- `ofNat_injective` — distinct values produce distinct identifiers.
- `ext` — extensionality: equal underlying values imply equal identifiers.

**OfNat instance removal (A-02/M-10):**

- All `OfNat` instances removed for 14 typed identifier types.
- Numeric literals can no longer implicitly coerce to typed identifiers.
- All construction sites migrated to explicit `⟨n⟩` or `TypeName.ofNat n` syntax.

**Sentinel predicate completion (A-01):**

- `ThreadId.valid` / `ServiceId.valid` / `CPtr.valid` — nonzero value predicates.
- `*.valid_iff_not_reserved` — equivalence between validity and non-reservation.
- `*.sentinel_not_valid` — sentinel is never valid (for all 4 sentinel-bearing types).

## 20. WS-H10 security model foundations

**MachineState projection (C-05/A-38):**

- `ObservableState.machineRegs : Option RegisterFile` — domain-gated register file projection, visible only when the current thread is observable.
- `projectMachineRegs` — projects register file through current-thread observability gate. Machine timer deliberately excluded (covert timing channel).
- All existing NI theorems updated with `machineRegs` branch proofs.

**Security lattice (A-34):**

- `securityLattice_reflexive` / `securityLattice_transitive` — legacy lattice forms a valid pre-order.
- `bibaIntegrityFlowsTo` / `bibaSecurityFlowsTo` / `bibaPolicy` — standard BIBA alternatives with reflexivity/transitivity proofs.

**Declassification model (A-39):**

- `DeclassificationPolicy` — authorized downgrade paths with `isDeclassificationAuthorized` gate.
- `declassifyStore` — enforcement operation gating on base-policy denial + declassification authorization.
- `enforcementSoundness_declassifyStore` — if operation succeeds, both authorization checks passed.
- `declassifyStore_NI` — declassification at a non-observable target preserves low-equivalence for non-target observers. Delegates to `storeObject_at_unobservable_preserves_lowEquivalent`.

**Endpoint policy well-formedness (M-16):**

- `endpointFlowPolicyWellFormed` — global + per-endpoint override policies must be reflexive + transitive.
- `endpointFlowCheck_reflexive` / `endpointFlowCheck_transitive` — well-formedness inheritance proofs.

**IF configuration invariant bundle:**

- `InformationFlowConfigInvariant` — structure collecting global policy WF, endpoint policy WF, and declassification consistency. Trivially preserved by kernel transitions (policies are external to `SystemState`).
- `defaultConfigInvariant` — existence proof for the default configuration.

## 22. Cross-subsystem invariant reconciliation (WS-H12e)

WS-H12e reconciles all subsystem invariant compositions after WS-H12a–d changes,
closing gaps where invariants were defined but not composed into the top-level proof surface.

### Changes to bundle compositions

| Bundle | Change | Effect |
|---|---|---|
| `schedulerInvariantBundleFull` | Extended from 4 to 5 conjuncts (+ `contextMatchesCurrent`) | Machine registers match current thread's saved context at all scheduler exit points |
| `coreIpcInvariantBundle` | Upgraded from `ipcInvariant` to `ipcInvariantFull` | `dualQueueSystemInvariant` and `allPendingMessagesBounded` now composed into cross-subsystem proof surface |
| `ipcSchedulerCouplingInvariantBundle` | Extended from 2 to 4 conjuncts (+ `contextMatchesCurrent`, `currentThreadDequeueCoherent`) | Running thread dequeue coherence and context consistency compose through IPC-scheduler boundary |
| `proofLayerInvariantBundle` | Uses `schedulerInvariantBundleFull` instead of `schedulerInvariantBundle` | Top-level proof surface includes all 5 scheduler conjuncts |

### New proofs and definitions

Scheduler preservation (4 updated theorems):
- `schedule_preserves_schedulerInvariantBundleFull` — 5th conjunct preservation
- `handleYield_preserves_schedulerInvariantBundleFull` — 5th conjunct preservation
- `timerTick_preserves_schedulerInvariantBundleFull` — 5th conjunct preservation
- `switchDomain_preserves_schedulerInvariantBundleFull` — 5th conjunct preservation (+ new `switchDomain_preserves_contextMatchesCurrent`)

Backward-compatible extraction theorems (3):
- `coreIpcInvariantBundle_to_ipcInvariant`
- `coreIpcInvariantBundle_to_dualQueueSystemInvariant`
- `coreIpcInvariantBundle_to_allPendingMessagesBounded`

Frame lemmas for `allPendingMessagesBounded` (8):
- `ensureRunnable_preserves_allPendingMessagesBounded`, `removeRunnable_preserves_allPendingMessagesBounded`
- `storeTcbIpcState_preserves_allPendingMessagesBounded`, `storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded`
- `storeTcbPendingMessage_preserves_allPendingMessagesBounded`, `storeObject_endpoint_preserves_allPendingMessagesBounded`
- `storeTcbQueueLinks_preserves_allPendingMessagesBounded`, `storeObject_notification_preserves_allPendingMessagesBounded`

Compound `allPendingMessagesBounded` preservation (3):
- `notificationSignal_preserves_allPendingMessagesBounded`, `notificationWait_preserves_allPendingMessagesBounded`
- `endpointReply_preserves_allPendingMessagesBounded`

Composed `ipcInvariantFull` preservation (7):
- `notificationSignal_preserves_ipcInvariantFull`, `notificationWait_preserves_ipcInvariantFull`
- `endpointReply_preserves_ipcInvariantFull`, `endpointSendDual_preserves_ipcInvariantFull`
- `endpointReceiveDual_preserves_ipcInvariantFull`, `endpointCall_preserves_ipcInvariantFull`
- `endpointReplyRecv_preserves_ipcInvariantFull`

Default-state proofs (6):
- `default_dualQueueSystemInvariant`, `default_allPendingMessagesBounded`, `default_ipcInvariantFull`
- `default_contextMatchesCurrent`, `default_currentThreadDequeueCoherent`, `default_schedulerInvariantBundleFull`

## 23. WS-H13: CSpace enrichment, service hardening & serviceCountBounded (v0.14.4)

WS-H13 closes 5 findings: H-01 (HIGH), A-29 (HIGH), A-21 (MEDIUM), A-30 (MEDIUM), M-17/A-31 (MEDIUM).

### Part A — Type-indexed CSpace with compressed-path CNodes (H-01)

CNode structure enriched with multi-level resolution fields:

- `depth` — CNode depth in CSpace hierarchy
- `guardWidth` — number of guard bits
- `guardValue` — guard bit pattern to match
- `radixWidth` — log₂ of slot count at this level

Multi-level resolver (`Capability/Operations.lean`):

- `resolveCapAddress` — recursive CSpace address resolver; walks CNode chain consuming `guardWidth + radixWidth` bits per hop. `termination_by bitsRemaining` with `hProgress : guardWidth + radixWidth ≥ 1` ensuring strict decrease.
- `resolveCapAddressK` — kernel monad wrapper
- `resolveCapAddressAndLookup` — composition with slot lookup

Resolution theorems:

- `resolveCapAddress_deterministic` — trivial (functional equality)
- `resolveCapAddress_zero_bits` — zero remaining bits → `.error .illegalState`
- `resolveCapAddress_result_valid_cnode` — success implies valid CNode exists at returned reference. Proved via `Nat.strongRecOn` (well-founded induction on `bits`) with nested `split at hOk` through all branches.

CSpace depth invariant:

- `cspaceDepthConsistent` — 8th conjunct added to `capabilityInvariantBundle` (7-tuple → 8-tuple)
- `default_capabilityInvariantBundle` — updated for 8-tuple (vacuous for empty object store)

### Part B — Atomic capability move (A-21)

- `cspaceMove_error_no_state` — error-path exclusion: on error, no success state is reachable.
- `cspaceMove_ok_implies_source_exists` — success-path: if move succeeds, the source capability existed.
- `resolveCapAddress_guard_reject` — guard mismatch at any CNode level returns `.error .invalidCapability` (primary CSpace attack surface coverage).
- Error monad (`Except`) provides implicit atomicity: error paths discard intermediate state, returning original state unchanged.

### Part C — Service backing-object verification (A-29)

`serviceStop` now checks backing-object existence before allowing transition:

- `serviceStop` — added `st.objects[svc.identity.backingObject]? = none` → `.error .backingObjectMissing` branch before policy check
- `serviceStop_error_backingObjectMissing` — rejection theorem
- `serviceStop_error_policyDenied` — updated with `hBacking` hypothesis (backing-object existence is a precondition for reaching the policy-denial branch)
- All downstream preservation theorems updated with extra `split at hStep` for new backing-object check branch

### Part D — Service restart atomicity (A-30)

Error monad (`Except`) provides implicit atomicity for `serviceRestart`:

- `serviceRestart_error_discards_state` — error path returns original state
- `serviceRestart_error_of_stop_error` / `serviceRestart_error_of_start_error` — failure-phase identification
- `serviceRestart_ok_implies_staged_steps` — success implies both stages completed

### Part E — serviceCountBounded invariant (M-17/A-31)

`serviceGraphInvariant` extended to 2-conjunct: `serviceDependencyAcyclic ∧ serviceCountBounded`.

Transfer lemma suite (6 lemmas for status-only `storeServiceState` where `entry.dependencies = svc.dependencies`):

- `serviceEdge_of_storeServiceState_sameDeps` — edge relation preserved
- `serviceNontrivialPath_of_storeServiceState_sameDeps` — path relation preserved
- `serviceDependencyAcyclic_of_storeServiceState_sameDeps` — acyclicity preserved
- `bfsUniverse_of_storeServiceState_sameDeps` — BFS universe preserved
- `serviceCountBounded_of_storeServiceState_sameDeps` — count bound preserved
- `serviceGraphInvariant_of_storeServiceState_sameDeps` — composed invariant preserved

Preservation theorems:

- `serviceStart_preserves_serviceGraphInvariant` — status change preserves graph invariant (dependencies unchanged)
- `serviceStop_preserves_serviceGraphInvariant` — status change preserves graph invariant (dependencies unchanged, extra backing-object branch)
- `serviceRegisterDependency_preserves_serviceGraphInvariant` — inline `serviceCountBounded` transfer through dependency insertion

## WS-H15: Platform & API Hardening (v0.14.7)

### Syscall capability-checking (WS-H15c)

Introduces the seL4-style capability-gated syscall entry pattern:

- **`SyscallGate`** — structure encoding caller identity, CSpace root, capability
  address, depth, and required access right.
- **`syscallLookupCap`** — resolves a capability through `resolveCapAddress` and
  validates the required access right.
- **`syscallInvoke`** — gated combinator that composes lookup with an operation.
- **Soundness theorems**: `syscallLookupCap_implies_capability_held` (successful
  lookup implies capability held with required right), `syscallLookupCap_state_unchanged`
  (lookup is read-only), `syscallInvoke_requires_right` (successful invocation
  implies caller held required capability).
- **13 `api*` wrappers**: capability-gated entry points for IPC, CSpace, lifecycle,
  VSpace, and service operations.

### Adapter proof hooks (WS-H15d)

- **`advanceTimerState_preserves_proofLayerInvariantBundle`** — generic theorem
  proving timer advancement preserves the full 7-conjunct invariant bundle,
  applicable to any `RuntimeBoundaryContract`.
- **`simRestrictiveAdapterProofHooks`** — concrete `AdapterProofHooks` instance
  for the simulation restrictive runtime contract.
