# AUDIT v0.30.11 — Comprehensive Pre-1.0 Audit

**Cut date:** 2026-04-26
**Audited version:** 0.30.11 (post WS-AN closure)
**Scope:** every Lean module, all Rust crates, build infrastructure, tests,
scripts, CI workflows, and documentation under canonical ownership.
**Branch:** `claude/comprehensive-project-audit-5uUqP`
**Auditor methodology:** parallel deep-read across eight subsystem
partitions, each tasked with reading source rather than trusting docstrings,
followed by spot-verification of the highest-impact claims against the live
codebase.

This audit succeeds `AUDIT_v0.30.6_COMPREHENSIVE.md` (now archived under
`docs/dev_history/audits/` after WS-AN closure) and is intended to be
the **pre-1.0 readiness checkpoint**. It does not yet have a paired
`WORKSTREAM_PLAN`/`BASELINE` because remediation has not started; those
artefacts will be added when (and only when) the next remediation workstream
opens. Per the `docs/audits/` README, this leaves the v0.30.6 artefacts in
place until the v0.30.11 remediation workstream closes.

## Verified codebase shape (re-counted at audit time)

| Metric | Value | Source |
|---|---|---|
| Lean production files | **167** | `find SeLe4n -name '*.lean' \| wc -l` |
| Lean production lines | **109,787** | `find SeLe4n -name '*.lean' -exec wc -l {} +` |
| Lean test suites | 28 | `find tests -name '*.lean' \| wc -l` |
| Lean test lines | ~18,925 | per `codebase_map.json` |
| Rust crates | 4 | `sele4n-{types,abi,hal,sys}` |
| Rust production lines | ~13,391 | `find rust -name '*.rs' -exec wc -l` |
| `sorry` / `axiom` in Lean | **0** | `grep -rn '\bsorry\b\|\baxiom\b' SeLe4n` |
| `unsafe` blocks in HAL | **53** | `grep -rE 'unsafe \{' rust/sele4n-hal/src` |
| `unsafe` blocks in non-HAL crates | 1 (sele4n-abi `raw_syscall`) | grep |
| Pre-commit hook installed | yes (symlink) | `.git/hooks/pre-commit` |

## Headline conclusion

The kernel is **production-ready for a v1.0 cut** with two pre-1.0 cleanups
(metric refresh, stale-marker sweep) and a tracked debt register of seven
post-1.0 maintainability tasks. **No correctness, security, or safety
defects were found.** No `sorry`, `axiom`, `Classical.choice`, or
unjustified `unsafe` is present anywhere in the production surface.
Hardware-binding closure (Theme 4.x) and information-flow composition
(IF-M4) are both faithful. The single architectural concern — the size of
`InformationFlow/Invariant/Operations.lean` (3857 LoC) and
`Scheduler/Operations/Preservation.lean` (3779 LoC) — is a maintainability
matter, not a correctness one, and is already partially staged for split
in the AN5/AN6 deferred-items plan.

## Document layout

1. Severity table and findings index
2. Subsystem audits (eight partitions)
3. Cross-cutting findings
4. Verified pre-1.0 documentation drift
5. Debt register (DEBT-* IDs introduced by this audit)
6. Recommendations and v1.0 sign-off checklist

---

## 1. Severity table and findings index

Severity legend — **C** critical (must fix before tag), **H** high (should
fix before tag), **M** medium (post-1.0 maintainability), **L** low
(cosmetic / cleanup), **I** informational.

### Pre-1.0 (must address before tagging v1.0)

| ID | Severity | Area | Summary |
|---|---|---|---|
| DEBT-DOC-01 | H | docs | README ↔ `codebase_map.json` metric drift (LoC ≈ 900, theorem decls 13). Verified live. |
| DEBT-RUST-02 | M | rust | Stale workstream-ID markers in `rust/sele4n-hal/src/{trap.rs:186,lib.rs:89}` claimed by predecessor audit (H-24); this audit could **not** reproduce the `WS-V`/`AG10` markers (grep returns zero hits). Either H-24 was already discharged silently or the markers used a different spelling — re-confirm and close H-24 or open replacement finding. |

### Post-1.0 maintainability (tracked, non-blocking)

| ID | Severity | Area | Summary |
|---|---|---|---|
| DEBT-ST-01 | M | Model/State+Builder | 17-conjunct tuple-projection chain in `allTablesInvExtK` plus the named-accessor workaround in Builder.lean. Acknowledged debt (AF5-F). |
| DEBT-CAP-01 | M | Capability/Operations | Shared frame-helper extraction across the cspaceInsertSlot preservation block (theorems start at line 471 — `_preserves_scheduler`, `_preserves_services` 501, `_preserves_objects_ne` 529, etc.). |
| DEBT-CAP-02 | L | Capability/Invariant/Preservation/* | Tactic-extraction for the Insert/Delete/Revoke proof scaffold (case-split → unfold → storeObject thread-through). |
| DEBT-SCH-01 | M | Scheduler/Operations/Preservation | 3779-LoC file is cohesive but ripe for per-invariant split (5–6 files). |
| DEBT-SCH-02 | M | Scheduler/Liveness/WCRT | Discharge `hDomainActiveRunnable` and `hBandProgress` from kernel invariants. |
| DEBT-IF-01 | M | InformationFlow/Invariant/Operations | 3857-LoC file ready for thematic split (AN6-A retirement). |
| DEBT-IF-02 | L | InformationFlow/Operations frame lemmas | Land closure-form discharge for the six capability dispatch arms (frame lemmas exist; just need to be wired into the per-op theorems). |
| DEBT-SVC-01 | M | Service/Invariant/Acyclicity | 1043-LoC file split (AN4-H.SVC-M04) blocked on Lean elaborator fragility around private BFS-boundary lemma `simp` shapes. |
| DEBT-IPC-01 | I | IPC/DualQueue/WithCaps | `capRecvSlot` H3 IPC-buffer extraction deferred to H3 phase. |
| DEBT-IPC-02 | L | IPC/Operations/Endpoint | AK10 rename `ipcInvariant → notificationInvariantSystem`. |
| DEBT-RT-01 | L | RadixTree/Core | Add `radixWidth ≤ 21` assertion if/when FrozenOps is promoted to production. |
| DEBT-FR-01 | L | RobinHood docs | Document FrozenOps "experimental, not in v1.0" status in README and SECURITY_ADVISORY (today only the file header says it). |
| DEBT-RUST-01 | M | sele4n-abi conformance tests | Extend conformance matrix to syscall-level error-encoding scenarios. |
| DEBT-TST-01 | L | tests/NegativeStateSuite | 3714-LoC monolith — split or document internal sectioning for maintainability. |
| DEBT-BOOT-01 | L | Platform/Boot | AF3-F minimum-configuration validation (≥1 thread, valid scheduler state). |

No findings of severity **C** were produced by any of the eight partitions
or by spot-verification.

---

## 2. Subsystem audits

### 2.1 Core Lean modules — `Prelude`, `Machine`, `Model`

**Files:** `SeLe4n.lean`, `Main.lean`, `Prelude.lean` (1830), `Machine.lean`
(977), `Model/Object{,/Types,/Structures}.lean`, `Model/State.lean` (2226),
`Model/{IntermediateState,Builder,FrozenState,FreezeProofs}.lean`.

**Findings.**

- **Clean files**: `SeLe4n.lean`, `Main.lean`, `Model/Object.lean`,
  `Model/IntermediateState.lean` — no findings.
- **Machine.lean** carries an intentional non-lawful `BEq RegisterFile`
  (lines 290–306) with a witnessing counter-example
  (`not_lawfulBEq`); safety analysis (X5-G, lines 308–327) confirms no
  correctness impact. `noOverlapAux` is O(n²) but bounded by hardware
  region count (~5 on RPi5).
- **Prelude.lean** — no `sorry`/`axiom`/incomplete proofs; repetitive
  `LawfulHashable`/`LawfulBEq` and roundtrip-theorem boilerplate is
  intentional uniform coverage. No new identifier-hygiene defects.
- **Model/Object/Types.lean** — `IpcMessage` carries `Array RegValue`
  (was `Nat`) per S4-D, justified. TCB BEq manually compares 22 fields
  because `RegisterFile` BEq is non-lawful; intentional.
  `Notification.waitingThreads : List ThreadId` rationale documented at
  lines 850–874.
- **Model/State.lean — DEBT-ST-01**: 17-conjunct `.2.2.2…` accessor
  depth in `allTablesInvExtK` (lines 386–395). Acknowledged at AF5-F as
  a known maintenance burden. `Model/Builder.lean` carries a named-
  accessor workaround (lines 32–97). Functional but fragile.
- **Model/FreezeProofs.lean** (1661) sampled — no `sorry`, no
  `native_decide` outside CI paths; index-parity reasoning around
  lines 294–300 uses `Nat.lt_or_ge` and `List.pairwise_iff_getElem`.
  Solid.

### 2.2 IPC subsystem

**Files:** `Operations.lean`, `DualQueue.lean`, `Invariant.lean` and their
submodules; structural quartet under `Invariant/Structural/{*}.lean`
totalling ~7800 LoC.

**Findings.**

- **Hub purity verified**: `Operations.lean` (41 LoC), `DualQueue.lean`
  (41), `Invariant.lean` (34), `Invariant/Structural.lean` (34),
  `Invariant/NotificationPreservation.lean` (23),
  `Invariant/CallReplyRecv.lean` (21) — all pure imports, AN3-A/C/D/F
  splits documented in headers.
- **Proof debt**: 0 sorry/axiom/Classical/unjustified-unsafe. Single
  `decide` at `QueueNoDup.lean:450` (boolean decision, justified).
- **Critical invariants verified.**
  - Dual-queue head disjointness: `endpointQueueNoDup` defined at
    `Invariant/Defs.lean:924` and bundled into the system invariant
    at line 1289; preservation requires the disjointness precondition
    explicitly (`QueueNoDup.lean:102`).
  - Capability transfer authority: `ipcUnwrapCaps` is gated on
    `endpointGrantRight` (CapTransfer.lean:161); callers extract via
    `endpointRights.mem .grant` (WithCaps.lean:110, 160, 196).
  - Timeout idempotency: `timeoutAwareReceive` clears `timedOut`
    immediately after detection (Timeout.lean:213); explicit-flag
    design retires the prior sentinel-collision fragility (AG8-A).
  - PIP revert safety: `timeoutThread` reverts only `.blockedOnReply`
    (line 105), justified by
    `blockingGraph_pipBoost_implies_blockedOnReply` (line 84).
  - Timeout error-arm reachability:
    `timeoutThread_succeeds_under_preconditions` (line 151) proves the
    error arms unreachable under valid invariants.
- **Performance**: no list-based ops (find/filter/reverse) in hot paths;
  capability-transfer loop bounded at `maxExtraCaps = 3`; intrusive
  dual-queue maintains O(1) head/tail.
- **Code-quality observations** (non-defect): structural quartet at
  ~7800 LoC across four files — within proof-density norms.
  `PerOperation.lean` 6–7-level nested `cases` is bounded by IPC state
  discriminators, not algorithmic depth.

### 2.3 Capability + Scheduler subsystems

**Capability — Operations.lean (1858)**

- `resolveCapAddress_caller_rights_obligation` (line 282) explicitly
  surfaces the seL4-divergence U-M25 contract: intermediate-level
  CSpace traversal does **not** check rights, callers must use
  `capHasRight` guards at the operation layer. Documented and intended.
- Badge derivation is one-way: `mintDerivedCap`
  (`Capability/Operations.lean:748`) enforces rights attenuation via
  `rightsSubset`. The AN4-E null-cap guard inside `mintDerivedCap`
  (lines 749–757) is explicit and unconditional;
  `mintDerivedCap_preserves_non_null` (line 762) discharges the
  obligation that downstream callers do not need to re-check the
  mint result against the null sentinel.
- **DEBT-CAP-01**: cross-subsystem frame-lemma copy-paste across the
  `cspaceInsertSlot` preservation block (theorems start at line 471
  with `cspaceInsertSlot_preserves_scheduler` and continue through
  `_preserves_services` (501), `_preserves_objects_ne` (529), and
  the matching `_invExt` / `_machine` / `_irqHandlers` theorems).
  Refactor candidate (shared frame helper or tactic).

**Capability — Invariant{/Defs,/Authority,/Preservation/*}**

- `Defs.lean` (1056): CDT hypothesis externalisation (lines 29–62)
  intentional; CDT structural properties (completeness, acyclicity)
  composed at the integration layer.
- `Authority.lean`: `cspaceRevoke_local_target_reduction` proves no
  sibling privilege leakage.
- AN4-F.3 split is clean: linear chain Insert ← Delete ←
  CopyMoveMutate ← Revoke ← EndpointReplyAndLifecycle ←
  BadgeIpcCapsAndCdtMaps; hub re-exports tail. **DEBT-CAP-02**: tactic
  extraction for the shared scaffold (unfold → match object store →
  case CNode variant → thread storeObject + storeCapabilityRef).

**Scheduler — Operations/Preservation.lean (3779)**

- **DEBT-SCH-01**: cohesive but the largest single file in the kernel.
  5 ops × ~12 invariants ≈ 60 theorems. Split candidates already
  outlined at lines 3711–3712: per-invariant bundling
  (QueueCurrentConsistent, CurrentThreadValid, TimeSlice,
  DomainAwareness, EDF).

**Scheduler — RunQueue.lean (883)**

- Priority-indexed flat list with RHSet hash backing. O(n) insert/remove
  justified by ≤256-thread RPi5 ceiling and microsecond ops within
  1 ms tick quantum. `flat_wf` + `flat_wf_rev` give bidirectional
  consistency. **Implicit invariant gap**: thread membership ⇒
  threadPriority entry is structurally maintained by the API rather
  than proof-enforced; only runtime-checked via
  `InvariantChecks.runQueueThreadPriorityConsistentB`. Acceptable for
  v1.0; document the trade-off in the file header.

**Scheduler — PriorityInheritance/BlockingGraph.lean**

- `blockingAcyclic` is a **defined invariant predicate** (lines
  148–149), not assumed. Fuel-bounded chain walk uses
  `objectIndex.length` as default. Cycle behaviour (AI6-A) is
  conservative over-promotion only — no priority inversion.

**Scheduler — Liveness/WCRT.lean**

- Fully parametric: `WCRTHypotheses` carries N/B/P/D/L_max as
  structure fields; `wcrtBound = D·L_max + N·(B+P)` proven monotone
  with zero-contention reduction. **No `decide` over a finite
  hardcoded model.**
- **DEBT-SCH-02**: two hypotheses (`hDomainActiveRunnable`,
  `hBandProgress`) externalised for v1.0 (AF1-D). Discharge from
  kernel invariants is post-1.0 work.

**Hub purity verified**: `Capability/Invariant.lean` (23),
`Capability/Invariant/Preservation.lean`, `Scheduler/Operations.lean`
(25), `Scheduler/Liveness.lean`, `Scheduler/PriorityInheritance.lean` —
all pure imports with empty namespace bodies.

**Cross-subsystem layering**: Capability → Scheduler (one-way at hub
level via `Scheduler.Invariant`). Scheduler does not import Capability.

### 2.4 Architecture, Platform, Lifecycle

**Architecture/Assumptions.lean** — AN6-B index
`archAssumptionConsumer` enumerates all five `ArchAssumption` variants;
marker theorem `architecture_assumptions_index` (line 155) uses
exhaustive case analysis so adding an assumption fails elaboration
without a paired proof update. Exemplary template.

**Architecture/AsidManager.lean — TLB-isolation correctness.**
AK3-A rollover fix (lines 165–185) replaces the prior unconditional
`ASID.mk 1` (which broke TLB isolation when ASID 1 was bound) with a
ground-truth `activeAsids` scan over `[1, maxAsidValue)`. Fail-closed
(`none`) when full. Three theorems carry the security guarantee:

- `AsidPool.allocate_result_fresh` (line 463) — returned ASID is never
  in the pre-call `activeAsids`. Three cases (free-list reuse, bump,
  rollover) discharged via `hFreeDisj`, monotonicity, and
  `List.find?_eq_some_iff_append.mp` (line 339).
- `AsidPool.allocate_preserves_wellFormed` (lines 281–358) preserves
  all 7 conjuncts (Nodup, free⊥active, val<nextAsid, count=length…).
- `maxAsidValue := 65536` (16-bit, ARM ARM D8.12, line 75). **Race-free.**

**Architecture/VSpaceInvariant.lean — VSpace closure.**
7-tuple bundle (lines 123–130): vspaceAsidRootsUnique, vspaceRootNonOverlap,
asidTableConsistent (bidirectional), wxExclusiveInvariant,
boundedAddressTranslation, vspaceCrossAsidIsolation,
canonicalAddressInvariant. Round-trip TPI-001 theorems all proved:
`vspaceLookup_after_map` (585), `vspaceLookup_map_other` (634),
`vspaceLookup_after_unmap` (687), `vspaceLookup_unmap_other`. **Genuine
semantic correctness, not reflexivity.** Helper
`asidTableConsistent_of_storeObject_vspaceRoot` (139) shared by map
and unmap success proofs.

**CrossSubsystem.lean (3309)** — All 11 cross-subsystem predicates
(lines 189–266) are actively consumed downstream. **Not a dumping
ground.** `collectQueueMembers` fuel-sufficiency uses an informal
argument backed by acyclicity + fuel-exhaustion-returns-`none`;
formal `QueueNextPath` ↔ `queueNext` connection is recorded as
TPI-DOC / AJ-L08 deferred post-1.0. AE5-A `Option (List ThreadId)`
return type prevents silent truncation.

**Platform/Boot.lean — 5-gate validation.**
`bootFromPlatformChecked` (line 696) runs:

1. `config.wellFormed` — `irqsUnique` + `objectIdsUnique` (HashSet,
   97–136)
2. `bootSafeObjectCheck` (534) — endpoints empty, TCBs ready, CNodes
   structurally valid, VSpaceRoots rejected
3. AK9-C: `irqHandlersReferenceNotifications` (659) — every IRQ
   handler ObjId references a `.notification`
4. AK9-F: MachineConfig.wellFormed + `physicalAddressWidth ≤ 52`
   (ARMv8 LPA)
5. AK9-G: `bootEnableInterruptsOp` post-boot

Correctness theorem `bootFromPlatformChecked_eq_bootFromPlatform`
(747). **DEBT-BOOT-01**: AF3-F minimum-configuration check (≥1
thread, valid scheduler state) deferred post-1.0.

**Platform/DeviceTree.lean** — `readBE32`/`readBE64` use
`ByteArray.get?` (none on OOB) plus explicit bounds guards.
`extractMemoryRegions` rejects truncated entries explicitly (V4-H /
M-HW-8). FDT token constants named (247–251). `parseFdtHeader`
validates blob ≥ 40 B, magic 0xD00DFEED, version ≥ 16, totalsize.
**No silent data loss on malformed FDT.**

**Platform Contract / Sim / RPi5 symmetry** — `Sim/Contract.lean`
provides both permissive and substantive (S5-D) bindings; U8-A /
U-L16 `simSubstantiveMemoryMap_eq_machineConfig` proves no drift
between Sim contract memory map and `simMachineConfig.memoryMap`.
AJ-L11 PA-width divergence (Sim 52-bit, RPi5 44-bit) is intentional.

**Lifecycle/Suspend.lean — H3 atomicity.** Suspension sequence
documented (line 210). Re-lookup of TCB after `cancelIpcBlocking`
(223–244) is defensive even though `cancelIpcBlocking` preserves
`schedContextBinding` structurally. **H3-ATOMICITY window** (235–237)
between G2 and G3 documented as requiring interrupt-disabled
execution on hardware (Rust HAL `with_interrupts_disabled`); the
sequential model is trivially safe.

### 2.5 InformationFlow + Service + SchedContext

**InformationFlow.**

- Hub purity: `Enforcement.lean` (22), `Invariant.lean` (23) — pure imports.
- `Operations.lean` (3857) — **DEBT-IF-01**: 12 thematic sections
  documented at the head, all 85 theorems are NI-preservation /
  lowEquivalent for specific kernel ops. Cohesive but ripe for split.
- `Projection.lean` (782) — sound, not leaky. `st.scheduler` field
  reads (lines 339, 346, 365, 370, 375) are intentional observable
  state per WS-H8 / A-36; `objects` map projection (327) does not
  leak non-observable pointers.
- `Policy.lean` (1023) — integrity model intentionally inverts BIBA
  (U6-I / M22) with witnessing theorems
  (`integrityFlowsTo_is_not_biba`,
  `integrityFlowsTo_denies_write_up_biba_allows`). Declassification
  gated to a single op (`declassifyStore`, Soundness.lean:516).
- `Composition.lean` (1181) — **IF-M4 main theorem**
  `composedNonInterference_step` (line 536). 30+ inductive
  `NonInterferenceStep` arms each carry full domain-separation
  hypotheses. Composition is faithful (two-sided projection
  preservation + transitivity).
- **DEBT-IF-02**: 6 capability dispatch arms ship closure-form
  theorems (`hProjEq` hypothesis); discharge via existing frame
  lemmas (`resumeThread_frame_insert`,
  `schedContextBind_frame_runQueue_rebucket` at 3648, 3807, 3821, 3846)
  is AN6-A retirement work.

**Service.**

- Hub purity: `Invariant.lean` (26) — pure imports.
- `Acyclicity.lean` (1043) — **WS-D4 / TPI-D07 fix** at line 75:
  replaced unsound BFS-based definition (vacuously true on
  `src=target`) with declarative non-trivial-path; correctly captures
  acyclicity. Layered proof: declarative graph → structural lemmas →
  storeServiceState frame lemmas → register/revoke preservation.
  **DEBT-SVC-01**: AN4-H.SVC-M04 file split deferred (Lean
  elaborator fragility on private BFS-boundary lemma `simp` shapes,
  same blocker as AN4-G.5 in Lifecycle); 1043 LoC under 2000 ceiling.
- `Registry.lean` (416) — backed by `RHTable`. Operation costs:
  `registerInterface` O(1); `hasEndpointRegistered` /
  `registerService` / `lookupServiceByCap` O(n);
  `revokeService` O(1) erase + O(n) dependency removal. Acceptable
  for registry size << 1000. AE5-B / U-20 uniqueness check at line 84
  prevents duplicate endpoint registrations. Per-thread observable
  timing via Robin Hood probing is accepted as a deployment-layer
  concern (C-L6).

**SchedContext.**

- Hub purity: `Invariant.lean` (56) intentionally imports only
  `Defs.lean` (not Preservation/PriorityPreservation) to break a
  cycle. Compile-time witness (lines 49–56) re-derives
  `schedContextWellFormed` to fail the build if the import is
  removed. Documented and intentional.
- `ReplenishQueue.lean` (504) — sorted-insertion uses **strict `<`**
  (not `≤`) for FIFO same-tick fairness (AK2-F / S-M04). Correctness
  (`insertSorted_preserves_sorted` 278–299) discharged inductively
  with helpers (`pairwiseSortedBy_head_le_all`,
  `insertSorted_head_ge`). `popDue` is single-pass prefix split on
  the sorted invariant. Cached size invariant maintained on every
  mutation.
- `PriorityManagement.lean` (362) — **MCP authority** enforces both
  the hardware ceiling (`maxHardwarePriority := 255` at line 81;
  AK8-D / C-M05) and `targetPriority ≤ callerTcb.maxControlledPriority`
  (`validatePriorityAuthority` at line 99).
  `setMCPriorityOp` (327) rejects `newMCP > caller MCP` (336) and
  caps the target's priority (344–350) if it exceeds the new MCP.
  **No escalation path.** Soundness witness
  `validatePriorityAuthority_bound` (110–117) proves every authorised
  priority fits hardware width.

### 2.6 Verified data structures (RobinHood, RadixTree, FrozenOps)

**RobinHood (4541 LoC across Core/Set/Bridge/Invariant trio).**

- Probe distance `(i + capacity − idealIndex) % capacity`
  (Core.lean:23) is underflow-safe; `displacement_roundtrip` lemma
  witnesses correctness.
- Robin Hood three-way split (Core 130–161): empty → place; match →
  update; `resident.dist < d` → swap. Textbook and clean.
- Load-factor invariant `loadFactorBounded` (`size·4 ≤ capacity·3`,
  Defs.lean:50). Resize triggers at `size·4 ≥ capacity·3`
  (Core.lean:409); doubles capacity → post-resize load ≈ 50%.
  `minPracticalRHCapacity := 16` (Bridge 50, 105) matches seL4 CNode
  minimum 2^4.
- **PCD (probeChainDominant)** is preserved by every operation —
  insert via insertLoop (Preservation 1057–1150), erase via
  relaxedPCD → PCD transition (1772–1893). Backshift uses
  gap-allowed `relaxedPCD` framework, reconciled at termination.
- get-after-insert / get-after-erase proved for **all** keys
  including collision cases (Bridge 198, 208, 219, 229).
- **BEq quirk (AK8-J)**: `LawfulBEq (RHTable α β)` is not provided as
  an instance; callers must supply `[LawfulBEq β]`. Documented
  (114–139).
- Bridge (1111) exports `invExt`/`invExtK` because the kernel must
  reason about resize-triggered load and erase preconditions; no
  leakage of probe-distance/insertion-loop/backshift internals.

**RadixTree (1233 LoC).** All 8 ops live, 24 proofs verified.
`extractBits` (Core.lean:37) is `(n >>> offset) % (2^width)`. Width is
parameter; typical `radixWidth=4`. **DEBT-RT-01**: no validation that
`offset + width ≤ 64`; current usage safe; add `radixWidth ≤ 21`
assertion if FrozenOps is promoted post-1.0. `lookup_insert_ne`
precondition (distinct radix positions for distinct slots,
Invariant.lean:89) matches the well-formed CNode invariant.

**FrozenOps (1884 LoC) — experimental.** Verified:
`grep -rl 'import SeLe4n.Kernel.FrozenOps' SeLe4n` returns only
FrozenOps internals plus six test files; **no production module
imports it**. `Commutativity.lean` Q7-D theorems
(`frozenMap_set_get?_same` plus 11 `frozenStoreObject` preservation
theorems) are complete but lack hardware validation.
**Recommendation**: exclude from v1.0 release surface; gate promotion
on RPi5 WCRT data per AG8-D. **DEBT-FR-01**: surface this status in
README and SECURITY_ADVISORY (today only Core.lean header says it).

### 2.7 Rust workspace (4 crates, ~13.4K LoC)

**Verified at audit time** (re-counted):
- `unsafe { … }` blocks: HAL **53**, sele4n-abi **1**
  (`raw_syscall`), sele4n-types/sele4n-sys **0**.
- 0 runtime dependencies; build-time only `cc = "1.2"` (sele4n-hal),
  pinned per AN8-E R-HAL-L3.

**sele4n-types** (~555). 15 newtype identifiers. KernelError 52
variants 0–51 + sentinel 255 with roundtrip tests
(`test_new_variants_discriminants`, `test_lean_rust_correspondence`).
AccessRights `TryFrom<u8>` rejects > 0x1F. Sentinel value 0 reserved
across ObjId/ThreadId/CPtr/ServiceId/InterfaceId.

**sele4n-abi** (~1.4K). `#![deny(unsafe_code)]` crate-wide; the
single `pub unsafe fn raw_syscall` (trap.rs:32) is annotated with a
targeted `#[allow(unsafe_code)]`. asm! `clobber_abi("C")` declares all
AAPCS64 caller-saved registers; explicit `inout` for x0–x5; x6
`lateout(_)`; x7 input-only. MessageInfo enforces 20-bit label
(V2-H), 2-bit extra_caps, 7-bit length with private fields and
`new()`/`decode()` validation. RegisterFile uses
`get(idx)→Option<u64>` / `set(idx,val)→Option<()>` (U3-G / U-L09).
IpcBuffer 960-byte `#[repr(C)]` with compile-time `offset_of!`
assertions; `set_mr(0..3) → Err(InvalidArgument)` matches `get_mr()`
asymmetry fix (R-ABI-M04).

**sele4n-hal** (~3.3K). 53 `unsafe { … }` blocks across 15 files,
each documented with ARM ARM section reference. Highlights:

- MMIO (mmio.rs 50–125): `read_volatile`/`write_volatile` with
  runtime `assert!()` alignment checks (production, not
  `debug_assert!`).
- Barriers (DMB/DSB/ISB/CSDB per ARM ARM D17.2). `BarrierKind` enum
  (AN9-H). CSDB after ESR class extraction in
  `handle_synchronous_exception` (Spectre v1, AG9-F).
- GIC-400 init order matches ARM GIC-400 TRM §3.1/§4.3; self-check
  (AN8-D / RUST-M05) reads back GICD_ITARGETSR[8] and halts on
  mismatch (aarch64 only). `is_spurious(intid >= 1020)` per spec.
  `gicd::ICENABLER_BASE` carries `#[allow(dead_code)]` documented as
  future selective-disable surface.
- MMU (AK5-C / R-HAL-H03): SCTLR_EL1 set as full bitmap (computed
  exact value, not OR-onto-reset). MAIR/TCR/TTBR per ARMv8 4 KiB
  granule, 48-bit VA, 44-bit PA.
- TrapFrame (AK5-F): 36 × 8 = 288 B, 16-byte aligned. Compile-time
  `offset_of!` assertions. AK5-F adds ESR_EL1 (272) and FAR_EL1 (280)
  read-only snapshots to prevent nested-exception corruption.
- `build.rs` regression guard (AN8-B.5 / H-18) rejects the legacy
  literal MPIDR mask in `boot.S`; enforces single-source-of-truth via
  symbol `MPIDR_CORE_ID_MASK` (AK5-I).
- UART PL011 (AK5-H) 115200 baud at 48 MHz with compile-time
  assertions; `init_with_baud(0)` uses `debug_assert!()` only —
  release builds rely on the compile-time witness.

**sele4n-sys** (~1.2K). 0 unsafe. All wrappers return
`KernelResult<T>` with `?` propagation. AN8-D RUST-M08:
`sched_context_configure` and `service_register` write the 5th
argument to IPC-buffer overflow slot 0 per AK4-A contract (matches
Lean `IpcBufferRead.lean`).

**Conformance tests** (~1459 LoC). RUST-XVAL-001..019 cover register
encoding for IPC, CSpace, Lifecycle, VSpace, Service, Notification,
SchedContext, TCB. **DEBT-RUST-01**: edge-case error encoding (label
overflow, etc.) is unit-tested in `message_info.rs` but not in
system-level conformance — extend post-1.0.

**DEBT-RUST-02 reproduction status.** The predecessor audit's H-24
finding (stale `TODO(WS-V/AG10)` in `rust/sele4n-hal/src/trap.rs:186`
and `lib.rs:89`) **could not be reproduced** — `grep -nE
'TODO\(WS-V|TODO\(AG10|WS-V|AG10' rust/sele4n-hal/src/{trap,lib}.rs`
returns zero matches. Either H-24 was discharged silently or the
markers used a different spelling. Action: re-confirm or close H-24
in `AUDIT_v0.30.6_DISCHARGE_INDEX.md`.

### 2.8 Tests, scripts, CI, documentation

**Tests** — 28 `.lean` suites, ~18,925 LoC. All registered in tier
scripts (`test_tier2_negative.sh`, `test_tier2_trace.sh`, scenario
catalog). No dead suites. `Testing/Helpers.lean` primitives carry
non-empty-string runtime guards (AN11-E.9 / TST-M09, lines 31–95);
`expectError` checks `KernelError` equality (line 60), not substring
— no false positives. ObjId range partitioning (lines 98–114)
prevents collisions across concurrent runs. **DEBT-TST-01**:
`NegativeStateSuite` is a 3714-line monolith — split or document
sectioning post-1.0.

**Scripts** — 40 shell + 7 python.

- `set -euo pipefail` in **100 %** of shell scripts.
- Trap-based cleanup discipline:
  `_common.sh:119–163` (`_SELE4N_TMPFILES` array +
  `_sele4n_tmpfile_cleanup_handler`); per-script `trap … EXIT` for
  every `mktemp` (test_qemu, test_tier2_*, setup_lean_env). The
  `_common.sh` `eval` at line 140 is the only `eval` and is used to
  re-invoke a saved trap with documented quoting inversion.
- All variable expansions quoted; `mktemp` with templates (no naked
  `/tmp`); paths derived via `cd "$(dirname "${BASH_SOURCE[0]}")/.."`.
- Python: type hints throughout; `subprocess.run([…], check=True)`
  list-form (no `shell=True`); explicit JSON schema validation in
  `scenario_catalog.py:20–79`; no `eval()`.
- Pre-commit hook is installed as a symlink — verified at audit time
  via `ls -la .git/hooks/pre-commit` →
  `→ ../../scripts/pre-commit-lean-build.sh`.

**CI** — five workflows.

- `lean_action_ci.yml`: `pull_request` (not `pull_request_target`),
  SHA-pinned actions, `cancel-in-progress: true`, job-tagged cache
  keys (`-fast`/`-smoke`/`-full`) preventing smaller jobs from
  overwriting larger `.lake/build` (AN11-F).
- `platform_security_baseline.yml`: ARM runner with
  SEGMENT_DOWNLOAD_TIMEOUT_MINS=30; gitleaks/Trivy/CodeQL gated on
  non-fork PRs; uses canonical `github.token`.
- Tier 0 hygiene gate enforces SHA-pinning
  (`test_tier0_hygiene.sh:86`).

**Documentation.**

- **DEBT-DOC-01 (verified live)**: `codebase_map.json` says
  production_loc `109,801`, theorem decls `3,199`, files `168`;
  README.md says `108,891`, `3,186`, `167 files`. Live `wc -l`
  returns `109,787` lines and `find` returns `167` files — README is
  closer on file count, JSON is closer on LoC.
- Audit lifecycle followed: v0.30.6 active comprehensive +
  workstream plan + baseline + discharge index, v0.29.0 deferred
  retained per "one active audit" rule with closure summary in
  `AUDIT_v0.29.0_DEFERRED.md`.
- `THIRD_PARTY_LICENSES.md` covers `cc 1.2.59`, `find-msvc-tools
  0.1.9`, `shlex 1.3.0`; matches `rust/Cargo.toml`. Zero runtime
  deps confirmed (line 170–173).
- `CONTRIBUTING.md` and `CLAUDE.md` synchronised with workflow.

---

## 3. Cross-cutting findings

### Identifier hygiene (CLAUDE.md "Internal-first naming")

CLAUDE.md prohibits encoding workstream IDs in identifiers (theorems,
fns, structures, files). Every partition reported the same result:
**zero new identifiers encode workstream IDs.** All workstream tags
(WS-*, AN*-*, AK*-*, AG*-*, etc.) appear in **docstrings and
comments only**. Pre-existing legacy identifiers (`ak8a_*`,
`an2f3_*`, etc.) are explicitly grandfathered by CLAUDE.md until
touched by a workstream that can rename them in the same commit.

### Re-export hub purity (sampled and verified)

| Hub | Lines | Status |
|---|---|---|
| `Kernel/IPC/Operations.lean` | 41 | pure imports |
| `Kernel/IPC/Invariant.lean` | 34 | pure imports |
| `Kernel/Capability/Invariant.lean` | 23 | pure imports |
| `Kernel/Scheduler/Operations.lean` | 25 | pure imports |
| `Kernel/InformationFlow/Enforcement.lean` | 22 | pure imports |
| `Kernel/InformationFlow/Invariant.lean` | 23 | pure imports |
| `Kernel/Service/Invariant.lean` | 26 | pure imports |
| `Kernel/SchedContext/Invariant.lean` | 56 | imports + compile-time guard |

### Proof-debt summary

| Category | Count | Notes |
|---|---|---|
| `sorry` | **0** | grep-verified |
| `axiom` | **0** | grep-verified |
| `Classical.choice` | **0** | grep-verified across audited subsystems |
| `unsafe` (Lean) | 0 | n/a in Lean kernel |
| `unsafe { … }` (Rust HAL) | 53 | each ARM-ARM-cited |
| `unsafe { … }` (Rust non-HAL) | 1 | sele4n-abi `raw_syscall`, justified |
| `decide` over finite hardcoded model | 0 | WCRT is fully parametric |

### Security-property checklist

| Property | Status | Witness |
|---|---|---|
| Badge derivation one-way | ✓ | `mintDerivedCap` rights attenuation (Capability/Operations.lean) |
| No sibling privilege leakage on revoke | ✓ | `cspaceRevoke_local_target_reduction` |
| CDT acyclicity invariant tracked | ✓ | `Invariant/Defs.lean` lines 29–62 |
| Blocking-graph acyclicity proved-not-assumed | ✓ | `blockingAcyclic` is a defined predicate |
| WCRT bound parametric | ✓ | `WCRTHypotheses` fields, monotonicity |
| ASID rollover preserves TLB isolation | ✓ | `AsidPool.allocate_result_fresh` |
| W^X invariant on VSpace | ✓ | `wxExclusiveInvariant` in 7-tuple bundle |
| VSpace lookup round-trips | ✓ | TPI-001 four theorems |
| Boot-time IRQ handler validity | ✓ | AK9-C `irqHandlersReferenceNotifications` |
| MCP authority bounds (no escalation) | ✓ | `validatePriorityAuthority_bound` |
| Information-flow composition (IF-M4) | ✓ | `composedNonInterference_step` |
| Single declassification site, gated | ✓ | `declassifyStore` + Soundness 520–529 |
| Service dependency acyclicity | ✓ | declarative `serviceDependencyAcyclic` (post WS-D4 fix) |
| FDT parser bounds-checked | ✓ | `readBE32`/`readBE64` + `parseFdtHeader` |

---

## 4. Verified pre-1.0 documentation drift (DEBT-DOC-01)

Confirmed live by `python3 -c "import json; print(json.load(open('docs/codebase_map.json'))['readme_sync'])"`
and `wc -l`/`find` on the production tree:

| Field | README | codebase_map.json | actual (live) |
|---|---|---|---|
| version | 0.30.11 | 0.30.11 | 0.30.11 |
| production_files | 167 | 168 | **167** |
| production_loc | 108,891 | 109,801 | **109,787** |
| proved_theorem_lemma_decls | 3,186 | 3,199 | (not directly grep-able; trust JSON) |

**Recommendation**: before tagging v1.0, run

```bash
./scripts/report_current_state.py
./scripts/sync_readme_from_codebase_map.sh
```

and commit the refresh in a single PR titled "DEBT-DOC-01: refresh
README ↔ codebase_map.json metrics for v1.0 cut". Verify
`scripts/check_version_sync.sh` and `scripts/sync_documentation_metrics.sh`
both pass before merge.

---

## 5. Debt register

All DEBT-* IDs introduced by this audit, indexed for the next
remediation workstream's `WORKSTREAM_PLAN.md`.

| ID | Severity | Location | Action |
|---|---|---|---|
| DEBT-DOC-01 | H (pre-1.0) | README.md, docs/codebase_map.json | Refresh metrics. |
| DEBT-RUST-02 | M (pre-1.0) | docs/dev_history/audits/AUDIT_v0.30.6_DISCHARGE_INDEX.md | Reconfirm or close H-24. |
| DEBT-ST-01 | M | SeLe4n/Model/State.lean, Builder.lean | Replace 17-conjunct projection chain with structure or HasField projections. |
| DEBT-CAP-01 | M | SeLe4n/Kernel/Capability/Operations.lean 503–641 | Extract shared frame-helper for cspaceInsertSlot preservation. |
| DEBT-CAP-02 | L | SeLe4n/Kernel/Capability/Invariant/Preservation/* | Tactic for Insert/Delete/Revoke proof scaffold. |
| DEBT-SCH-01 | M | SeLe4n/Kernel/Scheduler/Operations/Preservation.lean | Split into 5–6 per-invariant files. |
| DEBT-SCH-02 | M | SeLe4n/Kernel/Scheduler/Liveness/WCRT.lean | Discharge `hDomainActiveRunnable`/`hBandProgress` from kernel invariants. |
| DEBT-IF-01 | M | SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean | Thematic split (AN6-A retirement). |
| DEBT-IF-02 | L | same file | Land closure-form discharge for 6 capability dispatch arms. |
| DEBT-SVC-01 | M | SeLe4n/Kernel/Service/Invariant/Acyclicity.lean | Retry AN4-H.SVC-M04 split when Lean elaborator fragility resolves. |
| DEBT-IPC-01 | I | SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean | Land H3 IPC-buffer extraction for `capRecvSlot`. |
| DEBT-IPC-02 | L | SeLe4n/Kernel/IPC/Operations/Endpoint.lean | AK10 rename `ipcInvariant → notificationInvariantSystem`. |
| DEBT-RT-01 | L | SeLe4n/Kernel/RadixTree/Core.lean | Add `radixWidth ≤ 21` assertion when promoting FrozenOps. |
| DEBT-FR-01 | L | README.md, docs/SECURITY_ADVISORY.md | Surface FrozenOps "experimental, not in v1.0" status. |
| DEBT-RUST-01 | M | rust/sele4n-abi/tests/conformance.rs | Extend conformance to syscall-level error encoding. |
| DEBT-TST-01 | L | tests/NegativeStateSuite.lean | Document or split monolithic suite. |
| DEBT-BOOT-01 | L | SeLe4n/Platform/Boot.lean | AF3-F minimum-configuration validation. |

---

## 6. Recommendations and v1.0 sign-off checklist

### v1.0 release checklist (pre-tag)

- [ ] **DEBT-DOC-01**: refresh README and `codebase_map.json` metrics;
      verify `scripts/check_version_sync.sh` passes.
- [ ] **DEBT-RUST-02**: confirm H-24 is actually closed (this audit
      could not reproduce the markers); update
      `AUDIT_v0.30.6_DISCHARGE_INDEX.md`.
- [ ] **DEBT-FR-01**: add a "FrozenOps is experimental and not in
      v1.0" callout to `README.md` and `docs/SECURITY_ADVISORY.md`.
- [ ] Run `./scripts/test_full.sh` clean.
- [ ] Run `./scripts/test_rust.sh` and
      `./scripts/test_rust_conformance.sh` clean.
- [ ] Run `./scripts/check_website_links.sh` clean.
- [ ] Tag this audit closed by adding
      `AUDIT_v0.30.11_DISCHARGE_INDEX.md` if any of the above
      generates closure-form proof obligations; otherwise note "no
      closure-form artefacts" in `WORKSTREAM_HISTORY.md`.

### Post-1.0 maintainability sequencing (suggested)

1. **First post-1.0 workstream** — DEBT-SCH-01 + DEBT-IF-01 (the two
   ≥3.5K-LoC files). Both are pure splits; risk is low; benefit to
   future contributors is large.
2. **Second** — DEBT-CAP-01 + DEBT-CAP-02 (frame-lemma helper +
   tactic extraction). Reduces Capability proof scaffold by an
   estimated 15–20 %.
3. **Third** — DEBT-SCH-02 (WCRT hypothesis discharge). This is
   genuinely new proof work, not refactoring; needs design-doc
   prelude.
4. **Background**: DEBT-ST-01 (tuple-projection ergonomics) — use
   the next breaking change to `Model/State.lean` to absorb.

### Sign-off

This audit finds **no critical defects**. The kernel exhibits mature
proof discipline (zero `sorry`/`axiom`, parametric WCRT, faithful
information-flow composition), explicit hardware-correctness
boundaries (ASID uniqueness, W^X, TLB coherency, FDT parsing safety,
boot hardening), and disciplined Rust safety (HAL `unsafe` scoped and
ARM-ARM-cited, non-HAL crates `unsafe`-free except for the single
syscall trap).

The two pre-1.0 items (DEBT-DOC-01 metric refresh, DEBT-RUST-02
H-24 reconfirmation) are **documentation hygiene**, not correctness
work, and can be closed in under an hour. Once they are addressed,
the kernel is ready for the v1.0 tag.

— Audit closed 2026-04-26 on branch
`claude/comprehensive-project-audit-5uUqP`.
