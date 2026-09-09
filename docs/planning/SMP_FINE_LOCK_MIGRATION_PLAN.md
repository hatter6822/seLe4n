# SMP Fine-Lock Migration & Commit-Partitioning Plan

> **Status**: **PARTIAL — 9 of 13 PRs landed** (WS-RR RR7.19, `v0.34.70`;
> the header read "2 of 12" and "Tracks B, C and D are entirely unstarted"
> until this row, which was true when RR0 wrote it at `v0.34.26` and false
> from `v0.34.60` on).
> **Track A** (security, 2 PRs) is closed; its High revocation-precision
> finding closed at v0.33.88 (§3.1).
> **Track B** (3 PRs) is closed: the capability-transfer footprint and its
> coverage at `v0.34.60`/`v0.34.61` (RR7.7, RR7.8) and the four capability
> operations' CDT members at `v0.34.62` (RR7.9), which deleted
> `UncoveredLockDomain.capTransferReceiverCnode` and `.cdtNodeAllocation`.
> The third SM3.B-owned domain, `.queueOwnershipProtocol`, closed at
> `v0.34.88` (RR7.38) — outside Track B, whose rows never touched splice
> neighbours — by giving the eleven footprints that can write a *queued* TCB
> the queue owner's write lock.  **Five of the register's seven domains are
> covered and two remain** — `syscallSeamSchedulerDomain` (RR7.39's syscall
> half) and `taintTablePerKeyStore` (owned by the representation cut, Track D's
> PR 13); the register itself is the authority, since its completeness theorem
> fails until a covered constructor is deleted.
> **Track C** (4 PRs) is closed: the decoded-driven resolver at `v0.34.63`
> (RR7.10), the eight declared IPC footprints at `v0.34.64` (RR7.11), the
> **syscall seam's bracket** at `v0.34.65` (RR7.12) and the export-commit
> census at `v0.34.66` (RR7.13).
> **Track D** (commit partitioning, **4 PRs**) is **unstarted** and was
> **restructured at `v0.34.133`** — see its own section for the four findings
> that drove it.  Its first two rows are Lean and gated on **nothing**: the
> footprint-local commit theorem and the representation obligation derived from
> the write-set lists can be proved against the model as it stands, and the
> numbering rule requires them before the runtime that relies on them.  Only the
> two Rust rows are seam-gated, and to **BP6** (per-core readiness — the point at
> which more than one PE executes kernel code) with validation at **BP8**, not to
> "SM10.1", which is WS-BP's 42 sub-tasks rather than a phase.  RR6.27 registered
> the track as a named SM10.1 dependency and that registration is re-pointed with
> it.
>
> **What that means for the v1.0.0 claim.**  "Per-object reader-writer fine
> locks" is true of the **syscall seam** — eight of the thirty-five arms
> declare a footprint and the seam acquires it, `.replyRecv` included for a
> *delegated* reply since WS-OD OD3.5 (`v0.34.128`), which declares the recorded
> server's own TCB lock unconditionally and retires the round-6 refusal that had
> answered `none` there — and not yet true of the
> **per-core scheduler entries**, which commit run-queue and replenish-queue
> state under the SM5.I global entry lock only.  `ExportCommitDisciplineCensus`
> measures it rather than asserting it: **seven seams commit, five bracket**
> (WS-RR RR7.39; two before it).
> Live WCRT is therefore still the global lock's, and the fine-lock bound
> `PerCoreWcrt.lean` proves remains a statement about the intended discipline.
> Of the three lock domains Track C left uncovered, the dynamic PIP chain and
> the CSpace-walk interior closed at `v0.34.90`–`v0.34.91` (RR7.40, RR7.41,
> constructors deleted); RR7.39 gave the scheduler domain a runtime and put the
> three per-core scheduler *entries* inside their declared footprints, leaving
> only the **syscall** seam's scheduler writes — an `endpointSend`'s receiver
> wake — which needs per-arm resolved wake targets and is owned by RR8.

> **Phase**: SM3.C.9 (deferred `withLockSet` migration at the live kernel
> entry) + the capability-transfer footprint closure (**landed** as WS-RR
> RR7.7 + RR7.8 at `v0.34.60`/`v0.34.61`: the send and call footprints declare
> the transfer's destination CSpace root and the state-level lock its CDT write
> needs, and `UncoveredLockDomain.capTransferReceiverCnode` is deleted because
> the domain is covered) + commit partitioning (the fine-lock end-state).
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Origin**: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) §5.2 (SM3.C.9 deferral) + the v0.33.54 audit that registered `UncoveredLockDomain.capTransferReceiverCnode` (closed at `v0.34.61`).
> **Refs**: [`SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](SMP_DECLASSIFICATION_COMPLETION_PLAN.md) §SM9.D (audit-pass-7 closure); [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md) §"Kernel-entry serialisation" (SM5.I).
> **Target releases**: v0.33.55+ across 13 PRs in four tracks.
> **Calendar estimate**: ~10–16 weeks (Track A security first; Track D is the largest — a runtime commit-model change).

## 1. Phase goal

Three coupled closures, sequenced security-first:

1. **Fix the confirmed revocation-precision defect** (§3) — IPC capability
   transfer misattributed CDT provenance to a synthetic source slot, so
   `cspaceRevokeCdt` missed transferred children. High severity, single-core
   reachable, model-level (would have been a live CVE-class defect once the
   kernel boots at SM10.1). **CLOSED at v0.33.88 across five cuts — see
   §3.1 for the closure record**; items 2 and 3 below remain open.
2. **Close the registered footprint defect** `UncoveredLockDomain.capTransferReceiverCnode`
   — the receiver-CNode write (and the previously-undeclared CDT write on
   *every* CDT writer) rides no declared lock. Declare it, prove the coverage,
   delete the registration, re-pin every assertion that encoded the gap.
3. **Land the deferred SM3.C.9 fine-locks work** — migrate the live
   `@[export]` state-committing bodies to wrap their transitions in
   `withLockSet`, then implement the **partitioned commit** that lets the SM5.I
   global entry ticket lock finally be removed (Track D; its two Lean rows are
   gated on nothing, its two Rust rows on **BP6** with validation at **BP8**).

## 2. Context

### 2.1 The footprint defect (registered v0.33.54)

On a caps-carrying rendezvous the live `.send` / `.call` paths run
`ipcUnwrapCaps`, which installs the transferred capabilities into the
**receiver's CSpace root CNode** (`lookupCspaceRoot st' receiverId` →
`ipcUnwrapCaps …`, in `SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean` ~330 and
`EndpointCallDispatch.lean` ~100). `lockSet_endpointSend` /
`lockSet_endpointCall` (`SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean`)
declare **no CNode write** — their one CNode member is the *caller's* root, in
read mode. Under SM3.C.9's fine locks a caps-carrying send and any other writer
of the receiver's root would hold provably disjoint footprints while racing on
the same CNode.

Not live-exploitable today (SM5.I's global entry ticket lock serialises all
commits; `withLockSet` is deferred at the export bodies), so the audit
registered it as `UncoveredLockDomain.capTransferReceiverCnode` (owner SM3.B)
with the violation witness `capTransfer_receiverCnode_write_undeclared`
(`SeLe4n/Kernel/InformationFlow/FineLockFlow.lean`) whose docstring commits:
*closing the gap deletes this theorem*.

Investigating the write set found a wider, previously-undeclared surface: each
installed capability also writes the **CDT** — `cdt.edges` (a `List` cons),
`cdtNextNode` (a global counter), and `cdtSlotNode`/`cdtNodeSlot` at two
`SlotRef` keys — and the four `cspace{Mint,Copy,Move,Delete}` ops write the
identical fields, with **none** of the `lockSet_cspace*` footprints declaring
any of it. There is no documented CDT-lock convention in `Concurrency/`; SMP
safety is currently discharged only by the SM5.I bracket.

### 2.2 The SM3.C.9 deferral

Migrating every `@[export]` body to wrap its transition in `withLockSet`
requires the per-core kernel-state seam SM5 introduced. Of the three
state-committing entries, `suspend_thread_cross_core` is **already** migrated
(v0.32.149, `SyscallDispatchEntry.lean`); `lean_syscall_dispatch_cross_core`
(all 33 syscalls) and `lean_per_core_timer_tick` are not. SM5.I's global entry
ticket lock (`rust/sele4n-hal/src/kernel_entry.rs`) currently serialises all
commits, so none of the fine-lock work is live-exploitable — it is
model-fidelity plus the enabling step for eventually removing the global lock.

The end-state is blocked by **commit partitioning**: `modifyGetKernelState`
(`SeLe4n/Platform/FFI.lean`) commits the whole kernel state in one
read-then-write, so even after every syscall is bracketed, fine locks buy the
model-fidelity tie only — WCRT/concurrency change only when the commit itself
is partitioned and the entry lock removed
(`LockSetForSyscall.lean` runtime-scope note is authoritative; the end-state
docs frame the two as alternatives, `SMP_TLB_SHOOTDOWN_PLAN.md`
§"Kernel-entry serialisation"). This plan **implements** the partitioned
commit (Track D) rather than registering it as debt.

## 3. Confirmed security finding (High) — revocation bypass via IPC cap transfer

> **CLOSED at v0.33.59.**  `TransferCap { cap, srcRef }` now carries the slot each
> capability was resolved from, `resolveExtraCaps` keeps the `ref` it had already
> resolved, and the unwrap loop records the derivation edge from `tc.srcRef`.
> The `chain12b` regression revokes the real source (slot 5) and destroys the
> transferred copy, and revoking the old stand-in address (slot 0) leaves it
> alone — both verdicts swap under the defect.  The synthetic address is pinned
> out of the transfer path by a Tier-3 negative anchor.  The description below is
> retained as the record of the finding.

> **Residual, closed at v0.33.60**: a slot address is not stable across the
> parked window a blocking send creates, so `TransferCap` now carries
> `srcNode : CdtNodeId`, minted at resolution.  This restores `CdtNodeId`'s own
> stated contract — nodes are stable across slot moves, and edges are between
> nodes rather than slot addresses.
>
> **Still open — the delete guard does not see in-flight transfers.**
> `cspaceDeleteSlotCore` detaches a slot from its node, and `cspaceDeleteSlot`
> refuses a slot that already has CDT children.  A *parked* transfer is not yet
> a child, so deleting the source slot during the parked window is permitted and
> orphans the node the message names: no revoke reaches the transferred copy.
> Closure target: make an in-flight transfer visible to `hasCdtChildren`, so
> such a delete is refused exactly as one with a live child is.  This is a
> change to the delete guard, not to propagation.
>
> **Also owed — route the live `.receive` through `endpointReceiveDualWithCaps`.**
> The live receive arm runs no capability unwrap (`API.lean` says so in place),
> so `endpointReceiveDualWithCaps` is a verified function with zero live
> callers, and the parked-sender ordering transfers nothing.  Until it is wired,
> the taint model must not declare receive-side CSpace sinks.  Wiring it changes
> live IPC semantics, the return frame's `extraCaps` count, the golden trace and
> the invariant surface, so it belongs in its own PR alongside this track.

**Verified against primary sources; reported here per the project's
vulnerability-reporting rule.**

**Summary**: A capability transferred over IPC records its capability-derivation-tree
(CDT) parent as a *synthetic* slot — slot 0 of the sender's CSpace root —
instead of the real source slot, because the source `SlotRef` is discarded
before transfer. Revoking the true source capability never reaches its
IPC-transferred children; the receiver keeps authority the revoker meant to
destroy (use-after-revoke / authority leak). Symmetric over-revocation also
exists: every transferred cap is attributed to that one synthetic node, so
revoking whatever really lives at the sender-root's slot 0 destroys unrelated
transferred caps.

**Location / chain** (each link verified):
- `resolveExtraCaps` resolves each `CPtr` to a real `ref : SlotRef` but pushes
  only `cap`, discarding `ref` (`SeLe4n/Kernel/API.lean`) — so
  `IpcMessage.caps : Array Capability` carries no source slot.
- `ipcUnwrapCapsLoop` therefore hardcodes the CDT parent as
  `{ cnode := senderCspaceRoot, slot := Slot.ofNat 0 }`
  (`SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`).
- `ipcTransferSingleCap` records the edge from that synthetic node
  (`SeLe4n/Kernel/Capability/Operations.lean`).
- CDT nodes are keyed by the **full** `SlotRef`, with `ensureCdtNodeForSlot`
  minting a distinct node per distinct ref
  (`SeLe4n/Model/State.lean`), so slot 0's node is not the
  real source's node.
- The live userspace revoke `cspaceRevokeCdt` (the default for untrusted
  invocations) walks `descendantsOf (lookupCdtNodeOfSlot addr)` — the *real*
  source slot's node (`Operations.lean`); local `cspaceRevoke`
  only clears same-CNode siblings.

**Severity / reachability**: High — revocation of derived authority is a core
capability-system guarantee. Single-core reachable, requires only the `Grant`
right the transfer already needs; **not** concurrency-gated, so SM5.I does not
mask it. Model-level today; live once the kernel boots (SM10.1). No theorem is
false — the model faithfully exhibits the bypass.

**Remediation** (PR 2): thread the real source `SlotRef` through the transfer
path (`IpcMessage.caps : Array Capability` → `Array TransferCap` carrying
`(cap, srcRef)`; keep `resolveExtraCaps`'s already-resolved `ref`), record the
edge from the real source, and prove
`transferred_child_is_cdt_descendant_of_real_source` so `cspaceRevokeCdt`
provably reaches it, with a regression test whose load-bearing negative is that
the pre-fix state does not.

### 3.1 The class behind the finding, and where it is closed

The §3 finding was the first of five sightings of one defect, each found
separately and each initially patched where it surfaced:

| # | Where the orphan could be made | Closed at |
|---|--------------------------------|-----------|
| 1 | The transfer named a synthetic source slot, so the edge hung off a node the real source's revoke never walks | v0.33.59 → v0.33.60 (stable node id) |
| 2 | `cspaceDeleteSlot` refused a slot with CDT children, but a parked transfer is not yet a child | v0.33.62 |
| 3 | Retyping the CNode destroyed every slot it held with no such check at all | v0.33.64 |
| 4 | The revoke sweep deletes a descendant slot, and a transfer parked from it still lands | v0.33.64 |
| 5 | The revoke destroys the *derived subtree* without touching the source slot, so the source stays live and its in-flight child lands afterwards | v0.33.88 |

The common cause is structural rather than incidental. Every CDT invariant the
model carries is stated **node → slot**: `cdtCompleteness` says a node with a
slot mapping points at a live object, and its own docstring records that it is
*"robust through `detachSlotFromCdt` because detached nodes lose their mapping
(vacuously satisfying the condition)"*. Nothing states the converse — that a
node standing as a derivation parent must still have a live slot — so orphaning
a node **satisfies** the invariant surface instead of violating it. With no
invariant to fail, each slot-destroying operation had to remember the check on
its own, and the set of such operations is open-ended.

Closing it at the destroyers therefore cannot terminate: three are known, a
fourth is only as far away as the next transition that frees a slot. The fix is
placed at the **creator** instead. `ipcTransferSingleCap` is the single point at
which an `.ipcTransfer` edge comes into existence, and it now declines —
answering `CapTransferResult.sourceRevoked`, leaving the state untouched — when
`lookupCdtSlotOfNode` finds no slot for the source node.
`ipcTransferSingleCap_installed_implies_live_source` states the resulting
guarantee, and it holds against every destroyer at once, including ones not yet
written.

The two guards remain, and are deliberately not the guarantee.
`cspaceDeleteSlot` and the CNode retype arm both refuse via the shared
`slotIsDerivationParent` predicate, because `.revocationRequired` tells a caller
to revoke first, which is a better answer than a capability that silently fails
to arrive. They are the ergonomics; the creator-side check is what makes the
orphan unconstructible.

Sighting 5 is the one that shows where the creator-side check *stops*, and it is
worth stating precisely because the check reads as if it covered everything. It
keys on the **source slot's** liveness: a transfer declines when the node it was
derived from no longer maps to a slot. Revocation of a derived subtree does not
destroy the source slot — the source is exactly what the revoker is keeping — so
`sourceRevoked` never fires, and the in-flight child of a revoked parent lands
after the revoke reports success. The creator-side check answers *"is the thing I
was derived from still there?"*; revocation asks a different question, *"is this
particular derivation one I was told to destroy?"*, and only the revoke knows the
answer.

So revocation carries its own half of the guarantee.
`revokePendingTransfersFrom` sweeps the parked senders and drops the derivations
rooted at the revoked node or any of its descendants, and both `cspaceRevokeCdt`
and `cspaceRevokeCdtStreaming` end with it. The revoke still reports success —
refusing would let a parked sender block revocation indefinitely — and there is
nothing left for a later receive to install.
`revokePendingTransfersFrom_preserves_capabilityInvariantBundle` discharges all
seven conjuncts from `revokePendingTransfersFrom_frame`, which proves the sweep
rewrites TCBs to TCBs and leaves the CDT and both keyed maps untouched.

The two halves together are what the guarantee needs: the creator refuses a
derivation whose *source* is gone, the revoke destroys a derivation whose *parent
edge* was revoked. Neither implies the other, and a future operation that
destroys authority in a third way owes the same question of itself.

Still open, and deliberately: an invariant stating parent-liveness directly
(`∀ node, node is a derivation parent → cdtNodeSlot[node] ≠ none`) would let the
proof surface reject a future destroyer at elaboration time rather than relying
on the creator's runtime check. It belongs with the CDT coverage work in PR 5,
where the four `cspace{Mint,Copy,Move,Delete}` footprints are already being
opened up, and is recorded here so it is not lost.

## 4. PR decomposition (13 PRs, four tracks, security-first)

Each PR is one coherent, independently-green slice with its own patch bump +
`CHANGELOG` entry + docs sync + per-module `lake build`. Tracks are ordered;
within a track later PRs depend on earlier. Complex PRs are broken into ordered
**Steps** (each a self-contained work unit — commit at step boundaries so a
broken build localises).

### Track A — Security (lands before any refactor)

**PR 1 — Save this plan doc.** (this commit) The plan in `docs/planning/` — a
pure documentation add, not a version site, so no version bump and no website
manifest edit (`docs/planning/` is not manifested); the patch bump + `CHANGELOG`
entry begin with the first code PR (PR 2). Lands first so every later PR can
`Refs:` it.

**PR 2 — Revocation-precision fix (the §3 finding).** Report the finding in the
PR body per the vulnerability rule.
- *Step 1 (type):* add `TransferCap { cap : Capability, srcRef : SlotRef }`;
  change `IpcMessage.caps : Array Capability → Array TransferCap`. Rebuild to
  enumerate every break site.
- *Step 2 (producer):* `resolveExtraCaps` / `resolveExtraCapsDetailed` push
  `⟨cap, ref⟩` — they already resolve `ref` and discard it (`API.lean`);
  keep it.
- *Step 3 (consumer):* `ipcUnwrapCapsLoop` passes `tc.srcRef` to
  `ipcTransferSingleCap`, deleting the synthetic slot-0 literal
  (`CapTransfer.lean`).
- *Step 4 (constructors/fixtures):* update message builders, the live WithCaps
  callers (`endpointSendDualWithCaps` / `endpointCallWithCaps`), and any
  `IpcMessage.caps` fixtures.
- *Step 5 (proof):* `transferred_child_is_cdt_descendant_of_real_source`;
  repair the CDT-frame lemmas the type change touches.
- *Step 6 (regression):* a suite scenario + Tier-3 anchor showing
  `cspaceRevokeCdt` on the real source reaches the transferred child (pre-fix
  state does not — load-bearing negative).
- *Verify:* `test_full` (theorems), `test_rust` iff a message/ABI shape moves,
  golden fixtures iff a trace line moves.

### Track B — Footprint closure (the registered `capTransferReceiverCnode` defect)

**PR 3 — Endpoint caps footprint: declaration + algebra** (no coverage claim yet).
- *Step 1:* add the caps optional to `lockSet_endpointSend` /
  `lockSet_endpointCall` as the **outermost two** `lockSetExtendOpt`s, both
  mapping one `receiverCnodeObjId : Option ObjId := none` — `some r` adds
  `(cnodeLock r, .write)` **and** `(stateLevelLock, .write)`; `none` = identity,
  so every capless pin survives by `rfl`. Maxima: **send 6, call 8**
  (`maxLockSetSize` was 8 when this was written; WS-RR RR7.11 raised it to 9,
  measured against the caps-installing `.replyRecv`, so the call footprint is
  now one member below the cap rather than at it).
- *Step 2:* fold `lockSet_endpointCallWithCaps`
  (`IPC/CrossCore/EndpointCall.lean`) → `lockSet_endpointCall … (some
  destCnode)` (tie by `rfl`, kills the parallel-function drift); add the
  send-side analogue.
- *Step 3:* consistency tiers **+2** (one `Option` drives two members — send
  `base_plus_one_opt` → `_three_opts`; call `base_plus_three_opts` →
  `_five_opts`, which exists); `permittedKinds` += `.objStore` for `.send` /
  `.call` (`.cnode` already permitted).
- *Step 4:* size proofs to send ≤ 6 / call ≤ 8; **widen the
  `lockSetTransitions_within_bound` send/call conjunct arity**
  (`Deadlock.lean`) — the silent-unbounding hazard, exactly the SM9.C
  `notificationSignal` fix; re-pin `DeadlockInventory.lean` ("29" → true
  count).
- *Step 5:* `lockSet_endpointCall_reply_write_mem` switches
  `self_write_mem_insertOrMerge` → `mem_write_lockSetExtendOpt` (reply is no
  longer outermost); `lockSet_endpointCall_donation_extension` survives by `rfl`.
- *Step 6:* order-pin shifts (`.cnode` level 2 sorts first; second cnode key by
  `objId.val`) — positional expected lists in `LockSetSuite.lean` /
  `WithLockSetSuite.lean`; the `cspaceMove` two-cnode assertion is the template.
  **Same-root corner test** (receiver root = caller root → `insertOrMerge` +
  `AccessMode.lub` upgrades caller-root READ→WRITE in place, size unchanged).

**PR 4 — `ipcUnwrapCaps` coverage + debt deletion** (the closure).
- *Step 1:* route the state-resolved `lockSet_endpointCallOnCore` (and a new
  `lockSet_endpointSendOnCore`) through the new optional, computing
  caps-presence from the resolved receiver + the caps count/grant in `decoded`.
- *Step 2 (the coverage theorem):* `ipcUnwrapCaps`'s write set ⊆ the declared
  footprint — one for send, one for call. Object half reuses
  `ipcUnwrapCaps_preserves_objects_ne` (`CapTransfer.lean`) +
  `_objects_at_root_orig_or_cnode`; CDT half rides
  `(stateLevelLock, .write)`.
- *Step 3:* delete `capTransferReceiverCnode` — the violation theorem, the
  constructor + list entries (`UncoveredLockDomain` inventory 4→3;
  `mem_all`/`all_nodup`/`_complete` re-elaborate), the §1.13 anchors + GAP
  assertion (`tests/SmpInformationFlowSuite.lean`), and the four Tier-3
  `run_check`s (`scripts/test_tier3_invariant_surface.sh`) → `run_negative_check`
  pins forbidding the constructor / theorem / GAP-label from returning.
- *Step 4:* edit the `=4`→`=3` counts + labels, drop the `|| decide (o =
  recvRoot)` carve-out, restore the blanket "every write rides a declared lock"
  sentence (`SeLe4n/Kernel/InformationFlow/TaintPropagation.lean`).
- *Step 5 (docs):* CLAUDE/AGENTS finding-5 prose + suite tally,
  `REGISTERED_DEBT`, the completion plan, GitBook 12, claim index; add an
  **"Audit-pass-7 closure additions"** block to `SMP_PER_OBJECT_LOCKS_PLAN.md`
  §5.2 (audit-pass-6 PR #793 is the format) + check its §8 box.

**PR 5 — CDT coverage on the four `cspace{Mint,Copy,Move,Delete}` ops** (independent object).
- Declare `(stateLevelLock, .write)` on `lockSet_cspace{Mint,Copy,Move,Delete}`;
  `permittedKinds` += `.objStore`; coverage proofs (the CDT-write shape is
  identical across all four — `Operations.lean`).
- Fix `capabilityOp_modifiedFields` (`SeLe4n/Kernel/CrossSubsystem.lean`,
  `[.objects,.lifecycle]`) to include the four CDT `StateField` constructors.

### Track C — SM3.C.9 fine locks (object domain, dispatch entry)

**PR 6 — Resolver generalization (signature only).** Generalize production
`lockSetForSyscall` from `(sid, callerTid, targetTid, st)` to decoded-driven
resolution (IPC operands are endpoint/notification ObjIds, not ThreadIds);
`.tcbSuspend` preserved, all others still `none` with
`lockSetForSyscall_undeclared_none` re-stated. Production placement referencing
only production `LockSetTransitions` footprints (the staged
`EndpointCall`/`FineLockFlow` resolvers stay staged — partition-safe).

**PR 7 — IPC hot-path footprint declarations.** One coherent PR, one arm per
step: **send, call, reply, replyRecv, receive, signal, wait**. Each step
declares that arm's `lockSetForSyscall` footprint from the decoded operands +
its coverage proof (the transition's write set ⊆ the declared footprint).
Send/call feed the PR 3/4 caps optional. The other 32 arms stay `none`.

**PR 8 — Dispatch-body `withLockSet` migration.**
- *Step 1:* wire `syscallDispatchCrossCoreEntry`
  (`SyscallDispatchEntry.lean`) through the revalidated bracket
  (`RevalidatedEntryOutcome`: resolve → acquire → re-resolve → refuse-on-change)
  with fail-closed `none` fallback (undeclared syscalls run unbracketed exactly
  as today). Model on the already-migrated `suspend_thread_cross_core`
  (v0.32.149).
- *Step 2:* preserve `scheduleLocalSuccessorLive`-inside-the-closure and the
  diff-against-`st''` discipline (do not lift the reschedule out of the bracket).
- *Step 3:* update the `syscallDispatchCrossCoreEntry_def` marker theorem + the
  Rust `build.rs` Check-5 scanner pin.
- *Step 4:* flip the false `PerCoreWcrt.lean` sentence true (the dispatch body
  now brackets, so the SM5.I run loop genuinely acquires the footprints).
- *Verify:* trace byte-identical (the bracket is projection-invisible — confirm
  against the golden fixture).

**PR 9 — Export-body CI gate** (the improve-and-re-pin item the SMP-plan risk
row promised). Tier-1 elaborated-environment probe walking the three `@[export]`
state-committing bodies, failing on any that commits without a `withLockSet`
bracket or an explicit fail-closed-`none` justification; `--self-test` plants a
bare-commit body and asserts detection. Precedent:
`scripts/check_live_arm_per_core_routing.py`.

### Track D — Commit partitioning (the end-state)

**Restructured at `v0.34.133`**, after reading the track back against the code
it is about.  Four findings drove it, and each is answered by the shape below
rather than by a note.

1. **PR 11's theorem had no consumer in PR 12.**  The old PR 12 read
   "compute-from-snapshot + CAS on an `AtomicPtr`; on conflict re-run against
   fresh state (sound by `transition_footprint_local`)".  Re-running is sound by
   *purity*: every transition here is a total function `SystemState →
   SystemState`, so compute-from-snapshot, CAS, retry is the textbook optimistic
   update and needs no locality theorem at all.  What locality actually buys is
   the thing the track is named after — two commits with **disjoint footprints
   both succeeding** — and the old PR 12 never asked for it.
2. **A single-`AtomicPtr` CAS is not partitioning, and it regresses the WCRT
   bound.**  One pointer to the whole state means every commit conflicts with
   every other, so two cores doing disjoint IPC serialise exactly as they do
   under the SM5.I entry lock — and where the ticket lock gives a **bounded
   FIFO** wait, an optimistic retry loop gives an unbounded one, mitigated in
   the old plan by "bounded rebase fuel, fail-closed halt": a kernel that
   *halts under contention*.  For a system whose headline property is a
   worst-case response time that is a regression, not a step towards the end
   state.  It is a stated **non-goal** below.
3. **The runtime obligation is a set, and the note named one field.**  §5's
   note said the key-local reading of the object-store lock is sound once "the
   runtime realises `SystemState.objects` as per-object storage".
   `storeObject`'s own declared write set is five fields and the IPC list is
   seven (`storeObject_modifiedFields`, `ipcEndpointOp_modifiedFields`,
   `Kernel/CrossSubsystem.lean`), every one of them a structure the model
   replaces **whole**.  Deriving the obligation from those lists rather than
   naming a field is PR 11.
4. **The gate named a phase that no longer exists.**  "SM10.1" is WS-BP's 42
   sub-tasks now.  The seam flag is about the *entry lock*, so its gate is
   **BP6** (per-core readiness — the point at which more than one PE executes
   kernel code) with validation at **BP8** (first boot), and the two Lean rows
   are gated on nothing at all.

**Non-goal — the whole-state optimistic CAS.**  Track D will not replace
`modifyGetKernelState`'s read-modify-write with a compare-and-swap on a pointer
to the whole `SystemState`.  It buys no parallelism over the ticket lock it
would replace (every commit still conflicts with every other), and it trades the
one property the ticket lock does provide — a bounded, FIFO-ordered wait, which
is what `PerCoreWcrt.lean`'s live bound is stated over — for an unbounded retry
count.  If a future cut wants lock-freedom for its own sake it must first state
what its progress guarantee is; "bounded fuel then halt" is a liveness bug with
a fail-closed dressing.

**PR 10 — Footprint-local commit (Lean; gated on nothing).**  The theorem the
track rests on, stated over the model and provable today.

*What the tree already has, and it is two different things.*  RR7.11 gave the
eight declared arms their "coverage", and `LockSetForSyscall.lean`'s own
docstring distinguishes the two shapes it comes in.  The **membership** form —
`lockSetForSyscall_<arm>_covers_writes`, for the seven arms `.send`, `.call`,
`.receive`, `.reply`, `.replyRecv`, `.notificationSignal` and
`.notificationWait`, with `_covers_capsWrites` / `_covers_redonation` /
`_covers_boundDelivery` siblings where the arm has a conditional member — says
the locks *someone listed* are in the declared set; it is a presence statement
about a hand-written write set, and the project's own rule for that shape is
that a presence check is not a relation check.  The **quantified** form —
`lockSetForSyscall_{send,call}_object_writes_declared`, over RR7.8's
`endpointSendDualWithCaps_object_writes_declared` — says *every object the step
changes* has its lock declared, "which is stronger", in the file's words,
"because it quantifies over every object rather than over the members someone
listed".  Only the second is a coverage relation, and it exists for **two** of
the eight declared arms, over the **capability-transfer step alone**
(`st'` → `st''`), over the **`objects` field alone**.  The eighth arm,
`.tcbSuspend`, has neither form in this file — its containment is the scheduler
domain's (`suspendThreadOnCoreSchedLockSet`), which is a different lock type and
must be reconciled, not assumed.  A footprint-local commit needs the quantified
form for every declared arm, over the whole transition, over every field the arm
writes.

- *Step 1 (the missing definition):* **what a `LockSet` covers.**  `LockId` is
  `(LockKind, ObjId)`, so a footprint names a set of object keys plus, through
  `stateLevelLock`, the SystemState-level structures SM3.A.10 assigns to it.
  Nothing in the tree maps a footprint to the part of `SystemState` it protects
  — `lockWritesOnly` is about lock *words* — so define the coverage relation and
  the agreement it induces (`agreeOnFootprint S st₁ st₂`).  **Keep the abstract
  question separate from the representation one**, which is what conflating them
  cost §5: `lifecycle.objectTypes` is keyed by `ObjId` and
  `lifecycle.capabilityRefs` by `SlotRef = {cnode, slot}`, so both decompose by
  object *abstractly* and are covered by the per-object locks; `objectIndex`
  (a `List`), the CDT maps, `scThreadIndex` and `scheduler` do not, and are
  `stateLevelLock`'s or the scheduler domain's.  Whether the **runtime** can
  realise the per-object covers is a different question, and it is PR 11's.
- *Step 2 (the quantified form, everywhere):* extend *changed ⇒ declared* from
  two arms to eight, from the capability-transfer step to the whole transition,
  and from `objects` to every field in the arm's write-set list.  This is the
  step that can *fail* — an arm whose transition writes a field its footprint
  does not cover is a false footprint, which is how OD3.5 and OD3.6 each found a
  live one — so it is deliberately before the theorem that assumes it.
- *Step 3 (the generalisation):* SM3.E.5 proves commutation for
  `objStoreWriteInstance` — **one** object, written through `updateObjectAt`
  (`Locks/Serializability.lean`, `objStoreWriteInstance_actionsCommuteObs`).  A
  declared syscall footprint names up to `maxLockSetSize` members and its
  transition writes seven `StateField`s, so the single-object instance is not
  the shape the seam commits.  Generalise to a transition instance confined to
  its footprint's coverage, and re-derive the commutation there.
- *Step 4 (the payoff):* `transition_footprint_local` — a transition confined to
  `S` carries any two states agreeing on `S`'s coverage to post-states that
  agree on it and are unchanged outside, so two transitions with **disjoint**
  footprints commute.  Consumes RR7.12's declared footprints, RR7.19's
  `preservesFieldsOutside` and RR7.18's size bounds; instantiate at the eight
  declared arms so the theorem is about the transitions the seam runs rather
  than about an arbitrary `S`.
- *Step 5:* Tier 3 anchors, including the negative that the statement is **not**
  conditioned on a single global lock being held, and the negative that the
  membership form is not restated as the quantified one.

**PR 11 — The representation obligation, derived and decided (Lean; gated on
nothing).**  What PR 10's abstract commutation needs of the *runtime* state
before PR 13 can realise it — derived from the write-set lists, never
enumerated.  **Steps 1 and 2 consume nothing and may run alongside PR 10**; step
3 consumes PR 10's coverage relation, which is why the row is numbered second
rather than beside it.
- *Step 1:* classify every field in `storeObject_modifiedFields ++
  ipcEndpointOp_modifiedFields ++ capabilityOp_modifiedFields` as **per-key
  realisable** or **whole-structure**, with the classification *derived* from
  the operation's own definition rather than asserted.  The four already known:
  `lifecycle.capabilityRefs` is rebuilt by a `filter` over every entry on
  **every** `storeObject`, of every kind; `objectIndex` is a `List` whose head
  is shared; the CDT maps and `scThreadIndex` are the `stateLevelLock`
  precedent (RR7.9, WS-OD OD3.5).
- *Step 2:* **the `RHTable` locality theorem, with its real side condition.**
  `insertLoop`'s key-match arm is one `Array.set` of the value alone and returns
  at once, so two updates at distinct **resident** keys are slot-disjoint and
  the probe reads only `key`/`dist`, which neither writes.  But `RHTable.insert`
  tests the load factor *before* it knows whether the key is resident
  (`if t.size * 4 ≥ t.capacity * 3 then t.resize`), so a store at a resident key
  on a three-quarters-full table **rebuilds the whole table** — locality is
  conditional on the load factor, not on the key being new.  State it that way;
  the runtime consequence (pre-size the table, or take `stateLevelLock` on any
  store that may resize) is PR 13's to choose, and it cannot choose without
  this.
- *Step 3:* register the classification's residue in `UncoveredLockDomain`,
  beside `taintTablePerKeyStore`, which is the same shape and the only one of
  the family currently named.  Its completeness theorem is what stops a
  whole-structure write from being forgotten; PR 13 deletes the constructors it
  closes, under the deletion-last discipline RR7.40 and RR7.41 used.

**Parallelism, stated.**  PRs 10 and 11 are Lean-only, touch no file WS-OD or
WS-RR RR8 touch, and may run in parallel with either and with each other (PR
11's third step excepted, above).  PRs 12 and 13 are strictly sequential, follow
both Lean rows, and may not begin before BP6: PR 13 changes what a commit *is*,
and there is no way to validate that on a kernel that does not yet run on more
than one PE.

**PR 12 — The striped object-lock table (Rust; gated on BP6).**  Consumes PR 11.
- *Step 1:* the carrier is **known**, not to be explored: `STATIC_RW_LOCK_POOL`
  is `[QueuedRwLock; STATIC_RW_LOCK_POOL_SIZE]` with the size pinned equal to
  the RPi5 `coreCount` (`lock_bridge.rs`), i.e. a per-**core** pool, and
  `build.rs` pins the element type.  A stripe table is a different object and
  the migration is a replacement, not a resize.
- *Step 2:* `OBJECT_STRIPE_POOL` + `objid_stripe` hash + sorted multi-stripe
  acquire (collisions over-serialize, never under-serialize — the SM3
  deadlock-freedom argument survives).  Each `QueuedRwLock` carries three
  per-PE arrays across two cache lines
  (`shared_words_fill_the_first_line_and_requests_the_second`), so the stripe
  count is a memory decision to state, not to default.
- *Step 3:* the withdrawal contract travels with the lock: **one outstanding
  ticket per core per lock** (WS-LC LC3), so a multi-stripe acquire holds one
  ticket in each of several distinct locks and the unwind is `unwindAll` over
  them, which is already the 2PL shrinking phase (WS-LC LC4).
- *Step 4:* unit tests + 8-thread host stress (`shootdown.rs` CAS-mutex stress
  is the precedent) + a loom pair for the multi-stripe acquire/unwind.

**PR 13 — The partitioned commit and the entry-lock retirement (Rust + Lean;
gated on BP6, validated at BP8).**  Consumes PR 12.
- *Step 1:* realise the per-key structures PR 11 classified, and take
  `stateLevelLock` for the ones it did not — the honest split, and the one that
  makes the commit footprint-local rather than optimistic.
- *Step 2:* commit under the acquired footprint instead of under the global
  entry lock; two cores with disjoint footprints commit concurrently, which is
  the property PR 10 proves sound and the reason the track exists.
- *Step 3:* seam flag — retain SM5.I's global entry ticket lock behind a flag
  (`contextRestoreSeamLive` precedent), flipping only after BP8 validates on the
  board.  Both settings stay host-stressed while the flag exists.
- *Step 4:* delete the `UncoveredLockDomain` constructors PR 11 registered and
  PR 13 closes; re-pin the release closure
  (`SMP_RELEASE_CLOSURE_PLAN.md` SMP-C3 made dischargeable; the SMP-plan risk
  row).  The timer-tick fine-lock migration is **not** owed here: RR7.39 landed
  it at `v0.34.89`, and what remains of the scheduler domain is the syscall
  seam's own wake targets (`UncoveredLockDomain.syscallSeamSchedulerDomain`,
  owner RR8).
- *Step 5:* measure `tCs` on the board.  Every WCRT figure in this tree is
  parametric in it (`admissibleCriticalSection`, WS-RR RR7.31), so the
  partitioned commit's bound cannot be quoted as a time until this runs — and
  BP8 is the first point at which it can.

## 5. Cross-cutting design notes

- **CDT coverage = one `(stateLevelLock, .write)` member**, chosen over per-key
  decomposition. It covers `cdt.edges` (List cons), `cdtNextNode` (counter), and
  both `cdtSlotNode`/`cdtNodeSlot` keyed maps — including the sender-side keyed
  entry — in one member, so the caller-root member stays READ (no read→write
  upgrade that would break the shared "caller root read" shape). `stateLevelLock`
  (`LockSetTransitions.lean`) is already the declared serialization subject
  for the audit trail's List, so this is the established SM3.A.10 convention, not
  a new one; conservative (never under-serializes). *Runtime obligation
  (Track D)*: the key-local reading of the object-store lock is sound only once
  the runtime realises the state per key — and that obligation is a **set**, not
  a field.  It is derived in Track D PR 11 from the write-set lists themselves
  (`storeObject_modifiedFields` is five fields, `ipcEndpointOp_modifiedFields`
  seven), because naming one is the enumeration-standing-in-for-a-derivation
  shape: `lifecycle.capabilityRefs` is rebuilt by a `filter` over every entry on
  **every** `storeObject` of every kind, `objectIndex` is a `List` with a shared
  head, and `RHTable.insert` tests the load factor before it knows whether the
  key is resident — so even a store at a resident key rebuilds the table at
  three-quarters load.  This note previously read "the runtime realises
  `SystemState.objects` as per-object storage … discharged at SM10.1", which
  named one of the seven and a phase that no longer exists.
- **Caps-presence gating, not receiver-presence.** The capless-rendezvous
  `= 5`/900µs tick-fit pin (`tests/SmpIpcSuite.lean`) *has* a waiting
  receiver; receiver-gating would break it for all rendezvous calls. The
  caps-carrying call footprint (8) does **not** fit the 1 ms tick — pinned
  honestly as a load-bearing statement, not hidden.
- **Two optionals from one `Option`.** The caps feature adds **two**
  `lockSetExtendOpt`s driven by the same `receiverCnodeObjId`, so consistency
  tiers move **+2** (not +1) and the reply optional stops being outermost (hence
  the `mem_write_lockSetExtendOpt` switch).
- **Improve-and-re-pin roll-up** (folded into the PRs above): the false
  `PerCoreWcrt.lean` "under withLockSet" sentence (honest re-statement in PR 3/4,
  flipped true in PR 8); `DeadlockInventory.lean` count (PR 3);
  `LockSetInventory.lean` stale comments + inventory counts (PR 3–5);
  the SMP-plan risk row's promised-but-absent CI gate (built in PR 9);
  `SMP_RELEASE_CLOSURE_PLAN.md` SMP-C3 (PR 12); the `lockSet_endpointCallWithCaps`
  parallel-function drift (PR 3 fold-in).

## 6. Verification

Per PR: `lake build` each modified module (pre-commit hook enforces), then the
tier matching the change — `test_smoke.sh` minimum, `test_full.sh` for every
theorem-touching PR (2–8, 11). Rust PRs (2, 10, 12): `test_rust.sh`, with host
multi-thread stress in 10/12. Regenerate `docs/codebase_map.json` **last** —
after all `.lean` edits, before commit (the ordering trap hit twice in the SM9.D
workstream).

Expected assertion movements:
- **PR 2**: +revocation regression group; message/ABI shape pins move.
- **PR 3**: footprint size/order pins shift (`SmpIpc` / `LockSet` /
  `WithLockSet` suites); `lockSetTransitions_within_bound` conjunct arity +2;
  `DeadlockInventory` count.
- **PR 4**: `UncoveredLockDomain` 4→3; the closure-checklist deletions +
  `run_negative_check` pins; suite tallies.
- **PR 5**: cspace-op footprint size pins; `capabilityOp_modifiedFields` anchor.
- **PR 7**: seven new per-arm coverage anchors.
- **PR 8/9**: dispatch marker + `build.rs` pin; the export-body gate self-test.
- **PR 10**: the coverage relation and `transition_footprint_local` anchors,
  plus the negative that the statement is not conditioned on a global lock.
- **PR 11**: the field classification, the `RHTable` locality theorem with its
  load-factor side condition, and the `UncoveredLockDomain` constructors it
  registers (the completeness theorem moves with them).
- **PR 12/13**: new Rust stress cases + a multi-stripe loom pair; seam-flag pins;
  the `UncoveredLockDomain` deletions, under the deletion-last discipline.

End-to-end: PR 2's regression proves `cspaceRevokeCdt` reaches transferred
children; PR 8 keeps the golden trace byte-identical (bracket is
projection-invisible); PR 13 host stress proves the partitioned commit is
race-free under contention with the seam flag in **both** settings, and BP8
measures `tCs` on the board — without which no bound in this plan converts to a
time.

## 7. Risks & mitigations

- **WCRT pin breakage** — caps-gating keeps every capless pin by `rfl`; the caps
  shape (call 8) gets its own honest "does not fit one tick" pin. Verify base
  arity before touching builders.
- **Silent aggregate unbounding** (PR 3) — `lockSetTransitions_within_bound`
  MUST be widened to the new arity; a partial-application conjunct is the failure
  mode (SM9.C precedent).
- **Two-optional bookkeeping** (PR 3) — consistency tiers move +2; the reply
  optional stops being outermost.
- **Partition violation** (PR 6–8) — production `lockSetForSyscall` cannot import
  staged `EndpointCall`/`FineLockFlow`; the resolver references only production
  `LockSetTransitions`. `scripts/check_production_staging_partition.sh` gates it.
- **Naming gate** — no workstream-ID tokens in identifiers, non-docs comments, or
  new Tier-3 comments (the gate reads the git index and counts identifier-shaped
  tokens; the v0.33.54 cut hit this with a workstream ID in a shell comment).
- **Fixture ordering** — regenerate `.sha256` with the filename form; codebase
  map last.
- **IpcMessage blast radius** (PR 2) — the `caps` type change touches every
  constructor; grep-drive and rebuild each; a security fix that silently drops a
  cap is worse than the defect.
- **CDT over-declaration cost** (PR 4/5) — `stateLevelLock` on send/call + the
  four cspace ops widens footprints; verify none breaks a size/WCRT pin (cspace
  ops are not on the 1 ms IPC path).
- **Stripe collision** (PR 12) — collisions over-serialize, which is safe: the
  SM3 deadlock-freedom argument rests on the acquisition *order*, and a sorted
  multi-stripe acquire keeps it.  The stripe count is a stated memory decision,
  since each `QueuedRwLock` occupies two cache lines.
- **Retry livelock is designed out, not mitigated** (PR 13) — the whole-state
  optimistic CAS is a stated non-goal precisely because "bounded fuel then
  fail-closed halt" is an unbounded wait with a halt attached, and this kernel's
  headline property is a bounded one.  A footprint-local commit under acquired
  locks inherits the `QueuedRwLock` FIFO bound instead.  Seam flag validated in
  both settings on host before any BP6 flip.

## 8. Acceptance / closure

- [ ] PR 2: `cspaceRevokeCdt` on a real source reaches IPC-transferred children
      (regression + provenance theorem); the finding is closed.
- [ ] PR 4: `UncoveredLockDomain.capTransferReceiverCnode` deleted; every
      `ipcUnwrapCaps` write rides a declared lock.
- [ ] PR 5: every CDT writer (IPC + the four cspace ops) declares the CDT lock;
      `capabilityOp_modifiedFields` complete.
- [ ] PR 8: `lean_syscall_dispatch_cross_core` bracketed in `withLockSet`; trace
      byte-identical; the false `PerCoreWcrt` sentence flipped true.
- [ ] PR 9: export-body CI gate live with `--self-test`.
- [ ] PR 10: `transition_footprint_local` proved and instantiated at the eight
      declared arms; two disjoint footprints shown to commute.
- [ ] PR 11: every field in the three write-set lists classified, derived from
      the operations; the `RHTable` locality theorem stated with its load-factor
      condition; the residue registered in `UncoveredLockDomain`.
- [ ] PR 13: partitioned commit host-validated; SM5.I global entry lock behind a
      seam flag; the constructors PR 11 registered and PR 13 closes deleted;
      `tCs` measured on the board at BP8.

What remains open after this plan is the **syscall seam's scheduler domain**
(`UncoveredLockDomain.syscallSeamSchedulerDomain`, owner RR8) and the **BP6 seam
flip**; both are named follow-ons, not silent gaps.  The timer-tick fine-lock
migration this section used to name as SM3.C.9.b is **closed** — RR7.39 landed
it at `v0.34.89`.

## 9. Registered debt found while closing the queued-receive transfer

Both of these surfaced at v0.33.77, while wiring the live `.receive` through the
WithCaps path.  Neither is a regression from that cut; both are pre-existing and
were invisible while the receive installed nothing at all.

### 9.1 `.replyRecv`'s receive leg dropped a parked sender's capabilities — **CLOSED at v0.33.80**

`.receive` installed what a parked sender was carrying from v0.33.77.
`.replyRecv` is reply-then-receive, and its receive leg ran inside
`replyRecvBody`, which called the **bare** `endpointReceiveDualOnCore` — so the
identical defect survived on that arm: a caps-carrying send that parked and was
later collected by a `.replyRecv` rather than a `.receive` transferred nothing,
and the arm's staged `extraCaps` reported zero.  That arm is how an seL4-MCS
server loop actually runs (`Recv` once, then `ReplyRecv` forever), so a server
received capabilities on its first request and silently none afterwards.

Closed by threading the receiver's CSpace root and receive slot through
`replyRecvBody` and returning the `CapTransferSummary`, so both dispatch arms
stage the honest installed count.  The 59 figure recorded here counted prose;
the real surgery was **nine** applications plus the cross-core non-interference
carriage (`replyRecvBodyWriteSet` and the two theorems gained the two
parameters, and `endpointReceiveDualWithCapsOnCore` gained its own
scheduler/machine frame lemmas, confinement bound and NI instantiation — the
capability install writes no core, so the declared per-core footprint is
unchanged).

The cut also corrected an inventory claim that had gone stale one round earlier:
`crossCoreTransitionIsLiveArm` still marked the *bare* per-core receive a live
arm on the strength of two facts — that `.receive` invoked it directly and that
it was `replyRecvBody`'s receive leg — neither of which survives.  The live-arm
claim moved to a new `.endpointReceiveDualWithCaps` entry (which is also what
`syscallDelegates_receive` already names), and the bare transition joined
`.notificationSignal` and `.endpointReply` as a below-API entry.

Regression: `chain12dReplyRecvCapTransferArrivalOrder` runs both arrival
orderings from one state and compares them to each other, with a load-bearing
negative driving the bare per-core receive on the state ordering A succeeds
from — it installs nothing, so a reroute back to it fails the positive.

### 9.2 `ipcUnwrapCaps` carries a `senderCspaceRoot` nothing reads

The revocation-precision fix (v0.33.59) moved the CDT parent off a synthetic
`{ senderCspaceRoot, slot 0 }` onto the real source node the message carries
(`TransferCap.srcNode`).  `ipcUnwrapCapsLoop` has taken `senderCspaceRoot` ever
since **without using it**, and `ipcUnwrapCaps` passes it straight through.

It is not simply deletable: the parameter is what makes all three transfer paths
perform a `lookupCspaceRoot senderId` and fail closed with `.invalidCapability`
when the sender has no CSpace root — the AK1-I NI-symmetry behaviour.  Removing
the argument removes that lookup, and with it an error a caller can currently
observe, so the cut has to decide deliberately whether that fail-closed branch
is still wanted on its own terms.

**CLOSED at v0.34.82 (WS-RR RR7.33)**, with the decision this row was waiting
for made explicitly: **the fail-closed branch is not wanted on its own terms**,
and the parameter is gone from `ipcUnwrapCaps`, `ipcUnwrapCapsLoop`, and — since
the deadness propagates — from `endpointSendDualWithCaps`,
`endpointCallWithCaps`, their `OnCore` and cross-core-dispatch wrappers, the
flow-checked wrappers, and the syscall dispatch arms that fed them
`gate.cspaceRoot`.

Three reasons, in the order they bind:

1. *The transfer does not read it.*  The derivation parent has been
   `TransferCap.srcNode` since the revocation-precision fix (`v0.33.59`), and
   that node is minted at `resolveExtraCaps` **against the sender's own CSpace
   root** — so the authority the parameter looked like it carried is already
   established, at resolution, where the sender's root is the resolver's input.
2. *The lookup's error was a cross-principal channel.*  AK1-I made all three
   transfer paths fail closed on a missing CSpace root, and that is right for
   the **receiver's** root — it is where capabilities install, and the send and
   call arms still check it.  The receive arm looked up the **sender's** root
   only to feed this parameter, so its `.invalidCapability` made the
   *receiver's* syscall fail on a fact about the *sender's* TCB: a one-bit flow
   from sender-domain state into a receiver-visible `KernelError`, which is the
   shape AK1-I set out to remove rather than one it needed to add.
3. *The case it appeared to cover is already covered, better.*  A source slot
   destroyed between resolution and unwrap is declined per capability by
   `CapTransferResult.sourceRevoked`, which installs the rest; failing the whole
   transfer on the sender's root was coarser and answered a different question.

The receive arm keeps `receiverCspaceRoot` and the send/call arms keep their
receiver-root lookups, so every path still checks exactly the root it uses.
