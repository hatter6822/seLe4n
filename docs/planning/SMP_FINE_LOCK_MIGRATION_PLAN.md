# SMP Fine-Lock Migration & Commit-Partitioning Plan

> **Phase**: SM3.C.9 (deferred `withLockSet` migration at the live kernel
> entry) + the `capTransferReceiverCnode` footprint closure + commit
> partitioning (the fine-lock end-state).
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Origin**: [`SMP_PER_OBJECT_LOCKS_PLAN.md`](SMP_PER_OBJECT_LOCKS_PLAN.md) §5.2 (SM3.C.9 deferral) + the v0.33.54 audit that registered `UncoveredLockDomain.capTransferReceiverCnode`.
> **Refs**: [`SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](SMP_DECLASSIFICATION_COMPLETION_PLAN.md) §SM9.D (audit-pass-7 closure); [`SMP_TLB_SHOOTDOWN_PLAN.md`](SMP_TLB_SHOOTDOWN_PLAN.md) §"Kernel-entry serialisation" (SM5.I).
> **Target releases**: v0.33.55+ across 12 PRs in four tracks.
> **Calendar estimate**: ~10–16 weeks (Track A security first; Track D is the largest — a runtime commit-model change).

## 1. Phase goal

Three coupled closures, sequenced security-first:

1. **Fix the confirmed revocation-precision defect** (§3) — IPC capability
   transfer misattributes CDT provenance to a synthetic source slot, so
   `cspaceRevokeCdt` misses transferred children. High severity, single-core
   reachable, model-level today (a live CVE-class defect once the kernel boots
   at SM10.E).
2. **Close the registered footprint defect** `UncoveredLockDomain.capTransferReceiverCnode`
   — the receiver-CNode write (and the previously-undeclared CDT write on
   *every* CDT writer) rides no declared lock. Declare it, prove the coverage,
   delete the registration, re-pin every assertion that encoded the gap.
3. **Land the deferred SM3.C.9 fine-locks work** — migrate the live
   `@[export]` state-committing bodies to wrap their transitions in
   `withLockSet`, then implement the **partitioned commit** that lets the SM5.I
   global entry ticket lock finally be removed (seam-gated to SM10.E hardware
   validation).

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
  only `cap`, discarding `ref` (`SeLe4n/Kernel/API.lean:1000-1003`) — so
  `IpcMessage.caps : Array Capability` carries no source slot.
- `ipcUnwrapCapsLoop` therefore hardcodes the CDT parent as
  `{ cnode := senderCspaceRoot, slot := Slot.ofNat 0 }`
  (`SeLe4n/Kernel/IPC/Operations/CapTransfer.lean:114-116`).
- `ipcTransferSingleCap` records the edge from that synthetic node
  (`SeLe4n/Kernel/Capability/Operations.lean:1605-1607`).
- CDT nodes are keyed by the **full** `SlotRef`, with `ensureCdtNodeForSlot`
  minting a distinct node per distinct ref
  (`SeLe4n/Model/State.lean:455,665,4025-4034`), so slot 0's node is not the
  real source's node.
- The live userspace revoke `cspaceRevokeCdt` (the default for untrusted
  invocations) walks `descendantsOf (lookupCdtNodeOfSlot addr)` — the *real*
  source slot's node (`Operations.lean:941-943,1285-1308`); local `cspaceRevoke`
  only clears same-CNode siblings (`:966-980`).

**Severity / reachability**: High — revocation of derived authority is a core
capability-system guarantee. Single-core reachable, requires only the `Grant`
right the transfer already needs; **not** concurrency-gated, so SM5.I does not
mask it. Model-level today; live once the kernel boots (SM10.E). No theorem is
false — the model faithfully exhibits the bypass.

**Remediation** (PR 2): thread the real source `SlotRef` through the transfer
path (`IpcMessage.caps : Array Capability` → `Array TransferCap` carrying
`(cap, srcRef)`; keep `resolveExtraCaps`'s already-resolved `ref`), record the
edge from the real source, and prove
`transferred_child_is_cdt_descendant_of_real_source` so `cspaceRevokeCdt`
provably reaches it, with a regression test whose load-bearing negative is that
the pre-fix state does not.

## 4. PR decomposition (12 PRs, four tracks, security-first)

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
  `⟨cap, ref⟩` — they already resolve `ref` and discard it (`API.lean:1000-1003`);
  keep it.
- *Step 3 (consumer):* `ipcUnwrapCapsLoop` passes `tc.srcRef` to
  `ipcTransferSingleCap`, deleting the synthetic slot-0 literal
  (`CapTransfer.lean:114-116`).
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
  (= `maxLockSetSize`).
- *Step 2:* fold `lockSet_endpointCallWithCaps`
  (`IPC/CrossCore/EndpointCall.lean:144-163`) → `lockSet_endpointCall … (some
  destCnode)` (tie by `rfl`, kills the parallel-function drift); add the
  send-side analogue.
- *Step 3:* consistency tiers **+2** (one `Option` drives two members — send
  `base_plus_one_opt` → `_three_opts`; call `base_plus_three_opts` →
  `_five_opts`, which exists); `permittedKinds` += `.objStore` for `.send` /
  `.call` (`.cnode` already permitted).
- *Step 4:* size proofs to send ≤ 6 / call ≤ 8; **widen the
  `lockSetTransitions_within_bound` send/call conjunct arity**
  (`Deadlock.lean:915`) — the silent-unbounding hazard, exactly the SM9.C
  `notificationSignal` fix; re-pin `DeadlockInventory.lean:191` ("29" → true
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
  `ipcUnwrapCaps_preserves_objects_ne` (`CapTransfer.lean:367-379`) +
  `_objects_at_root_orig_or_cnode` (:805-817); CDT half rides
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
  `WORKSTREAM_HISTORY`, the completion plan, GitBook 12, claim index; add an
  **"Audit-pass-7 closure additions"** block to `SMP_PER_OBJECT_LOCKS_PLAN.md`
  §5.2 (audit-pass-6 PR #793 is the format) + check its §8 box.

**PR 5 — CDT coverage on the four `cspace{Mint,Copy,Move,Delete}` ops** (independent object).
- Declare `(stateLevelLock, .write)` on `lockSet_cspace{Mint,Copy,Move,Delete}`;
  `permittedKinds` += `.objStore`; coverage proofs (the CDT-write shape is
  identical across all four — `Operations.lean:991-1010,1160-1169`).
- Fix `capabilityOp_modifiedFields` (`SeLe4n/Kernel/CrossSubsystem.lean:1197-1198`,
  `[.objects,.lifecycle]`) to include the four CDT `StateField` constructors
  (:868-873).

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
  (`SyscallDispatchEntry.lean:561-606`) through the revalidated bracket
  (`RevalidatedEntryOutcome`: resolve → acquire → re-resolve → refuse-on-change)
  with fail-closed `none` fallback (undeclared syscalls run unbracketed exactly
  as today). Model on the already-migrated `suspend_thread_cross_core`
  (:734-791, v0.32.149).
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

### Track D — Commit partitioning (the end-state; seam-gated to SM10.E)

**PR 10 — Striped object-lock table (Rust).**
- *Step 1:* confirm the current carrier in `rust/sele4n-hal/src/lock_bridge.rs`
  (exploration: a coreCount-sized per-core pool, not a stripe table).
- *Step 2:* `OBJECT_STRIPE_POOL` (fixed lock-word pool) + `objid_stripe` hash +
  sorted multi-stripe acquire (collisions over-serialize, never under-serialize
  — the SM3 deadlock-freedom argument survives).
- *Step 3:* unit tests + 8-thread host stress (`shootdown.rs` CAS-mutex stress
  is the precedent).

**PR 11 — CAS-rebase soundness (Lean).** `transition_footprint_local` — a
footprint-local commit re-run against a state that changed only *outside* the
footprint yields the same delta. Built on `lockWritesOnly` (`FineLockFlow.lean`),
`observableSlotsConfinedToCores`
(`SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean`), and the 2PL
serializability theorem in
`SeLe4n/Kernel/Concurrency/Locks/Serializability.lean` (cite the exact name).

**PR 12 — CAS-rebase commit + seam gating.**
- *Step 1:* replace `modifyGetKernelState`'s read-then-write (`Platform/FFI.lean`)
  with compute-from-snapshot + CAS on an `AtomicPtr`; on conflict re-run against
  fresh state (sound by `transition_footprint_local`); bounded rebase fuel,
  fail-closed halt on exhaustion (SM7.B.6 discipline).
- *Step 2:* seam flag — retain SM5.I's global entry ticket lock behind a flag
  (`contextRestoreSeamLive` precedent), flipping only after SM10.E hardware
  validation.
- *Step 3:* host stress both flag settings.
- *Step 4:* release-closure re-pins (`SMP_RELEASE_CLOSURE_PLAN.md` SMP-C3 made
  dischargeable; the SMP-plan risk row) + register the timer-tick fine-lock
  migration as the named follow-on **SM3.C.9.b** (its `SchedLockId`
  `withLockSet` bracket does not exist — the timer entry stays on the global
  entry lock in this plan).

## 5. Cross-cutting design notes

- **CDT coverage = one `(stateLevelLock, .write)` member**, chosen over per-key
  decomposition. It covers `cdt.edges` (List cons), `cdtNextNode` (counter), and
  both `cdtSlotNode`/`cdtNodeSlot` keyed maps — including the sender-side keyed
  entry — in one member, so the caller-root member stays READ (no read→write
  upgrade that would break the shared "caller root read" shape). `stateLevelLock`
  (`LockSetTransitions.lean:239`) is already the declared serialization subject
  for the audit trail's List, so this is the established SM3.A.10 convention, not
  a new one; conservative (never under-serializes). *Runtime obligation
  (Track D)*: the key-local reading of the object-store lock is sound only if the
  runtime realises `SystemState.objects` as per-object storage — the same
  obligation `storeObject` already carries, discharged at SM10.E.
- **Caps-presence gating, not receiver-presence.** The capless-rendezvous
  `= 5`/900µs tick-fit pin (`tests/SmpIpcSuite.lean:707-718`) *has* a waiting
  receiver; receiver-gating would break it for all rendezvous calls. The
  caps-carrying call footprint (8) does **not** fit the 1 ms tick — pinned
  honestly as a load-bearing statement, not hidden.
- **Two optionals from one `Option`.** The caps feature adds **two**
  `lockSetExtendOpt`s driven by the same `receiverCnodeObjId`, so consistency
  tiers move **+2** (not +1) and the reply optional stops being outermost (hence
  the `mem_write_lockSetExtendOpt` switch).
- **Improve-and-re-pin roll-up** (folded into the PRs above): the false
  `PerCoreWcrt.lean` "under withLockSet" sentence (honest re-statement in PR 3/4,
  flipped true in PR 8); `DeadlockInventory.lean:191` count (PR 3);
  `LockSetInventory.lean:224,:306` stale comments + inventory counts (PR 3–5);
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
- **PR 10/11/12**: new Rust stress cases; the `transition_footprint_local`
  anchor; seam-flag pins.

End-to-end: PR 2's regression proves `cspaceRevokeCdt` reaches transferred
children; PR 8 keeps the golden trace byte-identical (bracket is
projection-invisible); PR 12 host stress proves the CAS-rebase commit is
race-free under contention with the seam flag in **both** settings.

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
- **Rebase livelock / stripe collision** (PR 12/10) — bounded fuel + fail-closed
  halt; stripe collisions over-serialize (safe). Seam flag validated both
  settings on host before any SM10.E flip.

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
- [ ] PR 12: partitioned CAS-rebase commit host-validated; SM5.I global entry
      lock behind a seam flag; timer-tick registered as SM3.C.9.b.

The **timer-tick fine-lock migration (SM3.C.9.b)** and the **SM10.E seam flip**
are the two items that remain open after this plan; both are named follow-ons,
not silent gaps.
