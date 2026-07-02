# Reply Objects (seL4-MCS) — Completion Plan: deferred Phase-C-invariants / D6 / H items

> Companion to the SM6.C/SM6.D reply-object slices in
> [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md) and the
> PR #822 hardening pass. This plan tracked the three remaining **completeness**
> items — the ABI / Prop-invariant / transition-fold tail. **✅ COMPLETE as of
> v0.31.155: all three items (#2, #1, #7) plus every residual-debt item are LANDED.**
> Item #7 (the D6 transition fold) closed across v0.31.152–154 (#7.0–#7.5); the
> rights-less reply-cap residual closed at v0.31.155. The sections below are retained
> as completion records (with cites and per-slice landing notes).
> **Post-completion review pass:** the Codex review of the landing PR (#827)
> surfaced numbered findings against the landed surface; **all closed by
> v0.32.57** — see the "PR #827 review pass" section at the end of this document.

## Context & status

The reply-object workstream landed the first-class `Reply` object, single-use
`.replyCap rid` capabilities, faithful Call/Receive/Reply/ReplyRecv linkage, the
cross-core dispatch, and the full PR-#822 hardening pass. **All three completion
items are fail-closed-safe at runtime regardless of completion state** — the live
`.reply` path rejects a dangling reply cap via `getReply?`, and the live dispatch
always links `replyObject` — so these close **model/ABI completeness gaps, not
safety holes**.

| # | Item | Layer | Status | Landed |
|---|------|-------|--------|--------|
| **#2** | retype → reply-cap authority (`mintReplyCap`) | ABI (Phase H) | ✅ **LANDED** | v0.31.140–143, 147 |
| **#1** | `replyCapPointsToValidReply` (7th bundle conjunct) | Capability invariant (Phase C-inv) | ✅ **LANDED** | v0.31.144–146, 149 |
| **#7** | `blockedOnReply ⇒ replyObject` (transition fold) | IPC invariant + transitions (Phase D6) | ✅ **LANDED** | #7.0–#7.3a v0.31.152; #7.3b v0.31.153; #7.4/#7.5 v0.31.154 |

**Original sequencing rationale (#2 → #1 → #7), preserved for the record.** #2 went
first (most self-contained ABI feature, establishing the `.replyCap`-from-retype
production path #1's invariant reasons about as "backed"); #1 second (Prop-invariant
completeness, cleanest once the cap-acquisition story was settled); #7 last (the
deepest re-base — folding reply-linking into the IPC transitions — the plan's D6
contract and the natural culmination). #2 and #1 executed in that order
(v0.31.140 → v0.31.146, lifecycle-coverage follow-on v0.31.149); #7 is now the
single open slice and the entire focus of **§#7** below.

### Residual-debt carried by the landed items (actionable)

1. **Rights-less reply cap (from #2).** ✅ **RESOLVED (v0.31.155).** `mintReplyCap`
   (`Capability/Operations.lean`) now mints `.replyCap rid` with
   `rights := AccessRightSet.empty` — **seL4-MCS reply caps are rights-less**: the
   cap conveys single-use reply authority by *possession* (`extractReplyId` resolves
   it on `cap.target` alone — the `.reply`/`.replyRecv` path never gates on rights),
   so a reply cap can no longer double as spurious read/write authority on the Reply
   object.  `mintReplyCap` was the only production reply-cap mint; the one invariant
   proof (`mintReplyCap_preserves_capabilityInvariantBundle`) updated to the rights-less
   shape (rights-agnostic — only the slot write and reply-target check matter).  Verified:
   `test_full` green; the retype→mint→link→use round-trip suite passes; trace byte-identical.
2. **Stale conjunct-count comment (from #1).** `capabilityInvariantBundle`'s
   doc-comment (`Capability/Invariant/Defs.lean:228` / :237) still reads "the
   bundle now has **6** conjuncts", but #1.a added the 7th
   (`replyCapPointsToValidReply`), so the live tuple has **7**. The comment
   describes a *worse* (out-of-date) state than the code; update it to "7" in
   the next `Capability/Invariant/Defs.lean` touch, and no later than #7.4
   (where `replyCallerLinkage`/bundle destructuring work already revisits the
   invariant surface).

---

## #2 — retype → reply-cap authority  ✅ LANDED (v0.31.140–143, 147)

**Problem (closed).** `lifecycleRetypeDirect` (`Lifecycle/Operations/RetypeWrappers.lean:246`)
retypes an ObjId **in place**: the authority cap stays `.object target` while the object
becomes `.reply`. `resolveRecvReplyId`/`extractReplyId` (`API.lean:269`, `:303`) require
`.replyCap rid`, so a retyped Reply's `.object` cap yielded `.invalidCapability` —
dynamically-retyped Reply objects were unusable; only boot-preinstalled reply caps worked.

**Approach taken (decision honoured).** A verified **mint-reply-cap** production path: a
`cspaceMint`-family op that, given an `.object target` cap where `target` holds a `.reply`
object, installs `.replyCap (ReplyId.ofObjId target)` into a destination slot —
CDT-tracked exactly like `cspaceMint`. Authority: the holder of the `.object` cap to the
Reply object may derive its reply cap (the object *is* the reply object). The round-trip
`(ReplyId.ofObjId target).toObjId = target` (Prelude) makes the minted cap resolve back to
the same Reply, so the result satisfies `replyCapPointsToValidReply` **by construction**.
*Alternative rejected:* making `extractReplyId` accept an `.object`-to-`.reply` cap —
rejected as diluting the deliberate `.replyCap` authority distinction.

**Sub-steps — all landed:**
- **#2.a** ✅ — `mintReplyCap` (`Capability/Operations.lean:1154`): resolve `.object target`
  via `cspaceLookupSlot` → require `getReply? (ReplyId.ofObjId target) ≠ none` (else
  `.invalidCapability`) → `cspaceInsertSlot` the `.replyCap rid` at dst. CDT-tracked variant
  `mintReplyCapWithCdt` (`:1172`). Mirrors `cspaceMint`'s lookup → derive → insert shape.
- **#2.b** ✅ — `mintReplyCap_preserves_capabilityInvariantBundle`
  (`Capability/Invariant/Preservation/Insert.lean:362`) +
  `mintReplyCapWithCdt_preserves_capabilityInvariantBundle`
  (`…/Preservation/CopyMoveMutate.lean:221`): the inserted `.replyCap`'s rid is backed by
  construction, discharging the `hCapBacked` hypothesis of the unifying keystone
  `cspaceInsertSlot_preserves_replyCapPointsToValidReply` (see #1.b).
- **#2.c** ✅ — ABI: `SyscallId.mintReplyCap = 28` (`Model/Object/Types.lean`; `count := 29`),
  decode (reuses `decodeCSpaceCopyArgs`), dispatch arm (`API.lean:914`, via
  `dispatchCapabilityOnly` → `mintReplyCapWithCdt`), `lockSet_mintReplyCap` +
  consistency + inventory (`LockSetTransitions.lean` / `LockSetInventory.lean`, 29 lockSet
  + 29 consistency entries), Rust `sele4n-types`/`sele4n-hal` mirror (`MintReplyCap = 28`,
  `COUNT = 29`) + conformance; trace fixture `[XVAL-002]` updated to "all 29 variants".
- **#2.d** ✅ — end-to-end test `reply_cap_end_to_end_retype_mint_link` (v0.31.147):
  retype Untyped→Reply, `mintReplyCap`, use the resulting `.replyCap` in the
  receive-with-reply path.

**Residual debt — ✅ RESOLVED (v0.31.155).** The minted cap was `[.read, .write]`;
seL4-MCS reply caps are **rights-less**, so `mintReplyCap` now mints
`rights := AccessRightSet.empty` — see *Follow-up / tracked debt* item 1.

---

## #1 — `replyCapPointsToValidReply`  ✅ LANDED (v0.31.144–146, lifecycle-coverage follow-on v0.31.149)

**Problem (closed).** The step-preserved `capabilityInvariantBundle` (and
`lifecycleStaleReferenceExclusionInvariant`) only constrained `.object` cap targets; a
`.replyCap rid` slot pointing at an absent/non-Reply object satisfied them while live
`.reply` rejects it. The model admitted a dangling reply cap. (The runtime check
`cspaceSlotCoherencyChecks` in `Testing/InvariantChecks.lean:126` already validated
`.replyCap rid => getReply? rid .isSome`; only the **Prop** invariant was blind.)

**Approach taken.** Added, mirroring the runtime check
(`Capability/Invariant/Defs.lean:146`):
```
def replyCapPointsToValidReply (st) : Prop :=
  ∀ oid cn slot cap rid, st.objects[oid]? = some (.cnode cn) →
    cn.lookup slot = some cap → cap.target = .replyCap rid → st.getReply? rid ≠ none
```
as the **7th conjunct of `capabilityInvariantBundle`** (`Defs.lean:230–233`) — the only
*step-preserved* home (`cdtMintCompleteness` and the cross-subsystem composition are
**boot-only**, so adding there would be vacuous-enforcement). Followed the AN4-F.5
named-projection idiom: tuple + `structure CapabilityInvariantBundle` field
(`replyCapBacked`) + bidirectional bridge + `@[simp]` projection (`.2.2.2.2.2.2`).

**Preservation (uniform — as proven).**
- Cap ops change CNodes, not Reply objects ⇒ `getReply? rid` frame-stable; an inserted
  `.replyCap` copies a backed source (or #2's mint, backed by construction) ⇒ backed.
- Delete/revoke remove caps ⇒ fewer reply caps ⇒ preserved.
- Retype: `lifecyclePreRetypeCleanup` + CDT-revoke remove a Reply's caps before destroy
  ⇒ no dangling.

**Sub-steps — all landed:**
- **#1 foundations** ✅ (v0.31.144) — `replyCapPointsToValidReply` + `_of_objects_eq` frame
  (`Defs.lean:146–160`).
- **#1.b (the keystone)** ✅ (v0.31.145) — the preservation lemmas. **Unifying insight:**
  most cap ops delegate to `cspaceInsertSlot`, so the *one* lemma
  `cspaceInsertSlot_preserves_replyCapPointsToValidReply
  (… hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none …)`
  (`…/Preservation/Insert.lean`) carries it; `cspaceCopy`/`Move`/`Mint`/`mintReplyCap`/`ipcUnwrap`
  discharge `hCapBacked` (inserted cap copies a backed source, or — for `mintReplyCap` —
  backed by construction). `cspaceDeleteSlotCore` dual: deletion only removes caps ⇒
  trivially preserved.
- **#1.a (contract)** ✅ (v0.31.146) — `replyCapPointsToValidReply` added as the 7th
  `capabilityInvariantBundle` conjunct; the ~155 construct/destructure sites repointed
  (each preservation theorem appends the #1.b witness; raw destructures gained a 7th binder).
  (The initial atomic-slice estimate was ~60 sites; the realized surface was ~155 — see
  the *lesson learned* note below, which informs #7's blast-radius planning.)
- **#1.c** ✅ — `default_capabilityInvariantBundle` (`Architecture/Invariant.lean:365`)
  discharges the 7th conjunct vacuously on empty objects; `Boot.lean` carries it (boot has
  no reply caps); `crossSubsystemInvariantWithCdtCoverage` threads it.
- **#1.d** ✅ — `replyCapPointsToValidReply_distinguishes_backed_and_dangling`
  (`ModelIntegritySuite`): dangling reply cap rejected by the Prop predicate; backed admitted.
- **Lifecycle-coverage follow-on** ✅ (v0.31.149, PR #822 review #02/#13) —
  `lifecycleCapabilityRefReplyCapBacked_of_replyCapPointsToValidReply`: the Lifecycle-layer
  stale-reference family (whose `.replyCap` metadata is *derived* from the slot cap) is
  **implied** by the step-preserved #1 conjunct, closing the review residual without a
  parallel lifecycle predicate.

**Residual debt — ✅ RESOLVED.** The `capabilityInvariantBundle` doc-comment
(`Capability/Invariant/Defs.lean`) now correctly reads "the bundle now has **7** conjuncts"
(with the 7 → 6 → 7 history) — see *Follow-up / tracked debt* item 2.

**Lesson learned for #7.** #1.a's tuple-expansion break-set was estimated at ~60 and
realized at ~155 (extraction lemmas + multi-layer preservation chains widen the surface).
**#7's atomic re-base estimate (~90 call sites / ~300 proof errors) should be treated as a
floor, not a ceiling** — budget the slice with the #1.a multiplier in mind, and front-load
every reusable frame lemma (#7.0) so the realized errors are *re-pointing*, not novel proof.

---

## #7 — `blockedOnReply ⇒ replyObject` (D6 contract) ✅ LANDED (v0.31.152–154)

> All slices landed: #7.1/#7.2/#7.3a (v0.31.152), #7.3b (v0.31.153), #7.4/#7.5 (v0.31.154).
> The fold makes the reply-link atomic with the blocking store across every producer
> (`endpointCall{,OnCore}` / `endpointReceiveDual{,OnCore}`), and `replyCallerLinkage`'s
> third clause now states the transition-level guarantee.  The problem statement below is
> retained as the completion record.

**Problem.** `replyCallerLinkage` (`IPC/Invariant/Defs.lean`) originally had **two**
conjuncts — a forward link (`tcb.replyObject = some rid ⇒ reply.caller = some tid`) and a
backward link (`reply.caller = some tid ⇒ tcb.replyObject = some rid ∧ tcb` is
`.blockedOnReply`). Both only constrain TCBs that *already* have `replyObject` set;
`replyCallerLinkage` is the **16th conjunct** of `ipcInvariantFull` (`Defs.lean:1271`), and
that invariant therefore admits a `.blockedOnReply ep rt` TCB with `replyObject = none`.
The raw single-core `endpointCall` (`DualQueue/Transport.lean`) and `endpointReceiveDual`
(`Transport.lean`) *used to* produce exactly that intermediate: the caller blocked before the
server-supplied reply cap was linked by a **separate** dispatch step
(`linkServerFirstCaller` / `linkReceivedCaller`). Slices #7.1–#7.3b have since **folded** that
link into the blocking transitions (`linkReceivedCaller`/`linkServerStashedReply` now run
atomically inside `endpointReceiveDual{,OnCore}` / `endpointCall{,OnCore}`), and both former
dispatch steps are deleted — so the only remaining gap is the *invariant* statement (#7.4).

**Root cause.** Reply-linking is a *dispatch-layer* step composed **after** the blocking
transition; the rid is server-supplied and unknown to the raw transition. So
`blockedOnReply ⇒ replyObject` holds at **syscall boundaries**, not **transition
boundaries** — and `ipcInvariantFull` is a transition-level invariant. The relevant TCB
shape is `ThreadIpcState.blockedOnReply (endpoint : ObjId) (replyTarget : Option ThreadId)`
(`Model/Object/Types.lean:611`), with the caller's reply in `TCB.replyObject`
(`:795`) and the server-first stash in `TCB.pendingReceiveReply` (`:806`).

**Optimal approach (faithful seL4-MCS fold).** Make reply-linking **atomic** with the
blocking transition by threading the resolved `rid` into the receive/call transitions, so
the dequeued `Call` caller is set `.blockedOnReply` **and** `replyObject := some rid` in
one store. `blockedOnCall` (the enqueue path, no server yet) carries no reply and is
*excluded* from the new clause; the later dequeue→`blockedOnReply` transition links the
rid atomically. The target invariant is the **third `replyCallerLinkage` clause**
```
(∀ tid tcb ep rt, getTcb? tid = some tcb →
   tcb.ipcState = .blockedOnReply ep rt → ∃ rid, tcb.replyObject = some rid)
```
which holds **only once every production path that produces `.blockedOnReply` links a
reply** — hence the strengthening (#7.4) is the *last* slice, after all three transitions
(single-core receive, per-core receive, call) fold.

### Decomposition — why and how it is finer than the original #7.a–d

The original `#7.a/#7.b/#7.c/#7.d` treated the fold as one transition change. The spike
(below) proved that a *single* function's signature change is an atomic, no-green-intermediate
re-base. But the three blocking transitions — `endpointReceiveDual` (single-core),
`endpointReceiveDualOnCore` (per-core, `IPC/CrossCore/EndpointReply.lean:150`), and
`endpointCall`'s server-waiting rendezvous — are **separate functions**. Changing one
function's signature does **not** break the others' call sites. Therefore the work splits
into **separately green slices, one per producer family**, bracketed by a frame-pre-land
slice (#7.0) and an invariant slice (#7.4). The only ordering constraint among the three
folds is semantic, not signature-driven: #7.3 (server-waiting `endpointCall`) consumes the
server-first stash that #7.1 moves into `endpointReceiveDual`, so #7.3 must land after
#7.1. #7.2 remains independent of both. Each numbered slice below compiles green on its
own once its stated prerequisites have landed (`replyCallerLinkage` unchanged until #7.4);
the invariant is strengthened only after all producers link. This converts "one ~300-error
atomic slice" into "one additive green PR + three smaller atomic-but-mechanical folds +
one invariant PR".

**Dependency graph (topological execution order):**
```
#7.0 (frames, additive)
   ├─> #7.1 (single-core receive fold) ──┬─> #7.3 (call-path fold) ──┐
   └─> #7.2 (per-core receive fold)    ──┴──────────────────────────┴─> #7.4 (strengthen replyCallerLinkage) ─> #7.5 (tests)
```
`#7.1` and `#7.2` may land in either order. `#7.3` is intentionally ordered after
`#7.1` because it relies on the server-first `pendingReceiveReply` stash becoming
transition-sourced there. **#7.4 is gated on all three** (the clause is false while
any producer still emits an unlinked `.blockedOnReply`). #7.5 closes after #7.4.

**Green sub-steps (each commits only when its module set is fully green):**

- **#7.0 — pre-land the reusable frame lemmas (additive, fully green).** Prove, against the
  *current* (unchanged-signature) code, the bare frames the spike's recipe (b) names as the
  "first step of execution":
  - `linkCallerReply_preserves_ipcInvariant` and `linkCallerReply_preserves_objects_invExt`
    — short consequences of the existing `linkCallerReply_objects_frame`
    (`DualQueueMembership.lean:2708`) and `linkCallerReply_preserves_ipcInvariantFull`
    (`:3011`).
  - the `pendingReceiveReply`-store duals — short consequences of
    `storeObject_tcb_preserves_ipcInvariant` (`CrossCore/NotificationBind.lean:202`) and
    `storeObject_tcb_replyObject_preserves_ipcInvariantCore` (`DualQueueMembership.lean:2526`).

  These reference only existing definitions, so they compile with **zero** call-site churn
  and shrink every later slice's realized error set to *re-pointing* rather than novel proof.
  **Verify:** per-module `lake build` of the two invariant files; smoke; trace byte-identical
  (no transition changed).

- **#7.1 — single-core receive fold (`endpointReceiveDual` + `WithCaps`, one atomic slice).**
  ✅ **LANDED (v0.31.152).** *Correction discovered in execution:* the live `.receive`/`.replyRecv`
  dispatch routes through the **per-core** `endpointReceiveDualOnCore` (post-SM6.C), not the
  single-core `endpointReceiveDual`, so `linkReceivedCaller` could not be deleted here — its
  deletion moved to **#7.2** (where the per-core transition folds). #7.1 folds the single-core
  transition + `WithCaps`/`Checked`/`endpointReplyRecv`/`ReplyRecvWithDonation` and re-bases the
  full IPC + info-flow preservation surface.
  Thread a **required** `replyId : Option ReplyId` into `endpointReceiveDual`
  (`Transport.lean:1634`) per recipe (a); `endpointReceiveDualWithCaps`
  (`DualQueue/WithCaps.lean:139`) gains and forwards it; `endpointReplyRecv`'s legacy
  single-core receive leg passes `none`. Rewire the `.receive`/`.replyRecv` dispatch in
  `API.lean` to pass the resolved `rid` and **delete the now-dead `linkReceivedCaller`**
  (`API.lean:349`) in the *same* slice (per the remove-redundant-code directive — the fold
  makes it dead the instant the dispatch passes `some rid`). Re-point the preservation suite
  to the #7.0 frames per recipe (b). **Execution order within the slice** (red until the
  last file — see *no-green-intermediate* note): `Transport` → the Tier-3 invariant files
  (`EndpointPreservation`, `DualQueueMembership`, `PerOperation`, `StoreObjectFrame`,
  `CallReplyRecv`/`ReplyRecv`) → `WithCaps` → `API.lean` → info-flow (`Composition`,
  `Operations`, `Wrappers`, `Soundness`) → single-core tests/harness (`MainTraceHarness`,
  `NegativeStateSuite`, `OperationChainSuite`, `InformationFlowSuite`) passing `none` where
  no reply is linked. Commit only when fully green. **Verify:** `test_full.sh` (Tier-3
  invariant surface touched); trace byte-identical.

- **#7.2 — per-core receive fold (`endpointReceiveDualOnCore`).** ✅ **LANDED (v0.31.152).**
  Folded the SM6.C cross-core receive transition, rewired the live `.receive`/`.replyRecv`
  dispatch (`replyRecvBody` + both arms) through it, and **deleted `linkReceivedCaller`** (its
  SD-051/SD-053(a,c) unit tests migrated to drive the real transition). Repeat #7.1's pattern for
  the SM6.C cross-core receive transition (`CrossCore/EndpointReply.lean:150`), threading the
  resolved `rid` from `endpointReceiveDualCrossCoreDispatch{,Checked}`. Re-point
  `CrossSubsystemPerCorePreservation` and the cross-core suites
  (`SmpCrossCoreCallSuite`, `SmpCrossCoreNotificationSuite`, `SmpCrossCoreReplySuite`).
  Independent of #7.1 and #7.3 (separate function and separate call-site family).
  **Verify:** per-module build of the CrossCore +
  per-core preservation files; the three SMP suites; trace byte-identical.

- **#7.3 — call-path fold (`endpointCall` server-waiting rendezvous).** *Split in execution into
  a single-core slice (#7.3a, landed) and a per-core slice (#7.3b, remaining)* — mirroring the
  #7.1/#7.2 single-then-per-core split, because the production `.call` dispatch routes through the
  per-core `endpointCallOnCore` (via `endpointCallCrossCoreDispatch`), not the single-core
  `endpointCall`. The fold reads the server's stashed reply *inside* the transition (no new
  parameter — unlike the receive fold, the reply object is the server's existing
  `pendingReceiveReply`) and links the caller via the new named, framed
  `SystemState.linkServerStashedReply caller server`, failing closed (`.replyCapInvalid`) when the
  server provided none. (The server-first stash is established by #7.1's no-sender path, so the
  stash is transition-sourced.)

  - **#7.3a — single-core (`endpointCall`).** ✅ **LANDED (v0.31.152).** Folded `endpointCall`'s
    server-waiting rendezvous; added `linkServerStashedReply` + its complete frame set
    (`_preserves_{objects_invExt,ipcInvariant}`/`_scheduler_eq` in `Defs`; the per-conjunct
    structural frames in `StoreObjectFrame`/`DualQueueMembership`/`PerOperation`; the
    comprehensive scheduler/contract frames + `_tcb_forward`/`_tcb_ipcState_backward` in
    `EndpointPreservation`; `_preserves_projection` in `Helpers`); re-based `Call.lean`'s four
    `endpointCall_preserves_*` proofs and `Operations.lean`'s `endpointCall_preserves_projection`
    (gained the `hIdxComplete`/`hObjSetInv` structural hypotheses, conclusion unchanged). Trace
    sites supplying a server-first reply: `MainTraceHarness` F1-03, `NegativeStateSuite`
    replyRecv-setup + R1-NEG.
  - **#7.3b — per-core (`endpointCallOnCore`) + delete `linkServerFirstCaller`.** ✅ **LANDED (v0.31.153).**
    Folded `endpointCallOnCore`'s server-waiting rendezvous (compose `linkServerStashedReply` at the
    `st4 → st5` seam, before `removeRunnableOnCore`); re-based `endpointCallOnCore_rendezvous_eq`
    and the four callers (`_emits_sgi_if_remote_receiver`/`_no_sgi_if_local_receiver`/`_perCore_blocking`/
    `_reply_linkage_under_lockSet` — gained `st5`/`hLink`, SGI/blocking conclusions unchanged, reply
    linkage transferred via `linkServerStashedReply_tcb_forward`/`_tcb_ipcState_backward`) and
    `EndpointCallInvariant`'s five conjunct proofs (made the three `StoreObjectFrame` frames public).
    Per-core NI: built the missing **`objectIndexSet`-completeness propagation frames** —
    `endpointQueuePopHead_preserves_objectIndexSetComplete_and_invExt` (+ the `storeTcbQueueLinks`
    pair) made public in `Operations`, and four new `wakeThread`/`enqueueRunnableOnCore` frames in
    `PerCoreWake` (raw insert at an existing key leaves `objectIndexSet` untouched; the receiver is
    `.ready` before the wake) — then re-based the boot-core `endpointCallOnCore_call_path_NI` and the
    ∀-core `_smp` (added `st5`/`hLink`/`hObjSetInv`/`hIdxComplete`; propagate completeness `st → st4`;
    peel the link via the new `linkServerStashedReply_preserves_projection{,OnCore}` — the per-core
    frame built from `linkServerStashedReply_{scheduler,machine}_eq` + `projectStateOnCore_congr`;
    conclusions unchanged). Rewired the three `.call` dispatch arms (`API.lean` — dropped the
    post-fold `linkServerFirstCaller`, which would now *double-link* and fail; updated the dispatch
    characterization theorem), **deleted `linkServerFirstCaller`**, and migrated SD-053(b,d) to drive
    the real `endpointCall` fold end-to-end. `SmpCrossCoreCallSuite` now exercises the atomic link +
    the fail-closed no-stash rendezvous ("no green intermediate"). **Verified:** default + staged
    builds, `SmpCrossCoreCallSuite`/`SyscallDispatchSuite`, `test_smoke`, staged-partition gate;
    trace byte-identical; AK7 re-anchored (one proof-level `getTcb?`→objects-side conversion,
    `GETTCB_ADOPTION` +12).

- **#7.4 — strengthen `replyCallerLinkage`.** ✅ **LANDED (v0.31.154).** Factored the
  bidirectional reciprocity into a reusable `replyCallerLinkageReciprocal` (the strongest
  invariant that survives the fold's post-blocking-store / pre-link intermediate) and defined
  `replyCallerLinkage := reciprocal ∧ (blockedOnReply ⇒ replyObject)`.  Updated: `default` /
  boot (vacuous — no `.blockedOnReply` TCBs); `replyCallerLinkage_of_objects_eq` (unfold both
  defs); `linkCallerReply_establishes_replyCallerLinkage` (precondition is now `reciprocal` +
  `hThirdExc`, the third clause for every blocked caller *other* than the one being linked —
  it discharges the third clause directly from the atomic link); `consumeCallerReply` (the
  link-teardown prep) downgraded to `…_preserves_replyCallerLinkageReciprocal` (standalone it
  clears `replyObject` without unblocking, so it cannot preserve the third clause — the fused
  reply transition, which unblocks first, does); `linkCallerReply_preserves_ipcInvariantFull`
  re-based on the honest intermediate-state preconditions (`ipcInvariantCore` + `reciprocal` +
  `hThirdExc` — full `ipcInvariantFull st` would be *vacuous* at a link site); and
  `consumeCallerReply_preserves_ipcInvariantFull` threads `replyCallerLinkage st'` like every
  live transition.  The 16-conjunct threading architecture is otherwise unchanged — the live
  `_preserves_ipcInvariantFull` theorems carry the strengthened conjunct as a hypothesis (no
  signature change).  **Verified:** `test_full.sh` (Tier 0–3, invariant surface anchors);
  trace byte-identical; AK7 re-anchored (third-clause `objects[tid.toObjId]?` +3).

- **#7.5 — tests (establish the boundary directly).** ✅ **LANDED (v0.31.154).**
  `ModelIntegritySuite` drives the real single-core fold end-to-end
  (`replyCallerLinkage_holds_at_call_rendezvous_boundary`: the blocked caller carries a
  `replyObject`, reciprocated by the Reply) + the negative dual
  (`call_without_reply_object_fails_closed_no_unanswerable_block`).  `NegativeStateSuite` adds
  the "no unanswerable `blockedOnReply`" fail-closed check to its reply coverage.  **Verified:**
  both suites + smoke.

**Risk (highest of the three items — SM6.A/C transition + preservation surface).** The risk
is concentrated in #7.1/#7.2/#7.3 (each a no-green-intermediate signature change) and #7.4
(the 16th-conjunct break-set). Mitigations, in order: (1) #7.0 front-loads every frame so the
folds are re-pointing, not proving; (2) the per-function split makes each fold independently
green and reviewable, instead of one 300-error slice; (3) #7.4 is gated, so the invariant is
strengthened only once every producer demonstrably links — never speculatively; (4) trace
byte-identical is asserted at every slice (the fold is a *reordering* of an existing link, so
observable behaviour must not move).

### VALIDATED DESIGN & EXECUTION RECIPE (2026-06-18 spike, v0.31.148 — transition compiles; full re-base scoped)

A throwaway spike threaded `endpointReceiveDual` end-to-end and confirmed three things:
the **transition body compiles**, the **proof composition is sound** (every needed frame
lemma already exists), and the **scope is a ~90-call-site + 300+-proof-error atomic re-base
across ~15 files** — there is *no green intermediate* (a required-`replyId` param breaks every
call site at once), so it must be executed as one focused, uninterrupted slice.

**(a) The threaded transition body (validated to compile).** `endpointReceiveDual (endpointId)
(receiver) (replyId : Option ReplyId)` folds the former `linkReceivedCaller` dispatch step in
at the two branches that already distinguish the cases:
- **Call path** (`senderWasCall`, sender → `.blockedOnReply`): after the `blockedOnReply`
  store, `match replyId with | none => .error .replyCapInvalid | some rid => SystemState.linkCallerReply
  sender rid …`, then the receiver `.ready` store.  (Reject when a Call rendezvous carries no
  Reply — the post-state is discarded, so no stranding.)
- **Send path** (sender → `.ready`): unchanged (a one-way Send links nothing).
- **No-sender path** (receiver → `.blockedOnReceive`): after the `storeTcbIpcState`, read the
  receiver TCB and `storeObject … { rTcb with pendingReceiveReply := replyId }` (server-first
  stash; `none` clears any stale stash).
Make `replyId` **required** (not defaulted) — a defaulted param before the `Kernel` monad arg
is mis-bound by every positional-state call `endpointReceiveDual ep recv st` anyway, so required
is cleaner.  `endpointReplyRecv`'s legacy single-core receive leg passes `none`.
`endpointReceiveDualWithCaps` gains the param and forwards it.

**(b) The proof re-base pattern (per `endpointReceiveDual_preserves_X`).** Each proof gains
`(replyId : Option ReplyId)` and, where it unfolds the body: in the Call branch, `cases replyId`
— `none` ⇒ `simp [hStep]` (the reject contradicts `hStep = .ok`); `some rid` ⇒ thread the
`linkCallerReply` frame between the two stores.  In the no-sender branch, thread the
`pendingReceiveReply` `storeObject` frame.  **Reusable frames that already exist:**
`linkCallerReply_objects_frame` (only `rid.toObjId` + `caller.toObjId` change),
`linkCallerReply_preserves_ipcInvariantFull`, `storeObject_tcb_preserves_ipcInvariant`
(NotificationBind.lean), `storeObject_tcb_replyObject_preserves_ipcInvariantCore`.  **First step
of execution: prove the *bare* reusable frames once** — `linkCallerReply_preserves_ipcInvariant`,
`linkCallerReply_preserves_objects_invExt`, and the `pendingReceiveReply`-store duals (each a
short consequence of `linkCallerReply_objects_frame` / `storeObject_tcb_*`) — then the ~300
per-site fixes are a *mechanical* application of those frames, not novel proofs.

**(c) Blast radius (90 applications / ~15 files).** Production: `WithCaps` (the
`endpointReceiveDualWithCaps` forward + its 3 preservation statements), the `.receive`/`.replyRecv`
dispatch in `API.lean` (pass the resolved `rid`, delete the now-dead `linkReceivedCaller`).
Proofs (Tier-3, the bulk — 64 errors in `EndpointPreservation.lean` alone):
`EndpointPreservation`, `DualQueueMembership`, `PerOperation`, `StoreObjectFrame`,
`CallReplyRecv/ReplyRecv`.  Info-flow: `Composition`, `Operations`, `Wrappers`, `Soundness`.
Cross-subsystem: `CrossSubsystemPerCorePreservation`.  Tests/harness (`replyId := none`):
`MainTraceHarness`, `NegativeStateSuite`, `SmpCrossCoreCallSuite`, `SmpCrossCoreNotificationSuite`,
`InformationFlowSuite`, `OperationChainSuite`.  This whole paragraph **is** slice #7.1
(single-core receive), which also removes `linkReceivedCaller` (`API.lean:349`) in the same
commit; slice #7.3 repeats for `endpointCall`'s server-waiting rendezvous (folding
`linkServerFirstCaller`, `API.lean:386`); slice #7.2 repeats for `endpointReceiveDualOnCore`
(the SM6.C cross-core suite); slice #7.4 strengthens `replyCallerLinkage` once all three
paths link.  The 64-errors-in-`EndpointPreservation.lean` figure is the *measured* #7.1
floor; apply the #1.a multiplier (estimate-to-realized ≈ 2.5×) when budgeting.

**Note on approach:** a wrapper transition (a separate `endpointReceiveDualLinked` the dispatch
composes) is **rejected** — it leaves the raw `endpointReceiveDual` producing an unanswerable
`blockedOnReply` state, defeating the transition-boundary invariant.  The fold must be **inside**
the public `endpointReceiveDual`.

---

## Verification (every sub-step)

Per-module `lake build` of **each modified module** (the default target is insufficient —
see CLAUDE.md "Module build verification"); `./scripts/test_smoke.sh` (Tier 0–2) minimum;
`./scripts/test_full.sh` + `test_tier3_invariant_surface.sh` for invariant/theorem changes
(every #7 fold touches preservation — #7.1, #7.2, #7.3 — and #7.4 changes the invariant
itself). Assert the `Main.lean` trace is **byte-identical** to
`tests/fixtures/main_trace_smoke.expected` at every #7 slice (each fold is a reordering of an
existing link, so observable behaviour must not move). After each landed slice:
`./scripts/bump_version.sh <version>` (syncs all version sites; verified by
`check_version_sync.sh`) + a `## v<x.y.z>` `CHANGELOG.md` entry; regenerate
`docs/codebase_map.json` when Lean sources change; run
`scripts/check_production_staging_partition.sh` if a module moves between production and
staged. Rust ABI mirrors (already landed for #2.c) are verified via
`cargo check --profile test` (cargo test hangs in-container; CI runs the full suite).
The pre-commit hook (module build + `sorry`/`axiom` scan) must remain installed and **not**
be bypassed with `--no-verify`.

## Follow-up / tracked debt
1. **Rights-less reply cap (#2 residual).** ✅ **RESOLVED (v0.31.155).** `mintReplyCap` now
   mints `.replyCap` with `rights := AccessRightSet.empty` (the only production reply-cap mint);
   the `mintReplyCap_preserves_capabilityInvariantBundle` proof updated to the rights-less shape.
2. **Stale `capabilityInvariantBundle` conjunct-count comment (#1 residual).** ✅ **RESOLVED.**
   `Capability/Invariant/Defs.lean` reads "the bundle now has **7** conjuncts" (with the
   7 → 6 → 7 history), matching the live tuple.
3. **Reply-cap badge model** (seL4 reply caps are badge-less). ✅ **CONFIRMED.** `mintReplyCap`
   mints `badge := none`; being the only production reply-cap mint, the kernel's reply caps are
   badge-less by construction.
4. **Full HW-tier reply-lock contention stress** — CI/QEMU, post-v1.0.0 (legitimately deferred;
   not a model-level item).

**Plan status: all actionable items landed.** #1–#6, #7.1–#7.5, and residual-debt #1/#2/#3
are complete (v0.31.140–v0.31.155).  Item 4 is a post-v1.0.0 hardware-tier stress task, tracked
in `docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`.

Refs: docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md (SM6.C/SM6.D Reply objects)
Refs: CHANGELOG.md v0.31.140–v0.31.149 (#2/#1 landing record; #7 design validation)

---

## PR #827 review pass — in-transition single-use consume (✅ v0.32.51–57)

The Codex review of PR #827 (the plan's landing PR) surfaced numbered findings
against the landed surface: #4 (usable `.write` mint rights) closed at v0.32.52,
#1/#2 (lock-set reply threading — 2PL coverage of the folded reply-object writes)
at v0.32.53, #6/#7 (receive-stash admission hardening) at v0.32.54–55.
**#3 (P2) — the deepest — closed across v0.32.56–57**: the direct `endpointReply` /
`endpointReplyRecv` primitives delivered but never consumed the answered
caller↔Reply link, so a below-API operation chain using them directly left the
Reply in-use forever (`reply.caller` set, the `.ready` caller's `replyObject`
stale) — single-use held only at the *dispatch* boundary, mirroring exactly the
#7 D6 gap on the link side.

**The fold (v0.32.57, same shape as #7.1–#7.3b).**  `consumeCallerReply` is folded
into the reply primitives — `endpointReply`, `endpointReplyRecv` (reply leg, ahead
of the receive leg so one-object reuse admits the same `rid`), and
`endpointReplyOnCore` (hence `endpointReplyRecvOnCore` + both cross-core dispatch
wrappers) — keyed on the woken caller's own `tcb.replyObject` (no-op when
unlinked).  The three separate dispatch-layer consume steps in `API.lean` are
deleted (`replyRecvBody` + both `.reply` arms).  `consumeCallerReply` is total
(`consumeCallerReply_isOk`), so no new failure mode.  Foundation slice (v0.32.56)
+ completion slice (v0.32.57): the per-conjunct `consumeCallerReply_preserves_*`
frame family over new `Model/State.lean` transport drivers; ~60
preservation-theorem re-bases (single-core + cross-core + staged NI);
`endpointReply_preserves_ipcInvariantFull` **de-threads `hRCLRecip'`** via the new
`endpointReply_preserves_replyCallerLinkageReciprocal` (a direct reply now
establishes reciprocity internally — the transition-boundary dual of #7.4's
link-side clause).  Boundary tests:
`ModelIntegritySuite` `direct_reply_consumes_caller_link_single_use`,
`SmpCrossCoreReplySuite` §3.8.  Trace byte-identical.

With this fold the Reply object is **single-use end-to-end at every layer**:
linked atomically at `Call`/receive rendezvous (#7.1–#7.3b), answerable always
(#7.4), and consumed atomically at delivery (PR #827 #3) — no layer can observe
or construct a delivered-but-unconsumed Reply.

Refs: CHANGELOG.md v0.32.51–v0.32.57 (per-finding landing record)
