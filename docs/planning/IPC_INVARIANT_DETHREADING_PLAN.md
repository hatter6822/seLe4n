# IPC `ipcInvariantFull` De-Threading — Workstream Plan

> **Goal.** Make every IPC transition's `*_preserves_ipcInvariantFull` theorem
> *concretely prove* `ipcInvariantFull st'` from `ipcInvariantFull st` + the step,
> with **no threaded post-state hypotheses**.  Today these theorems assume ~14
> structural post-state conjuncts (`hDualQueue'`, `hRCL'`, `hDCA'`, …) and only
> derive `ipcInvariantCore` + two easy conjuncts inline.  De-threading closes the
> verification: it is the difference between "*if* the post-state already satisfies
> the structural invariant, the transition is fine" and "the transition *establishes*
> the structural invariant."  This is the missing end-to-end maintenance proof that a
> top-level *"every IPC syscall preserves `ipcInvariantFull`"* theorem requires.

> **Origin.** Surfaced by the Reply-Objects completion-plan self-audit
> (`REPLY_OBJECTS_COMPLETION_PLAN.md` §#7.4): the third clause of `replyCallerLinkage`
> was added to the *definition* and proven *establishable* (`linkCallerReply_establishes_…`),
> but the live folded transitions still **thread** it.  The user scoped the fix up to
> the full bundle: de-thread **all** structural conjuncts for **all** IPC transitions.

## The surface (de-threading targets)

`*_preserves_ipcInvariantFull` theorems (each currently threads the post-state
structural conjuncts):

| Transition | File |
|---|---|
| `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv` | `IPC/Invariant/Structural/DualQueueMembership.lean` |
| `notificationSignal`, `notificationWait` | `IPC/Invariant/Structural/DualQueueMembership.lean` |
| `endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`, `endpointCallWithCaps` | `IPC/Invariant/Structural/DualQueueMembership.lean` |
| `endpointCallOnCore` (+ the SM6.B/C per-core `…OnCore` / `CrossCoreDispatch` arms) | `IPC/CrossCore/*Invariant.lean` |
| `linkCallerReply`, `consumeCallerReply` (reply-link primitives — prep) | `DualQueueMembership.lean` |

The 14 `ipcInvariantFull` conjuncts (post-`ipcInvariantCore` = #1):
`dualQueueSystemInvariant`, `allPendingMessagesBounded`*, `badgeWellFormed`*,
`waitingThreadsPendingMessageNone`, `endpointQueueNoDup`,
`ipcStateQueueMembershipConsistent`, `queueNextBlockingConsistent`,
`queueHeadBlockedConsistent`, `blockedThreadTimeoutConsistent`,
`donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`,
`donationBudgetTransfer`, `blockedOnReplyHasTarget`, `replyCallerLinkage`,
`pendingReceiveReplyWellFormed`.  (* already derived inline — not threaded.)

## Coverage census (concrete per-transition `*_preserves_<conjunct>` lemmas today)

| Conjunct | Status | Notes |
|---|---|---|
| `dualQueueSystemInvariant` | **wiring** | concrete lemma for all 7 base transitions (+ 2 WithCaps) |
| `waitingThreadsPendingMessageNone` | **wiring** | all 7 base transitions |
| `endpointQueueNoDup` | **wiring** | all 7 base transitions |
| `ipcStateQueueMembershipConsistent` | **wiring** | all 7 base transitions |
| `queueNextBlockingConsistent` | **partial** | store-level lemmas exist; transition-level gaps |
| `queueHeadBlockedConsistent` | **partial** | some store-level; transition-level gaps |
| `blockedThreadTimeoutConsistent` | **from scratch** | 0 concrete lemmas |
| `donationChainAcyclic` | **from scratch (hard)** | 0; acyclicity through donation mutation |
| `donationOwnerValid` | **from scratch** | 0 |
| `passiveServerIdle` | **from scratch** | 0 |
| `donationBudgetTransfer` | **from scratch** | 0 |
| `blockedOnReplyHasTarget` | **from scratch** | 0; TCB-state (`blockedOnReply ⇒ replyTarget.isSome`) |
| `replyCallerLinkage` | **from scratch** | 0; reciprocal threaded pre-#7.4, third clause new |
| `pendingReceiveReplyWellFormed` | **from scratch** | 0; stash well-formedness + injectivity |

## Sequencing (coherent PR-sized slices)

Each slice is independently green and trace-byte-identical (these are *proofs about*
existing transitions — no semantics change).  Within a slice, build the reusable
store/queue frame lemmas once, then apply across transitions.

- **D0 — assembly refactor.**  Add `ipcInvariantFull_of_components` (build the
  16-tuple from the 14 concrete results) so each de-threaded transition proof is a
  uniform 14-line assembly.  Name the new third clause `blockedOnReplyHasReplyObject`
  (a first-class predicate; gives a named projection + clean frame targets).
- **D1 — wiring (4 conjuncts).**  De-thread `dualQueueSystemInvariant`,
  `waitingThreadsPendingMessageNone`, `endpointQueueNoDup`,
  `ipcStateQueueMembershipConsistent` from the 7 base transitions by plugging the
  existing concrete lemmas into the bundle.  Removes 4 threaded hypotheses each.
- **D2 — `replyCallerLinkage` (the origin gap).**  Build the
  `blockedOnReplyHasReplyObject` frame family (through `endpointQueuePopHead`,
  `storeTcbIpcStateAndMessage` ready / blocked-except-self, `wakeThread`,
  `removeRunnable`, `storeObject` stash-clear) + `linkServerStashedReply_establishes_…`;
  prove `<foldedTransition>_establishes_replyCallerLinkage` for `endpointCall`,
  `endpointReceiveDual` (single-core) and `endpointCallOnCore`,
  `endpointReceiveDualOnCore` (per-core); for `endpointReply`/`endpointReplyRecv`
  preserve via unblock+consume.  Keep reciprocal threaded for now (it was threaded
  pre-#7.4) **or** discharge it here if the reciprocal frames fall out cheaply.
  Add the *consumer*: `blockedOnReply_caller_is_answerable` (every `.blockedOnReply`
  caller has a backing Reply naming it) — the safety lemma that *uses* the invariant.
- **D3 — `blockedOnReplyHasTarget` + `pendingReceiveReplyWellFormed`.**  TCB-state /
  stash invariants; moderate (store-frame + the fold's link/stash discipline).
- **D4 — `queueNextBlockingConsistent` + `queueHeadBlockedConsistent`.**  Lift the
  store-level lemmas to transition level; fill the gaps.
- **D5 — `blockedThreadTimeoutConsistent`.**  Timeout/budget TCB invariant.
- **D6 — `donationOwnerValid` + `donationBudgetTransfer` + `passiveServerIdle`.**
  Donation-state invariants; reuse the donation-step frames.
- **D7 — `donationChainAcyclic` (hardest).**  Acyclicity of the donation graph
  through `applyCallDonation` / `returnDonatedSchedContext` / PIP.  Likely needs a
  dedicated graph-frame lemma set.
- **D8 — close out.**  Drop the last threaded hypotheses from every bundle theorem;
  de-thread the WithCaps/Checked/CrossCore variants (route through the base proofs);
  add the payoff theorem `syscallDispatch_preserves_ipcInvariantFull` (now provable
  with no assumed conjuncts); tests + docs.

## Risk / effort

Largest invariant-proof workstream in the repo to date — comparable to a slice of
seL4's functional-correctness invariant preservation.  ~14 conjuncts × ~11
transitions; ~half wiring, ~half from-scratch.  `donationChainAcyclic` (D7) is the
research-grade item and is sequenced last so all reusable frames exist first.  Every
slice is behaviour-preserving (proofs only) ⇒ trace byte-identical is invariant.

## Status

| Slice | Status | Version |
|---|---|---|
| D0 named predicate (`blockedOnReplyHasReplyObject`) | ✅ LANDED | v0.31.157 |
| D1 wiring (4 conjuncts × 7 tx) | ⏳ **blocked**: the 4 "wiring" conjuncts (`dualQueueSystemInvariant`, `endpointQueueNoDup`, `ipcStateQueueMembershipConsistent`, `waitingThreadsPendingMessageNone`) all carry `hFreshCaller`/`hSendTailFresh` side-conditions on the enqueue-style transitions (`endpointCall`/`SendDual`/`ReceiveDual`); de-threading them needs a clean dispatcher-dischargeable freshness precondition (`caller .ready`) → freshness lemma via `ipcStateQueueMembershipConsistent`. Sequenced after D2. | — |
| D2 replyCallerLinkage (third clause) + consumer | ✅ **LANDED (all 3 establish cases)**: consumer (v0.31.157), full frame family incl. `endpointQueuePopHead`/`endpointQueueEnqueue` frames + `linkCallerReply`/`linkServerStashedReply`/`cleanupPreReceiveDonation` establishes + `wakeThread_…_of_ready` (per-core); single-core `endpointCall`/`endpointReceiveDual_establishes_…` (v0.31.159) **and** per-core `endpointCallOnCore_establishes_…` (v0.31.160); **all 3 bundle theorems that can introduce `.blockedOnReply` de-threaded** (thread `replyCallerLinkageReciprocal st'`, establish the third clause). Preserve-only bundles de-threaded: `endpointSendDual` (v0.31.161); `notificationSignal`/`notificationWait` (v0.31.162); `endpointReply` + `endpointReplyRecv` (v0.31.163); the **3 WithCaps** (v0.31.164) via a new cap-transfer frame chain (`ipcTransferSingleCap_ok_implies_cnode_at_root` → `ipcUnwrapCapsLoop_objects_at_root_orig_or_cnode` → `ipcUnwrapCaps_objects_at_root_orig_or_cnode` → `ipcUnwrapCaps_tcb_backward` → `ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject`; the WithCaps reuse the base establishes/preserve + this frame). **ALL IPC bundles de-threaded.** Only `consumeCallerReply` deliberately stays threaded — it clears a caller's `replyObject` **without** unblocking, so it cannot establish the third clause standalone (re-established by the fused reply transition). Reciprocal-half de-thread (optional). | v0.31.164 |
| D2′ lifecycle/retype third clause | ✅ **LANDED v0.31.165**: `lifecycleRetypeObject_preserves_blockedOnReplyHasReplyObject` (retype writes only `target`; every other slot framed, the `target` obligation discharged by a clean `newObj` well-formedness side-condition `hNewObjThird`, analogous to the bundle's existing CNode/notification `newObj` constraints). Both `lifecycleRetypeObject_preserves_{coreIpcInvariantBundle,lifecycleCompositionInvariantBundle}` de-threaded in place. **Every bundle whose third clause is sound to establish/preserve is now de-threaded; only `consumeCallerReply` stays threaded (cannot establish standalone).** | v0.31.165 |
| D3 blockedOnReplyHasTarget + pendingReceiveReplyWellFormed | 🔄 **`blockedOnReplyHasTarget` FULLY DE-THREADED** (v0.31.167): frame family + establishes/preserves for every transition built (v0.31.166), and **all** `ipcInvariantFull` bundles now wired — `hBRT'` removed, the clause established/preserved concretely from `hInv.blockedOnReplyHasTarget`: `endpointCall`/`endpointReceiveDual` (v0.31.166); `endpointSendDual`/`notificationSignal`/`notificationWait`/`endpointReply`/`endpointReplyRecv`/3×WithCaps/`endpointCallOnCore`/2×`lifecycleRetypeObject` (v0.31.167, the retype pair via a `hNewObjTarget` `newObj` side-condition). `consumeCallerReply_preserves_ipcInvariantFull` needs no edit — it derives the clause as the 15th `ipcInvariantCore` conjunct through the `ipcInvariantFull_of_core_replyCallerLinkage` seam. **`pendingReceiveReplyWellFormed` frame family LANDED (v0.31.168)**: 3 store-kind keystones (tcb/reply/non-tcb-reply; coincident-slot kind-disjointness `.reply`≠`.tcb` frames cross-kind lookups without a kind-stability invariant) + `establishStash` + `preserveFields` + `storeTcbIpcState{,AndMessage}`/`storeTcbQueueLinks`/`consumeReply`/`linkReply` store frames. **Finding F-1 (the kernel-semantics blocker) ✅ REMEDIATED (v0.31.170)**: eager stash-clear (`storeTcbReceiveComplete`) makes `pendingReceiveReplyWellFormed` a true invariant of `endpointSendDual`/`notificationSignalBound{,OnCore}`; 20 mirror frames carry their proofs. **✅ DE-THREADING COMPLETE: 15/15 bundles (v0.31.171 → v0.31.174)** — `grep "hPRR' : pendingReceiveReplyWellFormed st'"` is now empty. The v0.31.174 final slice closed the `endpointCall` family: `linkServerStashedReply_preserves_pendingReceiveReplyWellFormed` (the net-effect crux — the deliver-keeps-stash ≫ link-clears-stash composite, proven via C2-uniqueness: the server is the sole staser of `rid`, so clearing it leaves `rid` unstashed and linking it to the caller is C1-safe), `endpointCall` (threads dischargeable `hCallerNotRecv`), `endpointCallOnCore`, `endpointSendDualWithCaps`, `endpointCallWithCaps`. **Earlier progress: 12/15 (v0.31.171 → v0.31.173)** — `endpointReply`, `consumeCallerReply`, `notificationSignal` (`notificationWaiterConsistent st`), `notificationWait`/`endpointSendDual` (`hWaiterNotRecv`/`hSenderNotRecv`), `linkCallerReply` (`hNotStashed`), the `lifecycleRetypeObject` pair (`hNewObjNoStash`+`hTargetNotStashedReply`), **+ v0.31.173** the `endpointReceiveDual` establish family (`endpointReceiveDual`+`endpointReceiveDualWithCaps`+`endpointReplyRecv`; `hReplyIdValid`+`hReceiverNotRecv`+`hQHBC`) + reusable reply-store infrastructure. **3 bundles remain (the `endpointCall` family)** (precise per-bundle blockers in the "D3 remaining" note below): the `endpointReceiveDual` ESTABLISH (needs `hReplyIdValid` present-free-unstashed + `cleanupPreReceiveDonation`/`linkCallerReply` reply-half frames), `endpointCall` (mid-transition stash window before `linkServerStashedReply` — needs end-to-end object-diff proof), the WithCaps (`ipcUnwrapCaps_preserves_…` reply-slot-disjointness), `linkCallerReply`, and the tractable `lifecycleRetypeObject` pair. | v0.31.168 → F-1 v0.31.170 → 5/15 v0.31.171 |
| D4 queueNext/HeadBlocked | 🔄 **PARTIAL (v0.31.175): 9/26 slots** — `queueNextBlockingConsistent` de-threaded from 5 bundles, `queueHeadBlockedConsistent` from 4 (`endpointReply`, `notificationSignal`, `notificationWait` [qNext only], the `lifecycleRetypeObject` pair); ~46 reusable store/transition frames built. **8 enqueue-style transitions BLOCKED on missing invariant — see Finding F-2.** | v0.31.175 |
| **F-2 prereq: `endpointQueueMemberBlocked` (reachable→blocked) invariant** | ⏳ unblocks D4-residual + D1 | — |
| D5 blockedThreadTimeoutConsistent | ⏳ | — |
| D6 donationOwnerValid + donationBudgetTransfer + passiveServerIdle | ⏳ | — |
| D7 donationChainAcyclic | ✅ **DE-THREADED (v0.31.176): all 13 bundles** via `donationOwnerValid_implies_donationChainAcyclic st' hDOV'` (derives from the still-threaded `hDOV'`); `grep hDCA'` empty | v0.31.176 |
| D5 blockedThreadTimeoutConsistent | ⏳ **needs from-scratch infra** — no IPC transition ever writes `timeoutBudget := some`, but wakes set `.ready` while a thread *may* carry a budget; clean de-thread needs per-transition dischargeable `⟨woken⟩.timeoutBudget = none` preconditions | — |
| D6 donationOwnerValid + donationBudgetTransfer + passiveServerIdle | 🔄 **IN PROGRESS (UNBLOCKED by Finding F-3)** — **`donationBudgetTransfer` ✅ FULLY DE-THREADED (13/13 bundles, v0.31.182)**: `grep "hDBT' : donationBudgetTransfer st'"` is now empty — the **first conjunct established entirely from the pre-state** (D7's `donationChainAcyclic` is derived from the still-threaded `hDOV'`; this one stands alone). The v0.31.182 final slice closed the last 4: the 3 binding-**touching** receive-family bundles (`endpointReceiveDual` / `endpointReceiveDualWithCaps` / `endpointReplyRecv`) via `cleanupPreReceiveDonation_preserves_donationBudgetTransfer` (the pre-receive donation-return moves the SchedContext server→owner, keeping it singly-held — *not* `sameSchedContextBindings`, so it needs the dedicated preservation argument: `returnDonatedSchedContext_tcb_schedContextBinding_backward` gives the 3-way post-state binding shape [server→`.unbound`, owner→`.bound scId`, else framed], `returnDonatedSchedContext_preserves_donationBudgetTransfer` shows no new scId-sharing pair arises); **+ `endpointCallOnCore`** (cross-core) via `endpointCallOnCore_sameSchedContextBindings` (mirror of the single-core frame in `IPC/CrossCore/` — `wakeThread`/`removeRunnableOnCore` are scheduler-only writes, so the cross-core call leaves every TCB's `schedContextBinding` byte-identical; `wakeThread_sameSchedContextBindings_of_ready` is the new keystone). Earlier **(9/13, v0.31.181)**: + the 2 `lifecycleRetypeObject` bundles (`coreIpcInvariantBundle` + `lifecycleCompositionInvariantBundle`) via `lifecycleRetypeObject_preserves_donationBudgetTransfer` (a `newObj`-`.unbound` side-condition `hNewObjUnbound` — a fresh retyped TCB holds no SchedContext, so it cannot share an scId; every other slot frames from the pre-state). Earlier **(7/13, v0.31.180)**: + `endpointCall`, `endpointSendDualWithCaps`, `endpointCallWithCaps` via the link-helper family (`linkReply` / `linkCallerReply` / `linkServerStashedReply` `_sameSchedContextBindings` + `linkReply_preserves_objects_invExt`) and `ipcUnwrapCaps_sameSchedContextBindings` (one-liner off `ipcUnwrapCaps_tcb_backward` — cap transfer leaves every TCB slot byte-identical). **All 7 binding-free single-core transitions done.** Earlier **(4/13, v0.31.179)**: reusable `sameSchedContextBindings` frame (`donationBudgetTransfer_of_sameSchedContextBindings` + the store-op family `storeObject_{modifiedTcb,nonTcb}` / `storeTcbIpcState{,_fromTcb,AndMessage}` / `storeTcbReceiveComplete` / `storeTcbQueueLinks` / `storeObject_endpoint'` / `endpointQueue{PopHead,Enqueue}` `_sameSchedContextBindings` + `of_objects_eq`) de-threads `hDBT'` from `notificationWait` / `notificationSignal` / `endpointReply` (v0.31.178) **+ `endpointSendDual`** (v0.31.179). The binding-free transitions establish the conjunct by the frame; core IPC transitions never write a `schedContextBinding`. **`donationOwnerValid` IN PROGRESS (9/13 bundles, v0.31.188)**: **v0.31.188**: + the 2 clean WithCaps (`endpointSendDualWithCaps` + `endpointCallWithCaps`) via `ipcUnwrapCaps_donationOwnerFrame` — `ipcUnwrapCaps` writes only CNode caps at `receiverRoot`, so every SchedContext (new `ipcUnwrapCaps_preserves_schedContext_objects` chain: `ipcTransferSingleCap` → `ipcUnwrapCapsLoop` → `ipcUnwrapCaps`, mirroring the existing `_preserves_tcb_objects` — a SchedContext at `receiverRoot` makes `getCNode?` return `none`, contradicting the transfer's `.ok`) and every TCB (`ipcUnwrapCaps_preserves_tcb_objects`) survives byte-identical; the WithCaps frames compose the base `endpointSendDual`/`endpointCall` `_donationOwnerFrame` with the cap-transfer frame, threading the base's `hQHBC`/`hSenderNotReply`/`hCallerNotReply`. Earlier **(7/13, v0.31.187)**: + `endpointCallOnCore` (cross-core) via `endpointCallOnCore_donationOwnerFrame` — the cross-core mirror of `endpointCall` (per-core `wakeThread` [+ `wakeThread_donationOwnerFrame_of_ready` — the woken thread is `.ready`, so the object map is element-wise unchanged] / `removeRunnableOnCore` in place of `ensureRunnable`/`removeRunnable`); the bundle de-threads `hDOV'` after `subst hStep` via `donationOwnerValid_of_frames`. **The call path (single-core + cross-core) is now fully de-threaded for `donationOwnerValid`.** Earlier **(6/13, v0.31.186)**: + `endpointCall` via `endpointCall_donationOwnerFrame` — the rendezvous receiver (receiveQ head) is `.blockedOnReceive` (`hQHBC`) and the caller is running (dischargeable `hCallerNotReply`); the caller is *set* `.blockedOnReply` but was not one before, so no existing owner witness is lost. New forward link-helper frames `linkReply`/`linkCallerReply`/`linkServerStashedReply` `_donationOwnerFrame` (reply-object store + `ipcState`/binding-preserving TCB writes) carry the reply-link leg; the caller-store pre-state is discharged via `storeTcbIpcStateAndMessage_ipcState_eq` (caller=receiver) / `_preserves_objects_ne` + `endpointQueuePopHead_tcb_ipcState_backward` (caller≠receiver). Earlier **(5/13, v0.31.185)**: + the 2 `lifecycleRetypeObject` bundles (`coreIpcInvariantBundle` + `lifecycleCompositionInvariantBundle`) via `lifecycleRetypeObject_preserves_donationOwnerValid` — the retype reduces to a single `storeObject target newObj`, so `donationOwnerValid_of_frames` does *not* apply (retype can create a fresh TCB binding, breaking the backward `sameSchedContextBindings`); the direct proof handles the retype slot via `hNewObjUnbound` (a fresh TCB is `.unbound`, never `.donated`) and two dischargeable target-slot side-conditions (`hTargetNotSc`/`hTargetNotOwner` — the retyped slot is untyped/freed memory, not a live SchedContext or `.blockedOnReply` owner). Earlier **(3/13, v0.31.184)**: reusable forward-frame `donationOwnerFrame` (packaged `scForward` + `ownerForward` with `refl`/`trans`/`of_objects_eq`) + `donationOwnerValid_of_frames` (backward `sameSchedContextBindings` + forward `donationOwnerFrame`) + the store-op family — `storeObject_oldNonScNonTcb` / `storeObject_modifiedTcb` / `storeTcbIpcState{,_fromTcb,AndMessage}` / `storeTcbReceiveComplete` `_donationOwnerFrame` (a TCB store frames the owner side iff its pre-state `ipcState ≠ .blockedOnReply`), **plus** the ipcState+binding-preserving rewrites `storeObject_modifiedTcbPreservingOwner` / `storeTcbQueueLinks` / `endpointQueuePopHead` / `endpointQueueEnqueue` `_donationOwnerFrame` (queue-link rewrites preserve owner witnesses *unconditionally* — even a `.blockedOnReply` owner — since `tcbWithQueueLinks` touches only link fields). **v0.31.184**: + `endpointSendDual` via `endpointSendDual_donationOwnerFrame` — the rendezvous receiver (receiveQ head) is `.blockedOnReceive` by `hInv.queueHeadBlockedConsistent`, the block-path sender is the running caller (dischargeable `hSenderNotReply`); neither is a `.blockedOnReply` owner. Earlier **(2/13, v0.31.183)**: `notificationWait` (dischargeable `hWaiterNotReply`) + `notificationSignal` (woken head waiter `.blockedOnNotification` via `hNWC : notificationWaiterConsistent`). **Architectural note (binding the remaining 10)**: the bare `endpointReply`/`endpointReplyRecv` transitions *wake the `.blockedOnReply` donation owner* without returning the donation (the donation-return lives in the `*WithDonation` wrappers via `applyReplyDonation`), so they do **not** preserve `donationOwnerValid` at the bare level — de-threading those must compose at the donation-wrapper level. The receive family (`endpointReceiveDual{,WithCaps}`, `endpointReplyRecv`) additionally returns a donation via `cleanupPreReceiveDonation` (binding change → not `sameSchedContextBindings`-clean), needing the dedicated donation-return argument. **Remaining `donationOwnerValid` (4 bundles — the donation-return / owner-waking family)**: `endpointReceiveDual` + `endpointReceiveDualWithCaps` (return a donation via `cleanupPreReceiveDonation` — binding change, *not* `sameSchedContextBindings`-clean → needs the donation-return argument), `endpointReply`/`endpointReplyRecv` (wake the `.blockedOnReply` owner → composite `*WithDonation` treatment with `applyReplyDonation`; the bare transitions genuinely do not preserve `donationOwnerValid` — the donation-return is what restores it). **Remaining D6**: `donationOwnerValid` (4 bundles) + `passiveServerIdle` (13 bundles). | v0.31.188 |
| **D6 prereq: `donationOwnerUnique` (18th `ipcInvariantFull` conjunct)** | ✅ **ADDED (v0.31.189)** — no two distinct threads name the same `owner` in a `.donated _ owner` binding.  Established across all 13 bundles + retype + cross-core + default + boot + arch object-frames (preserved by `sameSchedContextBindings` injection / donation-return removal / fresh-retype / object-eq).  **Unblocks** `cleanupPreReceiveDonation_preserves_donationOwnerValid` (proven) → the receive-family `donationOwnerValid` de-thread (`endpointReceiveDual{,WithCaps}`).  The `endpointReply`/`endpointReplyRecv` pair remains composite-only (bare wakes the owner without the return). | v0.31.189 |
| D8 close-out + payoff theorem | ⏳ | — |

### Finding F-3 — `donationOwnerValid` ∧ `donationBudgetTransfer` were jointly unsatisfiable for any donated state — ✅ REMEDIATED (deep code/model fix)

**Severity: Medium** (specification gap; not directly exploitable). **Status: closed** —
remediated by completing the SchedContext ownership transfer in the donation primitive
(the **deep code/model fix**, not the spec-weakening originally sketched below).

**The defect (as found).**

- `donationOwnerValid` (`Defs.lean`, AUD-7 clause) required: a server with
  `schedContextBinding = .donated scId owner` ⇒ the `owner` has
  `schedContextBinding = .bound scId`. So both server (`.donated scId …`) and owner
  (`.bound scId`) had `schedContextBinding.scId? = some scId`.
- `donationBudgetTransfer` forbids **any** two distinct TCBs from both having
  `scId? = some scId`.
- `donationOwnerValid` also forces `owner ≠ server` (self-donation excluded). ⟹
  **contradiction whenever any donation was live.**
- **Live, not theoretical:** `donateSchedContext` (`Endpoint.lean`, via
  `applyCallDonation` on the production `.call` path) set the server
  `.donated clientScId clientTid` and `sc.boundThread := serverTid` but **never cleared
  the client's `.bound clientScId`**. Every donating call produced the inconsistent pair;
  `donationBudgetTransfer` was only ever established **vacuously** (boot, all `.unbound`).
- **Implication:** `ipcInvariantFull` could not hold for any donated state, so a
  `dispatchWithCap_preserves_ipcInvariantFull` over a donating `.call` was
  unprovable/vacuous — the IPC safety proofs effectively covered only donation-free states.

**Remediation that LANDED (implement-the-improvement — the deep fix, do NOT weaken
coverage).** The donation primitive now **completes the ownership transfer**: the donor
relinquishes its SchedContext, matching seL4 MCS `sched_context_donate` (which clears the
previous holder's `tcb_sched_context`). Concretely:

1. **`donateSchedContext` (`Endpoint.lean`)** — adds a donor-clear store
   (client `.bound clientScId` → `.unbound`), ordered before the server `.donated` store
   so the server-binding postcondition stays free of a `clientTid ≠ serverTid`
   side-condition. After donation the SchedContext is referenced by **exactly one**
   binding (the server's `.donated`).
2. **`donationOwnerValid` clause 4 (`Defs.lean`)** — owner `.bound scId` → owner
   **`.unbound`** (the donor gave up its SchedContext; it is recoverable through the reply
   object in clause 3, not a residual `.bound`). The acyclicity subsumption
   (`donationOwnerValid_implies_donationChainAcyclic`, `donationChain_no_extension`)
   survives verbatim — `.unbound ≠ .donated` is the same constructor disjointness as
   `.bound ≠ .donated`.
3. **`passiveServerIdle` (`Defs.lean`, + `_perCore`, `_scheduledNowhere`,
   `_smp_not_scheduled_anywhere`)** — also permits `.blockedOnReply` for unbound
   non-runqueue threads (a donor awaiting reply is a benign unbound state).
4. **`donationBudgetTransfer` — UNCHANGED**; now literally true for donated states (the
   donor is `.unbound`, only the server references the scId). The strongest guarantee is
   retained, *not* weakened.

**Why the deep fix over weakening `donationBudgetTransfer`** (the originally-sketched
shallow remediation): it keeps `donationBudgetTransfer` untouched, is seL4-faithful, is
**trace byte-identical** (the donation trace checks the *server's* binding post-donation
and the *donor's* only post-*return*, where it is rebound), is **information-flow-invisible**
(`Projection.lean` erases `schedContextBinding`), and adds **no** new
`SchedContextBinding` constructor (so no `BEq`/`scId?`/projection/NI-case-split cascade).
Consumers re-validated: the `DualQueueMembership` frame proofs (pass-through destructure,
robust to the clause-4 content change), the boot/per-core default-state proofs (`.ready`
stays the leftmost disjunct), `donateSchedContext_{server_binding,scheduler_eq,machine_eq}`,
`donateSchedContext_ok_server_donated`, and `applyCallDonation_preserves_projection` (the
previously-unused `hCallerObjHigh` hypothesis now discharges the donor-clear store).

**Unblocks D6** — `donationOwnerValid` / `donationBudgetTransfer` are now jointly
satisfiable for donated states, so the D6 establishes/preserves proofs become provable
rather than vacuous. The remaining D6 work is the per-transition establish/preserve
machinery (donation-step frames + the `donationOwnerValid`-`donationBudgetTransfer`
establishment on `applyCallDonation` / `applyReplyDonation`), not a spec inconsistency.

### Finding F-2 — D4 needs a new `reachable→blocked` queue invariant (8 enqueue transitions)

De-threading `queueNextBlockingConsistent` / `queueHeadBlockedConsistent` from the 8
enqueue-style transitions (`endpointSendDual`, `endpointCall`, `endpointReceiveDual`,
`endpointReplyRecv`, the 3 WithCaps, `endpointCallOnCore`; + `notificationWait` headBlocked)
is **blocked on missing invariant infrastructure**, not tedium. These transitions
`endpointQueueEnqueue` a `.ready` thread then `storeTcbIpcStateAndMessage` it to a blocking
state. Two obligations cannot be discharged store-by-store: (1) `queueHeadBlockedConsistent`
is *violated at the intermediate enqueue state* (empty-queue enqueue makes the head `.ready`
before the block-store); (2) `queueNextBlockingConsistent`'s predecessor obligation needs the
old queue tail to be *blocked on the same endpoint* to show link-compatibility. The root
cause: the codebase has only `ipcStateQueueMembershipConsistent` (**blocked→reachable**) but
lacks its converse **reachable→blocked** ("every thread reachable in an endpoint's send/receive
queue is `.blockedOnSend`/`.blockedOnCall` resp. `.blockedOnReceive` on *that* endpoint").
**Remediation (implement-the-improvement, not weaken):** add `endpointQueueMemberBlocked` as a
new `ipcInvariantFull` conjunct + prove its preservation across every transition (the
transitions maintain it by construction — enqueue is always paired with block, popHead with
unblock), then complete the 8 D4 de-threads using it. This same invariant unblocks **D1**'s
4 "wiring" conjuncts (same enqueue-freshness root). Sized as its own slice, sequenced before
the D4-residual and D1.

## Finding F-1 — `pendingReceiveReplyWellFormed` is not preserved by the Send/notification receive-completion wakes — ✅ REMEDIATED (v0.31.170)

**Status: closed.**  The eager-stash-clear remediation landed at v0.31.170: a dedicated
`storeTcbReceiveComplete` store helper (`= storeTcbIpcStateAndMessage` with `.ready`
hardcoded **and** `pendingReceiveReply := none`) now backs the three non-Call
receive-completion wakes — `endpointSendDual` rendezvous, `notificationSignalBound`, and
`notificationSignalBoundOnCore` — so a Send/notification-woken receiver no longer carries a
stale stash.  `storeTcbIpcStateAndMessage` itself is **unchanged** (the `endpointCall`
rendezvous keeps the stash for `linkServerStashedReply` to consume).  20 mirror frames
`storeTcbReceiveComplete_*` (each a near-verbatim copy of its `storeTcbIpcStateAndMessage_*`
sibling, the `.ready`-specialisation dropping the now-vacuous `ipc`/`hTargetOk`/`hStashOk`
side-conditions) carry the three transitions' structural / NI / lock-set proofs across the
helper swap.  `pendingReceiveReplyWellFormed` is now a **true invariant** of all three
transitions; the conjunct's de-threading (per-transition establishes/preserves + bundle
`hPRR'` removal, using the v0.31.168 frame family + the new `storeTcbReceiveComplete`
frames) is unblocked.  Trace byte-identical; full build green (376 jobs); `test_full` green.

----

## D3 `pendingReceiveReplyWellFormed` de-threading — remaining 10 bundles (v0.31.171)

5/15 bundles de-threaded (see the D3 status row).  **Update (v0.31.172): 8/15** — slice 1
added `linkCallerReply` (frame `linkCallerReply_preserves_pendingReceiveReplyWellFormed` with
an all-`tid tcb` `hNotStashed` precondition; bundle relocated after the frame family, now
core-keyed so it also carries pre-state `hPRR`) and the `lifecycleRetypeObject` pair (frame
`lifecycleRetypeObject_preserves_pendingReceiveReplyWellFormed` proved directly off the
post-state via `lifecycleRetypeObject_ok_as_storeObject`, with two `newObj`-keyed
side-conditions `hNewObjNoStash` + `hTargetNotStashedReply`).  **7 remain.**  The remaining 10 each need infrastructure
*beyond* the `blockedOnReplyHasTarget` template, because PRR's C1 reads **both** the TCB store
(ipcState + `pendingReceiveReply`) **and** the Reply store (`getReply?.caller`) — the
reply-half is the recurring blocker.  Precise per-bundle requirements:

**Update (v0.31.173): the establish family — 4 bundles — is DONE (12/15).**
`endpointReceiveDual_preserves_pendingReceiveReplyWellFormed` (the establish) +
`endpointReceiveDualWithCaps` + `endpointReplyRecv` de-threaded, plus reusable reply-store
infrastructure: `replyIdEstablishFresh` predicate + per-step frames, `cleanupPreReceiveDonation_`
/ `endpointQueue{Enqueue,PopHead}_` / `ipcUnwrapCaps_preserves_{reply_objects,pendingReceiveReplyWellFormed}`,
and the `*_tcb_pendingReceiveReply_backward` / `*_preserves_reply` backward/forward frames in
`Core.lean` / `Transport.lean` / `Defs.lean` / `Capability/Operations.lean` / `CapTransfer.lean`.
The establish threads `hReplyIdValid` (replyId present-free-unstashed — the receive syscall's
reply-cap validation) + `hReceiverNotRecv` (the completing receiver is the running thread, not
mid-receive-stash) + uses the existing `hQHBC` conjunct (the popped sendQ head is
`.blockedOnSend`/`.blockedOnCall`, never stashing).  All three are dischargeable pre-state
facts (the D2 precedent).  **3 remain: the `endpointCall` family.**

**Optional structural-symmetry note (NOT a defect; tracked simplification):**
`endpointReceiveDual`'s rendezvous completes the running receiver + woken sender to `.ready`
via `storeTcbIpcStateAndMessage` (keeps the stash field) rather than F-1's
`storeTcbReceiveComplete` (clears it).  This is **correct** — those threads provably carry no
stash (`pendingReceiveReply = none`), so the two helpers yield identical states — and is why
the establish needs `hReceiverNotRecv`/`hQHBC`.  A defensive-symmetry refactor (route those
completions through `storeTcbReceiveComplete`) would let the establish drop those two
preconditions and enforce the no-stash discipline structurally, but it requires re-proving
`endpointReceiveDual`'s full `ipcInvariantFull` suite + cross-core (an F-1-sized slice) for a
behaviour-identical result.  Closure target (low priority): `endpointReceiveDual{,OnCore,WithCaps}`
`.ready`-completion stores → `storeTcbReceiveComplete`.

- **`endpointReceiveDual` (the canonical ESTABLISH)** — no-sender branch writes
  `pendingReceiveReply := replyId`.  Needs precondition
  `hReplyIdValid : ∀ rid, replyId = some rid → (∃ r, st.getReply? rid = some r ∧ r.caller = none)
  ∧ (∀ tid tcb, st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)` (present-free-unstashed),
  plus `cleanupPreReceiveDonation_preserves_pendingReceiveReplyWellFormed`,
  `linkCallerReply_preserves_pendingReceiveReplyWellFormed`, and threading `hReplyIdValid`'s
  "rid stays free & unstashed" through the cleanup→enqueue→store chain.  Keystone
  (`storeObject_establishStash_…`) + queue frames already exist.
- **`endpointReceiveDualWithCaps`, `endpointReplyRecv`** — call `endpointReceiveDual` (blocked
  on the above); WithCaps additionally needs `ipcUnwrapCaps_preserves_…`.
- **`endpointCall`, `endpointCallOnCore`** — server-waiting branch sets the woken server `.ready`
  while its stash is *not cleared until* the final `linkServerStashedReply`; PRR is genuinely
  violated mid-transition, so step-by-step frame composition fails — needs a bespoke end-to-end
  object-diff proof + `hReplyIdValid` for the inner `linkCallerReply`.
- **`endpointSendDualWithCaps`** — wraps `endpointSendDual` (done) + `ipcUnwrapCaps`; only missing
  `ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed` (needs cap-transfer CNode writes at
  `receiverRoot` proven not to clobber a stashed reply slot, `rid.toObjId ≠ receiverRoot`).
- **`endpointCallWithCaps`** — wraps `endpointCall` (blocked) + `ipcUnwrapCaps`.
- **`linkCallerReply`** — below-API helper; needs `linkCallerReply_preserves_…` with an
  `hNotStashed`-for-rid precondition.
- **`lifecycleRetypeObject` {core,composition}** — most tractable: reduces to a single
  `storeObject newObj` (`lifecycleRetypeObject_ok_as_storeObject`), needs only a `newObj`-keyed
  side-condition dispatched across the existing `storeObject_{tcb,reply,nonTcbReply}_preserves_…`
  keystones.  No deep blocker.

----

### Historical record (the finding as surfaced)

**Surfaced by:** the D3 de-threading of `pendingReceiveReplyWellFormed` (v0.31.168
frame family).  Trying to *prove* (rather than thread) that the IPC transitions
establish/preserve the conjunct revealed that **two transitions genuinely violate it**.

**Statement.** `pendingReceiveReplyWellFormed` clause C1 requires every TCB with
`pendingReceiveReply = some rid` to be `.blockedOnReceive`.  A server-first `Recv`
with no waiting sender stashes `replyId` on the now-`.blockedOnReceive` receiver and
enqueues it in the endpoint `receiveQ` (`endpointReceiveDual` no-sender branch,
`Transport.lean:1728‑1746`).  Two transitions then wake such a receiver to `.ready`
via `storeTcbIpcStateAndMessage` **without clearing the stash**, leaving a `.ready`
thread carrying `pendingReceiveReply = some rid` — a C1 violation:

1. **`endpointSendDual`** rendezvous delivery (`Transport.lean:1604`): a plain `Send`
   to a stashing receiver.  (The `endpointReceiveDual` source comment at
   `Transport.lean:1736‑1738` explicitly acknowledges this "woke via `Send`" stale
   stash and relies on a *lazy* clear on the receiver's next `Recv`.)
2. **`notificationSignalBound`** delivery (`NotificationBind.lean:275`): a `Signal` to
   a bound TCB blocked on receive.

This is why the `*_preserves_ipcInvariantFull` bundles **thread** `hPRR'` rather than
prove it: the conjunct is not a true invariant of the kernel as written.

**Severity: Low (model-completeness, *not* an exploitable info-flow channel).**  The
information-flow projection already *erases* `pendingReceiveReply`
(`InformationFlow/Projection.lean:283`, `projectKernelObject_erases_pendingReceiveReply`
at `:402`), so a stale stash is invisible to a low observer — there is no covert
channel.  The impact is purely that `ipcInvariantFull`'s 17th conjunct is not
machine-checked-preserved end-to-end (it is assumed where threaded).

**Remediation (per the implement-the-improvement rule — weakening C1 is forbidden):**
eagerly clear `pendingReceiveReply := none` when a **non-Call** path completes a
receive out of `.blockedOnReceive`:

- `endpointSendDual` rendezvous delivery store, and
- `notificationSignalBound` delivery store.

**Do NOT** clear it globally in `storeTcbIpcStateAndMessage`: the `endpointCall`
rendezvous (`Transport.lean:1797`) delivers to the server with the *same* helper but
then consumes the stash via `linkServerStashedReply` (`State.lean:2434‑2445`,
read at `Transport.lean:1819`) — a global clear makes that link fail closed
`.replyCapInvalid` (verified: it breaks the F1-03 Call/reply trace
`[IMT-011/012/014]`).  The Call path already clears the stash correctly (inside
`linkServerStashedReply`); only the Send and notification paths leak it.

**Closure sequence (the de-threading then proceeds with the v0.31.168 frame family):**
1. Land the eager-stash-clear in `endpointSendDual` + `notificationSignalBound`
   (a dedicated receive-completion store helper), re-proving those two transitions'
   structural / NI / lock-set theorems; verify trace byte-identical.
2. Prove `<tx>_{establishes,preserves}_pendingReceiveReplyWellFormed` for every IPC
   transition using the v0.31.168 keystones (`storeObject_{tcb,reply,nonTcbReply}_…`,
   `establishStash`, `preserveFields`, the store-helper frames).
3. Wire `hPRR'` out of all `*_preserves_ipcInvariantFull` bundles.

Refs: docs/planning/REPLY_OBJECTS_COMPLETION_PLAN.md §#7.4 (origin)
