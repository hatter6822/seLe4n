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
| D3 blockedOnReplyHasTarget + pendingReceiveReplyWellFormed | 🔄 **`blockedOnReplyHasTarget` FULLY DE-THREADED** (v0.31.167): frame family + establishes/preserves for every transition built (v0.31.166), and **all** `ipcInvariantFull` bundles now wired — `hBRT'` removed, the clause established/preserved concretely from `hInv.blockedOnReplyHasTarget`: `endpointCall`/`endpointReceiveDual` (v0.31.166); `endpointSendDual`/`notificationSignal`/`notificationWait`/`endpointReply`/`endpointReplyRecv`/3×WithCaps/`endpointCallOnCore`/2×`lifecycleRetypeObject` (v0.31.167, the retype pair via a `hNewObjTarget` `newObj` side-condition). `consumeCallerReply_preserves_ipcInvariantFull` needs no edit — it derives the clause as the 15th `ipcInvariantCore` conjunct through the `ipcInvariantFull_of_core_replyCallerLinkage` seam. `pendingReceiveReplyWellFormed` ⏳ (next) | v0.31.167 |
| D4 queueNext/HeadBlocked | ⏳ | — |
| D5 blockedThreadTimeoutConsistent | ⏳ | — |
| D6 donationOwnerValid + donationBudgetTransfer + passiveServerIdle | ⏳ | — |
| D7 donationChainAcyclic | ⏳ | — |
| D8 close-out + payoff theorem | ⏳ | — |

Refs: docs/planning/REPLY_OBJECTS_COMPLETION_PLAN.md §#7.4 (origin)
