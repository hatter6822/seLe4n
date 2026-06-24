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
| D1 wiring (4 conjuncts) | 🔄 **3/4 conjuncts de-threaded from 7 bundles (v0.32.28)** — the freshness side-conditions (`hFresh*`/`*TailFresh`) the wiring conjuncts need are **already present** in every enqueue bundle (added for the D4 qNBC/tail-blocked de-thread), so wiring is pure establisher-call substitution. `dualQueueSystemInvariant` / `endpointQueueNoDup` / `ipcStateQueueMembershipConsistent` now **established** from the pre-state in the 7 bundles whose establishers are reachable from `DualQueueMembership`: the 3 base transitions (`endpointSendDual`/`endpointCall`/`endpointReceiveDual`), `notificationSignal`, `notificationWait`, `endpointReply`, `endpointReplyRecv` (the latter three already established `dualQueueSystemInvariant`; this slice adds NoDup+QMC). **Remaining D1 work** (separate slice): (a) `waitingThreadsPendingMessageNone` — its transition establishers live in `PerOperation` (downstream of the bundles), so it stays threaded pending either an establisher relocation upstream or discharge at the D8 layer; (b) the 3 `*WithCaps` bundles + cross-core `endpointCallOnCore` need their D1 establishers **built** (compose the base establisher with new `ipcUnwrapCaps_preserves_{endpointQueueNoDup,ipcStateQueueMembershipConsistent}` frames; the `dualQueue` WithCaps establishers + `ipcUnwrapCaps_preserves_dualQueueSystemInvariant` exist but in `PerOperation`, needing the same upstream relocation). | v0.32.28 |
| D2 replyCallerLinkage (third clause) + consumer | ✅ **LANDED (all 3 establish cases)**: consumer (v0.31.157), full frame family incl. `endpointQueuePopHead`/`endpointQueueEnqueue` frames + `linkCallerReply`/`linkServerStashedReply`/`cleanupPreReceiveDonation` establishes + `wakeThread_…_of_ready` (per-core); single-core `endpointCall`/`endpointReceiveDual_establishes_…` (v0.31.159) **and** per-core `endpointCallOnCore_establishes_…` (v0.31.160); **all 3 bundle theorems that can introduce `.blockedOnReply` de-threaded** (thread `replyCallerLinkageReciprocal st'`, establish the third clause). Preserve-only bundles de-threaded: `endpointSendDual` (v0.31.161); `notificationSignal`/`notificationWait` (v0.31.162); `endpointReply` + `endpointReplyRecv` (v0.31.163); the **3 WithCaps** (v0.31.164) via a new cap-transfer frame chain (`ipcTransferSingleCap_ok_implies_cnode_at_root` → `ipcUnwrapCapsLoop_objects_at_root_orig_or_cnode` → `ipcUnwrapCaps_objects_at_root_orig_or_cnode` → `ipcUnwrapCaps_tcb_backward` → `ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject`; the WithCaps reuse the base establishes/preserve + this frame). **ALL IPC bundles de-threaded.** Only `consumeCallerReply` deliberately stays threaded — it clears a caller's `replyObject` **without** unblocking, so it cannot establish the third clause standalone (re-established by the fused reply transition). Reciprocal-half de-thread (optional). | v0.31.164 |
| D2′ lifecycle/retype third clause | ✅ **LANDED v0.31.165**: `lifecycleRetypeObject_preserves_blockedOnReplyHasReplyObject` (retype writes only `target`; every other slot framed, the `target` obligation discharged by a clean `newObj` well-formedness side-condition `hNewObjThird`, analogous to the bundle's existing CNode/notification `newObj` constraints). Both `lifecycleRetypeObject_preserves_{coreIpcInvariantBundle,lifecycleCompositionInvariantBundle}` de-threaded in place. **Every bundle whose third clause is sound to establish/preserve is now de-threaded; only `consumeCallerReply` stays threaded (cannot establish standalone).** | v0.31.165 |
| D3 blockedOnReplyHasTarget + pendingReceiveReplyWellFormed | 🔄 **`blockedOnReplyHasTarget` FULLY DE-THREADED** (v0.31.167): frame family + establishes/preserves for every transition built (v0.31.166), and **all** `ipcInvariantFull` bundles now wired — `hBRT'` removed, the clause established/preserved concretely from `hInv.blockedOnReplyHasTarget`: `endpointCall`/`endpointReceiveDual` (v0.31.166); `endpointSendDual`/`notificationSignal`/`notificationWait`/`endpointReply`/`endpointReplyRecv`/3×WithCaps/`endpointCallOnCore`/2×`lifecycleRetypeObject` (v0.31.167, the retype pair via a `hNewObjTarget` `newObj` side-condition). `consumeCallerReply_preserves_ipcInvariantFull` needs no edit — it derives the clause as the 15th `ipcInvariantCore` conjunct through the `ipcInvariantFull_of_core_replyCallerLinkage` seam. **`pendingReceiveReplyWellFormed` frame family LANDED (v0.31.168)**: 3 store-kind keystones (tcb/reply/non-tcb-reply; coincident-slot kind-disjointness `.reply`≠`.tcb` frames cross-kind lookups without a kind-stability invariant) + `establishStash` + `preserveFields` + `storeTcbIpcState{,AndMessage}`/`storeTcbQueueLinks`/`consumeReply`/`linkReply` store frames. **Finding F-1 (the kernel-semantics blocker) ✅ REMEDIATED (v0.31.170)**: eager stash-clear (`storeTcbReceiveComplete`) makes `pendingReceiveReplyWellFormed` a true invariant of `endpointSendDual`/`notificationSignalBound{,OnCore}`; 20 mirror frames carry their proofs. **✅ DE-THREADING COMPLETE: 15/15 bundles (v0.31.171 → v0.31.174)** — `grep "hPRR' : pendingReceiveReplyWellFormed st'"` is now empty. The v0.31.174 final slice closed the `endpointCall` family: `linkServerStashedReply_preserves_pendingReceiveReplyWellFormed` (the net-effect crux — the deliver-keeps-stash ≫ link-clears-stash composite, proven via C2-uniqueness: the server is the sole staser of `rid`, so clearing it leaves `rid` unstashed and linking it to the caller is C1-safe), `endpointCall` (threads dischargeable `hCallerNotRecv`), `endpointCallOnCore`, `endpointSendDualWithCaps`, `endpointCallWithCaps`. **Earlier progress: 12/15 (v0.31.171 → v0.31.173)** — `endpointReply`, `consumeCallerReply`, `notificationSignal` (`notificationWaiterConsistent st`), `notificationWait`/`endpointSendDual` (`hWaiterNotRecv`/`hSenderNotRecv`), `linkCallerReply` (`hNotStashed`), the `lifecycleRetypeObject` pair (`hNewObjNoStash`+`hTargetNotStashedReply`), **+ v0.31.173** the `endpointReceiveDual` establish family (`endpointReceiveDual`+`endpointReceiveDualWithCaps`+`endpointReplyRecv`; `hReplyIdValid`+`hReceiverNotRecv`+`hQHBC`) + reusable reply-store infrastructure. **3 bundles remain (the `endpointCall` family)** (precise per-bundle blockers in the "D3 remaining" note below): the `endpointReceiveDual` ESTABLISH (needs `hReplyIdValid` present-free-unstashed + `cleanupPreReceiveDonation`/`linkCallerReply` reply-half frames), `endpointCall` (mid-transition stash window before `linkServerStashedReply` — needs end-to-end object-diff proof), the WithCaps (`ipcUnwrapCaps_preserves_…` reply-slot-disjointness), `linkCallerReply`, and the tractable `lifecycleRetypeObject` pair. | v0.31.168 → F-1 v0.31.170 → 5/15 v0.31.171 |
| D4 queueNext/HeadBlocked | 🔄 **qNBC ✅ FULLY DE-THREADED (v0.32.22)** + **tail-blocked (`hEQTB'`) ✅ FULLY DE-THREADED (v0.32.27)** — `queueNextBlockingConsistent` removed from **every** `ipcInvariantFull` bundle (zero `hQNBC'` threading sites): the 5 clean bundles (v0.31.175) + the 8 enqueue-style transitions unblocked by the Finding F-2 tail-blocked conjunct (`endpointSendDual` v0.32.17, `endpointCall` v0.32.18, `endpointReceiveDual` v0.32.19, 3×WithCaps v0.32.20, `endpointReplyRecv` v0.32.21, cross-core `endpointCallOnCore` v0.32.22) via cores (a)+(b). **`endpointQueueTailBlockedConsistent` now likewise removed from every bundle (zero `hEQTB'` threading sites, v0.32.23→27)**: the 3 base transitions (`endpointSendDual`/`endpointCall`/`endpointReceiveDual` v0.32.23–26) + (v0.32.27) `endpointReplyRecv`, 3×WithCaps, cross-core `endpointCallOnCore`, and `notificationWait` (the running waiter is `.ready` ⇒ no endpoint tail, so a fresh `notificationWait_preserves_endpointQueueTailBlockedConsistent` establishes it) via cores (a)+(c). **`queueHeadBlockedConsistent` (`hQHBC'`) + `queueNextTargetBlocked` (`hQNTB'`) NOW BOTH FULLY DE-THREADED (Slice 2c, v0.32.40→45)** — zero `hQHBC'`/`hQNTB'` threading sites anywhere (single-core 9 bundles + cross-core `endpointCallOnCore`). qHBC: pop core blocked-via-qNTB + enqueue keystones + no-head ready/blockedOnReply stores; qNTB (the 20th conjunct, strict link-target): the no-blocked-incoming store discipline + the fused enqueue+block-store keystone + cross-core wake (object-lookup-invisible). The call/notification/reply-recv bundles gain the dischargeable readiness preconditions (`hCallerReady`/`hReceiverReady`/`hWaiterReady`, supplied at D8). | v0.32.45 |
| **F-2 prereq: tail-blocked invariant (reachable→blocked, tail specialisation)** | 🔄 **SLICE 1 LANDED (v0.32.11)** — `endpointQueueTailBlockedConsistent` added as the **19th `ipcInvariantFull` conjunct** (def mirrors `queueHeadBlockedConsistent` for the queue **tail**; the minimal reachable→blocked fact the enqueue-style transitions need, since `endpointQueueEnqueue` links the **old tail**'s `queueNext` to the freshly-enqueued thread, so post-state `queueNextBlockingConsistent` needs the old tail blocked-on-the-same-endpoint — confirmed *not* derivable from the existing 18 conjuncts: `intrusiveQueueWellFormed` asserts the tail exists with `queueNext = none` but **not** that it is blocked, and there is no head→tail reachability lemma). **Preservation frame family** built (`QueueNextBlocking.lean`): the `_of_endpoint_tcb_backward` combinator + `ensureRunnable`/`removeRunnable`/`storeObject_{nonEndpointNonTcb,tcb_preserveIpc}`/`storeTcbIpcState{,AndMessage}`/`storeTcbPendingMessage` `_preserves_endpointQueueTailBlockedConsistent` (head→tail duals) + `endpointQueueTailBlockedConsistent_of_objects_eq`. **Established** (full preservation) for all root/frame producers: `default` + the 3 arch object-frames (`Architecture/Invariant.lean`) + `boot` (vacuous — empty queues) + per-core + the reply-mutators. **Threaded** `hEQTB'` for the endpoint-queue-touching transitions (the 8 D4-residual + the queue bundles), pending the Slice-2 enqueue-establish.  All 19 producers wired; full build + `test_full` green; `RAW_LOOKUP_TID` re-anchored 1131→1135. **SLICE 2a LANDED (v0.32.12)** — de-threaded `hEQTB'` from the 5 transitions that **touch no endpoint queue**, so they *establish* the tail-blocked conjunct from the pre-state instead of threading it: `notificationSignal` (woken head waiter is `.blockedOnNotification` via `hNWC` ⇒ no endpoint tail) + `endpointReply` (the unblocked `target` was `.blockedOnReply` ⇒ no endpoint tail) + `consumeCallerReply`/`linkCallerReply` (reply-object store + `replyObject` write — neither touches a queue or any `ipcState`; the former reads the conjunct off the pre-state `hInv`, the latter takes a `hTailPre` pre-state precondition as it carries only `ipcInvariantCore`) + the `lifecycleRetypeObject` pair (`hTargetNotTail` — the tail dual of the existing `hTargetNotHead`; a retype never creates an endpoint nor writes an endpoint tail). New establishers: the reply-mutator family (`storeObject_reply`/`consumeReply`/`linkReply`/`linkCallerReply`/`consumeCallerReply` `_preserves_endpointQueueTailBlockedConsistent`, relocated ahead of the reply bundles) + `lifecycleRetypeObject_preserves_endpointQueueTailBlockedConsistent`. `RAW_LOOKUP_TID` re-anchored 1135→1139 (retype establisher raw lookups). **SLICE 2b FOUNDATION LANDED (v0.32.13)** — the reusable queue-boundary store frames the enqueue/pop transition establishers compose over: `storeTcbQueueLinks_preserves_{queueHeadBlockedConsistent,endpointQueueTailBlockedConsistent}` (link-only writes preserve every endpoint + every `ipcState`, so both follow from the `_of_endpoint_tcb_backward` combinator + `storeTcbQueueLinks_{endpoint,tcb_ipcState}_backward`) and `storeObject_endpoint_preserves_{queueHeadBlockedConsistent,endpointQueueTailBlockedConsistent}` (an endpoint store changes only the queue-boundary fields, discharged by a caller-supplied `hNewHeads`/`hNewTails` obligation on the new endpoint's head/tail). **Scope correction (Slice 2b vs 2c — analysis-grounded):** the tail specialisation de-threads **`queueNextBlockingConsistent`** from the 8 (the enqueue link `oldTail.queueNext := tid` matches because the old tail is `.blockedOnSend`/`.blockedOnCall` by pre-state tail-blocked, and the pop leg already preserves qNBC via `endpointQueuePopHead_preserves_queueNextBlockingConsistent`) **and self-establishes `endpointQueueTailBlockedConsistent`** (the new sendQ tail is the freshly-blocked sender; the pop leaves the receiveQ tail unchanged or empties it). It does **not** de-thread **`queueHeadBlockedConsistent`** for the pop (rendezvous) leg: after popping the head, the new head is the old *second* element, whose blockedness is **not** derivable from the 19 conjuncts (`queueNextBlockingMatch (.blockedOnReceive _) .ready = True` via the catch-all, so qNBC does not force it; `ipcStateQueueMembershipConsistent` is the blocked→reachable converse; `intrusiveQueueWellFormed` constrains only head/tail). This is the **full** `endpointQueueMemberBlocked` (reachable→blocked for *every* member) that **Finding F-2** identifies as the eventual remediation — the tail specialisation is the partial step sufficient for qNBC. **Slice 2b (next): build `endpointQueuePopHead`/transition-level tail-blocked + qNBC establishers, de-thread qNBC + `hEQTB'` from the 8** (qHBC stays threaded). **Slice 2c: add `endpointQueueMemberBlocked`, de-thread qHBC.** | v0.32.13 |
| D5 blockedThreadTimeoutConsistent | ✅ **DE-THREADED (v0.32.10)** — see detailed row below | v0.32.10 |
| D6 donationOwnerValid + donationBudgetTransfer + passiveServerIdle | 🔄 see detailed row below | — |
| D7 donationChainAcyclic | ✅ **DE-THREADED (v0.31.176): all 13 bundles** via `donationOwnerValid_implies_donationChainAcyclic st' hDOV'` (derives from the still-threaded `hDOV'`); `grep hDCA'` empty | v0.31.176 |
| D5 blockedThreadTimeoutConsistent | ✅ **FULLY DE-THREADED (13/13 bundles, v0.32.10)** — `grep "hBlockedTimeout' : blockedThreadTimeoutConsistent st'"` is now empty; all 13 bundles carry the single uniform dischargeable precondition `hAllBudgetsNone : allTimeoutBudgetsNone st`. **Approach (key insight)**: no IPC transition ever writes `timeoutBudget := some` (every TCB store omits/zeroes the field), so the system in fact maintains the *stronger* `allTimeoutBudgetsNone` discipline — every thread carries no timeout budget. A state with all budgets `none` satisfies the seL4-faithful `blockedThreadTimeoutConsistent` (budget ⇒ blocking IPC state) **vacuously** (`blockedThreadTimeoutConsistent_of_all_none`). So instead of per-transition per-woken-thread `⟨woken⟩.timeoutBudget = none` side-conditions (which a rendezvous-partner queue-head would force into an awkward phrasing, and which are *only* dischargeable from the global all-none fact anyway), every bundle takes one global `allTimeoutBudgetsNone st` precondition and establishes the conjunct uniformly. **Infrastructure**: `allTimeoutBudgetsNone` def + `timeoutBudgetFrame` (budget-preservation: every post-state TCB pulls back to a pre-state TCB with equal `timeoutBudget`, parallel to `sameSchedContextBindings`) with `refl`/`trans`/`of_objects_eq` + `allTimeoutBudgetsNone_of_frame` + `blockedThreadTimeoutConsistent_of_frame` (frame + pre-state all-none ⇒ post-state consistent). Store-op family (zero per-thread side-conditions — every store satisfies budget-preservation by `rfl`): `storeObject_{modifiedTcb,nonTcb}` / `storeTcbIpcState{,_fromTcb,AndMessage}` / `storeTcbReceiveComplete` / `storeTcbQueueLinks` / `storeObject_endpoint'` / `endpointQueue{PopHead,Enqueue}` / `linkReply` / `linkCallerReply` / `linkServerStashedReply` / `cleanupPreReceiveDonation` (via the new `returnDonatedSchedContext_tcb_timeoutBudget_backward`, mirror of `_ipcState_replyObject_backward`) / `ipcUnwrapCaps` / `wakeThread_…_of_ready` `_timeoutBudgetFrame`. Per-transition frames (`endpointSendDual` / `endpointCall` / `endpointReceiveDual` / `endpointReply` / `endpointReplyRecv` / 3×WithCaps / `endpointCallOnCore` / notification pair) mirror their `passiveServerIdle` decomposition but **carry no precondition** (scheduler ops → `of_objects_eq`). Retype pair via `lifecycleRetypeObject_preserves_blockedThreadTimeoutConsistent` (the fresh-TCB slot discharged by a `hNewObjNoBudget` side-condition — a retyped TCB carries no budget). **D8 note**: the global `allTimeoutBudgetsNone st` precondition is dischargeable at the payoff level from a reachability invariant (no transition ever sets a budget) — it is *not* implied by `ipcInvariantFull` alone, so it surfaces as one extra dischargeable hypothesis, exactly as the per-thread variant would. | v0.32.10 |
| D6 donationOwnerValid + donationBudgetTransfer + passiveServerIdle | 🔄 **IN PROGRESS (UNBLOCKED by Finding F-3)** — **`donationBudgetTransfer` ✅ FULLY DE-THREADED (13/13 bundles, v0.31.182)**: `grep "hDBT' : donationBudgetTransfer st'"` is now empty — the **first conjunct established entirely from the pre-state** (D7's `donationChainAcyclic` is derived from the still-threaded `hDOV'`; this one stands alone). The v0.31.182 final slice closed the last 4: the 3 binding-**touching** receive-family bundles (`endpointReceiveDual` / `endpointReceiveDualWithCaps` / `endpointReplyRecv`) via `cleanupPreReceiveDonation_preserves_donationBudgetTransfer` (the pre-receive donation-return moves the SchedContext server→owner, keeping it singly-held — *not* `sameSchedContextBindings`, so it needs the dedicated preservation argument: `returnDonatedSchedContext_tcb_schedContextBinding_backward` gives the 3-way post-state binding shape [server→`.unbound`, owner→`.bound scId`, else framed], `returnDonatedSchedContext_preserves_donationBudgetTransfer` shows no new scId-sharing pair arises); **+ `endpointCallOnCore`** (cross-core) via `endpointCallOnCore_sameSchedContextBindings` (mirror of the single-core frame in `IPC/CrossCore/` — `wakeThread`/`removeRunnableOnCore` are scheduler-only writes, so the cross-core call leaves every TCB's `schedContextBinding` byte-identical; `wakeThread_sameSchedContextBindings_of_ready` is the new keystone). Earlier **(9/13, v0.31.181)**: + the 2 `lifecycleRetypeObject` bundles (`coreIpcInvariantBundle` + `lifecycleCompositionInvariantBundle`) via `lifecycleRetypeObject_preserves_donationBudgetTransfer` (a `newObj`-`.unbound` side-condition `hNewObjUnbound` — a fresh retyped TCB holds no SchedContext, so it cannot share an scId; every other slot frames from the pre-state). Earlier **(7/13, v0.31.180)**: + `endpointCall`, `endpointSendDualWithCaps`, `endpointCallWithCaps` via the link-helper family (`linkReply` / `linkCallerReply` / `linkServerStashedReply` `_sameSchedContextBindings` + `linkReply_preserves_objects_invExt`) and `ipcUnwrapCaps_sameSchedContextBindings` (one-liner off `ipcUnwrapCaps_tcb_backward` — cap transfer leaves every TCB slot byte-identical). **All 7 binding-free single-core transitions done.** Earlier **(4/13, v0.31.179)**: reusable `sameSchedContextBindings` frame (`donationBudgetTransfer_of_sameSchedContextBindings` + the store-op family `storeObject_{modifiedTcb,nonTcb}` / `storeTcbIpcState{,_fromTcb,AndMessage}` / `storeTcbReceiveComplete` / `storeTcbQueueLinks` / `storeObject_endpoint'` / `endpointQueue{PopHead,Enqueue}` `_sameSchedContextBindings` + `of_objects_eq`) de-threads `hDBT'` from `notificationWait` / `notificationSignal` / `endpointReply` (v0.31.178) **+ `endpointSendDual`** (v0.31.179). The binding-free transitions establish the conjunct by the frame; core IPC transitions never write a `schedContextBinding`. **`donationOwnerValid` IN PROGRESS (11/13 bundles, v0.32.1)**: **v0.32.1**: + the receive family (`endpointReceiveDual` + `endpointReceiveDualWithCaps`) via `endpointReceiveDual_preserves_donationOwnerValid` — the rendezvous sender is the sendQ **head** (`.blockedOnSend`/`.blockedOnCall` by `hQHBC`, never a `.blockedOnReply` owner) and the running receiver is `.ready` (dischargeable `hReceiverReady`, which both supplies the receiver-store's `hPreNotReply` and rules out the Call-leg corner where the receiver = dequeued sender so the receiver-store would overwrite a just-set `.blockedOnReply`); the blocking branch returns the receiver's *own* donation via `cleanupPreReceiveDonation_preserves_donationOwnerValid` (sound by the `donationOwnerUnique` 18th conjunct). The WithCaps composes the base establish with `ipcUnwrapCaps_donationOwnerFrame`. Both receive bundles drop `hDOV'` (add dischargeable `hReceiverReady`); `RAW_LOOKUP_TID` re-anchored 1071→1083 (invariant-frame raw lookups in the new establishers). Earlier **(9/13, v0.31.188)**: + the 2 clean WithCaps (`endpointSendDualWithCaps` + `endpointCallWithCaps`) via `ipcUnwrapCaps_donationOwnerFrame` — `ipcUnwrapCaps` writes only CNode caps at `receiverRoot`, so every SchedContext (new `ipcUnwrapCaps_preserves_schedContext_objects` chain: `ipcTransferSingleCap` → `ipcUnwrapCapsLoop` → `ipcUnwrapCaps`, mirroring the existing `_preserves_tcb_objects` — a SchedContext at `receiverRoot` makes `getCNode?` return `none`, contradicting the transfer's `.ok`) and every TCB (`ipcUnwrapCaps_preserves_tcb_objects`) survives byte-identical; the WithCaps frames compose the base `endpointSendDual`/`endpointCall` `_donationOwnerFrame` with the cap-transfer frame, threading the base's `hQHBC`/`hSenderNotReply`/`hCallerNotReply`. Earlier **(7/13, v0.31.187)**: + `endpointCallOnCore` (cross-core) via `endpointCallOnCore_donationOwnerFrame` — the cross-core mirror of `endpointCall` (per-core `wakeThread` [+ `wakeThread_donationOwnerFrame_of_ready` — the woken thread is `.ready`, so the object map is element-wise unchanged] / `removeRunnableOnCore` in place of `ensureRunnable`/`removeRunnable`); the bundle de-threads `hDOV'` after `subst hStep` via `donationOwnerValid_of_frames`. **The call path (single-core + cross-core) is now fully de-threaded for `donationOwnerValid`.** Earlier **(6/13, v0.31.186)**: + `endpointCall` via `endpointCall_donationOwnerFrame` — the rendezvous receiver (receiveQ head) is `.blockedOnReceive` (`hQHBC`) and the caller is running (dischargeable `hCallerNotReply`); the caller is *set* `.blockedOnReply` but was not one before, so no existing owner witness is lost. New forward link-helper frames `linkReply`/`linkCallerReply`/`linkServerStashedReply` `_donationOwnerFrame` (reply-object store + `ipcState`/binding-preserving TCB writes) carry the reply-link leg; the caller-store pre-state is discharged via `storeTcbIpcStateAndMessage_ipcState_eq` (caller=receiver) / `_preserves_objects_ne` + `endpointQueuePopHead_tcb_ipcState_backward` (caller≠receiver). Earlier **(5/13, v0.31.185)**: + the 2 `lifecycleRetypeObject` bundles (`coreIpcInvariantBundle` + `lifecycleCompositionInvariantBundle`) via `lifecycleRetypeObject_preserves_donationOwnerValid` — the retype reduces to a single `storeObject target newObj`, so `donationOwnerValid_of_frames` does *not* apply (retype can create a fresh TCB binding, breaking the backward `sameSchedContextBindings`); the direct proof handles the retype slot via `hNewObjUnbound` (a fresh TCB is `.unbound`, never `.donated`) and two dischargeable target-slot side-conditions (`hTargetNotSc`/`hTargetNotOwner` — the retyped slot is untyped/freed memory, not a live SchedContext or `.blockedOnReply` owner). Earlier **(3/13, v0.31.184)**: reusable forward-frame `donationOwnerFrame` (packaged `scForward` + `ownerForward` with `refl`/`trans`/`of_objects_eq`) + `donationOwnerValid_of_frames` (backward `sameSchedContextBindings` + forward `donationOwnerFrame`) + the store-op family — `storeObject_oldNonScNonTcb` / `storeObject_modifiedTcb` / `storeTcbIpcState{,_fromTcb,AndMessage}` / `storeTcbReceiveComplete` `_donationOwnerFrame` (a TCB store frames the owner side iff its pre-state `ipcState ≠ .blockedOnReply`), **plus** the ipcState+binding-preserving rewrites `storeObject_modifiedTcbPreservingOwner` / `storeTcbQueueLinks` / `endpointQueuePopHead` / `endpointQueueEnqueue` `_donationOwnerFrame` (queue-link rewrites preserve owner witnesses *unconditionally* — even a `.blockedOnReply` owner — since `tcbWithQueueLinks` touches only link fields). **v0.31.184**: + `endpointSendDual` via `endpointSendDual_donationOwnerFrame` — the rendezvous receiver (receiveQ head) is `.blockedOnReceive` by `hInv.queueHeadBlockedConsistent`, the block-path sender is the running caller (dischargeable `hSenderNotReply`); neither is a `.blockedOnReply` owner. Earlier **(2/13, v0.31.183)**: `notificationWait` (dischargeable `hWaiterNotReply`) + `notificationSignal` (woken head waiter `.blockedOnNotification` via `hNWC : notificationWaiterConsistent`). **Architectural note (binding the remaining 10)**: the bare `endpointReply`/`endpointReplyRecv` transitions *wake the `.blockedOnReply` donation owner* without returning the donation (the donation-return lives in the `*WithDonation` wrappers via `applyReplyDonation`), so they do **not** preserve `donationOwnerValid` at the bare level — de-threading those must compose at the donation-wrapper level. The receive family (`endpointReceiveDual{,WithCaps}`, `endpointReplyRecv`) additionally returns a donation via `cleanupPreReceiveDonation` (binding change → not `sameSchedContextBindings`-clean), needing the dedicated donation-return argument. **Remaining `donationOwnerValid` (2 bundles — the owner-waking reply family, D8/composite-only)**: `endpointReply`/`endpointReplyRecv` (wake the `.blockedOnReply` owner → composite `*WithDonation` treatment with `applyReplyDonation`; the bare transitions genuinely do not preserve `donationOwnerValid` — the donation-return is what restores it, so these stay threaded `hDOV'` until the donation-wrapper level). **`passiveServerIdle` ✅ FULLY DE-THREADED (13/13 bundles, v0.32.9)** — `grep "hPSI' : passiveServerIdle st'"` is now empty: reusable scheduler-aware frame `passiveServerIdleFrame` (the pullback only fires for **unbound + descheduled + not-yet-allowed** threads — i.e. those a transition would newly drive `.blockedOnSend`/`.blockedOnCall` while descheduled; the running sender/caller is excluded by holding a SchedContext, every blocked-into-an-allowed-state or woken-`.ready` thread by the `passiveServerIdleAllowed` filter, so the obligation only ever lands on untouched threads) + `passiveServerIdle_of_frame` + the micro-frame family (`storeObject_oldNonTcb`/`storeObject_modifiedTcb`/`storeTcbIpcState{,_fromTcb,AndMessage}` `_passiveServerIdleFrame` [bound-or-allowed side-condition], `ensureRunnable_passiveServerIdleFrame` [only adds to the run queue → clean], `removeRunnable_passiveServerIdleFrame` [removed thread bound-or-allowed]) leveraging the existing `removeRunnable_mem`/`ensureRunnable_mem_old`/`*_scheduler_current` scheduler lemmas. **v0.32.2**: + the notification pair (`notificationWait` woken-`.ready`/blocked-`.blockedOnNotification`, `notificationSignal` woken-`.ready` head waiter) — both drop `hPSI'`, no new precondition (the touched waiter is always in an allowed passive state). **v0.32.3**: + `endpointSendDual` via `endpointSendDual_passiveServerIdleFrame` — the rendezvous receiver is completed `.ready` + rescheduled (clean), the block-path sender is set `.blockedOnSend` + descheduled (a *non-allowed* state) so it carries the dischargeable `hSenderNotUnbound` (a running sender holds its own or a donated SchedContext); + the reusable queue micro-frames `endpointQueue{PopHead,Enqueue}_passiveServerIdleFrame` (via `passiveServerIdleFrame_of_backward` — `ipcState`+binding backward + scheduler-eq) and `storeTcbReceiveComplete_passiveServerIdleFrame`. **v0.32.4**: + `endpointReply` via `endpointReply_passiveServerIdleFrame` — it unblocks the reply target `.ready` (allowed) + reschedules, descheduling nothing; clean (no precondition), reuses the store + `ensureRunnable` frames (the bundle keeps `hDOV'` threaded — bare `endpointReply` is composite-only for `donationOwnerValid`). **v0.32.5**: + `endpointCall` via `endpointCall_passiveServerIdleFrame` — rendezvous completes the receiver `.ready` + sets the caller `.blockedOnReply` (allowed) + stashes the reply (new `linkServerStashedReply_passiveServerIdleFrame` + `linkCallerReply_passiveServerIdleFrame`, both clean via `passiveServerIdleFrame_of_backward`); the block path sets the caller `.blockedOnCall` (non-allowed) + deschedules, carrying the dischargeable `hCallerNotUnbound`. **v0.32.6**: + the send/call `*WithCaps` (`endpointSendDualWithCaps` + `endpointCallWithCaps`) via `ipcUnwrapCaps_passiveServerIdleFrame` (cap transfer writes only CNode caps → every TCB byte-identical via `ipcUnwrapCaps_tcb_backward`, scheduler untouched) composed with the base frame, threading the base `hSenderNotUnbound`/`hCallerNotUnbound`. **v0.32.7**: + the receive family (`endpointReceiveDual` + `endpointReceiveDualWithCaps` + `endpointReplyRecv`) — *clean* (every rewritten thread lands in an allowed passive state: receiver `.blockedOnReceive`, rendezvous sender `.ready`/`.blockedOnReply`, reply target `.ready`), so no "blocker" precondition; they reuse the already-threaded `hReceiverReady` (the running receiver is `.ready`). The keystone is `cleanupPreReceiveDonation_passiveServerIdleFrame` (the donation-return rebinds the owner `.unbound → .bound` and the receiver `.donated → .unbound` — the pullback excludes the owner [now **bound**] and the receiver [**allowed** `.ready`], framing every other thread via the 3-way `returnDonatedSchedContext` binding lemma). **v0.32.8**: + the 2 `lifecycleRetypeObject` retype bundles (`coreIpcInvariantBundle` + `lifecycleCompositionInvariantBundle`) via `lifecycleRetypeObject_preserves_passiveServerIdle` — the retype reduces to a single `storeObject target newObj` (scheduler-untouched); the retype slot is a fresh allowed-state TCB (`hNewObjAllowed`, dischargeable: a retyped TCB is `.ready`), every other slot frames from the pre-state. **v0.32.9**: + `endpointCallOnCore` (cross-core) via `endpointCallOnCore_passiveServerIdleFrame` — the per-core mirror of the single-core call frame: `wakeThread` (= `enqueueRunnableOnCore`) only *adds* to a run queue and preserves every core's current (clean, no exclusion — even the woken thread pulls back); `removeRunnableOnCore` on `executingCore` frames the bootCore queue/current by per-core locality (`removeRunnableOnCore_runQueueOnCore_{self,ne}` — case-split on `executingCore = bootCoreId`), carrying the dischargeable `hCallerNotUnbound`. The file-header architectural note (which previously called `passiveServerIdle` a "genuinely scheduler-sensitive" carried hypothesis) is updated. **Remaining D6**: `donationOwnerValid` (2 reply bundles, composite-only — the bare reply transitions wake the `.blockedOnReply` owner without returning the donation; restored at the `*WithDonation` layer). | v0.32.9 |
| **D6 prereq: `donationOwnerUnique` (18th `ipcInvariantFull` conjunct)** | ✅ **ADDED (v0.31.189)** — no two distinct threads name the same `owner` in a `.donated _ owner` binding.  Established across all 13 bundles + retype + cross-core + default + boot + arch object-frames (preserved by `sameSchedContextBindings` injection / donation-return removal / fresh-retype / object-eq).  **Unblocks** `cleanupPreReceiveDonation_preserves_donationOwnerValid` (proven) → the receive-family `donationOwnerValid` de-thread (`endpointReceiveDual{,WithCaps}`).  The `endpointReply`/`endpointReplyRecv` pair remains composite-only (bare wakes the owner without the return). | v0.31.189 |
| D8 close-out + payoff theorem | ⏳ **PER-TRANSITION INFRASTRUCTURE COMPLETE; remaining work is the dispatch integration.** After Slice 2c (v0.32.45) every IPC transition establishes all *structurally-establishable* conjuncts. The remaining threaded hypotheses are **not** per-transition de-threads — they are either (i) **dischargeable reachability preconditions** (`hCallerReady`/`hReceiverReady`/`hWaiterReady`/`allTimeoutBudgetsNone`/`*NotReply`/`*NotUnbound`/freshness — properties of the running syscall thread, supplied by a reachability bundle); (ii) **genuine composites** correctly threaded at the bare level and restored at the dispatch/consume layer — `replyCallerLinkageReciprocal` (bare `endpointReply` wakes the caller `.blockedOnReply→.ready` but `consumeCallerReply` clears `Reply.caller`) and `donationOwnerValid` for the 2 reply bundles (bare reply wakes the owner; `applyReplyDonation` returns the donation); or (iii) **`waitingThreadsPendingMessageNone`** (genuinely per-transition, establishers exist in `PerOperation` downstream — relocatable, but the plan's intended path is D8-layer discharge). **D8 payoff scope**: `dispatchWithCap_preserves_ipcInvariantFull` composes, per IPC arm, the cross-core dispatch wrappers (`endpointSendDualWithCaps`+`clearWokenReceiverStash`, `endpointReceiveDualOnCore`, `endpointCallCrossCoreDispatch`, `endpointReplyCrossCoreDispatch`+`consumeCallerReply`) — each needs a `_preserves_ipcInvariantFull` built over the now-de-threaded per-transition bundle — plus object-frame preservation for every capability/cspace arm + `dispatchCapabilityOnly`, all gated by the reachability bundle. Large multi-slice integration; the per-transition establishers it consumes are all in place. | — |

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

### Slice 2b/2c implementation decomposition (precise residual map)

The tail-blocked foundation (v0.32.13–14) is in place: `storeTcbQueueLinks` / `storeObject_endpoint`
boundary frames for both qHBC and tail-blocked, the `endpointQueuePopHead` tail-blocked frame, and
(v0.32.15) the `storeTcbReceiveComplete` tail-blocked frame (rendezvous receiver, `hNotTail`-gated).
What remains, per invariant:

- **Slice 2b — qNBC + `hEQTB'` de-thread (8 transitions, achievable now).** Each transition
  `T ∈ {endpointSendDual, endpointCall, endpointReceiveDual, endpointReplyRecv, 3×WithCaps,
  endpointCallOnCore}` needs `T_preserves_{queueNextBlockingConsistent, endpointQueueTailBlockedConsistent}`,
  then the bundle drops `hQNBC'`/`hEQTB'` (keeps `hQHBC'`). Branch structure:
  - **qNBC half — ✅ COMPLETE (v0.32.16–22).** Cores (a)+(b) built (v0.32.15–16); all 8
    `T_preserves_queueNextBlockingConsistent` establishers landed (`endpointSendDual` v0.32.17,
    `endpointCall` v0.32.18, `endpointReceiveDual` v0.32.19, the 3 WithCaps wrappers v0.32.20,
    `endpointReplyRecv` v0.32.21, cross-core `endpointCallOnCore` v0.32.22) and every bundle has
    dropped `hQNBC'` — **zero remaining `hQNBC'` threading sites**.
  - **`hEQTB'` half — ✅ COMPLETE (v0.32.23–27).** The reusable cores:
    **core (c)** `endpointQueueEnqueue_blockStore_establishes_endpointQueueTailBlockedConsistent`
    (block branch: the freshly-enqueued+blocked thread is the new tail) + `endpointQueueEnqueue_enqueued_is_tail`
    + the `storeTcbIpcState` variant `endpointQueueEnqueue_blockStoreIpc_establishes_…`
    (v0.32.23, 26); **core (a)** `endpointQueuePopHead_popped_not_tail` (rendezvous: the popped head is no
    post-pop tail, via `endpointQueuePopHead_post_endpoint_tail` + `dualQueueEndpointWellFormed` P3 +
    `queueHeadBlockedConsistent`) + the freshness companion `endpointQueuePopHead_fresh_not_tail`
    (v0.32.24–25). All 8 + `notificationWait` transition establishers + bundle de-threads landed:
    `endpointSendDual` (v0.32.24), `endpointCall` (v0.32.25, + the `linkServerStashedReply` tail-blocked
    frame), `endpointReceiveDual` (v0.32.26, core-(c) `storeTcbIpcState` variant + Call/Send rendezvous
    sub-paths with the receiver discharged by `_fresh_not_tail`), and (v0.32.27) `endpointReplyRecv`
    (composes the receive-leg establisher through the reply phase), the 3 WithCaps (compose base + the
    `ipcUnwrapCaps` tail-blocked frame — cap transfer writes only CNode caps), cross-core
    `endpointCallOnCore` (mirrors `endpointCall` with the per-core `wakeThread`/`removeRunnableOnCore`
    object-invisible frames — `wakeThread_preserves_endpointQueueTailBlockedConsistent_of_ready` +
    `removeRunnableOnCore_preserves_endpointQueueTailBlockedConsistent`), and `notificationWait` (touches
    no endpoint queue; the running waiter is `.ready` ⇒ no endpoint tail ⇒ the only rewritten TCB cannot
    break tail-blockedness). **Every `ipcInvariantFull` bundle is now free of BOTH `hQNBC'` and `hEQTB'`.**
  - **Rendezvous (pop) branch** — qNBC is *clean* (`endpointQueuePopHead_preserves_qNBC` +
    `storeTcbReceiveComplete_preserves_qNBC` [unconditional: the `.ready` woken thread matches any
    neighbour] + `ensureRunnable` frame). Tail-blocked uses the pop frame +
    `storeTcbReceiveComplete_preserves_endpointQueueTailBlockedConsistent`, whose `hNotTail` needs
    **reusable core (a)**: *the popped head is not a tail in the post-pop state* — from post-pop
    tail-blocked (pop frame) + the head's `.blockedOnReceive endpointId` state (pre-state qHBC,
    preserved) + the pop characterisation `post popped-queue tail ≠ old head` (old head's
    `queueNext = some next ⇒ old head ≠ old tail` by `intrusiveQueueWellFormed` P3
    `tail.queueNext = none`; `none ⇒ post queue empty`).
  - **Block (enqueue + block-store) branch** — tail-blocked: the new sendQ/receiveQ tail is the
    freshly-blocked thread (transition-level, since the bare enqueue leaves it `.ready`). qNBC needs
    **reusable core (b)** `endpointQueueEnqueue_predecessor_blocked`: the block-store
    `storeTcbIpcStateAndMessage_preserves_queueNextBlockingConsistent` `hBwd` — *the predecessor of
    the enqueued thread is the old tail, blocked on the same endpoint* — established cleanly via the
    **post-state** route: `endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity` (already exists,
    `DualQueueMembership.lean:1620`) gives `a.queueNext = some tid ⇒ tid.queuePrev = some a` in `st'`;
    the enqueue sets `tid.queuePrev := some oldTail` (non-empty) / `none` (empty), so `a = oldTail`
    (resp. no predecessor). This needs one new small lemma — `endpointQueueEnqueue_enqueued_queuePrev`
    characterising `tid.queuePrev` in `st'` (via `storeTcbQueueLinks_stored_queuePrev`, a mirror of
    the existing `_stored_queueNext`) — which is cleaner than the pre-state guard-extraction +
    multi-store `queueNext` tracing. Then pre-state tail-blocked (old tail `.blockedOnSend`/`.blockedOnCall`
    resp. `.blockedOnReceive endpointId`) + `endpointQueueEnqueue_tcb_ipcState_backward` (the enqueue
    leaves `oldTail.ipcState` unchanged) close the match. `hFwd` is vacuous (`tid.queueNext = none`).
    The WithCaps variants compose the base establisher with `ipcUnwrapCaps_preserves_{qNBC,tail-blocked}`
    (cap transfer writes only CNode caps).
  Cores (a)+(b) are built once in `QueueNextBlocking.lean`; the 8 establishers are then thin.

- **Slice 2c — qHBC de-thread (needs a new reachable→blocked conjunct).** The pop's new head is a
  former *middle* element; its blockedness is not in the 19 conjuncts. **Design choice (cleaner than
  the closure-style `endpointQueueMemberBlocked`):** add the *per-link* conjunct
  **`queueNextTargetBlocked`** — `a.queueNext = some b ⇒ b is blocked on the same endpoint/queue as
  `a` (no `.ready`)` — i.e. the *strict* form of `queueNextBlockingMatch` (which currently admits a
  `.ready` target via its catch-all). Together with `queueHeadBlockedConsistent` (head blocked) it
  yields "every queue member blocked", so the pop's new head (= old head's `queueNext` target) is
  blocked **from the pre-state**. Preservation has the *same* transition-level shape as tail-blocked
  (enqueue pairs with block-store; pop's relink removes the only target obligation), so the 2b cores
  largely carry over. Then drop `hQHBC'` from the 8. (`endpointQueueTailBlockedConsistent` becomes
  derivable from `queueNextTargetBlocked` + a tail-membership fact and can later be retired.)

  **FOUNDATION LANDED (v0.32.29):** the `queueNextTargetBlocked` def (`Defs.lean`, two-clause strict
  form: receive→receive and send/call→send/call, same endpoint) + the object-preserving frame family
  (`QueueNextBlocking.lean`): `queueNextTargetBlocked_of_objects_eq` (pointwise),
  `queueNextTargetBlocked_of_tcb_links_backward` (the workhorse combinator — backward maps preserving
  both `ipcState` **and** `queueNext`), `ensureRunnable`/`removeRunnable` scheduler frames, and
  `storeObject_{non_ep_non_tcb,endpoint}` object-store frames.  **Frame family COMPLETE (v0.32.30):**
  the two *link/state-mutating* frames also landed — `storeTcbQueueLinks_preserves_queueNextTargetBlocked`
  (`hNewLink` discharge for the freshly-set link) and
  `storeTcbIpcStateAndMessage_preserves_queueNextTargetBlocked` (`hBwd`/`hFwd` predecessor/successor
  obligations) — both ported from their qNBC analogues.  **KEYSTONE LANDED (v0.32.31):** the
  enqueue+block-store establisher `endpointQueueEnqueue_blockStore_establishes_queueNextTargetBlocked`
  (+ its `storeTcbIpcState` variant) — the strict form must reason **end-to-end** (unlike qNBC, the
  permissive→strict gap means the post-enqueue/pre-block-store state transiently *violates* qNTB), via
  core (b) `endpointQueueEnqueue_predecessor_blocked` for the new `oldTail → tid` link (source blocked
  + target blocked-same-endpoint ⇒ strict-match through `queueNextTargetBlocked_clause_of_predecessor_block`),
  `tid.queueNext = none` for the no-outgoing-link case, and the new `endpointQueueEnqueue_tcb_queueNext_backward_ne`
  + `storeTcbIpcStateAndMessage/storeTcbIpcState_tcb_queueNext_backward` backward helpers for the
  framed pre-existing links.  **POP/RENDEZVOUS FOUNDATION LANDED (v0.32.32):**
  `endpointQueuePopHead_preserves_queueNextTargetBlocked` (the pop only *removes* the head's outgoing
  link + re-stores the new head's own `queueNext` unchanged — no new link), plus the receiver-`.ready`
  discharge facts `endpointQueuePopHead_popped_queuePrev_none` (the pop's final
  `storeTcbQueueLinks headTid none none none` clears the head's `queuePrev`) and
  `endpointQueuePopHead_popped_no_incoming` (post-pop link integrity + cleared `queuePrev` ⇒ no thread
  links to the popped head, so setting it `.ready` is safe).  **`endpointSendDual` ESTABLISHER +
  no-incoming framing core LANDED (v0.32.33–34):** the first per-transition establisher
  `endpointSendDual_preserves_queueNextTargetBlocked` (block via keystone, rendezvous via
  pop-preservation + `storeTcbReceiveComplete_preserves_queueNextTargetBlocked` [`hNoIncoming` =
  `…_popped_no_incoming`] + `ensureRunnable`), plus the reusable no-incoming framing core
  `queueNext_noIncoming_of_backward` + `{storeTcbIpcStateAndMessage,ensureRunnable,storeObject_nonTcb}_preserves_noIncoming`.
  **Key design point** (discovered while extending to the *fresh*-receiver transitions): every
  ipcState-changing store needs "no thread links to the changed thread"; for the *popped head* this is
  derived (`…_popped_no_incoming`), but for a **fresh** receiver / notification-waiter / reply-target it
  is **not** derivable from the current invariants (it needs "queue-member ⇒ blocked", which is exactly
  what qNTB+qHBC *close* — a bootstrapping circularity), so those establishers take a **dischargeable**
  `hXNoIncoming` precondition (the running/notification-blocked thread is not in an endpoint queue),
  framed through the transition's earlier stores by the no-incoming core (the pop case additionally
  needs a pop `queueNext`-backward, still to build).  **Strategic insight:** the **`hQHBC'` de-thread
  (the actual goal) is likely *more* tractable than completing every qNTB establisher** — `qHBC`
  constrains only endpoint *heads*, and a fresh receiver is excluded from being a head by
  `hFreshReceiver`, so the receiver-`.ready` store preserves `qHBC` *trivially* (no no-incoming needed).
  Two paths to the goal: (a) complete all qNTB establishers then wire+qHBC; or (b) wire qNTB with
  `hQNTB'` *threaded* for the hard IPC bundles (established for the frame-style producers +
  `endpointSendDual`), build the easier `qHBC` establishers, drop `hQHBC'`, then de-thread `hQNTB'` as
  follow-on.  **Atomic-wire recipe VALIDATED (structural half builds in isolation):** the 5 `Defs.lean`
  edits are (a) append `∧ queueNextTargetBlocked st` to the `ipcInvariantFull` def; (b) add the
  `queueNextTargetBlocked` field to `structure IpcInvariantFull` (last); (c) append
  `h.queueNextTargetBlocked` to **both** directions of `ipcInvariantFull_iff_IpcInvariantFull` (named
  accessors — no positional shift); (d) **only the last** `@[simp]` projection shifts —
  `endpointQueueTailBlockedConsistent` goes `h.2.2…2` (18 `.2`) → `h.2.2…2.1`, and add the new
  `queueNextTargetBlocked` projection `h.2.2…2.2` (= 19 `.2`); (e) add `(hQNTB : queueNextTargetBlocked
  st)` param + `, hQNTB` to `ipcInvariantFull_of_core_replyCallerLinkage` **and** the
  `ipcInvariantFull_compositional` helper.  Then every **producer** appends a qNTB term to its tuple:
  the **17 producers** are the 10 direct-tuple bundles (`endpointSendDual`/`Call`/`ReceiveDual`/
  `notificationSignal`/`Wait`/`endpointReply`/`ReplyRecv`/3×WithCaps) + the 2 reply mutators
  (`linkCallerReply`/`consumeCallerReply`, via `_of_core_replyCallerLinkage`) + 3 arch frames
  (`advanceTimerState`/`writeRegisterState`/`contextSwitchState`) + cross-core `endpointCallOnCore` +
  per-core (`CrossSubsystemPerCorePreservation`).  Path-(b) recipe: thread `(hQNTB' :
  queueNextTargetBlocked st')` on the 10+cross-core+per-core bundles (append `, hQNTB'`); use the
  `endpointSendDual` establisher for that one; object-frame (`queueNextTargetBlocked_of_objects_eq`) for
  the 3 arch frames + the 2 reply mutators.  **Remaining 2c work** (next slices, in order): (2) the
  per-transition establishers composing keystone (block) + pop/rendezvous (the receiver-`.ready` store
  via the `storeTcbIpcStateAndMessage` frame with `hFwd` trivial [`.ready` source] + `hBwd` discharged
  by `…_popped_no_incoming` or `hXNoIncoming`); (3) the **atomic** wire per the validated recipe above,
  establish it for every producer (most are object-frames; the enqueue/pop transitions use step 2),
  then build the
  `T_preserves_queueHeadBlockedConsistent` establishers (pop new-head blocked via
  `queueNextTargetBlocked` + pre-state qHBC) and drop `hQHBC'` from the 9 bundles + cross-core.

  **ATOMIC WIRE LANDED (v0.32.36):** `queueNextTargetBlocked` is now the **20th `ipcInvariantFull`
  conjunct** per the validated recipe (the 5 `Defs.lean` edits + every producer wired).  **Established
  from the pre-state** (genuine de-thread): `endpointSendDual` (the v0.32.33 establisher),
  `lifecycleRetypeObject` (new frame — retyped object has `queueNext = none`, nobody links to the fresh
  target), the 2 reply mutators (`linkCallerReply`/`consumeCallerReply` — new
  `_preserves_queueNextTargetBlocked` frames via the new
  `storeObject_tcb_preserveIpcAndQueueNext_preserves_queueNextTargetBlocked` primitive), the 3 arch
  object-frames, `boot`, and `default`.  **Threaded transitionally (`hQNTB'`)** for the 9 remaining IPC
  bundles (`endpointReceiveDual`/`Call`/`notificationSignal`/`Wait`/`endpointReply`/`ReplyRecv`/3×WithCaps)
  + cross-core `endpointCallOnCore` — their rendezvous/deliver branches set the *running* (not popped)
  receiver/waiter `.ready`, whose no-incoming needs a `dualQueueSystemInvariant` derivation rather than
  the popped-head structural fact; each de-threaded in its own follow-on commit.  New supporting frames:
  `lifecycleRetypeObject_preserves_queueNextTargetBlocked` + `coreIpcInvariantBundle_to_queueNextTargetBlocked`
  (`EndpointReplyAndLifecycle.lean`), `default_queueNextTargetBlocked` (`Architecture/Invariant.lean`).
  Full build (376) + staged (`Platform.Staged`) + `test_smoke` green, trace byte-identical;
  `RAW_LOOKUP_TID` re-anchored 1195→1203.

  **qHBC POP CORE + FIRST `hQHBC'` DE-THREAD LANDED (v0.32.37):** the rendezvous-pop keystone
  **`endpointQueuePopHead_preserves_queueHeadBlockedConsistent`** — `endpointQueuePopHead` advances the
  popped queue's head to the old head's `queueNext` target
  (`endpointQueuePopHead_post_endpoint_queues`); that target is blocked on the **same** queue/endpoint
  as the old head (the head, blocked by pre-state `qHBC`) via **qNTB**; the other queue's head + every
  other endpoint frame (the pop rewrites no `ipcState`).  This is exactly the new-head blockedness that
  was *not* derivable before qNTB (the new head is a former *middle* element).  First wired `hQHBC'`
  de-thread: **`notificationWait`** (the easiest — touches the *notification* waitQ, never an endpoint
  queue, so endpoint heads frame; the running waiter is `.ready` ⇒ not a head), via
  `notificationWait_preserves_queueHeadBlockedConsistent` (head dual of the tail-blocked establisher).
  `RAW_LOOKUP_TID` re-anchored 1203→1205.

  **qHBC ENQUEUE KEYSTONE LANDED (v0.32.38):** the block-leg counterpart of the pop core.
  `endpointQueueEnqueue_post_head_cases` (`Transport.lean`, the enqueue dual of
  `endpointQueuePopHead_post_endpoint_queues`: enqueued-dir head = `tid` if empty else old head; other
  dir unchanged) + the two keystones `endpointQueueEnqueue_blockStore{Ipc,}_establishes_queueHeadBlockedConsistent`
  (`storeTcbIpcState` for `Receive`/`Call`, `storeTcbIpcStateAndMessage` for `Send`): every post-state
  head is a pre-state head (unchanged `ipcState`, blocked by `qHBC`) or `tid` in the empty case (blocked
  by `hBlock`); `tid` is fresh (`hFreshTid`), so heads no other queue.  `RAW_LOOKUP_TID` re-anchored
  1205→1213.  **Both legs of the endpoint transitions' `qHBC` preservation are now provable from the
  pre-state** (qNTB for the pop's new head; `hBlock`/`qHBC` for the enqueue).

  **FIRST ENDPOINT `hQHBC'` DE-THREAD LANDED (v0.32.39):** `endpointSendDual` (+ `WithCaps`).
  `endpointQueuePopHead_popped_not_head` (head dual of `…_popped_not_tail`: the popped head heads no
  queue — popped-queue new head ≠ `tid` by `tcbQueueChainAcyclic_no_self_loop`; other queues by the
  `qHBC` kind-pinning) + `endpointSendDual_preserves_queueHeadBlockedConsistent` (deliver: pop core +
  `storeTcbReceiveComplete` [`hNotHead` = `…_popped_not_head`] + `ensureRunnable`; block: the
  `storeTcbIpcStateAndMessage` enqueue keystone + `removeRunnable`) +
  `ipcUnwrapCaps_preserves_queueHeadBlockedConsistent` + `endpointSendDualWithCaps_preserves_queueHeadBlockedConsistent`.
  `hQHBC'` dropped from both send bundles.

  **`endpointReceiveDual` `hQHBC'` DE-THREAD LANDED (v0.32.40):** the dual Call/Send rendezvous
  sub-paths. Key helpers: `cleanupPreReceiveDonation_preserves_queueHeadBlockedConsistent` +
  `storeTcbIpcStateAndMessage_ready_preserves_queueHeadBlockedConsistent` (the receiver-wake frame —
  setting a thread `.ready` when already `.ready` preserves `qHBC`, `hNotHead` discharged internally
  from the store's success + a readiness precondition). The establisher transports the running
  receiver's readiness **backward** through the pop + sender-store + reply-link (`receiver ≠ sender`
  since the sender is blocked, the receiver `.ready`).  `endpointReceiveDual{,WithCaps}` `hQHBC'`
  dropped.

  **`endpointCall` + `endpointReplyRecv` `hQHBC'` DE-THREAD LANDED (v0.32.41) — single-core qHBC
  de-thread COMPLETE.** `endpointCall_preserves_queueHeadBlockedConsistent` (rendezvous pop receiveQ +
  caller `.blockedOnReply` store + `linkServerStashedReply`; block path = enqueue keystone) +
  `endpointCallWithCaps` (base + cap-transfer frame).  `endpointReplyRecv_preserves_queueHeadBlockedConsistent`
  composes the reply phase (`.ready`-wake of the `.blockedOnReply` target, no endpoint head) with the
  receive-leg qHBC establisher; the receive leg's `queueNextTargetBlocked` precondition is transported via
  the new `storeTcbIpcStateAndMessage_ready_of_blockedOnReply_preserves_queueNextTargetBlocked` frame, and
  the running-receiver readiness across the reply phase (`receiver ≠ replyTarget`).  `hQHBC'` dropped from
  `endpointCall{,WithCaps}` + `endpointReplyRecv` bundles.  **Every single-core IPC bundle now establishes
  `qHBC`.**

  **qNTB DE-THREAD IN PROGRESS (v0.32.42):** the strict link-target conjunct (#20).  Reusable frames:
  `storeTcbIpcStateAndMessage_no_incoming_nonQueueBlocked_preserves_queueNextTargetBlocked` (non-queue-blocking
  store to a no-blocked-incoming thread) + `queueNextTargetBlocked_no_incoming_of_notQueueBlocked` (a
  non-queue-blocked thread has no blocked incoming link) + `cleanupPreReceiveDonation` / `ipcUnwrapCaps` qNTB
  frames.  Key insight: unlike `qNBC`, qNTB needs the **fused** enqueue+block-store keystone (not enqueue
  alone) and the no-incoming discipline for `.ready`/`.blockedOnReply` stores.  De-threaded `hQNTB'` from
  `endpointReply`, `endpointReceiveDual`, `endpointReceiveDualWithCaps` (v0.32.42) and
  `endpointCall`, `endpointCallWithCaps` (v0.32.43; each gains the dischargeable `hCallerReady`
  precondition — the running syscall caller is `.ready`, supplied by the reachability bundle at D8).
  Frame `linkServerStashedReply_preserves_queueNextTargetBlocked` added.  **Single-core qNTB
  de-thread COMPLETE (v0.32.44):** `notificationSignal`, `notificationWait`, `endpointReplyRecv`,
  `endpointSendDualWithCaps` de-threaded (frames added: `storeTcbIpcState{,_no_incoming_nonQueueBlocked}_preserves_queueNextTargetBlocked`).
  Every single-core IPC bundle now de-threads **both** `hQHBC'` and `hQNTB'`.

  **SLICE 2c COMPLETE (v0.32.45):** the cross-core `endpointCallOnCore` `qHBC`+`qNTB` establishers
  landed (frames: `removeRunnableOnCore`/`wakeThread`-of-`.ready` for `qHBC`+`qNTB`; the wake is the
  object-lookup-invisible §2 keystone).  **Zero `hQHBC'`/`hQNTB'`-threaded sites remain anywhere** —
  every IPC `ipcInvariantFull` bundle, single-core and cross-core, now establishes both conjuncts
  from the pre-state.  The dischargeable readiness preconditions threaded into the call/notification/
  reply-recv bundles (`hCallerReady`/`hReceiverReady`/`hWaiterReady`) are supplied by the reachability
  bundle at the D8 layer.

- **D1 (4 wiring conjuncts):** same enqueue-freshness root — dischargeable once the caller-`.ready`
  freshness precondition is threaded from the dispatcher (independent of 2c).

- **D6 residual (`donationOwnerValid`, 2 reply bundles):** composite-only — the bare
  `endpointReply`/`endpointReplyRecv` wake the `.blockedOnReply` owner without returning the
  donation; de-thread must compose at the `*WithDonation` layer (`applyReplyDonation`).

- **D8 (payoff):** once D1/D4/D6 close, the dischargeable preconditions
  (`allTimeoutBudgetsNone`, caller-`.ready` freshness, `*NotReply`/`*NotUnbound`) are supplied by a
  reachability bundle, yielding the unconditional `ipcInvariantFull`-preservation payoff theorem.

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
