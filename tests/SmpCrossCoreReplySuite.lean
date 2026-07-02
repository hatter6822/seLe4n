-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyNI
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.C — Cross-core reply test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM6.C
"Reply path across cores" deliverable
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §4.3, §5).

* **§1 Surface anchors** — every public SM6.C symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (cross-core
  reply wake SGI, 2PL atomicity, per-core / ∀-core non-interference, donation
  chain extension) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cross_core_reply_suite` exercises the
  actual `endpointReplyOnCore` / `endpointReplyRecvOnCore` /
  `endpointReplyCrossCoreDispatch` / `lockSet_endpointReply` computations on the
  SM6.C cross-core reply scenarios: the SM6.C.1/.6 lock-set footprint + caller-TCB
  write-lock membership, the SM6.C.4 payload delivery to the right TCB, the
  SM6.C.2 local vs remote caller-wake SGI emission, the SM6.C.7 reply-replay
  barrier + confused-deputy rejection, the SM6.C.5 replyRecv lock-set, the SM6.C.3
  donation-chain lock-set extension, and the SM6.C.9 chain-length bound.
-/

namespace SeLe4n.Testing.SmpCrossCoreReply

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM6.C public symbol resolves
-- ============================================================================

-- SM6.C.1/.5 production transitions + lock-set helpers:
#check @endpointReplyOnCore
#check @endpointReceiveDualOnCore
#check @endpointReplyRecvOnCore
#check @endpointReplyDonation?
#check @lockSet_endpointReplyOnCore
#check @lockSet_endpointReplyRecvOnCore

-- SM6.C.1 path-reduction lemmas:
#check @endpointReplyOnCore_reply_eq
#check @endpointReplyOnCore_not_blocked_eq
#check @endpointReplyOnCore_delegated_replier_eq

-- SM6.C.2 cross-core caller wake (endpointReply_remote_wake):
#check @endpointReplyOnCore_remote_wake
#check @endpointReplyOnCore_no_sgi_if_local
#check @endpointReplyOnCore_not_blocked_no_sgi

-- SM6.C.1/.5 lock-set hierarchical correctness:
#check @endpointReplyOnCore_lockSet_correct
#check @lockSet_endpointReplyOnCore_correct
#check @endpointReplyRecv_lockSet_correct
#check @lockSet_endpointReplyRecvOnCore_correct

-- SM6.C.4 reply payload delivery to the right TCB:
#check @endpointReplyOnCore_perCore_delivery
#check @storeTcbIpcStateAndMessage_fromTcb_self

-- SM6.C.6 reply-state lifecycle: caller-TCB write lock in the footprint:
#check @lockSet_endpointReply_target_tcb_write_mem

-- SM6.C.7 reply-replay barrier:
#check @endpointReplyOnCore_replay_rejected

-- SM6.C 2PL atomicity (reply + replyRecv):
#check @endpointReplyOnCore_atomic_under_lockSet
#check @endpointReplyRecvOnCore_atomic_under_lockSet

-- SM6.C per-core wake locality:
#check @endpointReplyOnCore_perCore_consistent

-- SM6.C IPC-invariant preservation (objects.invExt + ipcInvariant) + state char:
#check @endpointReplyOnCore_state_eq
#check @endpointReplyOnCore_preserves_objects_invExt
#check @endpointReplyOnCore_preserves_ipcInvariant

-- SM6.C.8 non-interference (boot-core projectState + per-core / ∀-core smp):
#check @endpointReplyOnCore_reply_path_NI
#check @endpointReplyOnCore_reply_path_NI_smp

-- SM6.C.3 donation chain across cores + cross-core dispatch:
#check @applyReplyDonationOnCore
#check @applyReplyDonationOnCore_bootCoreId
#check @lockSet_endpointReply_donation_extension
-- WS-SM SM6.D (PR #822 review): the reply donation return is keyed on the RECORDED
-- SERVER (the caller's `blockedOnReply` server, who holds the donated SC), not the
-- possibly-delegated cap holder.
#check @recordedReplyServer?
#check @endpointReplyServerDonation?
-- WS-SM SM6.D: the per-object reply WRITE lock is in the reply footprint once the
-- reply object is resolved (the 2PL coverage of the single-use `reply.caller`
-- consume — PR #822 review 6J90-5).
#check @lockSet_endpointReply_reply_write_mem
-- WS-SM SM6.D (PR #822 review 6J-NL9): the per-object reply write lock is also in the
-- `.receive` / `.call` footprints once the linked reply is resolved (a Call rendezvous
-- on receive / a server-first Call links a Reply object under the reply write lock).
#check @lockSet_endpointReceive_reply_write_mem
#check @lockSet_endpointCall_reply_write_mem
-- PR #827 review #3 (reply-fold): the single-use `consumeCallerReply` teardown is
-- folded into `endpointReplyOnCore` itself — atomic with the delivery — so this
-- below-API dispatch (delivery + donation return + PIP reversion) and every direct
-- caller of the primitive get full single-use reply semantics by construction.
#check @endpointReplyCrossCoreDispatch
#check @endpointReplyCrossCoreDispatchChecked
#check @endpointReplyCrossCoreDispatchChecked_flow_denied
#check @endpointReplyCrossCoreDispatchChecked_flow_allowed
-- PR #822 review: the raw-thread `endpointReplyRecvCrossCoreDispatch{,Checked}`
-- wrappers were removed (they bypassed the reply cap); the live `.replyRecv` routes
-- through the reply-object-aware `API.replyRecvBody`.  The below-API combined
-- transition `endpointReplyRecvOnCore` (anchored above) remains the building block.

-- SM6.C.9 reply donation-chain length bound:
#check @endpointReply_donation_chain_length_bounded

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): theorems apply to typed inputs
-- ============================================================================

/-- SM6.C.2: a reply unblocking a remote caller emits the reschedule SGI. -/
example (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (targetTcb' : TCB)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hTcb' : st'.getTcb? target = some targetTcb')
    (hRemote : determineTargetCore st' target ≠ executingCore) :
    (endpointReplyOnCore replier target msg executingCore st).2
      = .ok (some (determineTargetCore st' target, SgiKind.reschedule)) :=
  endpointReplyOnCore_remote_wake replier target msg executingCore st st' tcb ep expected
    targetTcb' hSz1 hSz2 hLk hIpc hStore hTcb' hRemote

/-- SM6.C: the reply is a single 2PL-atomic step under its lock-set. -/
example (replier target : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (msg : IpcMessage)
    (executingCore : CoreId) (donatedSc? : Option SeLe4n.SchedContextId)
    (donatedOwner? : Option SeLe4n.ThreadId) (s : SystemState) :
    (withLockSet (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?)
        executingCore (endpointReplyOnCore replier target msg executingCore) s).2
      = (endpointReplyOnCore replier target msg executingCore
          (acquireAll executingCore
            (lockSet_endpointReply replier cnRoot target donatedSc? donatedOwner?).lockAcquireSequence s)).2 := by
  rw [endpointReplyOnCore_atomic_under_lockSet]

/-- SM6.C.8: a cross-core reply unblocking a high caller is invisible on every core. -/
example (ctx : LabelingContext) (observer : IfObserver)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st st' : SystemState) (tcb : TCB) (ep : SeLe4n.ObjId) (expected : SeLe4n.ThreadId)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hLk : lookupTcb st target = some tcb)
    (hIpc : tcb.ipcState = .blockedOnReply ep (some expected))
    (hStore : storeTcbIpcStateAndMessage_fromTcb st target tcb .ready (some msg) = .ok st')
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false) :
    lowEquivalent_smp ctx observer (endpointReplyOnCore replier target msg executingCore st).1 st :=
  endpointReplyOnCore_reply_path_NI_smp ctx observer replier target msg executingCore st st' tcb ep
    expected hSz1 hSz2 hLk hIpc hStore hObjInv hObjSetInv hIdxComplete hTargetHigh hTargetObjHigh

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM6.C cross-core reply scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def core1 : CoreId := ⟨1, by decide⟩

private def epId : SeLe4n.ObjId := ⟨600⟩
private def cnRoot : SeLe4n.ObjId := ⟨300⟩
private def serverTid : SeLe4n.ThreadId := ⟨601⟩
private def clientLocalTid : SeLe4n.ThreadId := ⟨602⟩
private def clientRemoteTid : SeLe4n.ThreadId := ⟨603⟩
private def wrongTid : SeLe4n.ThreadId := ⟨604⟩
private def scId : SeLe4n.SchedContextId := ⟨700⟩
private def replyMsg : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 100, SeLe4n.RegValue.ofNat 200, SeLe4n.RegValue.ofNat 300],
    caps := #[], badge := none }
private def replyMsg2 : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 999], caps := #[], badge := none }

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) (ipc : ThreadIpcState) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := ipc,
    cpuAffinity := aff }

/-- Endpoint + a ready (unbound) server (replier) + two clients `BlockedOnReply`
recording the server as the authorised replier: an unbound (local-home) client and
a core1-bound (remote-home) client.  Only the server is runnable; the clients are
blocked awaiting the reply. -/
private def stBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject serverTid.toObjId (.tcb (mkTcb 601 50 none .ready))
    |>.withObject clientLocalTid.toObjId
        (.tcb (mkTcb 602 30 none (.blockedOnReply epId (some serverTid))))
    |>.withObject clientRemoteTid.toObjId
        (.tcb (mkTcb 603 30 (some core1) (.blockedOnReply epId (some serverTid))))
    |>.withRunnable [serverTid]
    |>.build)

/-- The optional SGI surfaced by a cross-core reply (`none` on a kernel error). -/
private def replySgi (replier target : SeLe4n.ThreadId) (st : SystemState) (ec : CoreId) :
    Option (CoreId × SgiKind) :=
  match (endpointReplyOnCore replier target replyMsg ec st).2 with
  | .ok sgi => sgi
  | .error _ => none

private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.1 SM6.C.1/.6 lock-set footprint + caller-TCB write lock ---"
  -- SM6.C.1: every declared lock has a kind permitted for `.reply`.
  assertBool "reply lock-set kinds all permitted (replier W, cnode R, caller W)"
    (decide (∀ p ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid none none).pairs,
        p.fst.kind ∈ permittedKinds .reply))
  -- SM6.C.1: keys are duplicate-free.
  assertBool "reply lock-set keys are duplicate-free"
    (decide ((lockSet_endpointReply serverTid cnRoot clientLocalTid none none).pairs.map (·.fst)).Nodup)
  -- SM6.C.6: the caller-TCB *write* lock — the reply-state lifecycle write — is declared.
  assertBool "caller-TCB write lock is in the reply footprint (reply-state lifecycle)"
    (decide ((tcbLock clientLocalTid, AccessMode.write)
      ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid none none).pairs))
  -- SM6.C.5: the replyRecv lock-set is hierarchically correct.
  assertBool "replyRecv lock-set kinds all permitted"
    (decide (∀ p ∈ (lockSet_replyRecv serverTid cnRoot clientLocalTid epId none none none).pairs,
        p.fst.kind ∈ permittedKinds .replyRecv))
  -- SM6.C.1: the state-resolved reply lock-set is hierarchically correct.
  assertBool "state-resolved reply lock-set kinds all permitted"
    (decide (∀ p ∈ (lockSet_endpointReplyOnCore stBase serverTid cnRoot clientLocalTid).pairs,
        p.fst.kind ∈ permittedKinds .reply))
  -- WS-SM SM6.D: once the reply object is resolved (`replyId := some rid`), the
  -- per-object reply WRITE lock is in the footprint — the 2PL coverage of the
  -- single-use `reply.caller := none` consume against a copied reply cap on a
  -- second core (PR #822 review 6J90-5).
  assertBool "per-object reply write-lock is in the reply footprint (resolved rid)"
    (decide ((replyLock (⟨707⟩ : SeLe4n.ReplyId), AccessMode.write)
      ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid none none
          (some (⟨707⟩ : SeLe4n.ReplyId))).pairs))
  assertBool "reply lock-set with resolved reply object: kinds all still permitted"
    (decide (∀ p ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid none none
          (some (⟨707⟩ : SeLe4n.ReplyId))).pairs, p.fst.kind ∈ permittedKinds .reply))
  -- WS-SM SM6.D (PR #822 review 6J-NL9): the `.receive` / `.call` footprints also carry
  -- the per-object reply write lock once the linked reply is resolved — a Call rendezvous
  -- on receive (and a server-first Call) links a Reply object under that lock.
  assertBool "per-object reply write-lock is in the .receive footprint (resolved rid)"
    (decide ((replyLock (⟨707⟩ : SeLe4n.ReplyId), AccessMode.write)
      ∈ (lockSet_endpointReceive serverTid cnRoot epId none (some (⟨707⟩ : SeLe4n.ReplyId))).pairs))
  assertBool "per-object reply write-lock is in the .call footprint (resolved rid)"
    (decide ((replyLock (⟨707⟩ : SeLe4n.ReplyId), AccessMode.write)
      ∈ (lockSet_endpointCall serverTid cnRoot epId none none (some (⟨707⟩ : SeLe4n.ReplyId))).pairs))

private def runDeliveryChecks : IO Unit := do
  IO.println "--- §3.2 SM6.C.4 reply payload delivery to the right TCB ---"
  let (st', res) := endpointReplyOnCore serverTid clientLocalTid replyMsg bootCoreId stBase
  -- The reply succeeds (the server is the authorised replier).
  assertBool "authorised reply succeeds (no error)"
    (match res with | .ok _ => true | .error _ => false)
  -- The caller is delivered the reply message and made ready.
  assertBool "reply delivers the payload to the caller (.ready + the reply registers)"
    (match st'.getTcb? clientLocalTid with
     | some t => decide (t.ipcState = .ready ∧ t.pendingMessage = some replyMsg)
     | none => false)
  -- No OTHER thread receives the payload (the server's pendingMessage is unchanged).
  assertBool "the replier (server) does not receive the payload"
    (match st'.getTcb? serverTid with
     | some t => decide (t.pendingMessage = none)
     | none => false)

private def runWakeChecks : IO Unit := do
  IO.println "--- §3.3 SM6.C.2 reply wake (local vs remote SGI) ---"
  -- Local caller (unbound ⇒ home = boot core = executing core): no SGI.
  assertBool "reply waking a local (unbound) caller surfaces no SGI"
    (match replySgi serverTid clientLocalTid stBase bootCoreId with | none => true | _ => false)
  -- Remote caller (core1-bound): a reschedule SGI is fired to core 1.
  assertBool "reply waking a core1-bound (remote) caller fires a reschedule SGI to core 1"
    (match replySgi serverTid clientRemoteTid stBase bootCoreId with
     | some (tgt, kind) => decide (tgt = core1 ∧ kind = SgiKind.reschedule)
     | none => false)
  -- The woken remote caller is enqueued on core 1's run queue (its home core).
  let (st', _) := endpointReplyOnCore serverTid clientRemoteTid replyMsg bootCoreId stBase
  assertBool "the woken remote caller is enqueued on core 1 (its home core)"
    ((st'.scheduler.runQueueOnCore core1).contains clientRemoteTid)
  assertBool "the boot core's run queue is untouched by the remote wake"
    (!(st'.scheduler.runQueueOnCore bootCoreId).contains clientRemoteTid)

private def runReplayChecks : IO Unit := do
  IO.println "--- §3.4 SM6.C.7 reply-replay barrier + confused-deputy rejection ---"
  -- A delivered reply leaves the caller `.ready`; a SECOND reply (replay) fails closed.
  let (post, _) := endpointReplyOnCore serverTid clientLocalTid replyMsg bootCoreId stBase
  assertBool "a replayed reply to a now-ready caller fails with replyCapInvalid"
    (match (endpointReplyOnCore serverTid clientLocalTid replyMsg2 bootCoreId post).2 with
     | .error .replyCapInvalid => true | _ => false)
  -- PR #822 review 6J-lYm: a replier that is NOT the originally-recorded server — a holder
  -- of a copied/minted (delegated) reply cap — now SUCCEEDS.  Authority is the reply
  -- *capability* (resolved by the dispatch to `reply.caller = target`), not the fixed
  -- recorded replier; seL4-MCS reply caps are delegatable.  The confused-deputy protection
  -- is the cap (only a holder reaches this primitive); replay is the `.blockedOnReply`
  -- barrier (verified above) — a consumed reply leaves the caller `.ready`.
  assertBool "a delegated replier (copied reply-cap holder) succeeds (cap-based authority)"
    (match (endpointReplyOnCore wrongTid clientLocalTid replyMsg bootCoreId stBase).2 with
     | .ok _ => true | _ => false)
  -- A reply to a thread NOT in blockedOnReply state (the server itself) is rejected.
  assertBool "a reply to a non-blockedOnReply target is rejected"
    (match (endpointReplyOnCore serverTid serverTid replyMsg bootCoreId stBase).2 with
     | .error .replyCapInvalid => true | _ => false)
  -- A reply to an absent object fails with objectNotFound.
  assertBool "a reply to an absent target fails with objectNotFound"
    (match (endpointReplyOnCore serverTid ⟨9999⟩ replyMsg bootCoreId stBase).2 with
     | .error .objectNotFound => true | _ => false)

private def replyId707 : SeLe4n.ReplyId := ⟨707⟩

/-- `stBase` with a first-class Reply object **mutually linked** to the local
client (the seL4-MCS Call-time linkage: `reply.caller = clientLocal` and
`clientLocal.replyObject = reply`) — the pair the PR #827 #3 fold consumes. -/
private def stLinked : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject serverTid.toObjId (.tcb (mkTcb 601 50 none .ready))
    |>.withObject clientLocalTid.toObjId
        (.tcb { mkTcb 602 30 none (.blockedOnReply epId (some serverTid)) with
                  replyObject := some replyId707 })
    |>.withObject clientRemoteTid.toObjId
        (.tcb (mkTcb 603 30 (some core1) (.blockedOnReply epId (some serverTid))))
    |>.withObject replyId707.toObjId
        (.reply { replyId := replyId707, caller := some clientLocalTid })
    |>.withRunnable [serverTid]
    |>.build)

private def runConsumeChecks : IO Unit := do
  IO.println "--- §3.8 PR #827 #3 reply-fold: the in-transition single-use consume ---"
  -- A reply to a LINKED caller tears down both halves of the caller↔Reply link
  -- atomically with the delivery (formerly the separate dispatch-step consume).
  let (post, res) := endpointReplyOnCore serverTid clientLocalTid replyMsg bootCoreId stLinked
  assertBool "linked reply delivers (payload + .ready)"
    (match res, post.getTcb? clientLocalTid with
     | .ok _, some t => decide (t.ipcState = .ready ∧ t.pendingMessage = some replyMsg)
     | _, _ => false)
  assertBool "folded consume clears the Reply's caller (single-use barrier)"
    (match post.getReply? replyId707 with
     | some r => decide (r.caller = none)
     | none => false)
  assertBool "folded consume clears the woken caller's replyObject"
    (match post.getTcb? clientLocalTid with
     | some t => decide (t.replyObject = none)
     | none => false)
  -- Replay on the consumed reply: the caller is `.ready`, so a second reply
  -- fails closed — the freed Reply is available for re-linking (one-object reuse).
  assertBool "replay after the folded consume fails closed"
    (match (endpointReplyOnCore serverTid clientLocalTid replyMsg2 bootCoreId post).2 with
     | .error .replyCapInvalid => true | _ => false)
  -- An UNLINKED caller (no replyObject) is delivered with a no-op consume — the
  -- below-API direct-reply behaviour is unchanged.
  let (post2, res2) := endpointReplyOnCore serverTid clientRemoteTid replyMsg bootCoreId stLinked
  assertBool "unlinked reply still delivers unchanged (no-op consume)"
    (match res2, post2.getTcb? clientRemoteTid with
     | .ok _, some t => decide (t.ipcState = .ready ∧ t.replyObject = none)
     | _, _ => false)

private def runReplyRecvChecks : IO Unit := do
  IO.println "--- §3.5 SM6.C.5 replyRecv combined op (reply leg wakes caller) ---"
  -- The reply leg of replyRecv wakes the recorded caller; the receive leg then
  -- blocks the server on the (empty) endpoint.
  let (st', res) := endpointReplyRecvOnCore epId serverTid clientLocalTid replyMsg none bootCoreId stBase
  assertBool "replyRecv succeeds (reply leg + receive leg)"
    (match res with | .ok _ => true | .error _ => false)
  assertBool "replyRecv reply leg delivers the payload to the caller (.ready + registers)"
    (match st'.getTcb? clientLocalTid with
     | some t => decide (t.ipcState = .ready ∧ t.pendingMessage = some replyMsg)
     | none => false)
  -- The receive leg blocks the server on the endpoint (no sender was waiting).
  assertBool "replyRecv receive leg blocks the server on the endpoint (no waiting sender)"
    (match st'.getTcb? serverTid with
     | some t => decide (t.ipcState = .blockedOnReceive epId)
     | none => false)

private def runDonationChecks : IO Unit := do
  IO.println "--- §3.3' SM6.C.3 donation-chain lock-set extension ---"
  -- SM6.C.3: the donating reply lock-set = the non-donating one extended with the
  -- returned SC write lock + the original owner's TCB write lock.
  assertBool "donating reply lock-set includes the returned SchedContext write lock"
    (decide ((schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid (some scId) (some clientLocalTid)).pairs))
  assertBool "donating reply lock-set includes the original-owner TCB write lock"
    (decide ((tcbLock clientLocalTid, AccessMode.write)
      ∈ (lockSet_endpointReply serverTid cnRoot clientLocalTid (some scId) (some clientLocalTid)).pairs))
  -- The extension equation holds definitionally.
  assertBool "donation lock-set extension equation holds"
    (decide ((lockSet_endpointReply serverTid cnRoot clientLocalTid (some scId) (some clientLocalTid)).pairs
      = (lockSetExtendOpt (lockSetExtendOpt (lockSet_endpointReply serverTid cnRoot clientLocalTid none none)
          (some (schedContextLock scId, .write))) (some (tcbLock clientLocalTid, .write))).pairs))
  -- A replier holding no donated SC: the cross-core donation return is a no-op (ok).
  match SeLe4n.ThreadId.toValid? serverTid with
  | some serverV =>
      assertBool "applyReplyDonationOnCore on a non-donating replier is a no-op (ok)"
        (match applyReplyDonationOnCore stBase serverV bootCoreId with | .ok _ => true | .error _ => false)
  | none => assertBool "serverTid is a valid thread id" false
  -- WS-SM SM6.D (PR #822 review 6J90-... donation): the donation return is keyed on
  -- the RECORDED SERVER, not the (possibly delegated) cap holder.  Build a state
  -- where `clientLocalTid` is `blockedOnReply (some serverTid)` and `serverTid`
  -- holds `.donated scId clientLocalTid`; `wrongTid` is an unrelated (delegate)
  -- replier holding no donation.
  let stDonated : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject serverTid.toObjId
          (.tcb { mkTcb 601 50 none .ready with
                    schedContextBinding := .donated scId clientLocalTid })
      |>.withObject clientLocalTid.toObjId
          (.tcb (mkTcb 602 30 none (.blockedOnReply epId (some serverTid))))
      |>.withObject wrongTid.toObjId (.tcb (mkTcb 604 40 none .ready))
      |>.withRunnable [serverTid]
      |>.build)
  assertBool "recordedReplyServer? resolves the caller's recorded blockedOnReply server"
    (decide (recordedReplyServer? stDonated clientLocalTid = some serverTid))
  -- The key finding: the resolved donation is the RECORDED SERVER's, regardless of
  -- which thread holds the reply cap (the delegate `wrongTid` holds none).
  assertBool "endpointReplyServerDonation? resolves the recorded server's donation (not the replier's)"
    (decide (endpointReplyServerDonation? stDonated clientLocalTid = some (scId, clientLocalTid)))
  -- The state-resolved reply lock-set therefore covers the returned SC write lock
  -- AND the recorded server's TCB write lock, even on a delegated reply where the
  -- cap holder (`wrongTid`) is not the server.
  assertBool "delegated reply lock-set covers the returned SchedContext write lock (keyed on the server)"
    (decide ((schedContextLock scId, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore stDonated wrongTid cnRoot clientLocalTid).pairs))
  assertBool "delegated reply lock-set covers the recorded server's TCB write lock"
    (decide ((tcbLock serverTid, AccessMode.write)
      ∈ (lockSet_endpointReplyOnCore stDonated wrongTid cnRoot clientLocalTid).pairs))

private def runDispatchChecks : IO Unit := do
  IO.println "--- §3.6 SM6.C cross-core dispatch + SM6.C.9 chain bound ---"
  -- The live cross-core reply dispatch wakes the remote caller on its home core.
  let (st', res) := endpointReplyCrossCoreDispatch serverTid clientRemoteTid replyMsg bootCoreId stBase
  assertBool "cross-core reply dispatch succeeds"
    (match res with | .ok _ => true | .error _ => false)
  assertBool "cross-core reply dispatch surfaces the reschedule SGI to core 1"
    (match res with | .ok (some (tgt, kind)) => decide (tgt = core1 ∧ kind = SgiKind.reschedule) | _ => false)
  assertBool "cross-core reply dispatch enqueues the remote caller on core 1"
    ((st'.scheduler.runQueueOnCore core1).contains clientRemoteTid)
  -- SM6.C.9: the cross-core PIP-revert chain emits at most `fuel` SGIs.
  assertBool "donation-chain PIP reversion emits at most `fuel` (=8) cross-core SGIs"
    (decide ((PriorityInheritance.propagatePipChainCrossCore stBase serverTid bootCoreId 8).2.length ≤ 8))

def runSmpCrossCoreReplyChecks : IO Unit := do
  IO.println "WS-SM SM6.C — Cross-core reply suite"
  IO.println "===================================="
  runLockSetChecks
  runDeliveryChecks
  runWakeChecks
  runReplayChecks
  runConsumeChecks
  runReplyRecvChecks
  runDonationChecks
  runDispatchChecks
  IO.println "===================================="
  IO.println "All SM6.C cross-core reply checks PASS."

end SeLe4n.Testing.SmpCrossCoreReply

def main : IO Unit :=
  SeLe4n.Testing.SmpCrossCoreReply.runSmpCrossCoreReplyChecks
