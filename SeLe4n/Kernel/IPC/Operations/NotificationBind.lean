-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-!
# WS-SM SM6.B — Bound notifications (`NotificationBind`)

The seL4 *bound notification* relation: a notification can be bound to a single
TCB so that, when the notification is signalled while that TCB is
`BlockedOnReceive`, the signal is delivered **directly** to the bound TCB (the
badge becomes the TCB's receive result) instead of being stored as a pending
badge.  The binding is bidirectional — `Notification.boundTCB` ⇄
`TCB.boundNotification`.

This module adds:

* `bindNotification` / `unbindNotification` — establish / tear down the binding
  (both directions, with the seL4 "not already bound" / "is bound" preconditions).
* `boundDeliveryTarget?` — the pre-resolution: the bound TCB to deliver to, iff
  the notification has no waiters and its bound TCB is `BlockedOnReceive`.
* `notificationSignalBound` — the **canonical** notification signal: a thin
  wrapper that takes the bound-delivery path when applicable (dequeue the bound
  TCB from its endpoint, deliver the badge, wake it) and otherwise falls through
  to the unchanged `notificationSignal`.  The fall-through keeps every existing
  `notificationSignal` proof intact; the bound-delivery branch is fail-safe (a
  dangling or non-`BlockedOnReceive` binding simply falls through).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §0  `endpointQueueRemoveDual` preserves object-store integrity
-- ============================================================================

/-- WS-SM SM6.B: `endpointQueueRemoveDual` preserves `objects.invExt` — it is
built solely from `storeObject` / `storeTcbQueueLinks`, each of which preserves
the RobinHood object-store invariant.  The structural lemma the bound-delivery
path (which dequeues the bound TCB from its endpoint) needs; mirrors the case
structure of `endpointQueueRemoveDual_scheduler_eq`, threading `invExt` forward
through every branch. -/
theorem endpointQueueRemoveDual_preserves_objects_invExt
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold endpointQueueRemoveDual at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          split
          · simp
          · cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair1 hObjInv hStore1
                  cases hNext : tcb.queueNext with
                  | none =>
                    simp only []
                    cases hStore2 : storeObject endpointId _ pair1.2 with
                    | error e => simp
                    | ok pair2 =>
                      simp only []
                      have hInv2 := storeObject_preserves_objects_invExt' pair1.2 endpointId _ pair2 hInv1 hStore2
                      cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv2 hFinal
                  | some nextTid =>
                    simp only []
                    cases hLookupN : lookupTcb pair1.2 nextTid with
                    | none => simp
                    | some nextTcb =>
                      simp only []
                      cases hLink : storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                        have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                        simp only []
                        cases hStore2 : storeObject endpointId _ st2 with
                        | error e => simp
                        | ok pair2 =>
                          simp only []
                          have hInv3 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInv2 hStore2
                          cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                          | error e => simp
                          | ok st4 =>
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                            intro ⟨_, hEq⟩; subst hEq
                            exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv3 hFinal
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                  dsimp only [hLookupP]; split
                  · simp
                  · rename_i _ _ _ stAp heqAp
                    split at heqAp
                    · simp at heqAp
                    · cases hLink0 : storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                      | error e => simp [hLink0] at heqAp
                      | ok stPrev =>
                        simp [hLink0] at heqAp; subst heqAp
                        have hInv1 := storeTcbQueueLinks_preserves_objects_invExt _ _ prevTid _ _ _ hObjInv hLink0
                        cases hNext : tcb.queueNext with
                        | none =>
                          dsimp only [hNext]
                          cases hStore2 : storeObject endpointId _ stPrev with
                          | error e => simp
                          | ok pair2 =>
                            dsimp only [hStore2]
                            have hInv2 := storeObject_preserves_objects_invExt' stPrev endpointId _ pair2 hInv1 hStore2
                            cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                            | error e => simp
                            | ok st4 =>
                              simp only [Except.ok.injEq, Prod.mk.injEq]
                              intro ⟨_, hEq⟩; subst hEq
                              exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv2 hFinal
                        | some nextTid =>
                          dsimp only [hNext]
                          cases hLookupN : lookupTcb stPrev nextTid with
                          | none => simp
                          | some nextTcb =>
                            dsimp only [hLookupN]
                            cases hLink1 : storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                            | error e => simp
                            | ok st2 =>
                              have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink1
                              dsimp only [hLink1]
                              cases hStore2 : storeObject endpointId _ st2 with
                              | error e => simp
                              | ok pair2 =>
                                dsimp only [hStore2]
                                have hInv3 := storeObject_preserves_objects_invExt' st2 endpointId _ pair2 hInv2 hStore2
                                cases hFinal : storeTcbQueueLinks pair2.2 tid none none none with
                                | error e => simp
                                | ok st4 =>
                                  simp only [Except.ok.injEq, Prod.mk.injEq]
                                  intro ⟨_, hEq⟩; subst hEq
                                  exact storeTcbQueueLinks_preserves_objects_invExt _ _ tid _ _ _ hInv3 hFinal

-- ============================================================================
-- §1  Bind / unbind operations
-- ============================================================================

/-- WS-SM SM6.B (`NotificationBind`): bind notification `notificationId` to TCB
`tcbId`, setting **both** directions of the relation (`Notification.boundTCB` and
`TCB.boundNotification`).  Fails with `.illegalState` if either end is already
bound (the seL4 single-binding discipline). -/
def bindNotification (notificationId : SeLe4n.ObjId) (tcbId : SeLe4n.ThreadId) :
    Kernel Unit :=
  fun st =>
    match st.getNotification? notificationId with
    | some ntfn =>
        match lookupTcb st tcbId with
        | none => .error .objectNotFound
        | some tcb =>
            if ntfn.boundTCB.isSome || tcb.boundNotification.isSome then
              .error .illegalState
            else
              match storeObject notificationId
                  (.notification { ntfn with boundTCB := some tcbId }) st with
              | .error e => .error e
              | .ok ((), st1) =>
                  match storeObject tcbId.toObjId
                      (.tcb { tcb with boundNotification := some notificationId }) st1 with
                  | .error e => .error e
                  | .ok ((), st2) => .ok ((), st2)
    | none =>
        if (st.objects[notificationId]?).isSome then .error .invalidCapability
        else .error .objectNotFound

/-- WS-SM SM6.B (`UnbindNotification`): unbind TCB `tcbId` from its bound
notification, clearing **both** directions.  Fails with `.illegalState` if the TCB
is not bound.  Fail-safe: if the notification record has vanished, the TCB side is
still cleared. -/
def unbindNotification (tcbId : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match lookupTcb st tcbId with
    | none => .error .objectNotFound
    | some tcb =>
        match tcb.boundNotification with
        | none => .error .illegalState
        | some notificationId =>
            match storeObject tcbId.toObjId
                (.tcb { tcb with boundNotification := none }) st with
            | .error e => .error e
            | .ok ((), st1) =>
                match st1.getNotification? notificationId with
                | some ntfn =>
                    match storeObject notificationId
                        (.notification { ntfn with boundTCB := none }) st1 with
                    | .error e => .error e
                    | .ok ((), st2) => .ok ((), st2)
                | none => .ok ((), st1)

-- ============================================================================
-- §2  Bound-delivery pre-resolution
-- ============================================================================

/-- WS-SM SM6.B: the bound-delivery target of a signal to `notificationId` — the
bound TCB `t` together with the endpoint `epId` it is blocked on, iff the
notification has **no waiters** and its bound TCB is currently `BlockedOnReceive`.
`none` otherwise (fall through to the normal signal).  Pure, fail-safe (a dangling
binding or a non-receiving bound TCB resolves to `none`). -/
def boundDeliveryTarget? (st : SystemState) (notificationId : SeLe4n.ObjId) :
    Option (SeLe4n.ThreadId × SeLe4n.ObjId) :=
  match st.getNotification? notificationId with
  | some ntfn =>
      if ntfn.waitingThreads.val.isEmpty then
        match ntfn.boundTCB with
        | some t =>
            match st.getTcb? t with
            | some tcb =>
                match tcb.ipcState with
                | .blockedOnReceive epId => some (t, epId)
                | _ => none
            | none => none
        | none => none
      else none
  | none => none

-- ============================================================================
-- §3  Bound-aware notification signal (single-core canonical)
-- ============================================================================

/-- WS-SM SM6.B: the canonical notification signal.  When `boundDeliveryTarget?`
applies, deliver the badge directly to the bound TCB — dequeue it from its
endpoint receive queue (`endpointQueueRemoveDual`), store the badge into its
`pendingMessage` and mark it `.ready`, then make it runnable.  Otherwise fall
through to the unchanged single-core `notificationSignal` (so every existing
`notificationSignal` proof carries over verbatim). -/
def notificationSignalBound (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge) :
    Kernel Unit :=
  fun st =>
    match boundDeliveryTarget? st notificationId with
    | some (t, epId) =>
        let badgeMsg : IpcMessage := { IpcMessage.empty with badge := some badge }
        match endpointQueueRemoveDual epId true t st with
        | .error e => .error e
        | .ok ((), st1) =>
            match storeTcbIpcStateAndMessage st1 t .ready (some badgeMsg) with
            | .error e => .error e
            | .ok st2 => .ok ((), ensureRunnable st2 t)
    | none => notificationSignal notificationId badge st

end SeLe4n.Kernel
