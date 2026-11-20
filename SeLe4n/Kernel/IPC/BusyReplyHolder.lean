-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# The thread a reply object is busy with

seL4-MCS's `reply->replyTCB` when it is not the receiver presenting the reply:
the caller the reply is linked to, or the receiver that stashed it and still
waits.  `receiveIPC` cancels that thread's IPC before it receives
(`cancelReplyHolder`), and the receive's lock footprints declare what that
cancel writes, so both read the holder here.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The thread a reply object is busy with, other than `tid`, as its code**
(`0` for none, `t + 1` for thread `t`) — seL4-MCS's `reply->replyTCB` when it is
not the receiver: the caller the reply is linked to, or the receiver that
stashed it and still waits (`Reply.stasherCode`, `replyStashedAt`). -/
@[inline] def busyReplyHolderCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : Nat :=
  match st.getReply? rid with
  | none => 0
  | some r =>
    match r.caller with
    | some c => if c = tid then 0 else c.val + 1
    | none =>
      if st.replyStashedAt rid r then
        if r.stasherCode = tid.val + 1 then 0 else r.stasherCode
      else 0

/-- The thread the reply a receive names is busy with (`busyReplyHolderCode`),
if it names one: the thread whose IPC the receive cancels, read off the state
the receive is handed. -/
def busyReplyHolder? (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyId? : Option SeLe4n.ReplyId) : Option SeLe4n.ThreadId :=
  match replyId? with
  | none => none
  | some rid =>
    match busyReplyHolderCode st tid rid with
    | 0 => none
    | k + 1 => some ⟨k⟩

/-- **seL4's `reply->replyTCB` for a stash, as a state reads it**: the
recorded stasher while the record is live (`SystemState.replyStashedAt`), none
(`0`) once the stasher's own stash has been cleared.  seL4 clears `replyTCB` at
every `reply_unlink`; seLe4n leaves the record (`Reply.stasherCode`) to be
cleared lazily, so a stash dropped on the receiver's side writes no Reply and
takes no Reply lock.  Every reader of the record asks `replyStashedAt` before
it reads the field, so it reads exactly this value, the one seL4's eager clear
would leave (`replyStashedAt_stasherSeen`, `busyReplyHolderCode_eq_stasherSeen`,
`finaliseReplyUnstash_eq_stasherSeen`). -/
@[inline] def replyStasherSeen (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply) : Nat :=
  if st.replyStashedAt rid r then r.stasherCode else 0

/-- **The record read lazily answers as the record cleared eagerly**: whether a
reply is stashed has the same answer on the Reply as stored and on the Reply
seL4's eager clear would have left. -/
theorem replyStashedAt_stasherSeen (st : SystemState) (rid : SeLe4n.ReplyId) (r : Reply) :
    st.replyStashedAt rid { r with stasherCode := replyStasherSeen st rid r } =
      st.replyStashedAt rid r := by
  unfold replyStasherSeen
  split
  · rfl
  · next h =>
    simp only [Bool.not_eq_true] at h
    rw [h]
    rfl

/-- **The busy holder reads the stash record only as seL4's eager clear
leaves it** (`replyStasherSeen`). -/
theorem busyReplyHolderCode_eq_stasherSeen (st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    busyReplyHolderCode st tid rid =
      match st.getReply? rid with
      | none => 0
      | some r =>
        match r.caller with
        | some c => if c = tid then 0 else c.val + 1
        | none =>
          if replyStasherSeen st rid r = tid.val + 1 then 0 else replyStasherSeen st rid r := by
  unfold busyReplyHolderCode replyStasherSeen
  rcases st.getReply? rid with _ | r
  · rfl
  · simp only []
    rcases r.caller with _ | c
    · by_cases h : st.replyStashedAt rid r = true
      · simp [h]
      · simp [h]
    · rfl

/-- A reply's busy code never names the receiver that reads it. -/
theorem busyReplyHolderCode_ne_self (st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : busyReplyHolderCode st tid rid ≠ tid.val + 1 := by
  unfold busyReplyHolderCode
  split
  · omega
  · split
    · rename_i c _
      split
      · omega
      · rename_i hne
        intro h
        apply hne
        have e : c.val = tid.val := by omega
        cases c; cases tid; simp_all
    · split
      · split
        · omega
        · assumption
      · omega

/-- The thread a reply is busy with is never the receiver that names it. -/
theorem busyReplyHolder?_ne {st : SystemState} {tid : SeLe4n.ThreadId}
    {replyId? : Option SeLe4n.ReplyId} {holder : SeLe4n.ThreadId}
    (h : busyReplyHolder? st tid replyId? = some holder) : holder ≠ tid := by
  intro hEq
  subst hEq
  unfold busyReplyHolder? at h
  cases replyId? with
  | none => cases h
  | some rid =>
    simp only at h
    have hN := busyReplyHolderCode_ne_self st holder rid
    revert h hN
    cases busyReplyHolderCode st holder rid with
    | zero => intro h; cases h
    | succ k => intro h hN; cases h; exact hN rfl

end SeLe4n.Kernel
