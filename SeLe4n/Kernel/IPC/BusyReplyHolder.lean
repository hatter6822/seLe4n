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

end SeLe4n.Kernel
