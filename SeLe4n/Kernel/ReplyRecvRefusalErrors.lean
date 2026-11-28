/-
  seLe4n — The refused reply-receive's errors are not capability lookups' (WS-SX SX34)
-/
import SeLe4n.Platform.FFI

/-!
A refused `.replyRecv` (WS-SX SX34) reports the state its refusing step stopped
in.  The seam's capability-fault decision reads the reply capability's lookup
on that state and raises a fault only for a refusal that IS that lookup's
failure (`receiveReplyFaults`).  This module states the other half of that
decision: every refusal the transition makes after its reply leg comes from
the receive leg or the dequeued caller's donation, and none of the steps they
run looks a capability up, so none of their refusals is a `failedLookup`.
Each lemma below is one step's statement, built on the steps it calls.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- Whether a refusal is a capability lookup's (`failedLookup`). -/
def isFailedLookupError : KernelError → Bool
  | .failedLookup _ _ => true
  | _ => false

/-- `storeObject`'s refusals are not capability lookups'. -/
theorem storeObject_error_notLookup {id : SeLe4n.ObjId} {o : KernelObject} {st : SystemState}
    {e : KernelError} (h : storeObject id o st = .error e) :
    isFailedLookupError e = false := by
  unfold storeObject at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals (cases h; rfl)

/-- `modifyTcb`'s refusals are not capability lookups'. -/
theorem modifyTcb_error_notLookup {st : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    {e : KernelError} (h : modifyTcb st t f = .error e) :
    isFailedLookupError e = false := by
  unfold modifyTcb at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup])
        | split))

/-- `storeTcbQueueLinks`'s refusals are not capability lookups'. -/
theorem storeTcbQueueLinks_error_notLookup {st : SystemState} {t : SeLe4n.ThreadId} {a b c}
    {e : KernelError} (h : storeTcbQueueLinks st t a b c = .error e) :
    isFailedLookupError e = false := by
  unfold storeTcbQueueLinks at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [modifyTcb_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [modifyTcb_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [modifyTcb_error_notLookup])
        | split))

/-- `endpointQueuePopHead`'s refusals are not capability lookups'. -/
theorem endpointQueuePopHead_error_notLookup {ep : SeLe4n.ObjId} {q : Bool} {st : SystemState}
    {e : KernelError} (h : endpointQueuePopHead ep q st = .error e) :
    isFailedLookupError e = false := by
  unfold endpointQueuePopHead at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup])
        | split))

/-- `endpointQueueEnqueue`'s refusals are not capability lookups'. -/
theorem endpointQueueEnqueue_error_notLookup {ep : SeLe4n.ObjId} {q : Bool} {t : SeLe4n.ThreadId} {st : SystemState}
    {e : KernelError} (h : endpointQueueEnqueue ep q t st = .error e) :
    isFailedLookupError e = false := by
  unfold endpointQueueEnqueue at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        storeTcbQueueLinks_error_notLookup])
        | split))

/-- `storeTcbIpcStateAndMessage`'s refusals are not capability lookups'. -/
theorem storeTcbIpcStateAndMessage_error_notLookup {st : SystemState} {t : SeLe4n.ThreadId} {s m}
    {e : KernelError} (h : storeTcbIpcStateAndMessage st t s m = .error e) :
    isFailedLookupError e = false := by
  unfold storeTcbIpcStateAndMessage at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [modifyTcb_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [modifyTcb_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [modifyTcb_error_notLookup])
        | split))

/-- `SystemState.linkReply`'s refusals are not capability lookups'. -/
theorem linkReply_error_notLookup {r : SeLe4n.ReplyId} {c : SeLe4n.ThreadId} {st : SystemState}
    {e : KernelError} (h : SystemState.linkReply r c st = .error e) :
    isFailedLookupError e = false := by
  unfold SystemState.linkReply at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup])
        | split))

/-- `SystemState.linkCallerReply`'s refusals are not capability lookups'. -/
theorem linkCallerReply_error_notLookup {c : SeLe4n.ThreadId} {r : SeLe4n.ReplyId} {st : SystemState}
    {e : KernelError} (h : SystemState.linkCallerReply c r st = .error e) :
    isFailedLookupError e = false := by
  unfold SystemState.linkCallerReply at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        linkReply_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        linkReply_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        linkReply_error_notLookup])
        | split))

/-- `storeDonationHeadClear`'s refusals are not capability lookups'. -/
theorem storeDonationHeadClear_error_notLookup {x} {st : SystemState}
    {e : KernelError} (h : storeDonationHeadClear x st = .error e) :
    isFailedLookupError e = false := by
  unfold storeDonationHeadClear at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup])
        | split))

/-- `storeReplyReHead`'s refusals are not capability lookups'. -/
theorem storeReplyReHead_error_notLookup {sc} {x} {st : SystemState}
    {e : KernelError} (h : storeReplyReHead sc x st = .error e) :
    isFailedLookupError e = false := by
  unfold storeReplyReHead at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup])
        | split))

/-- `storeDonationHeadPop`'s refusals are not capability lookups'. -/
theorem storeDonationHeadPop_error_notLookup {sc} {x} {st : SystemState}
    {e : KernelError} (h : storeDonationHeadPop sc x st = .error e) :
    isFailedLookupError e = false := by
  unfold storeDonationHeadPop at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeDonationHeadClear_error_notLookup,
        storeReplyReHead_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeDonationHeadClear_error_notLookup,
        storeReplyReHead_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeDonationHeadClear_error_notLookup,
        storeReplyReHead_error_notLookup])
        | split))

/-- `donationHeadOf?`'s refusals are not capability lookups'. -/
theorem donationHeadOf_error_notLookup {st : SystemState} {a b}
    {e : KernelError} (h : donationHeadOf? st a b = .error e) :
    isFailedLookupError e = false := by
  unfold donationHeadOf? at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals (cases h; rfl)

/-- `replyStackOuterCaller?`'s refusals are not capability lookups'. -/
theorem replyStackOuterCaller_error_notLookup {st : SystemState} {a}
    {e : KernelError} (h : replyStackOuterCaller? st a = .error e) :
    isFailedLookupError e = false := by
  unfold replyStackOuterCaller? at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [donationHeadOf_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [donationHeadOf_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [donationHeadOf_error_notLookup])
        | split))

/-- `returnDonatedSchedContext`'s refusals are not capability lookups'. -/
theorem returnDonatedSchedContext_error_notLookup {st : SystemState} {a b c d}
    {e : KernelError} (h : returnDonatedSchedContext st a b c d = .error e) :
    isFailedLookupError e = false := by
  unfold returnDonatedSchedContext at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup])
        | split))

/-- `keepDonatedSchedContext`'s refusals are not capability lookups'. -/
theorem keepDonatedSchedContext_error_notLookup {st : SystemState} {a b c}
    {e : KernelError} (h : keepDonatedSchedContext st a b c = .error e) :
    isFailedLookupError e = false := by
  unfold keepDonatedSchedContext at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup])
        | split))

/-- `returnDonatedSchedContextResolved`'s refusals are not capability lookups'. -/
theorem returnDonatedSchedContextResolved_error_notLookup {st : SystemState} {a b c}
    {e : KernelError} (h : returnDonatedSchedContextResolved st a b c = .error e) :
    isFailedLookupError e = false := by
  unfold returnDonatedSchedContextResolved at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [replyStackOuterCaller_error_notLookup,
        returnDonatedSchedContext_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [replyStackOuterCaller_error_notLookup,
        returnDonatedSchedContext_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [replyStackOuterCaller_error_notLookup,
        returnDonatedSchedContext_error_notLookup])
        | split))

/-- `keepDonatedSchedContextResolved`'s refusals are not capability lookups'. -/
theorem keepDonatedSchedContextResolved_error_notLookup {st : SystemState} {a b}
    {e : KernelError} (h : keepDonatedSchedContextResolved st a b = .error e) :
    isFailedLookupError e = false := by
  unfold keepDonatedSchedContextResolved at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [replyStackOuterCaller_error_notLookup,
        keepDonatedSchedContext_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [replyStackOuterCaller_error_notLookup,
        keepDonatedSchedContext_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [replyStackOuterCaller_error_notLookup,
        keepDonatedSchedContext_error_notLookup])
        | split))

/-- `popHeldReplyHead`'s refusals are not capability lookups'. -/
theorem popHeldReplyHead_error_notLookup {st : SystemState} {a b c}
    {e : KernelError} (h : popHeldReplyHead st a b c = .error e) :
    isFailedLookupError e = false := by
  unfold popHeldReplyHead at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [returnDonatedSchedContextResolved_error_notLookup,
        keepDonatedSchedContextResolved_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [returnDonatedSchedContextResolved_error_notLookup,
        keepDonatedSchedContextResolved_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [returnDonatedSchedContextResolved_error_notLookup,
        keepDonatedSchedContextResolved_error_notLookup])
        | split))

/-- `cleanupPreReceiveDonationChecked`'s refusals are not capability lookups'. -/
theorem cleanupPreReceiveDonationChecked_error_notLookup {st : SystemState} {a}
    {e : KernelError} (h : cleanupPreReceiveDonationChecked st a = .error e) :
    isFailedLookupError e = false := by
  unfold cleanupPreReceiveDonationChecked at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [popHeldReplyHead_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [popHeldReplyHead_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [popHeldReplyHead_error_notLookup])
        | split))

/-- `cleanupPreReceiveDonationMigrated`'s refusals are not capability lookups'. -/
theorem cleanupPreReceiveDonationMigrated_error_notLookup {st : SystemState} {a}
    {e : KernelError} (h : cleanupPreReceiveDonationMigrated st a = .error e) :
    isFailedLookupError e = false := by
  unfold cleanupPreReceiveDonationMigrated at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [cleanupPreReceiveDonationChecked_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [cleanupPreReceiveDonationChecked_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [cleanupPreReceiveDonationChecked_error_notLookup])
        | split))

/-- `storeDonationFramePush`'s refusals are not capability lookups'. -/
theorem storeDonationFramePush_error_notLookup {a b c d} {st : SystemState}
    {e : KernelError} (h : storeDonationFramePush a b c d st = .error e) :
    isFailedLookupError e = false := by
  unfold storeDonationFramePush at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup])
        | split))

/-- `donationPushFrame?`'s refusals are not capability lookups'. -/
theorem donationPushFrame_error_notLookup {st : SystemState} {a}
    {e : KernelError} (h : donationPushFrame? st a = .error e) :
    isFailedLookupError e = false := by
  unfold donationPushFrame? at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals (cases h; rfl)

/-- `donationPushRefusal?`'s refusals are not capability lookups'. -/
theorem donationPushRefusal_some_notLookup {st : SystemState} {a b c} {e : KernelError}
    (h : donationPushRefusal? st a b c = some e) : isFailedLookupError e = false := by
  unfold donationPushRefusal? at h
  repeat' (first | (cases h; done) | (cases h; rfl) | split at h)

/-- `donateSchedContext`'s refusals are not capability lookups'. -/
theorem donateSchedContext_error_notLookup {st : SystemState} {a b c}
    {e : KernelError} (h : donateSchedContext st a b c = .error e) :
    isFailedLookupError e = false := by
  unfold donateSchedContext at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup,
        storeDonationFramePush_error_notLookup,
        donationPushFrame_error_notLookup,
        donationPushRefusal_some_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup,
        storeDonationFramePush_error_notLookup,
        donationPushFrame_error_notLookup,
        donationPushRefusal_some_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [storeObject_error_notLookup,
        storeDonationHeadPop_error_notLookup,
        donationHeadOf_error_notLookup,
        storeDonationFramePush_error_notLookup,
        donationPushFrame_error_notLookup,
        donationPushRefusal_some_notLookup])
        | split))

/-- `donateSchedContextValid`'s refusals are not capability lookups'. -/
theorem donateSchedContextValid_error_notLookup {st : SystemState} {a b c}
    {e : KernelError} (h : donateSchedContextValid st a b c = .error e) :
    isFailedLookupError e = false := by
  unfold donateSchedContextValid at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [donateSchedContext_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [donateSchedContext_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [donateSchedContext_error_notLookup])
        | split))

/-- `applyCallDonation`'s refusals are not capability lookups'. -/
theorem applyCallDonation_error_notLookup {st : SystemState} {a b}
    {e : KernelError} (h : applyCallDonation st a b = .error e) :
    isFailedLookupError e = false := by
  unfold applyCallDonation at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [donateSchedContextValid_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [donateSchedContextValid_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [donateSchedContextValid_error_notLookup])
        | split))

/-- `applyCallDonationOnCore`'s refusals are not capability lookups'. -/
theorem applyCallDonationOnCore_error_notLookup {st : SystemState} {a b c d}
    {e : KernelError} (h : applyCallDonationOnCore st a b c d = .error e) :
    isFailedLookupError e = false := by
  unfold applyCallDonationOnCore at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [applyCallDonation_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [applyCallDonation_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [applyCallDonation_error_notLookup])
        | split))

/-- `applyRendezvousCallDonation`'s refusals are not capability lookups'. -/
theorem applyRendezvousCallDonation_error_notLookup {st : SystemState} {a b}
    {e : KernelError} (h : applyRendezvousCallDonation st a b = .error e) :
    isFailedLookupError e = false := by
  unfold applyRendezvousCallDonation at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | solve_by_elim [applyCallDonationOnCore_error_notLookup]
    | (cases h; rfl)
    | (cases h; solve_by_elim [applyCallDonationOnCore_error_notLookup])
    | (cases h; rename_i hh; revert hh; repeat' (first
        | (intro hh; cases hh; done)
        | (intro hh; cases hh; rfl)
        | (intro hh; solve_by_elim [applyCallDonationOnCore_error_notLookup])
        | split))

theorem endpointReceiveDualOnCore_error_notLookup {ep : SeLe4n.ObjId} {r : SeLe4n.ThreadId}
    {rid : Option SeLe4n.ReplyId} {c : CoreId} {st s : SystemState} {e : KernelError}
    (h : endpointReceiveDualOnCore ep r rid c st = (s, .error e)) : isFailedLookupError e = false := by
  unfold endpointReceiveDualOnCore at h
  repeat' (first | (cases h; done) | (cases h; rfl) | (dsimp only at h) | split at h)
  all_goals first
    | (cases h; rfl)
    | (cases h; solve_by_elim [storeObject_error_notLookup, endpointQueuePopHead_error_notLookup,
        endpointQueueEnqueue_error_notLookup, storeTcbIpcStateAndMessage_error_notLookup,
        linkCallerReply_error_notLookup, cleanupPreReceiveDonationMigrated_error_notLookup])

theorem endpointReceiveDualWithCapsOnCore_error_notLookup {ep : SeLe4n.ObjId} {r : SeLe4n.ThreadId}
    {rid : Option SeLe4n.ReplyId} {c : CoreId} {st s : SystemState} {e : KernelError}
    (h : endpointReceiveDualWithCapsOnCore ep r rid c st = (s, .error e)) :
    isFailedLookupError e = false := by
  unfold endpointReceiveDualWithCapsOnCore at h
  dsimp only at h
  cases hL : endpointReceiveDualOnCore ep r rid c st with
  | mk sL res =>
    rw [hL] at h
    cases res with
    | error e' =>
      cases h
      exact endpointReceiveDualOnCore_error_notLookup hL
    | ok v =>
      dsimp only at h
      split at h
      · cases h
      · rw [receiveTransferCaps_eq_done] at h
        cases h

theorem endpointReplyRecvAnsweringBodyR_error_notLookup
    {answer : Option Architecture.FaultReplyOutcome}
    {epId : SeLe4n.ObjId} {tid : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {core : CoreId}
    {rs : SeLe4n.ThreadId} {req : Option (Capability × Array SeLe4n.CPtr)}
    {target : Option (TCB × Option CSpaceAddr)} {st s : SystemState} {e : KernelError}
    (hInv : st.objects.invExt) (hA : replyRecvPopAdmits st rid prevCaller = true)
    (h : endpointReplyRecvAnsweringBodyR answer epId tid rid prevCaller msg core rs req target st =
      .error (e, s)) :
    s = st ∨ isFailedLookupError e = false := by
  unfold endpointReplyRecvAnsweringBodyR at h
  generalize hR : endpointReplyOnCore tid prevCaller msg core st = R at h
  obtain ⟨st1, r1⟩ := R
  cases r1 with
  | error e1 =>
    have hSt := endpointReplyOnCore_error_state (e := e1) (by rw [hR])
    rw [hR] at hSt
    cases h; exact Or.inl hSt
  | ok sgi =>
  obtain ⟨⟨ret?, popped⟩, hPop⟩ := replyRecvPopDonation_ok_of_admits (replier := tid) (msg := msg)
    (core := core) hInv (by rw [hR]) hA
  rw [hR] at hPop
  dsimp only at hPop h
  have hPopR : replyRecvPopDonationR rid prevCaller st1 = .ok (ret?, popped) := by
    have := replyRecvPopDonationR_eq rid prevCaller st1
    rw [hPop] at this
    cases hq : replyRecvPopDonationR rid prevCaller st1 with
    | error es => rw [hq] at this; cases this
    | ok r => rw [hq] at this; cases this; rfl
  rw [hPopR] at h
  dsimp only at h
  refine Or.inr ?_
  generalize receiveTransferCapsDone req none target popped = D at h
  obtain ⟨xs, st1p⟩ := D
  dsimp only at h
  generalize hV : endpointReceiveDualWithCapsOnCore epId tid (some rid) core _ = V at h
  obtain ⟨st2, r2⟩ := V
  cases r2 with
  | error e2 => cases h; exact endpointReceiveDualWithCapsOnCore_error_notLookup hV
  | ok v =>
  obtain ⟨next, summary, sgi'⟩ := v
  dsimp only at h
  split at h
  · rename_i e3 s3 hD
    cases h
    have hSpec := replyRecvPostReceiveDonationR_eq tid rs next core ret? st2
    rw [hD] at hSpec
    unfold replyRecvPostReceiveDonation at hSpec
    revert hSpec
    repeat' (first | (intro hh; cases hh; done) | split)
    all_goals first
      | solve_by_elim [applyRendezvousCallDonation_error_notLookup]
      | (intro hh; simp only [Except.mapError] at hh
         first
           | solve_by_elim [applyRendezvousCallDonation_error_notLookup]
           | (cases hh <;> solve_by_elim [applyRendezvousCallDonation_error_notLookup])
           | cases hh)
  · cases h

/-- **A refused reply-receive transition refuses on its entry state or with an
error that is not a capability lookup's** (WS-SX SX34). -/
theorem replyRecvTransferOnCore_refusal_notLookup (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
    (grant : Bool) (core : CoreId) (st : SystemState) (hInv : st.objects.invExt)
    {ke : KernelError}
    (h : replyRecvTransferOnCore epId tid rid prevCaller label msg grant core st = .error ke) :
    replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st = st ∨
      isFailedLookupError ke = false := by
  have hEq := replyRecvTransferOnCoreR_eq epId tid rid prevCaller label msg grant core st
  cases hRR : replyRecvTransferOnCoreR epId tid rid prevCaller label msg grant core st with
  | ok r => rw [hRR, h] at hEq; cases hEq
  | error es =>
    obtain ⟨e, s⟩ := es
    rw [hRR, h] at hEq
    cases hEq
    have hS : replyRecvTransferStoppedState epId tid rid prevCaller label msg grant core st = s := by
      unfold replyRecvTransferStoppedState; rw [hRR]
    rw [hS]
    unfold replyRecvTransferOnCoreR at hRR
    split at hRR
    · rename_i hA
      exact endpointReplyRecvAnsweringBodyR_error_notLookup hInv hA hRR
    · cases hRR; exact Or.inl rfl

/-- The capability-fault decision answers no fault where the operand lookup
succeeds on the spilled state and the refusal is not a capability lookup's: the
reply capability's fault is raised only for its own lookup failure. -/
theorem syscallCapFaultAt_none_of_lookup_ok_of_notLookup (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (st s : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (tcb : TCB)
    (decoded : SeLe4n.Model.SyscallDecodeResult) (inRecv : Bool)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        (threadOperationCode st tid layout tcb.registerContext)
        st tid layout tcb.registerContext 32 = .ok decoded)
    (hIpc : Platform.FFI.capFaultReceivePhase? decoded.syscallId = some inRecv)
    (hLookup : syscallOperandLookup decoded.syscallId
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st = .ok ())
    (hKe : isFailedLookupError ke = false) :
    Platform.FFI.syscallCapFaultAt ctx layout st s tid ke = none := by
  have hR : ∀ g, receiveReplyFaults g decoded s ke = none := by
    intro g
    unfold receiveReplyFaults
    split
    · rename_i lf _
      split
      · rename_i hK; subst hK; cases hKe
      · rfl
    · rfl
  simp only [Platform.FFI.syscallCapFaultAt, SystemState.getObject?_eq_getElem, hTcb, hDec, hIpc,
    hLookup, hR]

/-- **The checked entry's refusal on a reply-receive that reached its answering
report is the transition's refusal**: every check the entry runs before the
transition passed (`ReplyRecvAnsweringEntry`), so the entry refuses with the
error the transition refuses with. -/
theorem ReplyRecvAnsweringEntry.entry_error {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} (hA : ReplyRecvAnsweringEntry ctx e st s)
    (h : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke) :
    ∃ (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (epId : SeLe4n.ObjId)
      (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage) (grant : Bool)
      (cap : Capability),
      st.scheduler.currentOnCore e = some tid ∧
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        (threadOperationCode st tid SeLe4n.arm64DefaultLayout tcb.registerContext)
        st tid SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
      decoded.syscallId = .replyRecv ∧
      syscallOperandLookup decoded.syscallId
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st = .ok () ∧
      s = replyRecvEntryRefusalTaint ctx tid decoded.msgInfo.extraCaps decoded.replyCPtr cap st
        (replyRecvTransferStoppedState epId tid rid c label msg grant e st) ∧
      replyRecvTransferOnCore epId tid rid c label msg grant e st = .error ke := by
  obtain ⟨tid, tcb, decoded, ref, hCtx, hCur, hObj, hDec, hRR, hRef, cap, epId, rid, c, badge,
    grant, hCap, hRes, hAcc, hRight, hTgt, hFlow, hXc, hR, hAns, hSig, hS⟩ := hA
  have hObj' : st.objects[tid.toObjId]? = some (.tcb tcb) := by
    rw [← SystemState.getObject?_eq_getElem]; exact hObj
  have hRoot : tcb.spaceCells[0] = callerCspaceRoot st tid := by
    simp only [callerCspaceRoot, hObj]
  have hResolve : syscallResolveCap
      { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
        requiredRight := syscallRequiredRight .replyRecv } st = .ok (cap, st) := by
    simp only [syscallResolveCap, SyscallGate.lookupSlot_mk, hRef, hCap, hRes, Bool.false_eq_true,
      ↓reduceIte]
  have hXc0 : ∀ n, syscallExtraCapCount .replyRecv n = 0 := fun _ => rfl
  refine ⟨tid, tcb, decoded, epId, rid, c, _, _, grant, cap, hCur, hObj', hDec, hRR, ?_, hS, ?_⟩
  · rw [hRR]
    simp only [syscallOperandLookup, hResolve, hXc0, callerExtraCapsFault?_zero, receiveGateRefuses,
      hAcc, hRight, receiveBoundRefuses, Bool.not_true, Bool.false_or, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, syscallReceivesOnCap, Bool.true_and, Bool.or_false]
  have hRegs : lookupThreadRegisterContext tid st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  have hResR := resolveReplyRecvReplyR_eq st tid
    { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
      requiredRight := syscallRequiredRight .replyRecv } decoded rfl hRoot
  rw [hR] at hResR
  have hEp : replyRecvReceiveEndpoint ctx
      { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
        requiredRight := syscallRequiredRight .replyRecv } tid st = .ok epId := by
    simp only [replyRecvReceiveEndpoint, hResolve, hAcc, hRight, hTgt, hFlow, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
  have hOrd := dispatchSyscallArmChecked_of_entryOrder (ctx := ctx) (decoded := decoded) (tid := tid)
    (executingCore := e) (xf := none) (st := st) (Or.inr (Or.inr ⟨epId, hEp⟩)) (fun _ => rfl)
  simp only [syscallEntryChecked, hCtx, hCur, hRegs, hDec, Bool.false_eq_true, ↓reduceIte,
    dispatchSyscallChecked, ne_eq, not_true_eq_false, hRR, reduceCtorEq, hObj, hOrd, syscallInvokeTyped,
    decodedExtraCapsFault?, hResolve, hXc0, callerExtraCapsFault?_zero, hAcc, Bool.not_true,
    hRight, dispatchWithCapChecked, dispatchCapabilityOnly, hTgt, hFlow, hXc, ← hResR, hAns,
    hSig] at h
  revert h
  cases replyRecvTransferOnCore epId tid rid c decoded.msgInfo.label _ grant e st with
  | error e' => intro h; cases h; rfl
  | ok r => intro h; cases h

/-- **A reply-receive that reached its answering report raises no capability
fault but on the state it was handed**: the fault decision reads the operand's
lookup, which passed, and the reply's lookup on the reported state, which
faults only on a lookup's refusal, and the transition's refusals are lookups'
only where it stopped where it started (`replyRecvTransferOnCore_refusal_notLookup`). -/
theorem ReplyRecvAnsweringEntry.capFault_none {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId}
    (hA : ReplyRecvAnsweringEntry ctx e st s) (hInv : st.objects.invExt)
    (hCur : st.scheduler.currentOnCore e = some t)
    (h : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke) :
    s = st ∨ Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st s t ke = none := by
  obtain ⟨tid, tcb, decoded, epId, rid, c, label, msg, grant, cap, hCur', hObj, hDec, hRR, hLookup,
    hS, hErr⟩ := hA.entry_error h
  rw [hCur] at hCur'
  cases hCur'
  rcases replyRecvTransferOnCore_refusal_notLookup epId t rid c label msg grant e st hInv hErr with
    hSt | hKe
  · exact Or.inl (hS.trans (by rw [hSt]; exact replyRecvEntryRefusalTaint_self ..))
  · exact Or.inr (syscallCapFaultAt_none_of_lookup_ok_of_notLookup ctx _ st s t ke tcb decoded true
      hObj hDec (by rw [hRR]; rfl) hLookup hKe)

/-- `ReplyRecvAnsweringEntry.capFault_none` on the dispatch the entry runs on the
running thread's decoded frame. -/
theorem ReplyRecvAnsweringEntry.capFault_none_of_dispatch {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId} {tcb : TCB}
    {decoded : SyscallDecodeResult}
    (hA : ReplyRecvAnsweringEntry ctx e st s) (hInv : st.objects.invExt)
    (hCur : st.scheduler.currentOnCore e = some t)
    (hObj : st.getObject? t.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
      (threadOperationCode st t SeLe4n.arm64DefaultLayout tcb.registerContext) st t
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (h : dispatchSyscallChecked ctx decoded t e st = .error ke) :
    s = st ∨ Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st s t ke = none := by
  refine hA.capFault_none hInv hCur ?_
  obtain ⟨_, _, _, _, hCtx, -⟩ := hA
  have hRegs : lookupThreadRegisterContext t st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  simp only [syscallEntryChecked, hCtx, hCur, hRegs, hDec, Bool.false_eq_true, ↓reduceIte]
  exact h

/-- **A refusal that raises a capability fault reported the state it was handed
or its busy reply's cancel** (WS-SX SX34): a reply-receive's stopped state
other than the state handed to it raises none
(`ReplyRecvAnsweringEntry.capFault_none`); a reply-receive whose receive
capability was looked up after its reply (WS-SX SX36.1) raises its fault on the
state the after-reply composite stopped in (`ReplyRecvAfterReplyEntry`). -/
theorem cancelReceiveBusyReply_cases_of_fault {ctx : LabelingContext} {e : CoreId}
    {st : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId} {f : Fault}
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore e = some t)
    (hE : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke)
    (hF : Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st
      (cancelReceiveBusyReply ctx e st) t ke = some f) :
    cancelReceiveBusyReply ctx e st = st ∨
      (∃ (tid holder : SeLe4n.ThreadId), st.scheduler.currentOnCore e = some tid ∧
        holder ≠ tid ∧ cancelReceiveBusyReply ctx e st = cancelReplyHolder st holder e) ∨
      ReplyRecvAfterReplyEntry ctx e st (cancelReceiveBusyReply ctx e st) := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with h | h | hA | hB
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases hA.capFault_none hInv hCur hE with h | h
    · exact Or.inl h
    · rw [h] at hF
      cases hF
  · exact Or.inr (Or.inr hB)

/-- **A reply-receive's composite whose receive endpoint refuses after its reply
refuses with that endpoint's refusal, or where it started**: the pop refuses only
where it is not admitted (the state handed in), the reply leg's refusals report
the state handed in (`endpointReplyOnCore_error_state`), and the receive's
endpoint, read on a state that keeps the entry's CNodes (`CNodeSlotsKept`),
refuses with `eR`. -/
theorem replyRecvTransferThenR_refused_error
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {label : Nat} {msg : IpcMessage}
    {grant : Bool} {core : CoreId} {st s : SystemState} {eR ke : KernelError}
    (hInv : st.objects.invExt) (hEp : ∀ s, CNodeSlotsKept st s → recvEp s = .error eR)
    (h : replyRecvTransferThenR recvEp tid rid prevCaller label msg grant core st =
      .error (ke, s)) :
    s = st ∨ ke = eR := by
  unfold replyRecvTransferThenR at h
  cases hA : replyRecvPopAdmits st rid prevCaller
  · simp only [hA, Bool.false_eq_true, ↓reduceIte, Except.error.injEq, Prod.mk.injEq] at h
    exact Or.inl h.2.symm
  simp only [hA, ↓reduceIte] at h
  revert h
  generalize replyRecvCallerFaultAnswer? st prevCaller label msg = a
  generalize replyRecvLegMessage a msg = m
  generalize (recordedReplyServer? st prevCaller).getD tid = rs
  generalize (if a.isSome = true then none else replyCapRequest st tid grant) = req
  generalize receiverCapTarget? st prevCaller = target
  intro h
  unfold endpointReplyRecvAnsweringBodyThenR at h
  have hInvR := endpointReplyOnCore_preserves_objects_invExt tid prevCaller m core st hInv
  generalize hR : endpointReplyOnCore tid prevCaller m core st = R at h hInvR
  obtain ⟨st1, r1⟩ := R
  cases r1 with
  | error e1 =>
    have hSt := endpointReplyOnCore_error_state (e := e1) (by rw [hR])
    rw [hR] at hSt
    simp only [Except.error.injEq, Prod.mk.injEq] at h
    exact Or.inl (h.2.symm.trans hSt)
  | ok sgi =>
  obtain ⟨⟨ret?, popped⟩, hPop⟩ := replyRecvPopDonation_ok_of_admits (replier := tid) (msg := m)
    (core := core) hInv (by rw [hR]) hA
  rw [hR] at hPop
  dsimp only at hPop h
  have hPopR : replyRecvPopDonationR rid prevCaller st1 = .ok (ret?, popped) := by
    have := replyRecvPopDonationR_eq rid prevCaller st1
    rw [hPop] at this
    cases hq : replyRecvPopDonationR rid prevCaller st1 with
    | error es => rw [hq] at this; cases this
    | ok r => rw [hq] at this; cases this; rfl
  rw [hPopR] at h
  dsimp only at h
  have hXo := receiveTransferCaps_eq_done req none target popped
  generalize receiveTransferCapsDone req none target popped = D at hXo h
  obtain ⟨xs, st1p⟩ := D
  dsimp only at h
  rw [hEp _ (replyRecvReplyStep_cnodeSlotsKept (answer := a) hInv hR hPop hXo)] at h
  simp only [Except.error.injEq, Prod.mk.injEq] at h
  exact Or.inr h.1.symm

/-- **An answering reply-receive whose receive endpoint refuses after its reply
refuses with that endpoint's refusal, or where it started**, on both of its
branches (`replyRecvTransferThenR_refused_error`; the signal arm's reply leg
refuses with the state handed in). -/
theorem replyRecvAnsweringThenR_refused_error {ctx : LabelingContext}
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {core : CoreId} {rid : SeLe4n.ReplyId}
    {prevCaller : SeLe4n.ThreadId} {replyBadge : Option SeLe4n.Badge} {replyGrant : Bool}
    {st s : SystemState} {eR ke : KernelError}
    (hInv : st.objects.invExt) (hEp : ∀ s, CNodeSlotsKept st s → recvEp s = .error eR)
    (h : replyRecvAnsweringThenR ctx recvEp decoded tid core rid prevCaller replyBadge replyGrant
      st = .error (ke, s)) :
    s = st ∨ ke = eR := by
  unfold replyRecvAnsweringThenR at h
  by_cases hSig : receiveCompletesSignal ctx st tid = true
  · rw [if_pos hSig] at h
    unfold replyRecvCompletesSignalArmThenR at h
    cases hR : replyTransferOnCoreChecked ctx tid prevCaller
        (replyRecvReplyMessageInfo decoded.msgInfo.label
          { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
              decoded.msgInfo, badge := replyBadge })
        (Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo)
        { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
            decoded.msgInfo, badge := replyBadge } replyGrant core st true with
    | error e1 =>
      rw [hR] at h
      simp only [Except.error.injEq, Prod.mk.injEq] at h
      exact Or.inl h.2.symm
    | ok p =>
      obtain ⟨⟨⟩, st1⟩ := p
      rw [hR] at h
      dsimp only at h
      rw [hEp st1 (replyTransferOnCoreChecked_cnodeSlotsKept hInv hR)] at h
      simp only [Except.error.injEq, Prod.mk.injEq] at h
      exact Or.inr h.1.symm
  · rw [if_neg hSig] at h
    cases hY : replyRecvTransferThenR recvEp tid rid prevCaller decoded.msgInfo.label
        { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
            decoded.msgInfo, badge := replyBadge } replyGrant core st with
    | ok r =>
      obtain ⟨_, _⟩ := r
      rw [hY] at h
      simp at h
    | error es =>
      rw [hY] at h
      try dsimp only at h
      cases h
      exact replyRecvTransferThenR_refused_error hInv hEp hY

/-- **A receive endpoint whose capability resolved refuses at its type, its right
or its flow, never at a lookup.** -/
theorem replyRecvReceiveEndpoint_error_notLookup {ctx : LabelingContext} {gate : SyscallGate}
    {tid : SeLe4n.ThreadId} {st : SystemState} {cap : Capability} {eR : KernelError}
    (hRc : syscallResolveCap gate st = .ok (cap, st))
    (h : replyRecvReceiveEndpoint ctx gate tid st = .error eR) :
    isFailedLookupError eR = false := by
  unfold replyRecvReceiveEndpoint at h
  rw [hRc] at h
  dsimp only at h
  cases h1 : syscallTargetAccepted .replyRecv st cap <;>
    cases h2 : cap.hasRight gate.requiredRight <;>
    simp only [h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      Except.error.injEq] at h
  all_goals try (subst h; rfl)
  cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h <;>
    try (simp only [Except.error.injEq] at h; subst h; rfl)
  rename_i epId
  cases hF : endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) <;>
    simp only [hF, Bool.false_eq_true, ↓reduceIte, Except.error.injEq, reduceCtorEq] at h
  subst h
  rfl

/-! ### The after-reply refusal's taint (WS-SX SX36) -/

/-- **A taint-word write keeps every CNode**: the objects agree off their taint
words, and a CNode holds none. -/
theorem CNodeSlotsKept.of_objectsAgreeOffTaint {st st' : SystemState}
    (h : st.objectsAgreeOffTaint st') : CNodeSlotsKept st st' := by
  refine ⟨fun id => ?_, fun id cn hC => ⟨cn, ?_, rfl, fun _ c hL => ⟨c, hL, rfl, fun _ => rfl⟩⟩⟩
  · have hk := h id
    have e : ∀ o : KernelObject, o.eraseTaint.objectType = o.objectType :=
      fun o => KernelObject.objectType_withTaintWords o {}
    cases h1 : st.objects[id]? <;> cases h2 : st'.objects[id]? <;> rw [h1, h2] at hk <;>
      simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hk ⊢
    rename_i o1 o2
    rw [← e o2, hk, e o1]
  · rw [SystemState.getCNode?_eq_some_iff] at hC ⊢
    exact (SystemState.objectsAgreeOffTaint.inert_iff h id (o := .cnode cn) rfl).2 hC

/-- **The after-reply refusal's taint is taint steps**: every property each
taint step keeps carries from `s0` to the state the refusal reports. -/
theorem taintSteps_of_afterReplyRefusal {ctx : LabelingContext} {decoded : SyscallDecodeResult}
    {tid : SeLe4n.ThreadId} {e : CoreId} {gate : SyscallGate} {rid : SeLe4n.ReplyId}
    {prev : SeLe4n.ThreadId} {badge : Option SeLe4n.Badge} {grant : Bool} {st s0 : SystemState} :
    ∀ P : SystemState → Prop,
      (∀ (plan : TaintPlan) (pre x : SystemState), P x → P (applySyscallTaint plan pre x)) →
        P s0 → P (replyRecvAfterReplyRefusalTaint ctx decoded tid e gate rid prev badge grant st s0) :=
  fun P hStep h => replyRecvAfterReplyRefusalTaint_induct P hStep h

/-- Taint steps keep every CNode. -/
theorem CNodeSlotsKept.of_taintSteps {s0 s : SystemState}
    (h : ∀ P : SystemState → Prop,
      (∀ (plan : TaintPlan) (pre x : SystemState), P x → P (applySyscallTaint plan pre x)) →
        P s0 → P s) :
    CNodeSlotsKept s0 s :=
  CNodeSlotsKept.of_objectsAgreeOffTaint (h (fun x => s0.objectsAgreeOffTaint x)
    (fun plan pre x hx => hx.trans (applySyscallTaint_objectsAgreeOffTaint plan pre x))
    (SystemState.objectsAgreeOffTaint.refl s0))

/-- The caller an answering reply answers waits for it. -/
theorem replyRecvCallerAwaitsReply_of_answering {ctx : LabelingContext} {gate : SyscallGate}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {st : SystemState}
    {rid : SeLe4n.ReplyId} {prev : SeLe4n.ThreadId} {badge : Option SeLe4n.Badge} {grant : Bool}
    (h : replyRecvAnsweringReply? ctx gate decoded tid st = some (rid, prev, badge, grant)) :
    replyRecvCallerAwaitsReply st prev = true := by
  unfold replyRecvAnsweringReply? at h
  split at h
  · cases h
  · split at h
    · rename_i c _
      split at h
      · rename_i hAns
        cases h
        unfold replyRecvReplyAnswers at hAns
        exact (Bool.and_eq_true_iff.1 hAns).2
      · cases h
    · cases h

/-- **The state the receive capability is read on keeps every CNode** of the
entry state: the reply step writes none. -/
theorem replyRecvAnsweringReadState?_cnodeSlotsKept {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {e : CoreId} {rid : SeLe4n.ReplyId}
    {prev : SeLe4n.ThreadId} {badge : Option SeLe4n.Badge} {grant : Bool} {st sA : SystemState}
    (hInv : st.objects.invExt)
    (h : replyRecvAnsweringReadState? ctx decoded tid e rid prev badge grant st = some sA) :
    CNodeSlotsKept st sA := by
  unfold replyRecvAnsweringReadState? at h
  dsimp only at h
  split at h
  · split at h
    · rename_i st1 hR
      cases h
      exact replyTransferOnCoreChecked_cnodeSlotsKept hInv hR
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i ret sA' hL
        cases h
        unfold replyRecvAnsweringReplyLegR at hL
        revert hL
        generalize hR : endpointReplyOnCore _ _ _ _ st = R
        obtain ⟨st1, r1⟩ := R
        cases r1 with
        | error e1 => intro hL; cases hL
        | ok sgi =>
          dsimp only
          cases hP : replyRecvPopDonationR rid prev st1 with
          | error es => intro hL; cases hL
          | ok p =>
            obtain ⟨ret', st1q⟩ := p
            intro hL
            dsimp only at hL
            have hPop : replyRecvPopDonation rid prev st1 = .ok (ret', st1q) := by
              rw [← replyRecvPopDonationR_eq, hP]; rfl
            have hXo := receiveTransferCaps_eq_done
              (if (replyRecvCallerFaultAnswer? st prev decoded.msgInfo.label
                { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
                    decoded.msgInfo, badge := badge }).isSome = true then none
                else replyCapRequest st tid grant) none (receiverCapTarget? st prev) st1q
            generalize receiveTransferCapsDone _ none (receiverCapTarget? st prev) st1q = D at hXo hL
            obtain ⟨xs, st1p⟩ := D
            simp only [Except.ok.injEq, Prod.mk.injEq] at hL
            obtain ⟨-, rfl⟩ := hL
            exact replyRecvReplyStep_cnodeSlotsKept hInv hR hPop hXo
    · cases h

/-- **A refusal on the state handed in reports it as it is**, where the
receive's endpoint refuses on every state keeping the entry's CNodes: the reply
was not delivered (its caller still waits) and the receive leg did not run. -/
theorem replyRecvAfterReplyRefusalTaint_self {ctx : LabelingContext}
    {decoded : SyscallDecodeResult} {tid : SeLe4n.ThreadId} {e : CoreId} {gate : SyscallGate}
    {rid : SeLe4n.ReplyId} {prev : SeLe4n.ThreadId} {badge : Option SeLe4n.Badge} {grant : Bool}
    {st : SystemState} {eR : KernelError} (hInv : st.objects.invExt)
    (hAns : replyRecvAnsweringReply? ctx gate decoded tid st = some (rid, prev, badge, grant))
    (hEp : ∀ x, CNodeSlotsKept st x → replyRecvReceiveEndpoint ctx gate tid x = .error eR) :
    replyRecvAfterReplyRefusalTaint ctx decoded tid e gate rid prev badge grant st st = st := by
  unfold replyRecvAfterReplyRefusalTaint
  cases hS : replyRecvAnsweringReadState? ctx decoded tid e rid prev badge grant st with
  | none =>
    dsimp only
    unfold replyRecvRefusalTaint
    rw [if_pos (replyRecvCallerAwaitsReply_of_answering hAns)]
  | some sA =>
    dsimp only
    rw [hEp sA (replyRecvAnsweringReadState?_cnodeSlotsKept hInv hS)]
    dsimp only
    unfold replyRecvRefusalTaint
    rw [if_pos (replyRecvCallerAwaitsReply_of_answering hAns)]

/-- **A reply-receive whose receive the entry refused after its reply raises no
capability fault where its receive capability resolved on entry, or reports the
state it was handed** (WS-SX SX36.1): the entry's refusal is the after-reply
composite's (`dispatchReplyRecvAfterReply`); that refuses where it started, or
with the receive endpoint's refusal on a state that keeps the entry's CNodes,
which, the capability resolved, is a type, right or flow refusal and never a
lookup's, so the fault decision on the reported state raises none
(`syscallCapFaultAt_none_of_lookup_ok_of_notLookup`). -/
theorem ReplyRecvAfterReplyEntry.capFault_none_of_dispatch {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId} {tcb : TCB}
    {decoded : SyscallDecodeResult} {cap : Capability}
    (hA : ReplyRecvAfterReplyEntry ctx e st s) (hInv : st.objects.invExt)
    (hCur : st.scheduler.currentOnCore e = some t)
    (hObj : st.getObject? t.toObjId = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
      (threadOperationCode st t SeLe4n.arm64DefaultLayout tcb.registerContext) st t
      SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded)
    (hLookup : syscallOperandLookup decoded.syscallId
        { callerId := t, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) st = .ok ())
    (hRc : syscallResolveCap (replyRecvCallerGate decoded t tcb) st = .ok (cap, st))
    (hAcc : syscallTargetAccepted .replyRecv st cap = true)
    (h : dispatchSyscallChecked ctx decoded t e st = .error ke) :
    s = st ∨ Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st s t ke = none := by
  obtain ⟨tid', tcb', decoded', gate, rid, prev, badge, grant, -, hCur', hObj', hDec', hRR, hRef,
    hS⟩ := hA
  rw [hCur] at hCur'
  cases hCur'
  rw [hObj] at hObj'
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hObj'
  subst hObj'
  rw [hDec] at hDec'
  cases hDec'
  obtain ⟨tcbR, eR, hTR, rfl, hAnsR, hEpR⟩ := replyRecvRefusedOnEntry?_some hRef
  rw [hObj] at hTR
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTR
  subst hTR
  -- the entry's refusal is the after-reply composite's
  have hD : replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t)
      decoded t e rid prev badge grant st = .error ke := by
    unfold dispatchSyscallChecked at h
    rw [if_neg (by rw [hCur]; simp), if_neg (by rw [hRR]; decide), hObj] at h
    dsimp only at h
    rw [dispatchSyscallArmChecked_replyRecv hRR] at h
    unfold dispatchReplyRecvAfterReply at h
    have hG : ({ callerId := t, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } : SyscallGate) = replyRecvCallerGate decoded t tcb := rfl
    rw [hG, hAnsR] at h
    dsimp only at h
    rw [hEpR] at h
    dsimp only at h
    cases hT : replyRecvAnsweringThen ctx
        (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
        badge grant st with
    | ok r => rw [hT] at h; simp at h
    | error e' => rw [hT] at h; simp only [Except.error.injEq] at h; rw [h]
  have hEq := replyRecvAnsweringThenR_eq ctx
    (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
    badge grant st
  rw [hD] at hEq
  cases hY : replyRecvAnsweringThenR ctx
      (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
      badge grant st with
  | ok r => rw [hY] at hEq; cases hEq
  | error es =>
    obtain ⟨ke', s'⟩ := es
    rw [hY] at hEq
    simp only [Except.mapError, Except.error.injEq] at hEq
    subst hEq
    have hSs : s = replyRecvAfterReplyRefusalTaint ctx decoded t e
        (replyRecvCallerGate decoded t tcb) rid prev badge grant st s' := by
      rw [hS]; unfold RefusalCarrying.stoppedState; rw [hY]
    have hEpK : ∀ x, CNodeSlotsKept st x →
        replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t x = .error eR :=
      fun x hK => (replyRecvReceiveEndpoint_eq_of_cnodeSlotsKept (ctx := ctx) (tid := t) hK hRc
        hAcc).trans hEpR
    rcases replyRecvAnsweringThenR_refused_error hInv hEpK hY with hSt | hKe
    · subst hSt
      exact Or.inl (hSs.trans (replyRecvAfterReplyRefusalTaint_self hInv hAnsR hEpK))
    · subst hKe
      refine Or.inr (syscallCapFaultAt_none_of_lookup_ok_of_notLookup ctx _ st s t _ tcb decoded true
        (by rw [← SystemState.getObject?_eq_getElem]; exact hObj) hDec (by rw [hRR]; rfl) hLookup ?_)
      exact replyRecvReceiveEndpoint_error_notLookup hRc hEpR


/-! ### Where an after-reply report raises its capability fault (WS-SX SX36.1) -/

/-- The nothing-received outcome keeps every CNode: the holder-only deschedule
and the priority-inheritance walk write run links and priorities alone. -/
theorem replyRecvNothingReceived_cnodeSlotsKept (rs : SeLe4n.ThreadId) (c : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (s : SystemState)
    (hInv : s.objects.invExt) : CNodeSlotsKept s (replyRecvNothingReceived rs c ret? s) := by
  unfold replyRecvNothingReceived
  cases ret? with
  | none => exact propagatePipChainCrossCore_cnodeSlotsKept _ _ _ _ hInv
  | some p =>
    obtain ⟨_, holder⟩ := p
    dsimp only
    by_cases hK : s.scheduler.currentOnCore c = some holder
    · rw [descheduleKeepingCurrentOnCore_of_current s holder c hK]
      exact propagatePipChainCrossCore_cnodeSlotsKept _ _ _ _ hInv
    · rw [descheduleKeepingCurrentOnCore_of_not_current s holder c hK]
      exact (descheduleAtPlacement_cnodeSlotsKept s holder).trans
        (propagatePipChainCrossCore_cnodeSlotsKept _ _ _ _
          (descheduleAtPlacement_preserves_objects_invExt _ _ hInv))

/-- The holder's deschedule after a refused post-receive donation keeps every CNode. -/
theorem replyRecvHolderDeschedule_cnodeSlotsKept (t holder : SeLe4n.ThreadId) (s : SystemState) :
    CNodeSlotsKept s (replyRecvHolderDeschedule t holder s) := by
  unfold replyRecvHolderDeschedule
  split
  · exact .refl _
  · exact descheduleAtPlacement_cnodeSlotsKept s holder

/-- **The after-reply composite's refusals past a receive endpoint that
resolved are no capability lookup's**: where the endpoint read on the answered
state resolves, the composite refuses where it started or in the receive leg
or the post-receive donation, neither of which refuses at a lookup. -/
theorem endpointReplyRecvAnsweringBodyThenR_error_notLookup_of_ok
    {answer : Option Architecture.FaultReplyOutcome}
    {recvEp : SystemState → Except KernelError SeLe4n.ObjId} {tid : SeLe4n.ThreadId}
    {rid : SeLe4n.ReplyId} {prevCaller : SeLe4n.ThreadId} {msg : IpcMessage} {core : CoreId}
    {rs : SeLe4n.ThreadId} {req : Option (Capability × Array SeLe4n.CPtr)}
    {target : Option (TCB × Option CSpaceAddr)} {st s : SystemState} {e : KernelError}
    (hInv : st.objects.invExt) (hA : replyRecvPopAdmits st rid prevCaller = true)
    (hOk : ∀ ret? popped, replyRecvPopDonation rid prevCaller
        (endpointReplyOnCore tid prevCaller msg core st).1 = .ok (ret?, popped) →
      ∃ epId, recvEp (replyRecvAnswerCaller answer (receiveTransferCapsDone req none target popped).2
        prevCaller (receiveTransferCapsDone req none target popped).1.capInfo) = .ok epId)
    (h : endpointReplyRecvAnsweringBodyThenR answer recvEp tid rid prevCaller msg core rs req target
      st = .error (e, s)) :
    s = st ∨ isFailedLookupError e = false := by
  unfold endpointReplyRecvAnsweringBodyThenR at h
  generalize hR : endpointReplyOnCore tid prevCaller msg core st = R at h hOk
  obtain ⟨st1, r1⟩ := R
  cases r1 with
  | error e1 =>
    have hSt := endpointReplyOnCore_error_state (e := e1) (by rw [hR])
    rw [hR] at hSt
    cases h; exact Or.inl hSt
  | ok sgi =>
  obtain ⟨⟨ret?, popped⟩, hPop⟩ := replyRecvPopDonation_ok_of_admits (replier := tid) (msg := msg)
    (core := core) hInv (by rw [hR]) hA
  rw [hR] at hPop
  dsimp only at hPop h hOk
  have hPopR : replyRecvPopDonationR rid prevCaller st1 = .ok (ret?, popped) := by
    have := replyRecvPopDonationR_eq rid prevCaller st1
    rw [hPop] at this
    cases hq : replyRecvPopDonationR rid prevCaller st1 with
    | error es => rw [hq] at this; cases this
    | ok r => rw [hq] at this; cases this; rfl
  rw [hPopR] at h
  dsimp only at h
  obtain ⟨epId, hE⟩ := hOk ret? popped hPop
  refine Or.inr ?_
  generalize receiveTransferCapsDone req none target popped = D at h hE
  obtain ⟨xs, st1p⟩ := D
  dsimp only at h hE
  rw [hE] at h
  dsimp only at h
  generalize hV : endpointReceiveDualWithCapsOnCore epId tid (some rid) core _ = V at h
  obtain ⟨st2, r2⟩ := V
  cases r2 with
  | error e2 => cases h; exact endpointReceiveDualWithCapsOnCore_error_notLookup hV
  | ok v =>
  obtain ⟨next, summary, sgi'⟩ := v
  dsimp only at h
  split at h
  · rename_i e3 s3 hD
    cases h
    have hSpec := replyRecvPostReceiveDonationR_eq tid rs next core ret? st2
    rw [hD] at hSpec
    unfold replyRecvPostReceiveDonation at hSpec
    revert hSpec
    repeat' (first | (intro hh; cases hh; done) | split)
    all_goals first
      | solve_by_elim [applyRendezvousCallDonation_error_notLookup]
      | (intro hh; simp only [Except.mapError] at hh
         first
           | solve_by_elim [applyRendezvousCallDonation_error_notLookup]
           | (cases hh <;> solve_by_elim [applyRendezvousCallDonation_error_notLookup])
           | cases hh)
  · cases h

/-- The capability-fault decision answers no fault where the reply-receive's
receive capability was looked up after its reply, that lookup succeeds on the
reported state, and the refusal is not a capability lookup's. -/
theorem syscallCapFaultAt_none_of_afterReply (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout)
    (st s : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (tcb : TCB)
    (decoded : SeLe4n.Model.SyscallDecodeResult) (inRecv : Bool)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        (threadOperationCode st tid layout tcb.registerContext)
        st tid layout tcb.registerContext 32 = .ok decoded)
    (hIpc : Platform.FFI.capFaultReceivePhase? decoded.syscallId = some inRecv)
    (hFlag : replyRecvLooksUpAfterReply ctx decoded tid st = true)
    (hLookup : syscallOperandLookup decoded.syscallId
        { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
          requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) s = .ok ())
    (hKe : isFailedLookupError ke = false) :
    Platform.FFI.syscallCapFaultAt ctx layout st s tid ke = none := by
  have hR : ∀ g, receiveReplyFaults g decoded s ke = none := by
    intro g
    unfold receiveReplyFaults
    split
    · rename_i lf _
      split
      · rename_i hK; subst hK; cases hKe
      · rfl
    · rfl
  unfold Platform.FFI.syscallCapFaultAt
  simp only [SystemState.getObject?_eq_getElem, hTcb, hDec, hIpc]
  split
  · simp only [hFlag, ↓reduceIte, hLookup, hR]
  · simp only [hR]

/-- **The checked entry's refusal on an after-reply report is the after-reply
composite's**: the entry's checks passed, its dispatch is the answering
reply-receive in seL4's order (`dispatchReplyRecvAfterReply`), and its refusal
carries the report. -/
theorem ReplyRecvAfterReplyEntry.composite_error {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} (hA : ReplyRecvAfterReplyEntry ctx e st s)
    (h : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke) :
    ∃ (tid : SeLe4n.ThreadId) (tcb : TCB) (decoded : SyscallDecodeResult) (rid : SeLe4n.ReplyId)
      (prev : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) (grant : Bool),
      st.scheduler.currentOnCore e = some tid ∧
      st.objects[tid.toObjId]? = some (.tcb tcb) ∧
      SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
        (threadOperationCode st tid SeLe4n.arm64DefaultLayout tcb.registerContext) st tid
        SeLe4n.arm64DefaultLayout tcb.registerContext 32 = .ok decoded ∧
      decoded.syscallId = .replyRecv ∧
      replyRecvRefusedOnEntry? ctx decoded tid st =
        some (replyRecvCallerGate decoded tid tcb, rid, prev, badge, grant) ∧
      ∃ s0, replyRecvAnsweringThenR ctx
        (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded tid tcb) tid)
        decoded tid e rid prev badge grant st = .error (ke, s0) ∧
      s = replyRecvAfterReplyRefusalTaint ctx decoded tid e (replyRecvCallerGate decoded tid tcb)
        rid prev badge grant st s0 := by
  obtain ⟨t, tcb, decoded, gate, rid, prev, badge, grant, hCtx, hCur, hObj, hDec, hRR, hRef,
    hS⟩ := hA
  obtain ⟨tcbR, eR, hTR, rfl, hAnsR, hEpR⟩ := replyRecvRefusedOnEntry?_some hRef
  rw [hObj] at hTR
  simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTR
  subst hTR
  have hRegs : lookupThreadRegisterContext t st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  simp only [syscallEntryChecked, hCtx, hCur, hRegs, hDec, Bool.false_eq_true, ↓reduceIte] at h
  have hD : replyRecvAnsweringThen ctx (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t)
      decoded t e rid prev badge grant st = .error ke := by
    unfold dispatchSyscallChecked at h
    rw [if_neg (by rw [hCur]; simp), if_neg (by rw [hRR]; decide), hObj] at h
    dsimp only at h
    rw [dispatchSyscallArmChecked_replyRecv hRR] at h
    unfold dispatchReplyRecvAfterReply at h
    have hG : ({ callerId := t, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr, requiredRight := syscallRequiredRight decoded.syscallId } : SyscallGate) = replyRecvCallerGate decoded t tcb := rfl
    rw [hG, hAnsR] at h
    dsimp only at h
    rw [hEpR] at h
    dsimp only at h
    cases hT : replyRecvAnsweringThen ctx
        (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
        badge grant st with
    | ok r => rw [hT] at h; simp at h
    | error e' => rw [hT] at h; simp only [Except.error.injEq] at h; rw [h]
  have hEq := replyRecvAnsweringThenR_eq ctx
    (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
    badge grant st
  rw [hD] at hEq
  refine ⟨t, tcb, decoded, rid, prev, badge, grant, hCur,
    (by rw [← SystemState.getObject?_eq_getElem]; exact hObj), hDec, hRR, hRef, ?_⟩
  cases hY : replyRecvAnsweringThenR ctx
      (replyRecvReceiveEndpoint ctx (replyRecvCallerGate decoded t tcb) t) decoded t e rid prev
      badge grant st with
  | ok r => rw [hY] at hEq; cases hEq
  | error es =>
    obtain ⟨ke', s'⟩ := es
    rw [hY] at hEq
    simp only [Except.mapError, Except.error.injEq] at hEq
    subst hEq
    refine ⟨s', rfl, ?_⟩
    rw [hS]; unfold RefusalCarrying.stoppedState; rw [hY]

/-- **Where an after-reply report raises a capability fault** (WS-SX SX36.1):
on the state the entry was handed; on the state the signal arm's reply leg
left (its receive capability, read there, refused); or on the nothing-received
outcome of the state the caller's answer left after the reply leg, the pop and
the reply's transfer (the receive's endpoint, read there, refused).  Where the
receive's endpoint resolved after the reply, the receive legs ran, the lookup
on the reported state resolves (they keep every CNode), and their refusals are
no lookup's, so no fault is raised. -/
theorem ReplyRecvAfterReplyEntry.fault_stop {ctx : LabelingContext} {e : CoreId}
    {st s : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId} {f : Fault}
    (hA : ReplyRecvAfterReplyEntry ctx e st s) (hInv : st.objects.invExt)
    (hCur : st.scheduler.currentOnCore e = some t)
    (hE : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke)
    (hF : Platform.FFI.syscallCapFaultAt ctx SeLe4n.arm64DefaultLayout st s t ke = some f) :
    ∃ s0, (∀ P : SystemState → Prop,
      (∀ (plan : TaintPlan) (pre x : SystemState), P x → P (applySyscallTaint plan pre x)) →
        P s0 → P s) ∧ (s0 = st ∨
      (∃ (prev : SeLe4n.ThreadId) (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
        (msg : IpcMessage) (grant : Bool) (st1 : SystemState),
        replyTransferOnCoreChecked ctx t prev mi regs msg grant e st true = .ok ((), st1) ∧ s0 = st1) ∨
      (∃ (rid : SeLe4n.ReplyId) (prev : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage)
        (grant : Bool) (st1 popped st1p : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
        (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (xs : CapTransferSummary),
        endpointReplyOnCore t prev
            (replyRecvLegMessage (replyRecvCallerFaultAnswer? st prev label msg) msg) e st =
          (st1, .ok sgi) ∧
        replyRecvPopDonation rid prev st1 = .ok (ret?, popped) ∧
        replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st prev label msg) st t prev grant
          popped = .ok (xs, st1p) ∧
        s0 = replyRecvNothingReceived ((recordedReplyServer? st prev).getD t) e ret?
          (replyRecvAnswerCaller (replyRecvCallerFaultAnswer? st prev label msg) st1p prev
            xs.capInfo))) := by
  obtain ⟨tid, tcb, decoded, rid, prev, badge, grant, hCur', hObj, hDec, hRR, hRef, s0, hY, hW⟩ :=
    hA.composite_error hE
  have hTS : ∀ P : SystemState → Prop,
      (∀ (plan : TaintPlan) (pre x : SystemState), P x → P (applySyscallTaint plan pre x)) →
        P s0 → P s := hW ▸ taintSteps_of_afterReplyRefusal
  refine ⟨s0, hTS, ?_⟩
  rw [hCur] at hCur'
  cases hCur'
  unfold replyRecvAnsweringThenR at hY
  dsimp only at hY
  by_cases hSig : receiveCompletesSignal ctx st t = true
  · rw [if_pos hSig] at hY
    unfold replyRecvCompletesSignalArmThenR at hY
    revert hY
    split
    · intro hY; cases hY; exact Or.inl rfl
    · rename_i st1 hR1
      intro hY
      refine Or.inr (Or.inl ⟨prev, _, _, _, grant, st1, hR1, ?_⟩)
      revert hY
      repeat' (first | (intro hY; cases hY; done) | split)
      all_goals (intro hY; cases hY; rfl)
  rw [if_neg hSig] at hY
  revert hY
  split
  · intro hY; cases hY
  rename_i es hT
  intro hY
  cases hY
  unfold replyRecvTransferThenR at hT
  by_cases hNotAdmitted : replyRecvPopAdmits st rid prev = false
  · simp only [hNotAdmitted, Bool.false_eq_true, ↓reduceIte] at hT; cases hT; exact Or.inl rfl
  have hAd : replyRecvPopAdmits st rid prev = true := by simpa using hNotAdmitted
  simp only [hAd, ↓reduceIte] at hT
  have hSt := endpointReplyRecvAnsweringBodyThenR_stopped hInv hAd hT
  rcases hSt with ⟨-, hS0⟩ | ⟨sgi, ret?, popped, hR1, hPop, hInvP, hTail⟩
  · exact Or.inl hS0
  rcases hTail with ⟨eR, -, hSN⟩ | ⟨epId, hEok, hRan⟩
  · refine Or.inr (Or.inr ⟨rid, prev, decoded.msgInfo.label, _, grant, _, popped, _, sgi, ret?, _,
      Prod.ext rfl hR1, hPop, ?_, hSN⟩)
    rw [replyRecvReplyTransfer_eq_receiveTransferCaps]
    exact receiveTransferCaps_eq_done _ _ _ _
  rcases endpointReplyRecvAnsweringBodyThenR_error_notLookup_of_ok hInv hAd
      (fun r p hp => by rw [hPop] at hp; cases hp; exact ⟨epId, hEok⟩) hT with hS0 | hKe
  · exact Or.inl hS0
  -- the receive legs ran: no fault
  exfalso
  have hDn := receiveTransferCaps_eq_done
    (if (replyRecvCallerFaultAnswer? st prev decoded.msgInfo.label
        { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := badge }).isSome = true
      then none else replyCapRequest st t grant) none (receiverCapTarget? st prev) popped
  generalize receiveTransferCapsDone _ none (receiverCapTarget? st prev) popped = D at hDn hEok hRan
  obtain ⟨xs, st1p⟩ := D
  dsimp only at hEok hRan
  have hIp : st1p.objects.invExt := receiveTransferCaps_objects_invExt hInvP hDn
  have hIa := replyRecvAnswerCaller_preserves_objects_invExt
    (replyRecvCallerFaultAnswer? st prev decoded.msgInfo.label
      { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := badge })
    st1p prev xs.capInfo hIp
  have K1 := receiveReturnSchedContext_cnodeSlotsKept true _ t hIa
  have hIX := receiveReturnSchedContext_objects_invExt true _ t hIa
  have K2 := endpointReceiveDualWithCapsOnCore_cnodeSlotsKept (endpointId := epId) (receiver := t)
    (replyId := some rid) (executingCore := e) hIX
  have hI2 := endpointReceiveDualWithCapsOnCore_preserves_objects_invExt epId t (some rid) e _ hIX
  have hK : CNodeSlotsKept (replyRecvAnswerCaller (replyRecvCallerFaultAnswer? st prev
      decoded.msgInfo.label
      { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs decoded.msgInfo, badge := badge })
      st1p prev xs.capInfo) s0 := by
    rcases hRan with hS | ⟨st2, next, summary, sgi', hV, hS⟩
    · rw [hS]; exact K1.trans (K2.trans (replyRecvNothingReceived_cnodeSlotsKept _ _ _ _ hI2))
    rw [hV] at K2 hI2
    rcases hS with hS | ⟨sc, holder, -, hS⟩
    · rw [hS]; exact K1.trans (K2.trans (replyRecvNothingReceived_cnodeSlotsKept _ _ _ _ hI2))
    rw [hS]
    exact K1.trans (K2.trans ((replyRecvHolderDeschedule_cnodeSlotsKept _ _ _).trans
      (replyRecvNothingReceived_cnodeSlotsKept _ _ _ _
        (by
          unfold replyRecvHolderDeschedule
          split
          · exact hI2
          · exact descheduleAtPlacement_preserves_objects_invExt _ _ hI2))))
  obtain ⟨cap, hL, hAcc, -⟩ := replyRecvReceiveEndpoint_resolved hEok
  obtain ⟨_, -, -, hRt, -⟩ := syscallLookupCap_implies_capability_held _ _ cap _ hL
  obtain ⟨hResS, hAccS⟩ := replyRecvReceiveCap_of_cnodeSlotsKept (hK.trans (CNodeSlotsKept.of_taintSteps hTS)) _
    (syscallResolveCap_of_lookup _ _ cap _ hL) hAcc
  have hLs : syscallOperandLookup decoded.syscallId
      { callerId := t, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr,
        requiredRight := syscallRequiredRight decoded.syscallId }
      (syscallExtraCapCount decoded.syscallId decoded.msgInfo.extraCaps) s = .ok () := by
    unfold replyRecvCallerGate at hResS hRt
    rw [hRR] at hResS hRt ⊢
    have hXc0 : ∀ n, syscallExtraCapCount .replyRecv n = 0 := fun _ => rfl
    simp only [syscallOperandLookup, hResS, hXc0, callerExtraCapsFault?_zero, receiveGateRefuses,
      hAccS, hRt, receiveBoundRefuses, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, syscallReceivesOnCap, Bool.or_false]
  rw [syscallCapFaultAt_none_of_afterReply ctx _ st s t ke tcb decoded true hObj hDec
    (by rw [hRR]; rfl) (replyRecvLooksUpAfterReply_of_some hRR hRef) hLs hKe] at hF
  cases hF

end SeLe4n.Kernel
