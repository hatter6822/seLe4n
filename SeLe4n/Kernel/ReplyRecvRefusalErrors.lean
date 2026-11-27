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
theorem syscallCapFaultAt_none_of_lookup_ok_of_notLookup (layout : SeLe4n.SyscallRegisterLayout)
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
    Platform.FFI.syscallCapFaultAt layout st s tid ke = none := by
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
      (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId) (label : Nat) (msg : IpcMessage) (grant : Bool),
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
      s = replyRecvTransferStoppedState epId tid rid c label msg grant e st ∧
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
  refine ⟨tid, tcb, decoded, epId, rid, c, _, _, grant, hCur, hObj', hDec, hRR, ?_, hS, ?_⟩
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
  simp only [syscallEntryChecked, hCtx, hCur, hRegs, hDec, Bool.false_eq_true, ↓reduceIte,
    dispatchSyscallChecked, ne_eq, not_true_eq_false, hRR, reduceCtorEq, hObj, syscallInvokeTyped,
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
    s = st ∨ Platform.FFI.syscallCapFaultAt SeLe4n.arm64DefaultLayout st s t ke = none := by
  obtain ⟨tid, tcb, decoded, epId, rid, c, label, msg, grant, hCur', hObj, hDec, hRR, hLookup, hS,
    hErr⟩ := hA.entry_error h
  rw [hCur] at hCur'
  cases hCur'
  rcases replyRecvTransferOnCore_refusal_notLookup epId t rid c label msg grant e st hInv hErr with
    hSt | hKe
  · exact Or.inl (hS.trans hSt)
  · exact Or.inr (syscallCapFaultAt_none_of_lookup_ok_of_notLookup _ st s t ke tcb decoded true
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
    s = st ∨ Platform.FFI.syscallCapFaultAt SeLe4n.arm64DefaultLayout st s t ke = none := by
  refine hA.capFault_none hInv hCur ?_
  obtain ⟨_, _, _, _, hCtx, -⟩ := hA
  have hRegs : lookupThreadRegisterContext t st = .ok (tcb.registerContext, st) := by
    simp only [lookupThreadRegisterContext, hObj]
  simp only [syscallEntryChecked, hCtx, hCur, hRegs, hDec, Bool.false_eq_true, ↓reduceIte]
  exact h

/-- **A refusal that raises a capability fault reported the state it was handed
or its busy reply's cancel** (WS-SX SX34): a reply-receive's stopped state
other than the state handed to it raises none
(`ReplyRecvAnsweringEntry.capFault_none`), so a consumer of the fault's
delivery takes the two cases it always took. -/
theorem cancelReceiveBusyReply_cases_of_fault {ctx : LabelingContext} {e : CoreId}
    {st : SystemState} {ke : KernelError} {t : SeLe4n.ThreadId} {f : Fault}
    (hInv : st.objects.invExt) (hCur : st.scheduler.currentOnCore e = some t)
    (hE : syscallEntryChecked ctx SeLe4n.arm64DefaultLayout e 32 st = .error ke)
    (hF : Platform.FFI.syscallCapFaultAt SeLe4n.arm64DefaultLayout st
      (cancelReceiveBusyReply ctx e st) t ke = some f) :
    cancelReceiveBusyReply ctx e st = st ∨
      ∃ (tid holder : SeLe4n.ThreadId), st.scheduler.currentOnCore e = some tid ∧
        holder ≠ tid ∧ cancelReceiveBusyReply ctx e st = cancelReplyHolder st holder e := by
  rcases cancelReceiveBusyReply_cases_holder ctx e st with h | h | hA
  · exact Or.inl h
  · exact Or.inr h
  · rcases hA.capFault_none hInv hCur hE with h | h
    · exact Or.inl h
    · rw [h] at hF
      cases hF

end SeLe4n.Kernel
