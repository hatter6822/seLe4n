/-
Copyright (c) 2025 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license.

WS-SM SM9.D.7-.D.12: **taint propagation** — how the causal provenance the
laundering detector reads gets onto the objects that hold declassified content.

Three things move a tag, and exactly three:

* **Origination.**  An authorized downgrade tags the object its content lands in
  and the subject that performed it, with that downgrade's own identity.
  Recovered from the trail's own diff (`newlyRecordedEvents`), so a *new*
  declassifying syscall originates tags the day it lands, without a planner of
  its own.
* **Ordinary delivery.**  IPC moves content between objects, so it moves tags:
  the sink joins the source's taint.  Every content-moving syscall declares its
  edges from the pre-state, in `contentFlowEdges`.
* **Destruction.**  A retype commits `storeObject target newObj` at the *same*
  id, so a framed retype would leave a destroyed object's tags on its unrelated
  replacement.  Retype **clears** (`retypeClearsTaint`).

**Where the write happens, and why there.**  `applySyscallTaint` runs once, at
the per-core syscall entry (`API.syscallEntryChecked`), on the state the
dispatch committed.  That is the SM7.F.5 seam one step later — the entry already
threads a projection-invisible model write (`tlbFillIpcBufferOnCore`) around the
dispatch for exactly this kind of bookkeeping — and it buys three things a
per-arm write does not:

* **one writer.**  `storeObject_declassificationTaint_eq` frames the field, so
  "this is the only writer" is a checkable fact rather than a reading of the
  call graph, and the Tier-1 content-flow gate can enforce it by reach.
* **no churn in the transitions.**  Every IPC transition's frame, invariant and
  non-interference surface is untouched, so the propagation adds no obligation
  to the ~1900-reference invariant surface.  In particular the declassification
  producers still write *only* the trail
  (`authorizeDeclassificationOnCore_frame`), which keeps SM8.C's rule true.
* **a classification whose domain is exhaustive of what it polices.**  Every
  live arm is a `SyscallId`, and `contentFlowClass` is total on it with no
  wildcard, so a new syscall is a missing case at elaboration.  §3.7 of the plan
  warns that totality over the wrong domain proves nothing — which is why the
  *sub*-transition question ("does any callee move content the declared edges do
  not cover?") is answered by reach, in
  `scripts/check_content_flow_coverage.py`, and not by this function.

**The direction the model errs in.**  Every planner over-approximates: a send
tags the endpoint *and* the rendezvous receiver even when the message carries
nothing, and a saturated taint names identities it never received.  For a
detector that is the safe direction — extra reports, never a missed chain.
-/
import SeLe4n.Kernel.InformationFlow.DeclassifiedSignal
import SeLe4n.Kernel.InformationFlow.Invariant
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.SyscallArgDecode

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  WS-SM SM9.D.7 — the classification
-- ============================================================================

/-- WS-SM SM9.D.7: **how a syscall moves declassified content.**

The classification the propagation planner branches on.  Total on `SyscallId`
with **no wildcard**, so a new syscall is a missing case at elaboration rather
than a silent `.inert`. -/
inductive ContentFlowClass where
  /-- Moves no content between distinct objects.  Either it writes no object at
      all, or its writes are confined to one object (so a taint edge would be a
      self-loop). -/
  | inert
  /-- Delivers content from one object to another; the edges are declared in
      `contentFlowEdges`. -/
  | movesContent
  /-- Destroys and re-creates an object at the same id, so its provenance must
      be **forgotten** rather than framed. -/
  | clearsProvenance
  deriving Repr, DecidableEq

/-- WS-SM SM9.D.7: **the classification of every syscall.**

Written as an exhaustive match with no wildcard: the enumeration is
`SyscallId`'s own, which is exhaustive of the live dispatch arms, so adding a
syscall without deciding how it moves content does not elaborate.

The `.inert` arms are not "assumed harmless".  Each falls into one of three
justified groups:

* **No object write at all** — `.serviceQuery`, `.auditRead`, the two VSpace
  maintenance calls (`.vspaceMap`/`.vspaceUnmap`/`.vspaceUnifyInstruction` move
  page-table entries and cache/TLB state, not object content), `.declassify`
  (which authorizes and records; it moves no bytes — that is SM8.C.9's own
  headline), `.auditDrain` (which removes trail entries).
* **Writes confined to one object** — the CSpace operations.  `cspaceCopy`,
  `cspaceMove`, `cspaceMint`, `cspaceDelete` and `mintReplyCap`
  all take the CNode from the *capability* and both slots from the decoded
  arguments (`src.cnode = dst.cnode = cnodeId`, verified at the arms), so source
  and sink are the same object and an edge would be a self-loop.
* **Scheduler and lifecycle state** — priorities, affinities, binding, suspend
  and resume move no content between objects; they move a thread's *scheduling*
  attributes.  `.tcbSetIPCBuffer` installs a buffer address, not its contents.

`.lifecycleRetype` is the sole `.clearsProvenance` arm, and the seven
content-moving arms are the IPC surface plus the declassifying signal. -/
def contentFlowClass : SyscallId → ContentFlowClass
  -- The IPC surface: a message or a badge crosses between objects.
  | .send => .movesContent
  | .receive => .movesContent
  | .call => .movesContent
  | .reply => .movesContent
  | .replyRecv => .movesContent
  | .notificationSignal => .movesContent
  | .notificationWait => .movesContent
  -- WS-SM SM9.C: the data-carrying declassification rides the notification path.
  | .declassifySignal => .movesContent
  -- WS-SM SM9.D.12: a retype re-purposes the object at the same id.
  | .lifecycleRetype => .clearsProvenance
  -- CSpace: both slots live in the capability's own CNode (verified at the
  -- arms), so any edge would be a self-loop.
  | .cspaceCopy => .inert
  | .cspaceMove => .inert
  | .cspaceMint => .inert
  | .cspaceDelete => .inert
  | .mintReplyCap => .inert
  -- VSpace and cache/TLB maintenance: page-table entries and cache lines, not
  -- object content.
  | .vspaceMap => .inert
  | .vspaceUnmap => .inert
  | .vspaceUnifyInstruction => .inert
  -- Scheduling attributes and thread lifecycle.
  | .tcbSuspend => .inert
  | .tcbResume => .inert
  | .tcbSetPriority => .inert
  | .tcbSetMCPriority => .inert
  | .tcbSetIPCBuffer => .inert
  | .tcbSetAffinity => .inert
  | .tcbBindNotification => .inert
  | .tcbUnbindNotification => .inert
  | .schedContextBind => .inert
  | .schedContextUnbind => .inert
  | .schedContextConfigure => .inert
  -- Services: a registration is a name, not content.
  | .serviceRegister => .inert
  | .serviceRevoke => .inert
  | .serviceQuery => .inert
  -- WS-SM SM8.C.9 / SM9.A: the declassification authority and the audit reader.
  | .declassify => .inert
  | .auditRead => .inert
  | .auditDrain => .inert

/-- WS-SM SM9.D.7: the classification is total — every syscall the ABI admits
has one, by construction.  Stated over `SyscallId.all` so a constructor added
without an arm fails `mem_all` as well as elaboration. -/
theorem contentFlowClass_total (sid : SyscallId) :
    contentFlowClass sid = .inert ∨ contentFlowClass sid = .movesContent ∨
      contentFlowClass sid = .clearsProvenance := by
  cases sid <;> simp [contentFlowClass]

/-- WS-SM SM9.D.7: exactly one syscall clears provenance, and it is the retype —
the arm SM9.D.12 requires to forget rather than frame. -/
theorem contentFlowClass_clears_iff (sid : SyscallId) :
    contentFlowClass sid = .clearsProvenance ↔ sid = .lifecycleRetype := by
  cases sid <;> simp [contentFlowClass]

/-- WS-SM SM9.D.7: the content-moving arms, named.  The list a reader checks
against the propagation planners below, and against the Tier-1 reach gate. -/
theorem contentFlowClass_moves_iff (sid : SyscallId) :
    contentFlowClass sid = .movesContent ↔
      (sid = .send ∨ sid = .receive ∨ sid = .call ∨ sid = .reply ∨ sid = .replyRecv ∨
        sid = .notificationSignal ∨ sid = .notificationWait ∨ sid = .declassifySignal) := by
  cases sid <;> simp [contentFlowClass]

-- ============================================================================
-- §2  WS-SM SM9.D.8-.D.11 — the edges
-- ============================================================================

/-- WS-SM SM9.D.8: **one content flow** — the sink joins the source's taint.

Directed, and read from the **pre**-state: the sources are what the objects held
before the transition ran, so a chain of edges within one syscall is a
simultaneous update rather than an order-dependent fold. -/
structure TaintFlowEdge where
  /-- The object receiving content. -/
  sink : SeLe4n.ObjId
  /-- The object the content came from. -/
  source : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- WS-SM SM9.D.7: **what one syscall does to the taint table** — the edges it
declares and the objects whose provenance it destroys.

Computed entirely from the pre-state and the decoded syscall, so the plan a
syscall runs is a function of what the caller asked for, never of what the
transition happened to do. -/
structure TaintPlan where
  /-- Content flows: `sink ⊔= source`, sources read from the pre-state. -/
  edges : List TaintFlowEdge := []
  /-- Objects whose provenance is destroyed (SM9.D.12: retype). -/
  cleared : List SeLe4n.ObjId := []
  deriving Repr, DecidableEq

/-- WS-SM SM9.D.7: the empty plan — what an `.inert` syscall runs. -/
def TaintPlan.inert : TaintPlan := {}

/-- WS-SM SM9.D.7: **the operand capability, resolved the way the dispatch
resolves it.**

The planner needs the object the caller named, and the entry has only the raw
`CPtr`.  This is the same resolution `syscallResolveCap` performs — caller's
TCB, its CSpace root, `resolveCapAddress`, then the slot — so the plan is keyed
on the object the arm acts on rather than on a second reading of the operand.

Shared with the SM9.B refusal seam (`Platform.FFI.refusedSignalReceiver?`),
which used to spell the same four steps out; one resolver means the two cannot
drift. -/
def syscallOperandCap? (st : SystemState) (tid : SeLe4n.ThreadId)
    (capPtr : SeLe4n.CPtr) : Option Capability :=
  match st.getTcb? tid with
  | none => none
  | some tcb =>
    match st.getCNode? tcb.cspaceRoot with
    | none => none
    | some rootCn =>
      match resolveCapAddress tcb.cspaceRoot capPtr rootCn.depth st with
      | .error _ => none
      | .ok ref => SystemState.lookupSlotCap st ref

/-- WS-SM SM9.D.11: **the capability-transfer sink.**

A message may carry capabilities, and `ipcUnwrapCaps` installs them into the
*receiver's* CSpace — a CNode, a different object from the receiver's TCB.  A
badge minted into a transferred capability is data, and a CNode is shared: a
second thread rooted at the same CSpace reads what the transfer installed
without ever touching the receiver's TCB, so tagging the TCB alone would lose
the link at exactly the point where the content becomes reachable by a third
subject.

Declared **unconditionally** for a resolved receiver rather than gated on the
message actually carrying capabilities.  The plan's own principle decides the
direction: for a detector, over-approximation is safe and under-approximation
is not, and the message is not in the decoded operand's hands at this point —
gating on it would mean re-deriving the sender's `pendingMessage`, which is
exactly the kind of duplicated computation that drifts.  A resolved receiver
whose TCB is absent contributes nothing, which is correct: no CSpace, no
install. -/
def capTransferTaintSinks (st : SystemState) (tid : SeLe4n.ThreadId)
    (receiver : SeLe4n.ThreadId) : List TaintFlowEdge :=
  match st.getTcb? receiver with
  | some rtcb => [{ sink := rtcb.cspaceRoot, source := tid.toObjId }]
  | none => []

/-- WS-SM SM9.D.8: **a sender's edges** — `.send` and `.call`.

The message leaves the sender, so it reaches the endpoint (where a blocking send
parks it) **and**, on a rendezvous, the receiver the transition wakes.  Both are
declared: which of the two actually happens depends on the endpoint's queue, and
naming both over-approximates in the safe direction.

The receiver is `receiveQ.head` at the pre-state, which is exactly the thread the
arms themselves compute as `wokenReceiver?`. -/
def senderTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) :
    List TaintFlowEdge :=
  { sink := epId, source := tid.toObjId } ::
    (match (st.getEndpoint? epId).bind (·.receiveQ.head) with
     | some receiver =>
         { sink := receiver.toObjId, source := tid.toObjId } ::
           capTransferTaintSinks st tid receiver
     | none => [])

/-- WS-SM SM9.D.8: **a receiver's edges** — `.receive` and `.replyRecv`.

Content reaches the receiver from the endpoint (a message parked by an earlier
blocking send) and, on a rendezvous, directly from the blocked sender
`sendQ.head` — the thread the arms compute as `wokenSender?`. -/
def receiverTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) :
    List TaintFlowEdge :=
  { sink := tid.toObjId, source := epId } ::
    (match (st.getEndpoint? epId).bind (·.sendQ.head) with
     | some sender => [{ sink := tid.toObjId, source := sender.toObjId }]
     | none => [])

/-- WS-SM SM9.D.9: **a replier's edge** — `.reply`.

The reply message travels from the replying server to the caller the reply
object records, which is the thread the arm resolves through `reply.caller`. -/
def replyTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    List TaintFlowEdge :=
  match (st.getReply? rid).bind (·.caller) with
  | some caller => [{ sink := caller.toObjId, source := tid.toObjId }]
  | none => []

/-- WS-SM SM9.D.10: **a signaller's edges** — `.notificationSignal` and
`.declassifySignal`.

The badge leaves the signaller for the notification, and — when a waiter or a
bound TCB is there to take it — on to that receiver.  The receiver is resolved
by `declassifiedSignalReceiver?`, the *same* function SM9.C's second-hop gate
and the SM9.B refusal seam use, so the object the plan tags is the object the
delivery reaches.

Both edges are declared because both orderings occur: with a waiter present the
badge reaches it in this step, and with none it sits on the notification until a
`.notificationWait` moves it (`waitTaintEdges`). -/
def signalTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) :
    List TaintFlowEdge :=
  { sink := nid, source := tid.toObjId } ::
    (match declassifiedSignalReceiver? st nid with
     | some receiver =>
         [ { sink := receiver.toObjId, source := tid.toObjId }
         , { sink := receiver.toObjId, source := nid } ]
     | none => [])

/-- WS-SM SM9.D.10: **a waiter's edge** — `.notificationWait`.

The signal-before-wait ordering is why this arm is not optional: with no waiter
present the signal leaves the badge pending on the notification, and it is the
*wait* that moves it to the waiter.  Omitting this edge would lose hop 1 in one
of the two orderings, and the §3.6 chain — downgrade, ordinary delivery,
downgrade — would go undetected exactly half the time. -/
def waitTaintEdges (tid : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) : List TaintFlowEdge :=
  [{ sink := tid.toObjId, source := nid }]

/-- WS-SM SM9.D.8-.D.11: **the edges a content-moving syscall declares.**

Keyed on the decoded syscall and the resolved operand, so the plan names the
object the arm acts on.  A capability that does not resolve, or resolves to the
wrong shape, declares nothing — which is correct rather than fail-open: the arm
itself rejects such a call with `.invalidCapability` before any content
moves. -/
def contentFlowEdges (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : List TaintFlowEdge :=
  match syscallOperandCap? st tid decoded.capAddr with
  | none => []
  | some cap =>
    match decoded.syscallId, cap.target with
    | .send, .object epId => senderTaintEdges st tid epId
    | .call, .object epId => senderTaintEdges st tid epId
    | .receive, .object epId => receiverTaintEdges st tid epId
    | .replyRecv, .object epId => receiverTaintEdges st tid epId
    | .reply, .replyCap rid => replyTaintEdges st tid rid
    | .notificationSignal, .object nid => signalTaintEdges st tid nid
    | .declassifySignal, .object nid => signalTaintEdges st tid nid
    | .notificationWait, .object nid => waitTaintEdges tid nid
    | _, _ => []

/-- WS-SM SM9.D.12: **what a retype destroys.**

The target comes from the decoded arguments rather than from the capability —
the retype's capability names the *authority*, and `args.targetObj` names the
object being re-purposed, exactly as the live arm reads it. -/
def retypeClearedObjects (decoded : SyscallDecodeResult) : List SeLe4n.ObjId :=
  match Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs decoded with
  | .error _ => []
  | .ok args => [args.targetObj]

/-- WS-SM SM9.D.7: **the plan a syscall runs**, from its classification. -/
def syscallTaintPlan (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : TaintPlan :=
  match contentFlowClass decoded.syscallId with
  | .inert => TaintPlan.inert
  | .movesContent => { edges := contentFlowEdges st tid decoded }
  | .clearsProvenance => { cleared := retypeClearedObjects decoded }

/-- WS-SM SM9.D.7: an inert syscall plans nothing — the property the reach gate
checks the *other* half of (that nothing it calls moves content either). -/
@[simp] theorem syscallTaintPlan_inert (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (h : contentFlowClass decoded.syscallId = .inert) :
    syscallTaintPlan st tid decoded = TaintPlan.inert := by
  simp [syscallTaintPlan, h]

-- ============================================================================
-- §3  WS-SM SM9.D.12 / SM9.D.13a — applying a plan
-- ============================================================================

/-- WS-SM SM9.D.8: apply the declared flows, reading every source from the
**pre**-state table so the update is simultaneous rather than order-dependent. -/
def applyTaintFlow (pre : TaintTable) (edges : List TaintFlowEdge) (tbl : TaintTable) :
    TaintTable :=
  edges.foldl (fun t e => t.joinAt e.sink (pre e.source)) tbl

/-- WS-SM SM9.D.12: forget the provenance of every destroyed object. -/
def applyTaintClears (cleared : List SeLe4n.ObjId) (tbl : TaintTable) : TaintTable :=
  cleared.foldl (fun t o => t.clearAt o) tbl

/-- WS-SM SM9.D.13a: **the events this syscall recorded**, recovered from the
trail's own diff.

Guarded on the epoch: a drain removes a prefix and advances the epoch, so an
unchanged epoch is exactly the condition under which the post-trail extends the
pre-trail and `drop` names the appended suffix.  No syscall both drains and
appends, and the guard means a future one that did would originate nothing
rather than mis-attribute.

Diff-recovered rather than planned, so a *new* declassifying syscall originates
tags the day it lands: the record it writes is the whole specification of what
its downgrade released. -/
def newlyRecordedEvents (pre post : SystemState) : List DeclassificationEvent :=
  if pre.declassificationAuditEpoch = post.declassificationAuditEpoch then
    post.declassificationAuditLog.drop pre.declassificationAuditLog.length
  else []

/-- WS-SM SM9.D.13a: **on a pure append the diff IS the appended suffix.**

The characterisation the origination rests on, so "recovered from the trail's
own diff" is a checked fact rather than a reading of `drop`. -/
theorem newlyRecordedEvents_append (pre post : SystemState)
    (new : DeclassificationAuditLog)
    (hEpoch : pre.declassificationAuditEpoch = post.declassificationAuditEpoch)
    (hLog : post.declassificationAuditLog = pre.declassificationAuditLog ++ new) :
    newlyRecordedEvents pre post = new := by
  simp [newlyRecordedEvents, hEpoch, hLog]

/-- WS-SM SM9.D.13a: **a commit that advanced the epoch originates nothing.**

The drain is the only such commit, and it records no downgrade, so this is
exactly right for every commit the kernel can perform.  The direction matters
and is deliberate: a hypothetical future syscall that both drained and appended
would originate *nothing* rather than mis-attribute a suffix computed against a
trail whose prefix is gone — under-approximating where this module otherwise
over-approximates, which is why the epoch guard is stated here rather than left
to `drop`'s behaviour on a shortened list. -/
theorem newlyRecordedEvents_drained (pre post : SystemState)
    (hEpoch : pre.declassificationAuditEpoch ≠ post.declassificationAuditEpoch) :
    newlyRecordedEvents pre post = [] := by
  simp [newlyRecordedEvents, hEpoch]

/-- WS-SM SM9.D.13a: **a downgrade originates its own identity** — on the object
its content landed in, and on the subject that performed it.

The target because that is where the released content now lives; the actor
because a subject that released content at `t` and releases again later is a
laundering candidate, and without this the second downgrade would carry no
predecessor. -/
def originationTags (events : List DeclassificationEvent) : List (SeLe4n.ObjId × Nat) :=
  events.flatMap (fun e => [(e.targetObject, e.timestamp), (e.sourceSubject, e.timestamp)])

/-- WS-SM SM9.D.13a: apply the origination tags. -/
def applyOrigination (origins : List (SeLe4n.ObjId × Nat)) (tbl : TaintTable) : TaintTable :=
  origins.foldl (fun t p => t.joinAt p.1 (DeclassificationTaint.singleton p.2)) tbl

/-- WS-SM SM9.D.7 (**the one writer**): apply a syscall's whole taint effect to
the state the dispatch committed.

Order is flows, then clears, then origination, and each step is where it is for a
reason:

* flows first, because their sources are the **pre**-state's taint;
* clears next, so a retype forgets provenance the same commit's flows could not
  have given it (a retype declares no flows);
* origination last, because a downgrade's identity does not exist until the
  event is recorded, and it must land on the object the delivery reached — which
  the flows have just re-tainted. -/
def applySyscallTaint (plan : TaintPlan) (pre post : SystemState) : SystemState :=
  { post with
      declassificationTaint :=
        applyOrigination (originationTags (newlyRecordedEvents pre post))
          (applyTaintClears plan.cleared
            (applyTaintFlow pre.declassificationTaint plan.edges
              post.declassificationTaint)) }

/-- WS-SM SM9.D.7 (**the frame**): the taint write touches the taint table and
nothing else.

The theorem every carriage argument rides: the entry's propagation step changes
no object, no scheduler slot, no register bank, no trail, and no lock — so every
invariant and non-interference result about the dispatch transfers across it. -/
theorem applySyscallTaint_frame (plan : TaintPlan) (pre post : SystemState) :
    applySyscallTaint plan pre post =
      { post with
          declassificationTaint :=
            applyOrigination (originationTags (newlyRecordedEvents pre post))
              (applyTaintClears plan.cleared
                (applyTaintFlow pre.declassificationTaint plan.edges
                  post.declassificationTaint)) } := rfl

/-- WS-SM SM9.D.7: every field but the taint table is carried through — the
projection form the carriage arguments read. -/
@[simp] theorem applySyscallTaint_objects (plan : TaintPlan) (pre post : SystemState) :
    (applySyscallTaint plan pre post).objects = post.objects := rfl

@[simp] theorem applySyscallTaint_scheduler (plan : TaintPlan) (pre post : SystemState) :
    (applySyscallTaint plan pre post).scheduler = post.scheduler := rfl

@[simp] theorem applySyscallTaint_machine (plan : TaintPlan) (pre post : SystemState) :
    (applySyscallTaint plan pre post).machine = post.machine := rfl

@[simp] theorem applySyscallTaint_declassificationAuditLog (plan : TaintPlan)
    (pre post : SystemState) :
    (applySyscallTaint plan pre post).declassificationAuditLog =
      post.declassificationAuditLog := rfl

@[simp] theorem applySyscallTaint_declassificationAuditEpoch (plan : TaintPlan)
    (pre post : SystemState) :
    (applySyscallTaint plan pre post).declassificationAuditEpoch =
      post.declassificationAuditEpoch := rfl

@[simp] theorem applySyscallTaint_declassificationRefusals (plan : TaintPlan)
    (pre post : SystemState) :
    (applySyscallTaint plan pre post).declassificationRefusals =
      post.declassificationRefusals := rfl

/-- WS-SM SM9.D.7: an inert plan on a syscall that recorded nothing is the
identity — the property that makes "most syscalls do not touch the table" a
fact rather than an expectation. -/
theorem applySyscallTaint_inert (pre post : SystemState)
    (hEvents : newlyRecordedEvents pre post = []) :
    applySyscallTaint TaintPlan.inert pre post = post := by
  show { post with
      declassificationTaint :=
        applyOrigination (originationTags (newlyRecordedEvents pre post))
          (applyTaintClears [] (applyTaintFlow pre.declassificationTaint []
            post.declassificationTaint)) } = post
  rw [hEvents]
  simp [originationTags, applyOrigination, applyTaintClears, applyTaintFlow]

-- ============================================================================
-- §3b  WS-SM SM9.D.8-.D.12 — what propagation establishes
-- ============================================================================

/-- WS-SM SM9.D.8: **the flow fold never forgets** — a tag already at an object
survives every later edge. -/
theorem contains_applyTaintFlow_mono (pre : TaintTable) :
    ∀ (edges : List TaintFlowEdge) (tbl : TaintTable) (o : SeLe4n.ObjId) {t : Nat},
      (tbl o).contains t = true → ((applyTaintFlow pre edges tbl) o).contains t = true := by
  intro edges
  induction edges with
  | nil => intro tbl o t h; simpa [applyTaintFlow] using h
  | cons e rest ih =>
    intro tbl o t h
    simp only [applyTaintFlow, List.foldl_cons]
    exact ih _ o (TaintTable.contains_joinAt_of_contains tbl e.sink o (pre e.source) h)

/-- WS-SM SM9.D.8 (**the propagation property**): a declared edge really moves
the source's provenance to the sink.

Every per-site theorem below is this one instantiated; the site-specific content
is *which* edges the planner declares. -/
theorem contains_applyTaintFlow_of_mem (pre : TaintTable) :
    ∀ (edges : List TaintFlowEdge) (tbl : TaintTable) (e : TaintFlowEdge),
      e ∈ edges → ∀ {t : Nat}, (pre e.source).contains t = true →
        ((applyTaintFlow pre edges tbl) e.sink).contains t = true := by
  intro edges
  induction edges with
  | nil => intro tbl e hMem; exact absurd hMem (by simp)
  | cons e' rest ih =>
    intro tbl e hMem t h
    simp only [applyTaintFlow, List.foldl_cons]
    rcases List.mem_cons.mp hMem with rfl | hRest
    · exact contains_applyTaintFlow_mono pre rest _ e.sink
        (TaintTable.contains_joinAt_of_source tbl e.sink (pre e.source) h)
    · exact ih _ e hRest h

/-- WS-SM SM9.D.12: clearing an object other than `o` leaves `o` alone. -/
theorem contains_applyTaintClears_of_not_mem :
    ∀ (cleared : List SeLe4n.ObjId) (tbl : TaintTable) (o : SeLe4n.ObjId),
      o ∉ cleared → ∀ {t : Nat}, (tbl o).contains t = true →
        ((applyTaintClears cleared tbl) o).contains t = true := by
  intro cleared
  induction cleared with
  | nil => intro tbl o _ t h; simpa [applyTaintClears] using h
  | cons c rest ih =>
    intro tbl o hNot t h
    simp only [applyTaintClears, List.foldl_cons]
    refine ih _ o (fun hm => hNot (List.mem_cons_of_mem _ hm)) ?_
    have hne : o ≠ c := fun hEq => hNot (by rw [hEq]; exact List.mem_cons_self)
    simpa [TaintTable.clearAt_ne tbl hne] using h

/-- WS-SM SM9.D.13a: origination only ever adds — it cannot remove a tag a flow
just established. -/
theorem contains_applyOrigination_mono :
    ∀ (origins : List (SeLe4n.ObjId × Nat)) (tbl : TaintTable) (o : SeLe4n.ObjId) {t : Nat},
      (tbl o).contains t = true → ((applyOrigination origins tbl) o).contains t = true := by
  intro origins
  induction origins with
  | nil => intro tbl o t h; simpa [applyOrigination] using h
  | cons p rest ih =>
    intro tbl o t h
    simp only [applyOrigination, List.foldl_cons]
    exact ih _ o (TaintTable.contains_joinAt_of_contains tbl p.1 o
      (DeclassificationTaint.singleton p.2) h)

/-- WS-SM SM9.D.13a: **origination records the identity it is given.** -/
theorem contains_applyOrigination_of_mem :
    ∀ (origins : List (SeLe4n.ObjId × Nat)) (tbl : TaintTable) (p : SeLe4n.ObjId × Nat),
      p ∈ origins → ((applyOrigination origins tbl) p.1).contains p.2 = true := by
  intro origins
  induction origins with
  | nil => intro tbl p hMem; exact absurd hMem (by simp)
  | cons q rest ih =>
    intro tbl p hMem
    simp only [applyOrigination, List.foldl_cons]
    rcases List.mem_cons.mp hMem with rfl | hRest
    · exact contains_applyOrigination_mono rest _ p.1
        (TaintTable.contains_joinAt_of_source tbl p.1 (DeclassificationTaint.singleton p.2)
          (DeclassificationTaint.contains_singleton_self p.2))
    · exact ih _ p hRest

/-- WS-SM SM9.D.8 (**the headline propagation theorem**): a declared edge moves
the source's provenance to the sink, through the whole applied plan.

The `cleared = []` hypothesis is what a content-moving plan supplies by
construction (`syscallTaintPlan` gives a `.movesContent` syscall no clears), and
it is genuinely necessary: a plan that both moved and destroyed provenance would
have to say which wins.  Only the retype clears, and it declares no edges. -/
theorem taintPropagation_edge (plan : TaintPlan) (pre post : SystemState)
    (e : TaintFlowEdge) (hMem : e ∈ plan.edges) (hClear : plan.cleared = []) {t : Nat}
    (hSrc : (pre.declassificationTaint e.source).contains t = true) :
    ((applySyscallTaint plan pre post).declassificationTaint e.sink).contains t = true := by
  show ((applyOrigination (originationTags (newlyRecordedEvents pre post))
      (applyTaintClears plan.cleared
        (applyTaintFlow pre.declassificationTaint plan.edges
          post.declassificationTaint))) e.sink).contains t = true
  refine contains_applyOrigination_mono _ _ e.sink ?_
  rw [hClear]
  simpa [applyTaintClears] using
    contains_applyTaintFlow_of_mem pre.declassificationTaint plan.edges
      post.declassificationTaint e hMem hSrc

/-- WS-SM SM9.D.13a (**origination**): a downgrade recorded by this commit tags
the object its content landed in.

Together with `taintPropagation_edge` this is the whole of how a tag gets onto
an object: a declassification originates it, and ordinary delivery moves it. -/
theorem taintOrigination_target (plan : TaintPlan) (pre post : SystemState)
    (ev : DeclassificationEvent) (hMem : ev ∈ newlyRecordedEvents pre post) :
    ((applySyscallTaint plan pre post).declassificationTaint ev.targetObject).contains
      ev.timestamp = true := by
  show ((applyOrigination (originationTags (newlyRecordedEvents pre post)) _)
    ev.targetObject).contains ev.timestamp = true
  exact contains_applyOrigination_of_mem _ _ (ev.targetObject, ev.timestamp)
    (List.mem_flatMap.mpr ⟨ev, hMem, by simp⟩)

/-- WS-SM SM9.D.13a (**origination, actor half**): a downgrade also tags the
subject that performed it, so a subject that releases content twice carries the
first release's identity into the second's snapshot.

Without this the `.declassify`-then-`.declassify` chain — the simplest laundering
shape there is — would carry no predecessor and go undetected. -/
theorem taintOrigination_actor (plan : TaintPlan) (pre post : SystemState)
    (ev : DeclassificationEvent) (hMem : ev ∈ newlyRecordedEvents pre post) :
    ((applySyscallTaint plan pre post).declassificationTaint ev.sourceSubject).contains
      ev.timestamp = true := by
  show ((applyOrigination (originationTags (newlyRecordedEvents pre post)) _)
    ev.sourceSubject).contains ev.timestamp = true
  exact contains_applyOrigination_of_mem _ _ (ev.sourceSubject, ev.timestamp)
    (List.mem_flatMap.mpr ⟨ev, hMem, by simp⟩)

/-- WS-SM SM9.D.8: the edge a content-moving syscall's plan carries, named once
so every per-site corollary below reads the same resolution. -/
private theorem mem_movesContent_edges {st : SystemState} {tid : SeLe4n.ThreadId}
    {decoded : SyscallDecodeResult} {e : TaintFlowEdge}
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hMem : e ∈ contentFlowEdges st tid decoded) :
    e ∈ (syscallTaintPlan st tid decoded).edges ∧
      (syscallTaintPlan st tid decoded).cleared = [] := by
  simp only [syscallTaintPlan, hClass]
  exact ⟨hMem, trivial⟩

/-- WS-SM SM9.D.8 (**send / call → endpoint**): the message a sender parks on an
endpoint carries the sender's provenance with it.

The endpoint edge is declared unconditionally, so the tag lands whether the send
rendezvoused or blocked — which is what makes the later `.receive` able to pick
it up (`taintPropagation_receive_from_endpoint`). -/
theorem taintPropagation_send_to_endpoint (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (epId : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId) {t : Nat}
    (hSender : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      epId).contains t = true := by
  have hMem : ({ sink := epId, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget] <;> simp [senderTaintEdges]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hSender

/-- WS-SM SM9.D.8 (**send / call → rendezvous receiver**): when a receiver is
already queued, the sender's provenance reaches it directly.

`receiveQ.head` is the thread the arms themselves compute as `wokenReceiver?`,
so the object the plan tags is the object the delivery wakes. -/
theorem taintPropagation_send_to_receiver (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (epId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId)
    (hRecv : (st.getEndpoint? epId).bind (·.receiveQ.head) = some receiver) {t : Nat}
    (hSender : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      receiver.toObjId).contains t = true := by
  have hMem : ({ sink := receiver.toObjId, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget] <;> simp [senderTaintEdges, hRecv]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hSender

/-- WS-SM SM9.D.11 (**send / call → receiver's CSpace**): a transferred
capability lands in the receiver's CNode, so the CNode carries the sender's
provenance too.

The sink the receiver's TCB tag does not cover: a CNode is shared, so a second
thread rooted at the same CSpace reads what `ipcUnwrapCaps` installed without
ever touching the receiver's TCB. -/
theorem taintPropagation_send_to_receiver_cspace (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap : Capability)
    (epId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (rtcb : SeLe4n.Model.TCB)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId)
    (hRecv : (st.getEndpoint? epId).bind (·.receiveQ.head) = some receiver)
    (hTcb : st.getTcb? receiver = some rtcb) {t : Nat}
    (hSender : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      rtcb.cspaceRoot).contains t = true := by
  have hMem : ({ sink := rtcb.cspaceRoot, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;>
      simp only [h, hTarget] <;>
      simp [senderTaintEdges, hRecv, capTransferTaintSinks, hTcb]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hSender

/-- WS-SM SM9.D.8 (**receive / replyRecv ← endpoint**): a receiver picks up the
provenance parked on the endpoint by an earlier blocking send. -/
theorem taintPropagation_receive_from_endpoint (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (epId : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .receive ∨ decoded.syscallId = .replyRecv)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId) {t : Nat}
    (hEndpoint : (st.declassificationTaint epId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      tid.toObjId).contains t = true := by
  have hMem : ({ sink := tid.toObjId, source := epId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget] <;> simp [receiverTaintEdges]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hEndpoint

/-- WS-SM SM9.D.9 (**reply → caller**): a reply message carries the replying
server's provenance to the caller the reply object records. -/
theorem taintPropagation_reply_to_caller (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (rid : SeLe4n.ReplyId)
    (caller : SeLe4n.ThreadId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .reply)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .replyCap rid)
    (hCaller : (st.getReply? rid).bind (·.caller) = some caller) {t : Nat}
    (hReplier : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      caller.toObjId).contains t = true := by
  have hMem : ({ sink := caller.toObjId, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap, hSid, hTarget]
    simp [replyTaintEdges, hCaller]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hReplier

/-- WS-SM SM9.D.10 (**signal → notification**): a badge carries the signaller's
provenance onto the notification, whether or not anyone is waiting. -/
theorem taintPropagation_signal_to_notification (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap : Capability)
    (nid : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .notificationSignal ∨ decoded.syscallId = .declassifySignal)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object nid) {t : Nat}
    (hSignaller : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      nid).contains t = true := by
  have hMem : ({ sink := nid, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget] <;> simp [signalTaintEdges]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hSignaller

/-- WS-SM SM9.D.10 (**wait ← notification**): the *other* ordering.

With no waiter present a signal leaves the badge — and its provenance — on the
notification, and it is this arm that moves it to the waiter.  Omitting it would
lose hop 1 of the §3.6 chain in the signal-before-wait ordering, so the detector
would miss the design's own scenario half the time. -/
theorem taintPropagation_wait_from_notification (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap : Capability)
    (nid : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .notificationWait)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object nid) {t : Nat}
    (hNotification : (st.declassificationTaint nid).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      tid.toObjId).contains t = true := by
  have hMem : ({ sink := tid.toObjId, source := nid } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap, hSid, hTarget]
    simp [waitTaintEdges]
  obtain ⟨hIn, hClear⟩ := mem_movesContent_edges hClass hMem
  exact taintPropagation_edge _ st post _ hIn hClear hNotification

-- ============================================================================
-- §3c  WS-SM SM9.D.12 — the retype forgets
-- ============================================================================

/-- WS-SM SM9.D.12: **a retype's plan clears its target** — and declares no
flows, so nothing re-establishes what it removes in the same commit. -/
theorem retypeClearsTaint (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (hSid : decoded.syscallId = .lifecycleRetype)
    (args : Architecture.SyscallArgDecode.LifecycleRetypeArgs)
    (hArgs : Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs decoded = .ok args) :
    syscallTaintPlan st tid decoded = { edges := [], cleared := [args.targetObj] } := by
  simp [syscallTaintPlan, contentFlowClass, hSid, retypeClearedObjects, hArgs]

/-- WS-SM SM9.D.12 (**the property**): after a retype the destroyed object
carries **no** provenance.

The hypothesis on the trail is discharged by the retype itself: it records no
declassification, so this commit originates nothing that could re-tag the
cleared id.  Stated with the hypothesis rather than assumed, because
`applySyscallTaint` is total over arbitrary pre/post pairs and the retype's own
trail frame belongs to the lifecycle layer. -/
theorem retypedObject_taint_empty (plan : TaintPlan) (pre post : SystemState)
    (oid : SeLe4n.ObjId) (hPlan : plan = { edges := [], cleared := [oid] })
    (hNoEvents : newlyRecordedEvents pre post = []) :
    (applySyscallTaint plan pre post).declassificationTaint oid =
      DeclassificationTaint.empty := by
  subst hPlan
  show (applyOrigination (originationTags (newlyRecordedEvents pre post))
      (applyTaintClears [oid] (applyTaintFlow pre.declassificationTaint []
        post.declassificationTaint))) oid = DeclassificationTaint.empty
  rw [hNoEvents]
  simp [originationTags, applyOrigination, applyTaintClears, applyTaintFlow]

/-- WS-SM SM9.D.12 / SM9.D.15 (**the distinction that keeps the residual claim
true**): stale taint is **not** saturation.

The over-approximation SM9.D.15 accepts is the saturating top: an object that
has received more than `maxTaintTags` distinct downgrades names identities it
never received.  A framed retype would produce a *different* imprecision — a
specific, unsaturated identity attached to an object that never received
anything from it — and the two must not be conflated, because the claim "the
residual imprecision is saturation" would be false the day it was written.

Exhibited rather than argued: a table carrying one specific tag at an object,
unsaturated, whose only removal is the clear. -/
theorem staleTaint_is_not_saturation :
    ∃ (tbl : TaintTable) (oid : SeLe4n.ObjId) (t : Nat),
      (tbl oid).saturated = false ∧
      (tbl oid).contains t = true ∧
      ((tbl.clearAt oid) oid).contains t = false := by
  refine ⟨TaintTable.empty.joinAt (SeLe4n.ObjId.ofNat 7) (DeclassificationTaint.singleton 3),
          SeLe4n.ObjId.ofNat 7, 3, by decide, by decide, by decide⟩

-- ============================================================================
-- §3d  WS-SM SM9.D.17 — the write set, and the lock that serialises it
-- ============================================================================

/-! ### The serialization subject is the *key's own lock*.

`SystemState.declassificationTaint` is a table keyed by `ObjId`, represented —
like `SystemState.objects` — as a single field.  That representation is what
makes the question sharp: is a taint write serialised by the coarse table lock
(`stateLevelLock`, hierarchy level 0), or by the lock the transition already
holds on the object the write is keyed at?

The codebase already answers it for the object store, and the answer is the
per-object lock.  `storeObject` writes one key of `SystemState.objects` and no
`lockSet_<τ>` declares `objStoreLock` for it; `.objStore` is reserved for
*structural* table operations, which is why `stateLevelLock` appears in exactly
three footprints before this phase — `lockSet_declassify`, `lockSet_auditRead`
and `lockSet_auditDrain` — all of which write the audit **trail**, a `List`
whose append is genuinely not key-decomposable (both writers read the length,
both write the whole list, and one append is lost).

A keyed table is decomposable, so declaring `stateLevelLock` on the eight
content-moving syscalls would be both inconsistent with the object store's own
discipline and materially worse than it: it puts a single globally-contended
lock on `.send` / `.receive` / `.call` / `.reply` / `.replyRecv` /
`.notificationSignal` / `.notificationWait`, so two cores performing unrelated
IPC on unrelated endpoints would serialise against each other.  For a
microkernel whose IPC path is the product, that is not a footprint refinement —
it is a design regression, and it fails the SM5.J tick-budget reasoning the
`smp_ipc_suite` and `smp_notification_suite` fixtures pin (`|lockSet| · 3 · tCs`
at `tCs = 60µs` fits a 1 ms tick only up to five locks).

So the declared subject is the object's own lock, and what this section supplies
is the fact that makes that declaration checkable rather than asserted: the
**write set** of a plan, and the frame proving the table is untouched outside
it.

**Implementation obligation, recorded rather than assumed.**  The model writes
the field whole, so the key-local reading is sound only if the runtime realises
the table as per-object storage — a store at slot `o` for
`TaintTable.set _ o _`.  That is precisely the obligation `SystemState.objects`
already carries for `storeObject` under the same discipline, and it is
discharged the same way: by the representation, at SM10.E.  Stated here so a
reader of the footprint knows which half is proven and which half is owed. -/

/-- WS-SM SM9.D.17: **the objects a plan's flows write.**

The sink of every declared edge — the object content reaches.  Sources are
*read*, so they are not in the write set (a read lock on the source suffices,
which is what `lockSet_notificationSignal`'s `.read` on the signaller's TCB
already is). -/
def taintFlowSinks (plan : TaintPlan) : List SeLe4n.ObjId :=
  plan.edges.map (·.sink)

/-- WS-SM SM9.D.17: **the objects an origination tags.**

An audit event tags its target and its actor's TCB.  This list is empty unless
the commit appended to the trail, which only `.declassify` and
`.declassifySignal` do — and both already declare `stateLevelLock` in write
mode for that append, so the actor-TCB key (which their footprints hold only in
*read* mode) is covered.  `taintOriginationKeys_nil_of_no_events` is that
premise made checkable. -/
def taintOriginationKeys (pre post : SystemState) : List SeLe4n.ObjId :=
  (originationTags (newlyRecordedEvents pre post)).map (·.fst)

/-- WS-SM SM9.D.17: **the full write set** — flow sinks, cleared ids, and
origination targets. -/
def taintWriteKeys (plan : TaintPlan) (pre post : SystemState) : List SeLe4n.ObjId :=
  taintFlowSinks plan ++ plan.cleared ++ taintOriginationKeys pre post

/-- WS-SM SM9.D.17: an origination writes nothing when the commit appended no
event — so for the six content-moving syscalls that do not touch the trail the
write set is exactly the declared sinks. -/
@[simp] theorem taintOriginationKeys_nil_of_no_events (pre post : SystemState)
    (h : newlyRecordedEvents pre post = []) :
    taintOriginationKeys pre post = [] := by
  simp [taintOriginationKeys, h, originationTags]

private theorem applyTaintFlow_not_mem (pre : TaintTable) (o : SeLe4n.ObjId) :
    ∀ (edges : List TaintFlowEdge) (tbl : TaintTable),
      o ∉ edges.map (fun e => e.sink) → applyTaintFlow pre edges tbl o = tbl o := by
  intro edges
  induction edges with
  | nil => intro tbl _; rfl
  | cons e rest ih =>
    intro tbl h
    have hne : o ≠ e.sink := by
      intro hEq; exact h (by simp [hEq])
    have hrest : o ∉ rest.map (fun e => e.sink) := by
      intro hMem; exact h (by simp [hMem])
    show applyTaintFlow pre rest (tbl.joinAt e.sink (pre e.source)) o = tbl o
    rw [ih _ hrest]
    exact TaintTable.joinAt_ne tbl hne _

private theorem applyTaintClears_not_mem (o : SeLe4n.ObjId) :
    ∀ (cleared : List SeLe4n.ObjId) (tbl : TaintTable),
      o ∉ cleared → applyTaintClears cleared tbl o = tbl o := by
  intro cleared
  induction cleared with
  | nil => intro tbl _; rfl
  | cons c rest ih =>
    intro tbl h
    have hne : o ≠ c := by intro hEq; exact h (by simp [hEq])
    have hrest : o ∉ rest := by intro hMem; exact h (by simp [hMem])
    show applyTaintClears rest (tbl.clearAt c) o = tbl o
    rw [ih _ hrest]
    exact TaintTable.clearAt_ne tbl hne

private theorem applyOrigination_not_mem (o : SeLe4n.ObjId) :
    ∀ (origins : List (SeLe4n.ObjId × Nat)) (tbl : TaintTable),
      o ∉ origins.map (·.fst) → applyOrigination origins tbl o = tbl o := by
  intro origins
  induction origins with
  | nil => intro tbl _; rfl
  | cons g rest ih =>
    intro tbl h
    have hne : o ≠ g.fst := by intro hEq; exact h (by simp [hEq])
    have hrest : o ∉ rest.map (·.fst) := by intro hMem; exact h (by simp [hMem])
    show applyOrigination rest (tbl.joinAt g.fst (DeclassificationTaint.singleton g.snd)) o
        = tbl o
    rw [ih _ hrest]
    exact TaintTable.joinAt_ne tbl hne _

/-- WS-SM SM9.D.17 (**the key-locality frame**): outside its write set a plan
leaves the taint table literally unchanged.

This is what licenses declaring the propagation under the *object* locks the
transition already holds rather than under `stateLevelLock`: the update at key
`o` is a function of `o`'s own entry and its declared sources, and every key
the plan does not name is carried through untouched. -/
theorem applySyscallTaint_frame_off_writeKeys (plan : TaintPlan)
    (pre post : SystemState) (o : SeLe4n.ObjId)
    (h : o ∉ taintWriteKeys plan pre post) :
    (applySyscallTaint plan pre post).declassificationTaint o =
      post.declassificationTaint o := by
  have hFlow : o ∉ taintFlowSinks plan := fun hm => h (by
    simp only [taintWriteKeys, List.mem_append]; exact Or.inl (Or.inl hm))
  have hClear : o ∉ plan.cleared := fun hm => h (by
    simp only [taintWriteKeys, List.mem_append]; exact Or.inl (Or.inr hm))
  have hOrig : o ∉ taintOriginationKeys pre post := fun hm => h (by
    simp only [taintWriteKeys, List.mem_append]; exact Or.inr hm)
  show applyOrigination (originationTags (newlyRecordedEvents pre post))
      (applyTaintClears plan.cleared
        (applyTaintFlow pre.declassificationTaint plan.edges
          post.declassificationTaint)) o = post.declassificationTaint o
  rw [applyOrigination_not_mem o _ _ hOrig,
      applyTaintClears_not_mem o _ _ hClear,
      applyTaintFlow_not_mem pre.declassificationTaint o _ _ hFlow]

/-- WS-SM SM9.D.17: two plans whose write sets are disjoint touch disjoint keys,
so neither can lose the other's update.

The model-level content of "the object's own lock is a sufficient serialization
subject": with disjoint write sets the two updates are independent at every key,
which is exactly the property a per-object representation realises and a single
whole-field word would not. -/
theorem taintWriteKeys_disjoint_updates_independent
    (planA planB : TaintPlan) (preA postA preB postB : SystemState)
    (o : SeLe4n.ObjId)
    (hA : o ∈ taintWriteKeys planA preA postA)
    (hDisj : ∀ k ∈ taintWriteKeys planA preA postA,
      k ∉ taintWriteKeys planB preB postB) :
    (applySyscallTaint planB preB postB).declassificationTaint o =
      postB.declassificationTaint o :=
  applySyscallTaint_frame_off_writeKeys planB preB postB o (hDisj o hA)

/-- WS-SM SM9.D.17: **the trail writers are the only originators.**

A syscall that appends no audit event has an empty origination set, so its taint
write set is confined to the objects its own edges and clears name — every one
of which the transition writes and therefore already write-locks.  The two
syscalls that *do* append (`.declassify`, `.declassifySignal`) are exactly the
two whose footprints already carry `stateLevelLock` in write mode for the
append, which is what covers their actor-TCB origination key. -/
theorem taintWriteKeys_of_no_events (plan : TaintPlan) (pre post : SystemState)
    (h : newlyRecordedEvents pre post = []) :
    taintWriteKeys plan pre post = taintFlowSinks plan ++ plan.cleared := by
  simp [taintWriteKeys, taintOriginationKeys_nil_of_no_events pre post h]

/-- WS-SM SM9.D.17: an inert syscall writes no key at all. -/
theorem taintWriteKeys_inert (pre post : SystemState)
    (h : newlyRecordedEvents pre post = []) :
    taintWriteKeys TaintPlan.inert pre post = [] := by
  simp [taintWriteKeys_of_no_events _ pre post h, taintFlowSinks, TaintPlan.inert]

-- ============================================================================
-- §4  WS-SM SM9.D.6 / SM9.D.18 — the propagation is invisible
-- ============================================================================

/-- WS-SM SM9.D.6: **the propagation write moves no observer's view.**

Immediate from the frame plus `declassificationTaint_write_preserves_projection`,
and stated here so every consumer of the entry seam — the SM8.D bracket, the
per-core non-interference inventory, the SM8.B live-arm results — reads one
name rather than re-deriving it. -/
theorem applySyscallTaint_preserves_projection (ctx : LabelingContext)
    (observer : IfObserver) (plan : TaintPlan) (pre post : SystemState) :
    projectState ctx observer (applySyscallTaint plan pre post) =
      projectState ctx observer post := rfl

end SeLe4n.Kernel
