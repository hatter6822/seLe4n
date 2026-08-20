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
* **Writes confined to one object** — `cspaceCopy`, `cspaceMove`, `cspaceDelete`
  and `mintReplyCap` all take the CNode from the *capability* and both slots from
  the decoded arguments (`src.cnode = dst.cnode = cnodeId`, verified at the
  arms), so source and sink are the same object and an edge would be a self-loop.
* **Outside the tracked-content scope** — `cspaceMint`.  Its slots are
  same-CNode like its siblings, but unlike them it does not merely relocate an
  existing capability: `decodeCSpaceMintArgs` reads the new **badge** and
  **rights** from the caller's message registers, so a mint writes
  caller-supplied bits into the destination capability.  Those bits are
  *capability metadata* — the authority a capability names, and the identity a
  badged endpoint delivers — not the message/notification payload this model
  tracks as content (`contentTrackedFields`).  Classifying mint `.inert` is
  therefore a statement about the **scope boundary**, not the self-loop claim its
  siblings rest on, and the boundary is deliberate: a capability badge is
  authority-identity, and tracking it as content would have to follow every
  `cspace*` operation and every badged delivery.  Recorded as an accepted
  out-of-scope channel (`capabilityBadgeChannel_out_of_scope`) rather than left
  to a justification that does not hold for this arm.
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

/-- WS-SM SM9.D.7: **what this model tracks as content**, named so the boundary
is a value rather than a claim in prose.

Exactly the two payload channels the Tier-1 reach gate scans for
(`scripts/check_content_flow_coverage.py`'s `CONTENT_CHANNELS`): a delivered
message and a delivered badge.  Anything else an arm writes is out of scope by
this definition — which is what makes `.cspaceMint`'s `.inert` classification a
scope statement rather than the (false, for that arm) self-loop claim. -/
def contentTrackedFields : List (String × String) :=
  [("TCB", "pendingMessage"), ("Notification", "pendingBadge")]

/-- WS-SM SM9.D.7 (**the accepted out-of-scope channel**): a capability's badge
and rights are caller-supplied on a mint, and they are **not** tracked content.

Stated as a theorem rather than left in a docstring so the boundary is checkable
and a future decision to track capability metadata has to delete this — the shape
`UncoveredLockDomain` uses for a registered gap.  Two halves: the mint is
classified `.inert`, and the fields it writes are outside `contentTrackedFields`,
so the classification follows from the scope rather than from a claim about
mint's slots.

The channel this accepts: a subject holding declassified content can encode bits
in a badge it mints into a CNode another subject reads, and the causal detector
will not link the two.  It is bounded by capability authority — the minter needs
a CNode capability with mint rights, and the reader needs that CNode — and
closing it means tracking badge provenance through every `cspace*` operation and
every badged delivery, a threat-model expansion deliberately not taken here. -/
theorem capabilityBadgeChannel_out_of_scope :
    contentFlowClass .cspaceMint = .inert ∧
      ("CNode", "slots") ∉ contentTrackedFields := by
  refine ⟨rfl, ?_⟩
  simp [contentTrackedFields]

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
  /-- Objects the commit's recorded downgrade *names* but whose content it
      **bypassed**, so the fresh event must not be originated onto them.

      Distinct from `cleared`, and the distinction is the point.  A clear is
      destructive — the object held content and now holds none, so its provenance
      goes with it.  A bypass destroys nothing: a signal delivered to a bound TCB
      writes that thread and never touches the notification, so a badge already
      stored there keeps both its content and its provenance, while the *new*
      badge never landed there at all.  Folding the two together would either
      wipe the stored badge's provenance (a missed chain) or tag a notification
      the new badge went nowhere near (a false one). -/
  bypassed : List SeLe4n.ObjId := []
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

**Three edges, because provenance has to arrive *and* be consumed.**  The first
tags the receiver's CSpace root with the *sender's own content* (`tid`).  The
second tags it with the *sender's CSpace-root* taint (`stcb.cspaceRoot`): a
capability a prior transfer installed into `tid`'s CSpace carries that
transfer's provenance on `tid`'s root, and forwarding it must carry the chain
forward.  Without the second edge the taint this function writes would be an
unwired structure — written on the receiver's root and read by nothing, since no
other edge sources from a CSpace root — and a cap forwarded by an untainted
courier would drop the link.

The third edge is the one simultaneity makes necessary.  `applyTaintFlow` reads
**every** source from the pre-state table, so the root-to-root edge above and any
root-to-subject edge in the same plan do not compose within one commit: the
receiver's root gets the sender's provenance, but a root-to-subject edge keyed on
the receiver's root still reads that root's *old* value and the receiver's TCB
stays untainted.  A courier whose provenance lives only on the sender's CSpace
root would therefore hand a capability to a receiver who could downgrade
immediately with no recorded predecessor — a missed chain.  Sourcing the
receiver's *subject* directly from the sender's root closes that in one hop,
which is why the edge is here (shared by both rendezvous orderings) rather than
in either planner.

**Gated on capabilities actually crossing.**  A plain message installs nothing,
so declaring these sinks for every delivery would write the sender's provenance
into a CSpace no capability reached — and since a CSpace root now feeds the
consuming subject, that over-approximation would name an *unsaturated*
predecessor for an unrelated later downgrade.  That is precisely the false
positive `staleTaint_is_not_saturation` says must not exist, so over-approximating
here is not the safe direction it would be for an isolated sink; the gate is the
caller's, because the two orderings learn about capabilities differently (a send
from its own `MessageInfo`, a receive from the parked message it is about to
unwrap).

A resolved receiver whose TCB is absent contributes nothing, which is correct: no
CSpace, no install.  An absent sender TCB drops both CSpace-provenance edges and
keeps the content edge. -/
def capTransferTaintSinks (st : SystemState) (tid : SeLe4n.ThreadId)
    (receiver : SeLe4n.ThreadId) (carriesCaps : Bool) : List TaintFlowEdge :=
  match carriesCaps with
  | false => []
  | true =>
    match st.getTcb? receiver, st.getTcb? tid with
    | some rtcb, some stcb =>
        [ { sink := rtcb.cspaceRoot, source := tid.toObjId }
        , { sink := rtcb.cspaceRoot, source := stcb.cspaceRoot }
        , { sink := receiver.toObjId, source := stcb.cspaceRoot } ]
    | some rtcb, none => [{ sink := rtcb.cspaceRoot, source := tid.toObjId }]
    | none, _ => []

/-- WS-SM SM9.D.11: **does a `.send` / `.call` declare capabilities?**

Read from the caller's own `MessageInfo`, which is what `resolveExtraCaps`
iterates: the message is still in the sender's registers at this point, so the
declared count is the only signal available and re-deriving anything else would
duplicate the dispatch's own decode.  Silent-drop means the resolved count can
be *lower* than the declared one, so this over-approximates by at most a
declared-but-unresolvable capability — a sink declared for a transfer that moves
nothing, which is the harmless direction (the sink's source contributes whatever
the sender already held, exactly as an ordinary content edge would). -/
def sendCarriesCaps (cap : Capability) (decoded : SyscallDecodeResult) : Bool :=
  decoded.msgInfo.extraCaps > 0 && cap.hasRight .grant

/-- WS-SM SM9.D.8: **a sender's edges** — `.send` and `.call`.

The message leaves the sender.  On a rendezvous it reaches the receiver the
transition wakes (`receiveQ.head` at the pre-state, exactly the thread the arms
compute as `wokenReceiver?`); on a blocking send it stays in the sender's own
`pendingMessage`, whose provenance is already the sender's taint, so there is
nothing to propagate at send time.

**The endpoint is not tagged.**  It buffers no content of its own — a parked
message lives in the blocked sender's TCB — and a receiver always reads the head
sender directly (`receiverTaintEdges`), so an endpoint proxy would be redundant
*and* less precise (it would hand a receiver the taint of every queued sender,
not just the one it consumes).  Not declaring it is the content-derived model:
an object's taint reflects the content it currently holds, and an endpoint holds
none. -/
def senderTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (carriesCaps : Bool) : List TaintFlowEdge :=
  match (st.getEndpoint? epId).bind (·.receiveQ.head) with
  | some receiver =>
      { sink := receiver.toObjId, source := tid.toObjId } ::
        capTransferTaintSinks st tid receiver carriesCaps
  | none => []

/-- WS-SM SM9.D.8: **a receiver's edges** — `.receive` and `.replyRecv`.

Content reaches the receiver directly from the blocked sender at `sendQ.head` —
the thread the arms compute as `wokenSender?` — whether that sender parked in an
earlier syscall or arrives in this rendezvous.  The endpoint is **not** a source:
it holds no content of its own (`senderTaintEdges`), and the head-sender edge is
exact where an endpoint proxy would over-approximate to every queued sender.

**No CSpace sink is declared here, because the live receive installs nothing.**
The `.receive` arm runs `endpointReceiveDualOnCore`, which delivers the dequeued
sender's message wholesale and performs **no capability unwrap** — the arm says
so in place, and reports an installed count of zero however many capabilities the
parked message still carries.  `endpointReceiveDualWithCaps` exists and is
verified but has no live caller.  Declaring a receiver-CNode sink here would
therefore write the sender's provenance into a CNode no capability reached, and —
because a CSpace root feeds the consuming subject — hand an unrelated later
downgrade an *unsaturated* predecessor, which is exactly what
`staleTaint_is_not_saturation` forbids.

So the model states what the kernel does rather than what the design intends.
Capability provenance is still tracked on the ordering where a transfer actually
happens: the live send *does* unwrap, and `senderTaintEdges` declares the sinks
there.  Wiring the receive through the WithCaps path — and restoring these sinks
behind it — is tracked in `docs/planning/SMP_FINE_LOCK_MIGRATION_PLAN.md`; it
changes live IPC semantics, the return frame's `extraCaps` count and the golden
trace, so it belongs in its own cut rather than being anticipated here. -/
def receiverTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) :
    List TaintFlowEdge :=
  match (st.getEndpoint? epId).bind (·.sendQ.head) with
  | some sender => [{ sink := tid.toObjId, source := sender.toObjId }]
  | none => []

/-- WS-SM SM9.D.9: **a replier's edge** — `.reply`.

The reply message travels from the replying server to the caller the reply
object records, which is the thread the arm resolves through `reply.caller`. -/
def replyTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    List TaintFlowEdge :=
  match (st.getReply? rid).bind (·.caller) with
  | some caller => [{ sink := caller.toObjId, source := tid.toObjId }]
  | none => []

/-- WS-SM SM9.D.9: **the replyRecv REPLY leg** — the edge the receive-leg pair
cannot carry.

`.replyRecv` is two deliveries in one commit: the receive leg (endpoint /
blocked sender → server, `receiverTaintEdges`) and the reply leg — the server's
message registers delivered to the *previous caller* the reply object records.
The steady-state server loop is exactly the hop that returns declassified
content to a client, so omitting this edge would lose hop 2 of the §3.6 chain
whenever the server replies through `replyRecv` rather than a bare `.reply` —
an under-approximation, the direction a detector must never err in.

The resolution mirrors `resolveReplyRecvReply` step for step: the MR0-present
guard, `decodeReplyRecvArgs` for the reply CPtr, the caller's own CSpace at
that slot (`syscallOperandCap?`, the same root/depth/resolver the dispatch
gate carries), the `.replyCap` shape, then `getReply? → reply.caller` — which
is `replyTaintEdges`, so the `.reply` arm and this leg cannot drift apart.
Rights are deliberately not re-checked (the arm requires `.write` and errors
before content moves; a spuriously declared edge on a call that fails is the
safe direction), exactly as `syscallOperandCap?` itself declines to gate. -/
def replyRecvReplyLegEdges (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : List TaintFlowEdge :=
  if decoded.msgInfo.length == 0 then []
  else
    match Architecture.SyscallArgDecode.decodeReplyRecvArgs decoded with
    | .error _ => []
    | .ok rargs =>
        match syscallOperandCap? st tid (SeLe4n.CPtr.ofNat rargs.replyCPtr) with
        | none => []
        | some rcap =>
            match rcap.target with
            | .replyCap rid => replyTaintEdges st tid rid
            | _ => []

/-- WS-SM SM9.D.10: **how a signal actually delivers.**

Three outcomes, and every consumer of a signal's taint effect is derived from
this one classification rather than re-deriving its own.  That is deliberate:
the three consumers — the declared edges, the transport clear, and the
origination filter — disagreed three separate times, each caught in a different
review round, because each re-read `declassifiedSignalReceiver?` and drew its own
conclusion about what the delivery did to the notification.  A single classifier
makes a disagreement between them impossible to write.

* `stored` — no receiver.  The badge lands on the notification and stays there
  until a `.notificationWait` consumes it.
* `toWaiter` — a queued waiter takes the badge directly.  Nothing is stored, so
  the notification ends the commit holding no content.
* `toBound` — a bound TCB parked on an endpoint takes it.  `notificationSignalBound`
  writes that thread's `pendingMessage` and **never touches the notification**,
  so whatever badge it already held is still there afterwards, along with that
  badge's provenance. -/
inductive SignalDelivery where
  /-- No receiver: the badge is stored on the notification. -/
  | stored
  /-- A queued waiter takes it; the notification is left empty. -/
  | toWaiter (w : SeLe4n.ThreadId)
  /-- A bound TCB takes it; the notification is left untouched. -/
  | toBound (t : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

/-- WS-SM SM9.D.10: classify a signal's delivery.

Mirrors `declassifiedSignalReceiver?` exactly — bound target first, then the head
waiter — but keeps the two receiver kinds **distinguishable**, which is the
information `declassifiedSignalReceiver?` discards and which all three consumers
turned out to need. -/
def signalDelivery (st : SystemState) (nid : SeLe4n.ObjId) : SignalDelivery :=
  match boundDeliveryTarget? st nid with
  | some (t, _) => .toBound t
  | none =>
    match notificationSignalWaiter? st nid with
    | some w => .toWaiter w
    | none => .stored

/-- WS-SM SM9.D.10: the classification agrees with the resolver the delivery
itself uses, so the plan tags the object the delivery reaches. -/
theorem signalDelivery_agrees_with_receiver (st : SystemState) (nid : SeLe4n.ObjId) :
    (match signalDelivery st nid with
     | .stored => none
     | .toWaiter w => some w
     | .toBound t => some t) = declassifiedSignalReceiver? st nid := by
  unfold signalDelivery declassifiedSignalReceiver?
  cases hb : boundDeliveryTarget? st nid with
  | some p => obtain ⟨t, ep⟩ := p; simp
  | none => cases hw : notificationSignalWaiter? st nid with
            | some w => simp
            | none => simp

/-- WS-SM SM9.D.10: no resolved receiver is exactly the `stored` case — the
bridge between the classifier and the resolver every consumer's hypotheses are
stated against. -/
theorem signalDelivery_stored_of_no_receiver (st : SystemState) (nid : SeLe4n.ObjId)
    (h : declassifiedSignalReceiver? st nid = none) : signalDelivery st nid = .stored := by
  unfold signalDelivery
  cases hb : boundDeliveryTarget? st nid with
  | some p =>
      obtain ⟨t, ep⟩ := p
      rw [declassifiedSignalReceiver?_bound st nid t ep hb] at h
      exact absurd h (by simp)
  | none =>
      cases hw : notificationSignalWaiter? st nid with
      | some w =>
          rw [declassifiedSignalReceiver?_fallthrough st nid hb, hw] at h
          exact absurd h (by simp)
      | none => simp

/-- WS-SM SM9.D.10: **a signaller's edges** — `.notificationSignal` and
`.declassifySignal`.

The badge leaves the signaller for the notification, and — when a waiter or a
bound TCB is there to take it — on to that receiver.  The receiver is resolved
by `declassifiedSignalReceiver?`, the *same* function SM9.C's second-hop gate
and the SM9.B refusal seam use, so the object the plan tags is the object the
delivery reaches.

The two orderings write different objects, because a notification's taint
reflects the content it currently holds (the content-derived model).  With a
waiter present the badge is delivered directly and **nothing is stored** — a
waiter and a pending badge are mutually exclusive — so the signaller's content
flows to the receiver (`{receiver, tid}`) and the notification is cleared
(`contentFlowClears`) rather than tagged; the `{receiver, nid}` edge carries a
*declassified* badge's fresh event to the receiver through the origination seed
(`applySyscallTaint`) and is empty for an ordinary signal, whose `nid` holds
nothing.  With no waiter the badge is stored, so the signaller's content joins
onto the notification — where it stays until a `.notificationWait` consumes it. -/
def signalTaintEdges (st : SystemState) (tid : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) :
    List TaintFlowEdge :=
  match signalDelivery st nid with
  | .stored => [{ sink := nid, source := tid.toObjId }]
  | .toWaiter w =>
      [ { sink := w.toObjId, source := tid.toObjId }
      , { sink := w.toObjId, source := nid } ]
  | .toBound t => [{ sink := t.toObjId, source := tid.toObjId }]

/-- WS-SM SM9.D.10: **a waiter's edge** — `.notificationWait`.

The signal-before-wait ordering is why this arm is not optional: with no waiter
present the signal leaves the badge pending on the notification, and it is the
*wait* that moves it to the waiter.  Omitting this edge would lose hop 1 in one
of the two orderings, and the §3.6 chain — downgrade, ordinary delivery,
downgrade — would go undetected exactly half the time.

The wait reads the notification's stored-badge taint, then the notification is
**cleared** (`contentFlowClears`): a wait consumes the whole merged badge, so the
object holds nothing afterwards and its taint must not outlive the content — the
content-derived model, which the clear (running after the flow has read `pre`)
supplies without disturbing what the waiter received. -/
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
    | .send, .object epId => senderTaintEdges st tid epId (sendCarriesCaps cap decoded)
    | .call, .object epId => senderTaintEdges st tid epId (sendCarriesCaps cap decoded)
    | .receive, .object epId => receiverTaintEdges st tid epId
    | .replyRecv, .object epId =>
        receiverTaintEdges st tid epId ++ replyRecvReplyLegEdges st tid decoded
    | .reply, .replyCap rid => replyTaintEdges st tid rid
    | .notificationSignal, .object nid => signalTaintEdges st tid nid
    | .declassifySignal, .object nid => signalTaintEdges st tid nid
    | .notificationWait, .object nid => waitTaintEdges tid nid
    | _, _ => []

/-- WS-SM SM9.D.10: **the notification a signal empties**, if any.

A signal has two delivering orderings and they leave the object in different
states.  Delivery to a queued *waiter* stores nothing, so the notification ends
the commit holding no badge and its taint must not outlive that content.
Delivery to a *bound* TCB writes into that thread's `pendingMessage` and leaves
the notification untouched — so whatever badge it already held is still there,
and so is that badge's provenance.  Only the first ordering clears. -/
def signalClearedNotification (st : SystemState) (nid : SeLe4n.ObjId) :
    List SeLe4n.ObjId :=
  match signalDelivery st nid with
  | .toWaiter _ => [nid]
  | .stored => []
  | .toBound _ => []

/-- WS-SM SM9.D.10: **a bound delivery clears nothing** — the notification is not
written by `notificationSignalBound`, so a badge it already held stays, and so
must that badge's provenance. -/
@[simp] theorem signalClearedNotification_bound (st : SystemState) (nid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (ep : SeLe4n.ObjId)
    (h : boundDeliveryTarget? st nid = some (t, ep)) :
    signalClearedNotification st nid = [] := by
  simp [signalClearedNotification, signalDelivery, h]

/-- WS-SM SM9.D.10: **a waiter delivery empties the notification** — nothing is
stored, so its provenance goes with the content. -/
theorem signalClearedNotification_waiter (st : SystemState) (nid : SeLe4n.ObjId)
    (w : SeLe4n.ThreadId) (hb : boundDeliveryTarget? st nid = none)
    (hw : notificationSignalWaiter? st nid = some w) :
    signalClearedNotification st nid = [nid] := by
  simp [signalClearedNotification, signalDelivery, hb, hw]

/-- WS-SM SM9.D.10: **no receiver, no clear** — the badge is stored on the
notification, which is exactly where its taint belongs. -/
theorem signalClearedNotification_of_no_receiver (st : SystemState) (nid : SeLe4n.ObjId)
    (h : declassifiedSignalReceiver? st nid = none) :
    signalClearedNotification st nid = [] := by
  simp [signalClearedNotification, signalDelivery_stored_of_no_receiver st nid h]

/-- WS-SM SM9.D.10: **the notification a signal bypassed**, if any.

The third consumer of `signalDelivery`, and the one whose absence was the round-7
finding.  On the bound path the badge goes straight into the bound thread's
`pendingMessage`; the notification is not written at all, so a downgrade recorded
against it must not be originated onto it.  It is not *cleared* either — a badge
already stored there keeps its content and its provenance — which is why this is
a separate list rather than more entries in `cleared`. -/
def signalBypassedNotification (st : SystemState) (nid : SeLe4n.ObjId) :
    List SeLe4n.ObjId :=
  match signalDelivery st nid with
  | .toBound _ => [nid]
  | .toWaiter _ => []
  | .stored => []

/-- WS-SM SM9.D.10: the objects a content-moving syscall's delivery bypassed. -/
def contentFlowBypassed (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : List SeLe4n.ObjId :=
  match syscallOperandCap? st tid decoded.capAddr with
  | none => []
  | some cap =>
    match decoded.syscallId, cap.target with
    | .notificationSignal, .object nid => signalBypassedNotification st nid
    | .declassifySignal, .object nid => signalBypassedNotification st nid
    | _, _ => []

/-- WS-SM SM9.D.8 (**content-derived transport**): the transport objects a
content-moving syscall *empties*, so an object's taint reflects the content it
currently holds rather than everything that ever passed through it.

A `.notificationWait` consumes the whole pending badge, so the notification is
cleared once the waiter has read it; a signal delivered directly to a *waiter*
stores nothing, so its notification is cleared then too.  Endpoints never appear
here — they hold no content of their own (the message lives in the blocked
sender's TCB) and are not declared as taint sinks at all (`senderTaintEdges`),
so there is nothing on them to clear.

**The bound-delivery path is deliberately not a clear**, and the distinction is
load-bearing rather than fussy.  `boundDeliveryTarget?` requires only an empty
*waiter list* and a bound TCB parked on an endpoint — it says nothing about the
pending badge — and `notificationSignalBound` delivers into that TCB's
`pendingMessage` without touching the notification at all.  So a notification
that already holds a badge keeps it across a bound delivery, and clearing there
would discard the provenance of content the object still stores: a later
`.notificationWait` would then read that badge from an empty source and a
downgrade behind it would record no predecessor.  That is a *missed* chain, the
direction a detector must never err in, so the clear is restricted to the
ordering where delivery provably empties the object.  On the bound path with no
badge stored the clear would have been a no-op anyway
(`TaintTable.clearAt_eq_of_empty`), so nothing is lost by omitting it. -/
def contentFlowClears (st : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) : List SeLe4n.ObjId :=
  match syscallOperandCap? st tid decoded.capAddr with
  | none => []
  | some cap =>
    match decoded.syscallId, cap.target with
    | .notificationWait, .object nid => [nid]
    | .notificationSignal, .object nid => signalClearedNotification st nid
    | .declassifySignal, .object nid => signalClearedNotification st nid
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
  | .movesContent => { edges := contentFlowEdges st tid decoded,
                       cleared := contentFlowClears st tid decoded,
                       bypassed := contentFlowBypassed st tid decoded }
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

* flows first, and their sources are read from the **pre**-state's taint —
  **seeded with this commit's own origination**, so a syscall that both
  declassifies *and* delivers (`.declassifySignal`, whose second hop to a waiting
  receiver is an ordinary delivery) carries the fresh event's tag to the object
  the delivery reached.  Without the seed the receiver would read the target's
  pre-event taint and the fresh downgrade would have no successor — a missed
  chain, the direction a detector must never err in.  The seed is a no-op for
  every syscall that records nothing (`originationTags [] = []`);
* clears next, so a retype forgets provenance the same commit's flows could not
  have given it, and a consumed transport (a `.notificationWait`, or a signal
  delivered directly to a waiter) is emptied to the content it now holds;
* origination last on the committed table, because a downgrade's identity does
  not exist until the event is recorded, and it must land on the object the
  delivery reached — which the flows have just re-tainted.  **Cleared objects are
  excluded from this final pass**: a `.declassifySignal` that delivers straight to
  a waiter records the notification as its `targetObject` while storing no badge
  there, so tagging it would immediately undo the clear the step before and leave
  a fresh, *unsaturated* identity on an object holding nothing — inheritable by
  the next unrelated badge.  The exclusion is only on the final pass; the seed
  above keeps the full tag list, which is what carries the fresh event to the
  receiver that actually took the badge.  `taintWriteKeys` is unaffected, since
  it unions the cleared list in anyway. -/
def applySyscallTaint (plan : TaintPlan) (pre post : SystemState) : SystemState :=
  -- Bound once.  `newlyRecordedEvents` is `post.log.drop pre.log.length`, so each
  -- evaluation is two O(n) walks with n bounded at the SM9.A 256-entry cliff, and
  -- `applySyscallTaint` runs on EVERY syscall — inert plans included, since the
  -- entry always applies a plan.  Computing it twice made every syscall pay four
  -- list walks where two suffice.
  let origins := originationTags (newlyRecordedEvents pre post)
  { post with
      declassificationTaint :=
        applyOrigination
          (origins.filter (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
          (applyTaintClears plan.cleared
            (applyTaintFlow
              (applyOrigination origins pre.declassificationTaint)
              plan.edges
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
            applyOrigination
              ((originationTags (newlyRecordedEvents pre post)).filter
                (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
              (applyTaintClears plan.cleared
                (applyTaintFlow
                  (applyOrigination (originationTags (newlyRecordedEvents pre post))
                    pre.declassificationTaint)
                  plan.edges
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
        applyOrigination
          ((originationTags (newlyRecordedEvents pre post)).filter
            (fun p => !([] : List SeLe4n.ObjId).contains p.1))
          (applyTaintClears [] (applyTaintFlow
            (applyOrigination (originationTags (newlyRecordedEvents pre post))
              pre.declassificationTaint) []
            post.declassificationTaint)) } = post
  rw [hEvents]
  simp [originationTags, applyOrigination, applyTaintClears, applyTaintFlow]

-- ----------------------------------------------------------------------------
-- WS-SM SM9.D.17: per-step key frames, stated next to the steps they frame.
-- Each says the same thing about one fold: a key the step does not name is
-- carried through untouched.  `applySyscallTaint_frame_off_writeKeys` composes
-- the three, and `applySyscallTaint_cleared_empty` uses two of them.
-- ----------------------------------------------------------------------------

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

/-- WS-SM SM9.D.12: **a cleared key ends the fold empty** — carried as a
disjunction so the induction can hand the `o = c` case to its own tail. -/
private theorem applyTaintClears_empty_of_mem_or_empty (o : SeLe4n.ObjId) :
    ∀ (cleared : List SeLe4n.ObjId) (tbl : TaintTable),
      (o ∈ cleared ∨ tbl o = DeclassificationTaint.empty) →
      applyTaintClears cleared tbl o = DeclassificationTaint.empty := by
  intro cleared
  induction cleared with
  | nil =>
    intro tbl h
    rcases h with hm | he
    · exact absurd hm (by simp)
    · exact he
  | cons c rest ih =>
    intro tbl h
    show applyTaintClears rest (tbl.clearAt c) o = DeclassificationTaint.empty
    refine ih (tbl.clearAt c) ?_
    by_cases hoc : o = c
    · exact Or.inr (by rw [hoc]; exact TaintTable.clearAt_self tbl c)
    · rcases h with hm | he
      · rcases List.mem_cons.mp hm with hEq | hr
        · exact absurd hEq hoc
        · exact Or.inl hr
      · exact Or.inr (by rw [TaintTable.clearAt_ne tbl hoc]; exact he)

/-- WS-SM SM9.D.12 / SM9.D.10 (**a clear is final within its commit**): an object
the plan empties ends the commit empty — even when the *same* syscall recorded a
downgrade naming that object.

This is what makes the content-derived model hold for a declassifying signal that
delivers straight to a waiter: the notification is the event's `targetObject`, but
it stores no badge, so re-tagging it after the clear would leave a fresh
unsaturated identity on an object holding nothing, inheritable by the next
unrelated badge through it.  The final origination pass therefore skips every
cleared key (`applySyscallTaint`), and this theorem is the checkable form of
that. -/
theorem applySyscallTaint_cleared_empty (plan : TaintPlan) (pre post : SystemState)
    (o : SeLe4n.ObjId) (h : o ∈ plan.cleared) :
    (applySyscallTaint plan pre post).declassificationTaint o =
      DeclassificationTaint.empty := by
  have hOrigF : o ∉ ((originationTags (newlyRecordedEvents pre post)).filter
      (fun p => !(plan.cleared ++ plan.bypassed).contains p.1)).map (·.fst) := by
    intro hm
    obtain ⟨q, hq, hqo⟩ := List.mem_map.mp hm
    have hkeep := (List.mem_filter.mp hq).2
    rw [← hqo] at h
    simp [h] at hkeep
  show applyOrigination
      ((originationTags (newlyRecordedEvents pre post)).filter
        (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
      (applyTaintClears plan.cleared
        (applyTaintFlow
          (applyOrigination (originationTags (newlyRecordedEvents pre post))
            pre.declassificationTaint)
          plan.edges post.declassificationTaint)) o = DeclassificationTaint.empty
  rw [applyOrigination_not_mem o _ _ hOrigF]
  exact applyTaintClears_empty_of_mem_or_empty o plan.cleared _ (Or.inl h)

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

The hypothesis is `e.sink ∉ plan.cleared`, not `plan.cleared = []`: a
content-moving plan now empties the transports it consumes (`contentFlowClears` —
a `.notificationWait`, or a signal delivered to a waiter), so a flow whose sink
were one of those cleared objects would genuinely be undone.  Every declared
flow's sink is a *subject* (a TCB, a CNode) or a *stored* notification, none of
which a same-commit clear names, so the per-site corollaries discharge it
directly.

The source is read from the origination-seeded pre-table (`applySyscallTaint`),
which only *adds* tags, so the raw-pre-table hypothesis suffices by monotonicity
(`contains_applyOrigination_mono`). -/
theorem taintPropagation_edge (plan : TaintPlan) (pre post : SystemState)
    (e : TaintFlowEdge) (hMem : e ∈ plan.edges) (hClear : e.sink ∉ plan.cleared) {t : Nat}
    (hSrc : (pre.declassificationTaint e.source).contains t = true) :
    ((applySyscallTaint plan pre post).declassificationTaint e.sink).contains t = true := by
  show ((applyOrigination
      ((originationTags (newlyRecordedEvents pre post)).filter
        (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
      (applyTaintClears plan.cleared
        (applyTaintFlow
          (applyOrigination (originationTags (newlyRecordedEvents pre post))
            pre.declassificationTaint)
          plan.edges post.declassificationTaint))) e.sink).contains t = true
  refine contains_applyOrigination_mono _ _ e.sink ?_
  refine contains_applyTaintClears_of_not_mem plan.cleared _ e.sink hClear ?_
  exact contains_applyTaintFlow_of_mem
    (applyOrigination (originationTags (newlyRecordedEvents pre post))
      pre.declassificationTaint)
    plan.edges post.declassificationTaint e hMem
    (contains_applyOrigination_mono _ pre.declassificationTaint e.source hSrc)

/-- WS-SM SM9.D.13a (**origination**): a downgrade recorded by this commit tags
the object its content landed in.

Together with `taintPropagation_edge` this is the whole of how a tag gets onto
an object: a declassification originates it, and ordinary delivery moves it.

**Unless the same commit emptied that object.**  A downgrade whose content was
handed straight to a waiter records the transport as its `targetObject` while
storing nothing there, and the content-derived model says an object that holds
nothing carries no provenance — so the target must not be re-tagged after the
clear (`applySyscallTaint`).  The hypothesis is discharged at every per-site
corollary, because the objects a plan clears and the objects a downgrade targets
coincide only in that delivered-onward case, where
`taintOrigination_target_cleared` states the opposite and the receiver holds the
tag instead. -/
theorem taintOrigination_target (plan : TaintPlan) (pre post : SystemState)
    (ev : DeclassificationEvent) (hMem : ev ∈ newlyRecordedEvents pre post)
    (hClear : ev.targetObject ∉ plan.cleared ++ plan.bypassed) :
    ((applySyscallTaint plan pre post).declassificationTaint ev.targetObject).contains
      ev.timestamp = true := by
  show ((applyOrigination
    ((originationTags (newlyRecordedEvents pre post)).filter
      (fun p => !(plan.cleared ++ plan.bypassed).contains p.1)) _)
    ev.targetObject).contains ev.timestamp = true
  exact contains_applyOrigination_of_mem _ _ (ev.targetObject, ev.timestamp)
    (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨ev, hMem, by simp⟩, by simp [hClear]⟩)

/-- WS-SM SM9.D.13a (**origination, actor half**): a downgrade also tags the
subject that performed it, so a subject that releases content twice carries the
first release's identity into the second's snapshot.

Without this the `.declassify`-then-`.declassify` chain — the simplest laundering
shape there is — would carry no predecessor and go undetected. -/
theorem taintOrigination_actor (plan : TaintPlan) (pre post : SystemState)
    (ev : DeclassificationEvent) (hMem : ev ∈ newlyRecordedEvents pre post)
    (hClear : ev.sourceSubject ∉ plan.cleared ++ plan.bypassed) :
    ((applySyscallTaint plan pre post).declassificationTaint ev.sourceSubject).contains
      ev.timestamp = true := by
  show ((applyOrigination
    ((originationTags (newlyRecordedEvents pre post)).filter
      (fun p => !(plan.cleared ++ plan.bypassed).contains p.1)) _)
    ev.sourceSubject).contains ev.timestamp = true
  exact contains_applyOrigination_of_mem _ _ (ev.sourceSubject, ev.timestamp)
    (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨ev, hMem, by simp⟩, by simp [hClear]⟩)

/-- WS-SM SM9.D.8: the edge a content-moving syscall's plan carries, named once
so every per-site corollary below reads the same resolution. -/
private theorem mem_movesContent_edges {st : SystemState} {tid : SeLe4n.ThreadId}
    {decoded : SyscallDecodeResult} {e : TaintFlowEdge}
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hMem : e ∈ contentFlowEdges st tid decoded) :
    e ∈ (syscallTaintPlan st tid decoded).edges ∧
      (syscallTaintPlan st tid decoded).cleared = contentFlowClears st tid decoded := by
  constructor
  · simp only [syscallTaintPlan, hClass]; exact hMem
  · simp only [syscallTaintPlan, hClass]

-- WS-SM SM9.D.8 (**content-derived**): there is deliberately no
-- `taintPropagation_send_to_endpoint`.  A `.send`/`.call` declares no endpoint
-- sink (`senderTaintEdges`), so it leaves the endpoint's provenance untouched —
-- an endpoint buffers no content of its own, the delivered message rides the
-- direct receiver edge (`taintPropagation_send_to_receiver`) or stays in the
-- blocked sender's TCB, and a receiver reads the head sender directly rather than
-- an endpoint proxy.  This is what closes the stale-endpoint false positive;
-- `SmpInformationFlowSuite` §12 exhibits the untouched endpoint on concrete
-- distinct object ids.

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
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hSender
  rw [hCleared]; rcases hSid with h | h <;> simp [contentFlowClears, hCap, h, hTarget]

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
    (hTcb : st.getTcb? receiver = some rtcb)
    (hCaps : sendCarriesCaps cap decoded = true) {t : Nat}
    (hSender : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      rtcb.cspaceRoot).contains t = true := by
  have hCT : ({ sink := rtcb.cspaceRoot, source := tid.toObjId } : TaintFlowEdge) ∈
      capTransferTaintSinks st tid receiver (sendCarriesCaps cap decoded) := by
    simp only [capTransferTaintSinks, hCaps, hTcb]
    cases st.getTcb? tid <;> simp
  have hMem : ({ sink := rtcb.cspaceRoot, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget, senderTaintEdges, hRecv] <;>
      exact List.mem_cons_of_mem _ hCT
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hSender
  rw [hCleared]; rcases hSid with h | h <;> simp [contentFlowClears, hCap, h, hTarget]

/-- WS-SM SM9.D.8 (**receive / replyRecv ← sender**): a receiver picks up the
provenance of the blocked sender at `sendQ.head` directly — whether that sender
parked in an earlier syscall or arrives in this rendezvous.  The content-derived
model: there is no endpoint proxy to read, and the head-sender edge is exact
where a proxy would over-approximate to every queued sender. -/
theorem taintPropagation_receive_from_sender (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (epId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .receive ∨ decoded.syscallId = .replyRecv)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId)
    (hSender : (st.getEndpoint? epId).bind (·.sendQ.head) = some sender) {t : Nat}
    (hSrc : (st.declassificationTaint sender.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      tid.toObjId).contains t = true := by
  have hMem : ({ sink := tid.toObjId, source := sender.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h
    · simp [h, hTarget, receiverTaintEdges, hSender]
    · simp only [h, hTarget]
      exact List.mem_append_left _ (by simp [receiverTaintEdges, hSender])
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hSrc
  rw [hCleared]; rcases hSid with h | h <;> simp [contentFlowClears, hCap, h, hTarget]

-- Three receive-side theorems are deliberately GONE, not moved: they asserted
-- capability provenance on a path that installs nothing.
--
--   * `taintPropagation_queued_receive_to_cspace` — the queued transfer's CNode
--     sink.  Added when the receive was believed to unwrap; it does not.
--   * `taintPropagation_cspace_taints_consumer` — the root-to-subject feedback.
--     Ungated, it tagged a receiver from an unrelated earlier transfer's
--     provenance on an ordinary capless delivery.
--   * `taintPropagation_transfer_taints_receiver` — the receive-side direct
--     sender-root edge, which has no transfer to describe here.
--
-- The send ordering keeps all three properties, because the live send really
-- does unwrap.  Restoring these belongs with wiring the receive through
-- `endpointReceiveDualWithCaps`, tracked in the fine-lock plan.

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
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hReplier
  rw [hCleared]; simp [contentFlowClears, hCap, hSid, hTarget]

/-- WS-SM SM9.D.9 (**replyRecv → previous caller**): the reply half of the
server's steady-state loop carries the server's provenance to the caller the
reply object records — the hop a receive-leg-only plan would lose. -/
theorem taintPropagation_replyRecv_reply_to_prevCaller (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap rcap : Capability)
    (epId : SeLe4n.ObjId) (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId)
    (rargs : Architecture.SyscallArgDecode.ReplyRecvArgs)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .replyRecv)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId)
    (hLen : (decoded.msgInfo.length == 0) = false)
    (hArgs : Architecture.SyscallArgDecode.decodeReplyRecvArgs decoded = .ok rargs)
    (hRCap : syscallOperandCap? st tid (SeLe4n.CPtr.ofNat rargs.replyCPtr) = some rcap)
    (hRTarget : rcap.target = .replyCap rid)
    (hCaller : (st.getReply? rid).bind (·.caller) = some prevCaller) {t : Nat}
    (hServer : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      prevCaller.toObjId).contains t = true := by
  have hMem : ({ sink := prevCaller.toObjId, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap, hSid, hTarget, List.mem_append]
    refine Or.inr ?_
    simp only [replyRecvReplyLegEdges, hLen, hArgs, hRCap, hRTarget]
    simp [replyTaintEdges, hCaller]
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hServer
  rw [hCleared]; simp [contentFlowClears, hCap, hSid, hTarget]

/-- WS-SM SM9.D.10 (**signal → notification, stored**): when no waiter is present
the badge is stored on the notification, so it carries the signaller's provenance
there until a `.notificationWait` consumes it.

Restricted to the no-waiter case (`declassifiedSignalReceiver? = none`): with a
waiter the badge is delivered directly and nothing is stored — the notification
is cleared, not tagged (`contentFlowClears`), which is the content-derived model
and what closes the stale-notification false positive. -/
theorem taintPropagation_signal_to_notification (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap : Capability)
    (nid : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .notificationSignal ∨ decoded.syscallId = .declassifySignal)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object nid)
    (hNoWaiter : declassifiedSignalReceiver? st nid = none) {t : Nat}
    (hSignaller : (st.declassificationTaint tid.toObjId).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      nid).contains t = true := by
  have hMem : ({ sink := nid, source := tid.toObjId } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;>
      simp [h, hTarget, signalTaintEdges, signalDelivery_stored_of_no_receiver st nid hNoWaiter]
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hSignaller
  rw [hCleared]; rcases hSid with h | h <;>
    simp [contentFlowClears, hCap, h, hTarget,
      signalClearedNotification_of_no_receiver st nid hNoWaiter]

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
    (hTarget : cap.target = .object nid)
    (hNe : tid.toObjId ≠ nid) {t : Nat}
    (hNotification : (st.declassificationTaint nid).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      tid.toObjId).contains t = true := by
  have hMem : ({ sink := tid.toObjId, source := nid } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap, hSid, hTarget]
    simp [waitTaintEdges]
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hNotification
  rw [hCleared]; simp [contentFlowClears, hCap, hSid, hTarget, hNe]

/-- WS-SM SM9.D.10 (**the consumed transport is emptied**): after a
`.notificationWait` the notification carries **no** provenance.

The content-derived model made checkable: a wait consumes the whole pending
badge, so the object holds nothing afterwards and its taint must not outlive it.
Without this a later, unrelated badge through the same notification would hand
its receiver the previous badge's identity — a specific, unsaturated false
positive, which is exactly what `staleTaint_is_not_saturation` says must not
exist.

No trail hypothesis is needed: the final origination pass skips cleared keys
(`applySyscallTaint_cleared_empty`), so the notification ends empty whatever the
commit recorded — which is the property the bound-delivery ordering needed and
the reason the clear and the origination can no longer fight. -/
theorem waitClearsNotificationTaint (st post : SystemState) (tid : SeLe4n.ThreadId)
    (decoded : SyscallDecodeResult) (cap : Capability) (nid : SeLe4n.ObjId)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .notificationWait)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object nid) :
    (applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint nid =
      DeclassificationTaint.empty := by
  have hCleared : (syscallTaintPlan st tid decoded).cleared = [nid] := by
    simp only [syscallTaintPlan, hClass]
    simp [contentFlowClears, hCap, hSid, hTarget]
  exact applySyscallTaint_cleared_empty _ st post nid (by rw [hCleared]; simp)

/-- WS-SM SM9.D.11 (**the CSpace provenance is consumed**): a capability
transfer reads the *sender's* CSpace-root taint into the receiver's root, so a
capability an earlier transfer installed carries its chain forward when it is
forwarded again.

Without this edge the tag `capTransferTaintSinks` writes would be an unwired
structure — written on a CSpace root and read by nothing, since no other edge
sources from one — and a capability forwarded by an untainted courier would drop
the link at exactly the hop the detector is looking for. -/
theorem taintPropagation_cspace_provenance_forwarded (st post : SystemState)
    (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult) (cap : Capability)
    (epId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (rtcb stcb : SeLe4n.Model.TCB)
    (hClass : contentFlowClass decoded.syscallId = .movesContent)
    (hSid : decoded.syscallId = .send ∨ decoded.syscallId = .call)
    (hCap : syscallOperandCap? st tid decoded.capAddr = some cap)
    (hTarget : cap.target = .object epId)
    (hRecv : (st.getEndpoint? epId).bind (·.receiveQ.head) = some receiver)
    (hRTcb : st.getTcb? receiver = some rtcb)
    (hSTcb : st.getTcb? tid = some stcb)
    (hCaps : sendCarriesCaps cap decoded = true) {t : Nat}
    (hSenderCSpace : (st.declassificationTaint stcb.cspaceRoot).contains t = true) :
    ((applySyscallTaint (syscallTaintPlan st tid decoded) st post).declassificationTaint
      rtcb.cspaceRoot).contains t = true := by
  have hCT : ({ sink := rtcb.cspaceRoot, source := stcb.cspaceRoot } : TaintFlowEdge) ∈
      capTransferTaintSinks st tid receiver (sendCarriesCaps cap decoded) := by
    simp [capTransferTaintSinks, hCaps, hRTcb, hSTcb]
  have hMem : ({ sink := rtcb.cspaceRoot, source := stcb.cspaceRoot } : TaintFlowEdge) ∈
      contentFlowEdges st tid decoded := by
    simp only [contentFlowEdges, hCap]
    rcases hSid with h | h <;> simp only [h, hTarget, senderTaintEdges, hRecv] <;>
      exact List.mem_cons_of_mem _ hCT
  obtain ⟨hIn, hCleared⟩ := mem_movesContent_edges hClass hMem
  refine taintPropagation_edge _ st post _ hIn ?_ hSenderCSpace
  rw [hCleared]; rcases hSid with h | h <;> simp [contentFlowClears, hCap, h, hTarget]

/-- WS-SM SM9.D.11 (**a plain message installs nothing**): a delivery carrying no
capabilities declares no CSpace sink at all.

The load-bearing negative for the gate.  Without it the sender's provenance would
be written into a CSpace root no capability reached, and — since a root now feeds
the consuming subject — an unrelated later downgrade could name that as an
*unsaturated* predecessor.  That is exactly the false positive
`staleTaint_is_not_saturation` rules out, so over-approximating here would break
a stated property rather than merely cost precision. -/
@[simp] theorem capTransferTaintSinks_capless (st : SystemState)
    (tid receiver : SeLe4n.ThreadId) :
    capTransferTaintSinks st tid receiver false = [] := rfl

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

No hypothesis on the trail is needed — the final origination pass skips cleared
keys — so this holds for an arbitrary pre/post pair rather than only for the
retype's own (event-free) commit, and the lifecycle layer owes nothing here. -/
theorem retypedObject_taint_empty (plan : TaintPlan) (pre post : SystemState)
    (oid : SeLe4n.ObjId) (hPlan : plan = { edges := [], cleared := [oid] }) :
    (applySyscallTaint plan pre post).declassificationTaint oid =
      DeclassificationTaint.empty := by
  subst hPlan
  exact applySyscallTaint_cleared_empty _ pre post oid (by simp)

/-- WS-SM SM9.D.10 (**the bound-delivery family, in one place**): on the bound
path the notification is not written, so all three of its taint consumers agree
that nothing about it changes.

Bound delivery produced three separate findings across three review rounds — the
clear, the edge, and the origination — because each consumer re-derived its own
answer from `declassifiedSignalReceiver?`, which cannot tell a bound target from
a waiter.  Deriving all three from `signalDelivery` makes disagreement
unwritable, and this theorem is that agreement stated once. -/
theorem signalDelivery_bound_leaves_notification_alone (st : SystemState)
    (nid : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (t : SeLe4n.ThreadId)
    (h : signalDelivery st nid = .toBound t) :
    signalClearedNotification st nid = [] ∧
    signalBypassedNotification st nid = [nid] ∧
    signalTaintEdges st tid nid = [{ sink := t.toObjId, source := tid.toObjId }] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [signalClearedNotification, signalBypassedNotification, signalTaintEdges, h]

/-- WS-SM SM9.D.10 (**the waiter path, for contrast**): delivery to a queued
waiter empties the notification, so it *is* cleared, is not bypassed, and the
receiver takes both the signaller's content and the notification's entry — the
latter carrying the fresh event through the origination seed. -/
theorem signalDelivery_waiter_empties_notification (st : SystemState)
    (nid : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (w : SeLe4n.ThreadId)
    (h : signalDelivery st nid = .toWaiter w) :
    signalClearedNotification st nid = [nid] ∧
    signalBypassedNotification st nid = [] ∧
    signalTaintEdges st tid nid =
      [ { sink := w.toObjId, source := tid.toObjId }
      , { sink := w.toObjId, source := nid } ] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [signalClearedNotification, signalBypassedNotification, signalTaintEdges, h]

/-- WS-SM SM9.D.10 (**a bypassed object keeps what it had**): the fresh event is
not originated onto a notification the delivery went around, and — unlike a
clear — its existing provenance survives untouched.

This is the round-7 property: the bound path records the notification as the
event's `targetObject`, but the badge never landed there, so tagging it would
attach a fresh unsaturated identity to an object holding either nothing or a
*different*, still-stored badge. -/
theorem bypassedObject_not_originated (plan : TaintPlan) (pre post : SystemState)
    (o : SeLe4n.ObjId) (hBypass : o ∈ plan.bypassed) (hClear : o ∉ plan.cleared)
    (hFlow : o ∉ plan.edges.map (fun e => e.sink)) :
    (applySyscallTaint plan pre post).declassificationTaint o =
      post.declassificationTaint o := by
  have hOrigF : o ∉ ((originationTags (newlyRecordedEvents pre post)).filter
      (fun p => !(plan.cleared ++ plan.bypassed).contains p.1)).map (·.fst) := by
    intro hm
    obtain ⟨q, hq, hqo⟩ := List.mem_map.mp hm
    have hkeep := (List.mem_filter.mp hq).2
    rw [← hqo] at hBypass
    simp [hBypass] at hkeep
  show applyOrigination
      ((originationTags (newlyRecordedEvents pre post)).filter
        (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
      (applyTaintClears plan.cleared
        (applyTaintFlow
          (applyOrigination (originationTags (newlyRecordedEvents pre post))
            pre.declassificationTaint)
          plan.edges post.declassificationTaint)) o = post.declassificationTaint o
  rw [applyOrigination_not_mem o _ _ hOrigF,
      applyTaintClears_not_mem o _ _ hClear,
      applyTaintFlow_not_mem _ o _ _ hFlow]

/-- WS-SM SM9.D.12 / SM9.D.15 (**the distinction that keeps the residual claim
true**): stale taint is **not** saturation.

The over-approximation SM9.D.15 accepts is the saturating top: an object that
has received more than `maxTaintTags` distinct downgrades names identities it
never received.  Taint that outlives the content it describes would produce a
*different* imprecision — a specific, unsaturated identity attached to an object
that never received anything from it — and the two must not be conflated,
because the claim "the residual imprecision is saturation" would be false the day
it was written.

There are exactly **two** ways an object can outlive its content, and both are
closed by a clear rather than a frame:

* a **retype** re-purposes the object at the same id (`retypeClearedObjects`), so
  a framed retype would leave a destroyed object's tags on its replacement;
* a **consumed transport** — a `.notificationWait` takes the whole pending badge,
  and a signal delivered straight to a waiter stores none — so a framed
  notification would hand the *next* unrelated badge's receiver the previous
  one's provenance (`contentFlowClears`).  Endpoints cannot produce this at all,
  because they are not taint sinks: they buffer no content of their own, and a
  receiver reads the head sender directly (`senderTaintEdges`).

With both closed, the residual really is saturation.

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
  have hOrigF : o ∉ ((originationTags (newlyRecordedEvents pre post)).filter
      (fun p => !(plan.cleared ++ plan.bypassed).contains p.1)).map (·.fst) := by
    intro hm
    obtain ⟨q, hq, hqo⟩ := List.mem_map.mp hm
    exact hOrig (List.mem_map.mpr ⟨q, (List.mem_filter.mp hq).1, hqo⟩)
  show applyOrigination
      ((originationTags (newlyRecordedEvents pre post)).filter
        (fun p => !(plan.cleared ++ plan.bypassed).contains p.1))
      (applyTaintClears plan.cleared
        (applyTaintFlow
          (applyOrigination (originationTags (newlyRecordedEvents pre post))
            pre.declassificationTaint)
          plan.edges post.declassificationTaint)) o = post.declassificationTaint o
  rw [applyOrigination_not_mem o _ _ hOrigF,
      applyTaintClears_not_mem o _ _ hClear,
      applyTaintFlow_not_mem _ o _ _ hFlow]

/-- WS-SM SM9.D.17: two plans whose write sets are disjoint touch disjoint keys,
so **applying both preserves each one's result at its own keys** — in either
order, and at every key.

The model-level content of "the object's own lock is a sufficient serialization
subject": with disjoint write sets the two updates are independent, which is
exactly the property a per-object representation realises and a single
whole-field word would not.

Both plans are genuinely applied here.  An earlier form of this theorem bound
`planA` and then concluded only about `planB`, which made it a restatement of
`applySyscallTaint_frame_off_writeKeys` — true, but silent about composition,
and therefore silent about the very thing the footprint argument cites it for.
The composition is taken over a **common** state, since that is the shape two
concurrent commits have. -/
theorem taintWriteKeys_disjoint_updates_independent
    (planA planB : TaintPlan) (pre st : SystemState) (o : SeLe4n.ObjId)
    (hA : o ∈ taintWriteKeys planA pre st)
    (hDisj : ∀ k ∈ taintWriteKeys planA pre st, k ∉ taintWriteKeys planB pre st)
    (hKeysB : taintWriteKeys planB pre (applySyscallTaint planA pre st)
      = taintWriteKeys planB pre st) :
    -- B's application leaves A's key alone …
    (applySyscallTaint planB pre st).declassificationTaint o =
      st.declassificationTaint o ∧
    -- … and A's result at that key survives B being applied on top of it.
    (applySyscallTaint planB pre (applySyscallTaint planA pre st)).declassificationTaint o =
      (applySyscallTaint planA pre st).declassificationTaint o := by
  have hNotB : o ∉ taintWriteKeys planB pre st := hDisj o hA
  refine ⟨applySyscallTaint_frame_off_writeKeys planB pre st o hNotB, ?_⟩
  exact applySyscallTaint_frame_off_writeKeys planB pre (applySyscallTaint planA pre st) o
    (by rw [hKeysB]; exact hNotB)

/-- WS-SM SM9.D.17 (**order-independence at a disjoint key**): with disjoint
write sets, the key `planA` writes ends up carrying `planA`'s value whichever
order the two plans are applied in.

The composition statement the per-object serialization argument actually needs:
not merely that each plan frames the other's keys, but that the *interleaving*
cannot change the outcome — which is what makes two concurrent commits holding
different object locks safe. -/
theorem taintWriteKeys_disjoint_order_independent
    (planA planB : TaintPlan) (pre st : SystemState) (o : SeLe4n.ObjId)
    (hA : o ∈ taintWriteKeys planA pre st)
    (hDisj : ∀ k ∈ taintWriteKeys planA pre st, k ∉ taintWriteKeys planB pre st)
    (hKeysB : taintWriteKeys planB pre (applySyscallTaint planA pre st)
      = taintWriteKeys planB pre st)
    -- `planA`'s effect at its own key is computed from the same inputs either
    -- way: its sources are read from `pre`, and `planB` did not touch `o`.
    (hStable :
      (applySyscallTaint planA pre (applySyscallTaint planB pre st)).declassificationTaint o =
        (applySyscallTaint planA pre st).declassificationTaint o) :
    (applySyscallTaint planB pre (applySyscallTaint planA pre st)).declassificationTaint o =
      (applySyscallTaint planA pre (applySyscallTaint planB pre st)).declassificationTaint o := by
  rw [hStable]
  exact applySyscallTaint_frame_off_writeKeys planB pre (applySyscallTaint planA pre st) o
    (by rw [hKeysB]; exact hDisj o hA)

/-- WS-SM SM9.D.17: **the trail writers are the only originators.**

A syscall that appends no audit event has an empty origination set, so its taint
write set is confined to the objects its own edges and clears name — each of
which the transition itself writes.  All but one of those writes ride a
declared write lock; the exception is the capability-transfer sink, the
receiver's CSpace root, whose write the send/call footprints have never
declared — a pre-existing SM3.B gap this phase's audit surfaced and registered
(`UncoveredLockDomain.capTransferReceiverCnode`,
`capTransfer_receiverCnode_write_undeclared`), not a property of the taint
layer: the taint write at that key is exactly as covered as the object write
it shadows.  The two syscalls that *do* append (`.declassify`,
`.declassifySignal`) are exactly the two whose footprints already carry
`stateLevelLock` in write mode for the append, which is what covers their
actor-TCB origination key. -/
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
