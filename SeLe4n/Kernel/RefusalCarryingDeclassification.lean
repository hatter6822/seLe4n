-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingDispatch

/-!
# The declassification and audit calls on the register file

WS-ZA ZA5.13.  The two declassifications (`.declassify`, `.declassifySignal`)
and the audit pair (`.auditRead`, `.auditDrain`) are routed on the register file
as the entry's `audited` arm (`Architecture.RegisterDecode.routedAudited`),
behind the shared operand check (`dispatchOperandCheckedR`), equal to
`dispatchSyscallChecked` (`dispatchAuditedCheckedR_eq`).

Each call has an **admitted** form and a general one, as seL4 splits an
invocation into its decode and its perform (`RefusalCarrying.ofChecked`).  The
admission is every check the specification makes, read from the state before
anything is written; when it holds, the call writes in place — a downgrade's
event over the audit ring's next slot (`DeclassificationEvent.overwrite`,
`AuditRing.recordEvent`), the snapshot words read off the actor as scalars
(`withTaintWordsAt`); an audit read's word computed by walking the ring's live
window, never building the trail (`AuditRing.toList`) or its visible view —
and is proven to be what the specification does.  Otherwise the call takes the
specification's arm (`auditedArmSpec`), whose refusals all precede its writes,
so every refusal carries the state the call was handed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode (routedAudited)

/-! ## The specification's arm, read from the register file -/

/-- The decode record a routed declassification or audit call stands for, as
far as its arm reads it: the syscall, the operand address and the layout's
message registers read from the caller's file (`dispatchWithCapChecked_eq_auditedArmSpec`). -/
def auditedDecoded (sid : SyscallId) (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) :
    SyscallDecodeResult :=
  { capAddr, msgInfo := ⟨routedLength regs, 0, 0, 0⟩, syscallId := sid,
    msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs),
    inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size }

/-- The gate a routed declassification or audit call's arm reads: only its
required right (`dispatchWithCapChecked_eq_auditedArmSpec`). -/
def auditedGate (tid : SeLe4n.ThreadId) (capAddr : SeLe4n.CPtr) (sid : SyscallId) : SyscallGate :=
  { callerId := tid, cspaceRoot := ⟨0⟩, capAddr, capDepth := 0,
    requiredRight := syscallRequiredRight sid }

/-- **The general form**: `dispatchWithCapChecked`'s arm for a routed
declassification or audit call, on the record and gate it reads.  Built only
on a call the admitted form does not take. -/
def auditedArmSpec (ctx : LabelingContext) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : Kernel Unit :=
  dispatchWithCapChecked ctx (auditedDecoded sid capAddr regs) tid executingCore
    (auditedGate tid capAddr sid) cap

/-- A routed declassification or audit call's arm reads its decode only through
the syscall and the message registers, and its gate only through the right. -/
theorem dispatchWithCapChecked_eq_auditedArmSpec (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (h : routedAudited decoded.syscallId = true)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (hRight : gate.requiredRight = syscallRequiredRight decoded.syscallId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      auditedArmSpec ctx decoded.syscallId decoded.capAddr regs tid executingCore cap := by
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  have hR : ∀ i, i < 4 → Architecture.SyscallArgDecode.requireMsgReg msgRegs i =
      Architecture.SyscallArgDecode.requireMsgReg
        (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) i := hRegs
  simp only at h hRight hLen
  unfold auditedArmSpec
  cases sid <;> simp only [routedAudited, Bool.false_eq_true] at h <;>
    simp (disch := decide) only [dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded,
      auditedGate, hR, hLen, Architecture.SyscallArgDecode.requireMessageLength,
      hRight,
      Architecture.SyscallArgDecode.decodeAuditReadArgs,
      Architecture.SyscallArgDecode.decodeAuditDrainArgs]

/-! ## `.declassify` -/

/-- Whether a `.declassify` of `targetId` by the subject `actorTid` is admitted:
the checks `declassifyObjectFromCore` makes, in its order — the target is
present, the base lattice denies the flow (`legacyLattice_canFlow_embed`: the
embedded legacy relation is `securityFlowsTo`), the declassification policy
permits it, and the trail has room. -/
@[inline] def declassifyAdmitted (ctx : LabelingContext) (st : SystemState)
    (actorTid : SeLe4n.ThreadId) (targetId : SeLe4n.ObjId) : Bool :=
  (st.getObjectType? targetId).isSome &&
    !securityFlowsTo (ctx.threadLabelOf actorTid) (ctx.objectLabelOf targetId) &&
    ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf actorTid))
      (embedLegacyLabel (ctx.objectLabelOf targetId)) &&
    decide (st.declassificationAudit.length < maxDeclassificationAuditEntries)

/-- **A downgrade's event written over the audit ring's next slot**
(`AuditRing.recordEvent`, `DeclassificationEvent.overwrite`), stamped `ts` and
carrying the actor's taint words handed in as scalars.  Out of line, so the
stamp and the words are read before the state is handed over
(`recordEventInPlace_eq`). -/
@[noinline] def recordEventInPlace (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (ts : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (st : SystemState) : SystemState :=
  { st with
    declassificationAudit := st.declassificationAudit.recordEvent actorDomain dstDomain targetId
      ts c actorTid actorDomain a0 a1 a2 a3 a4 a5 a6 a7 ac as }

/-- The in-place record is the ring's record of the event the state stamps. -/
theorem recordEventInPlace_eq (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (w : TaintWords)
    (st : SystemState) :
    recordEventInPlace c actorTid actorDomain dstDomain targetId
        (st.declassificationAudit.epoch + st.declassificationAudit.length)
        w.tag0 w.tag1 w.tag2 w.tag3 w.tag4 w.tag5 w.tag6 w.tag7 w.count w.saturated st =
      { st with
        declassificationAudit := st.declassificationAudit.append
          (declassifyStoreEventWithTags c { subject := actorTid, domain := actorDomain }
            actorDomain dstDomain targetId w st) } := by
  unfold recordEventInPlace
  rw [AuditRing.recordEvent_eq]
  rfl

/-- **An admitted downgrade's writes**: its event over the ring's next slot
(`recordEventInPlace`), then its taint step (`declassifyTaintStep`), over the
stamp, the words and the bypass bit read before the state is handed over
(`declassifyPerform_eq`). -/
@[noinline] def declassifyPerform (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (nrB : Bool)
    (epoch len : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool) (st : SystemState) : SystemState :=
  declassifyTaintStep nrB targetId epoch len
    (recordEventInPlace c actorTid actorDomain dstDomain targetId (epoch + len) a0 a1 a2 a3 a4 a5 a6 a7 ac as st)

/-- The admitted downgrade's writes are the specification's record of the event
the pre-state stamps, then the taint step. -/
theorem declassifyPerform_eq (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (nrB : Bool)
    (st : SystemState) :
    declassifyPerform c actorTid actorDomain dstDomain targetId nrB
        st.declassificationAudit.epoch st.declassificationAudit.length
        (st.taintWordsAt actorTid.toObjId).tag0 (st.taintWordsAt actorTid.toObjId).tag1
        (st.taintWordsAt actorTid.toObjId).tag2 (st.taintWordsAt actorTid.toObjId).tag3
        (st.taintWordsAt actorTid.toObjId).tag4 (st.taintWordsAt actorTid.toObjId).tag5
        (st.taintWordsAt actorTid.toObjId).tag6 (st.taintWordsAt actorTid.toObjId).tag7
        (st.taintWordsAt actorTid.toObjId).count (st.taintWordsAt actorTid.toObjId).saturated
        st =
      declassifyTaintStep nrB targetId st.declassificationAudit.epoch
        st.declassificationAudit.length
        { st with
          declassificationAudit := st.declassificationAudit.append
            (declassifyStoreEvent c { subject := actorTid, domain := actorDomain } actorDomain
              dstDomain targetId st) } := by
  unfold declassifyPerform
  rw [recordEventInPlace_eq]

/-- An admitted `.declassify` is the specification's record of its event. -/
theorem auditedArmSpec_declassify_admitted (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (targetId : SeLe4n.ObjId) (actorTid : SeLe4n.ThreadId)
    (hT : cap.target = .object targetId)
    (hCur : st.scheduler.currentOnCore executingCore = some actorTid)
    (hA : declassifyAdmitted ctx st actorTid targetId = true) :
    auditedArmSpec ctx .declassify capAddr regs tid executingCore cap st =
      .ok ((), { st with
        declassificationAudit := st.declassificationAudit.append
          (declassifyStoreEvent executingCore
            { subject := actorTid, domain := embedLegacyLabel (ctx.threadLabelOf actorTid) }
            (embedLegacyLabel (ctx.threadLabelOf actorTid))
            (embedLegacyLabel (ctx.objectLabelOf targetId)) targetId st) }) := by
  simp only [declassifyAdmitted, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hA
  obtain ⟨⟨⟨hPresent, hFlow⟩, hDecl⟩, hRoom⟩ := hA
  obtain ⟨ty, hTy⟩ := Option.isSome_iff_exists.mp hPresent
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    declassifyObjectFromCore, hCur, hTy, authorizeDeclassificationOnCore,
    declassificationDecision, liftLegacyContext, legacyLattice_canFlow_embed, hFlow, hDecl,
    Bool.false_eq_true, ↓reduceIte, recordDeclassificationChecked, hRoom,
    declassificationActorOf]

/-- **Why a `.declassify` that `declassifyAdmitted` refuses is refused**, in
`declassifyObjectFromCore`'s order: the target absent (`.objectNotFound`), the
base lattice already permitting the flow (`.flowDenied`), the declassification
policy denying it (`.declassificationDenied`), and otherwise the trail full
(`.auditLogCapacityExceeded`).  A scalar, read before anything is written
(`auditedArmSpec_declassify_refused`). -/
@[inline] def declassifyRefusal (ctx : LabelingContext) (st : SystemState)
    (actorTid : SeLe4n.ThreadId) (targetId : SeLe4n.ObjId) : KernelError :=
  if (st.getObjectType? targetId).isNone then .objectNotFound
  else if securityFlowsTo (ctx.threadLabelOf actorTid) (ctx.objectLabelOf targetId) then
    .flowDenied
  else if !ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf actorTid))
      (embedLegacyLabel (ctx.objectLabelOf targetId)) then .declassificationDenied
  else .auditLogCapacityExceeded

/-- A `.declassify` the admission refuses is the specification's refusal, with
the error `declassifyRefusal` reads. -/
theorem auditedArmSpec_declassify_refused (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (targetId : SeLe4n.ObjId) (actorTid : SeLe4n.ThreadId)
    (hT : cap.target = .object targetId)
    (hCur : st.scheduler.currentOnCore executingCore = some actorTid)
    (hA : declassifyAdmitted ctx st actorTid targetId = false) :
    auditedArmSpec ctx .declassify capAddr regs tid executingCore cap st =
      .error (declassifyRefusal ctx st actorTid targetId) := by
  unfold declassifyAdmitted at hA
  unfold declassifyRefusal
  cases hTy : st.getObjectType? targetId with
  | none =>
    simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
      declassifyObjectFromCore, hCur, hTy, Option.isNone_none, ↓reduceIte]
  | some ty =>
    simp only [hTy, Option.isSome_some, Bool.true_and] at hA
    by_cases hFlow : securityFlowsTo (ctx.threadLabelOf actorTid) (ctx.objectLabelOf targetId) = true
    · simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
        declassifyObjectFromCore, hCur, hTy, authorizeDeclassificationOnCore,
        declassificationDecision, liftLegacyContext, legacyLattice_canFlow_embed, hFlow,
        Option.isNone_some, Bool.false_eq_true, ↓reduceIte, declassificationActorOf]
    · simp only [Bool.not_eq_true] at hFlow
      by_cases hDecl : ctx.declassificationPolicy.canDeclassify
          (embedLegacyLabel (ctx.threadLabelOf actorTid))
          (embedLegacyLabel (ctx.objectLabelOf targetId)) = true
      · have hRoom : ¬ st.declassificationAudit.length < maxDeclassificationAuditEntries := by
          intro h; simp [hFlow, hDecl, h] at hA
        simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded,
          hT, declassifyObjectFromCore, hCur, hTy, authorizeDeclassificationOnCore,
          declassificationDecision, liftLegacyContext, legacyLattice_canFlow_embed, hFlow, hDecl,
          Option.isNone_some, Bool.false_eq_true, ↓reduceIte, recordDeclassificationChecked, hRoom,
          declassificationActorOf, Bool.not_true]
      · simp only [Bool.not_eq_true] at hDecl
        simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded,
          hT, declassifyObjectFromCore, hCur, hTy, authorizeDeclassificationOnCore,
          declassificationDecision, liftLegacyContext, legacyLattice_canFlow_embed, hFlow, hDecl,
          Option.isNone_some, Bool.false_eq_true, ↓reduceIte, declassificationActorOf,
          Bool.not_false]

/-- `.declassify`'s general form: the specification's arm, then its fused taint
step over the pre-state's bypass bit and trail position (`declassifyTaintStep_eq`),
every refusal carrying the state it was handed. -/
def declassifyGeneralR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match auditedArmSpec ctx .declassify capAddr regs tid executingCore cap st with
    | .error e => .error (e, st)
    | .ok ((), post) =>
        .ok ((), declassifyTaintStep (declassifyBypassB st (some cap)) (capObjectId cap)
          st.declassificationAuditEpoch st.declassificationAudit.length post)

/-- **`.declassify` behind its operand check**: the idle-object check and the
rights gate of the classic lookup, then the admitted form — the event written
over the ring's next slot in place — or its refusal, read before any write
(`declassifyRefusal`), or the general one (`declassifyOperandArmR_eq`). -/
@[inline] def declassifyOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
      else if !syscallTargetAccepted .declassify st cap then .error (.invalidCapability 0, st)
      else if cap.hasRight (syscallRequiredRight .declassify) then
        match cap.target, st.scheduler.currentOnCore executingCore with
        | .object targetId, some actorTid =>
          if declassifyAdmitted ctx st actorTid targetId then
            withTaintWordsAt st actorTid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
              .ok ((), declassifyPerform executingCore actorTid
                (embedLegacyLabel (ctx.threadLabelOf actorTid))
                (embedLegacyLabel (ctx.objectLabelOf targetId)) targetId
                (!declassifyTargetHoldsContent st targetId) st.declassificationAudit.epoch
                st.declassificationAudit.length a0 a1 a2 a3 a4 a5 a6 a7 ac as st)
          else .error (declassifyRefusal ctx st actorTid targetId, st)
        | _, _ => declassifyGeneralR ctx regs capAddr tid executingCore cap st
      else .error (syscallMissingRightError .declassify, st)

/-- `.declassify` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem declassifyOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .declassify)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    declassifyOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  have hOp := syscallOperandCap?_of_resolved st tid decoded.capAddr tcb rootCn ref hTcb hRoot hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hSid,
    syscallInvokeTyped, syscallResolveCap, hRef,
    declassifyTaintStep_eq st tid decoded hSid, hOp]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [declassifyOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hType : syscallTargetAccepted .declassify st cap = false
    · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    replace hType : syscallTargetAccepted .declassify st cap = true := by simpa using hType
    by_cases hRight : cap.hasRight (syscallRequiredRight .declassify) = true
    · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
      have hSpec := dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } cap
        (by rw [hSid]; rfl) hRegs hLen rfl
      rw [hSid] at hSpec
      rw [hSpec]
      split
      · next targetId actorTid hT hCur =>
        split
        · next hA =>
          rw [auditedArmSpec_declassify_admitted ctx decoded.capAddr regs tid executingCore cap st
            targetId actorTid hT hCur hA, withTaintWordsAt_eq, declassifyPerform_eq]
          simp only [declassifyBypassB, operandObjectId, capObjectId, hT]
        · next hA =>
          rw [auditedArmSpec_declassify_refused ctx decoded.capAddr regs tid executingCore cap st
            targetId actorTid hT hCur (by simpa using hA)]
      · unfold declassifyGeneralR
        rcases auditedArmSpec ctx .declassify decoded.capAddr regs tid executingCore cap st with
          _ | ⟨⟨⟩, post⟩ <;> rfl
    · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## Walking the ring's live window -/

/-- `auditEntryVisibleTo` at the embedded legacy context (`liftLegacyContext`),
read without building it (`auditEntryVisibleLegacy_eq`). -/
@[inline] def auditEntryVisibleLegacy (ctx : LabelingContext) (reader : SecurityDomain)
    (e : DeclassificationEvent) : Bool :=
  DomainFlowPolicy.legacyLattice.canFlow e.srcDomain reader &&
    DomainFlowPolicy.legacyLattice.canFlow e.dstDomain reader &&
    DomainFlowPolicy.legacyLattice.canFlow e.actor.domain reader &&
    DomainFlowPolicy.legacyLattice.canFlow (embedLegacyLabel (ctx.objectLabelOf e.targetObject))
      reader

theorem auditEntryVisibleLegacy_eq (ctx : LabelingContext) (reader : SecurityDomain) :
    auditEntryVisibleLegacy ctx reader = auditEntryVisibleTo (liftLegacyContext ctx) reader := rfl

@[simp] theorem liftLegacyContext_policy (ctx : LabelingContext) :
    (liftLegacyContext ctx).policy = .legacyLattice := rfl

@[simp] theorem liftLegacyContext_threadDomainOf (ctx : LabelingContext) (t : SeLe4n.ThreadId) :
    (liftLegacyContext ctx).threadDomainOf t = embedLegacyLabel (ctx.threadLabelOf t) := rfl

@[simp] theorem liftLegacyContext_objectDomainOf (ctx : LabelingContext) (o : SeLe4n.ObjId) :
    (liftLegacyContext ctx).objectDomainOf o = embedLegacyLabel (ctx.objectLabelOf o) := rfl

/-- The trail is the ring's window from position `0`. -/
theorem AuditRing.toList_eq_window (r : AuditRing) : r.toList = r.window 0 r.length := by
  simp [AuditRing.toList, AuditRing.window]

/-- Whether every entry of the `n` from position `i` is visible to `reader`,
walked in place (`auditWindowAllVisible_eq`). -/
def auditWindowAllVisible (ctx : LabelingContext) (reader : SecurityDomain) (r : AuditRing) :
    Nat → Nat → Bool
  | _, 0 => true
  | i, n + 1 => auditEntryVisibleLegacy ctx reader (r.entry i) &&
      auditWindowAllVisible ctx reader r (i + 1) n

theorem auditWindowAllVisible_eq (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) : ∀ (n i : Nat),
      auditWindowAllVisible ctx reader r i n = (r.window i n).all (auditEntryVisibleLegacy ctx reader)
  | 0, _ => rfl
  | n + 1, i => by
      rw [AuditRing.window_succ, List.all_cons, ← auditWindowAllVisible_eq ctx reader r n (i + 1)]
      rfl

/-- How many of the `n` entries from position `i` are visible to `reader`, added
to `acc`, walked in place (`auditWindowVisibleCount_eq`). -/
def auditWindowVisibleCount (ctx : LabelingContext) (reader : SecurityDomain) (r : AuditRing) :
    Nat → Nat → Nat → Nat
  | _, 0, acc => acc
  | i, n + 1, acc => auditWindowVisibleCount ctx reader r (i + 1) n
      (if auditEntryVisibleLegacy ctx reader (r.entry i) then acc + 1 else acc)

theorem auditWindowVisibleCount_eq (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) : ∀ (n i acc : Nat),
      auditWindowVisibleCount ctx reader r i n acc =
        acc + ((r.window i n).filter (auditEntryVisibleLegacy ctx reader)).length
  | 0, _, acc => by simp [auditWindowVisibleCount]
  | n + 1, i, acc => by
      rw [AuditRing.window_succ, List.filter_cons]
      unfold auditWindowVisibleCount
      rw [auditWindowVisibleCount_eq ctx reader r n (i + 1)]
      split <;> simp only [List.length_cons] <;> omega

/-- Where the `k`th entry visible to `reader` among the `n` from position `i`
stands, as a code: `0` when there is none, `j + 1` when it is the entry at
position `j` (`auditWindowFindVisible_eq`). -/
def auditWindowFindVisible (ctx : LabelingContext) (reader : SecurityDomain) (r : AuditRing) :
    Nat → Nat → Nat → Nat
  | _, 0, _ => 0
  | i, n + 1, k =>
    if auditEntryVisibleLegacy ctx reader (r.entry i) then
      (if k = 0 then i + 1 else auditWindowFindVisible ctx reader r (i + 1) n (k - 1))
    else auditWindowFindVisible ctx reader r (i + 1) n k

theorem auditWindowFindVisible_eq (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) : ∀ (n i k : Nat),
      ((r.window i n).filter (auditEntryVisibleLegacy ctx reader))[k]? =
        match auditWindowFindVisible ctx reader r i n k with
        | 0 => none
        | j + 1 => some (r.entry j)
  | 0, _, _ => by simp [auditWindowFindVisible]
  | n + 1, i, k => by
      rw [AuditRing.window_succ, List.filter_cons]
      unfold auditWindowFindVisible
      split
      · next hV =>
        cases k with
        | zero => simp
        | succ k =>
          simp only [List.getElem?_cons_succ, Nat.add_one_ne_zero, ↓reduceIte,
            Nat.add_sub_cancel]
          exact auditWindowFindVisible_eq ctx reader r n (i + 1) k
      · exact auditWindowFindVisible_eq ctx reader r n (i + 1) k

/-! ## `.auditDrain` -/

/-- Message register `i`'s word, read from the caller's file through the
hardware layout. -/
@[inline] def auditedArgWord (regs : SeLe4n.RegisterFile) (i : Nat) : UInt64 :=
  if h : i < SeLe4n.arm64DefaultLayout.msgRegs.size then
    readRegWord regs SeLe4n.arm64DefaultLayout.msgRegs[i]
  else 0

theorem auditedDecoded_msgReg (regs : SeLe4n.RegisterFile) (i : Nat) (hi : i < 4) :
    Architecture.SyscallArgDecode.requireMsgReg
        (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) i =
      .ok ⟨auditedArgWord regs i⟩ := by
  have hs : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := by decide
  simp only [Architecture.SyscallArgDecode.requireMsgReg_map_readReg,
    Architecture.SyscallArgDecode.msgRegOfFile, auditedArgWord, hs, hi, ↓reduceDIte, Except.map]

/-- `validatedAuditMonitorClearance` at a configured clearance, read without
building its `some`: whether the clearance dominates every legacy subject
label (`validatedAuditMonitorClearance_eq_some`). -/
@[inline] def auditClearanceDominates (m : SecurityDomain) : Bool :=
  DomainFlowPolicy.legacyLattice.canFlow ⟨0⟩ m && DomainFlowPolicy.legacyLattice.canFlow ⟨1⟩ m &&
    DomainFlowPolicy.legacyLattice.canFlow ⟨2⟩ m && DomainFlowPolicy.legacyLattice.canFlow ⟨3⟩ m

theorem validatedAuditMonitorClearance_eq_some (ctx : LabelingContext) (m : SecurityDomain)
    (hM : ctx.auditMonitorClearance = some m) (hD : auditClearanceDominates m = true) :
    validatedAuditMonitorClearance ctx = some m := by
  simp only [auditClearanceDominates, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hD
  simp only [validatedAuditMonitorClearance, hM, legacySubjectLabels, List.all_cons, List.all_nil,
    embedLegacyLabel, h0, h1, h2, h3, Bool.and_true, ↓reduceIte]

/-- Whether an audit call through `cap` is refused `.truncatedMessage`: the
target is the trail and the capability carries the call's right, the checks
its arm makes first, and the frame's message is shorter than the call's
arguments (`truncationMinimum`), read off the message-info word
(`routedLength`). -/
@[inline] def auditTruncated (sid : SyscallId) (regs : SeLe4n.RegisterFile) (cap : Capability) :
    Bool :=
  match cap.target with
  | .auditTrail _ =>
    cap.hasRight (syscallRequiredRight sid) &&
      decide (routedLength regs < Architecture.SyscallArgDecode.truncationMinimum sid)
  | _ => false

/-- A call `auditTruncated` does not refuse, on the trail with its right, is
long enough. -/
theorem auditTruncated_false_le {sid : SyscallId} {regs : SeLe4n.RegisterFile} {cap : Capability}
    {code : Nat} (hTr : auditTruncated sid regs cap = false) (hT : cap.target = .auditTrail code)
    (hRight : cap.hasRight (syscallRequiredRight sid) = true) :
    Architecture.SyscallArgDecode.truncationMinimum sid ≤ routedLength regs := by
  unfold auditTruncated at hTr
  rw [hT] at hTr
  simp only [hRight, Bool.true_and, decide_eq_false_iff_not, Nat.not_lt] at hTr
  exact hTr

/-- **A truncated audit call is the specification's refusal**: its target and
right checked, its decode refuses `.truncatedMessage` before any argument. -/
theorem auditedArmSpec_audit_truncated (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState)
    (hSid : sid = .auditRead ∨ sid = .auditDrain) (hTr : auditTruncated sid regs cap = true) :
    auditedArmSpec ctx sid capAddr regs tid executingCore cap st = .error .truncatedMessage := by
  unfold auditTruncated at hTr
  split at hTr
  · next code hT =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hTr
    obtain ⟨hRight, hLt⟩ := hTr
    rcases hSid with rfl | rfl <;>
      simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded,
        hT, extractAuditAuthority, auditedGate, hRight, ↓reduceIte,
        Architecture.SyscallArgDecode.decodeAuditReadArgs,
        Architecture.SyscallArgDecode.decodeAuditDrainArgs,
        Architecture.SyscallArgDecode.requireMessageLength, hLt, bind, Except.bind]
  · cases hTr

/-- Whether an `.auditDrain` through `cap` is admitted: the target is the trail,
the capability carries the drain's right, the configured clearance validates,
the core runs a subject the clearance dominates, and that subject sees every
entry of the trail (`auditDrainViewComplete`, walked in place). -/
@[inline] def auditDrainAdmitted (ctx : LabelingContext) (st : SystemState)
    (executingCore : Concurrency.CoreId) (cap : Capability) : Bool :=
  match cap.target, ctx.auditMonitorClearance, st.scheduler.currentOnCore executingCore with
  | .auditTrail _, some m, some reader =>
      cap.hasRight (syscallRequiredRight .auditDrain) && auditClearanceDominates m &&
        DomainFlowPolicy.legacyLattice.canFlow m (embedLegacyLabel (ctx.threadLabelOf reader)) &&
        auditWindowAllVisible ctx (embedLegacyLabel (ctx.threadLabelOf reader))
          st.declassificationAudit 0 st.declassificationAudit.length
  | _, _, _ => false

/-- **An admitted drain's writes**: the trail's first `min count length` entries
drained (`AuditRing.dropFront`) and the new length staged into the caller's
return registers as words (`writeReturnFrameToTcb_ofWord_eq_words`). -/
@[noinline] def auditDrainPerform (tid : SeLe4n.ThreadId) (count : Nat) (st : SystemState) :
    SystemState :=
  let len := st.declassificationAudit.length
  let removed := min count len
  let w := (len - removed).toUInt64
  ({ st with declassificationAudit := st.declassificationAudit.dropFront removed }).updateTcb tid
    (TCB.withReturnWords · w 0 0 0 0 0)

/-- An admitted drain is the specification's. -/
theorem auditedArmSpec_auditDrain_admitted (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState)
    (hTr : auditTruncated .auditDrain regs cap = false)
    (hA : auditDrainAdmitted ctx st executingCore cap = true) :
    auditedArmSpec ctx .auditDrain capAddr regs tid executingCore cap st =
      .ok ((), auditDrainPerform tid (auditedArgWord regs 0).toNat st) := by
  unfold auditDrainAdmitted at hA
  split at hA
  · next m reader hT hM hCur =>
    simp only [Bool.and_eq_true] at hA
    obtain ⟨⟨⟨hRight, hDom⟩, hMon⟩, hAll⟩ := hA
    have hL := Nat.not_lt.mpr (auditTruncated_false_le hTr hT hRight)
    have hV := validatedAuditMonitorClearance_eq_some ctx m hM hDom
    rw [auditWindowAllVisible_eq, ← AuditRing.toList_eq_window, List.all_eq_true] at hAll
    have hComplete : auditLogVisibleTo (liftLegacyContext ctx)
        (embedLegacyLabel (ctx.threadLabelOf reader)) st.declassificationAuditLog =
          st.declassificationAuditLog := by
      unfold auditLogVisibleTo
      rw [List.filter_eq_self]
      intro a ha
      rw [← auditEntryVisibleLegacy_eq]
      exact hAll a ha
    simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
      extractAuditAuthority, auditedGate, hRight, ↓reduceIte,
      Architecture.SyscallArgDecode.decodeAuditDrainArgs,
      Architecture.SyscallArgDecode.requireMessageLength, hL,
      auditedDecoded_msgReg regs 0 (by decide), bind, Except.bind, pure,
      Except.pure, hV, auditDrainVisiblePrefix, auditMonitorGate, auditReaderDomain, hCur,
      Option.map_some, auditMonitorAuthorized, auditDrainViewComplete, liftLegacyContext_policy,
      liftLegacyContext_threadDomainOf, hComplete, hMon, decide_true, Bool.and_true]
    rw [Architecture.writeReturnFrameToTcb_ofWord_eq_words]
    rfl
  · cases hA

/-- An audit call's general form: the specification's arm, whose taint step is
the identity (`auditTaintStep_eq`), every refusal carrying the state it was
handed. -/
def auditGeneralR (ctx : LabelingContext) (sid : SyscallId) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match auditedArmSpec ctx sid capAddr regs tid executingCore cap st with
    | .error e => .error (e, st)
    | .ok r => .ok r

/-- An audit call on a capability that does not target the audit trail is
refused `.invalidCapability` before anything else is read
(`extractAuditAuthority`, the target checked first). -/
theorem auditedArmSpec_audit_not_trail (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState)
    (hSid : sid = .auditRead ∨ sid = .auditDrain)
    (hT : ∀ code, cap.target ≠ .auditTrail code) :
    auditedArmSpec ctx sid capAddr regs tid executingCore cap st = .error (.invalidCapability 0) := by
  have hA : extractAuditAuthority cap = .error (.invalidCapability 0) := by
    unfold extractAuditAuthority
    cases h : cap.target <;> first | rfl | exact absurd h (hT _)
  rcases hSid with rfl | rfl <;>
    simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded,
      auditedGate, hA]

/-- **An audit call's general form, its target read first**: a capability that
does not target the audit trail is refused here, in the state it was handed,
so the specification's arm (whose decode and gate are records) runs only on an
audit capability (`auditTargetGeneralR_eq`). -/
@[inline] def auditTargetGeneralR (ctx : LabelingContext) (sid : SyscallId)
    (regs : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .auditTrail _ => auditGeneralR ctx sid regs capAddr tid executingCore cap st
    | _ => .error (.invalidCapability 0, st)

theorem auditTargetGeneralR_eq (ctx : LabelingContext) (sid : SyscallId)
    (regs : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState)
    (hSid : sid = .auditRead ∨ sid = .auditDrain) :
    auditTargetGeneralR ctx sid regs capAddr tid executingCore cap st =
      auditGeneralR ctx sid regs capAddr tid executingCore cap st := by
  unfold auditTargetGeneralR
  cases hT : cap.target with
  | auditTrail _ => rfl
  | _ =>
    simp only [auditGeneralR, auditedArmSpec_audit_not_trail ctx sid capAddr regs tid
      executingCore cap st hSid (by intro code; rw [hT]; exact fun h => by cases h)]

/-- **`.auditDrain` behind its operand check**: the idle-object check (the
target is checked before the right, as the gate checks it), then the admitted form — the drain and the staged
length written in place — or the general one (`auditDrainOperandArmR_eq`). -/
@[inline] def auditDrainOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
      else if auditTruncated .auditDrain regs cap then .error (.truncatedMessage, st)
      else if auditDrainAdmitted ctx st executingCore cap then
        .ok ((), auditDrainPerform tid (auditedArgWord regs 0).toNat st)
      else auditTargetGeneralR ctx .auditDrain regs capAddr tid executingCore cap st

/-- What an audit call's operand check leaves to its arm: the specification's
arm and taint step, through the typed gate, is the arm alone on a capability
that resolves (`auditTaintStep_eq`): the arm checks the type and the right in
the gate's order. -/
theorem auditOperand_spec (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st =
      match SystemState.lookupSlotCap st ref with
      | none => .error (.invalidCapability 0, st)
      | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else auditGeneralR ctx decoded.syscallId regs decoded.capAddr tid executingCore cap st := by
  have hR : routedAudited decoded.syscallId = true := by
    rcases hSid with h | h <;> rw [h] <;> rfl
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    syscallInvokeTyped, syscallResolveCap, hRef, auditTaintStep_eq st tid decoded hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only []
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · simp only [hIdle, Bool.false_eq_true, ↓reduceIte, auditGeneralR]
      rw [dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore _ cap hR
        hRegs hLen rfl]
      -- The gate's type and right restate the arm's own target-first checks.
      by_cases hT : ∃ code, cap.target = .auditTrail code
      · obtain ⟨code, hTc⟩ := hT
        have hAcc : syscallTargetAccepted decoded.syscallId st cap = true := by
          rcases hSid with h | h <;> simp [syscallTargetAccepted, syscallObjectKind?, h, hTc]
        by_cases hRt : cap.hasRight (syscallRequiredRight decoded.syscallId) = true
        · simp only [hAcc, hRt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases auditedArmSpec ctx decoded.syscallId decoded.capAddr regs tid executingCore cap
            st with _ | ⟨⟨⟩, post⟩ <;> rfl
        · have hNo := dispatchWithCapChecked_audit_insufficient_right_denied ctx
            (auditedDecoded decoded.syscallId decoded.capAddr regs) tid executingCore
            (auditedGate tid decoded.capAddr decoded.syscallId) cap st hSid hTc
            (by simpa [auditedGate] using hRt)
          simp only [auditedArmSpec] at hNo
          simp only [hAcc, hRt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, auditedArmSpec, hNo]
          rcases hSid with h | h <;> simp [h, syscallMissingRightError]
      · have hNA : syscallTargetAccepted decoded.syscallId st cap = false := by
          rcases hSid with h | h <;> cases hTc : cap.target <;>
            simp_all [syscallTargetAccepted, syscallObjectKind?]
        rw [auditedArmSpec_audit_not_trail ctx decoded.syscallId decoded.capAddr regs tid
          executingCore cap st hSid (fun code h => hT ⟨code, h⟩)]
        simp [hNA]

/-- `.auditDrain` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem auditDrainOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditDrain)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    auditDrainOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  rw [auditOperand_spec ctx decoded regs tid executingCore (.inr hSid) hRegs hLen st tcb rootCn ref hRef,
    hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only [auditDrainOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hTr : auditTruncated .auditDrain regs cap = true
    · simp only [hIdle, hTr, Bool.false_eq_true, ↓reduceIte, auditGeneralR,
        auditedArmSpec_audit_truncated ctx .auditDrain decoded.capAddr regs tid executingCore cap
          st (.inr rfl) hTr]
    · simp only [hIdle, hTr, Bool.false_eq_true, ↓reduceIte]
      split
      · next hA =>
        simp only [auditGeneralR, auditedArmSpec_auditDrain_admitted ctx decoded.capAddr regs tid
          executingCore cap st (Bool.eq_false_iff.mpr hTr) hA]
      · exact auditTargetGeneralR_eq ctx _ regs _ tid executingCore cap st (.inr rfl)

/-! ## `.auditRead` -/

/-- A number below `2 ^ 64` as its word: the word reads back the number. -/
theorem toNat_toUInt64_of_lt (v : Nat) (h : v < 18446744073709551616) :
    v.toUInt64.toNat = v := by
  simp only [Nat.toUInt64_eq]
  exact Nat.mod_eq_of_lt h

/-- `auditFieldChunkCount?` by repeated division (`auditChunkCountN_eq_div`). -/
@[inline] def auditChunkCountDiv (v : Nat) : Nat :=
  if v < auditFieldChunkModulus then 1
  else if v / auditFieldChunkModulus < auditFieldChunkModulus then 2
  else if v / auditFieldChunkModulus / auditFieldChunkModulus < auditFieldChunkModulus then 3
  else if v / auditFieldChunkModulus / auditFieldChunkModulus / auditFieldChunkModulus <
      auditFieldChunkModulus then 4
  else 0

/-- `auditFieldChunkCount?` as a code: `0` for `none`, else the count.  A
number below `2 ^ 64` (every value a field holds) is compared as its word, so
a number past `2 ^ 63`, which the runtime holds as a big number, is never
divided (`auditChunkCountN_eq_div`). -/
@[inline] def auditChunkCountN (v : Nat) : Nat :=
  if v < 18446744073709551616 then (if v.toUInt64 < 4294967296 then 1 else 2)
  else auditChunkCountDiv v

theorem auditChunkCountN_eq_div (v : Nat) : auditChunkCountN v = auditChunkCountDiv v := by
  unfold auditChunkCountN auditChunkCountDiv
  split
  · next h =>
    have hu := toNat_toUInt64_of_lt v h
    have hlt : (v.toUInt64 < 4294967296) ↔ v < 4294967296 := by
      rw [UInt64.lt_iff_toNat_lt, hu]; rfl
    show _ = if v < 4294967296 then 1 else if v / 4294967296 < 4294967296 then 2 else _
    by_cases h1 : v < 4294967296
    · simp only [hlt.mpr h1, ↓reduceIte, h1]
    · have h2 : v / 4294967296 < 4294967296 := by omega
      have h1' : ¬ (v.toUInt64 < 4294967296) := fun h' => h1 (hlt.mp h')
      simp only [h1', ↓reduceIte, h1, h2]
  · rfl

theorem auditFieldChunkCount?_eq_code (v : Nat) :
    auditFieldChunkCount? v =
      if auditChunkCountN v = 0 then none else some (auditChunkCountN v) := by
  rw [auditChunkCountN_eq_div]
  unfold auditFieldChunkCount? auditChunkCountDiv
  simp only [maxAuditFieldChunks, auditChunkCountUpTo]
  by_cases h1 : v < auditFieldChunkModulus
  · simp [h1]
  by_cases h2 : v / auditFieldChunkModulus < auditFieldChunkModulus
  · simp [h1, h2]
  by_cases h3 : v / auditFieldChunkModulus / auditFieldChunkModulus < auditFieldChunkModulus
  · simp [h1, h2, h3]
  by_cases h4 : v / auditFieldChunkModulus / auditFieldChunkModulus / auditFieldChunkModulus <
      auditFieldChunkModulus
  · simp [h1, h2, h3, h4]
  · simp [h1, h2, h3, h4]

/-- A field's chunk count, read off the `index`th visible entry, as a code:
`0` when the entry or the count is missing, `n + 1` for count `n`. -/
@[inline] def auditFieldCountCode (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) (index : Nat) (f : AuditReadField) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length index with
  | 0 => 0
  | j + 1 =>
    let n := auditChunkCountN (auditExportedFieldValue true index (r.entry j) f)
    if n = 0 then 0 else n + 1

/-- Chunk `i` of `v` in base `K` by repeated division: the four chunks a field
exports never form the power `K ^ i`, a number past a word for `i ≥ 2`
(`divChunk_eq`). -/
@[inline] def divChunk (K v i : Nat) : Nat :=
  match i with
  | 0 => v % K
  | 1 => v / K % K
  | 2 => v / K / K % K
  | 3 => v / K / K / K % K
  | _ => v / K ^ i % K

theorem divChunk_eq (K v i : Nat) : divChunk K v i = v / K ^ i % K := by
  unfold divChunk
  split
  · rw [Nat.pow_zero, Nat.div_one]
  · rw [Nat.pow_one]
  · rw [Nat.div_div_eq_div_mul, ← Nat.pow_two]
  · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_two, Nat.mul_comm,
      ← Nat.pow_succ]
  · rfl

/-- `auditFieldChunk` without forming a power: a number below `2 ^ 64` read as
its word's halves, so a number past `2 ^ 63` is never divided, and any other by
repeated division (`auditFieldChunkCode_eq`). -/
@[inline] def auditFieldChunkCode (v i : Nat) : Nat :=
  if v < 18446744073709551616 then
    if i = 0 then (v.toUInt64 &&& 0xffffffff).toNat
    else if i = 1 then (v.toUInt64 >>> 32).toNat
    else if i < 4 then 0
    else divChunk auditFieldChunkModulus v i
  else divChunk auditFieldChunkModulus v i
theorem auditFieldChunkCode_eq (v i : Nat) : auditFieldChunkCode v i = auditFieldChunk v i := by
  rw [show auditFieldChunk v i = divChunk auditFieldChunkModulus v i from
    (divChunk_eq _ v i).symm]
  unfold auditFieldChunkCode
  split
  · next h =>
    have hu := toNat_toUInt64_of_lt v h
    split
    · next h0 =>
      subst h0
      rw [UInt64.toNat_and, hu]
      show v &&& (2 ^ 32 - 1) = v % 2 ^ 32
      exact Nat.and_two_pow_sub_one_eq_mod v 32
    split
    · next h1 =>
      subst h1
      rw [UInt64.toNat_shiftRight, hu]
      show v >>> (32 % 64) = v / 4294967296 % 4294967296
      rw [Nat.shiftRight_eq_div_pow]
      have : v / 2 ^ 32 < 2 ^ 32 := by omega
      exact (Nat.mod_eq_of_lt this).symm
    split
    · next h4 =>
      have h0 : v / 4294967296 / 4294967296 = 0 := by omega
      have : i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl
      · show 0 = v / 4294967296 / 4294967296 % 4294967296
        rw [h0]
      · show 0 = v / 4294967296 / 4294967296 / 4294967296 % 4294967296
        rw [h0]
    · rfl
  · rfl

/-- A field's chunk, read off the `index`th visible entry, as a code: `0` when
the entry is missing or the chunk is out of range, `w + 1` for word `w`. -/
@[inline] def auditFieldWordCode (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) (index chunk : Nat) (f : AuditReadField) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length index with
  | 0 => 0
  | j + 1 =>
    let v := auditExportedFieldValue true index (r.entry j) f
    let n := auditChunkCountN v
    if n ≠ 0 ∧ chunk < n then auditFieldChunkCode v chunk + 1 else 0

/-- `ByteArray.toList`'s loop is the array's list after the bytes it has
consed. -/
theorem auditBytes_toList_loop (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop]
    have : ¬ i < bs.size := by omega
    simp only [this, ↓reduceIte]
    have hd : bs.data.toList.drop i = [] := by
      simp only [List.drop_eq_nil_iff, Array.length_toList]; exact Nat.le_of_not_lt this
    rw [hd, List.append_nil]
  | succ k ih =>
    intro i r hk
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    simp only [hi, ↓reduceIte]
    rw [ih (i+1) _ (by omega)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1
    have hl : i < bs.data.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hl]
    simp [ByteArray.get!, hi]

theorem auditBytes_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [auditBytes_toList_loop bs _ 0 [] rfl]; simp

/-- Byte `i` of a string's UTF-8 encoding, `0` past its end, read in place. -/
@[inline] def auditBasisByteAt (s : String) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then (s.getUTF8Byte ⟨i⟩ h).toNat else 0

theorem auditBasisBytes_getD (e : DeclassificationEvent) (i : Nat) :
    ((auditBasisBytes e).getD i 0).toNat = auditBasisByteAt e.authorizationBasis.render i := by
  unfold auditBasisBytes
  generalize e.authorizationBasis.render = s
  rw [String.toUTF8_eq_toByteArray, auditBytes_toList]
  unfold auditBasisByteAt
  split
  · next h =>
    have h' : i < s.toByteArray.data.toList.length := by rw [Array.length_toList]; exact h
    simp [String.getUTF8Byte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h',
      ByteArray.getElem_eq_getElem_data]
  · next h =>
    have h' : s.toByteArray.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']

theorem auditBasisBytes_length (e : DeclassificationEvent) :
    (auditBasisBytes e).length = e.authorizationBasis.render.utf8ByteSize := by
  unfold auditBasisBytes
  rw [String.toUTF8_eq_toByteArray, auditBytes_toList]
  simp only [Array.length_toList, String.utf8ByteSize, ByteArray.size]

/-- `auditBasisChunkValue` of an entry's designation, read in place. -/
@[inline] def auditBasisChunkCode (s : String) (i : Nat) : Nat :=
  auditBasisByteAt s (4 * i) + 256 * auditBasisByteAt s (4 * i + 1)
    + 65536 * auditBasisByteAt s (4 * i + 2) + 16777216 * auditBasisByteAt s (4 * i + 3)

theorem auditBasisChunkCode_eq (e : DeclassificationEvent) (i : Nat) :
    auditBasisChunkCode e.authorizationBasis.render i =
      auditBasisChunkValue (auditBasisBytes e) i := by
  unfold auditBasisChunkCode auditBasisChunkValue
  simp only [auditBasisBytes_getD]

/-- An entry's designation byte count, as a code. -/
@[inline] def auditBasisCountCode (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) (index : Nat) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length index with
  | 0 => 0
  | j + 1 =>
    let n := (r.entry j).authorizationBasis.render.utf8ByteSize
    if n ≤ maxAuditDesignationBytes then n + 1 else 0

/-- An entry's designation chunk, as a code. -/
@[inline] def auditBasisWordCode (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) (index chunk : Nat) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length index with
  | 0 => 0
  | j + 1 =>
    let s := (r.entry j).authorizationBasis.render
    let n := s.utf8ByteSize
    if n ≤ maxAuditDesignationBytes then
      (if chunk < auditBasisChunkCount n then auditBasisChunkCode s chunk + 1 else 0)
    else 0

/-- A refusal-ledger slot's code: `0` for a slot out of range or empty, else
`f` of its refusal, read off the slot's words: `f` is applied to a refusal
literal on each side of the receiver flag, so inlined it reads the slot's fields
and no record is built, nor carried to a join of the two sides. -/
@[inline] def refusalSlotCode (rl : RefusalLedger) (slot : Nat)
    (f : DeclassificationRefusal → Nat) : Nat :=
  if h : slot < refusalRingSize then
    let s := rl.slots.get ⟨slot, h⟩
    if s.occupied then
      if s.receiverNamed then f (s.toRefusalWith (some s.receiver)) else f (s.toRefusalWith none)
    else 0
  else 0

/-- A refusal-ledger slot's code for a reader of its scalar fields alone (every
field but the receiver): `f` of the slot's refusal with no receiver, a literal
`f` inlined reads straight off the slot's words, so the read builds no record
(`refusalScalarSlotCode_some`). -/
@[inline] def refusalScalarSlotCode (rl : RefusalLedger) (slot : Nat)
    (f : DeclassificationRefusal → Nat) : Nat :=
  if h : slot < refusalRingSize then
    let s := rl.slots.get ⟨slot, h⟩
    if s.occupied then f (s.toRefusalWith none) else 0
  else 0

/-- A word's chunk count: a word never needs more than two chunks. -/
@[inline] def wordChunkCount (w : UInt64) : Nat := if w < 4294967296 then 1 else 2

theorem auditChunkCountN_toNat (w : UInt64) : auditChunkCountN w.toNat = wordChunkCount w := by
  unfold auditChunkCountN wordChunkCount
  rw [if_pos w.toNat_lt]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]

/-- A word's chunk `i`, read off its halves. -/
@[inline] def wordChunk (w : UInt64) (i : Nat) : Nat :=
  if i = 0 then (w &&& 0xffffffff).toNat
  else if i = 1 then (w >>> 32).toNat
  else if i < 4 then 0
  else divChunk auditFieldChunkModulus w.toNat i

theorem auditFieldChunkCode_toNat (w : UInt64) (i : Nat) :
    auditFieldChunkCode w.toNat i = wordChunk w i := by
  unfold auditFieldChunkCode wordChunk
  rw [if_pos w.toNat_lt]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]

/-- A refusal field's chunk count: the requested target read off its word, so an
address past `2 ^ 63` builds no number (`refusalFieldCount_eq`). -/
@[inline] def refusalFieldCount (r : DeclassificationRefusal) (f : RefusalReadField) : Nat :=
  match f with
  | .requestedTarget => wordChunkCount r.requestedTarget.word
  | _ => auditChunkCountN (refusalExportedFieldValue r f)

theorem refusalFieldCount_eq (r : DeclassificationRefusal) (f : RefusalReadField) :
    refusalFieldCount r f = auditChunkCountN (refusalExportedFieldValue r f) := by
  cases f
  · rfl
  · rfl
  · exact (auditChunkCountN_toNat _).symm

/-- A refusal field's chunk, the requested target read off its word
(`refusalFieldChunk_eq`). -/
@[inline] def refusalFieldChunk (r : DeclassificationRefusal) (f : RefusalReadField)
    (chunk : Nat) : Nat :=
  match f with
  | .requestedTarget => wordChunk r.requestedTarget.word chunk
  | _ => auditFieldChunkCode (refusalExportedFieldValue r f) chunk

theorem refusalFieldChunk_eq (r : DeclassificationRefusal) (f : RefusalReadField) (chunk : Nat) :
    refusalFieldChunk r f chunk = auditFieldChunkCode (refusalExportedFieldValue r f) chunk := by
  cases f
  · rfl
  · rfl
  · exact (auditFieldChunkCode_toNat _ _).symm

/-- A refusal's field chunk count, as a code. -/
@[inline] def refusalFieldCountCode (r : DeclassificationRefusal) (f : RefusalReadField) : Nat :=
  let n := refusalFieldCount r f
  if n = 0 then 0 else n + 1

/-- A refusal's field chunk, as a code. -/
@[inline] def refusalFieldWordCode (r : DeclassificationRefusal) (f : RefusalReadField)
    (chunk : Nat) : Nat :=
  let n := refusalFieldCount r f
  if n ≠ 0 ∧ chunk < n then refusalFieldChunk r f chunk + 1 else 0

/-- A refusal's receiver chunk count, as a code (`1` for no receiver: count 0). -/
@[inline] def refusalReceiverCountCode (r : DeclassificationRefusal) : Nat :=
  match r.refusedReceiver with
  | none => 1
  | some receiver =>
    let n := auditChunkCountN receiver.val
    if n = 0 then 0 else n + 1

/-- A refusal's receiver chunk, as a code. -/
@[inline] def refusalReceiverWordCode (r : DeclassificationRefusal) (chunk : Nat) : Nat :=
  match r.refusedReceiver with
  | none => 0
  | some receiver =>
    let n := auditChunkCountN receiver.val
    if n ≠ 0 ∧ chunk < n then auditFieldChunkCode receiver.val chunk + 1 else 0

/-- **Whether a later event names an earlier one**, read off the later event's
snapshot words (`declassificationEventNames_eq_code`). -/
@[inline] def auditEventNamesCode (later earlier : DeclassificationEvent) : Bool :=
  later.predecessorWords.containsCode earlier.timestamp

theorem declassificationEventNames_eq_code (later earlier : DeclassificationEvent) :
    declassificationEventNames later earlier = auditEventNamesCode later earlier :=
  TaintWords.decode_contains_eq _ _

/-- A causality verdict over two visible entries, as a code. -/
@[inline] def auditChainCode (ctx : LabelingContext) (reader : SecurityDomain) (r : AuditRing)
    (later earlier : Nat) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length later,
      auditWindowFindVisible ctx reader r 0 r.length earlier with
  | j + 1, i + 1 => (if auditEventNamesCode (r.entry j) (r.entry i) then 1 else 0) + 1
  | _, _ => 0

/-- **A monitor's audit read, walked in place**, as a code: `w + 1` for the word
`w` the specification returns (`auditReadFastCode_spec`), `0` for a read the
specification refuses.  Every opcode is read off the trail's live window and the
refusal ledger's slots, so no view, designation, number or tag list is built. -/
def auditReadFastCode (ctx : LabelingContext) (reader : SecurityDomain) (st : SystemState)
    (opcode index chunk : Nat) : Nat :=
  let r := st.declassificationAudit
  let rl := st.declassificationRefusals
  match opcode with
  | 0 => auditStatusWord (auditWindowVisibleCount ctx reader r 0 r.length 0) r.epoch + 1
  | 1 => auditFieldCountCode ctx reader r index .srcDomain
  | 2 => auditFieldCountCode ctx reader r index .dstDomain
  | 3 => auditFieldCountCode ctx reader r index .targetObject
  | 4 => auditFieldCountCode ctx reader r index .timestamp
  | 5 => auditFieldWordCode ctx reader r index chunk .srcDomain
  | 6 => auditFieldWordCode ctx reader r index chunk .dstDomain
  | 7 => auditFieldWordCode ctx reader r index chunk .targetObject
  | 8 => auditFieldWordCode ctx reader r index chunk .timestamp
  | 9 =>
    match auditWindowFindVisible ctx reader r 0 r.length index with
    | 0 => 0
    | j + 1 => auditCoreAndTrustWord (r.entry j) + 1
  | 10 => auditBasisCountCode ctx reader r index
  | 11 => auditBasisWordCode ctx reader r index chunk
  | 12 => refusalStatusWord rl.nextSlot.val rl.version + 1
  | 13 => refusalCountersWord rl.attemptCount.val rl.droppedCount.val + 1
  | 14 => refusalScalarSlotCode rl index fun x => refusalTagsWord x + 1
  | 15 => refusalScalarSlotCode rl index fun x => refusalFieldCountCode x .subject
  | 16 => refusalScalarSlotCode rl index fun x => refusalFieldCountCode x .subjectDomain
  | 17 => refusalScalarSlotCode rl index fun x => refusalFieldCountCode x .requestedTarget
  | 18 => refusalScalarSlotCode rl index fun x => refusalFieldWordCode x .subject chunk
  | 19 => refusalScalarSlotCode rl index fun x => refusalFieldWordCode x .subjectDomain chunk
  | 20 => refusalScalarSlotCode rl index fun x => refusalFieldWordCode x .requestedTarget chunk
  | 21 => auditFieldCountCode ctx reader r index .actorSubject
  | 22 => auditFieldCountCode ctx reader r index .actorDomain
  | 23 => auditFieldWordCode ctx reader r index chunk .actorSubject
  | 24 => auditFieldWordCode ctx reader r index chunk .actorDomain
  | 25 => refusalSlotCode rl index refusalReceiverCountCode
  | 26 => refusalSlotCode rl index fun x => refusalReceiverWordCode x chunk
  | 27 => if index = 0 then 0 else auditChainCode ctx reader r index (index - 1)
  | 28 => if chunk < index then auditChainCode ctx reader r index chunk else 0
  | 29 =>
    if chunk < r.epoch then
      match auditWindowFindVisible ctx reader r 0 r.length index with
      | 0 => 0
      | j + 1 => (if (r.entry j).predecessorWords.containsCode chunk then 1 else 0) + 1
    else 0
  | _ => 0

/-- The visible view's entries, found in place. -/
theorem auditLogVisibleTo_getElem? (ctx : LabelingContext) (reader : SecurityDomain)
    (st : SystemState) (k : Nat) :
    (auditLogVisibleTo (liftLegacyContext ctx) reader st.declassificationAuditLog)[k]? =
      match auditWindowFindVisible ctx reader st.declassificationAudit 0
          st.declassificationAudit.length k with
      | 0 => none
      | j + 1 => some (st.declassificationAudit.entry j) := by
  unfold auditLogVisibleTo
  rw [← auditEntryVisibleLegacy_eq, show st.declassificationAuditLog =
    st.declassificationAudit.toList from rfl, AuditRing.toList_eq_window, auditWindowFindVisible_eq]

/-- The visible view's length, counted in place. -/
theorem auditLogVisibleTo_length (ctx : LabelingContext) (reader : SecurityDomain)
    (st : SystemState) :
    (auditLogVisibleTo (liftLegacyContext ctx) reader st.declassificationAuditLog).length =
      auditWindowVisibleCount ctx reader st.declassificationAudit 0
        st.declassificationAudit.length 0 := by
  unfold auditLogVisibleTo
  rw [← auditEntryVisibleLegacy_eq, show st.declassificationAuditLog =
    st.declassificationAudit.toList from rfl, AuditRing.toList_eq_window,
    auditWindowVisibleCount_eq, Nat.zero_add]

/-- A field-count code is the specification's chunk count, for a monitor. -/
theorem auditFieldCountCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (index w : Nat) (f : AuditReadField)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : auditFieldCountCode ctx reader st.declassificationAudit index f = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.fieldChunkCount index f) =
      .ok w := by
  unfold auditFieldCountCode at h
  simp only [auditReadWord, auditLogVisibleTo_getElem?, hIs, auditFieldChunkCount?_eq_code]
  split at h
  · cases h
  · next j hF =>
    by_cases hn : auditChunkCountN (auditExportedFieldValue true index
      (st.declassificationAudit.entry j) f) = 0
    · simp only [hn, ↓reduceIte] at h; cases h
    · simp only [hn, ↓reduceIte, Nat.add_right_cancel_iff] at h ⊢
      rw [h]

/-- A field-chunk code is the specification's chunk, for a monitor. -/
theorem auditFieldWordCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (index chunk w : Nat) (f : AuditReadField)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : auditFieldWordCode ctx reader st.declassificationAudit index chunk f = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.field index f chunk) =
      .ok w := by
  unfold auditFieldWordCode at h
  simp only [auditReadWord, auditLogVisibleTo_getElem?, hIs, auditFieldChunkCount?_eq_code]
  split at h
  · cases h
  · next j hF =>
    by_cases hc : auditChunkCountN (auditExportedFieldValue true index
        (st.declassificationAudit.entry j) f) ≠ 0 ∧
      chunk < auditChunkCountN (auditExportedFieldValue true index
        (st.declassificationAudit.entry j) f)
    · obtain ⟨hn, hlt⟩ := hc
      simp only [ne_eq, hn, not_false_eq_true, hlt, and_self, ↓reduceIte,
        Nat.add_right_cancel_iff, auditFieldChunkCode_eq] at h ⊢
      rw [h]
    · simp only [hc, ↓reduceIte] at h; cases h

/-- A designation byte-count code is the specification's count. -/
theorem auditBasisCountCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (index w : Nat)
    (h : auditBasisCountCode ctx reader st.declassificationAudit index = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.basisByteCount index) =
      .ok w := by
  unfold auditBasisCountCode at h
  simp only [auditReadWord, auditLogVisibleTo_getElem?]
  split at h
  · cases h
  · next j hF =>
    simp only [auditBasisBytes_length]
    by_cases hn : (st.declassificationAudit.entry j).authorizationBasis.render.utf8ByteSize ≤
        maxAuditDesignationBytes
    · simp only [hn, ↓reduceIte, Nat.add_right_cancel_iff] at h ⊢
      rw [h]
    · simp only [hn, ↓reduceIte] at h; cases h

/-- A designation chunk code is the specification's chunk. -/
theorem auditBasisWordCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (index chunk w : Nat)
    (h : auditBasisWordCode ctx reader st.declassificationAudit index chunk = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.basisChunk index chunk) =
      .ok w := by
  unfold auditBasisWordCode at h
  simp only [auditReadWord, auditLogVisibleTo_getElem?]
  split at h
  · cases h
  · next j hF =>
    simp only [auditBasisBytes_length]
    by_cases hn : (st.declassificationAudit.entry j).authorizationBasis.render.utf8ByteSize ≤
        maxAuditDesignationBytes
    · by_cases hc : chunk < auditBasisChunkCount
          (st.declassificationAudit.entry j).authorizationBasis.render.utf8ByteSize
      · simp only [hn, hc, ↓reduceIte, Nat.add_right_cancel_iff] at h ⊢
        rw [← auditBasisChunkCode_eq, h]
      · simp only [hn, hc, ↓reduceIte] at h; cases h
    · simp only [hn, ↓reduceIte] at h; cases h

/-- A refusal slot's code is nonzero only on a present slot. -/
theorem refusalSlotCode_some {rl : RefusalLedger} {slot w : Nat}
    {f : DeclassificationRefusal → Nat} (h : refusalSlotCode rl slot f = w + 1) :
    ∃ (hs : slot < refusalRingSize) (r : DeclassificationRefusal),
      rl.recent.get ⟨slot, hs⟩ = some r ∧ f r = w + 1 := by
  unfold refusalSlotCode at h
  split at h
  · next hs =>
    dsimp only at h
    split at h
    · next hOcc =>
      split at h
      · next hN =>
        exact ⟨hs, _, by simp only [RefusalLedger.recent_get, RefusalSlot.view, hOcc,
          RefusalSlot.toRefusal, RefusalSlot.receiver?, hN, ↓reduceIte], h⟩
      · next hN =>
        exact ⟨hs, _, by simp only [RefusalLedger.recent_get, RefusalSlot.view, hOcc,
          RefusalSlot.toRefusal, RefusalSlot.receiver?, hN, ↓reduceIte, Bool.false_eq_true], h⟩
    · cases h
  · cases h

/-- A scalar slot's code is nonzero only on a present slot, for a reader `f` the
receiver does not move. -/
theorem refusalScalarSlotCode_some {rl : RefusalLedger} {slot w : Nat}
    {f : DeclassificationRefusal → Nat}
    (hScalar : ∀ r : DeclassificationRefusal, f { r with refusedReceiver := none } = f r)
    (h : refusalScalarSlotCode rl slot f = w + 1) :
    ∃ (hs : slot < refusalRingSize) (r : DeclassificationRefusal),
      rl.recent.get ⟨slot, hs⟩ = some r ∧ f r = w + 1 := by
  unfold refusalScalarSlotCode at h
  split at h
  · next hs =>
    dsimp only at h
    split at h
    · next hOcc =>
      refine ⟨hs, (rl.slots.get ⟨slot, hs⟩).toRefusal, ?_, ?_⟩
      · simp only [RefusalLedger.recent_get, RefusalSlot.view, hOcc, ↓reduceIte]
      · exact (hScalar _).symm.trans h
    · cases h
  · cases h

/-- A refusal-ledger opcode's code is the specification's word, for a monitor. -/
theorem refusalFieldCountCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (slot w : Nat) (f : RefusalReadField)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : refusalScalarSlotCode st.declassificationRefusals slot
      (fun x => refusalFieldCountCode x f) = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.refusalSlotFieldChunkCount slot f) =
      .ok w := by
  obtain ⟨hs, r, hr, hf⟩ := refusalScalarSlotCode_some (fun _ => rfl) h
  simp only [auditReadWord, hIs, ↓reduceIte, hs, dite_true, RefusalLedger.slotView_eq, hr, auditFieldChunkCount?_eq_code]
  unfold refusalFieldCountCode at hf
  rw [refusalFieldCount_eq] at hf
  by_cases hn : auditChunkCountN (refusalExportedFieldValue r f) = 0
  · simp only [hn, ↓reduceIte] at hf; cases hf
  · simp only [hn, ↓reduceIte, Nat.add_right_cancel_iff] at hf ⊢
    rw [hf]

theorem refusalFieldWordCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (slot chunk w : Nat) (f : RefusalReadField)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : refusalScalarSlotCode st.declassificationRefusals slot
      (fun x => refusalFieldWordCode x f chunk) = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.refusalSlotField slot f chunk) =
      .ok w := by
  obtain ⟨hs, r, hr, hf⟩ := refusalScalarSlotCode_some (fun _ => rfl) h
  simp only [auditReadWord, hIs, ↓reduceIte, hs, dite_true, RefusalLedger.slotView_eq, hr, auditFieldChunkCount?_eq_code]
  unfold refusalFieldWordCode at hf
  rw [refusalFieldCount_eq, refusalFieldChunk_eq] at hf
  by_cases hc : auditChunkCountN (refusalExportedFieldValue r f) ≠ 0 ∧
      chunk < auditChunkCountN (refusalExportedFieldValue r f)
  · obtain ⟨hn, hlt⟩ := hc
    simp only [ne_eq, hn, not_false_eq_true, hlt, and_self, ↓reduceIte,
      Nat.add_right_cancel_iff, auditFieldChunkCode_eq] at hf ⊢
    rw [hf]
  · simp only [hc, ↓reduceIte] at hf; cases hf

theorem refusalReceiverCountCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (slot w : Nat)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : refusalSlotCode st.declassificationRefusals slot refusalReceiverCountCode = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.refusalReceiverChunkCount slot) =
      .ok w := by
  obtain ⟨hs, r, hr, hf⟩ := refusalSlotCode_some h
  simp only [auditReadWord, hIs, ↓reduceIte, hs, dite_true, RefusalLedger.slotView_eq, hr, auditFieldChunkCount?_eq_code]
  unfold refusalReceiverCountCode at hf
  split at hf
  · next hN =>
    simp only [hN] at hf ⊢
    obtain rfl : w = 0 := by omega
    rfl
  · next rc hN =>
    simp only [hN]
    by_cases hn : auditChunkCountN rc.val = 0
    · simp only [hn, ↓reduceIte] at hf; cases hf
    · simp only [hn, ↓reduceIte, Nat.add_right_cancel_iff] at hf ⊢
      rw [hf]

theorem refusalReceiverWordCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (slot chunk w : Nat)
    (hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true)
    (h : refusalSlotCode st.declassificationRefusals slot
      (fun x => refusalReceiverWordCode x chunk) = w + 1) :
    auditReadWord (liftLegacyContext ctx) (some m) reader st (.refusalReceiverChunk slot chunk) =
      .ok w := by
  obtain ⟨hs, r, hr, hf⟩ := refusalSlotCode_some h
  simp only [auditReadWord, hIs, ↓reduceIte, hs, dite_true, RefusalLedger.slotView_eq, hr, auditFieldChunkCount?_eq_code]
  unfold refusalReceiverWordCode at hf
  split at hf
  · cases hf
  · next rc hN =>
    simp only [hN]
    by_cases hc : auditChunkCountN rc.val ≠ 0 ∧ chunk < auditChunkCountN rc.val
    · obtain ⟨hn, hlt⟩ := hc
      simp only [ne_eq, hn, not_false_eq_true, hlt, and_self, ↓reduceIte,
        Nat.add_right_cancel_iff, auditFieldChunkCode_eq] at hf ⊢
      rw [hf]
    · simp only [hc, ↓reduceIte] at hf; cases hf

/-- A causality code is the specification's verdict over two visible entries. -/
theorem auditChainCode_some {ctx : LabelingContext} {reader : SecurityDomain} {st : SystemState}
    {later earlier w : Nat}
    (h : auditChainCode ctx reader st.declassificationAudit later earlier = w + 1) :
    ∃ j i, auditWindowFindVisible ctx reader st.declassificationAudit 0
        st.declassificationAudit.length later = j + 1 ∧
      auditWindowFindVisible ctx reader st.declassificationAudit 0
        st.declassificationAudit.length earlier = i + 1 ∧
      (if declassificationEventNames (st.declassificationAudit.entry j)
          (st.declassificationAudit.entry i) then 1 else 0) = w := by
  unfold auditChainCode at h
  split at h
  · next j i hF1 hF2 =>
    refine ⟨j, i, hF1, hF2, ?_⟩
    rw [declassificationEventNames_eq_code]
    omega
  · cases h

/-- **A read's code is the specification's word**, for a reader the clearance
dominates. -/
theorem auditReadFastCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (opcode index chunk w : Nat)
    (hMon : DomainFlowPolicy.legacyLattice.canFlow m reader = true)
    (h : auditReadFastCode ctx reader st opcode index chunk = w + 1) :
    (match decodeAuditReadOp opcode index chunk with
     | none => (.error .invalidSyscallArgument : Except KernelError Nat)
     | some op => auditReadWord (liftLegacyContext ctx) (some m) reader st op) = .ok w := by
  have hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true := hMon
  unfold auditReadFastCode at h
  dsimp only at h
  match opcode, h with
  | 0, h =>
    simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte, auditLogVisibleTo_length]
    simp only [Nat.add_right_cancel_iff] at h
    rw [h]
  | 1, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 2, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 3, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 4, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 5, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 6, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 7, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 8, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 9, h =>
    simp only [decodeAuditReadOp, auditReadWord, auditLogVisibleTo_getElem?]
    generalize auditWindowFindVisible ctx reader st.declassificationAudit 0
      st.declassificationAudit.length index = v at h ⊢
    cases v with
    | zero => cases h
    | succ j =>
      simp only [Nat.add_right_cancel_iff] at h
      subst h; rfl
  | 10, h => exact auditBasisCountCode_spec ctx m reader st _ _ h
  | 11, h => exact auditBasisWordCode_spec ctx m reader st _ _ _ h
  | 12, h =>
    simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte]
    simp only [Nat.add_right_cancel_iff] at h
    rw [h]
  | 13, h =>
    simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte]
    simp only [Nat.add_right_cancel_iff] at h
    rw [h]
  | 14, h =>
    obtain ⟨hs, r, hr, hf⟩ := refusalScalarSlotCode_some (fun _ => rfl) h
    simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte, hs, dite_true, RefusalLedger.slotView_eq, hr]
    simp only [Nat.add_right_cancel_iff] at hf
    rw [hf]
  | 15, h => exact refusalFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 16, h => exact refusalFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 17, h => exact refusalFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 18, h => exact refusalFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 19, h => exact refusalFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 20, h => exact refusalFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 21, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 22, h => exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h
  | 23, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 24, h => exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h
  | 25, h => exact refusalReceiverCountCode_spec ctx m reader st _ _ hIs h
  | 26, h => exact refusalReceiverWordCode_spec ctx m reader st _ _ _ hIs h
  | 27, h =>
    by_cases hi : index = 0
    · simp only [hi, ↓reduceIte] at h; cases h
    · simp only [hi, ↓reduceIte] at h
      obtain ⟨j, i, hF1, hF2, hw⟩ := auditChainCode_some h
      simp only [decodeAuditReadOp, auditReadWord, auditLogVisibleTo_getElem?, hF1, hF2, hi,
        ↓reduceIte, hw]
  | 28, h =>
    by_cases hc : chunk < index
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨j, i, hF1, hF2, hw⟩ := auditChainCode_some h
      simp only [decodeAuditReadOp, auditReadWord, auditLogVisibleTo_getElem?, hF1, hF2, hc,
        ↓reduceIte, hw]
    · simp only [hc, ↓reduceIte] at h; cases h
  | 29, h =>
    by_cases hc : chunk < st.declassificationAudit.epoch
    · simp only [hc, ↓reduceIte] at h
      split at h
      · cases h
      · next j hF =>
        simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte,
          SystemState.declassificationAuditEpoch, hc, auditLogVisibleTo_getElem?, hF,
          TaintWords.decode_contains_eq]
        simp only [Nat.add_right_cancel_iff] at h
        rw [h]
    · simp only [hc, ↓reduceIte] at h; cases h
  | _ + 30, h => cases h

/-- **An admitted read's write**: the word staged into the caller's return
registers as words (`writeReturnFrameToTcb_ofWord_eq_words`). -/
@[noinline] def auditReadPerform (tid : SeLe4n.ThreadId) (w : Nat) (st : SystemState) :
    SystemState :=
  st.updateTcb tid (TCB.withReturnWords · w.toUInt64 0 0 0 0 0)

/-- Whether an `.auditRead` is admitted, given the code its read computes
(`auditReadFastCode`): the target is the trail (checked by the caller), the
capability carries the read's right, the configured clearance validates and
dominates the reader, and the read is covered, succeeds and fits a word. -/
@[inline] def auditReadAdmitted (cap : Capability) (m readerDomain : SecurityDomain)
    (code : Nat) : Bool :=
  cap.hasRight (syscallRequiredRight .auditRead) && auditClearanceDominates m &&
    DomainFlowPolicy.legacyLattice.canFlow m readerDomain && code != 0 &&
    decide (code - 1 < 2 ^ 64)

/-- The opcode, index and chunk of a read, from the caller's registers. -/
@[inline] def auditReadCode (ctx : LabelingContext) (readerDomain : SecurityDomain)
    (st : SystemState) (regs : SeLe4n.RegisterFile) : Nat :=
  auditReadFastCode ctx readerDomain st (auditedArgWord regs 0).toNat
    (auditedArgWord regs 1).toNat (auditedArgWord regs 2).toNat

/-- An admitted read is the specification's. -/
theorem auditedArmSpec_auditRead_admitted (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (m : SecurityDomain) (reader : SeLe4n.ThreadId)
    {code : Nat} (hT : cap.target = .auditTrail code) (hM : ctx.auditMonitorClearance = some m)
    (hCur : st.scheduler.currentOnCore executingCore = some reader)
    (hTr : auditTruncated .auditRead regs cap = false)
    (hA : auditReadAdmitted cap m (embedLegacyLabel (ctx.threadLabelOf reader))
      (auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs) = true) :
    auditedArmSpec ctx .auditRead capAddr regs tid executingCore cap st =
      .ok ((), auditReadPerform tid
        (auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs - 1) st) := by
  simp only [auditReadAdmitted, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hA
  obtain ⟨⟨⟨⟨hRight, hDom⟩, hMon⟩, hCode⟩, hFit⟩ := hA
  have hL := Nat.not_lt.mpr (auditTruncated_false_le hTr hT hRight)
  have hV := validatedAuditMonitorClearance_eq_some ctx m hM hDom
  obtain ⟨w, hw⟩ : ∃ w, auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs =
      w + 1 := Nat.exists_eq_succ_of_ne_zero hCode
  have hSpec := auditReadFastCode_spec ctx m _ st _ _ _ w hMon hw
  rw [hw, Nat.add_sub_cancel] at hFit ⊢
  have hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m)
      (embedLegacyLabel (ctx.threadLabelOf reader)) = true := hMon
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    extractAuditAuthority, auditedGate, hRight, ↓reduceIte,
    Architecture.SyscallArgDecode.decodeAuditReadArgs,
    Architecture.SyscallArgDecode.requireMessageLength, hL, auditedDecoded_msgReg regs 0 (by decide),
    auditedDecoded_msgReg regs 1 (by decide), auditedDecoded_msgReg regs 2 (by decide), bind,
    Except.bind, pure, Except.pure, hV, SeLe4n.RegValue.val_mk]
  revert hSpec
  cases decodeAuditReadOp (auditedArgWord regs 0).toNat (auditedArgWord regs 1).toNat
      (auditedArgWord regs 2).toNat with
  | none => intro hSpec; cases hSpec
  | some op =>
    intro hSpec
    simp only at hSpec
    simp only [auditReadFromCore, auditReaderDomain, hCur, Option.map_some,
      liftLegacyContext_threadDomainOf, hIs, ↓reduceIte, hSpec, hFit]
    rw [Architecture.writeReturnFrameToTcb_ofWord_eq_words]
    rfl

/-- **`.auditRead` behind its operand check**: the idle-object check, then the admitted form — the word computed by walking the
ring's live window and staged in place — or the general one
(`auditReadOperandArmR_eq`). -/
@[inline] def auditReadOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
      else if auditTruncated .auditRead regs cap then .error (.truncatedMessage, st)
      else
        match cap.target, ctx.auditMonitorClearance, st.scheduler.currentOnCore executingCore with
        | .auditTrail _, some m, some reader =>
          let code := auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs
          if auditReadAdmitted cap m (embedLegacyLabel (ctx.threadLabelOf reader)) code then
            .ok ((), auditReadPerform tid (code - 1) st)
          else auditGeneralR ctx .auditRead regs capAddr tid executingCore cap st
        | _, _, _ => auditTargetGeneralR ctx .auditRead regs capAddr tid executingCore cap st

/-- `.auditRead` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem auditReadOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditRead)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    auditReadOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  rw [auditOperand_spec ctx decoded regs tid executingCore (.inl hSid) hRegs hLen st tcb rootCn ref hRef,
    hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only [auditReadOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hTr : auditTruncated .auditRead regs cap = true
    · simp only [hIdle, hTr, Bool.false_eq_true, ↓reduceIte, auditGeneralR,
        auditedArmSpec_audit_truncated ctx .auditRead decoded.capAddr regs tid executingCore cap
          st (.inl rfl) hTr]
    · simp only [hIdle, hTr, Bool.false_eq_true, ↓reduceIte]
      split
      · next m reader hT hM hCur =>
        split
        · next hA =>
          simp only [auditGeneralR, auditedArmSpec_auditRead_admitted ctx decoded.capAddr regs tid
            executingCore cap st m reader hT hM hCur (Bool.eq_false_iff.mpr hTr) hA]
        · rfl
      · exact auditTargetGeneralR_eq ctx _ regs _ tid executingCore cap st (.inl rfl)

/-! ## `.declassifySignal` -/

/-- Whether a `.declassifySignal` to `nid` is admitted on the path that stores
its badge: the core runs the caller, the notification is present with no bound
receiver to deliver to and no waiter to wake (`signalDelivery` is `.stored`, so
the plan has no second hop), and the first hop is either an ordinary flow or a
downgrade the policy permits with room in the trail.  A signal that wakes a
receiver takes the general form. -/
@[inline] def declassifySignalStoredAdmitted (ctx : LabelingContext) (st : SystemState)
    (tid signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) : Bool :=
  decide (signaler = tid) && (st.getNotification? nid).isSome &&
    (boundDeliveryTarget? st nid).isNone && (notificationSignalWaiter? st nid).isNone &&
    (securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) ||
      (ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf signaler))
          (embedLegacyLabel (ctx.objectLabelOf nid)) &&
        decide (st.declassificationAudit.length < maxDeclassificationAuditEntries)))

/-- The stored signal's record: when its hop is a downgrade (`hop`), the event
written over the ring's next slot, with the caller's words read from the
signalled state as the specification reads them (`recordDeclassifiedHops`). -/
@[inline] def declassifySignalRecord (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain : SecurityDomain) (nid : SeLe4n.ObjId) (hop : Bool)
    (st1 : SystemState) : SystemState :=
  if hop then
    withTaintWordsAt st1 tid.toObjId fun c0 c1 c2 c3 c4 c5 c6 c7 cc cs =>
      recordEventInPlace c tid actorDomain notifDomain nid
        (st1.declassificationAudit.epoch + st1.declassificationAudit.length) c0 c1 c2 c3 c4 c5 c6 c7 cc cs st1
  else st1

/-- **A stored signal succeeds**: with no bound receiver and no waiter on a
present notification, the signal stores the badge and refuses nothing, so the
admitted form needs no refusal arm. -/
theorem notificationSignalBoundOnCore_stored_ok (nid : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : Concurrency.CoreId) (st : SystemState) (ntfn : Notification)
    (hN : st.getNotification? nid = some ntfn) (hBound : boundDeliveryTarget? st nid = none)
    (hWait : notificationSignalWaiter? st nid = none) :
    (notificationSignalBoundOnCore nid badge c st).2 = .ok none := by
  have hHead : ntfn.waitHead = none := by
    simpa only [notificationSignalWaiter?, hN] using hWait
  unfold notificationSignalBoundOnCore
  rw [hBound, notificationSignalOnCore_eq_impl]
  unfold notificationSignalOnCoreImpl
  simp only [hN, hHead]
  split <;> rfl

/-- **An admitted stored `.declassifySignal`'s writes**: the signal stores the
badge (`notificationSignalBoundOnCore`, which refuses nothing here,
`notificationSignalBoundOnCore_stored_ok`), then the record and the fused taint
step over the caller's and the notification's words captured before the signal.
Out of line, so the words reach it as scalars, and returning the state alone, so
no result record is built across the call. -/
@[noinline] def declassifySignalStoredPerform (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain : SecurityDomain) (nid : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hop : Bool) (epoch len : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool) (st : SystemState) :
    SystemState :=
  declassifySignalTaintStep .stored nid tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ epoch len
    (declassifySignalRecord c tid actorDomain notifDomain nid hop
      (notificationSignalBoundOnCore nid badge c st).1)

/-- A write that leaves a thread's taint words where they are reads the same
words at every id. -/
theorem taintWordsAt_mapTcbInPlace_withMessageSlots (X : SystemState) (w : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (k : SeLe4n.ObjId) :
    (X.mapTcbInPlace w (TCB.withMessageSlots ρ μ π)).taintWordsAt k = X.taintWordsAt k := by
  rw [SystemState.taintWordsAt_eq, SystemState.taintWordsAt_eq, SystemState.objects_mapTcbInPlace]
  by_cases hw : (w.toObjId == k) = true
  · rw [if_pos hw]
    rcases X.objects[k]? with _ | o
    · rfl
    · cases o <;> rfl
  · rw [if_neg hw]

/-- The stored signal's record and a write to a waiter's message slots commute:
the record reads the trail and the caller's words, which the write leaves. -/
theorem declassifySignalRecord_mapTcbInPlace (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain : SecurityDomain) (nid : SeLe4n.ObjId) (hop : Bool)
    (X : SystemState) (w : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) :
    declassifySignalRecord c tid actorDomain notifDomain nid hop
        (X.mapTcbInPlace w (TCB.withMessageSlots ρ μ π)) =
      (declassifySignalRecord c tid actorDomain notifDomain nid hop X).mapTcbInPlace w
        (TCB.withMessageSlots ρ μ π) := by
  unfold declassifySignalRecord
  split
  · rw [withTaintWordsAt_eq, withTaintWordsAt_eq, taintWordsAt_mapTcbInPlace_withMessageSlots]
    rfl
  · rfl

theorem declassifySignalRecord_objects (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain : SecurityDomain) (nid : SeLe4n.ObjId) (hop : Bool)
    (X : SystemState) :
    (declassifySignalRecord c tid actorDomain notifDomain nid hop X).objects = X.objects := by
  unfold declassifySignalRecord
  split
  · rw [withTaintWordsAt_eq]; rfl
  · rfl


/-- **A hop's event written over the audit ring's next slot**, its source
domain given (`recordEventInPlace` writes a first hop, whose source is the
actor's own): stamped `ts`, carrying the taint words handed in as scalars. -/
@[noinline] def recordHopInPlace (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (ts : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool) (st : SystemState) : SystemState :=
  { st with
    declassificationAudit := st.declassificationAudit.recordEvent srcDomain dstDomain targetId
      ts c actorTid actorDomain a0 a1 a2 a3 a4 a5 a6 a7 ac as }

/-- The in-place hop record is the ring's record of the event the state stamps. -/
theorem recordHopInPlace_eq (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain srcDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId)
    (w : TaintWords) (st : SystemState) :
    recordHopInPlace c actorTid actorDomain srcDomain dstDomain targetId
        (st.declassificationAudit.epoch + st.declassificationAudit.length)
        w.tag0 w.tag1 w.tag2 w.tag3 w.tag4 w.tag5 w.tag6 w.tag7 w.count w.saturated st =
      { st with
        declassificationAudit := st.declassificationAudit.append
          (declassifyStoreEventWithTags c { subject := actorTid, domain := actorDomain }
            srcDomain dstDomain targetId w st) } := by
  unfold recordHopInPlace
  rw [AuditRing.recordEvent_eq]
  rfl

/-- **The records a delivered declassified signal owes**, written in place: the
first hop's (`hop1`, the caller into the notification) stamped against the
signalled state and carrying the caller's words, then the second hop's
(`hop2`, the notification into the receiver `recv`) stamped against the state
the first left and carrying the caller's words extended with the first's stamp
when there was one (`recordDeclassifiedHopsFrom`).  Every word is read off the
state before it is handed over. -/
@[inline] def declassifySignalHopsRecord (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (recv : SeLe4n.ThreadId) (hop1 hop2 : Bool) (st1 : SystemState) : SystemState :=
  withTaintWordsAt st1 tid.toObjId fun c0 c1 c2 c3 c4 c5 c6 c7 cc cs =>
    let ts := st1.declassificationAudit.epoch + st1.declassificationAudit.length
    let s1 := if hop1 then
        recordHopInPlace c tid actorDomain actorDomain notifDomain nid ts
          c0 c1 c2 c3 c4 c5 c6 c7 cc cs st1
      else st1
    if hop2 then
      let w := TaintWords.selectWords hop1
        (TaintWords.join ⟨c0, c1, c2, c3, c4, c5, c6, c7, cc, cs⟩ (TaintWords.singletonWords ts))
        ⟨c0, c1, c2, c3, c4, c5, c6, c7, cc, cs⟩
      recordHopInPlace c tid actorDomain notifDomain recvDomain recv.toObjId
        (s1.declassificationAudit.epoch + s1.declassificationAudit.length)
        w.tag0 w.tag1 w.tag2 w.tag3 w.tag4 w.tag5 w.tag6 w.tag7 w.count w.saturated s1
    else s1

/-- A hop's authorization as the plan reads it: a downgrade, or an ordinary
flow. -/
@[inline] def hopAuthorizationOf (downgrade : Bool) : DeclassifiedHopAuthorization :=
  if downgrade then .declassified else .ordinary

/-- **The in-place records are the specification's**: with room in the trail
for every record owed, `recordDeclassifiedHops` records the two hops' records
exactly as `declassifySignalHopsRecord` writes them. -/
theorem recordDeclassifiedHops_hopsRecord (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (recv : SeLe4n.ThreadId) (hop1 hop2 : Bool) (st1 : SystemState)
    (hRoom : st1.declassificationAudit.length + (if hop1 then 1 else 0) +
      (if hop2 then 1 else 0) ≤ maxDeclassificationAuditEntries) :
    recordDeclassifiedHops c { subject := tid, domain := actorDomain }
        (declassifiedHopRecords (hopAuthorizationOf hop1) actorDomain notifDomain nid ++
          declassifiedHopRecords (hopAuthorizationOf hop2) notifDomain recvDomain recv.toObjId)
        st1 =
      some (declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid recv hop1 hop2
        st1) := by
  unfold declassifySignalHopsRecord
  rw [withTaintWordsAt_eq]
  cases hop1 <;> cases hop2 <;>
    simp only [hopAuthorizationOf, Bool.false_eq_true, ↓reduceIte, declassifiedHopRecords,
      List.nil_append, List.cons_append, recordDeclassifiedHops, recordDeclassifiedHopsFrom,
      recordDeclassificationChecked, declassificationActorWords, TaintWords.selectWords_eq,
      TaintWords.mk_fields] at hRoom ⊢
  · rw [if_pos (by omega), recordHopInPlace_eq]
  · rw [if_pos (by omega), recordHopInPlace_eq]
  · have hL := AuditRing.length_append st1.declassificationAudit
      (declassifyStoreEventWithTags c { subject := tid, domain := actorDomain } actorDomain
        notifDomain nid (st1.taintWordsAt tid.toObjId) st1)
      (by rw [AuditRing.length_toList]; omega)
    rw [if_pos (by omega), recordHopInPlace_eq, recordHopInPlace_eq]
    simp only [hL, if_pos (show st1.declassificationAudit.length + 1 <
      maxDeclassificationAuditEntries by omega)]

/-- The in-place records write no object. -/
theorem declassifySignalHopsRecord_objects (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (recv : SeLe4n.ThreadId) (hop1 hop2 : Bool) (X : SystemState) :
    (declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid recv hop1 hop2
      X).objects = X.objects := by
  unfold declassifySignalHopsRecord
  rw [withTaintWordsAt_eq]
  cases hop1 <;> cases hop2 <;> rfl

/-- The in-place records and a write to a thread's message slots commute: the
records read the trail and the caller's words, which the write leaves. -/
theorem declassifySignalHopsRecord_mapTcbInPlace (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (actorDomain notifDomain recvDomain : SecurityDomain)
    (nid : SeLe4n.ObjId) (recv : SeLe4n.ThreadId) (hop1 hop2 : Bool) (X : SystemState)
    (w : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) :
    declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid recv hop1 hop2
        (X.mapTcbInPlace w (TCB.withMessageSlots ρ μ π)) =
      (declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid recv hop1 hop2
        X).mapTcbInPlace w (TCB.withMessageSlots ρ μ π) := by
  unfold declassifySignalHopsRecord
  rw [withTaintWordsAt_eq, withTaintWordsAt_eq, taintWordsAt_mapTcbInPlace_withMessageSlots]
  cases hop1 <;> cases hop2 <;> rfl

/-- **A declassified signal's wake, delivered**: the waiter woken without the
badge message, the records its two hops owe written over the trail, then the
badge frame written into the waiter's saved registers
(`declassifySignalWoken_eq_writes`).  The message is built only where the
waiter is, unexpectedly, not ready. -/
@[inline] def declassifySignalWokenWrites (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (nextCode : Nat) (badge : SeLe4n.Badge) (hop1 hop2 : Bool)
    (st : SystemState) : SystemState :=
  let X := (wakeThread (storeSignalWokenWith st nid waiter (SeLe4n.ThreadId.ofOptCode nextCode)
    receiverReady) waiter c).1
  let Y := declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid waiter hop1
    hop2 X
  writeDeliveredFrameIfReady Y waiter (Architecture.returnFrameOfBadge badge)
    (fun _ => holdSignalBody Y waiter badge)

/-- The specification's woken signal, its records, then the staged badge, is
the delivered form. -/
theorem declassifySignalWoken_eq_writes (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (badge : SeLe4n.Badge)
    (hop1 hop2 : Bool) (st : SystemState) (hNo : st.objects.noResizeDue) :
    Architecture.stageWokenDelivery
        (declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid waiter hop1 hop2
          (wakeThread (storeSignalWoken st nid waiter next
            { IpcMessage.empty with badge := some badge }) waiter c).1)
        (some waiter) 0 =
      declassifySignalWokenWrites c tid actorDomain notifDomain recvDomain nid waiter
        (SeLe4n.ThreadId.optCode next) badge hop1 hop2 st := by
  have hNo0 := storeSignalWokenWith_noResizeDue st nid waiter next receiverReady hNo
  have hNo1 := wakeThread_noResizeDue _ waiter c hNo0
  unfold declassifySignalWokenWrites holdSignalBody
  rw [SeLe4n.ThreadId.ofOptCode_optCode, storeSignalWoken_eq_hold _ _ _ _ _ hNo,
    wakeThread_msg _ _ _ _ _ _ _ hNo0]
  dsimp only
  rw [declassifySignalHopsRecord_mapTcbInPlace, Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _
      (by rw [declassifySignalHopsRecord_objects]; exact hNo1) (by simp [IpcMessage.empty]),
    returnFrameOfMessage_badge]

/-- Whether a `.declassifySignal` to `nid` that wakes the notification's head
waiter `waiter` is admitted in place: the core runs the caller, no bound
receiver, every write of the wake in its slot (`signalWakesInPlace`), each hop
either an ordinary flow or a downgrade the policy permits, and room in the trail
for every record the downgrades owe. -/
@[inline] def declassifySignalWokenAdmitted (ctx : LabelingContext) (st : SystemState)
    (tid signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId) : Bool :=
  decide (signaler = tid) && (boundDeliveryTarget? st nid).isNone &&
    signalWakesInPlace st nid waiter &&
    (securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) ||
      ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf signaler))
        (embedLegacyLabel (ctx.objectLabelOf nid))) &&
    (securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf waiter) ||
      ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.objectLabelOf nid))
        (embedLegacyLabel (ctx.threadLabelOf waiter))) &&
    decide (st.declassificationAudit.length +
        (if !securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) then 1 else 0) +
        (if !securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf waiter) then 1 else 0) ≤
      maxDeclassificationAuditEntries)

/-- **An admitted woken `.declassifySignal`'s writes**: the wake delivered with
its records (`declassifySignalWokenWrites`), then the fused taint step over the
caller's and the notification's words captured before the signal. -/
@[noinline] def declassifySignalWokenPerform (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (nextCode : Nat) (badge : SeLe4n.Badge) (hop1 hop2 : Bool)
    (epoch len : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool) (st : SystemState) :
    SystemState :=
  declassifySignalTaintStep (.toWaiter waiter) nid tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ epoch len
    (declassifySignalWokenWrites c tid actorDomain notifDomain recvDomain nid waiter nextCode badge
      hop1 hop2 st)

/-- **A declassified signal's bound delivery, delivered**: the bound thread `t`
taken off the receive queue of the endpoint `epId` it is blocked on and made
ready without the badge message, woken, the records its two hops owe written
over the trail, then the badge frame written into its saved registers
(`declassifySignalBound_eq_writes`).  The message is built only where the
thread is, unexpectedly, not ready. -/
@[inline] def declassifySignalBoundWrites (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB)
    (badge : SeLe4n.Badge) (hop1 hop2 : Bool) (st : SystemState) : SystemState :=
  let X := (wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t receiveReadyTcb) t
    c).1
  let Y := declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid t hop1 hop2 X
  writeDeliveredFrameIfReady Y t (Architecture.returnFrameOfBadge badge)
    (fun _ => holdSignalBody Y t badge)

/-- The specification's bound delivery, its records, the stash drop and the
staged badge, is the delivered form. -/
theorem declassifySignalBound_eq_writes (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB)
    (badge : SeLe4n.Badge) (hop1 hop2 : Bool) (st : SystemState)
    (hNo : st.objects.noResizeDue) :
    Architecture.stageWokenDelivery
        (clearWokenReceiverStashPure (some t)
          (declassifySignalHopsRecord c tid actorDomain notifDomain recvDomain nid t hop1 hop2
            (wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t
              (receiveCompleteTcb { IpcMessage.empty with badge := some badge })) t c).1))
        (some t) 0 =
      declassifySignalBoundWrites c tid actorDomain notifDomain recvDomain nid t epId ep tcb
        badge hop1 hop2 st := by
  have hNo1 := storeQueueRemove_noResizeDue st epId true t ep tcb hNo
  have hNo2 : ((storeQueueRemove st epId true t ep tcb).mapTcbInPlace t
      ipcReadyTcb).objects.noResizeDue := (SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNo1
  unfold declassifySignalBoundWrites holdSignalBody
  rw [receiveCompleteTcb_eq_slots, receiveReadyTcb_eq_slots,
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1,
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo1,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.mapTcbInPlace_mapTcbInPlace]
  simp only [receiveCompleteSlots, clearMessageSlots]
  rw [wakeThread_msg _ _ _ _ _ _ _ hNo2, wakeThread_msg _ _ _ _ _ _ _ hNo2]
  dsimp only
  rw [declassifySignalHopsRecord_mapTcbInPlace, declassifySignalHopsRecord_mapTcbInPlace]
  have hD : ∀ M : IpcMessage,
      TCB.withMessageSlots id (fun _ => some M) (fun _ : Nat => 0) =
        holdMessage M ∘ TCB.withMessageSlots id (fun _ => none) (fun _ => 0) := fun _ => rfl
  rw [clearWokenReceiverStashPure_mapTcbInPlace _ _ _ (fun _ => rfl),
    hD, ← SystemState.mapTcbInPlace_mapTcbInPlace,
    Architecture.stageWokenDelivery_some,
    stageDeliveredMessage_holdMessage _ _ _
      ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr
        (by rw [declassifySignalHopsRecord_objects]; exact wakeThread_noResizeDue _ _ _ hNo2))
      (by simp [IpcMessage.empty]),
    returnFrameOfMessage_badge]

/-- Whether a `.declassifySignal` to `nid` that delivers to its bound thread `t`,
blocked receiving on the endpoint `ep` at `epId` (whose TCB is `tcb`), is
admitted in place: the core runs the caller, every write of the removal in its
slot (`queueRemoveInPlace`), each hop either an ordinary flow or a downgrade
the policy permits, and room in the trail for every record the downgrades
owe. -/
@[inline] def declassifySignalBoundAdmitted (ctx : LabelingContext) (st : SystemState)
    (tid signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB) : Bool :=
  decide (signaler = tid) && queueRemoveInPlace st epId true t ep tcb &&
    (securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) ||
      ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf signaler))
        (embedLegacyLabel (ctx.objectLabelOf nid))) &&
    (securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf t) ||
      ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.objectLabelOf nid))
        (embedLegacyLabel (ctx.threadLabelOf t))) &&
    decide (st.declassificationAudit.length +
        (if !securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) then 1 else 0) +
        (if !securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf t) then 1 else 0) ≤
      maxDeclassificationAuditEntries)

/-- **An admitted bound `.declassifySignal`'s writes**: the bound delivery with
its records (`declassifySignalBoundWrites`), then the fused taint step over the
caller's and the notification's words captured before the signal. -/
@[noinline] def declassifySignalBoundPerform (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain recvDomain : SecurityDomain) (nid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB)
    (badge : SeLe4n.Badge) (hop1 hop2 : Bool) (epoch len : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool) (st : SystemState) :
    SystemState :=
  declassifySignalTaintStep (.toBound t) nid tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ epoch len
    (declassifySignalBoundWrites c tid actorDomain notifDomain recvDomain nid t epId ep tcb badge
      hop1 hop2 st)

/-- A notification with a bound-delivery target has no waiter. -/
theorem notificationSignalWaiter?_of_boundDeliveryTarget (st : SystemState) (nid : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (h : boundDeliveryTarget? st nid = some (t, epId)) :
    notificationSignalWaiter? st nid = none := by
  unfold boundDeliveryTarget? at h
  unfold notificationSignalWaiter?
  split at h
  · next ntfn hN =>
    rw [hN]
    split at h
    · next h0 => simp only [Notification.waitHead, h0]; rfl
    · cases h
  · cases h

/-- An admitted bound `.declassifySignal` is the specification's: the bound
thread taken off its endpoint and woken holding the badge, the records its two
hops owe, its stash dropped, then the badge staged into it. -/
theorem auditedArmSpec_declassifySignal_bound (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId) (ep : Endpoint) (tcb : TCB)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hTarget : boundDeliveryTarget? st nid = some (t, epId))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hTT : st.objects[t.toObjId]? = some (.tcb tcb))
    (hA : declassifySignalBoundAdmitted ctx st tid signaler nid t epId ep tcb = true) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      .ok ((), Architecture.stageWokenDelivery
        (clearWokenReceiverStashPure (some t)
          (declassifySignalHopsRecord executingCore tid
            (embedLegacyLabel (ctx.threadLabelOf tid)) (embedLegacyLabel (ctx.objectLabelOf nid))
            (embedLegacyLabel (ctx.threadLabelOf t)) nid t
            (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
            (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf t))
            (wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t
              (receiveCompleteTcb
                { IpcMessage.empty with badge := some cap.signalBadge }))
              t executingCore).1))
        (some t) 0) := by
  simp only [declassifySignalBoundAdmitted, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at hA
  obtain ⟨⟨⟨⟨hSig, hG⟩, hHop1⟩, hHop2⟩, hRoom⟩ := hA
  subst hSig
  obtain ⟨ntfn, hN⟩ := declassifiedSignalReceiver?_some_notification st nid t
    (declassifiedSignalReceiver?_bound st nid t epId hTarget)
  have hWait := notificationSignalWaiter?_of_boundDeliveryTarget st nid t epId hTarget
  have hS := notificationSignalBoundOnCore_bound_eq nid
    cap.signalBadge executingCore st t epId ep tcb hTarget hE hTT hG
  have hLen := congrArg List.length (notificationSignalBoundOnCore_declassificationAuditLog_eq nid
    cap.signalBadge executingCore st)
  rw [hS] at hLen
  simp only [SystemState.declassificationAuditLog, AuditRing.length_toList] at hLen
  generalize (wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t
      (receiveCompleteTcb
        { IpcMessage.empty with badge := some cap.signalBadge }))
      t executingCore) = W at hS hLen ⊢
  have hRec := recordDeclassifiedHops_hopsRecord executingCore signaler
    (embedLegacyLabel (ctx.threadLabelOf signaler)) (embedLegacyLabel (ctx.objectLabelOf nid))
    (embedLegacyLabel (ctx.threadLabelOf t)) nid t
    (!securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid))
    (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf t)) W.1 (by rw [hLen]; exact hRoom)
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    notificationSignalDeclassifiedCrossCoreDispatch,
    notificationSignalDeclassifiedOnCore, hCur, hN, declassificationActorOf,
    liftLegacyContext_threadDomainOf, liftLegacyContext_objectDomainOf, declassifiedSignalPlan,
    declassifiedSignalHopAuthorization, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    declassifiedSignalReceiver?, hTarget, hWait, Option.map_some, hS,
    clearWokenReceiverStash_eq_pure, Architecture.stageWokenDelivery_none]
  by_cases hF1 : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true <;>
  by_cases hF2 : securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf t) = true <;>
  simp only [hF1, hF2, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    declassificationDecision, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    hopAuthorizationOf] at hRec hHop1 hHop2 ⊢
  all_goals simp only [false_or, true_or] at hHop1 hHop2
  all_goals (try simp only [hHop1, hHop2, ↓reduceIte])
  all_goals rw [hRec]

/-- Whether a hop from `src` to `dst` is refused: the base lattice denies the
flow and the declassification policy does not authorize it
(`declassifiedSignalHopAuthorization` on the lifted legacy context). -/
@[inline] def declassifySignalHopRefused (ctx : LabelingContext) (src dst : SecurityLabel) : Bool :=
  !securityFlowsTo src dst &&
    !ctx.declassificationPolicy.canDeclassify (embedLegacyLabel src) (embedLegacyLabel dst)

/-- **Why `.declassifySignal`'s plan refuses**, as a code read before any
write (`declassifiedSignalPlan`): `1` when the signaller's hop into the
notification is refused (`.declassificationDenied`), `2` when the hop onward
into the resolved receiver is (`.declassificationDeniedAtReceiver`), `0` when
the plan is admitted.  The receiver is matched where it is resolved, so
neither its `some` nor the bound pair is built. -/
@[inline] def declassifySignalPlanRefusal (ctx : LabelingContext) (st : SystemState)
    (signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) : Nat :=
  if declassifySignalHopRefused ctx (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) then 1
  else
    match declassifiedSignalReceiver? st nid with
    | some receiver =>
      if declassifySignalHopRefused ctx (ctx.objectLabelOf nid) (ctx.threadLabelOf receiver) then 2
      else 0
    | none => 0

/-- `declassifySignalPlanRefusal` as compiled: the receiver resolved as its code
(`declassifiedSignalReceiverCode`), its hop tested on the word, so the plan
builds no receiver (`declassifySignalPlanRefusal_eq_code`). -/
@[inline] def declassifySignalPlanRefusalCode (ctx : LabelingContext) (st : SystemState)
    (signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) : Nat :=
  if declassifySignalHopRefused ctx (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) then 1
  else
    match declassifiedSignalReceiverCode st nid with
    | 0 => 0
    | k + 1 =>
      if declassifySignalHopRefused ctx (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩) then 2
      else 0

@[csimp] theorem declassifySignalPlanRefusal_eq_code :
    @declassifySignalPlanRefusal = @declassifySignalPlanRefusalCode := by
  funext ctx st signaler nid
  unfold declassifySignalPlanRefusal declassifySignalPlanRefusalCode
  rw [← ofOptCode_declassifiedSignalReceiverCode]
  split
  · rfl
  · rcases declassifiedSignalReceiverCode st nid with _ | k <;> rfl

/-- **The plan's refusal on a present notification**: `declassifySignalPlanRefusal`
when the capability names a notification, `0` otherwise.  The notification's
lookup is matched where it is made and its `some` discarded, so a caller that
reads the notification again (the admitted forms below) holds no option across
the test (`declassifySignalPresentRefusal_ne_zero`). -/
@[inline] def declassifySignalPresentRefusal (ctx : LabelingContext) (st : SystemState)
    (signaler : SeLe4n.ThreadId) (nid : SeLe4n.ObjId) : Nat :=
  match st.getNotification? nid with
  | some _ => declassifySignalPlanRefusal ctx st signaler nid
  | none => 0

theorem declassifySignalPresentRefusal_ne_zero {ctx : LabelingContext} {st : SystemState}
    {signaler : SeLe4n.ThreadId} {nid : SeLe4n.ObjId}
    (h : declassifySignalPresentRefusal ctx st signaler nid ≠ 0) :
    (st.getNotification? nid).isSome = true ∧
      declassifySignalPresentRefusal ctx st signaler nid =
        declassifySignalPlanRefusal ctx st signaler nid ∧
      declassifySignalPlanRefusal ctx st signaler nid ≠ 0 := by
  unfold declassifySignalPresentRefusal at h ⊢
  split at h
  · next hN => exact ⟨by simp only [hN, Option.isSome_some], rfl, h⟩
  · exact absurd rfl h

/-- **A `.declassifySignal` whose capability names no notification**: `1` when
the object it names is present but of another kind, `2` when nothing is there,
`0` when it names a notification.  The lookup is matched where it is made, so
no option is held across the test; the specification answers it as the
ordinary signal does (`auditedArmSpec_declassifySignal_absent`). -/
@[inline] def declassifySignalAbsentRefusal (st : SystemState) (nid : SeLe4n.ObjId) : Nat :=
  match st.getNotification? nid with
  | some _ => 0
  | none => if (st.getObjectType? nid).isSome then 1 else 2

/-- The error an absent notification's code names. -/
@[inline] def declassifySignalAbsentRefusalError (code : Nat) : KernelError :=
  if code = 1 then (.invalidCapability 0) else .objectNotFound

theorem declassifySignalAbsentRefusal_ne_zero {st : SystemState} {nid : SeLe4n.ObjId}
    (h : declassifySignalAbsentRefusal st nid ≠ 0) : st.getNotification? nid = none := by
  unfold declassifySignalAbsentRefusal at h
  split at h
  · exact absurd rfl h
  · assumption

/-- The error a refused plan's code names. -/
@[inline] def declassifySignalPlanRefusalError (code : Nat) : KernelError :=
  if code = 1 then .declassificationDenied else .declassificationDeniedAtReceiver

/-- A `.declassifySignal` on a present notification whose plan refuses is the
specification's refusal, with the error its code names. -/
theorem auditedArmSpec_declassifySignal_planRefused (ctx : LabelingContext)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState)
    (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hPresent : (st.getNotification? nid).isSome = true)
    (hR : declassifySignalPlanRefusal ctx st signaler nid ≠ 0) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      .error (declassifySignalPlanRefusalError (declassifySignalPlanRefusal ctx st signaler nid)) := by
  obtain ⟨ntfn, hN⟩ := Option.isSome_iff_exists.mp hPresent
  unfold declassifySignalPlanRefusal at hR ⊢
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    notificationSignalDeclassifiedCrossCoreDispatch,
    notificationSignalDeclassifiedOnCore, hCur, hN, declassificationActorOf,
    liftLegacyContext_threadDomainOf, liftLegacyContext_objectDomainOf, declassifiedSignalPlan,
    declassifiedSignalHopAuthorization, liftLegacyContext_policy, legacyLattice_canFlow_embed]
  by_cases h1 : declassifySignalHopRefused ctx (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid)
  · have h1' := h1
    simp only [declassifySignalHopRefused, Bool.and_eq_true, Bool.not_eq_true'] at h1'
    simp only [h1, h1'.1, h1'.2, ↓reduceIte, declassificationDecision, liftLegacyContext_policy,
      legacyLattice_canFlow_embed, Bool.false_eq_true, declassifySignalPlanRefusalError,
      DeclassifiedSignalHop.refusal]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hR ⊢
    have hOk : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true ∨
        ctx.declassificationPolicy.canDeclassify (embedLegacyLabel (ctx.threadLabelOf signaler))
          (embedLegacyLabel (ctx.objectLabelOf nid)) = true := by
      by_cases hF : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true
      · exact .inl hF
      · right
        simp only [declassifySignalHopRefused, hF, Bool.not_false,
          Bool.true_and, Bool.not_eq_true'] at h1
        simpa using h1
    rcases hOk with hF | hD
    · simp only [hF, ↓reduceIte]
      cases hRcv : declassifiedSignalReceiver? st nid with
      | none => simp only [hRcv] at hR; exact absurd rfl hR
      | some receiver =>
        simp only [hRcv] at hR ⊢
        by_cases h2 : declassifySignalHopRefused ctx (ctx.objectLabelOf nid)
            (ctx.threadLabelOf receiver)
        · have h2' := h2
          simp only [declassifySignalHopRefused, Bool.and_eq_true, Bool.not_eq_true'] at h2'
          simp only [h2, h2'.1, h2'.2, ↓reduceIte, declassificationDecision,
            liftLegacyContext_policy, legacyLattice_canFlow_embed, Bool.false_eq_true,
            declassifySignalPlanRefusalError, DeclassifiedSignalHop.refusal, Nat.reduceEqDiff]
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hR
          exact absurd rfl hR
    · by_cases hF : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true
      · simp only [hF, ↓reduceIte]
        cases hRcv : declassifiedSignalReceiver? st nid with
        | none => simp only [hRcv] at hR; exact absurd rfl hR
        | some receiver =>
          simp only [hRcv] at hR ⊢
          by_cases h2 : declassifySignalHopRefused ctx (ctx.objectLabelOf nid)
              (ctx.threadLabelOf receiver)
          · have h2' := h2
            simp only [declassifySignalHopRefused, Bool.and_eq_true, Bool.not_eq_true'] at h2'
            simp only [h2, h2'.1, h2'.2, ↓reduceIte, declassificationDecision,
              liftLegacyContext_policy, legacyLattice_canFlow_embed, Bool.false_eq_true,
              declassifySignalPlanRefusalError, DeclassifiedSignalHop.refusal, Nat.reduceEqDiff]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hR
            exact absurd rfl hR
      · simp only [hF, Bool.false_eq_true, ↓reduceIte, declassificationDecision,
          liftLegacyContext_policy, legacyLattice_canFlow_embed, hD]
        cases hRcv : declassifiedSignalReceiver? st nid with
        | none => simp only [hRcv] at hR; exact absurd rfl hR
        | some receiver =>
          simp only [hRcv] at hR ⊢
          by_cases h2 : declassifySignalHopRefused ctx (ctx.objectLabelOf nid)
              (ctx.threadLabelOf receiver)
          · have h2' := h2
            simp only [declassifySignalHopRefused, Bool.and_eq_true, Bool.not_eq_true'] at h2'
            simp only [h2, h2'.1, h2'.2, ↓reduceIte,
              Bool.false_eq_true,
              declassifySignalPlanRefusalError, DeclassifiedSignalHop.refusal, Nat.reduceEqDiff]
          · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hR
            exact absurd rfl hR

/-- `.declassifySignal`'s general form: the specification's arm, then its fused
taint step over the pre-state's words (`declassifySignalTaintStep_eq`), every
refusal carrying the state it was handed. -/
def declassifySignalGeneralR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st with
    | .error e => .error (e, st)
    | .ok ((), post) =>
        .ok ((), declassifySignalTaintStep (signalTaintCaseOf st (some cap)) (capObjectId cap) tid
          (st.taintWordsAt tid.toObjId) (st.taintWordsAt (capObjectId cap))
          st.declassificationAuditEpoch st.declassificationAudit.length post)

/-- A `.declassifySignal` whose capability names no notification is the
specification's refusal, with the error its code names. -/
theorem auditedArmSpec_declassifySignal_absent (ctx : LabelingContext)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState)
    (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hAbsent : st.getNotification? nid = none) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      .error (declassifySignalAbsentRefusalError (declassifySignalAbsentRefusal st nid)) := by
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    notificationSignalDeclassifiedCrossCoreDispatch, notificationSignalDeclassifiedOnCore, hCur,
    hAbsent, declassifySignalAbsentRefusal, declassifySignalAbsentRefusalError]
  by_cases hO : (st.getObjectType? nid).isSome = true <;> simp [hO]

/-- **`.declassifySignal` behind its operand check**: the idle-object check and
the rights gate of the classic lookup, then the admitted in-place form, the
badge stored, the head waiter woken or the bound thread delivered to (each
writing the records its one or two downgrades owe), or else the general one
(`declassifySignalOperandArmR_eq`). -/
@[inline] def declassifySignalOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
      else if !syscallTargetAccepted .declassifySignal st cap then .error (.invalidCapability 0, st)
      else if cap.hasRight (syscallRequiredRight .declassifySignal) then
        match cap.target, st.scheduler.currentOnCore executingCore with
        | .object nid, some signaler =>
          if declassifySignalAbsentRefusal st nid != 0 then
            .error (declassifySignalAbsentRefusalError (declassifySignalAbsentRefusal st nid), st)
          else
          if declassifySignalPresentRefusal ctx st signaler nid != 0 then
            .error (declassifySignalPlanRefusalError (declassifySignalPresentRefusal ctx st signaler nid),
              st)
          else
          if declassifySignalStoredAdmitted ctx st tid signaler nid then
            withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
            withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
            .ok ((), declassifySignalStoredPerform executingCore tid
              (embedLegacyLabel (ctx.threadLabelOf tid)) (embedLegacyLabel (ctx.objectLabelOf nid))
              nid cap.signalBadge
              (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
              st.declassificationAudit.epoch st.declassificationAudit.length
              a0 a1 a2 a3 a4 a5 a6 a7 ac as b0 b1 b2 b3 b4 b5 b6 b7 bc bs st)
          else
            match st.getNotification? nid with
            | some ntfn =>
              match ntfn.waitHeadCode with
              | k + 1 =>
                if declassifySignalWokenAdmitted ctx st tid signaler nid ⟨k⟩ then
                  withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
                  withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
                  .ok ((), declassifySignalWokenPerform executingCore tid
                    (embedLegacyLabel (ctx.threadLabelOf tid))
                    (embedLegacyLabel (ctx.objectLabelOf nid))
                    (embedLegacyLabel (ctx.threadLabelOf ⟨k⟩)) nid ⟨k⟩ (ntfnSuccessorCode st ⟨k⟩)
                    cap.signalBadge
                    (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
                    (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩))
                    st.declassificationAudit.epoch st.declassificationAudit.length
                    a0 a1 a2 a3 a4 a5 a6 a7 ac as b0 b1 b2 b3 b4 b5 b6 b7 bc bs st)
                else declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
              | 0 =>
                -- No waiter: a bound thread blocked receiving takes the badge.
                match ntfn.boundTCBCode with
                | k + 1 =>
                  match st.getTcb? ⟨k⟩ with
                  | some tcb =>
                    if tcb.ipcStateCode = 1 then
                      match st.getEndpoint? ⟨tcb.ipcObjectCode⟩ with
                      | some ep =>
                        if declassifySignalBoundAdmitted ctx st tid signaler nid ⟨k⟩
                            ⟨tcb.ipcObjectCode⟩ ep tcb then
                          withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
                          withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
                          .ok ((), declassifySignalBoundPerform executingCore tid
                            (embedLegacyLabel (ctx.threadLabelOf tid))
                            (embedLegacyLabel (ctx.objectLabelOf nid))
                            (embedLegacyLabel (ctx.threadLabelOf ⟨k⟩)) nid ⟨k⟩
                            ⟨tcb.ipcObjectCode⟩ ep tcb cap.signalBadge
                            (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
                            (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩))
                            st.declassificationAudit.epoch st.declassificationAudit.length
                            a0 a1 a2 a3 a4 a5 a6 a7 ac as b0 b1 b2 b3 b4 b5 b6 b7 bc bs st)
                        else declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
                      | _ => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
                    else declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
                  | _ => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
                | 0 => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
            | none => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
        | _, _ => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
      else .error (syscallMissingRightError .declassifySignal, st)

/-- An admitted stored `.declassifySignal` is the specification's: the signal,
then the record its one hop owes when it is a downgrade. -/
theorem auditedArmSpec_declassifySignal_stored (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hA : declassifySignalStoredAdmitted ctx st tid signaler nid = true) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      match notificationSignalBoundOnCore nid cap.signalBadge
          executingCore st with
      | (_, .error e) => .error e
      | (st1, .ok _) => .ok ((), declassifySignalRecord executingCore tid
          (embedLegacyLabel (ctx.threadLabelOf tid)) (embedLegacyLabel (ctx.objectLabelOf nid)) nid
          (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid)) st1) := by
  simp only [declassifySignalStoredAdmitted, Bool.and_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none, Bool.or_eq_true] at hA
  obtain ⟨⟨⟨⟨hSig, hPresent⟩, hBound⟩, hWait⟩, hHop⟩ := hA
  subst hSig
  obtain ⟨ntfn, hN⟩ := Option.isSome_iff_exists.mp hPresent
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    notificationSignalDeclassifiedCrossCoreDispatch,
    notificationSignalDeclassifiedOnCore, hCur, hN, declassificationActorOf,
    liftLegacyContext_threadDomainOf, liftLegacyContext_objectDomainOf, declassifiedSignalPlan,
    declassifiedSignalHopAuthorization, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    declassifiedSignalReceiver?, hBound, hWait, Option.map_none]
  have hLen := congrArg List.length (notificationSignalBoundOnCore_declassificationAuditLog_eq nid
    cap.signalBadge executingCore st)
  simp only [SystemState.declassificationAuditLog, AuditRing.length_toList] at hLen
  rcases hS : notificationSignalBoundOnCore nid cap.signalBadge
      executingCore st with ⟨st1, _ | sgi⟩
  · rw [hS] at hLen
    by_cases hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true
    · simp only [hFlow, ↓reduceIte]
    · obtain ⟨hDecl, -⟩ := hHop.resolve_left hFlow
      simp only [hFlow, Bool.false_eq_true, ↓reduceIte, declassificationDecision,
        liftLegacyContext_policy, legacyLattice_canFlow_embed, hDecl]
  · rw [hS] at hLen
    simp only at hLen
    by_cases hFlow : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true
    · simp only [hFlow, ↓reduceIte, declassifiedHopRecords, recordDeclassifiedHops_nil,
        declassifySignalRecord, Bool.not_true, Bool.false_eq_true, clearWokenReceiverStash,
        Architecture.stageWokenDelivery_none]
    · obtain ⟨hDecl, hRoom⟩ := hHop.resolve_left hFlow
      have hRoom1 : st1.declassificationAudit.length < maxDeclassificationAuditEntries := by
        rw [hLen]; exact hRoom
      simp only [hFlow, Bool.false_eq_true, ↓reduceIte, declassificationDecision,
        liftLegacyContext_policy, legacyLattice_canFlow_embed, hDecl, declassifiedHopRecords,
        recordDeclassifiedHops, recordDeclassifiedHopsFrom, recordDeclassificationChecked,
        hRoom1, declassifySignalRecord, Bool.not_false,
        clearWokenReceiverStash, Architecture.stageWokenDelivery_none, withTaintWordsAt_eq]
      rw [recordEventInPlace_eq]

/-- An admitted woken `.declassifySignal` is the specification's: the wake,
then the records its two hops owe, then the badge staged into the waiter. -/
theorem auditedArmSpec_declassifySignal_woken (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (ntfn : Notification) (k : Nat)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hN : st.getNotification? nid = some ntfn) (hK : ntfn.waitHeadCode = k + 1)
    (hA : declassifySignalWokenAdmitted ctx st tid signaler nid ⟨k⟩ = true) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      .ok ((), Architecture.stageWokenDelivery
        (declassifySignalHopsRecord executingCore tid
          (embedLegacyLabel (ctx.threadLabelOf tid)) (embedLegacyLabel (ctx.objectLabelOf nid))
          (embedLegacyLabel (ctx.threadLabelOf ⟨k⟩)) nid ⟨k⟩
          (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
          (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩))
          (wakeThread (storeSignalWoken st nid ⟨k⟩ (ntfnSuccessor? st ⟨k⟩)
            { IpcMessage.empty with badge := some cap.signalBadge })
            ⟨k⟩ executingCore).1)
        (some ⟨k⟩) 0) := by
  simp only [declassifySignalWokenAdmitted, Bool.and_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none, Bool.or_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨hSig, hBound⟩, hW⟩, hHop1⟩, hHop2⟩, hRoom⟩ := hA
  subst hSig
  have hHead : ntfn.waitHead = some ⟨k⟩ := by
    rw [← Notification.ofOptCode_waitHeadCode, hK]; rfl
  have hWait : notificationSignalWaiter? st nid = some ⟨k⟩ := by
    simp only [notificationSignalWaiter?, hN, hHead]
  have hS : notificationSignalBoundOnCore nid cap.signalBadge
      executingCore st =
      ((wakeThread (storeSignalWoken st nid ⟨k⟩ (ntfnSuccessor? st ⟨k⟩)
          { IpcMessage.empty with badge := some cap.signalBadge })
          ⟨k⟩ executingCore).1,
        .ok (wakeThread (storeSignalWoken st nid ⟨k⟩ (ntfnSuccessor? st ⟨k⟩)
          { IpcMessage.empty with badge := some cap.signalBadge })
          ⟨k⟩ executingCore).2) := by
    simp only [notificationSignalBoundOnCore, hBound, notificationSignalOnCore_eq_impl,
      notificationSignalOnCoreImpl, hN, hHead, hW, ↓reduceIte]
  have hLen := congrArg List.length (notificationSignalBoundOnCore_declassificationAuditLog_eq nid
    cap.signalBadge executingCore st)
  rw [hS] at hLen
  simp only [SystemState.declassificationAuditLog, AuditRing.length_toList] at hLen
  generalize (wakeThread (storeSignalWoken st nid ⟨k⟩ (ntfnSuccessor? st ⟨k⟩)
      { IpcMessage.empty with badge := some cap.signalBadge })
      ⟨k⟩ executingCore) = W at hS hLen ⊢
  have hRec := recordDeclassifiedHops_hopsRecord executingCore signaler
    (embedLegacyLabel (ctx.threadLabelOf signaler)) (embedLegacyLabel (ctx.objectLabelOf nid))
    (embedLegacyLabel (ctx.threadLabelOf ⟨k⟩)) nid ⟨k⟩
    (!securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid))
    (!securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩)) W.1
    (by rw [hLen]; exact hRoom)
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    notificationSignalDeclassifiedCrossCoreDispatch,
    notificationSignalDeclassifiedOnCore, hCur, hN, declassificationActorOf,
    liftLegacyContext_threadDomainOf, liftLegacyContext_objectDomainOf, declassifiedSignalPlan,
    declassifiedSignalHopAuthorization, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    declassifiedSignalReceiver?, hBound, hWait, Option.map_none, hS,
    clearWokenReceiverStash, Architecture.stageWokenDelivery_none]
  by_cases hF1 : securityFlowsTo (ctx.threadLabelOf signaler) (ctx.objectLabelOf nid) = true <;>
  by_cases hF2 : securityFlowsTo (ctx.objectLabelOf nid) (ctx.threadLabelOf ⟨k⟩) = true <;>
  simp only [hF1, hF2, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    declassificationDecision, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    hopAuthorizationOf] at hRec hHop1 hHop2 ⊢
  all_goals simp only [false_or, true_or] at hHop1 hHop2
  all_goals (try simp only [hHop1, hHop2, ↓reduceIte])
  all_goals rw [hRec]

/-- `.declassifySignal` behind its operand check is the specification's arm and
taint step, on every capability the operand resolves to. -/
theorem declassifySignalOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .declassifySignal)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs)
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hTcb : st.getObject? tid.toObjId = some (.tcb tcb))
    (hRoot : st.getObject? tcb.cspaceRoot = some (.cnode rootCn))
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    declassifySignalOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  have hOp := syscallOperandCap?_of_resolved st tid decoded.capAddr tcb rootCn ref hTcb hRoot hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hSid,
    syscallInvokeTyped, syscallResolveCap, hRef,
    declassifySignalTaintStep_eq st tid decoded hSid _ _ _ _ _ (decode_taintWordsAt st tid.toObjId)
      (decode_taintWordsAt st _), hOp]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [declassifySignalOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hType : syscallTargetAccepted .declassifySignal st cap = false
    · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    replace hType : syscallTargetAccepted .declassifySignal st cap = true := by simpa using hType
    by_cases hRight : cap.hasRight (syscallRequiredRight .declassifySignal) = true
    · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]
      have hSpec := dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } cap
        (by rw [hSid]; rfl) hRegs hLen rfl
      rw [hSid] at hSpec
      rw [hSpec]
      split
      · next nid signaler hT hCur =>
        split
        · next hAb =>
          simp only [bne_iff_ne, ne_eq] at hAb
          rw [auditedArmSpec_declassifySignal_absent ctx decoded.capAddr regs tid executingCore
            cap st nid signaler hT hCur (declassifySignalAbsentRefusal_ne_zero hAb)]
        · split
          · next hR =>
            simp only [bne_iff_ne, ne_eq] at hR
            obtain ⟨hP, hEq, hR'⟩ := declassifySignalPresentRefusal_ne_zero hR
            rw [hEq, auditedArmSpec_declassifySignal_planRefused ctx decoded.capAddr regs tid executingCore
              cap st nid signaler hT hCur hP hR']
          · split
            · next hA =>
              have hA' := hA
              simp only [declassifySignalStoredAdmitted, Bool.and_eq_true, decide_eq_true_eq,
                Option.isNone_iff_eq_none] at hA'
              obtain ⟨⟨⟨⟨-, hPresent⟩, hBound⟩, hWait⟩, -⟩ := hA'
              obtain ⟨ntfn, hN⟩ := Option.isSome_iff_exists.mp hPresent
              have hCase : signalTaintCaseOf st (some cap) = .stored := by
                simp only [signalTaintCaseOf, signalTaintCaseOfCap, hT, signalDelivery, hBound, hWait]
              rw [auditedArmSpec_declassifySignal_stored ctx decoded.capAddr regs tid executingCore cap
                st nid signaler hT hCur hA, withTaintWordsAt_eq, withTaintWordsAt_eq, hCase]
              simp only [declassifySignalStoredPerform, TaintWords.mk_fields, operandObjectId,
                capObjectId, hT]
              have hOk := notificationSignalBoundOnCore_stored_ok nid
                cap.signalBadge executingCore st ntfn hN hBound hWait
              rcases hS : notificationSignalBoundOnCore nid cap.signalBadge
                  executingCore st with ⟨st1, e | sgi⟩
              · rw [hS] at hOk; cases hOk
              · rfl
            · split
              · next ntfn hN =>
                split
                · next k hK =>
                  split
                  · next hA =>
                    have hA' := hA
                    simp only [declassifySignalWokenAdmitted, Bool.and_eq_true, decide_eq_true_eq,
                      Option.isNone_iff_eq_none] at hA'
                    obtain ⟨⟨⟨⟨⟨-, hBound⟩, hW⟩, -⟩, -⟩, -⟩ := hA'
                    have hHead : ntfn.waitHead = some ⟨k⟩ := by
                      rw [← Notification.ofOptCode_waitHeadCode, hK]; rfl
                    have hWait : notificationSignalWaiter? st nid = some ⟨k⟩ := by
                      simp only [notificationSignalWaiter?, hN, hHead]
                    have hCase : signalTaintCaseOf st (some cap) = .toWaiter ⟨k⟩ := by
                      simp only [signalTaintCaseOf, signalTaintCaseOfCap, hT, signalDelivery, hBound,
                        hWait]
                    have hNo : st.objects.noResizeDue := by
                      simp only [signalWakesInPlace, Bool.and_eq_true] at hW
                      exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW.1.1.2
                    rw [auditedArmSpec_declassifySignal_woken ctx decoded.capAddr regs tid executingCore
                      cap st nid signaler ntfn k hT hCur hN hK hA, withTaintWordsAt_eq,
                      withTaintWordsAt_eq, hCase, declassifySignalWoken_eq_writes _ _ _ _ _ _ _ _ _ _ _ st hNo,
                      ← optCode_ntfnSuccessor?]
                    simp only [declassifySignalWokenPerform, TaintWords.mk_fields, operandObjectId,
                      capObjectId, hT]
                  · unfold declassifySignalGeneralR
                    rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore
                      cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
                · next hK0 =>
                  split
                  · next k hB =>
                    split
                    · next tcb hTT0 =>
                      have hTT := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTT0
                      split
                      · next hSt =>
                        split
                        · next ep hE0 =>
                          have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE0
                          split
                          · next hA =>
                            have hBT : boundDeliveryTarget? st nid =
                                some (⟨k⟩, ⟨tcb.ipcObjectCode⟩) := by
                              have hBl := (blockedOnQueueSide_ipcState
                                (isReceiveQ := true) (endpointId := ⟨tcb.ipcObjectCode⟩) (t := tcb)
                                (by simp only [blockedOnQueueSide, ↓reduceIte, hSt, beq_self_eq_true,
                                  Bool.and_self])).1 rfl
                              have hTg : st.getTcb? ⟨k⟩ = some tcb :=
                                (SystemState.getTcb?_eq_some_iff _ _ _).mpr hTT
                              simp only [boundDeliveryTarget?, hN, hK0, ↓reduceIte, Notification.boundTCB,
                                hB, SeLe4n.ThreadId.ofOptCode, hTg, hBl]
                            have hCase : signalTaintCaseOf st (some cap) = .toBound ⟨k⟩ := by
                              simp only [signalTaintCaseOf, signalTaintCaseOfCap, hT, signalDelivery, hBT]
                            have hNo : st.objects.noResizeDue := by
                              have hA' := hA
                              simp only [declassifySignalBoundAdmitted, Bool.and_eq_true] at hA'
                              obtain ⟨⟨⟨⟨-, hQ⟩, -⟩, -⟩, -⟩ := hA'
                              unfold queueRemoveInPlace at hQ
                              simp only [Bool.and_eq_true] at hQ
                              obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hFE⟩, -⟩, -⟩, -⟩, -⟩ := hQ
                              exact RobinHood.RHTable.noResizeDue_of_findsInPlace hFE
                            rw [auditedArmSpec_declassifySignal_bound ctx decoded.capAddr regs tid
                              executingCore cap st nid signaler ⟨k⟩ ⟨tcb.ipcObjectCode⟩ ep tcb hT hCur hBT
                              hE hTT hA, withTaintWordsAt_eq, withTaintWordsAt_eq, hCase,
                              declassifySignalBound_eq_writes _ _ _ _ _ _ _ _ _ _ _ _ _ st hNo]
                            simp only [declassifySignalBoundPerform, TaintWords.mk_fields, operandObjectId,
                              capObjectId, hT]
                          all_goals
                            unfold declassifySignalGeneralR
                            rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid
                              executingCore cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
                        all_goals
                          unfold declassifySignalGeneralR
                          rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid
                            executingCore cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
                      all_goals
                        unfold declassifySignalGeneralR
                        rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid
                          executingCore cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
                    all_goals
                      unfold declassifySignalGeneralR
                      rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid
                        executingCore cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
                  all_goals
                    unfold declassifySignalGeneralR
                    rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore
                      cap st with _ | ⟨⟨⟩, post⟩ <;> rfl
              · unfold declassifySignalGeneralR
                rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore cap st
                  with _ | ⟨⟨⟩, post⟩ <;> rfl
      · unfold declassifySignalGeneralR
        rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore cap st
          with _ | ⟨⟨⟩, post⟩ <;> rfl
    · simp only [hIdle, hType, Bool.not_true, Bool.false_eq_true, hRight, ↓reduceIte, Bool.false_eq_true]

/-! ## The routed dispatch -/

/-- A routed declassification or audit call's arm behind the operand check. -/
@[inline] def auditedOperandArmR (ctx : LabelingContext) (sid : SyscallId)
    (regs : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : Option Capability → RefusalCarrying Unit :=
  match sid with
  | .declassify => declassifyOperandArmR ctx regs capAddr tid executingCore
  | .declassifySignal => declassifySignalOperandArmR ctx regs capAddr tid executingCore
  | .auditRead => auditReadOperandArmR ctx regs capAddr tid executingCore
  | .auditDrain => auditDrainOperandArmR ctx regs capAddr tid executingCore
  | _ => fun _ st => .error (.illegalState, st)

/-- `dispatchSyscallChecked` for a routed declassification or audit call, its
operand address, syscall and arguments read from the caller's register file
(`dispatchAuditedCheckedR_eq`).

A specification: the compiled entry runs the arm out of line
(`syscallEntryRoutedK`), so no code is generated for it. -/
noncomputable def dispatchAuditedCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (auditedOperandArmR ctx sid regs capAddr tid executingCore)

theorem dispatchAuditedCheckedR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hRouted : routedAudited decoded.syscallId = true)
    (hRegs : Architecture.SyscallArgDecode.MsgRegsAgreeBelow decoded.msgRegs
      (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) 4)
    (hLen : decoded.msgInfo.length = routedLength regs) :
    dispatchAuditedCheckedR ctx decoded.syscallId decoded.capAddr regs tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    intro h; rw [h] at hRouted; cases hRouted
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref hTcb hRoot hRef
  rcases hs : decoded.syscallId <;> rw [hs] at hRouted <;>
    simp only [routedAudited, Bool.false_eq_true] at hRouted <;> simp only [auditedOperandArmR]
  all_goals first
    | (have h := declassifyOperandArmR_eq ctx decoded regs tid executingCore hs hRegs hLen st tcb rootCn
        ref hTcb hRoot hRef
       rw [hs] at h; exact h)
    | (have h := declassifySignalOperandArmR_eq ctx decoded regs tid executingCore hs hRegs hLen st tcb
        rootCn ref hTcb hRoot hRef
       rw [hs] at h; exact h)
    | (have h := auditReadOperandArmR_eq ctx decoded regs tid executingCore hs hRegs hLen st tcb rootCn
        ref hRef
       rw [hs] at h; exact h)
    | (have h := auditDrainOperandArmR_eq ctx decoded regs tid executingCore hs hRegs hLen st tcb rootCn
        ref hRef
       rw [hs] at h; exact h)

end SeLe4n.Kernel
