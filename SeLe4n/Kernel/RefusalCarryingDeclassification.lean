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
`AuditRing.recordWith`), the snapshot words read off the actor as scalars
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
  { capAddr, msgInfo := ⟨0, 0, 0⟩, syscallId := sid,
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
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
    (hRight : gate.requiredRight = syscallRequiredRight decoded.syscallId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap =
      auditedArmSpec ctx decoded.syscallId decoded.capAddr regs tid executingCore cap := by
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, capRecvSlot, inlineCount, overflowCount⟩
  simp only at hRegs h hRight
  subst hRegs
  unfold auditedArmSpec
  cases sid <;> simp only [routedAudited, Bool.false_eq_true] at h <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, auditedGate,
      hRight, Architecture.SyscallArgDecode.decodeNotificationSignalArgs,
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
(`AuditRing.recordWith`, `DeclassificationEvent.overwrite`), stamped `ts` and
carrying the actor's taint words handed in as scalars.  Out of line, so the
stamp and the words are read before the state is handed over
(`recordEventInPlace_eq`). -/
@[noinline] def recordEventInPlace (c : Concurrency.CoreId) (actorTid : SeLe4n.ThreadId)
    (actorDomain dstDomain : SecurityDomain) (targetId : SeLe4n.ObjId) (ts : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool)
    (st : SystemState) : SystemState :=
  { st with declassificationAudit :=
      st.declassificationAudit.recordWith (·.overwrite actorDomain dstDomain targetId ts c actorTid
        actorDomain a0 a1 a2 a3 a4 a5 a6 a7 ac as) }

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
  rw [AuditRing.recordWith_const _ _ _ (fun e => DeclassificationEvent.overwrite_eq e ..)]
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
over the ring's next slot in place — or the general one
(`declassifyOperandArmR_eq`). -/
@[inline] def declassifyOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
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
          else declassifyGeneralR ctx regs capAddr tid executingCore cap st
        | _, _ => declassifyGeneralR ctx regs capAddr tid executingCore cap st
      else .error (.illegalAuthority, st)

/-- `.declassify` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem declassifyOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .declassify)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
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
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hSid, syscallChecksTargetFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    declassifyTaintStep_eq st tid decoded hSid, hOp]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [declassifyOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hRight : cap.hasRight (syscallRequiredRight .declassify) = true
    · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
      have hSpec := dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } cap
        (by rw [hSid]; rfl) hRegs rfl
      rw [hSid] at hSpec
      rw [hSpec]
      split
      · next targetId actorTid hT hCur =>
        split
        · next hA =>
          rw [auditedArmSpec_declassify_admitted ctx decoded.capAddr regs tid executingCore cap st
            targetId actorTid hT hCur hA, withTaintWordsAt_eq, declassifyPerform_eq]
          simp only [declassifyBypassB, operandObjectId, capObjectId, hT]
        · unfold declassifyGeneralR
          rcases auditedArmSpec ctx .declassify decoded.capAddr regs tid executingCore cap st with
            _ | ⟨⟨⟩, post⟩ <;> rfl
      · unfold declassifyGeneralR
        rcases auditedArmSpec ctx .declassify decoded.capAddr regs tid executingCore cap st with
          _ | ⟨⟨⟩, post⟩ <;> rfl
    · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

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
      .ok ⟨(auditedArgWord regs i).toNat⟩ := by
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

/-- Whether an `.auditDrain` through `cap` is admitted: the target is the trail,
the capability carries the drain's right, the configured clearance validates,
the core runs a subject the clearance dominates, and that subject sees every
entry of the trail (`auditDrainViewComplete`, walked in place). -/
@[inline] def auditDrainAdmitted (ctx : LabelingContext) (st : SystemState)
    (executingCore : Concurrency.CoreId) (cap : Capability) : Bool :=
  match cap.target, ctx.auditMonitorClearance, st.scheduler.currentOnCore executingCore with
  | .auditTrail, some m, some reader =>
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
    (hA : auditDrainAdmitted ctx st executingCore cap = true) :
    auditedArmSpec ctx .auditDrain capAddr regs tid executingCore cap st =
      .ok ((), auditDrainPerform tid (auditedArgWord regs 0).toNat st) := by
  unfold auditDrainAdmitted at hA
  split at hA
  · next m reader hT hM hCur =>
    simp only [Bool.and_eq_true] at hA
    obtain ⟨⟨⟨hRight, hDom⟩, hMon⟩, hAll⟩ := hA
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

/-- **`.auditDrain` behind its operand check**: the resolve-only lookup's
idle-object check (the target is checked before the right,
`syscallChecksTargetFirst`), then the admitted form — the drain and the staged
length written in place — or the general one (`auditDrainOperandArmR_eq`). -/
@[inline] def auditDrainOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
      else if auditDrainAdmitted ctx st executingCore cap then
        .ok ((), auditDrainPerform tid (auditedArgWord regs 0).toNat st)
      else auditGeneralR ctx .auditDrain regs capAddr tid executingCore cap st

/-- What an audit call's operand check leaves to its arm: the specification's
arm and taint step, through the resolve-only lookup, is the arm alone on a
capability that resolves (`auditTaintStep_eq`). -/
theorem auditOperand_spec (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditRead ∨ decoded.syscallId = .auditDrain)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st =
      match SystemState.lookupSlotCap st ref with
      | none => .error (.invalidCapability, st)
      | some cap =>
        if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
        else auditGeneralR ctx decoded.syscallId regs decoded.capAddr tid executingCore cap st := by
  have hFirst : syscallChecksTargetFirst decoded.syscallId = true := by
    rcases hSid with h | h <;> rw [h] <;> rfl
  have hR : routedAudited decoded.syscallId = true := by
    rcases hSid with h | h <;> rw [h] <;> rfl
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hFirst, ↓reduceIte,
    syscallInvokeResolved, syscallResolveCap, hRef, auditTaintStep_eq st tid decoded hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only []
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · simp only [hIdle, Bool.false_eq_true, ↓reduceIte, auditGeneralR]
      rw [dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore _ cap hR
        hRegs rfl]
      rcases auditedArmSpec ctx decoded.syscallId decoded.capAddr regs tid executingCore cap st with
        _ | ⟨⟨⟩, post⟩ <;> rfl

/-- `.auditDrain` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem auditDrainOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditDrain)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    auditDrainOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  rw [auditOperand_spec ctx decoded regs tid executingCore (.inr hSid) hRegs st tcb rootCn ref hRef,
    hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only [auditDrainOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · simp only [hIdle, Bool.false_eq_true, ↓reduceIte]
      split
      · next hA =>
        simp only [auditGeneralR, auditedArmSpec_auditDrain_admitted ctx decoded.capAddr regs tid
          executingCore cap st hA]
      · rfl

/-! ## `.auditRead` -/

/-- `auditFieldChunkCount?` as a code: `0` for `none`, else the count. -/
@[inline] def auditChunkCountN (v : Nat) : Nat :=
  if v < auditFieldChunkModulus then 1
  else if v / auditFieldChunkModulus < auditFieldChunkModulus then 2
  else if v / auditFieldChunkModulus / auditFieldChunkModulus < auditFieldChunkModulus then 3
  else if v / auditFieldChunkModulus / auditFieldChunkModulus / auditFieldChunkModulus <
      auditFieldChunkModulus then 4
  else 0

theorem auditFieldChunkCount?_eq_code (v : Nat) :
    auditFieldChunkCount? v =
      if auditChunkCountN v = 0 then none else some (auditChunkCountN v) := by
  unfold auditFieldChunkCount? auditChunkCountN
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

/-- A field's chunk, read off the `index`th visible entry, as a code: `0` when
the entry is missing or the chunk is out of range, `w + 1` for word `w`. -/
@[inline] def auditFieldWordCode (ctx : LabelingContext) (reader : SecurityDomain)
    (r : AuditRing) (index chunk : Nat) (f : AuditReadField) : Nat :=
  match auditWindowFindVisible ctx reader r 0 r.length index with
  | 0 => 0
  | j + 1 =>
    let v := auditExportedFieldValue true index (r.entry j) f
    let n := auditChunkCountN v
    if n ≠ 0 ∧ chunk < n then auditFieldChunk v chunk + 1 else 0

/-- **A monitor's audit read, walked in place**, as a code: `w + 1` for the word
`w` the specification returns (`auditReadFastCode_spec`), `0` for a read this
form does not cover — the basis, refusal-ledger and causality opcodes, which
take the general form — or one the specification refuses. -/
def auditReadFastCode (ctx : LabelingContext) (reader : SecurityDomain) (r : AuditRing)
    (opcode index chunk : Nat) : Nat :=
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
  | 21 => auditFieldCountCode ctx reader r index .actorSubject
  | 22 => auditFieldCountCode ctx reader r index .actorDomain
  | 23 => auditFieldWordCode ctx reader r index chunk .actorSubject
  | 24 => auditFieldWordCode ctx reader r index chunk .actorDomain
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
    dsimp only
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
    dsimp only
    by_cases hc : auditChunkCountN (auditExportedFieldValue true index
        (st.declassificationAudit.entry j) f) ≠ 0 ∧
      chunk < auditChunkCountN (auditExportedFieldValue true index
        (st.declassificationAudit.entry j) f)
    · obtain ⟨hn, hlt⟩ := hc
      simp only [ne_eq, hn, not_false_eq_true, hlt, and_self, ↓reduceIte,
        Nat.add_right_cancel_iff] at h ⊢
      rw [h]
    · simp only [hc, ↓reduceIte] at h; cases h

/-- A covered read's code is the specification's word, for a reader the
clearance dominates. -/
theorem auditReadFastCode_spec (ctx : LabelingContext) (m reader : SecurityDomain)
    (st : SystemState) (opcode index chunk w : Nat)
    (hMon : DomainFlowPolicy.legacyLattice.canFlow m reader = true)
    (h : auditReadFastCode ctx reader st.declassificationAudit opcode index chunk = w + 1) :
    (match decodeAuditReadOp opcode index chunk with
     | none => (.error .invalidSyscallArgument : Except KernelError Nat)
     | some op => auditReadWord (liftLegacyContext ctx) (some m) reader st op) = .ok w := by
  have hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m) reader = true := hMon
  unfold auditReadFastCode at h
  split at h
  · simp only [decodeAuditReadOp, auditReadWord, hIs, ↓reduceIte, auditLogVisibleTo_length]
    simp only [Nat.add_right_cancel_iff] at h
    rw [h]
  all_goals first
    | (simp only [decodeAuditReadOp]; exact auditFieldCountCode_spec ctx m reader st _ _ _ hIs h)
    | (simp only [decodeAuditReadOp]; exact auditFieldWordCode_spec ctx m reader st _ _ _ _ hIs h)
    | skip
  · simp only [decodeAuditReadOp, auditReadWord, auditLogVisibleTo_getElem?]
    split at h
    · cases h
    · next j hF =>
      dsimp only
      simp only [Nat.add_right_cancel_iff] at h
      rw [h]
  · cases h

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
  auditReadFastCode ctx readerDomain st.declassificationAudit (auditedArgWord regs 0).toNat
    (auditedArgWord regs 1).toNat (auditedArgWord regs 2).toNat

/-- An admitted read is the specification's. -/
theorem auditedArmSpec_auditRead_admitted (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (m : SecurityDomain) (reader : SeLe4n.ThreadId)
    (hT : cap.target = .auditTrail) (hM : ctx.auditMonitorClearance = some m)
    (hCur : st.scheduler.currentOnCore executingCore = some reader)
    (hA : auditReadAdmitted cap m (embedLegacyLabel (ctx.threadLabelOf reader))
      (auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs) = true) :
    auditedArmSpec ctx .auditRead capAddr regs tid executingCore cap st =
      .ok ((), auditReadPerform tid
        (auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs - 1) st) := by
  simp only [auditReadAdmitted, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hA
  obtain ⟨⟨⟨⟨hRight, hDom⟩, hMon⟩, hCode⟩, hFit⟩ := hA
  have hV := validatedAuditMonitorClearance_eq_some ctx m hM hDom
  obtain ⟨w, hw⟩ : ∃ w, auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs =
      w + 1 := Nat.exists_eq_succ_of_ne_zero hCode
  have hSpec := auditReadFastCode_spec ctx m _ st _ _ _ w hMon hw
  rw [hw, Nat.add_sub_cancel] at hFit ⊢
  have hIs : auditMonitorAuthorized (liftLegacyContext ctx) (some m)
      (embedLegacyLabel (ctx.threadLabelOf reader)) = true := hMon
  simp only [auditedArmSpec, dispatchWithCapChecked, dispatchCapabilityOnly, auditedDecoded, hT,
    extractAuditAuthority, auditedGate, hRight, ↓reduceIte,
    Architecture.SyscallArgDecode.decodeAuditReadArgs, auditedDecoded_msgReg regs 0 (by decide),
    auditedDecoded_msgReg regs 1 (by decide), auditedDecoded_msgReg regs 2 (by decide), bind,
    Except.bind, pure, Except.pure, hV]
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

/-- **`.auditRead` behind its operand check**: the resolve-only lookup's
idle-object check, then the admitted form — the word computed by walking the
ring's live window and staged in place — or the general one
(`auditReadOperandArmR_eq`). -/
@[inline] def auditReadOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
      else
        match cap.target, ctx.auditMonitorClearance, st.scheduler.currentOnCore executingCore with
        | .auditTrail, some m, some reader =>
          let code := auditReadCode ctx (embedLegacyLabel (ctx.threadLabelOf reader)) st regs
          if auditReadAdmitted cap m (embedLegacyLabel (ctx.threadLabelOf reader)) code then
            .ok ((), auditReadPerform tid (code - 1) st)
          else auditGeneralR ctx .auditRead regs capAddr tid executingCore cap st
        | _, _, _ => auditGeneralR ctx .auditRead regs capAddr tid executingCore cap st

/-- `.auditRead` behind its operand check is the specification's arm and taint
step, on every capability the operand resolves to. -/
theorem auditReadOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .auditRead)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
    (st : SystemState) (tcb : TCB) (rootCn : CNode) (ref : CSpaceAddr)
    (hRef : resolveCapAddress tcb.cspaceRoot decoded.capAddr rootCn.depth st = .ok ref) :
    auditReadOperandArmR ctx regs decoded.capAddr tid executingCore
        (SystemState.lookupSlotCap st ref) st =
      RefusalCarrying.ofKernel (dispatchCheckedArmThenTaint ctx decoded tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId }
        (syscallTaintPlan st tid decoded) st.declassificationAuditEpoch
        st.declassificationAudit.length st.declassificationTaint) st := by
  rw [auditOperand_spec ctx decoded regs tid executingCore (.inl hSid) hRegs st tcb rootCn ref hRef,
    hSid]
  rcases SystemState.lookupSlotCap st ref with _ | cap
  · rfl
  · simp only [auditReadOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · simp only [hIdle, Bool.false_eq_true, ↓reduceIte]
      split
      · next m reader hT hM hCur =>
        split
        · next hA =>
          simp only [auditGeneralR, auditedArmSpec_auditRead_admitted ctx decoded.capAddr regs tid
            executingCore cap st m reader hT hM hCur hA]
        · rfl
      · rfl

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

/-- **An admitted stored `.declassifySignal`**: the signal stores the badge
(`notificationSignalBoundOnCore`, refusing in the state it was handed), then the
record and the fused taint step over the caller's and the notification's words
captured before the signal.  Out of line, so the words reach it as scalars. -/
@[noinline] def declassifySignalStoredR (c : Concurrency.CoreId) (tid : SeLe4n.ThreadId)
    (actorDomain notifDomain : SecurityDomain) (nid : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hop : Bool) (epoch len : Nat) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool) : RefusalCarrying Unit :=
  fun st =>
    match notificationSignalBoundOnCore nid badge c st with
    | (st1, .ok _) =>
        .ok ((), declassifySignalTaintStep .stored nid tid ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ epoch len
          (declassifySignalRecord c tid actorDomain notifDomain nid hop st1))
    | (st1, .error e) => .error (e, st1)

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

/-- **`.declassifySignal` behind its operand check**: the idle-object check and
the rights gate of the classic lookup, then the admitted stored form or the
general one (`declassifySignalOperandArmR_eq`). -/
@[inline] def declassifySignalOperandArmR (ctx : LabelingContext) (regs : SeLe4n.RegisterFile)
    (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) :
    Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
      if SeLe4n.Kernel.capTargetsReservedIdleObject cap then .error (.invalidCapability, st)
      else if cap.hasRight (syscallRequiredRight .declassifySignal) then
        match cap.target, st.scheduler.currentOnCore executingCore with
        | .object nid, some signaler =>
          if declassifySignalStoredAdmitted ctx st tid signaler nid then
            withTaintWordsAt st tid.toObjId fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
            withTaintWordsAt st nid fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
            declassifySignalStoredR executingCore tid (embedLegacyLabel (ctx.threadLabelOf tid))
              (embedLegacyLabel (ctx.objectLabelOf nid)) nid (SeLe4n.Badge.ofWord (auditedArgWord regs 0))
              (!securityFlowsTo (ctx.threadLabelOf tid) (ctx.objectLabelOf nid))
              st.declassificationAudit.epoch st.declassificationAudit.length a0 a1 a2 a3 a4 a5 a6 a7 ac as b0 b1 b2 b3 b4 b5 b6 b7 bc bs st
          else declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
        | _, _ => declassifySignalGeneralR ctx regs capAddr tid executingCore cap st
      else .error (.illegalAuthority, st)

/-- An admitted stored `.declassifySignal` is the specification's: the signal,
then the record its one hop owes when it is a downgrade. -/
theorem auditedArmSpec_declassifySignal_stored (ctx : LabelingContext) (capAddr : SeLe4n.CPtr)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) (st : SystemState) (nid : SeLe4n.ObjId) (signaler : SeLe4n.ThreadId)
    (hT : cap.target = .object nid)
    (hCur : st.scheduler.currentOnCore executingCore = some signaler)
    (hA : declassifySignalStoredAdmitted ctx st tid signaler nid = true) :
    auditedArmSpec ctx .declassifySignal capAddr regs tid executingCore cap st =
      match notificationSignalBoundOnCore nid (SeLe4n.Badge.ofWord (auditedArgWord regs 0))
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
    Architecture.SyscallArgDecode.decodeNotificationSignalArgs,
    auditedDecoded_msgReg regs 0 (by decide), bind, Except.bind, pure, Except.pure,
    ← SeLe4n.Badge.ofWord_eq_ofNatMasked, notificationSignalDeclassifiedCrossCoreDispatch,
    notificationSignalDeclassifiedOnCore, hCur, hN, declassificationActorOf,
    liftLegacyContext_threadDomainOf, liftLegacyContext_objectDomainOf, declassifiedSignalPlan,
    declassifiedSignalHopAuthorization, liftLegacyContext_policy, legacyLattice_canFlow_embed,
    declassifiedSignalReceiver?, hBound, hWait, Option.map_none]
  have hLen := congrArg List.length (notificationSignalBoundOnCore_declassificationAuditLog_eq nid
    (SeLe4n.Badge.ofWord (auditedArgWord regs 0)) executingCore st)
  simp only [SystemState.declassificationAuditLog, AuditRing.length_toList] at hLen
  rcases hS : notificationSignalBoundOnCore nid (SeLe4n.Badge.ofWord (auditedArgWord regs 0))
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

/-- `.declassifySignal` behind its operand check is the specification's arm and
taint step, on every capability the operand resolves to. -/
theorem declassifySignalOperandArmR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hSid : decoded.syscallId = .declassifySignal)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs))
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
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hSid, syscallChecksTargetFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    declassifySignalTaintStep_eq st tid decoded hSid _ _ _ _ _ (decode_taintWordsAt st tid.toObjId)
      (decode_taintWordsAt st _), hOp]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [declassifySignalOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedIdleObject cap = true
    · simp only [hIdle, ↓reduceIte]
    by_cases hRight : cap.hasRight (syscallRequiredRight .declassifySignal) = true
    · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
      have hSpec := dispatchWithCapChecked_eq_auditedArmSpec ctx decoded regs tid executingCore
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr,
          capDepth := rootCn.depth, requiredRight := syscallRequiredRight decoded.syscallId } cap
        (by rw [hSid]; rfl) hRegs rfl
      rw [hSid] at hSpec
      rw [hSpec]
      split
      · next nid signaler hT hCur =>
        split
        · next hA =>
          have hA' := hA
          simp only [declassifySignalStoredAdmitted, Bool.and_eq_true, decide_eq_true_eq,
            Option.isNone_iff_eq_none] at hA'
          obtain ⟨⟨⟨⟨-, -⟩, hBound⟩, hWait⟩, -⟩ := hA'
          have hCase : signalTaintCaseOf st (some cap) = .stored := by
            simp only [signalTaintCaseOf, signalTaintCaseOfCap, hT, signalDelivery, hBound, hWait]
          rw [auditedArmSpec_declassifySignal_stored ctx decoded.capAddr regs tid executingCore cap
            st nid signaler hT hCur hA, withTaintWordsAt_eq, withTaintWordsAt_eq, hCase]
          simp only [declassifySignalStoredR, TaintWords.mk_fields, operandObjectId, capObjectId, hT]
          rcases hS : notificationSignalBoundOnCore nid (SeLe4n.Badge.ofWord (auditedArgWord regs 0))
              executingCore st with ⟨st1, e | sgi⟩
          · have h1 := notificationSignalBoundOnCore_error_state nid
              (SeLe4n.Badge.ofWord (auditedArgWord regs 0)) executingCore st e (by rw [hS])
            rw [hS] at h1
            simp only at h1
            subst h1
            rfl
          · rfl
        · unfold declassifySignalGeneralR
          rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore cap st
            with _ | ⟨⟨⟩, post⟩ <;> rfl
      · unfold declassifySignalGeneralR
        rcases auditedArmSpec ctx .declassifySignal decoded.capAddr regs tid executingCore cap st
          with _ | ⟨⟨⟩, post⟩ <;> rfl
    · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

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
(`dispatchAuditedCheckedR_eq`). -/
@[inline] def dispatchAuditedCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore
    (auditedOperandArmR ctx sid regs capAddr tid executingCore)

theorem dispatchAuditedCheckedR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (regs : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hRouted : routedAudited decoded.syscallId = true)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg regs)) :
    dispatchAuditedCheckedR ctx decoded.syscallId decoded.capAddr regs tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    intro h; rw [h] at hRouted; cases hRouted
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref hTcb hRoot hRef
  rcases hs : decoded.syscallId <;> rw [hs] at hRouted <;>
    simp only [routedAudited, Bool.false_eq_true] at hRouted <;> simp only [auditedOperandArmR]
  all_goals first
    | (have h := declassifyOperandArmR_eq ctx decoded regs tid executingCore hs hRegs st tcb rootCn
        ref hTcb hRoot hRef
       rw [hs] at h; exact h)
    | (have h := declassifySignalOperandArmR_eq ctx decoded regs tid executingCore hs hRegs st tcb
        rootCn ref hTcb hRoot hRef
       rw [hs] at h; exact h)
    | (have h := auditReadOperandArmR_eq ctx decoded regs tid executingCore hs hRegs st tcb rootCn
        ref hRef
       rw [hs] at h; exact h)
    | (have h := auditDrainOperandArmR_eq ctx decoded regs tid executingCore hs hRegs st tcb rootCn
        ref hRef
       rw [hs] at h; exact h)

end SeLe4n.Kernel
