-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.TransferCommute

/-!
# seL4's `transferCaps`, in place

The specification's transfer (`receiveTransferCaps`) resolves the sender's
extra capability addresses into an array, collects the capabilities they name,
reads the receiver's side into an option of a pair, and runs the loop
(`ipcUnwrapCapsLoop`) over the array, pushing each result into a summary.
Every one of those is a heap cell.  The transfer here runs the same steps on
words: each address is read and resolved in place (`extraCapRefK`), the
capabilities are read from their slots once, before any write, as the
specification reads them, and held as the slots' own records; the receive slot
is read in place (`receiveSlotK`); and the loop (`capStepsApply`) writes each
badge and the one install straight into the state, its report
(`capStepsInfo`) counted in two numbers.

Every decision the loop makes reads the objects alone, and the badge writes
before the install keep them, so the report is read off the state the
transfer starts from (`capStepsInfo_eq`) and the arm computes it before the
writes, which then consume the state they are handed.  The whole is the
specification's transfer (`capTransferK_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Architecture.IpcBufferRead

/-! ### Reading the request and the receive slot in place -/

/-- **The sender's extra capability address `i`, read in place**:
`senderExtraCapAddr?` with its answer handed to a continuation. -/
@[inline] def senderCapAddrK {α : Type} (st : SystemState) (stcb : TCB) (i : Nat)
    (kNone : Unit → α) (k : SeLe4n.CPtr → α) : α :=
  match ipcBufferWordPAddr? st stcb (ipcBufferCapsOrBadgesWord i) false with
  | none => kNone ()
  | some pa => k (SeLe4n.CPtr.ofWord (userWordAt st.machine pa))

theorem senderCapAddrK_eq {α : Type} (st : SystemState) (stcb : TCB) (i : Nat)
    (kNone : Unit → α) (k : SeLe4n.CPtr → α) :
    senderCapAddrK st stcb i kNone k =
      match senderExtraCapAddr? st stcb i with
      | none => kNone ()
      | some a => k a := by
  unfold senderCapAddrK senderExtraCapAddr?
  cases ipcBufferWordPAddr? st stcb (ipcBufferCapsOrBadgesWord i) false <;> rfl

/-- **The slot the sender's extra capability address `i` names**, read and
resolved in place in the sender's CSpace `root` of depth `depth`. -/
@[inline] def extraCapRefK {α : Type} (st : SystemState) (stcb : TCB) (root : SeLe4n.ObjId)
    (depth i : Nat) (kFail : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  senderCapAddrK st stcb i kFail fun a =>
    resolveCapAddressKUnrolled root a depth st (fun _ => kFail ()) k

theorem extraCapRefK_eq {α : Type} (st : SystemState) (stcb : TCB) (root : SeLe4n.ObjId)
    (depth i : Nat) (kFail : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) :
    extraCapRefK st stcb root depth i kFail k =
      match senderExtraCapAddr? st stcb i with
      | none => kFail ()
      | some a =>
        match resolveCapAddress root a depth st with
        | .error _ => kFail ()
        | .ok ref => k ref.cnode ref.slot := by
  unfold extraCapRefK
  rw [senderCapAddrK_eq]
  cases senderExtraCapAddr? st stcb i with
  | none => rfl
  | some a =>
    simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
    cases resolveCapAddress root a depth st <;> rfl

/-- **The receive slot a receive path names, in place** (`receivePathSlot?`). -/
@[inline] def receivePathSlotK {α : Type} (st : SystemState) (tcb : TCB)
    (cnodeWord indexWord depthWord : UInt64)
    (kNone : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match st.getCNode? tcb.cspaceRoot with
  | none => kNone ()
  | some rootCn =>
    resolveCapAddressKUnrolled tcb.cspaceRoot (SeLe4n.CPtr.ofWord cnodeWord) rootCn.depth st
      (fun _ => kNone ())
      (fun cn sl =>
        match SystemState.lookupSlotCap st ⟨cn, sl⟩ with
        | none => kNone ()
        | some cap =>
          match cap.target with
          | .object cnodeId =>
            match st.getCNode? cnodeId with
            | none => kNone ()
            | some _ =>
              if depthWord == 0 || (64 : UInt64) < depthWord then kNone () else
              resolveCapAddressKUnrolled cnodeId (SeLe4n.CPtr.ofWord indexWord) depthWord.toNat st
                (fun _ => kNone ())
                (fun cn' sl' =>
                  match SystemState.lookupSlotCap st ⟨cn', sl'⟩ with
                  | none => k cn' sl'
                  | some _ => kNone ())
          | _ => kNone ())

theorem receivePathSlotK_eq {α : Type} (st : SystemState) (tcb : TCB) (c i d : UInt64)
    (kNone : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) :
    receivePathSlotK st tcb c i d kNone k =
      match receivePathSlot? st tcb c i d with
      | none => kNone ()
      | some dst => k dst.cnode dst.slot := by
  unfold receivePathSlotK receivePathSlot?
  cases st.getCNode? tcb.cspaceRoot with
  | none => rfl
  | some rootCn =>
    simp only [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
    cases resolveCapAddress tcb.cspaceRoot (SeLe4n.CPtr.ofWord c) rootCn.depth st with
    | error _ => rfl
    | ok ref =>
      simp only []
      cases SystemState.lookupSlotCap st ⟨ref.cnode, ref.slot⟩ with
      | none => rfl
      | some cap =>
        simp only []
        cases cap.target with
        | object cnodeId =>
          simp only []
          cases st.getCNode? cnodeId with
          | none => rfl
          | some _ =>
            simp only [receiveDepthRefused_eq]
            by_cases hd : d.toNat = 0 ∨ 64 < d.toNat
            · simp only [hd, decide_true, ↓reduceIte]
            · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte]
              cases resolveCapAddress cnodeId (SeLe4n.CPtr.ofWord i) d.toNat st with
              | error _ => rfl
              | ok ref' =>
                simp only []
                cases SystemState.lookupSlotCap st ⟨ref'.cnode, ref'.slot⟩ <;> rfl
        | _ => rfl

/-- **The receiver's receive slot, in place** (`receiveSlot?`). -/
@[inline] def receiveSlotK {α : Type} (st : SystemState) (tcb : TCB)
    (kNone : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  match receiverBufferWord? st tcb ipcBufferReceiveCNodeWord,
      receiverBufferWord? st tcb ipcBufferReceiveIndexWord,
      receiverBufferWord? st tcb ipcBufferReceiveDepthWord with
  | some c, some i, some d => receivePathSlotK st tcb c i d kNone k
  | _, _, _ => kNone ()

theorem receiveSlotK_eq {α : Type} (st : SystemState) (tcb : TCB)
    (kNone : Unit → α) (k : SeLe4n.ObjId → SeLe4n.Slot → α) :
    receiveSlotK st tcb kNone k =
      match receiveSlot? st tcb with
      | none => kNone ()
      | some dst => k dst.cnode dst.slot := by
  unfold receiveSlotK receiveSlot?
  cases receiverBufferWord? st tcb ipcBufferReceiveCNodeWord <;>
    cases receiverBufferWord? st tcb ipcBufferReceiveIndexWord <;>
    cases receiverBufferWord? st tcb ipcBufferReceiveDepthWord <;>
    first | rfl | exact receivePathSlotK_eq _ _ _ _ _ _ _

/-! ### One capability's install, in place -/

/-- **The checks `ipcTransferSingleCap` makes**, read in place: the source slot
holds a capability, the derivation rule admits it, and the receive slot is an
empty, addressable slot of a CNode. -/
@[inline] def transferInstallAdmitted (scn : SeLe4n.ObjId) (ssl : SeLe4n.Slot)
    (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot) (cap : Capability) (st : SystemState) : Bool :=
  (SystemState.lookupSlotCap st ⟨scn, ssl⟩).isSome && !untypedDeriveRefused st ⟨scn, ssl⟩ cap &&
    cspaceDstAdmitted ⟨dcn, dsl⟩ st

/-- **`ipcTransferSingleCap`'s writes, in place**: the capability's fields,
with no mapping record, written straight into the receive slot's own record
(`CNode.insertFields`, as `cspaceCopyPerformImpl` writes a copy), the transfer's
derivation edge, and an untyped source set full. -/
@[inline] def transferInstallPerform (scn : SeLe4n.ObjId) (ssl : SeLe4n.Slot)
    (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot) (cap : Capability) (st : SystemState) :
    SystemState :=
  untypedSourceSetFull
    ((st.storeCNodeWith dcn
      (·.insertFields dsl cap.target cap.rights cap.badgeWord cap.badged cap.freeIndex)).cdtAddChild
      ⟨scn, ssl⟩ ⟨dcn, dsl⟩ .ipcTransfer) ⟨scn, ssl⟩ cap

/-- **One install is its checks and its writes**: where the checks pass, the
specification's install succeeds with exactly the in-place writes; where they
fail it refuses. -/
theorem ipcTransferSingleCap_eq_inPlace {β : Type} (cap : Capability) (src dst : SlotRef)
    (st : SystemState) (kErr : β) (kOk : SystemState → β) :
    (match ipcTransferSingleCap cap src dst st with
      | .error _ => kErr
      | .ok ((), st') => kOk st') =
      if transferInstallAdmitted src.cnode src.slot dst.cnode dst.slot cap st then
        kOk (transferInstallPerform src.cnode src.slot dst.cnode dst.slot cap st)
      else kErr := by
  unfold transferInstallAdmitted
  cases hD : cspaceDstAdmitted ⟨dst.cnode, dst.slot⟩ st with
  | false =>
    simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    cases hT : ipcTransferSingleCap cap src dst st with
    | error _ => rfl
    | ok p =>
      obtain ⟨⟨⟩, st'⟩ := p
      obtain ⟨_, st2, -, -, -, hIns, -⟩ := ipcTransferSingleCap_ok_cases hT
      obtain ⟨cn, hC, hA, hE, -⟩ := cspaceInsertSlot_ok_decompose _ _ _ _ hIns
      unfold cspaceDstAdmitted at hD
      simp only [hC, hA, hE, Option.isNone_none, Bool.and_self, Bool.true_eq_false] at hD
  | true =>
    have hIns := cspaceInsertSlot_of_admitted hD cap.withoutMapping
    have hC : ∃ cn, st.getCNode? dst.cnode = some cn := by
      unfold cspaceDstAdmitted at hD
      split at hD
      · next cn h => exact ⟨cn, h⟩
      · cases hD
    obtain ⟨cn, hC⟩ := hC
    simp only [Bool.and_true]
    unfold ipcTransferSingleCap cdtNodeIsRevocable
    simp only [hC]
    cases hL : (SystemState.lookupSlotCap st src).isSome with
    | false => rfl
    | true =>
      simp only [Bool.true_and]
      cases hU : untypedDeriveRefused st src cap with
      | true => rfl
      | false =>
        simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        rw [hIns]
        unfold transferInstallPerform
        simp only [CNode.insertFields_eq_insert]
        rfl

theorem ipcTransferSingleCap_of_admitted {cap : Capability} {src dst : SlotRef}
    {st : SystemState}
    (h : transferInstallAdmitted src.cnode src.slot dst.cnode dst.slot cap st = true) :
    ipcTransferSingleCap cap src dst st =
      .ok ((), transferInstallPerform src.cnode src.slot dst.cnode dst.slot cap st) := by
  have := ipcTransferSingleCap_eq_inPlace (β := Option SystemState) cap src dst st none some
  rw [if_pos h] at this
  revert this
  cases ipcTransferSingleCap cap src dst st with
  | error _ => intro h; cases h
  | ok p => obtain ⟨⟨⟩, s⟩ := p; intro h; cases h; rfl

theorem ipcTransferSingleCap_of_refused {cap : Capability} {src dst : SlotRef}
    {st : SystemState}
    (h : transferInstallAdmitted src.cnode src.slot dst.cnode dst.slot cap st = false) :
    ∃ e, ipcTransferSingleCap cap src dst st = .error e := by
  have := ipcTransferSingleCap_eq_inPlace (β := Option SystemState) cap src dst st none some
  rw [if_neg (by simp [h])] at this
  revert this
  cases ipcTransferSingleCap cap src dst st with
  | error e => intro _; exact ⟨e, rfl⟩
  | ok p => obtain ⟨⟨⟩, s⟩ := p; intro h; cases h

/-! ### The transfer loop, in place -/

/-- One of three, by index (the third for every index past the second). -/
@[inline] def pick3 {β : Type} (i : Nat) (a b c : β) : β :=
  match i with
  | 0 => a
  | 1 => b
  | _ => c

/-- The badge an unwrapped capability delivers (`cap.badge.getD Badge.zero`). -/
@[inline] def capBadgeOrZero (cap : Capability) : SeLe4n.Badge :=
  if cap.badged then cap.badgeWord else SeLe4n.Badge.zero

theorem capBadgeOrZero_eq (cap : Capability) :
    capBadgeOrZero cap = cap.badge.getD SeLe4n.Badge.zero := by
  unfold capBadgeOrZero Capability.badge
  cases cap.badged <;> rfl

/-- **seL4's `transferCapsToSlots` loop, in place**, over the capabilities
`c0`, `c1`, `c2` read from the slots `(r0c, r0s)`, `(r1c, r1s)`, `(r2c, r2s)`:
from index `idx`, a capability to the endpoint unwraps (its badge to the
receiver's buffer); any other is installed in the receive slot `(dcn, dsl)` if
it is still free and the install's checks pass, and the slot is used up; or
the loop stops. -/
def capStepsApply (ep : SeLe4n.ObjId) (rt : TCB) (c0 c1 c2 : Capability)
    (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId) (r1s : SeLe4n.Slot)
    (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot) :
    (idx fuel : Nat) → (free : Bool) → SystemState → SystemState
  | _, 0, _, st => st
  | idx, fuel + 1, free, st =>
    let cap := pick3 idx c0 c1 c2
    if capUnwrapsAt cap (some ep) then
      capStepsApply ep rt c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl (idx + 1) fuel free
        (recordUnwrappedBadge st rt idx (capBadgeOrZero cap))
    else if free && transferInstallAdmitted (pick3 idx r0c r1c r2c) (pick3 idx r0s r1s r2s)
        dcn dsl cap st then
      capStepsApply ep rt c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl (idx + 1) fuel false
        (transferInstallPerform (pick3 idx r0c r1c r2c) (pick3 idx r0s r1s r2s) dcn dsl cap st)
    else st

/-- **The loop's report, read off the state it starts from**: the count of the
capabilities it processes plus four times the mask of those it unwraps
(`CapTransferSummary.capInfo`), from the counts `n` and `m` so far.  The
install's checks read objects only, which the badge writes before it keep. -/
def capStepsInfo (ep : SeLe4n.ObjId) (c0 c1 c2 : Capability)
    (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId) (r1s : SeLe4n.Slot)
    (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot)
    (st : SystemState) : (idx fuel : Nat) → (free : Bool) → (n m : Nat) → Nat
  | _, 0, _, n, m => n + 4 * m
  | idx, fuel + 1, free, n, m =>
    let cap := pick3 idx c0 c1 c2
    if capUnwrapsAt cap (some ep) then
      capStepsInfo ep c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl st (idx + 1) fuel free (n + 1)
        (m + 2 ^ n)
    else if free && transferInstallAdmitted (pick3 idx r0c r1c r2c) (pick3 idx r0s r1s r2s)
        dcn dsl cap st then
      capStepsInfo ep c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl st (idx + 1) fuel false (n + 1) m
    else n + 4 * m

/-- The transfer's capability `j` of the three. -/
@[inline] def transferCapAt (c0 c1 c2 : Capability)
    (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId) (r1s : SeLe4n.Slot)
    (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (j : Nat) : TransferCap :=
  TransferCap.fromSlot (pick3 j c0 c1 c2) ⟨pick3 j r0c r1c r2c, pick3 j r0s r1s r2s⟩

/-- The report's counts over the results so far. -/
def capInfoCounts (acc : Array CapTransferResult) : Nat × Nat :=
  acc.foldl CapTransferSummary.capInfoStep (0, 0)

/-- `Z` is `Zs` with only its physical-write ledger written. -/
def LedgerOnly (Zs Z : SystemState) : Prop :=
  ∃ (L : SeLe4n.Kernel.Architecture.PhysicalWriteLedger) (D : Bool),
    Z = { Zs with physicalWrites := L, physicalWritesDrained := D }

theorem LedgerOnly.refl (Z : SystemState) : LedgerOnly Z Z :=
  ⟨Z.physicalWrites, Z.physicalWritesDrained, rfl⟩

theorem LedgerOnly.badge {Zs Z : SystemState} (h : LedgerOnly Zs Z) (rt : TCB) (i : Nat)
    (b : SeLe4n.Badge) : LedgerOnly Zs (recordUnwrappedBadge Z rt i b) := by
  obtain ⟨L, D, rfl⟩ := h
  unfold recordUnwrappedBadge
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨L, D, rfl⟩

theorem transferInstallAdmitted_ledgerOnly {Zs Z : SystemState} (h : LedgerOnly Zs Z)
    (scn : SeLe4n.ObjId) (ssl : SeLe4n.Slot) (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot)
    (cap : Capability) :
    transferInstallAdmitted scn ssl dcn dsl cap Z = transferInstallAdmitted scn ssl dcn dsl cap Zs := by
  obtain ⟨L, D, rfl⟩ := h
  rfl

/-- **The specification's loop is the loop in place**, over capabilities the
array holds at the indices the loop visits: the same state, and a summary whose
report is the in-place report read off the state the loop starts from. -/
theorem ipcUnwrapCapsLoop_eq_capSteps (ep : SeLe4n.ObjId) (rt : TCB) (c0 c1 c2 : Capability)
    (r0c : SeLe4n.ObjId) (r0s : SeLe4n.Slot) (r1c : SeLe4n.ObjId) (r1s : SeLe4n.Slot)
    (r2c : SeLe4n.ObjId) (r2s : SeLe4n.Slot) (dcn : SeLe4n.ObjId) (dsl : SeLe4n.Slot)
    (caps : Array TransferCap) (Zs : SystemState) :
    ∀ (fuel idx : Nat) (free : Bool) (acc : Array CapTransferResult) (Z : SystemState),
      (∀ j, j < fuel → caps[idx + j]? = some (transferCapAt c0 c1 c2 r0c r0s r1c r1s r2c r2s (idx + j))) →
      (free = true → LedgerOnly Zs Z) →
      ∃ s : CapTransferSummary,
        ipcUnwrapCapsLoop caps (some ep) rt idx (if free then some ⟨dcn, dsl⟩ else none) acc fuel Z =
          .ok (s, capStepsApply ep rt c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl idx fuel free Z) ∧
        s.capInfo = capStepsInfo ep c0 c1 c2 r0c r0s r1c r1s r2c r2s dcn dsl Zs idx fuel free
          (capInfoCounts acc).1 (capInfoCounts acc).2
  | 0, idx, free, acc, Z, _, _ => ⟨{ results := acc }, rfl, rfl⟩
  | fuel + 1, idx, free, acc, Z, hC, hL => by
    have h0 := hC 0 (Nat.succ_pos _)
    rw [Nat.add_zero] at h0
    have hC' : ∀ j, j < fuel → caps[idx + 1 + j]? =
        some (transferCapAt c0 c1 c2 r0c r0s r1c r1s r2c r2s (idx + 1 + j)) := by
      intro j hj
      have := hC (j + 1) (Nat.succ_lt_succ hj)
      rwa [show idx + (j + 1) = idx + 1 + j by omega] at this
    simp only [ipcUnwrapCapsLoop, h0, capStepsApply, capStepsInfo]
    unfold transferCapAt TransferCap.fromSlot
    dsimp only
    split
    · next hU =>
      have hCounts : capInfoCounts (acc.push (.unwrapped ((pick3 idx c0 c1 c2).badge.getD
          SeLe4n.Badge.zero))) = ((capInfoCounts acc).1 + 1,
            (capInfoCounts acc).2 + 2 ^ (capInfoCounts acc).1) := by
        unfold capInfoCounts; rw [Array.foldl_push]; rfl
      obtain ⟨s, hs, hi⟩ := ipcUnwrapCapsLoop_eq_capSteps ep rt c0 c1 c2 r0c r0s r1c r1s r2c r2s
        dcn dsl caps Zs fuel (idx + 1) free _ _ hC'
        (fun hf => (hL hf).badge rt idx _)
      refine ⟨s, ?_, ?_⟩
      · rw [capBadgeOrZero_eq]; exact hs
      · rw [hi, hCounts]
    · next hU =>
      cases free with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        exact ⟨{ results := acc }, rfl, rfl⟩
      | true =>
        simp only [↓reduceIte, Bool.true_and]
        rw [transferInstallAdmitted_ledgerOnly (hL rfl)]
        cases hA : transferInstallAdmitted (pick3 idx r0c r1c r2c) (pick3 idx r0s r1s r2s) dcn dsl
            (pick3 idx c0 c1 c2) Zs with
        | true =>
          have hA' := (transferInstallAdmitted_ledgerOnly (hL rfl) _ _ _ _ _).trans hA
          rw [ipcTransferSingleCap_of_admitted (src := ⟨pick3 idx r0c r1c r2c, pick3 idx r0s r1s r2s⟩) (dst := ⟨dcn, dsl⟩) hA']
          simp only [↓reduceIte]
          have hCounts : capInfoCounts (acc.push (.installed dcn dsl)) =
              ((capInfoCounts acc).1 + 1, (capInfoCounts acc).2) := by
            unfold capInfoCounts; rw [Array.foldl_push]; rfl
          obtain ⟨s, hs, hi⟩ := ipcUnwrapCapsLoop_eq_capSteps ep rt c0 c1 c2 r0c r0s r1c r1s
            r2c r2s dcn dsl caps Zs fuel (idx + 1) false _ _ hC' (fun hf => by cases hf)
          refine ⟨s, ?_, ?_⟩
          · exact hs
          · rw [hi, hCounts]
        | false =>
          have hA' := (transferInstallAdmitted_ledgerOnly (hL rfl) _ _ _ _ _).trans hA
          obtain ⟨e, he⟩ := ipcTransferSingleCap_of_refused (src := ⟨pick3 idx r0c r1c r2c, pick3 idx r0s r1s r2s⟩) (dst := ⟨dcn, dsl⟩) hA'
          rw [he]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨{ results := acc }, rfl, rfl⟩

/-! ### The whole transfer, in place -/

/-- **The capabilities the slots hold, read once, up to the first empty one**
(`extraCapsFromSlots`): how many (`n`) and the slots' own records, the last
one repeated past `n` (never read there). -/
@[inline] def transferCapsReadK {α : Type} (st : SystemState) (count : Nat)
    (a0 : SeLe4n.ObjId) (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId) (b1 : SeLe4n.Slot)
    (a2 : SeLe4n.ObjId) (b2 : SeLe4n.Slot)
    (k : Nat → Capability → Capability → Capability → α) : α :=
  match SystemState.lookupSlotCap st ⟨a0, b0⟩ with
  | none => k 0 default default default
  | some x0 =>
    if count ≤ 1 then k 1 x0 x0 x0 else
    match SystemState.lookupSlotCap st ⟨a1, b1⟩ with
    | none => k 1 x0 x0 x0
    | some x1 =>
      if count ≤ 2 then k 2 x0 x1 x1 else
      match SystemState.lookupSlotCap st ⟨a2, b2⟩ with
      | none => k 2 x0 x1 x1
      | some x2 => k 3 x0 x1 x2

/-- **The slots the sender's addresses name, all or nothing**
(`senderExtraCapAddrs`, then `resolveExtraCaps`'s lookup): each of the first
`count` addresses (at most three) read from the sender's buffer and resolved in
its CSpace; any that does not read or resolve fails the whole request. -/
@[inline] def transferRefsK {α : Type} (st : SystemState) (stcb : TCB) (root : SeLe4n.ObjId)
    (depth count : Nat) (kFail : Unit → α)
    (k : SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    α :=
  if count = 0 then kFail () else
  extraCapRefK st stcb root depth 0 kFail fun a0 b0 =>
  if count ≤ 1 then k a0 b0 a0 b0 a0 b0 else
  extraCapRefK st stcb root depth 1 kFail fun a1 b1 =>
  if count ≤ 2 then k a0 b0 a1 b1 a1 b1 else
  extraCapRefK st stcb root depth 2 kFail fun a2 b2 => k a0 b0 a1 b1 a2 b2

/-- **seL4's `transferCaps`, in place**, for a sender `stcb` naming `count`
extra capabilities and a receiver `rt`, of a message sent on `ep`: everything
the loop reads, handed to `kRun` as words and the slots' own records — whether
the receive slot is free and where it is, how many capabilities there are, the
capabilities and the slots they were read from.  A request that transfers
nothing hands over no capability. -/
@[inline] def capTransferK {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (stcb : TCB)
    (count : Nat) (rt : TCB)
    (kRun : Bool → SeLe4n.ObjId → SeLe4n.Slot → Nat → Capability → Capability → Capability →
      SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → SeLe4n.ObjId → SeLe4n.Slot → α) :
    α :=
  if receiverHasBuffer st rt then
    match st.getCNode? stcb.cspaceRoot with
    | none => kRun false ep default 0 default default default ep default ep default ep default
    | some rootCn =>
      transferRefsK st stcb stcb.cspaceRoot rootCn.depth count
        (fun _ => kRun false ep default 0 default default default ep default ep default ep default)
        fun a0 b0 a1 b1 a2 b2 =>
          transferCapsReadK st count a0 b0 a1 b1 a2 b2 fun n x0 x1 x2 =>
            receiveSlotK st rt
              (fun _ => kRun false ep default n x0 x1 x2 a0 b0 a1 b1 a2 b2)
              (fun dcn dsl => kRun true dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2)
  else kRun false ep default 0 default default default ep default ep default ep default

/-- The request a sender's frame makes once it decodes (`senderFrameCapRequest`
past its decode), for `count` extra capabilities. -/
def frameCapRequestOf (st : SystemState) (stcb : TCB) (count : Nat) :
    Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat) :=
  let addrs := senderExtraCapAddrs st stcb count
  if addrs.isEmpty then none else
  match st.getCNode? stcb.cspaceRoot with
  | some rootCn => some (stcb.cspaceRoot, addrs, rootCn.depth)
  | none => none

/-- The receiver's side as the specification reads it (`receiverCapTarget?`
past the receiver's lookup). -/
def capTargetOf (st : SystemState) (rt : TCB) : Option (TCB × Option CSpaceAddr) :=
  if receiverHasBuffer st rt then some (rt, receiveSlot? st rt) else none

/-- **The specification's transfer over capabilities read into the three**:
its loop from the start is the loop in place, its summary's report the
in-place report. -/
theorem ipcUnwrapCaps_eq_run {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (caps : Array TransferCap) (n : Nat)
    (x0 x1 x2 : Capability) (a0 : SeLe4n.ObjId) (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId)
    (b1 : SeLe4n.Slot) (a2 : SeLe4n.ObjId) (b2 : SeLe4n.Slot)
    (hSize : caps.size = n)
    (hAt : ∀ j, j < n → caps[j]? = some (transferCapAt x0 x1 x2 a0 b0 a1 b1 a2 b2 j)) :
    receiveSlotK st rt
        (fun _ => K (capStepsInfo ep x0 x1 x2 a0 b0 a1 b1 a2 b2 ep default st 0 n false 0 0)
          (capStepsApply ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 ep default 0 n false st))
        (fun dcn dsl => K (capStepsInfo ep x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl st 0 n true 0 0)
          (capStepsApply ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n true st)) =
      match ipcUnwrapCaps caps (some ep) rt (receiveSlot? st rt) st with
      | .ok (s, st') => K s.capInfo st'
      | .error _ => K 0 st := by
  have hAt' : ∀ j, j < n → caps[0 + j]? = some (transferCapAt x0 x1 x2 a0 b0 a1 b1 a2 b2 (0 + j)) := by
    intro j hj; rw [Nat.zero_add]; exact hAt j hj
  rw [receiveSlotK_eq]
  unfold ipcUnwrapCaps
  rw [hSize]
  cases receiveSlot? st rt with
  | none =>
    obtain ⟨s, hs, hi⟩ := ipcUnwrapCapsLoop_eq_capSteps ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 ep
      default caps st n 0 false #[] st hAt' (fun h => by cases h)
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    simp only [hs, hi]
    rfl
  | some d =>
    obtain ⟨s, hs, hi⟩ := ipcUnwrapCapsLoop_eq_capSteps ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 d.cnode
      d.slot caps st n 0 true #[] st hAt' (fun _ => LedgerOnly.refl st)
    simp only [↓reduceIte] at hs
    simp only [hs, hi]
    rfl

theorem senderExtraCapAddrs_one (st : SystemState) (tcb : TCB) :
    senderExtraCapAddrs st tcb 1 =
      match senderExtraCapAddr? st tcb 0 with
      | some a => #[a]
      | none => #[] := by
  unfold senderExtraCapAddrs
  simp only [show min 1 maxExtraCaps = 1 by decide, List.range_one, List.mapM_cons,
    List.mapM_nil]
  cases senderExtraCapAddr? st tcb 0 <;> rfl

theorem senderExtraCapAddrs_two (st : SystemState) (tcb : TCB) :
    senderExtraCapAddrs st tcb 2 =
      match senderExtraCapAddr? st tcb 0, senderExtraCapAddr? st tcb 1 with
      | some a, some b => #[a, b]
      | _, _ => #[] := by
  unfold senderExtraCapAddrs
  simp only [show min 2 maxExtraCaps = 2 by decide, show List.range 2 = [0, 1] from rfl,
    List.mapM_cons, List.mapM_nil]
  cases senderExtraCapAddr? st tcb 0 <;> cases senderExtraCapAddr? st tcb 1 <;> rfl

theorem senderExtraCapAddrs_three (st : SystemState) (tcb : TCB) (c : Nat) :
    senderExtraCapAddrs st tcb (c + 3) =
      match senderExtraCapAddr? st tcb 0, senderExtraCapAddr? st tcb 1,
          senderExtraCapAddr? st tcb 2 with
      | some a, some b, some d => #[a, b, d]
      | _, _, _ => #[] := by
  unfold senderExtraCapAddrs
  simp only [show min (c + 3) maxExtraCaps = 3 by simp [maxExtraCaps],
    show List.range 3 = [0, 1, 2] from rfl, List.mapM_cons, List.mapM_nil]
  cases senderExtraCapAddr? st tcb 0 <;> cases senderExtraCapAddr? st tcb 1 <;>
    cases senderExtraCapAddr? st tcb 2 <;> rfl

theorem receiveTransferCaps_no_target (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat))
    (ep : Option SeLe4n.ObjId) (st : SystemState) :
    receiveTransferCaps req ep none st = .ok ({ results := #[] }, st) := by
  unfold receiveTransferCaps
  split
  · rfl
  · dsimp only; split <;> rfl

/-- The specification's transfer of a request whose addresses resolve to the
slots `refs`, to a receiver with a buffer. -/
theorem receiveTransferCaps_some (root : SeLe4n.ObjId) (addrs : Array SeLe4n.CPtr) (depth : Nat)
    (ep : Option SeLe4n.ObjId) (rt : TCB) (slot? : Option CSpaceAddr) (st : SystemState) :
    receiveTransferCaps (some (root, addrs, depth)) ep (some (rt, slot?)) st =
      let caps := resolveExtraCaps root addrs depth true st
      if caps.isEmpty then .ok ({ results := #[] }, st) else ipcUnwrapCaps caps ep rt slot? st :=
  rfl

/-- The in-place transfer's last step: the loop in place over `n` capabilities,
its report and state handed to `K`, the receive slot free when the buffer names
one. -/
abbrev capRunFinish {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (n : Nat) (x0 x1 x2 : Capability) (a0 : SeLe4n.ObjId)
    (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId) (b1 : SeLe4n.Slot) (a2 : SeLe4n.ObjId)
    (b2 : SeLe4n.Slot) : α :=
  receiveSlotK st rt
    (fun _ => K (capStepsInfo ep x0 x1 x2 a0 b0 a1 b1 a2 b2 ep default st 0 n false 0 0)
      (capStepsApply ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 ep default 0 n false st))
    (fun dcn dsl => K (capStepsInfo ep x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl st 0 n true 0 0)
      (capStepsApply ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n true st))

/-- The specification's transfer over the capabilities `caps` resolved, to a
receiver with a buffer, its answer handed to `K`. -/
abbrev capSpecFinish {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (caps : Array TransferCap) : α :=
  match (if caps.isEmpty then .ok ({ results := #[] }, st)
      else ipcUnwrapCaps caps (some ep) rt (receiveSlot? st rt) st) with
  | .ok (s, st') => K s.capInfo st'
  | .error _ => K 0 st

theorem capRunFinish_zero {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (x0 x1 x2 : Capability) (a0 : SeLe4n.ObjId)
    (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId) (b1 : SeLe4n.Slot) (a2 : SeLe4n.ObjId)
    (b2 : SeLe4n.Slot) :
    capRunFinish st ep rt K 0 x0 x1 x2 a0 b0 a1 b1 a2 b2 = capSpecFinish st ep rt K #[] := by
  unfold capRunFinish
  rw [receiveSlotK_eq]
  cases receiveSlot? st rt <;> rfl

theorem capRunFinish_eq {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (caps : Array TransferCap) (n : Nat)
    (x0 x1 x2 : Capability) (a0 : SeLe4n.ObjId) (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId)
    (b1 : SeLe4n.Slot) (a2 : SeLe4n.ObjId) (b2 : SeLe4n.Slot)
    (hSize : caps.size = n) (hn : n ≠ 0)
    (hAt : ∀ j, j < n → caps[j]? = some (transferCapAt x0 x1 x2 a0 b0 a1 b1 a2 b2 j)) :
    capRunFinish st ep rt K n x0 x1 x2 a0 b0 a1 b1 a2 b2 = capSpecFinish st ep rt K caps := by
  have hE : caps.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff]; intro h; rw [h] at hSize; exact hn hSize.symm
  unfold capRunFinish capSpecFinish
  rw [ipcUnwrapCaps_eq_run st ep rt K caps n x0 x1 x2 a0 b0 a1 b1 a2 b2 hSize hAt, hE]
  rfl

section ReadLemmas
variable {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
  (K : Nat → SystemState → α) (a0 : SeLe4n.ObjId) (b0 : SeLe4n.Slot) (a1 : SeLe4n.ObjId)
  (b1 : SeLe4n.Slot) (a2 : SeLe4n.ObjId) (b2 : SeLe4n.Slot)

theorem transferCapsReadK_one :
    transferCapsReadK st 1 a0 b0 a1 b1 a2 b2
        (fun n x0 x1 x2 => capRunFinish st ep rt K n x0 x1 x2 a0 b0 a1 b1 a2 b2) =
      capSpecFinish st ep rt K (extraCapsFromSlots st [⟨a0, b0⟩] #[]) := by
  unfold transferCapsReadK
  simp only [extraCapsFromSlots]
  cases SystemState.lookupSlotCap st ⟨a0, b0⟩ with
  | none => exact capRunFinish_zero _ _ _ _ _ _ _ _ _ _ _ _ _
  | some x0 =>
    simp only [Nat.le_refl, ↓reduceIte]
    refine capRunFinish_eq _ _ _ _ _ 1 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
    intro j hj
    match j, hj with
    | 0, _ => rfl

theorem transferCapsReadK_two :
    transferCapsReadK st 2 a0 b0 a1 b1 a2 b2
        (fun n x0 x1 x2 => capRunFinish st ep rt K n x0 x1 x2 a0 b0 a1 b1 a2 b2) =
      capSpecFinish st ep rt K (extraCapsFromSlots st [⟨a0, b0⟩, ⟨a1, b1⟩] #[]) := by
  unfold transferCapsReadK
  simp only [extraCapsFromSlots]
  cases SystemState.lookupSlotCap st ⟨a0, b0⟩ with
  | none => exact capRunFinish_zero _ _ _ _ _ _ _ _ _ _ _ _ _
  | some x0 =>
    simp only [show ¬(2 ≤ 1) by decide, ↓reduceIte, Nat.le_refl]
    cases SystemState.lookupSlotCap st ⟨a1, b1⟩ with
    | none =>
      refine capRunFinish_eq _ _ _ _ _ 1 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
      intro j hj
      match j, hj with
      | 0, _ => rfl
    | some x1 =>
      refine capRunFinish_eq _ _ _ _ _ 2 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
      intro j hj
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl

theorem transferCapsReadK_three (c : Nat) :
    transferCapsReadK st (c + 3) a0 b0 a1 b1 a2 b2
        (fun n x0 x1 x2 => capRunFinish st ep rt K n x0 x1 x2 a0 b0 a1 b1 a2 b2) =
      capSpecFinish st ep rt K (extraCapsFromSlots st [⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩] #[]) := by
  unfold transferCapsReadK
  simp only [extraCapsFromSlots]
  cases SystemState.lookupSlotCap st ⟨a0, b0⟩ with
  | none => exact capRunFinish_zero _ _ _ _ _ _ _ _ _ _ _ _ _
  | some x0 =>
    simp only [show ¬(c + 3 ≤ 1) by omega, show ¬(c + 3 ≤ 2) by omega, ↓reduceIte]
    cases SystemState.lookupSlotCap st ⟨a1, b1⟩ with
    | none =>
      refine capRunFinish_eq _ _ _ _ _ 1 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
      intro j hj
      match j, hj with
      | 0, _ => rfl
    | some x1 =>
      cases SystemState.lookupSlotCap st ⟨a2, b2⟩ with
      | none =>
        refine capRunFinish_eq _ _ _ _ _ 2 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
        intro j hj
        match j, hj with
        | 0, _ => rfl
        | 1, _ => rfl
      | some x2 =>
        refine capRunFinish_eq _ _ _ _ _ 3 _ _ _ _ _ _ _ _ _ rfl (by decide) ?_
        intro j hj
        match j, hj with
        | 0, _ => rfl
        | 1, _ => rfl
        | 2, _ => rfl

end ReadLemmas

theorem resolveExtraCaps_list (root : SeLe4n.ObjId) (depth : Nat) (st : SystemState)
    (l : List SeLe4n.CPtr) :
    resolveExtraCaps root l.toArray depth true st =
      match l.mapM (fun a => (resolveCapAddress root a depth st).toOption) with
      | none => #[]
      | some refs => extraCapsFromSlots st refs #[] := by
  unfold resolveExtraCaps
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem capSpecFinish_request {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (rt : TCB)
    (K : Nat → SystemState → α) (root : SeLe4n.ObjId) (addrs : Array SeLe4n.CPtr) (depth : Nat) :
    (match receiveTransferCaps (if addrs.isEmpty then none else some (root, addrs, depth))
        (some ep) (some (rt, receiveSlot? st rt)) st with
      | .ok (s, st') => K s.capInfo st'
      | .error _ => K 0 st) =
      capSpecFinish st ep rt K (resolveExtraCaps root addrs depth true st) := by
  cases hE : addrs.isEmpty with
  | true =>
    have : addrs = #[] := by
      rcases addrs with ⟨l⟩; cases l
      · rfl
      · simp at hE
    subst this
    rfl
  | false => rfl

/-- **The transfer in place is the specification's transfer**: for a sender's
request read off its frame (`frameCapRequestOf`) and the receiver's side
(`capTargetOf`), the report and the state the in-place transfer hands on are the
summary's report and the state the specification's transfer answers. -/
theorem capTransferK_eq {α : Type} (st : SystemState) (ep : SeLe4n.ObjId) (stcb : TCB)
    (count : Nat) (rt : TCB) (K : Nat → SystemState → α) :
    capTransferK st ep stcb count rt (fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
        K (capStepsInfo ep x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl st 0 n free 0 0)
          (capStepsApply ep rt x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free st)) =
      match receiveTransferCaps (frameCapRequestOf st stcb count) (some ep)
          (capTargetOf st rt) st with
      | .ok (s, st') => K s.capInfo st'
      | .error _ => K 0 st := by
  unfold capTransferK capTargetOf
  cases hB : receiverHasBuffer st rt with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, receiveTransferCaps_no_target]
    rfl
  | true =>
  simp only [↓reduceIte]
  unfold frameCapRequestOf
  cases hR : st.getCNode? stcb.cspaceRoot with
  | none =>
    simp only [ite_self]
    rfl
  | some rootCn =>
    simp only []
    rw [capSpecFinish_request]
    match count with
    | 0 =>
      simp only [transferRefsK, senderExtraCapAddrs_zero, ↓reduceIte]
      rfl
    | 1 =>
      simp only [transferRefsK, senderExtraCapAddrs_one, extraCapRefK_eq, Nat.one_ne_zero,
        ↓reduceIte, Nat.le_refl]
      cases h0 : senderExtraCapAddr? st stcb 0 with
      | none => rfl
      | some a =>
        simp only []
        rw [show (#[a] : Array SeLe4n.CPtr) = [a].toArray from rfl, resolveExtraCaps_list]
        simp only [List.mapM_cons, List.mapM_nil]
        cases hr0 : resolveCapAddress stcb.cspaceRoot a rootCn.depth st with
        | error _ => rfl
        | ok r0 =>
          exact transferCapsReadK_one st ep rt K r0.cnode r0.slot r0.cnode r0.slot r0.cnode r0.slot
    | 2 =>
      simp only [transferRefsK, senderExtraCapAddrs_two, extraCapRefK_eq,
        show (2 : Nat) ≠ 0 by decide, show ¬(2 ≤ 1) by decide, ↓reduceIte, Nat.le_refl]
      cases h0 : senderExtraCapAddr? st stcb 0 with
      | none => rfl
      | some a =>
        cases h1 : senderExtraCapAddr? st stcb 1 with
        | none =>
          simp only []
          cases resolveCapAddress stcb.cspaceRoot a rootCn.depth st <;> rfl
        | some b =>
          simp only []
          rw [show (#[a, b] : Array SeLe4n.CPtr) = [a, b].toArray from rfl, resolveExtraCaps_list]
          simp only [List.mapM_cons, List.mapM_nil]
          cases hr0 : resolveCapAddress stcb.cspaceRoot a rootCn.depth st with
          | error _ => rfl
          | ok r0 =>
            cases hr1 : resolveCapAddress stcb.cspaceRoot b rootCn.depth st with
            | error _ => rfl
            | ok r1 =>
              exact transferCapsReadK_two st ep rt K r0.cnode r0.slot r1.cnode r1.slot r1.cnode r1.slot
    | c + 3 =>
      simp only [transferRefsK, senderExtraCapAddrs_three, extraCapRefK_eq,
        show c + 3 ≠ 0 by omega, show ¬(c + 3 ≤ 1) by omega, show ¬(c + 3 ≤ 2) by omega,
        ↓reduceIte]
      cases h0 : senderExtraCapAddr? st stcb 0 with
      | none => rfl
      | some a =>
        cases h1 : senderExtraCapAddr? st stcb 1 with
        | none =>
          simp only []
          cases resolveCapAddress stcb.cspaceRoot a rootCn.depth st <;> rfl
        | some b =>
          cases h2 : senderExtraCapAddr? st stcb 2 with
          | none =>
            simp only []
            cases resolveCapAddress stcb.cspaceRoot a rootCn.depth st <;>
              cases resolveCapAddress stcb.cspaceRoot b rootCn.depth st <;> rfl
          | some d =>
            simp only []
            rw [show (#[a, b, d] : Array SeLe4n.CPtr) = [a, b, d].toArray from rfl,
              resolveExtraCaps_list]
            simp only [List.mapM_cons, List.mapM_nil]
            cases hr0 : resolveCapAddress stcb.cspaceRoot a rootCn.depth st with
            | error _ => rfl
            | ok r0 =>
              cases hr1 : resolveCapAddress stcb.cspaceRoot b rootCn.depth st with
              | error _ => rfl
              | ok r1 =>
                cases hr2 : resolveCapAddress stcb.cspaceRoot d rootCn.depth st with
                | error _ => rfl
                | ok r2 =>
                  exact transferCapsReadK_three st ep rt K r0.cnode r0.slot r1.cnode r1.slot
                    r2.cnode r2.slot c

end SeLe4n.Kernel
