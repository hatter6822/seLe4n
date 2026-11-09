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

end SeLe4n.Kernel
