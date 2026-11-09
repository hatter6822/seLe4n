-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace

/-!
# A capability transfer that transfers nothing

seL4's `transferCaps` transfers nothing to a receiver with no IPC buffer, and
nothing to one whose buffer names no receive slot when the first extra
capability is not one it unwraps: the loop stops at that capability.  The
caps-unwrapped bits and the extra-caps count it reports are then both zero, and
no slot or buffer word is written.  The specification reads the receiver's side
of the transfer from the pre-state (`receiverCapTarget?`); this module states
when the transfer transfers nothing (`capTransferInert`), proves it the
identity reporting nothing (`receiveTransferCaps_of_inert`), and gives the
decision in the form the compiled arms make it (`receiveSlotAbsentW`,
`extraCapStaysW`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **A transfer to a receiver that can take no capability is the identity and
reports none.** -/
theorem receiveTransferCaps_of_noTarget
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)) (endpointId : SeLe4n.ObjId)
    (st : SystemState) :
    receiveTransferCaps req endpointId none st = .ok ({ results := #[] }, st) := by
  unfold receiveTransferCaps
  rcases req with _ | ⟨sroot, addrs, depth⟩
  · rfl
  · simp only []
    split <;> rfl

/-! ### A transfer that transfers nothing

seL4's `transferCaps` also transfers nothing to a receiver whose buffer names no
receive slot when the first extra capability is not one it unwraps: the loop
stops at that capability (`ipcUnwrapCapsLoop`), so no badge and no capability
reaches the receiver and the report is zero.  The decision is read from the
state the send found, and the transfer runs after the rendezvous, which writes
no CNode; the receiver's side is read from the pre-state already
(`receiverCapTarget?`), and the sender's capabilities are resolved alike in
both (`resolveExtraCaps_congr_getCNode?`). -/

/-- **Does a transfer to the receiver's side `target?` of the request `req`
transfer nothing?**  The receiver takes no capability, or it names no receive
slot and the first address does not name a capability the transfer unwraps (it
fails to resolve, names an empty slot, or names a capability to another
object). -/
def capTransferInert (st : SystemState) (endpointId : SeLe4n.ObjId)
    (target? : Option (TCB × Option CSpaceAddr))
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)) : Bool :=
  match req with
  | none => true
  | some (root, addrs, depth) =>
    match target? with
    | none => true
    | some (_, some _) => false
    | some (_, none) =>
      match addrs[0]? with
      | none => true
      | some a =>
        match resolveCapAddress root a depth st with
        | .error _ => true
        | .ok ref =>
          match SystemState.lookupSlotCap st ref with
          | none => true
          | some cap => !capUnwrapsAt cap endpointId

/-- The slots' capabilities are read alike in two states that read every CNode
alike. -/
theorem extraCapsFromSlots_congr_getCNode? (st₁ st₂ : SystemState)
    (hCNode : ∀ id, st₁.getCNode? id = st₂.getCNode? id) :
    ∀ (refs : List SlotRef) (acc : Array TransferCap),
      extraCapsFromSlots st₁ refs acc = extraCapsFromSlots st₂ refs acc
  | [], _ => rfl
  | ref :: rest, acc => by
    simp only [extraCapsFromSlots, lookupSlotCap_congr_getCNode? st₁ st₂ hCNode ref]
    split
    · rfl
    · exact extraCapsFromSlots_congr_getCNode? st₁ st₂ hCNode rest _

/-- **The sender's capabilities resolve alike** in two states that read every
CNode alike. -/
theorem resolveExtraCaps_congr_getCNode? (st₁ st₂ : SystemState)
    (hCNode : ∀ id, st₁.getCNode? id = st₂.getCNode? id) (root : SeLe4n.ObjId)
    (addrs : Array SeLe4n.CPtr) (depth : Nat) (granted : Bool) :
    resolveExtraCaps root addrs depth granted st₁ = resolveExtraCaps root addrs depth granted st₂ := by
  have hf : (fun addr => (resolveCapAddress root addr depth st₁).toOption) =
      (fun addr => (resolveCapAddress root addr depth st₂).toOption) := by
    funext addr; rw [resolveCapAddress_congr_getCNode? st₁ st₂ hCNode]
  unfold resolveExtraCaps
  rw [hf]
  split
  · rfl
  · split
    · rfl
    · exact extraCapsFromSlots_congr_getCNode? st₁ st₂ hCNode _ _

/-- The capabilities collected keep the ones already collected. -/
theorem extraCapsFromSlots_getElem?_of_lt (st : SystemState) :
    ∀ (refs : List SlotRef) (acc : Array TransferCap) (i : Nat), i < acc.size →
      (extraCapsFromSlots st refs acc)[i]? = acc[i]?
  | [], _, _, _ => rfl
  | ref :: rest, acc, i, hi => by
    unfold extraCapsFromSlots
    split
    · rfl
    · rw [extraCapsFromSlots_getElem?_of_lt st rest _ i (by simp; omega)]
      simp only [Array.getElem?_push, show i ≠ acc.size by omega, ↓reduceIte]

/-- **A transfer that transfers nothing is the identity and reports none**,
run in any state reading every CNode as the one its decision was read in. -/
theorem receiveTransferCaps_of_inert {st st' : SystemState}
    {req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)} {endpointId : SeLe4n.ObjId}
    {target? : Option (TCB × Option CSpaceAddr)}
    (hInert : capTransferInert st endpointId target? req = true)
    (hCNode : ∀ id, st'.getCNode? id = st.getCNode? id) :
    receiveTransferCaps req endpointId target? st' = .ok ({ results := #[] }, st') := by
  rcases req with _ | ⟨root, addrs, depth⟩
  · rfl
  rcases target? with _ | ⟨rtcb, _ | dst⟩
  · exact receiveTransferCaps_of_noTarget _ endpointId st'
  · simp only [capTransferInert] at hInert
    simp only [receiveTransferCaps, resolveExtraCaps_congr_getCNode? st' st hCNode]
    rcases addrs with ⟨_ | ⟨a, rest⟩⟩
    · simp [resolveExtraCaps, extraCapsFromSlots]
    · simp only [List.getElem?_toArray, List.getElem?_cons_zero] at hInert
      unfold resolveExtraCaps
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mapM_cons]
      generalize rest.mapM (fun addr => (resolveCapAddress root addr depth st).toOption) = m
      cases hR : resolveCapAddress root a depth st with
      | error e => rfl
      | ok ref =>
        simp only [hR] at hInert
        cases m with
        | none => rfl
        | some refs =>
          show (if (extraCapsFromSlots st (ref :: refs) #[]).isEmpty then
              .ok ({ results := #[] }, st')
            else ipcUnwrapCaps (extraCapsFromSlots st (ref :: refs) #[]) endpointId rtcb none st') =
            .ok ({ results := #[] }, st')
          cases hL : SystemState.lookupSlotCap st ref with
          | none => simp [extraCapsFromSlots, hL]
          | some cap =>
            simp only [hL] at hInert
            have hU : capUnwrapsAt cap endpointId = false := by simpa using hInert
            simp only [extraCapsFromSlots, hL]
            have h0 := extraCapsFromSlots_getElem?_of_lt st refs
              (#[].push (TransferCap.fromSlot cap ref)) 0 (by simp)
            generalize extraCapsFromSlots st refs (#[].push (TransferCap.fromSlot cap ref)) = caps at h0
            simp only [Array.getElem?_push, Array.size_empty, ↓reduceIte] at h0
            have hPos : 0 < caps.size := by
              rcases Nat.eq_zero_or_pos caps.size with h | h
              · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at h0; cases h0
              · exact h
            have hNe : caps.isEmpty = false := by
              cases hE : caps.isEmpty
              · rfl
              · rw [Array.isEmpty_iff_size_eq_zero] at hE; omega
            simp only [hNe, Bool.false_eq_true, ↓reduceIte, ipcUnwrapCaps]
            obtain ⟨n, hS⟩ : ∃ n, caps.size = n + 1 := ⟨caps.size - 1, by omega⟩
            rw [hS]
            simp only [ipcUnwrapCapsLoop, h0, TransferCap.fromSlot, hU, Bool.false_eq_true,
              ↓reduceIte]
  · simp [capTransferInert] at hInert

/-! ### The decision, in place

The compiled arms decide `capTransferInert` without building the receiver's
side or the sender's resolved capabilities: each lookup is a continuation-form
resolve (`resolveCapAddressKUnrolled`), so the decision builds nothing on the
common path. -/

/-- The receive depth refused, compared as the word (so no number is built for
a word too large for a scalar). -/
theorem receiveDepthRefused_eq (d : UInt64) :
    (d == 0 || (64 : UInt64) < d) = decide (d.toNat = 0 ∨ 64 < d.toNat) := by
  have h1 : (d == 0) = decide (d.toNat = 0) := by
    by_cases h : d = 0
    · subst h; rfl
    · have : d.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
      simp [h, this]
  have h2 : ((64 : UInt64) < d) ↔ 64 < d.toNat := UInt64.lt_iff_toNat_lt
  rw [h1]
  by_cases a : d.toNat = 0 <;> by_cases b : 64 < d.toNat <;> simp [a, b, h2]

/-- `receivePathSlot?` names no slot, decided in place
(`receivePathAbsentW_eq`). -/
@[inline] def receivePathAbsentW (st : SystemState) (tcb : TCB)
    (cnodeWord indexWord depthWord : UInt64) : Bool :=
  match st.getCNode? tcb.cspaceRoot with
  | none => true
  | some rootCn =>
    resolveCapAddressKUnrolled tcb.cspaceRoot (SeLe4n.CPtr.ofWord cnodeWord) rootCn.depth st
      (fun _ => true)
      (fun cn sl =>
        match SystemState.lookupSlotCap st ⟨cn, sl⟩ with
        | none => true
        | some cap =>
          match cap.target with
          | .object cnodeId =>
            match st.getCNode? cnodeId with
            | none => true
            | some _ =>
              if depthWord == 0 || (64 : UInt64) < depthWord then true else
              resolveCapAddressKUnrolled cnodeId (SeLe4n.CPtr.ofWord indexWord) depthWord.toNat st
                (fun _ => true)
                (fun cn' sl' => (SystemState.lookupSlotCap st ⟨cn', sl'⟩).isSome)
          | _ => true)

theorem receivePathAbsentW_eq (st : SystemState) (tcb : TCB) (c i d : UInt64) :
    receivePathAbsentW st tcb c i d = (receivePathSlot? st tcb c i d).isNone := by
  unfold receivePathAbsentW receivePathSlot?
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
            · simp only [hd, decide_true, ↓reduceIte, Option.isNone_none]
            · simp only [hd, decide_false, Bool.false_eq_true, ↓reduceIte]
              cases resolveCapAddress cnodeId (SeLe4n.CPtr.ofWord i) d.toNat st with
              | error _ => rfl
              | ok ref' =>
                simp only []
                cases SystemState.lookupSlotCap st ⟨ref'.cnode, ref'.slot⟩ <;> rfl
        | _ => rfl

/-- The receiver's buffer names no receive slot, decided in place
(`receiveSlotAbsentW_eq`). -/
@[inline] def receiveSlotAbsentW (st : SystemState) (tcb : TCB) : Bool :=
  match receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveCNodeWord,
      receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveIndexWord,
      receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveDepthWord with
  | some c, some i, some d => receivePathAbsentW st tcb c i d
  | _, _, _ => true

theorem receiveSlotAbsentW_eq (st : SystemState) (tcb : TCB) :
    receiveSlotAbsentW st tcb = (receiveSlot? st tcb).isNone := by
  unfold receiveSlotAbsentW receiveSlot?
  cases receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveCNodeWord <;>
    cases receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveIndexWord <;>
    cases receiverBufferWord? st tcb Architecture.IpcBufferRead.ipcBufferReceiveDepthWord <;>
    first | rfl | exact receivePathAbsentW_eq _ _ _ _ _

/-- The capability an address names does not unwrap at `endpointId` (or the
address names none), decided in place (`extraCapStaysW_eq`). -/
@[inline] def extraCapStaysW (st : SystemState) (endpointId root : SeLe4n.ObjId)
    (addr : SeLe4n.CPtr) (depth : Nat) : Bool :=
  resolveCapAddressKUnrolled root addr depth st (fun _ => true)
    (fun cn sl =>
      match SystemState.lookupSlotCap st ⟨cn, sl⟩ with
      | none => true
      | some cap => !capUnwrapsAt cap endpointId)

theorem extraCapStaysW_eq (st : SystemState) (endpointId root : SeLe4n.ObjId)
    (addr : SeLe4n.CPtr) (depth : Nat) :
    extraCapStaysW st endpointId root addr depth =
      match resolveCapAddress root addr depth st with
      | .error _ => true
      | .ok ref =>
        match SystemState.lookupSlotCap st ref with
        | none => true
        | some cap => !capUnwrapsAt cap endpointId := by
  unfold extraCapStaysW
  rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
  cases resolveCapAddress root addr depth st <;> rfl

end SeLe4n.Kernel
