-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.SetSpace

/-! # seL4's `TCB_SetIPCBuffer`

A thread's IPC buffer is two words of its TCB, as in seL4: the buffer's
address (`TCB.ipcBuffer`, seL4's `tcbIPCBuffer`) and the capability to the
frame that holds it, in the thread's buffer slot (`TCB.ipcBufferSlot`, seL4's
`tcbBuffer`).  Every read and write of the buffer goes through that capability
(`IpcBufferRead.lookupIPCBuffer`), never through the thread's address space.

`setIPCBufferOp` sets both as seL4-MCS's `decodeSetIPCBuffer` and
`invokeTCB_ThreadControlCaps` do (WS-SX SX6.6):

1. the frame capability is the caller's **extra capability 0**, resolved as a
   slot through the caller's CSpace; a message naming none is refused
   `truncatedMessage`;
2. a nonzero buffer address derives the capability (`untypedDeriveRefused`,
   seL4's `deriveCap`) and checks it as `checkValidIPCBuffer` does: a frame
   capability (`illegalState`, seL4's `seL4_IllegalOperation`), not device
   memory (`illegalState`), and the address aligned to the buffer's size
   (`alignmentError`).  A zero address takes the null capability: the slot is
   emptied and nothing is inserted;
3. the buffer slot is then set as a space slot is (`threadSlotSet`): its old
   capability deleted as `cteDelete` deletes it, finalising what it was the
   last capability to, and the derived copy inserted with the derivation edge
   from the source slot; the address is written into the thread.

The thread need not be suspended: seL4 changes a running thread's buffer, and
the change takes effect at its next IPC.  The address space is not consulted:
seL4 does not walk it, and a buffer the thread has not mapped faults the thread
when it touches it, not the kernel.
-/

namespace SeLe4n.Kernel.Architecture.IpcBufferValidation

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

/-- The rights mask the buffer slot's copy takes: every right, so the copy keeps
the rights of the capability it is derived from, as seL4's `deriveCap` keeps a
frame capability's.  A constant, built once. -/
def ipcBufferSlotRights : AccessRightSet :=
  AccessRightSet.ofList [.read, .write, .grant, .grantReply, .retype]

/-- The CNode the buffer slot is set from: the source's, or, for a zero buffer
address (seL4's null capability), the thread itself.  A thread is no CNode, so no
slot lookup finds a capability there, and the slot set inserts nothing
(`setIPCBufferPerform_zero`). -/
@[inline] def ipcBufferSourceCNode (tid : ThreadId) (srcCNode : ObjId) (addr : VAddr) : ObjId :=
  if addr.toNat = 0 then tid.toObjId else srcCNode

/-- The slot the buffer slot is set from (`ipcBufferSourceCNode`). -/
@[inline] def ipcBufferSourceSlot (srcSlot : Slot) (addr : VAddr) : Slot :=
  if addr.toNat = 0 then TCB.ipcBufferSlot else srcSlot

/-- **The writes of a buffer change**: the buffer slot set from the source slot
(`threadSlotSet`, the old capability deleted and finalised, the derived copy
inserted with its edge), then the buffer address written into the thread. -/
@[inline] def setIPCBufferPerform (executingCore : Concurrency.CoreId) (st : SystemState)
    (tid : ThreadId) (srcCNode : ObjId) (srcSlot : Slot) (addr : VAddr) : SystemState :=
  (threadSlotSet executingCore st tid TCB.ipcBufferSlot (ipcBufferSourceCNode tid srcCNode addr)
    (ipcBufferSourceSlot srcSlot addr) ipcBufferSlotRights 0).updateTcb tid
    (fun t => { t with ipcBuffer := addr })

/-- **seL4's `checkValidIPCBuffer` on the capability derived from the source
slot**, for a nonzero address: admitted when the slot holds a capability the
derivation accepts, naming a frame of RAM, and the address is aligned to the
buffer's size. -/
@[inline] def ipcBufferSourceAdmitted (st : SystemState) (srcCNode : ObjId) (srcSlot : Slot)
    (addr : VAddr) : Bool :=
  match SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
  | none => false
  | some cap =>
    !untypedDeriveRefused st { cnode := srcCNode, slot := srcSlot } cap &&
    match cap.target with
    | .object id =>
      match st.getFrame? id with
      | some f => !f.isDevice && addr.toNat % ipcBufferAlignment == 0
      | none => false
    | _ => false

/-- **A buffer change from the source slot `srcCNode`/`srcSlot`**, refused,
committing nothing, when the thread is not a stored TCB (`objectNotFound`) or,
for a nonzero address, as `checkValidIPCBuffer` refuses the derived capability:
an empty slot or a capability that is no frame's, or a frame of device memory
(`illegalState`), an untyped capability the derivation refuses
(`revocationRequired`), an unaligned address (`alignmentError`). -/
def setIPCBufferFrom (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : ValidThreadId) (srcCNode : ObjId) (srcSlot : Slot) (addr : VAddr) :
    Except KernelError SystemState :=
  match st.getTcb? vtid.val with
  | none => .error .objectNotFound
  | some _ =>
    if addr.toNat = 0 then .ok (setIPCBufferPerform executingCore st vtid.val srcCNode srcSlot addr)
    else
      match SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
      | none => .error .illegalState
      | some cap =>
        if untypedDeriveRefused st { cnode := srcCNode, slot := srcSlot } cap then
          .error .revocationRequired
        else
          match cap.target with
          | .object id =>
            match st.getFrame? id with
            | some f =>
              if f.isDevice then .error .illegalState
              else if addr.toNat % ipcBufferAlignment != 0 then .error .alignmentError
              else .ok (setIPCBufferPerform executingCore st vtid.val srcCNode srcSlot addr)
            | none => .error .illegalState
          | _ => .error .illegalState

/-- **`.tcbSetIPCBuffer`: seL4's `TCB_SetIPCBuffer`** — the frame capability is
the caller's extra capability 0 (`bufferCap?`, seL4's `excaprefs[0]`; none is
`truncatedMessage`), resolved as a slot through the caller's CSpace, then the
change from that slot (`setIPCBufferFrom`). -/
def setIPCBufferOp (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : ValidThreadId) (callerTid : ThreadId) (bufferCap? : Option CPtr) (addr : VAddr) :
    Except KernelError SystemState :=
  match bufferCap? with
  | none => .error .truncatedMessage
  | some cptr =>
    match st.getTcb? callerTid with
    | none => .error .objectNotFound
    | some callerTcb =>
      match lookupSlot callerTcb cptr st with
      | .error f => .error (.failedLookup false f)
      | .ok src => setIPCBufferFrom executingCore st vtid src.cnode src.slot addr

/-- **`setIPCBufferFrom`'s checks**, read before anything is written: the
thread is a stored TCB, and a nonzero address's source is admitted.  When they
pass the operation is its writes (`setIPCBufferFrom_of_admitted`). -/
@[inline] def setIPCBufferAdmitted (st : SystemState) (vtid : ValidThreadId) (srcCNode : ObjId)
    (srcSlot : Slot) (addr : VAddr) : Bool :=
  (st.getTcb? vtid.val).isSome &&
    (addr.toNat == 0 || ipcBufferSourceAdmitted st srcCNode srcSlot addr)

/-- What an admitted source is: a capability the derivation accepts, naming a
frame of RAM, and an aligned address. -/
theorem ipcBufferSourceAdmitted_spec {st : SystemState} {srcCNode : ObjId} {srcSlot : Slot}
    {addr : VAddr} (h : ipcBufferSourceAdmitted st srcCNode srcSlot addr = true) :
    ∃ cap id f, SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } = some cap ∧
      untypedDeriveRefused st { cnode := srcCNode, slot := srcSlot } cap = false ∧
      cap.target = .object id ∧ st.getFrame? id = some f ∧ f.isDevice = false ∧
      addr.toNat % ipcBufferAlignment = 0 := by
  unfold ipcBufferSourceAdmitted at h
  split at h
  · cases h
  · rename_i cap hL
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hU, h⟩ := h
    split at h
    · rename_i id hTg
      split at h
      · rename_i f hF
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        exact ⟨cap, id, f, hL, hU, hTg, hF, h.1, h.2⟩
      · cases h
    · cases h

theorem setIPCBufferFrom_of_admitted {ec : Concurrency.CoreId} {st : SystemState}
    {vtid : ValidThreadId} {srcCNode : ObjId} {srcSlot : Slot} {addr : VAddr}
    (h : setIPCBufferAdmitted st vtid srcCNode srcSlot addr = true) :
    setIPCBufferFrom ec st vtid srcCNode srcSlot addr =
      .ok (setIPCBufferPerform ec st vtid.val srcCNode srcSlot addr) := by
  unfold setIPCBufferAdmitted at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hT, hA⟩ := h
  unfold setIPCBufferFrom
  obtain ⟨t, hT⟩ := Option.isSome_iff_exists.mp hT
  rw [hT]
  dsimp only
  by_cases h0 : addr.toNat = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    obtain ⟨cap, id, f, hL, hU, hTg, hF, hD, hAl⟩ :=
      ipcBufferSourceAdmitted_spec (hA.resolve_left h0)
    simp only [hL, hU, hTg, hF, hD, hAl, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]

/-- **What a successful buffer change from a slot consists of**: the thread was
a stored TCB, a nonzero address's source was admitted, and the state is the
change's writes. -/
theorem setIPCBufferFrom_ok {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : ValidThreadId} {srcCNode : ObjId} {srcSlot : Slot} {addr : VAddr}
    (h : setIPCBufferFrom ec st vtid srcCNode srcSlot addr = .ok st') :
    ∃ t, st.getTcb? vtid.val = some t ∧
      (addr.toNat = 0 ∨ ipcBufferSourceAdmitted st srcCNode srcSlot addr = true) ∧
      st' = setIPCBufferPerform ec st vtid.val srcCNode srcSlot addr := by
  unfold setIPCBufferFrom at h
  cases hT : st.getTcb? vtid.val with
  | none => rw [hT] at h; cases h
  | some t =>
    rw [hT] at h
    dsimp only at h
    refine ⟨t, rfl, ?_⟩
    by_cases h0 : addr.toNat = 0
    · rw [if_pos h0] at h; cases h; exact ⟨.inl h0, rfl⟩
    · rw [if_neg h0] at h
      cases hL : SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } with
      | none => rw [hL] at h; cases h
      | some cap =>
        rw [hL] at h
        dsimp only at h
        cases hU : untypedDeriveRefused st { cnode := srcCNode, slot := srcSlot } cap with
        | true => rw [hU] at h; cases h
        | false =>
          rw [hU] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hTg : cap.target with
          | object id =>
            rw [hTg] at h
            dsimp only at h
            cases hF : st.getFrame? id with
            | none => rw [hF] at h; cases h
            | some f =>
              rw [hF] at h
              dsimp only at h
              cases hD : f.isDevice with
              | true => rw [hD] at h; cases h
              | false =>
                rw [hD] at h
                by_cases hAl : addr.toNat % ipcBufferAlignment = 0
                · simp only [hAl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                    Except.ok.injEq] at h
                  refine ⟨.inr ?_, h.symm⟩
                  simp only [ipcBufferSourceAdmitted, hL, hU, hTg, hF, hD, hAl, Bool.not_false,
                    Bool.true_and, beq_self_eq_true, Bool.and_self]
                · have : (addr.toNat % ipcBufferAlignment != 0) = true := by simpa using hAl
                  simp only [this, Bool.false_eq_true, ↓reduceIte] at h; cases h
          | _ => rw [hTg] at h; cases h

/-- **A buffer change goes through the slot extra capability 0 names**: the
change from that slot (`setIPCBufferFrom`). -/
theorem setIPCBufferOp_ok {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : ValidThreadId} {callerTid : ThreadId} {bufferCap? : Option CPtr} {addr : VAddr}
    (h : setIPCBufferOp ec st vtid callerTid bufferCap? addr = .ok st') :
    ∃ srcCNode srcSlot, setIPCBufferFrom ec st vtid srcCNode srcSlot addr = .ok st' := by
  unfold setIPCBufferOp at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact ⟨_, _, h⟩

/-- **What a successful buffer change consists of**: the thread was a stored
TCB, a nonzero address's source slot was admitted, and the state is the change's
writes from that slot. -/
theorem setIPCBufferOp_ok_perform {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : ValidThreadId} {callerTid : ThreadId} {bufferCap? : Option CPtr} {addr : VAddr}
    (h : setIPCBufferOp ec st vtid callerTid bufferCap? addr = .ok st') :
    ∃ srcCNode srcSlot t, st.getTcb? vtid.val = some t ∧
      (addr.toNat = 0 ∨ ipcBufferSourceAdmitted st srcCNode srcSlot addr = true) ∧
      st' = setIPCBufferPerform ec st vtid.val srcCNode srcSlot addr := by
  obtain ⟨c, s, h⟩ := setIPCBufferOp_ok h
  obtain ⟨t, hT, hA, rfl⟩ := setIPCBufferFrom_ok h
  exact ⟨c, s, t, hT, hA, rfl⟩

/-- **The source a buffer change copies from names no untyped**: a zero
address's is the thread's own slot, which no slot lookup finds (a thread is no
CNode), and a nonzero address's names a frame. -/
theorem setIPCBufferSource_notUntyped {st : SystemState} {tid : ThreadId} {t : TCB}
    {srcCNode : ObjId} {srcSlot : Slot} {addr : VAddr} (hT : st.getTcb? tid = some t)
    (hA : addr.toNat = 0 ∨ ipcBufferSourceAdmitted st srcCNode srcSlot addr = true) :
    ∀ cap, SystemState.lookupSlotCap st
        ⟨ipcBufferSourceCNode tid srcCNode addr, ipcBufferSourceSlot srcSlot addr⟩ = some cap →
      ∀ u, cap.target = .object u → st.getUntyped? u = none := by
  intro cap hL u hu
  unfold ipcBufferSourceCNode ipcBufferSourceSlot at hL
  by_cases h0 : addr.toNat = 0
  · simp only [h0, ↓reduceIte] at hL
    have hO := (SystemState.getTcb?_eq_some_iff st tid t).mp hT
    simp [SystemState.lookupSlotCap, SystemState.lookupCNode, hO] at hL
  · simp only [h0, ↓reduceIte] at hL
    obtain ⟨cap', id, f, hL', -, hTg, hF, -⟩ := ipcBufferSourceAdmitted_spec (hA.resolve_left h0)
    rw [hL] at hL'; cases hL'
    rw [hTg] at hu; cases hu
    unfold SystemState.getFrame? at hF; unfold SystemState.getUntyped?
    split at hF <;> simp_all

/-- AE4-H (U-32/A-IB01): IPC buffer cross-page safety.

The IPC buffer (`ipcBufferAlignment`, 1024 bytes) never crosses a page
boundary when the address is aligned to its size. Since 1024 divides the
ARM64 page size (4096 = 1024 × 4), any 1024-aligned offset within a page
leaves at least 1024 bytes before the next page boundary, so the buffer lies in
the one frame its capability names. -/
theorem ipcBuffer_within_page (addr : VAddr)
    (hAligned : addr.toNat % ipcBufferAlignment = 0) :
    addr.toNat / 4096 = (addr.toNat + ipcBufferAlignment - 1) / 4096 := by
  simp only [ipcBufferAlignment] at hAligned ⊢
  omega

end SeLe4n.Kernel.Architecture.IpcBufferValidation
