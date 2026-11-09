-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultInPlace
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# A send of more than four words, delivered in place

WS-ZA ZA6.35.  seL4's `doIPCTransfer` copies a message that runs past the
message registers straight from the sender's IPC buffer into the receiver's
(`copyMRs`): the first words go register to register, the rest buffer word to
buffer word, and the receiver's message info reports what arrived.  The
specification here holds the whole message in the receiver's TCB and stages it
(`stageDeliveredMessage`), which builds the message array and the list of its
overflow writes.  This module is the same delivery written word by word: the
inline words into the receiver's saved registers (`withFrameWords`), and each
overflow word read from the sender's buffer and recorded as a user-word store
at the receiver's slot (`overflowCopyStore`), up to the first slot the
receiver's buffer does not resolve (`overflowSlotsFrom`).

The words are read after the rendezvous and the wake, which write no thread's
VSpace root or IPC buffer and no VSpace root (`ipcBufferReadsAgree`), so each
word is the one the specification's decode read before them
(`performSendDeliveredLong_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ## What an IPC-buffer read reads -/

/-- What an IPC-buffer read reads of an object: a thread's VSpace root and
buffer address, a VSpace root itself, nothing of any other object. -/
@[inline] def ipcBufferViewOf : KernelObject → Option ((SeLe4n.ObjId × SeLe4n.VAddr) ⊕ VSpaceRoot)
  | .tcb t => some (.inl (t.vspaceRoot, t.ipcBuffer))
  | .vspaceRoot r => some (.inr r)
  | _ => none

/-- The VSpace root a view names. -/
@[inline] def viewVSpaceRoot : Option ((SeLe4n.ObjId × SeLe4n.VAddr) ⊕ VSpaceRoot) →
    Option VSpaceRoot
  | some (.inr r) => some r
  | _ => none

/-- The thread's VSpace root and buffer address a view names. -/
@[inline] def viewBuffer : Option ((SeLe4n.ObjId × SeLe4n.VAddr) ⊕ VSpaceRoot) →
    Option (SeLe4n.ObjId × SeLe4n.VAddr)
  | some (.inl p) => some p
  | _ => none

/-- **Two states read every IPC buffer alike**: at every key the same view
(`ipcBufferViewOf`), and the same machine, whose memory and entry words the
reads return. -/
def ipcBufferReadsAgree (st' st : SystemState) : Prop :=
  (∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).bind ipcBufferViewOf = (st.objects[x]?).bind ipcBufferViewOf) ∧
  st'.machine = st.machine

namespace ipcBufferReadsAgree

theorem refl (st : SystemState) : ipcBufferReadsAgree st st := ⟨fun _ => rfl, rfl⟩

theorem trans {a b c : SystemState} (h₂ : ipcBufferReadsAgree c b)
    (h₁ : ipcBufferReadsAgree b a) : ipcBufferReadsAgree c a :=
  ⟨fun x => (h₂.1 x).trans (h₁.1 x), h₂.2.trans h₁.2⟩

theorem of_eq {st st' : SystemState} (hO : st'.objects = st.objects)
    (hM : st'.machine = st.machine) : ipcBufferReadsAgree st' st :=
  ⟨fun x => by rw [hO], hM⟩

end ipcBufferReadsAgree

theorem getVSpaceRoot?_eq_view (st : SystemState) (id : SeLe4n.ObjId) :
    st.getVSpaceRoot? id = viewVSpaceRoot ((st.objects[id]?).bind ipcBufferViewOf) := by
  unfold SystemState.getVSpaceRoot?
  cases st.objects[id]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem getTcb?_buffer_eq_view (st : SystemState) (t : SeLe4n.ThreadId) :
    (st.getTcb? t).map (fun tcb => (tcb.vspaceRoot, tcb.ipcBuffer)) =
      viewBuffer ((st.objects[t.toObjId]?).bind ipcBufferViewOf) := by
  unfold SystemState.getTcb?
  cases st.objects[t.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

namespace ipcBufferReadsAgree

variable {st st' : SystemState} (h : ipcBufferReadsAgree st' st)
include h

theorem getVSpaceRoot? (id : SeLe4n.ObjId) : st'.getVSpaceRoot? id = st.getVSpaceRoot? id := by
  rw [getVSpaceRoot?_eq_view, getVSpaceRoot?_eq_view, h.1]

theorem getTcb?_buffer (t : SeLe4n.ThreadId) :
    (st'.getTcb? t).map (fun tcb => (tcb.vspaceRoot, tcb.ipcBuffer)) =
      (st.getTcb? t).map (fun tcb => (tcb.vspaceRoot, tcb.ipcBuffer)) := by
  rw [getTcb?_buffer_eq_view, getTcb?_buffer_eq_view, h.1]

/-- A read of a thread's IPC buffer reads the same word in both states. -/
theorem ipcBufferReadMr (tid : SeLe4n.ThreadId) (i : Nat) :
    Architecture.IpcBufferRead.ipcBufferReadMr st' tid i =
      Architecture.IpcBufferRead.ipcBufferReadMr st tid i := by
  have hT := h.getTcb?_buffer tid
  unfold Architecture.IpcBufferRead.ipcBufferReadMr
  by_cases hi : i ≥ Architecture.IpcBufferRead.maxOverflowSlots
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte]
    cases e' : st'.getTcb? tid <;> cases e : st.getTcb? tid <;>
      simp only [e', e, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Prod.mk.injEq] at hT
    · rfl
    · next t' t =>
      obtain ⟨hv, hb⟩ := hT
      simp only []
      rw [hv, hb, h.getVSpaceRoot?, h.2]

/-- A slot of a thread's IPC buffer resolves to the same address in both
states. -/
theorem overflowSlotOf (r : SeLe4n.ThreadId) (i : Nat) :
    SeLe4n.Kernel.overflowSlotOf st' r i = SeLe4n.Kernel.overflowSlotOf st r i := by
  have hT := h.getTcb?_buffer r
  unfold SeLe4n.Kernel.overflowSlotOf
  cases e' : st'.getTcb? r <;> cases e : st.getTcb? r <;>
    simp only [e', e, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq] at hT
  · rfl
  · next t' t =>
    obtain ⟨hv, hb⟩ := hT
    simp only [Architecture.IpcBufferRead.ipcBufferSlotPAddr?,
      Architecture.IpcBufferRead.ipcBufferWordPAddr?]
    rw [hv, hb, h.getVSpaceRoot?, h.2]

end ipcBufferReadsAgree

/-! ## Writes that keep every read -/

/-- A TCB write that keeps the thread's VSpace root and buffer address keeps
every read. -/
theorem ipcBufferReadsAgree_mapTcbInPlace (X : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (hg : ∀ t, (g t).vspaceRoot = t.vspaceRoot ∧ (g t).ipcBuffer = t.ipcBuffer) :
    ipcBufferReadsAgree (X.mapTcbInPlace r g) X := by
  refine ⟨fun x => ?_, rfl⟩
  rw [SystemState.objects_mapTcbInPlace]
  split
  · cases X.objects[x]? with
    | none => rfl
    | some o =>
      cases o with
      | tcb t =>
        simp only [Option.map_some, Option.bind_some, KernelObject.mapTcb, ipcBufferViewOf,
          (hg t).1, (hg t).2]
      | _ => rfl
  · rfl

/-- An object write that keeps every object's view keeps every read, on a
table with no resize due. -/
theorem ipcBufferReadsAgree_modifyObject (X : SystemState) (k : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hF : ∀ o, ipcBufferViewOf (F o) = ipcBufferViewOf o)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (X.modifyObject k F) X := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.get?_mapValueAt]
    split
    · cases X.objects.get? x with
      | none => rfl
      | some o => simp only [Option.map_some, Option.bind_some, hF]
    · rfl
  · rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo]

theorem ipcBufferReadsAgree_updateTcb (X : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (hg : ∀ t, (g t).vspaceRoot = t.vspaceRoot ∧ (g t).ipcBuffer = t.ipcBuffer)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (X.updateTcb r g) X := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  exact ipcBufferReadsAgree_mapTcbInPlace X r g hg

/-- Objects that agree off their run-queue links agree on every view. -/
theorem ipcBufferReadsAgree_of_offRunLinks {X X' : SystemState}
    (h : SystemState.objectsAgreeOffRunLinks X' X) (hM : X'.machine = X.machine) :
    ipcBufferReadsAgree X' X := by
  refine ⟨fun x => ?_, hM⟩
  have hx := congrArg (fun o => o.bind ipcBufferViewOf) (h x)
  have hv : ∀ o : KernelObject, ipcBufferViewOf o.withoutRunLinks = ipcBufferViewOf o := by
    intro o; cases o <;> rfl
  simp only [Option.bind_map, Function.comp_def, hv] at hx
  exact hx

theorem ipcBufferViewOf_popEndpoint (isReceiveQ : Bool) (nextCode : Nat) (o : KernelObject) :
    ipcBufferViewOf (popEndpoint isReceiveQ nextCode o) = ipcBufferViewOf o := by
  cases o with
  | endpoint e => simp only [popEndpoint]; split <;> rfl
  | _ => rfl

/-- **The send rendezvous keeps every read**: it pops the endpoint's queue and
writes queue links and the receiver's message slots, never a VSpace root or a
buffer address. -/
theorem ipcBufferReadsAgree_storeSendRendezvousWith (st : SystemState)
    (endpointId : SeLe4n.ObjId) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (g : TCB → TCB) (hg : ∀ t, (g t).vspaceRoot = t.vspaceRoot ∧ (g t).ipcBuffer = t.ipcBuffer)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeSendRendezvousWith st endpointId head next g) st := by
  unfold storeSendRendezvousWith
  dsimp only
  have h1 := modifyObject_noResizeDue st endpointId
    (popEndpoint true (ThreadId.optCode next)) hNo
  have a1 := ipcBufferReadsAgree_modifyObject st endpointId
    (popEndpoint true (ThreadId.optCode next)) (ipcBufferViewOf_popEndpoint _ _) hNo
  generalize st.modifyObject endpointId (popEndpoint true (ThreadId.optCode next)) = s1 at h1 a1
  cases next with
  | none =>
    dsimp only
    have h3 := updateTcb_noResizeDue s1 head tcbOffQueue h1
    have a3 := ipcBufferReadsAgree_updateTcb s1 head tcbOffQueue (fun _ => ⟨rfl, rfl⟩) h1
    exact (ipcBufferReadsAgree_updateTcb _ head g hg h3).trans (a3.trans a1)
  | some n =>
    dsimp only
    have h2 := updateTcb_noResizeDue s1 n tcbAsQueueHead h1
    have a2 := ipcBufferReadsAgree_updateTcb s1 n tcbAsQueueHead (fun _ => ⟨rfl, rfl⟩) h1
    have h3 := updateTcb_noResizeDue _ head tcbOffQueue h2
    have a3 := ipcBufferReadsAgree_updateTcb _ head tcbOffQueue (fun _ => ⟨rfl, rfl⟩) h2
    exact (ipcBufferReadsAgree_updateTcb _ head g hg h3).trans (a3.trans (a2.trans a1))

/-- **A wake keeps every read**: it marks the thread ready and writes run-queue
links. -/
theorem ipcBufferReadsAgree_enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId)
    (t : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (enqueueRunnableOnCore st c t) st := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  split
  · next tcb hT =>
    split
    · exact .refl _
    · dsimp only
      have a1 := ipcBufferReadsAgree_modifyObject st t.toObjId
        (SystemState.mapTcbObject fun t => t.setIpcState .ready)
        (fun o => by cases o <;> rfl) hNo
      generalize st.modifyObject t.toObjId
        (SystemState.mapTcbObject fun t => t.setIpcState .ready) = s1 at a1
      have a2 := ipcBufferReadsAgree_of_offRunLinks
        (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks s1 c t tcb.boostedPriority)
        (SystemState.runEnqueueAdmitted_machine s1 c t tcb.boostedPriority)
      exact (ipcBufferReadsAgree.of_eq rfl rfl).trans (a2.trans a1)
  · exact .refl _

theorem ipcBufferReadsAgree_wakeThread (st : SystemState) (t : SeLe4n.ThreadId)
    (core : Concurrency.CoreId)
    (hNo : st.objects.noResizeDue) : ipcBufferReadsAgree (wakeThread st t core).1 st := by
  rw [wakeThread_state_eq_enqueue]
  exact ipcBufferReadsAgree_enqueueRunnableOnCore st _ t hNo

/-- …so the receiver woken by a send reads every buffer where the send found it. -/
theorem ipcBufferReadsAgree_sendWoken (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (nextCode : Nat) (core : Concurrency.CoreId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree
      (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1 st := by
  unfold storeSendRendezvousReady
  exact (ipcBufferReadsAgree_wakeThread _ r core
    (storeSendRendezvousWith_noResizeDue _ _ _ _ _ hNo)).trans
    (ipcBufferReadsAgree_storeSendRendezvousWith _ _ _ _ _ (fun _ => ⟨rfl, rfl⟩) hNo)

theorem ipcBufferReadsAgree_recordPhysicalWrite (S : SystemState) (w : Architecture.PhysicalWrite) :
    ipcBufferReadsAgree (S.recordPhysicalWrite w) S := .of_eq rfl rfl

/-! ## The overflow words, copied word by word -/

/-- Overflow word `i` of thread `s`'s IPC buffer, as the decode reads it, `0`
where the read refuses (`overflowWordAt_eq`).  The read lands in the caller's
arm as a machine word: no `Except` cell is built. -/
@[inline] def overflowWordAt (S : SystemState) (s : SeLe4n.ThreadId) (i : Nat) : UInt64 :=
  Architecture.IpcBufferRead.ipcBufferReadMrK S s i (fun _ => 0) id

theorem overflowWordAt_eq (S : SystemState) (s : SeLe4n.ThreadId) (i : Nat) :
    overflowWordAt S s i =
      match Architecture.IpcBufferRead.ipcBufferReadMr S s i with
      | .ok w => w
      | .error _ => 0 := by
  unfold overflowWordAt
  rw [Architecture.IpcBufferRead.ipcBufferReadMrK_eq]
  rfl

theorem ipcBufferReadsAgree.overflowWordAt {S S' : SystemState} (h : ipcBufferReadsAgree S' S)
    (s : SeLe4n.ThreadId) (i : Nat) :
    SeLe4n.Kernel.overflowWordAt S' s i = SeLe4n.Kernel.overflowWordAt S s i := by
  rw [overflowWordAt_eq, overflowWordAt_eq, h.ipcBufferReadMr]

/-- The registers `n` overflow slots of thread `s`'s buffer hold, from slot `i`. -/
def overflowRegsFrom (S : SystemState) (s : SeLe4n.ThreadId) : Nat → Nat → List SeLe4n.RegValue
  | _, 0 => []
  | i, n + 1 => (⟨(overflowWordAt S s i).toNat⟩ : SeLe4n.RegValue) :: overflowRegsFrom S s (i + 1) n

theorem overflowRegsFrom_length (S : SystemState) (s : SeLe4n.ThreadId) :
    ∀ (i n : Nat), (overflowRegsFrom S s i n).length = n
  | _, 0 => rfl
  | i, n + 1 => by simp only [overflowRegsFrom, List.length_cons, overflowRegsFrom_length S s (i + 1) n]

theorem ipcBufferReadsAgree.overflowRegsFrom {S S' : SystemState} (h : ipcBufferReadsAgree S' S)
    (s : SeLe4n.ThreadId) : ∀ (i n : Nat),
      SeLe4n.Kernel.overflowRegsFrom S' s i n = SeLe4n.Kernel.overflowRegsFrom S s i n
  | _, 0 => rfl
  | i, n + 1 => by
    simp only [SeLe4n.Kernel.overflowRegsFrom, h.overflowWordAt, h.overflowRegsFrom s (i + 1) n]

/-- **The sender's overflow words, copied into the receiver's buffer in
place**: word `i` of thread `s`'s buffer recorded as a user-word store at
thread `r`'s slot `i`, word by word, up to the first slot of `r`'s that does
not resolve (`overflowCopyStore_eq`).  Each word is read before the write that
records it. -/
def overflowCopyStore (S : SystemState) (r s : SeLe4n.ThreadId) : Nat → Nat → SystemState
  | _, 0 => S
  | i, n + 1 =>
    match overflowSlotOf S r i with
    | some pa => overflowCopyStore
        (S.recordPhysicalWrite (.storeUserWord pa (overflowWordAt S s i))) r s (i + 1) n
    | none => S

theorem overflowCopyStore_eq (r s : SeLe4n.ThreadId) (X : SystemState) (t : TCB) (Y : SystemState) :
    ∀ (n i : Nat) (S : SystemState),
      (∀ j, overflowSlotOf S r j = Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true) →
      ipcBufferReadsAgree S Y →
      overflowCopyStore S r s i n =
        Architecture.recordPhysicalWrites S
          (Architecture.overflowDeliveryWrites X t (overflowRegsFrom Y s i n) i)
  | 0, _, S, _, _ => (Architecture.recordPhysicalWrites_nil S).symm
  | n + 1, i, S, hS, hA => by
    simp only [overflowCopyStore, overflowRegsFrom, hS]
    unfold Architecture.overflowDeliveryWrites
    split
    · next pa hPa =>
      rw [hPa, recordPhysicalWrites_cons]
      have hReg : (⟨(overflowWordAt Y s i).toNat⟩ : SeLe4n.RegValue).val.toUInt64 =
          overflowWordAt Y s i := by
        simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]
      rw [hReg, hA.overflowWordAt]
      have hA' := (ipcBufferReadsAgree_recordPhysicalWrite S
        (.storeUserWord pa (overflowWordAt Y s i))).trans hA
      exact overflowCopyStore_eq r s X t Y n (i + 1) _
        (fun j => by rw [(ipcBufferReadsAgree_recordPhysicalWrite S _).overflowSlotOf, hS j]) hA'
    · next hPa => rw [hPa]; exact (Architecture.recordPhysicalWrites_nil S).symm

/-! ## The delivery -/

/-- The message a send of `len` words delivers whose first words are the
layout's message registers of `rf` and the rest the overflow slots of thread
`s`'s buffer: the message the specification holds in the receiver. -/
@[inline] def longSendMessage (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (S : SystemState) (s : SeLe4n.ThreadId) (len : Nat) (badge : Option SeLe4n.Badge) :
    IpcMessage :=
  { registers := Architecture.regMessageRegs layout rf ++ (overflowRegsFrom S s 0 (len - 4)).toArray,
    badge := badge }

/-- The message-info word a long send's delivered frame carries, `k` overflow
words having arrived.  Out of line, as `regMessageInfoWord`. -/
@[noinline] def longMessageInfoWord (len k : Nat) : UInt64 :=
  (({ length := min (min len (4 + k)) maxMessageRegisters
      extraCaps := 0 % 4
      label := min 0 (Architecture.errorLabelBase - 1)
      capsUnwrapped := 0 / 4 % 8 } : MessageInfo).encode).toUInt64

/-- The long message held where the woken receiver is, unexpectedly, not ready.
Out of line, so the message is built only on that path. -/
@[noinline] def holdLongSendMessage (X : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) : SystemState :=
  X.mapTcbInPlace r (holdMessage (longSendMessage layout rf X s len badge))

/-- **A long send's delivery to a woken receiver, in place**: the frame
written into the receiver's saved registers, its length counting the overflow
words the receiver's buffer takes (`overflowSlotsFrom`), then those words
copied from the sender's buffer (`overflowCopyStore`).  A receiver that is,
unexpectedly, not ready holds the message (`holdLongSendMessage`).  Each step
reads what it needs before it writes (`deliverLongSendFrame_eq`). -/
@[inline] def deliverLongSendFrame (X : SystemState) (r : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let k := overflowSlotsFrom X r 0 (len - 4)
      overflowCopyStore
        (X.mapTcbInPlace r (withFrameWords (Architecture.badgeWordIf badgeWord badged)
          (longMessageInfoWord len k) (Architecture.regMessageWord layout rf len 0)
          (Architecture.regMessageWord layout rf len 1) (Architecture.regMessageWord layout rf len 2)
          (Architecture.regMessageWord layout rf len 3)))
        r s 0 (len - 4)
    else holdLongSendMessage X r layout rf len s (SeLe4n.Badge.opt badgeWord badged)
  | none => X

theorem longSendMessage_size (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (S : SystemState) (s : SeLe4n.ThreadId) (len : Nat) (badge : Option SeLe4n.Badge)
    (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    (longSendMessage layout rf S s len badge).registers.size = len := by
  simp only [longSendMessage, Array.size_append, Architecture.regMessageRegs, Array.size_map, hSize,
    List.size_toArray, overflowRegsFrom_length]
  omega

theorem longSendMessage_tail (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (S : SystemState) (s : SeLe4n.ThreadId) (len : Nat) (badge : Option SeLe4n.Badge)
    (hSize : layout.msgRegs.size = 4) :
    (longSendMessage layout rf S s len badge).registers.toList.drop 4 =
      overflowRegsFrom S s 0 (len - 4) := by
  simp only [longSendMessage, Array.toList_append]
  rw [List.drop_append_of_le_length (by simp [Architecture.regMessageRegs, hSize]),
    List.drop_eq_nil_of_le (by simp [Architecture.regMessageRegs, hSize]), List.nil_append]

theorem longSendMessage_word (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (S : SystemState) (s : SeLe4n.ThreadId) (len : Nat) (badge : Option SeLe4n.Badge)
    (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) (i : Nat) (hi : i < 4) :
    (((((longSendMessage layout rf S s len badge).registers)[i]?).map SeLe4n.RegValue.val).getD
        0).toUInt64 = Architecture.regMessageWord layout rf len i := by
  rw [← Architecture.regMessageBody_word]
  have hA : ((longSendMessage layout rf S s len badge).registers)[i]? =
      (Architecture.regMessageBody layout rf len)[i]? := by
    simp only [longSendMessage, Architecture.regMessageBody, Architecture.regMessageRegs]
    rw [Array.getElem?_append_left (by simp [hSize]; omega), Array.getElem?_extract]
    simp only [Array.size_map, hSize]
    rw [if_pos (by simp only [maxMessageRegisters]; omega)]
    simp
  rw [hA]

theorem longSendFrame_eq (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (S : SystemState) (s : SeLe4n.ThreadId) (len k : Nat) (badgeWord : SeLe4n.Badge)
    (badged : Bool) (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    withFrameWords (Architecture.badgeWordIf badgeWord badged) (longMessageInfoWord len k)
        (Architecture.regMessageWord layout rf len 0) (Architecture.regMessageWord layout rf len 1)
        (Architecture.regMessageWord layout rf len 2) (Architecture.regMessageWord layout rf len 3) =
      withFrameWords
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x0
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x1
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x2
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x3
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x4
        (Architecture.returnFrameOfMessage
          (longSendMessage layout rf S s len (SeLe4n.Badge.opt badgeWord badged)) 0 k).x5 := by
  have hB : Architecture.badgeWordIf badgeWord badged =
      ((SeLe4n.Badge.opt badgeWord badged).map SeLe4n.Badge.word).getD 0 := by
    rw [← Architecture.badgeWordOrZero_opt]; rfl
  simp only [Architecture.returnFrameOfMessage,
    longSendMessage_word layout rf S s len _ hSize hLen 0 (by omega),
    longSendMessage_word layout rf S s len _ hSize hLen 1 (by omega),
    longSendMessage_word layout rf S s len _ hSize hLen 2 (by omega),
    longSendMessage_word layout rf S s len _ hSize hLen 3 (by omega), hB]
  congr 1
  simp only [longMessageInfoWord, Architecture.returnMessageInfo,
    longSendMessage_size layout rf S s len _ hSize hLen]
  rfl

/-- **The in-place delivery is the specification's stage** of the long message,
its overflow words read in a state `Y` that reads every buffer as the
delivery's own does. -/
theorem deliverLongSendFrame_eq (X Y : SystemState) (r s : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (hNoX : X.objects.noResizeDue)
    (hA : ipcBufferReadsAgree X Y) (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    deliverLongSendFrame X r layout rf len s badgeWord badged =
      Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage
        (longSendMessage layout rf Y s len (SeLe4n.Badge.opt badgeWord badged)))) r 0 := by
  rw [stageDeliveredMessage_holdMessage_overflow _ r _ _ hNoX
    (longSendMessage_tail layout rf Y s len _ hSize)]
  unfold deliverLongSendFrame
  cases hT : X.getTcb? r with
  | none => rfl
  | some t =>
    simp only []
    split
    · have hX : ∀ j, overflowSlotOf X r j =
          Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun j => by
        simp only [overflowSlotOf, hT]
      have hS : ∀ (a b c d e g : UInt64) j,
          overflowSlotOf (X.mapTcbInPlace r (withFrameWords a b c d e g)) r j =
            Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun a b c d e g j => by
        simp only [overflowSlotOf, SystemState.getTcb?_mapTcbInPlace, hT, Option.map_some]
        exact ipcBufferSlotPAddr?_mapTcbInPlace X r _ t _ j true rfl rfl
      have hAg : ∀ (a b c d e g : UInt64),
          ipcBufferReadsAgree (X.mapTcbInPlace r (withFrameWords a b c d e g)) Y :=
        fun a b c d e g =>
          (ipcBufferReadsAgree_mapTcbInPlace X r (withFrameWords a b c d e g)
            (fun _ => ⟨rfl, rfl⟩)).trans hA
      have hC := overflowSlotsFrom_eq X r X t hX (overflowRegsFrom Y s 0 (len - 4)) 0
      rw [overflowRegsFrom_length] at hC
      rw [overflowCopyStore_eq r s X t Y _ 0 _ (hS _ _ _ _ _ _) (hAg _ _ _ _ _ _), hC,
        longSendFrame_eq layout rf Y s len _ badgeWord badged hSize hLen]
    · unfold holdLongSendMessage longSendMessage
      rw [hA.overflowRegsFrom]

/-- **The long send rendezvous, delivered**: the receiver woken without the
message, then the inline words written into its saved registers and the
overflow words copied from the sender's buffer into its own
(`deliverLongSendFrame`).  The message is built only where the receiver is,
unexpectedly, not ready. -/
@[noinline] def performSendDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (r : SeLe4n.ThreadId) (nextCode : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (s : SeLe4n.ThreadId) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (core : Concurrency.CoreId) : SystemState :=
  deliverLongSendFrame (wakeThread (storeSendRendezvousReady st endpointId r nextCode) r core).1 r
    layout rf len s badgeWord badged

/-! ## The sender's overflow words, as the decode reads them -/

theorem overflowRegsFrom_eq_map (S : SystemState) (s : SeLe4n.ThreadId) :
    ∀ (i n : Nat), overflowRegsFrom S s i n =
      (List.range' i n).map (fun j => (⟨(overflowWordAt S s j).toNat⟩ : SeLe4n.RegValue))
  | _, 0 => rfl
  | i, n + 1 => by
    rw [List.range'_succ, List.map_cons, ← overflowRegsFrom_eq_map S s (i + 1) n]
    rfl

/-- Where every slot from `i` reads, the decode's reads of them are the words
`overflowWordAt` names. -/
theorem mapM_readOverflowWord (S : SystemState) (s : SeLe4n.ThreadId) :
    ∀ (n i : Nat),
      (∀ j, i ≤ j → j < i + n → ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr S s j = .ok w) →
      (List.range' i n).mapM (Architecture.RegisterDecode.readOverflowWord S s) =
        .ok ((List.range' i n).map (overflowWordAt S s))
  | 0, _, _ => rfl
  | n + 1, i, h => by
    obtain ⟨w, hw⟩ := h i (by omega) (by omega)
    have hRest := mapM_readOverflowWord S s n (i + 1)
      (fun j h1 h2 => h j (by omega) (by omega))
    rw [List.range'_succ, List.mapM_cons, List.map_cons, hRest]
    have hW : overflowWordAt S s i = w := by rw [overflowWordAt_eq, hw]
    simp only [Architecture.RegisterDecode.readOverflowWord, hw, hW]
    rfl

/-- Where a slot from `i` does not read, the decode's reads of them are
refused, as the decode refuses any overflow slot it cannot read. -/
theorem mapM_readOverflowWord_error (S : SystemState) (s : SeLe4n.ThreadId) :
    ∀ (n i : Nat), (∃ j e, i ≤ j ∧ j < i + n ∧
        Architecture.IpcBufferRead.ipcBufferReadMr S s j = .error e) →
      (List.range' i n).mapM (Architecture.RegisterDecode.readOverflowWord S s) =
        .error .invalidMessageInfo
  | 0, _, ⟨_, _, h1, h2, _⟩ => by omega
  | n + 1, i, ⟨j, e, h1, h2, hj⟩ => by
    rw [List.range'_succ, List.mapM_cons]
    cases hi : Architecture.IpcBufferRead.ipcBufferReadMr S s i with
    | error e' =>
      simp only [Architecture.RegisterDecode.readOverflowWord, hi]
      rfl
    | ok w =>
      have hji : j ≠ i := by intro h; subst h; rw [hi] at hj; cases hj
      have hRest := mapM_readOverflowWord_error S s n (i + 1) ⟨j, e, by omega, by omega, hj⟩
      simp only [Architecture.RegisterDecode.readOverflowWord, hi, hRest]
      rfl
