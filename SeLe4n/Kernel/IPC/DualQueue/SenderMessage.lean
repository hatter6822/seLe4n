-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Kernel.Architecture.Fault

/-!
# The message a blocked sender holds

WS-ZA ZA4.7.  A sender that blocks keeps its message where seL4 keeps it: the
words in its saved registers and IPC buffer, what its capability contributed
(badge, grant right) in its TCB (`TCB.setSendCap`), and its extra capabilities
as addresses in its own CSpace.  The receive that takes the message reads it
there (`blockedSenderMessage`): the words through the entry's own decoder
(`decodeSyscallArgsFromState`), and the capabilities resolved in the sender's
CSpace at that moment (`resolveExtraCaps`), so a capability revoked while the
sender waits is never transferred.  A fault is the one message the kernel
writes: a thread blocked delivering one carries it as its `pendingFault`
(`TCB.ipcFaultSend`), and the receive builds the message from it
(`faultMessage`), as seL4 does from `tcbFault`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-RR RR4.4: the `IpcMessage` a fault is delivered as.

The encoder (`Architecture.encodeFault`) owns the layout; this is the
model-side envelope: the encoded register array, the encoded `seL4_Fault_tag`
as the message label, the handler capability's badge (seL4 passes
`cap_endpoint_cap_get_capEPBadge(handlerCap)` to `sendIPC`, so a handler
serving several faulting threads through badged capabilities can tell them
apart), and **no capabilities**.

A fault never transfers authority: its send carries no capability request
(`sendPayloadCapRequest` of `.fault` is `none`).  It is a diagnostic report the
kernel writes about a thread, so granting through it would let the *kernel*
hand a handler capabilities the faulting thread never offered — and it is what
makes the RR4.20 non-interference argument about a data flow alone. -/
def faultMessage (f : Fault) (ctx : FaultContext) (badge : Option SeLe4n.Badge) :
    IpcMessage :=
  { registers   := (Architecture.encodeFault f ctx).2
    badge       := badge
    label       := (Architecture.encodeFault f ctx).1.label }

/-- WS-RR RR4.6: the message satisfies the model's payload bound predicate. -/
theorem faultMessage_bounded (f : Fault) (ctx : FaultContext)
    (badge : Option SeLe4n.Badge) : (faultMessage f ctx badge).bounded :=
  Architecture.encodeFault_within_budget f ctx

/-- **The capabilities in the resolved slots, up to the first empty one.**  An
empty slot holds seL4's null capability, which `transferCaps` neither unwraps
nor derives, so the transfer stops there; the slots after it are never read. -/
def extraCapsFromSlots (st : SystemState) : List SlotRef → Array TransferCap → Array TransferCap
  | [], acc => acc
  | ref :: rest, acc =>
    match SystemState.lookupSlotCap st ref with
    | none => acc
    | some cap => extraCapsFromSlots st rest (acc.push (TransferCap.fromSlot cap ref))

/-- **Resolve the extra capability addresses a sender names** (seL4's
`lookupExtraCaps`), in its CSpace from its root capability `root`, at the
rendezvous, each through seL4's `lookupSlot` (`lookupSlotFrom`, 64 bits).

seL4 semantics: the lookup of the addresses is all or nothing — if any address
fails to resolve to a slot, the message carries no capabilities
(`doNormalTransfer` clears the list on a lookup failure).  The capabilities are
then the slots' contents in order, up to the first empty slot, at which seL4's
transfer stops (`extraCapsFromSlots`).  A sender without the grant right
transfers nothing, and its addresses are not looked up at all (PR #873 round 14:
the authority is checked once, where it decides something).

Resolution is a pure read.  Each capability carries the address of the slot it
was read from: the slot is its own derivation node (WS-ZA ZA5.3), so the
transfer that installs it records the edge from that slot, and nothing is
minted here.  A send resolves its addresses at the rendezvous only, so no source
address is ever held across a syscall. -/
def resolveExtraCaps (root : Capability)
    (capAddrs : Array SeLe4n.CPtr) (granted : Bool)
    (st : SystemState) : Array TransferCap :=
  if !granted then #[] else
  match capAddrs.toList.mapM (fun addr => (lookupSlotFrom root addr st).toOption) with
  | none => #[]
  | some refs => extraCapsFromSlots st refs #[]


/-- Every capability `extraCapsFromSlots` collects is the content of the slot it
names. -/
theorem extraCapsFromSlots_slot (st : SystemState) :
    ∀ (refs : List SlotRef) (acc : Array TransferCap),
      (∀ c ∈ acc, SystemState.lookupSlotCap st c.srcSlot = some c.cap) →
      ∀ c ∈ extraCapsFromSlots st refs acc, SystemState.lookupSlotCap st c.srcSlot = some c.cap
  | [], _, hAcc => hAcc
  | ref :: rest, acc, hAcc => by
    unfold extraCapsFromSlots
    split
    · exact hAcc
    · rename_i cap hLk
      refine extraCapsFromSlots_slot st rest _ ?_
      intro c hc
      rcases Array.mem_push.mp hc with hc | rfl
      · exact hAcc c hc
      · exact hLk

/-- **Every resolved capability is the content of its source slot** in the state
it is resolved in. -/
theorem resolveExtraCaps_slot (cspaceRoot : Capability) (capAddrs : Array SeLe4n.CPtr)
    (granted : Bool) (st : SystemState) (c : TransferCap)
    (hc : c ∈ resolveExtraCaps cspaceRoot capAddrs granted st) :
    SystemState.lookupSlotCap st c.srcSlot = some c.cap := by
  unfold resolveExtraCaps at hc
  split at hc
  · simp at hc
  · split at hc
    · simp at hc
    · exact extraCapsFromSlots_slot st _ #[] (by simp) c hc

/-- WS-ZA ZA4.7: the decode of a blocked sender's saved frame — the entry's own
decoder (`decodeSyscallArgsFromState`) on the registers the entry saved
(`registerContext`), with the overflow words read from its IPC buffer. -/
def blockedSenderDecode (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    Except KernelError SyscallDecodeResult :=
  Architecture.RegisterDecode.decodeSyscallArgsFromState st sender
    SeLe4n.arm64DefaultLayout tcb.registerContext 32

/-- WS-ZA ZA4.7: **the message a sender's frame holds**, given the decode of
its saved registers and what its capability contributes: the body cut to the
declared length (`extractMessageRegisters`) and the capability's badge, with
no capabilities (the transfer resolves those, under the grant right, from
`senderFrameCapRequest`).  A frame
that does not decode delivers no words.  The send that meets a waiting receiver
and the receive that takes a blocked sender both read the message here, so the
two arrival orders deliver the same words. -/
@[inline] def senderFrameMessage (decode : Except KernelError SyscallDecodeResult)
    (badge : Option SeLe4n.Badge) : IpcMessage :=
  match decode with
  | .error _ => { IpcMessage.empty with badge := badge }
  | .ok decoded =>
      { registers := Architecture.RegisterDecode.extractMessageRegisters decoded.msgRegs
          decoded.msgInfo,
        badge := badge }

/-- WS-ZA ZA4.7: **the message a blocked sender holds**, given the decode of
its saved frame.

* A thread blocked delivering a fault carries the fault (`pendingFault`), and
  its message is `faultMessage` of it under the handler capability's badge.
* Any other sender's message is its saved frame decoded as the entry decodes
  it: the body cut to the declared length (`extractMessageRegisters`), the
  badge its capability carried.  A frame that no longer
  decodes (its registers were rewritten while it waited) delivers no words.

The extra capabilities are not part of this read: the receive that takes the
message resolves them (`blockedSenderCapRequest`) and installs them in one
step, as the send that meets a waiting receiver does, so no capability is in
flight between syscalls.  The decode is an argument so the live store
(`blockedSenderMessage`) and the frozen one read the message through this one
definition. -/
@[inline] def blockedSenderMessageOf (tcb : TCB)
    (decode : Except KernelError SyscallDecodeResult) : IpcMessage :=
  if tcb.ipcFaultSend then
    match tcb.pendingFault with
    | some tf => faultMessage tf.fault tf.context tcb.ipcBadgeView
    | none => { IpcMessage.empty with badge := tcb.ipcBadgeView }
  else senderFrameMessage decode tcb.ipcBadgeView

/-- WS-ZA ZA4.7: **the message a blocked sender holds**, read at the
rendezvous from where seL4 keeps it (`blockedSenderMessageOf` of the live
decode of its saved frame). -/
def blockedSenderMessage (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    IpcMessage :=
  blockedSenderMessageOf tcb (blockedSenderDecode st sender tcb)

/-- **The address of a sender's extra capability `i`** (seL4's
`getExtraCPtr`): word `i` of its IPC buffer's `caps_or_badges`, read where the
kernel may read the buffer; `none` where the buffer does not resolve. -/
@[inline] def senderExtraCapAddr? (st : SystemState) (tcb : TCB) (i : Nat) : Option SeLe4n.CPtr :=
  (Architecture.IpcBufferRead.ipcBufferWordPAddrIn? st
    (Architecture.IpcBufferRead.lookupIPCBuffer false st tcb)
    (Architecture.IpcBufferRead.ipcBufferCapsOrBadgesWord i)).map
    fun pa => SeLe4n.CPtr.ofWord (Architecture.IpcBufferRead.userWordAt st.machine pa)

/-- **The extra capability addresses a sender names** (seL4's
`lookupExtraCaps` reading `getExtraCPtr`): the first `count` words of its IPC
buffer's `caps_or_badges`.  A sender whose buffer the kernel may not read names
none, and seL4 then transfers no capability; the words lie in one frame
(`ipcBufferWords_within_alignment`), so a buffer resolves all of them or none. -/
def senderExtraCapAddrs (st : SystemState) (tcb : TCB) (count : Nat) : Array SeLe4n.CPtr :=
  match (List.range (min count maxExtraCaps)).mapM (senderExtraCapAddr? st tcb) with
  | some addrs => addrs.toArray
  | none => #[]

/-- A frame that names no extra capability names no address. -/
theorem senderExtraCapAddrs_zero (st : SystemState) (tcb : TCB) :
    senderExtraCapAddrs st tcb 0 = #[] := by
  unfold senderExtraCapAddrs
  rw [Nat.zero_min]
  rfl

/-- The first address a sender names is its `caps_or_badges` word 0. -/
theorem senderExtraCapAddrs_getElem?_zero {st : SystemState} {tcb : TCB} {count : Nat}
    {a : SeLe4n.CPtr} (ha : (senderExtraCapAddrs st tcb count)[0]? = some a) :
    senderExtraCapAddr? st tcb 0 = some a := by
  unfold senderExtraCapAddrs at ha
  cases hn : min count maxExtraCaps with
  | zero => rw [hn] at ha; simp at ha
  | succ n =>
    rw [hn, List.range_succ_eq_map] at ha
    cases h0 : senderExtraCapAddr? st tcb 0 with
    | none => simp [List.mapM_cons, h0] at ha
    | some b =>
      cases hr : (List.map Nat.succ (List.range n)).mapM (senderExtraCapAddr? st tcb) with
      | none => simp [List.mapM_cons, h0, hr] at ha
      | some l => simp [List.mapM_cons, h0, hr] at ha; rw [ha]

/-- **One extra capability an invocation names, looked up** (seL4's
`lookupCapAndSlot` inside `lookupExtraCaps`): the slot the address resolves to
in the caller's CSpace and the capability it holds, `none` for an empty slot
(seL4's null capability, which the invocation's decode then refuses as the
wrong kind).  A failed lookup answers the address and its lookup fault, which
the entry raises as `CapFault(cptr, false)`, the send phase. -/
def lookupExtraCapsOf (st : SystemState) (tcb : TCB) :
    List SeLe4n.CPtr → Except (SeLe4n.CPtr × LookupFault) (List (SlotRef × Option Capability))
  | [] => .ok []
  | cptr :: rest =>
    match lookupSlot tcb cptr st with
    | .error f => .error (cptr, f)
    | .ok ref =>
      match lookupExtraCapsOf st tcb rest with
      | .error e => .error e
      | .ok refs => .ok ((ref, st.lookupSlotCap ref) :: refs)

/-- WS-SX SX6.1: **seL4's `lookupExtraCaps`** (`tcb.c`), run at decode for an
invocation: the first `count` addresses of the caller's IPC buffer
`caps_or_badges` (`senderExtraCapAddrs`, at most `maxExtraCaps`, none where the
buffer does not resolve, as seL4's null buffer names none), each looked up in
the caller's CSpace (`lookupExtraCapsOf`).  IPC transfers still look their
capabilities up at the rendezvous (`resolveExtraCaps`, seL4's `thread.c`). -/
def lookupExtraCaps (st : SystemState) (tcb : TCB) (count : Nat) :
    Except (SeLe4n.CPtr × LookupFault) (List (SlotRef × Option Capability)) :=
  lookupExtraCapsOf st tcb (senderExtraCapAddrs st tcb count).toList

/-- A looked-up list has one entry per address. -/
theorem lookupExtraCapsOf_length {st : SystemState} {tcb : TCB} :
    ∀ {addrs : List SeLe4n.CPtr} {refs : List (SlotRef × Option Capability)},
      lookupExtraCapsOf st tcb addrs = .ok refs → refs.length = addrs.length
  | [], refs, h => by simp only [lookupExtraCapsOf, Except.ok.injEq] at h; subst h; rfl
  | cptr :: rest, refs, h => by
    unfold lookupExtraCapsOf at h
    split at h
    · cases h
    · split at h
      · cases h
      · next refs' hR =>
        simp only [Except.ok.injEq] at h; subst h
        simp only [List.length_cons, lookupExtraCapsOf_length hR]

/-- Each entry is the slot its address resolves to, and that slot's capability. -/
theorem lookupExtraCapsOf_getElem? {st : SystemState} {tcb : TCB} :
    ∀ {addrs : List SeLe4n.CPtr} {refs : List (SlotRef × Option Capability)} {i : Nat}
      {cptr : SeLe4n.CPtr},
      lookupExtraCapsOf st tcb addrs = .ok refs → addrs[i]? = some cptr →
      ∃ ref, lookupSlot tcb cptr st = .ok ref ∧ refs[i]? = some (ref, st.lookupSlotCap ref)
  | [], _, _, _, _, h => by simp at h
  | c :: rest, refs, i, cptr, h, hi => by
    unfold lookupExtraCapsOf at h
    split at h
    · cases h
    · next ref hL =>
      split at h
      · cases h
      · next refs' hR =>
        simp only [Except.ok.injEq] at h; subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
          exact ⟨ref, hL, rfl⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact lookupExtraCapsOf_getElem? hR hi

/-- A failed lookup names an address of the list and its fault. -/
theorem lookupExtraCapsOf_error {st : SystemState} {tcb : TCB} :
    ∀ {addrs : List SeLe4n.CPtr} {cptr : SeLe4n.CPtr} {f : LookupFault},
      lookupExtraCapsOf st tcb addrs = .error (cptr, f) →
      cptr ∈ addrs ∧ lookupSlot tcb cptr st = .error f
  | [], _, _, h => by simp [lookupExtraCapsOf] at h
  | c :: rest, cptr, f, h => by
    unfold lookupExtraCapsOf at h
    split at h
    · next f' hL =>
      simp only [Except.error.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self .., hL⟩
    · split at h
      · next e hR =>
        simp only [Except.error.injEq] at h; subst h
        obtain ⟨hm, hf⟩ := lookupExtraCapsOf_error hR
        exact ⟨List.mem_cons_of_mem _ hm, hf⟩
      · cases h

/-- A frame that names no extra capability looks none up. -/
theorem lookupExtraCaps_zero (st : SystemState) (tcb : TCB) :
    lookupExtraCaps st tcb 0 = .ok [] := by
  unfold lookupExtraCaps; rw [senderExtraCapAddrs_zero]; rfl

/-- Whether the `caps_or_badges` words `i, …, i + k - 1` of a sender's IPC
buffer all resolve (`senderExtraCapAddr?`): a counted loop over the words,
building no list. -/
def extraCapAddrsResolveFrom (st : SystemState) (tcb : TCB) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => (senderExtraCapAddr? st tcb i).isSome && extraCapAddrsResolveFrom st tcb (i + 1) k

/-- **The first of the extra capabilities `i, …, i + k - 1` whose lookup
fails**, `i + k` when every one resolves: each word read and walked
(`lookupSlotK`) in turn, a counted loop that returns a number, so no address
array, slot list or continuation is built.  Read where every word resolves
(`extraCapAddrsResolveFrom`, `extraCapsFailFrom_spec`). -/
def extraCapsFailFrom (st : SystemState) (tcb : TCB) : Nat → Nat → Nat
  | i, 0 => i
  | i, k + 1 =>
    match senderExtraCapAddr? st tcb i with
    | none => i + (k + 1)
    | some cptr =>
      lookupSlotK tcb cptr st (fun _ _ _ _ => i)
        (fun _ _ => extraCapsFailFrom st tcb (i + 1) k)

/-- WS-SX SX6.1: **seL4's `lookupExtraCaps` as the entry runs it**: the
`count` extra capabilities (at most `maxExtraCaps`) read word by word and
looked up in turn (`extraCapsFailFrom`); the first that fails is walked again
for its lookup-fault words, handed to `onErr` with its address, and `onOk`
runs otherwise; a buffer that does not resolve names none.  The arm after it
is `onOk ()`, one join point the compiled entry jumps to.  The allocation-free
form of `lookupExtraCaps` (`extraCapsLookupK_eq`). -/
@[inline] def extraCapsLookupK {α : Type} (st : SystemState) (tcb : TCB) (count : Nat)
    (onErr : SeLe4n.CPtr → UInt64 → UInt64 → UInt64 → UInt64 → α) (onOk : Unit → α) : α :=
  let n := min count maxExtraCaps
  let i := if extraCapAddrsResolveFrom st tcb 0 n then extraCapsFailFrom st tcb 0 n else n
  if i < n then
    match senderExtraCapAddr? st tcb i with
    | some cptr => lookupSlotK tcb cptr st (onErr cptr) (fun _ _ => onOk ())
    | none => onOk ()
  else onOk ()

theorem extraCapAddrs_mapM_none {st : SystemState} {tcb : TCB} :
    ∀ {i k : Nat}, extraCapAddrsResolveFrom st tcb i k = false →
      (List.range' i k).mapM (senderExtraCapAddr? st tcb) = none
  | _, 0, h => by simp [extraCapAddrsResolveFrom] at h
  | i, k + 1, h => by
    simp only [extraCapAddrsResolveFrom, Bool.and_eq_false_iff] at h
    rw [List.range'_succ, List.mapM_cons]
    cases hA : senderExtraCapAddr? st tcb i with
    | none => rfl
    | some c =>
      rw [hA] at h
      have hR : extraCapAddrsResolveFrom st tcb (i + 1) k = false := by
        rcases h with h | h
        · simp at h
        · exact h
      rw [extraCapAddrs_mapM_none hR]; rfl

/-- Where every word resolves, `extraCapsFailFrom` is the index of the first
address whose lookup fails, with that address and its lookup fault, or `i + k`
when every lookup succeeds. -/
theorem extraCapsFailFrom_spec {st : SystemState} {tcb : TCB} :
    ∀ {i k : Nat}, extraCapAddrsResolveFrom st tcb i k = true →
      ∃ addrs, (List.range' i k).mapM (senderExtraCapAddr? st tcb) = some addrs ∧
        (∀ cptr f, lookupExtraCapsOf st tcb addrs = .error (cptr, f) →
          i ≤ extraCapsFailFrom st tcb i k ∧ extraCapsFailFrom st tcb i k < i + k ∧
          senderExtraCapAddr? st tcb (extraCapsFailFrom st tcb i k) = some cptr ∧
          lookupSlot tcb cptr st = .error f) ∧
        (∀ refs, lookupExtraCapsOf st tcb addrs = .ok refs →
          extraCapsFailFrom st tcb i k = i + k)
  | i, 0, _ => ⟨[], rfl, fun _ _ h => by simp [lookupExtraCapsOf] at h, fun _ _ => rfl⟩
  | i, k + 1, h => by
    simp only [extraCapAddrsResolveFrom, Bool.and_eq_true] at h
    obtain ⟨hA, hR⟩ := h
    obtain ⟨rest, hRest, hE, hO⟩ := extraCapsFailFrom_spec hR
    cases hC : senderExtraCapAddr? st tcb i with
    | none => rw [hC] at hA; cases hA
    | some c =>
      refine ⟨c :: rest, ?_, ?_, ?_⟩
      · rw [List.range'_succ, List.mapM_cons, hC, hRest]; rfl
      · intro cptr f hL
        simp only [extraCapsFailFrom, hC, lookupSlotK_eq]
        simp only [lookupExtraCapsOf] at hL
        cases hS : lookupSlot tcb c st with
        | error f0 =>
          rw [hS] at hL; cases hL
          dsimp only
          exact ⟨Nat.le_refl _, by omega, hC, hS⟩
        | ok ref =>
          rw [hS] at hL
          dsimp only
          cases hL' : lookupExtraCapsOf st tcb rest with
          | error e =>
            rw [hL'] at hL; cases hL
            obtain ⟨h1, h2, h3, h4⟩ := hE _ _ hL'
            exact ⟨by omega, by omega, h3, h4⟩
          | ok _ => rw [hL'] at hL; cases hL
      · intro refs hL
        simp only [extraCapsFailFrom, hC, lookupSlotK_eq]
        simp only [lookupExtraCapsOf] at hL
        cases hS : lookupSlot tcb c st with
        | error f0 => rw [hS] at hL; cases hL
        | ok ref =>
          rw [hS] at hL
          cases hL' : lookupExtraCapsOf st tcb rest with
          | error e => rw [hL'] at hL; cases hL
          | ok r => dsimp only; rw [hO r hL']; omega

/-- **The entry's lookup is seL4's `lookupExtraCaps`.** -/
theorem extraCapsLookupK_eq {α : Type} (st : SystemState) (tcb : TCB) (count : Nat)
    (onErr : SeLe4n.CPtr → UInt64 → UInt64 → UInt64 → UInt64 → α) (onOk : Unit → α) :
    extraCapsLookupK st tcb count onErr onOk =
      match lookupExtraCaps st tcb count with
      | .error (cptr, f) => onErr cptr (f.word 0) (f.word 1) (f.word 2) (f.word 3)
      | .ok _ => onOk () := by
  unfold extraCapsLookupK lookupExtraCaps senderExtraCapAddrs
  rw [List.range_eq_range']
  cases hR : extraCapAddrsResolveFrom st tcb 0 (min count maxExtraCaps) with
  | false =>
    simp only [hR, extraCapAddrs_mapM_none hR, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl]
    rfl
  | true =>
    obtain ⟨addrs, hM, hE, hO⟩ := extraCapsFailFrom_spec hR
    simp only [↓reduceIte, hM, List.toList_toArray]
    cases hL : lookupExtraCapsOf st tcb addrs with
    | error e =>
      obtain ⟨cptr, f⟩ := e
      obtain ⟨-, h2, h3, h4⟩ := hE cptr f hL
      have h2' : extraCapsFailFrom st tcb 0 (min count maxExtraCaps) < min count maxExtraCaps := by
        omega
      simp only [hR, h2', ↓reduceIte, h3, lookupSlotK_eq, h4]
    | ok refs =>
      have h0 := hO refs hL
      simp only [Nat.zero_add] at h0
      simp only [hR, h0, Nat.lt_irrefl, ↓reduceIte]

/-- WS-SX SX6.1: **the extra-capability lookup failure an invocation raises**
(seL4's `lookupExtraCaps` setting `current_fault` to `CapFault(cptr, false)`):
the first extra capability address that does not resolve, and its lookup
fault; `none` when every one resolves. -/
def extraCapsLookupFault? (st : SystemState) (tcb : TCB) (count : Nat) :
    Option (SeLe4n.CPtr × LookupFault) :=
  match lookupExtraCaps st tcb count with
  | .error e => some e
  | .ok _ => none

/-- The extra capabilities' lookups read only the CNodes and the slots. -/
theorem lookupExtraCapsOf_congr (st₁ st₂ : SystemState)
    (hCNode : ∀ id, st₁.getCNode? id = st₂.getCNode? id)
    (hSlot : ∀ ref, st₁.lookupSlotCap ref = st₂.lookupSlotCap ref) (tcb : TCB) :
    ∀ addrs, lookupExtraCapsOf st₁ tcb addrs = lookupExtraCapsOf st₂ tcb addrs
  | [] => rfl
  | cptr :: rest => by
    simp only [lookupExtraCapsOf, lookupSlot_congr_getCNode? st₁ st₂ hCNode tcb cptr, hSlot,
      lookupExtraCapsOf_congr st₁ st₂ hCNode hSlot tcb rest]

/-- **A TLB fill leaves the extra capabilities' lookup alone**: it reads the
objects and memory, never the per-core TLBs. -/
theorem lookupExtraCaps_perCoreTlb (st : SystemState) (tcb : TCB) (n : Nat)
    (t : Vector TlbState Concurrency.numCores) :
    lookupExtraCaps { st with perCoreTlb := t } tcb n = lookupExtraCaps st tcb n := by
  unfold lookupExtraCaps
  rw [show senderExtraCapAddrs { st with perCoreTlb := t } tcb n = senderExtraCapAddrs st tcb n
    from rfl]
  exact lookupExtraCapsOf_congr { st with perCoreTlb := t } st (fun _ => rfl) (fun _ => rfl) tcb _

theorem extraCapsLookupFault?_perCoreTlb (st : SystemState) (tcb : TCB) (n : Nat)
    (t : Vector TlbState Concurrency.numCores) :
    extraCapsLookupFault? { st with perCoreTlb := t } tcb n = extraCapsLookupFault? st tcb n := by
  simp only [extraCapsLookupFault?, lookupExtraCaps_perCoreTlb]

/-- **The extra-capability lookup failure a caller's invocation raises**
(`extraCapsLookupFault?`), read from the caller's TCB on the state the gate
runs on: the first of its `n` extra capabilities whose address does not
resolve, with its lookup fault; `none` when every one resolves or the caller
is no thread. -/
def callerExtraCapsFault? (st : SystemState) (tid : SeLe4n.ThreadId) (n : Nat) :
    Option (SeLe4n.CPtr × LookupFault) :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) => extraCapsLookupFault? st tcb n
  | _ => none

/-- **The address of a caller's extra capability `i`** (seL4's
`current_extra_caps.excaprefs[i]`, read by `getExtraCPtr`): word `i` of its IPC
buffer's `caps_or_badges` when its message names more than `i` extra
capabilities (`n`, at most `maxExtraCaps`); `none` when it names fewer, when its
buffer does not resolve (seL4's null buffer names none), or when the caller is
no thread.  The dispatch prologue has looked every named one up
(`lookupExtraCaps`), so an invocation that reads one reads an address that
resolves. -/
@[inline] def callerExtraCapAddr? (st : SystemState) (tid : SeLe4n.ThreadId) (n i : Nat) :
    Option SeLe4n.CPtr :=
  if i < min n maxExtraCaps then
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) => senderExtraCapAddr? st tcb i
    | _ => none
  else none

/-- A message that names no extra capability names no address. -/
theorem callerExtraCapAddr?_zero (st : SystemState) (tid : SeLe4n.ThreadId) (i : Nat) :
    callerExtraCapAddr? st tid 0 i = none := by
  unfold callerExtraCapAddr?
  rw [Nat.zero_min, if_neg (Nat.not_lt_zero i)]

/-- **The dispatch runs the receive arm with no reply leg**: a `.receive`, or
a `.replyRecv` whose message names an extra capability that does not look up
(seL4-MCS `SysReplyRecv`: `handleInvocation` with `isBlocking = false` skips the
reply with no fault, and `handleRecv` still runs). -/
def receivesWithoutReply (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (st : SystemState) : Prop :=
  decoded.syscallId = .receive ∨
    (decoded.syscallId = .replyRecv ∧
      (callerExtraCapsFault? st tid decoded.msgInfo.extraCaps).isSome)

/-- **Whether a caller's extra capabilities fail, in continuation form**
(`callerExtraCapsFault?`, `callerExtraCapsFailK_eq`): `onFail` when one of the
`n` the caller's message names does not look up, `onOk` otherwise, through the
allocation-free `extraCapsLookupK`, so nothing is built. -/
@[inline] def callerExtraCapsFailK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (n : Nat) (onFail onOk : Unit → α) : α :=
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) => extraCapsLookupK st tcb n (fun _ _ _ _ _ => onFail ()) onOk
  | _ => onOk ()

theorem callerExtraCapsFailK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId) (n : Nat)
    (onFail onOk : Unit → α) :
    callerExtraCapsFailK st tid n onFail onOk =
      match callerExtraCapsFault? st tid n with
      | some _ => onFail ()
      | none => onOk () := by
  unfold callerExtraCapsFailK callerExtraCapsFault? extraCapsLookupFault?
  split
  · rw [extraCapsLookupK_eq]
    cases lookupExtraCaps st _ n <;> rfl
  · rfl

theorem extraCapsLookupFault?_zero (st : SystemState) (tcb : TCB) :
    extraCapsLookupFault? st tcb 0 = none := by
  simp only [extraCapsLookupFault?, lookupExtraCaps_zero]

/-- WS-ZA ZA4.7: **the capabilities a sender's frame asks to transfer**, as the
CSpace root capability and the addresses it resolves (at 64 bits) -- or
`none` when it transfers nothing: no grant right, a frame that does not decode,
no capability addresses, or no CSpace root capability.  The send that meets a
waiting receiver and the receive that takes a blocked sender both resolve this
request at the rendezvous (`receiveTransferCaps`), so no capability is looked up
on the arm that blocks. -/
def senderFrameCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB)
    (grant : Bool) : Option (Capability × Array SeLe4n.CPtr) :=
  if !grant then none else
  match blockedSenderDecode st sender tcb with
  | .error _ => none
  | .ok decoded =>
      let addrs := senderExtraCapAddrs st tcb decoded.msgInfo.extraCaps
      if addrs.isEmpty then none else
      match tcb.spaceCells[0] with
      | some root => some (root, addrs)
      | none => none


/-- A message-info word that decodes carries the extra-capability count its
bits 7..8 hold. -/
theorem decodeMsgInfoWord_extraCaps {w : UInt64} {mi : MessageInfo}
    (h : Architecture.RegisterDecode.decodeMsgInfoWord w = .ok mi) :
    mi.extraCaps = ((w >>> 7) &&& 3).toNat := by
  unfold Architecture.RegisterDecode.decodeMsgInfoWord at h
  split at h
  · cases h; rfl
  · cases h

/-- A register decode that succeeds took its message info from the layout's
message-info register. -/
theorem decodeSyscallArgs_msgInfo {layout : SeLe4n.SyscallRegisterLayout}
    {regs : SeLe4n.RegisterFile} {n : Nat} {d : SyscallDecodeResult}
    (h : Architecture.RegisterDecode.decodeSyscallArgs layout regs n = .ok d) :
    Architecture.RegisterDecode.decodeMsgInfo (SeLe4n.readReg regs layout.msgInfoReg)
      = .ok d.msgInfo := by
  unfold Architecture.RegisterDecode.decodeSyscallArgs at h
  cases hM : Architecture.RegisterDecode.decodeMsgInfo (SeLe4n.readReg regs layout.msgInfoReg) with
  | error e =>
    simp only [hM, bind, Except.bind, pure, Except.pure] at h
    repeat (first | (split at h <;> try cases h))
  | ok mi =>
    simp only [hM, bind, Except.bind, pure, Except.pure] at h
    repeat (first | (split at h <;> try cases h))
    all_goals rfl

/-- And so does the state-aware decode, up to its length: the overflow merge
keeps the base decode's message info, and a message the buffer cannot supply is
clamped to its inline words (`clampToInline`), its label and capability count
kept. -/
theorem decodeSyscallArgsFromState_msgInfo {st : SystemState} {tid : SeLe4n.ThreadId}
    {layout : SeLe4n.SyscallRegisterLayout} {regs : SeLe4n.RegisterFile}
    {n : Nat} {d : SyscallDecodeResult}
    (h : Architecture.RegisterDecode.decodeSyscallArgsFromState st tid layout regs n = .ok d) :
    ∃ mi, Architecture.RegisterDecode.decodeMsgInfo (SeLe4n.readReg regs layout.msgInfoReg)
      = .ok mi ∧ d.msgInfo.extraCaps = mi.extraCaps ∧ d.msgInfo.label = mi.label := by
  unfold Architecture.RegisterDecode.decodeSyscallArgsFromState at h
  cases hB : Architecture.RegisterDecode.decodeSyscallArgs layout regs n with
  | error e => simp only [hB, bind, Except.bind] at h; cases h
  | ok base =>
    have hb := decodeSyscallArgs_msgInfo hB
    simp only [hB, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h; exact ⟨_, hb, rfl, rfl⟩
    · split at h
      · split at h
        · cases h; exact ⟨_, hb, rfl, rfl⟩
        · cases h; exact ⟨_, hb, rfl, rfl⟩
      · cases h; exact ⟨_, hb, rfl, rfl⟩

/-- **A saved frame names no extra capability, decided on its message-info
word** (seL4's `seL4_MessageInfo_get_extraCaps`, bits 7..8 of the word the
entry saved): a scalar test on one register, with nothing built. -/
@[inline] def frameNamesNoExtraCapsW (tcb : TCB) : Bool :=
  ((SeLe4n.readRegWord tcb.registerContext SeLe4n.arm64DefaultLayout.msgInfoReg >>> 7)
    &&& 3) == 0

/-- **A frame that names no extra capability asks to transfer none**, whatever
the grant right: a frame that decodes carries the word's count, zero, and so
names no address (`senderExtraCapAddrs_zero`); one that does not decode asks
for nothing either. -/
theorem senderFrameCapRequest_of_noExtraCaps {st : SystemState} {sender : SeLe4n.ThreadId}
    {tcb : TCB} (grant : Bool) (h : frameNamesNoExtraCapsW tcb = true) :
    senderFrameCapRequest st sender tcb grant = none := by
  unfold senderFrameCapRequest
  cases grant
  · rfl
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hD : blockedSenderDecode st sender tcb with
  | error _ => rfl
  | ok d =>
    obtain ⟨mi, hM, hX, -⟩ := decodeSyscallArgsFromState_msgInfo hD
    rw [← Architecture.RegisterDecode.decodeMsgInfoWord_readReg] at hM
    have hE := decodeMsgInfoWord_extraCaps hM
    unfold frameNamesNoExtraCapsW at h
    rw [beq_iff_eq.mp h] at hE
    simp only [hX, hE, UInt64.toNat_zero, senderExtraCapAddrs_zero, Array.isEmpty_empty, ↓reduceIte]
/-- WS-ZA ZA4.7: **the capabilities a blocked sender asks to transfer**, as the
CSpace root capability and the addresses it resolves (at 64 bits) -- or
`none` when it transfers nothing: a fault message, a sender without the grant
right, a frame that no longer decodes, no capability addresses, or a missing
CSpace root.  `resolveExtraCaps` of the request is what the receive installs;
`receiveInstallsCaps` is this function's `isSome`, so the receive's lock
footprint and its install read one answer. -/
def blockedSenderCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    Option (Capability × Array SeLe4n.CPtr) :=
  if tcb.ipcFaultSend then none else senderFrameCapRequest st sender tcb tcb.ipcCanGrant

/-- WS-ZA ZA4.7: and it is within the payload bound: a fault encodes inside the
budget, and a decoded body is cut to at most `maxMessageRegisters` words. -/
theorem blockedSenderMessage_bounded (st : SystemState) (sender : SeLe4n.ThreadId)
    (tcb : TCB) : (blockedSenderMessage st sender tcb).bounded := by
  unfold blockedSenderMessage blockedSenderMessageOf senderFrameMessage
  split
  · split
    · exact Architecture.encodeFault_within_budget _ _
    · simp [IpcMessage.empty, IpcMessage.bounded]
  · split
    · simp [IpcMessage.empty, IpcMessage.bounded]
    · exact Architecture.RegisterDecode.extractMessageRegisters_length _ _


/-- WS-ZA ZA4.7: **what a send carries in from its capability** -- all a send
or call is handed, as seL4's `sendIPC` is handed only the badge and the grant
right.  The words are not part of it: they are in the sender's saved registers
and IPC buffer, and whichever arm delivers them reads them there
(`sendPayloadMessage`), so a send that meets a waiting receiver and one that
blocks until a receive takes it deliver the same words.

* `frame badge grant` -- an ordinary send: the message is the sender's frame
  (`senderFrameMessage`) under its capability's badge; the grant right decides
  only the capability request (`sendPayloadCapRequest`).
* `fault f ctx badge` -- the one message the kernel writes: a fault, delivered
  under the handler capability's badge (`faultMessage`). -/
inductive SendPayload where
  | frame (badge : Option SeLe4n.Badge) (grant : Bool)
  | fault (f : Fault) (ctx : FaultContext) (badge : Option SeLe4n.Badge)

/-- The badge a send's capability carries. -/
@[inline] def SendPayload.badge : SendPayload → Option SeLe4n.Badge
  | .frame b _ => b
  | .fault _ _ b => b

/-- Whether a send may transfer capabilities: an ordinary send whose capability
had the grant right; a fault never transfers authority. -/
@[inline] def SendPayload.grant : SendPayload → Bool
  | .frame _ g => g
  | .fault _ _ _ => false

/-- WS-ZA ZA4.7: the decode of a sender's saved frame, looked up by its id: a
thread that does not exist has no frame, and its decode is a refusal. -/
def senderFrameDecode (st : SystemState) (sender : SeLe4n.ThreadId) :
    Except KernelError SyscallDecodeResult :=
  match st.getTcb? sender with
  | some tcb => blockedSenderDecode st sender tcb
  | none => .error .objectNotFound

/-- WS-ZA ZA4.7: **the message a send delivers** to a waiting receiver: the
fault message for a fault, otherwise the sender's frame under its capability's
badge -- the same read the receive that takes a blocked sender
makes (`sendPayloadMessage_frame_eq_blockedSenderMessage`). -/
@[inline] def sendPayloadMessage (st : SystemState) (sender : SeLe4n.ThreadId) :
    SendPayload → IpcMessage
  | .frame b _ => senderFrameMessage (senderFrameDecode st sender) b
  | .fault f ctx b => faultMessage f ctx b

/-- WS-ZA ZA4.7: **the capabilities a send transfers** to a waiting receiver:
the frame's request (`senderFrameCapRequest`) under the capability's grant
right, none for a fault. -/
def sendPayloadCapRequest (st : SystemState) (sender : SeLe4n.ThreadId) (tcb : TCB) :
    SendPayload → Option (Capability × Array SeLe4n.CPtr)
  | .frame _ g => senderFrameCapRequest st sender tcb g
  | .fault _ _ _ => none

/-- WS-ZA ZA4.7: **both arrival orders deliver one message**: an ordinary send
that blocks records its capability's badge and grant right (`TCB.setSendCap`),
and the receive that takes it reads what the send to a waiting receiver
delivers. -/
theorem sendPayloadMessage_frame_eq_blockedSenderMessage (st : SystemState)
    (sender : SeLe4n.ThreadId) (tcb : TCB) (badge : Option SeLe4n.Badge) (grant : Bool)
    (hT : st.getTcb? sender = some tcb) :
    blockedSenderMessageOf (tcb.setSendCap badge grant) (blockedSenderDecode st sender tcb) =
      sendPayloadMessage st sender (.frame badge grant) := by
  simp [blockedSenderMessageOf, sendPayloadMessage, senderFrameDecode, hT]

/-- WS-ZA ZA4.7: and it is within the payload bound. -/
theorem sendPayloadMessage_bounded (st : SystemState) (sender : SeLe4n.ThreadId)
    (p : SendPayload) : (sendPayloadMessage st sender p).bounded := by
  cases p with
  | frame b g =>
    simp only [sendPayloadMessage, senderFrameMessage]
    split
    · simp [IpcMessage.empty, IpcMessage.bounded]
    · exact Architecture.RegisterDecode.extractMessageRegisters_length _ _
  | fault f ctx b => exact faultMessage_bounded f ctx b

end SeLe4n.Kernel
