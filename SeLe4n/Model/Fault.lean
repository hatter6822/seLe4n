-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Model.KernelError

/-!
# WS-RR RR4.1/RR4.2 — the `Fault` value a thread carries

The fault *value* is model data, not architecture: seL4 declares
`seL4_Fault_t` in the shared `shared_types.bf` and stores it in the generic
TCB as `tcbFault`, with only the VM-fault arm's payload arch-specific.  This
module is the same split — `Fault` and its `FaultContext` live here, below
`Model/Object/Types.lean`, so `TCB.pendingFault` can carry them; the ESR_EL1
classification that *produces* a fault and the wire format that *delivers* it
stay in `SeLe4n/Kernel/Architecture/Fault.lean`, which is where the ARM64
detail belongs.

Without a TCB field there is no fault handling at all, only fault *reporting*:
a reply to a fault message has to know which fault it answers before it can
decide between resume, restart and abandon (seL4's `handleFaultReply` switches
on `receiver->tcbFault`), and the restart has to know the register context the
fault was taken in.
-/

namespace SeLe4n.Model

open SeLe4n

-- ============================================================================
-- §1  RR4.1 — the `Fault` inductive
-- ============================================================================

/-- WS-RR RR4.1: a kernel-visible thread fault, at seL4 parity.

One constructor per `seL4_Fault_t` tag the kernel raises for a user thread,
each carrying **the fault-specific payload its message needs** — the
contextual words (restart PC, SP, LR, SPSR, `x0`-`x7`) come from the faulting
thread's saved register file and are spliced in by
`Architecture.encodeFault`, exactly as seL4's `setMRs_fault` splices
`getRestartPC(sender)`.

* `vmFault` — a data or instruction abort.  `address` is FAR_EL1, `status`
  the ESR_EL1 syndrome seL4 reports as `seL4_VMFault_FSR` (on AArch64
  `getDFSR()`/`getIFSR()` both read ESR_EL1 whole), and `prefetch` is
  seL4's `instructionFault` flag: `true` for an instruction abort, which is
  what tells a handler to map an executable page rather than a data page.
* `capFault` — a capability lookup that failed on a path with no syscall
  return to fail into (the IPC receive phase, or a fault-handler lookup).
  `capAddress` is the CPtr that failed to resolve, `inReceivePhase`
  seL4's `seL4_CapFault_InRecvPhase`, and `lookupFailure` the reason.

  seL4 carries the reason as a separate `lookup_fault_t` with its own
  four-word tail; this model already has a total, typed vocabulary for
  exactly that — the `KernelError` `resolveCapAddress` returns — so the
  reason rides as that error rather than as a second inductive whose
  constructors would duplicate it.  Nothing is dropped: the discriminant
  encoding is the one `KernelError.toDiscriminant` pins, and
  `KernelError.ofDiscriminant?` inverts it.
* `unknownSyscall` — a syscall number outside the kernel's ABI.  The
  syscall number is the fault-specific word; the whole `x0`-`x7` window
  rides as context, so a handler can emulate the call and reply with the
  registers the emulation produced.
* `userException` — an alignment fault, an undefined instruction, or any
  synchronous exception the kernel does not model.  `number` is the
  ESR_EL1 exception class and `code` the whole syndrome word. -/
inductive Fault where
  | vmFault (address : UInt64) (status : UInt64) (prefetch : Bool)
  | capFault (capAddress : UInt64) (inReceivePhase : Bool)
      (lookupFailure : KernelError)
  | unknownSyscall (syscallNumber : UInt64)
  | userException (number : UInt64) (code : UInt64)
  deriving Repr, DecidableEq

/-- WS-RR RR4.2: the default fault is the null VM fault — a fault value is
never `default` on any kernel path, but `Inhabited` lets `Fault` sit inside
`getD`-style total readers. -/
instance : Inhabited Fault := ⟨.vmFault 0 0 false⟩

/-- WS-RR RR4.2: `BEq` derived from the decidable equality, so the two agree
by construction rather than by a second hand-written traversal. -/
instance : BEq Fault := instBEqOfDecidableEq

/-- WS-RR RR4.2: and the agreement, as an instance — `f == g` reflects
`f = g`, which is what lets a `==` guard in executable code stand in for a
propositional hypothesis in the proofs about it. -/
instance : LawfulBEq Fault := inferInstance

namespace Fault

/-- WS-RR RR4.2 (congruence): two `vmFault`s are equal exactly when all three
payload fields agree. -/
@[simp] theorem vmFault_inj {a₁ a₂ s₁ s₂ : UInt64} {p₁ p₂ : Bool} :
    Fault.vmFault a₁ s₁ p₁ = Fault.vmFault a₂ s₂ p₂ ↔ a₁ = a₂ ∧ s₁ = s₂ ∧ p₁ = p₂ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- WS-RR RR4.2 (congruence): `capFault` injectivity. -/
@[simp] theorem capFault_inj {a₁ a₂ : UInt64} {r₁ r₂ : Bool} {e₁ e₂ : KernelError} :
    Fault.capFault a₁ r₁ e₁ = Fault.capFault a₂ r₂ e₂ ↔ a₁ = a₂ ∧ r₁ = r₂ ∧ e₁ = e₂ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- WS-RR RR4.2 (congruence): `unknownSyscall` injectivity. -/
@[simp] theorem unknownSyscall_inj {n₁ n₂ : UInt64} :
    Fault.unknownSyscall n₁ = Fault.unknownSyscall n₂ ↔ n₁ = n₂ := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

/-- WS-RR RR4.2 (congruence): `userException` injectivity. -/
@[simp] theorem userException_inj {n₁ n₂ c₁ c₂ : UInt64} :
    Fault.userException n₁ c₁ = Fault.userException n₂ c₂ ↔ n₁ = n₂ ∧ c₁ = c₂ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- WS-RR RR4.2: the four constructors are pairwise distinct — the property a
label-keyed decoder relies on (a decoded label picks exactly one arm). -/
theorem constructors_pairwise_distinct
    (a s : UInt64) (p : Bool) (ca : UInt64) (rp : Bool) (e : KernelError)
    (n : UInt64) (un cd : UInt64) :
    Fault.vmFault a s p ≠ Fault.capFault ca rp e ∧
    Fault.vmFault a s p ≠ Fault.unknownSyscall n ∧
    Fault.vmFault a s p ≠ Fault.userException un cd ∧
    Fault.capFault ca rp e ≠ Fault.unknownSyscall n ∧
    Fault.capFault ca rp e ≠ Fault.userException un cd ∧
    Fault.unknownSyscall n ≠ Fault.userException un cd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> cases h

end Fault

-- ============================================================================
-- §2  The contextual half of a fault message
-- ============================================================================

/-- WS-RR RR4.4: the faulting thread's saved context, as the fault-message
encoder consumes it and the fault-reply restart writes it back.

seL4's `setMRs_fault` reads these words straight off the faulting TCB
(`getRestartPC`, `getRegister(sender, SP_EL0)`, `…LR`, `…SPSR_EL1`, and
`x0`-`x7` for the unknown-syscall message).  Keeping them in a separate
record — rather than as extra `Fault` constructor fields — is what makes the
RR4.5 round trip a statement about the *fault*:
`Architecture.decodeFault` recovers the fault whatever context was spliced
in, because every fault-specific word sits at an index no contextual word
occupies. -/
structure FaultContext where
  /-- The instruction the thread must be restarted at — seL4's
      `getRestartPC(sender)`.  For an abort this is `ELR_EL1`, which on
      AArch64 addresses the faulting instruction itself. -/
  faultIP : UInt64 := 0
  /-- The faulting thread's user stack pointer (`SP_EL0`). -/
  sp : UInt64 := 0
  /-- The faulting thread's link register (`x30`). -/
  lr : UInt64 := 0
  /-- Saved PSTATE (`SPSR_EL1`).  Carried **outbound only**: the fault
      message reports it so a handler can diagnose the trap, and no reply
      path writes it back.  seL4 does allow a handler to rewrite PSTATE on an
      unknown-syscall reply, behind `sanitiseRegister`'s mask; this model has
      no PSTATE field in `RegisterFile` to write it into, and refusing the
      override is the fail-closed direction — a handler can move a thread's
      PC, SP and arguments, never its privilege or interrupt-mask bits. -/
  spsr : UInt64 := 0
  /-- The argument window `x0`-`x7` at the fault.  Only the unknown-syscall
      message carries it (so a handler can emulate the call); shorter arrays
      read as zero through `gprAt`, which is what keeps the encoded length
      fixed per fault kind regardless of what the caller supplies. -/
  gprs : Array UInt64 := #[]
  deriving Repr, DecidableEq, Inhabited

namespace FaultContext

/-- WS-RR RR4.4: the size of the `x0`-`x7` window a fault context carries —
seL4's `n_syscallMessage` argument range. -/
def gprWindow : Nat := 8

/-- WS-RR RR4.4: total read of the `x0`-`x7` window — absent entries read as
zero, so the encoded message length is a function of the fault kind alone. -/
def gprAt (ctx : FaultContext) (i : Nat) : UInt64 := ctx.gprs[i]?.getD 0

/-- WS-RR RR4.4: build a fault context from a thread's saved register file
and the syndrome's return address.

`sp`/`lr`/`x0`-`x7` come from the register file (the ARM64 mapping: `SP_EL0`
is the file's `sp`, `LR` is `x30`); `faultIP` and `spsr` come from the
exception entry, which is the only place they exist — the register file has
no PSTATE field and its `pc` is not written by the trap path. -/
def ofRegisterFile (rf : SeLe4n.RegisterFile) (faultIP spsr : UInt64) : FaultContext :=
  { faultIP := faultIP
    sp      := rf.sp.val.toUInt64
    lr      := (rf.gpr ⟨30⟩).val.toUInt64
    spsr    := spsr
    gprs    := (Array.range gprWindow).map (fun i => (rf.gpr ⟨i⟩).val.toUInt64) }

/-- WS-RR RR4.4: the `x0`-`x7` window built by `ofRegisterFile` reads back
register for register — the property the unknown-syscall message needs for a
handler to emulate the trapped call. -/
theorem ofRegisterFile_gprAt (rf : SeLe4n.RegisterFile) (faultIP spsr : UInt64)
    (i : Nat) (hi : i < gprWindow) :
    (ofRegisterFile rf faultIP spsr).gprAt i = (rf.gpr ⟨i⟩).val.toUInt64 := by
  simp [ofRegisterFile, gprAt, hi]

/-- WS-RR RR4.4: and the window is exactly `gprWindow` wide, so `gprAt`'s
zero fallback is never reached inside it. -/
@[simp] theorem ofRegisterFile_gprs_size (rf : SeLe4n.RegisterFile) (faultIP spsr : UInt64) :
    (ofRegisterFile rf faultIP spsr).gprs.size = gprWindow := by
  simp [ofRegisterFile]

end FaultContext

-- ============================================================================
-- §2b  The trap-frame window the fault entry spills
-- ============================================================================

/-- WS-RR RR4 (audit round): the registers the trap layer hands the fault
entry — the faulting thread's `x0`-`x7`, `SP_EL0` and `x30` **as saved at the
trap**.

Why this exists: `TCB.registerContext` is a *partial* mirror of the hardware
register file.  The SVC seam spills `x0`-`x5` and `x7` at syscall entry and
the return path writes the result frame back, so between two syscalls the
mirror holds whatever the *last syscall* left there — never the values the
thread had when it took a data abort.  A fault context read off the mirror
alone would carry a stale argument window into the unknown-syscall message
and, worse, *install* it on resume: `applyFaultRestart` writes `x0`-`x7`,
`lr` and `sp` from the context, so a payload-free reply would clobber the
thread's live registers with its last syscall's arguments.  The entry
therefore spills this window into the mirror first
(`Kernel.writeFaultRegistersToTcb`), so the context the delivery builds is the
hardware's (`FaultRegisterWindow.ofRegisterFile_spill`), and a resume
reinstalls exactly what the thread had.

The window is seL4's `n_syscallMessage` register set — the registers a fault
message reads and a fault reply writes — and no more: `x8`-`x29` are neither
reported nor restorable through the fault IPC, so they stay in the trap frame
the SM10.1 context restore merges the staged registers into. -/
structure FaultRegisterWindow where
  /-- `x0`-`x7`, in order; a shorter array reads as zero through `gprAt`. -/
  gprs : Array UInt64 := #[]
  /-- `SP_EL0`. -/
  sp : UInt64 := 0
  /-- `x30`, the link register. -/
  lr : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

namespace FaultRegisterWindow

/-- Total read of the `x0`-`x7` window, zero beyond what was supplied. -/
def gprAt (w : FaultRegisterWindow) (i : Nat) : UInt64 := w.gprs[i]?.getD 0

/-- Spill the window into a saved register file: `x0`-`x7` and `x30` into the
GPR map, `SP_EL0` into `sp`.  Every other register — `pc` included, which the
exception entry carries separately as `ELR_EL1` — is left as it was. -/
def spill (w : FaultRegisterWindow) (rf : SeLe4n.RegisterFile) : SeLe4n.RegisterFile :=
  { rf with
    sp  := ⟨w.sp.toNat⟩
    gpr := fun r =>
      if r.val < FaultContext.gprWindow then ⟨(w.gprAt r.val).toNat⟩
      else if r.val = 30 then ⟨w.lr.toNat⟩
      else rf.gpr r }

/-- The spill leaves the saved `pc` alone — the restart address is the
syndrome's `ELR_EL1`, threaded separately, never a register-file read. -/
@[simp] theorem spill_pc (w : FaultRegisterWindow) (rf : SeLe4n.RegisterFile) :
    (w.spill rf).pc = rf.pc := rfl

/-- A register outside the window and the link register reads through to the
file underneath — the spill overwrites exactly what the trap frame carries. -/
theorem spill_gpr_outside (w : FaultRegisterWindow) (rf : SeLe4n.RegisterFile)
    (r : SeLe4n.RegName) (hLo : ¬ r.val < FaultContext.gprWindow) (hLr : r.val ≠ 30) :
    (w.spill rf).gpr r = rf.gpr r := by
  simp [spill, hLo, hLr]

/-- **The context a delivery builds from a spilled file is the window** — the
words the hardware saved, not whatever the mirror held before.  This is the
statement that closes the stale-mirror defect: every contextual word of the
fault message, and every register a resume reinstalls, is a function of the
trap frame and the syndrome alone. -/
theorem ofRegisterFile_spill (w : FaultRegisterWindow) (rf : SeLe4n.RegisterFile)
    (faultIP spsr : UInt64) :
    FaultContext.ofRegisterFile (w.spill rf) faultIP spsr =
      { faultIP := faultIP, sp := w.sp, lr := w.lr, spsr := spsr,
        gprs := (Array.range FaultContext.gprWindow).map w.gprAt } := by
  unfold FaultContext.ofRegisterFile
  refine FaultContext.mk.injEq _ _ _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, ?_, rfl, ?_⟩
  · simp [spill]
  · simp [spill, FaultContext.gprWindow]
  · apply Array.ext'
    simp only [Array.toList_map, Array.toList_range]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp [spill, hi]

/-- The pointwise form of `ofRegisterFile_spill`, in the shape the message
encoder reads (`FaultContext.gprAt`). -/
theorem ofRegisterFile_spill_gprAt (w : FaultRegisterWindow) (rf : SeLe4n.RegisterFile)
    (faultIP spsr : UInt64) (i : Nat) (hi : i < FaultContext.gprWindow) :
    (FaultContext.ofRegisterFile (w.spill rf) faultIP spsr).gprAt i = w.gprAt i := by
  rw [FaultContext.ofRegisterFile_gprAt _ _ _ i hi]
  simp [spill, hi]

end FaultRegisterWindow

-- ============================================================================
-- §3  What a faulting thread carries
-- ============================================================================

/-- WS-RR RR4: the fault a thread is blocked on — seL4's `tcbFault`, as a
single TCB field.

Bundling the fault with the context it was taken in (rather than storing two
`Option`s) makes the pairing structural: there is no state in which a thread
carries a fault whose register context is missing, or a context with no fault
to restart from. -/
structure ThreadFault where
  /-- The fault itself — what to tell the handler. -/
  fault : Fault
  /-- The register context the fault was taken in — what to restart from. -/
  context : FaultContext
  deriving Repr, DecidableEq, Inhabited

end SeLe4n.Model
