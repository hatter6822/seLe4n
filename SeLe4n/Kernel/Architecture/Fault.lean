-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.SyscallReturn

/-!
# WS-RR RR4 — The `Fault` type and the fault-message wire format

This module is the RR4.1–RR4.6 deliverable of the pre-SM10 remediation
workstream (plan `docs/planning/SMP_RELEASE_READINESS_PLAN.md` §RR4).  It
supplies the four things the fault-IPC path needs before any transition can
exist:

* **the syndrome layer** (§1) — `ExceptionContext` and the ESR_EL1
  classification, moved down here from `Architecture/ExceptionModel.lean` so
  the IPC layer can consume them.  `ExceptionModel` imports this module, so
  every existing consumer of those names is unchanged;
* **the `Fault` inductive** (§2, RR4.1/RR4.2) — one constructor per seL4
  fault kind, each carrying the payload its message needs.  Nullary
  constructors would leave the wire layout unable to carry what a handler
  needs to diagnose or restart the fault, and the round trip below would
  then only preserve an already-impoverished value;
* **the classification map** (§3, RR4.3) — `ExceptionContext → Option Fault`.
  Deliberately **not** a map out of `SynchronousExceptionClass`: that
  inductive is nullary, while the fault address and syndrome exist only in
  `ExceptionContext.far` / `.esr`, so a class-to-fault map could only invent
  them and would corrupt the VM-fault message before it is encoded;
* **the wire format** (§5–§7, RR4.4–RR4.6) — `Fault → MessageInfo × registers`
  at seL4 parity, its inverse, the round-trip identity, and the bound that
  every fault fits the message-register budget.

## seL4 parity

The message layouts mirror `sel4/arch/constants.h` on AArch64 one word at a
time.  seL4 splits the payload across two sources: the `seL4_Fault_t` value
itself (the *fault-specific* words) and the faulting thread's saved context
(`getRestartPC`, SP, LR, SPSR, `x0`-`x7` — the *contextual* words, spliced in
by `setMRs_fault`).  `Fault` carries the first, `FaultContext` (§4) the
second, and `encodeFault` interleaves them exactly as `setMRs_fault` does.

That split is what makes the RR4.5 round trip a statement about `Fault`:
`decodeFault` recovers the fault from any context, because every
fault-specific word sits at a fixed index that no contextual word occupies.

## What the labels mean

The `MessageInfo.label` a fault message carries is seL4's `seL4_Fault_tag`
(`sel4/shared_types.bf`), so a handler distinguishes fault kinds exactly as
it does on seL4 — by the label of the message it received, not by a
convention private to this kernel.  `IpcMessage.label` (added with this
module) is what carries it from the delivery transition to the handler's
return frame; before RR4 the model discarded every message label at decode
time, which would have made a fault message indistinguishable from a
successful receive.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1  Exception syndrome — ESR_EL1 classification
-- ============================================================================
--
-- Moved down from `Architecture/ExceptionModel.lean` (which imports
-- `Kernel.API`, far above the IPC layer) so that the fault path can consume
-- the classification without inverting the import graph.  `ExceptionModel`
-- imports this module and both live in `SeLe4n.Kernel.Architecture`, so every
-- name below is still visible to every existing consumer unchanged.

/-- AG3-C: Synchronous exception class (derived from ESR_EL1 EC field).

**Review round (PR #887): `kernelAbort` is the current-EL abort** — EC `0x25`
(data abort taken from the same EL) and `0x21` (instruction abort taken from
the same EL).  The kernel runs at EL1, so an exception with either syndrome
was raised by the *kernel*, never by a user thread: it is a kernel bug or a
hardware fault, and the only correct answer is to halt.  Folding it into
`dataAbort` / `instrAbort` — as the AG3-C table did — would have delivered a
kernel page fault, with the kernel's own `FAR_EL1` and register window, to
whichever user thread happened to be current, whose handler's reply could
then resume the kernel at the faulting instruction as if nothing had
happened. -/
inductive SynchronousExceptionClass where
  | svc             -- SVC instruction (syscall)
  | dataAbort       -- Data abort, taken from a lower EL (a user thread)
  | instrAbort      -- Instruction abort, taken from a lower EL
  | pcAlignment     -- PC alignment fault
  | spAlignment     -- SP alignment fault
  | unknownReason   -- Unclassified synchronous exception
  | kernelAbort     -- Data or instruction abort taken from the current EL: the kernel faulted
  deriving Repr, DecidableEq

/-- AG3-C: Exception context — captures the ARM64 exception registers
    saved on exception entry. All values are `UInt64` matching the
    hardware register width. -/
structure ExceptionContext where
  /-- ESR_EL1: Exception Syndrome Register -/
  esr : UInt64
  /-- ELR_EL1: Exception Link Register (return address) -/
  elr : UInt64
  /-- SPSR_EL1: Saved Program Status Register -/
  spsr : UInt64
  /-- FAR_EL1: Fault Address Register -/
  far : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- AG3-C: Extract the Exception Class (EC) field from ESR_EL1.
    EC is bits [31:26] — a 6-bit field identifying the exception reason. -/
def extractExceptionClass (esr : UInt64) : UInt64 :=
  (esr >>> 26) &&& 0x3F

/-- Review round (PR #887): **which exception level the exception was taken
from**, read off the saved `SPSR_EL1`.  `M[3:2]` (bits 3 and 2 of the mode
field) is the EL: `0` for EL0, `1` for EL1.  This is the second, syndrome-
independent half of the kernel-origin gate: `kernelAbort` catches the two
abort classes whose EC encodes "current EL", but an alignment fault or an
undefined instruction has one EC whichever EL raised it, and only the saved
PSTATE says which.  A fault entry must deliver only exceptions taken from
EL0 — the kernel has no fault handler to deliver to and a user handler must
never be handed a kernel fault. -/
def ExceptionContext.takenFromEl0 (ectx : ExceptionContext) : Bool :=
  ((ectx.spsr >>> 2) &&& 0x3) == 0

/-- WS-RR RR4.3: extract the Instruction Specific Syndrome (ISS) field from
    ESR_EL1 — bits [24:0].  The per-class detail word: for a data abort it
    carries the DFSC status code, the write-not-read bit and the access size;
    for an alignment or undefined-instruction fault it carries the
    class-specific encoding a handler needs to diagnose the trap. -/
def extractInstructionSyndrome (esr : UInt64) : UInt64 :=
  esr &&& 0x1FFFFFF

/-- AG3-C: Classify a synchronous exception from the ESR_EL1 EC field.
    Maps ARM64 exception class codes to our model's classification:
    - EC 0x15: SVC from AArch64 (syscall)
    - EC 0x24: Data abort from a lower EL (a user thread)
    - EC 0x20: Instruction abort from a lower EL
    - EC 0x25 / 0x21: Data / instruction abort from the **current** EL — the
      kernel itself faulted (`kernelAbort`; review round, PR #887)
    - EC 0x22: PC alignment fault
    - EC 0x26: SP alignment fault
    - All others: Unknown/unmodeled -/
def classifySynchronousException (ectx : ExceptionContext) : SynchronousExceptionClass :=
  let ec := extractExceptionClass ectx.esr
  if ec = 0x15 then .svc
  else if ec = 0x24 then .dataAbort
  else if ec = 0x20 then .instrAbort
  else if ec = 0x25 || ec = 0x21 then .kernelAbort
  else if ec = 0x22 then .pcAlignment
  else if ec = 0x26 then .spAlignment
  else .unknownReason

/-- Review round (PR #887): the two current-EL abort syndromes classify as a
kernel abort — never as a user fault. -/
theorem classifySynchronousException_currentEl_abort (ectx : ExceptionContext)
    (h : extractExceptionClass ectx.esr = 0x25 ∨ extractExceptionClass ectx.esr = 0x21) :
    classifySynchronousException ectx = .kernelAbort := by
  unfold classifySynchronousException
  rcases h with h | h <;> simp [h]

/-- AG3-C: Classification is total — every ESR value produces a valid class. -/
theorem classifySynchronousException_total (ectx : ExceptionContext) :
    ∃ cls, classifySynchronousException ectx = cls :=
  ⟨_, rfl⟩

-- ============================================================================
-- §3  RR4.3 — `ExceptionContext → Fault`
-- ============================================================================

/-- WS-RR RR4.3: classify a synchronous exception into the fault the kernel
raises for it, reading the payload out of the syndrome registers.

`none` for two classes: an `SVC` is the syscall path, not a fault, and
returning a fault for it would make the abort wiring (RR4.21) divert syscalls
into the handler endpoint; and a `kernelAbort` is the kernel's own fault
(review round, PR #887), which no user thread may be handed — the trap layer
halts on it, and this map refuses to manufacture a user fault for it.

* data abort → `vmFault (FAR) (ESR) prefetch := false`
* instruction abort → `vmFault (FAR) (ESR) prefetch := true`
* PC/SP alignment and every unmodeled class → `userException (EC) (ESR)`

The VM-fault payload comes from `ectx.far` / `ectx.esr`, which is the reason
this function takes the whole `ExceptionContext` rather than the nullary
`SynchronousExceptionClass`: a class-to-fault map has no address to report and
could only invent one. -/
def faultOfExceptionContext (ectx : ExceptionContext) : Option Fault :=
  match classifySynchronousException ectx with
  | .svc          => none
  | .kernelAbort  => none
  | .dataAbort    => some (.vmFault ectx.far ectx.esr false)
  | .instrAbort   => some (.vmFault ectx.far ectx.esr true)
  | .pcAlignment  => some (.userException (extractExceptionClass ectx.esr) ectx.esr)
  | .spAlignment  => some (.userException (extractExceptionClass ectx.esr) ectx.esr)
  | .unknownReason => some (.userException (extractExceptionClass ectx.esr) ectx.esr)

/-- WS-RR RR4.3 / review round: the SVC class and the kernel abort — and only
they — yield no fault. -/
theorem faultOfExceptionContext_eq_none_iff (ectx : ExceptionContext) :
    faultOfExceptionContext ectx = none ↔
      (classifySynchronousException ectx = .svc ∨
        classifySynchronousException ectx = .kernelAbort) := by
  unfold faultOfExceptionContext
  cases h : classifySynchronousException ectx <;> simp

/-- Review round (PR #887): a kernel abort is never turned into a user fault. -/
theorem faultOfExceptionContext_kernelAbort (ectx : ExceptionContext)
    (h : classifySynchronousException ectx = .kernelAbort) :
    faultOfExceptionContext ectx = none := by
  simp [faultOfExceptionContext, h]

/-- WS-RR RR4.3: every user-originated non-SVC synchronous exception produces
a fault — the totality the abort wiring relies on (there is no
"unclassifiable" arm that would silently fall back to resuming the faulting
instruction).  The kernel abort is excluded by name: it is the one class the
trap layer must *halt* on rather than deliver. -/
theorem faultOfExceptionContext_isSome_of_ne_svc (ectx : ExceptionContext)
    (h : classifySynchronousException ectx ≠ .svc)
    (hK : classifySynchronousException ectx ≠ .kernelAbort) :
    (faultOfExceptionContext ectx).isSome := by
  unfold faultOfExceptionContext
  cases hc : classifySynchronousException ectx <;> simp_all

/-- WS-RR RR4.3: a data abort maps to a non-prefetch VM fault carrying the
fault address and the whole syndrome. -/
theorem faultOfExceptionContext_dataAbort (ectx : ExceptionContext)
    (h : classifySynchronousException ectx = .dataAbort) :
    faultOfExceptionContext ectx = some (.vmFault ectx.far ectx.esr false) := by
  simp [faultOfExceptionContext, h]

/-- WS-RR RR4.3: an instruction abort maps to a **prefetch** VM fault — the
flag seL4 reports as `seL4_VMFault_PrefetchFault`, which is what tells a
handler to map an executable page rather than a data page. -/
theorem faultOfExceptionContext_instrAbort (ectx : ExceptionContext)
    (h : classifySynchronousException ectx = .instrAbort) :
    faultOfExceptionContext ectx = some (.vmFault ectx.far ectx.esr true) := by
  simp [faultOfExceptionContext, h]

/-- WS-RR RR4.3: the data and instruction aborts differ exactly in the
prefetch flag — a mapping that collapsed them would give the handler no way
to tell an unmapped code page from an unmapped data page. -/
theorem faultOfExceptionContext_abort_prefetch_distinguishes
    (d i : ExceptionContext)
    (hd : classifySynchronousException d = .dataAbort)
    (hi : classifySynchronousException i = .instrAbort)
    (hFar : d.far = i.far) (hEsr : d.esr = i.esr) :
    faultOfExceptionContext d ≠ faultOfExceptionContext i := by
  rw [faultOfExceptionContext_dataAbort d hd, faultOfExceptionContext_instrAbort i hi,
      ← hFar, ← hEsr]
  simp

-- ============================================================================
-- §4  Reading a fault context off a thread
-- ============================================================================
--
-- `FaultContext` itself lives in `SeLe4n/Model/Fault.lean` (below
-- `Model/Object/Types.lean`, so `TCB.pendingFault` can carry it).  What stays
-- here is the reader that needs a `SystemState`.

/-- WS-RR RR4.4: build a fault context from a thread's TCB — the shape the
delivery transition uses.  A missing TCB yields the syndrome words alone; the
caller has already failed closed on the lookup before it gets here, so the
arm exists for totality, not as a path. -/
def faultContextOfThread (st : SystemState) (tid : SeLe4n.ThreadId)
    (faultIP spsr : UInt64) : FaultContext :=
  match st.getTcb? tid with
  | some tcb => FaultContext.ofRegisterFile tcb.registerContext faultIP spsr
  | none     => { faultIP := faultIP, spsr := spsr }

/-- WS-RR RR4.4: the restart PC survives context construction on both arms —
the word every one of the four fault messages carries. -/
@[simp] theorem faultContextOfThread_faultIP (st : SystemState) (tid : SeLe4n.ThreadId)
    (faultIP spsr : UInt64) : (faultContextOfThread st tid faultIP spsr).faultIP = faultIP := by
  unfold faultContextOfThread; cases st.getTcb? tid <;> rfl

/-- WS-RR RR4.4: and so does the saved PSTATE. -/
@[simp] theorem faultContextOfThread_spsr (st : SystemState) (tid : SeLe4n.ThreadId)
    (faultIP spsr : UInt64) : (faultContextOfThread st tid faultIP spsr).spsr = spsr := by
  unfold faultContextOfThread; cases st.getTcb? tid <;> rfl

-- ============================================================================
-- §5  RR4.4 — the fault-message wire format
-- ============================================================================

/-! ### WS-RR RR4.4: the `seL4_Fault_tag` values, as `MessageInfo` labels

Taken from seL4's `shared_types.bf` / `arch/object/structures.bf` so a handler
written against seL4's `seL4_Fault_tag` constants reads seLe4n's fault
messages unchanged.  `nullFault` (0) is never sent — it is seL4's "this thread
has no outstanding fault" marker and is named here so the fault labels cannot
silently collide with the WS-RA success label, which is also `0`. -/
namespace FaultLabel

/-- seL4 `seL4_Fault_NullFault` — never carried by a delivered fault message. -/
def nullFault : Nat := 0
/-- seL4 `seL4_Fault_CapFault`. -/
def capFault : Nat := 1
/-- seL4 `seL4_Fault_UnknownSyscall`. -/
def unknownSyscall : Nat := 2
/-- seL4 `seL4_Fault_UserException`. -/
def userException : Nat := 3
/-- seL4 `seL4_Fault_DebugException` — reserved, never carried: this model
delivers no debug exceptions.  Named so the gap at 4 is a documented tag and
not an unexplained hole. -/
def debugException : Nat := 4
/-- seL4 `seL4_Fault_Timeout` (MCS) — reserved, never carried: a CBS budget's
exhaustion is a scheduling event here, not a delivered fault. -/
def timeout : Nat := 5
/-- seL4 `seL4_Fault_VMFault` — **6**, the MCS layout's arch tag.

`libsel4/arch_include/arm/sel4/arch/shared_types.bf` numbers the union in two
layouts: under `CONFIG_KERNEL_MCS` it is `Timeout 5` then `VMFault 6` (with
`VGICMaintenance 7`, `VCPUFault 8`, `VPPIEvent 9` under the hypervisor
option); without MCS the arch tags start at `VMFault 5`.  This kernel is the
MCS shape — scheduling contexts, CBS budgets, timeout budgets — so its
handlers decode the MCS layout, and `6` is the tag a `seL4_Fault_VMFault`
arrives under.  The review of PR #887 read the non-MCS layout and reported
`6` as a timeout; `faultLabel_ne_timeout` below is the pin that keeps the two
layouts from being confused again. -/
def vmFault : Nat := 6

end FaultLabel

/-- WS-RR RR4.4: the message-register count each fault kind occupies.

Three of the four are seL4's lengths verbatim (`seL4_VMFault_Length` = 4,
`seL4_UnknownSyscall_Length` = 13, `seL4_UserException_Length` = 5).  The
capability fault is **4** words here — IP, address, receive-phase flag, and
the lookup-failure reason — where seL4's `setMRs_lookup_failure` appends one
or two further words (`BitsLeft`, `BitsFound` / `GuardFound`) for the
depth-mismatch and guard-mismatch failure kinds; this model's reason word is a
`KernelError` discriminant with no such sub-fields, so the message has no
extra words to carry. -/
def faultMessageLength : Fault → Nat
  | .vmFault _ _ _        => 4
  | .capFault _ _ _       => 4
  | .unknownSyscall _     => 13
  | .userException _ _    => 5

/-- WS-RR RR4.4: the `seL4_Fault_tag` a fault is delivered under. -/
def faultLabel : Fault → Nat
  | .vmFault _ _ _        => FaultLabel.vmFault
  | .capFault _ _ _       => FaultLabel.capFault
  | .unknownSyscall _     => FaultLabel.unknownSyscall
  | .userException _ _    => FaultLabel.userException

/-- WS-RR RR4 (audit round, ABI v3): **every fault tag is a delivery label**
— far below `errorLabelBase`, the first kernel-status label — so a handler's
`seL4_Recv` returns the tag in `x1` and its decoder reads a successful
receive, never a kernel error.  Under the v2 offset carriage a `vmFault`'s
tag `6` decoded as discriminant `5` and a `capFault`'s tag `1` as
`.invalidCapability`; this is the theorem that closed that. -/
theorem faultLabel_lt_errorLabelBase (f : Fault) : faultLabel f < errorLabelBase := by
  rw [errorLabelBase_eq]
  cases f <;> simp [faultLabel, FaultLabel.vmFault, FaultLabel.capFault,
    FaultLabel.unknownSyscall, FaultLabel.userException]

/-- PR #887 review round 2: no delivered fault carries the MCS `Timeout` tag.
The layout is the MCS one, in which `5` is the timeout and `6` the VM fault,
and this model delivers no timeout faults — so a handler that decodes `5` as
`seL4_Fault_Timeout` never sees a VM fault under that tag. -/
theorem faultLabel_ne_timeout (f : Fault) : faultLabel f ≠ FaultLabel.timeout := by
  cases f <;> simp [faultLabel, FaultLabel.timeout, FaultLabel.vmFault, FaultLabel.capFault,
    FaultLabel.unknownSyscall, FaultLabel.userException]

/-- …nor the debug-exception tag, the other reserved value below the VM fault. -/
theorem faultLabel_ne_debugException (f : Fault) :
    faultLabel f ≠ FaultLabel.debugException := by
  cases f <;> simp [faultLabel, FaultLabel.debugException, FaultLabel.vmFault,
    FaultLabel.capFault, FaultLabel.unknownSyscall, FaultLabel.userException]

/-- WS-RR RR4.4: a fault's label is never the success/null label, so a fault
message can never be mistaken for a `seL4_Fault_NullFault` marker — nor, on
the WS-RA return convention where label `0` means success, for a completed
syscall. -/
theorem faultLabel_ne_null (f : Fault) : faultLabel f ≠ FaultLabel.nullFault := by
  cases f <;> simp [faultLabel, FaultLabel.nullFault, FaultLabel.vmFault,
    FaultLabel.capFault, FaultLabel.unknownSyscall, FaultLabel.userException]

/-- WS-RR RR4.4: distinct fault kinds carry distinct labels — the property a
label-keyed decoder relies on. -/
theorem faultLabel_injective_on_kinds (f g : Fault)
    (h : faultLabel f = faultLabel g) :
    (∃ a s p a' s' p', f = .vmFault a s p ∧ g = .vmFault a' s' p') ∨
    (∃ a r e a' r' e', f = .capFault a r e ∧ g = .capFault a' r' e') ∨
    (∃ n n', f = .unknownSyscall n ∧ g = .unknownSyscall n') ∨
    (∃ n c n' c', f = .userException n c ∧ g = .userException n' c') := by
  cases f <;> cases g <;> simp_all [faultLabel, FaultLabel.vmFault, FaultLabel.capFault,
    FaultLabel.unknownSyscall, FaultLabel.userException]

/-- WS-RR RR4.4: `Bool` → wire word, seL4's flag convention. -/
@[inline] def encodeFlag (b : Bool) : UInt64 := if b then 1 else 0

/-- WS-RR RR4.4: wire word → `Bool`.  Nonzero is `true`, matching every seL4
flag reader; the round trip below pins `decodeFlag ∘ encodeFlag = id`. -/
@[inline] def decodeFlag (w : UInt64) : Bool := w != 0

@[simp] theorem decodeFlag_encodeFlag (b : Bool) : decodeFlag (encodeFlag b) = b := by
  cases b <;> rfl

/-- WS-RR RR4.4: a `UInt64` wire word as a model register value. -/
@[inline] def regOf (w : UInt64) : SeLe4n.RegValue := ⟨w.toNat⟩

/-- WS-RR RR4.4: a model register value back as a wire word.  Total: an
out-of-range `RegValue` (unreachable — every register the model writes is
below `machineWordMax`) truncates, exactly as the hardware register would. -/
@[inline] def wordOf (v : SeLe4n.RegValue) : UInt64 := v.val.toUInt64

@[simp] theorem wordOf_regOf (w : UInt64) : wordOf (regOf w) = w := by
  simp [wordOf, regOf]

/-- WS-RR RR4.4: read wire word `i` out of a message-register array, `0` when
absent — the fail-closed reader `decodeFault` uses under an explicit length
check, so a short array can never be silently accepted. -/
@[inline] def wordAt (regs : Array SeLe4n.RegValue) (i : Nat) : UInt64 :=
  (regs[i]?.map wordOf).getD 0

/-- WS-RR RR4.4 (**the layout**): encode a fault and its context into the
`MessageInfo` and message registers a fault IPC carries.

Word for word this is seL4's `setMRs_fault` on AArch64:

| Fault | MR0 | MR1 | MR2 | MR3 | MR4 | … | MR12 |
|---|---|---|---|---|---|---|---|
| `vmFault` | IP | Addr | PrefetchFault | FSR | | | |
| `capFault` | IP | Addr | InRecvPhase | LookupFailure | | | |
| `unknownSyscall` | x0 | x1 | x2 … | | x7 (MR7), IP (MR8), SP (MR9), LR (MR10), SPSR (MR11) | | Syscall |
| `userException` | IP | SP | SPSR | Number | Code | | |

`extraCaps` is `0` for every fault: a fault message carries diagnostic words,
never authority.  That is not a simplification of seL4 — seL4's fault messages
carry no extra caps either — and it is what makes the RR4.20
non-interference argument about a *data* flow only.

**What reaches hardware registers.**  The full message is delivered in the
model — a handler's `pendingMessage` holds every word, and
`decodeFault_encodeFault` recovers the fault from it — but the WS-RA return
frame carries only `MR0`-`MR3` in `x2`-`x5`, and no receive path yet writes
`MR4` onward into the receiver's IPC buffer (seL4's `setMRs_fault` does; the
buffer-side write is a registered WS-RA residual with no consumer until this
phase).  So on hardware a `vmFault` or `capFault` handler sees its whole
message in registers, while an `unknownSyscall` (13 words) or `userException`
(5 words) handler sees the first four and must not read `seL4_GetMR(4)`
onward until the buffer write lands.  Tracked debt, not a silent truncation:
`docs/REGISTERED_DEBT.md` carries the row and its closure target. -/
def encodeFault (f : Fault) (ctx : FaultContext) :
    MessageInfo × Array SeLe4n.RegValue :=
  ({ length := faultMessageLength f, extraCaps := 0, label := faultLabel f },
   match f with
   | .vmFault address status prefetch =>
       #[regOf ctx.faultIP, regOf address, regOf (encodeFlag prefetch), regOf status]
   | .capFault capAddress inReceivePhase lookupFailure =>
       #[regOf ctx.faultIP, regOf capAddress, regOf (encodeFlag inReceivePhase),
         regOf (Nat.toUInt64 (KernelError.toDiscriminant lookupFailure))]
   | .unknownSyscall syscallNumber =>
       #[regOf (ctx.gprAt 0), regOf (ctx.gprAt 1), regOf (ctx.gprAt 2), regOf (ctx.gprAt 3),
         regOf (ctx.gprAt 4), regOf (ctx.gprAt 5), regOf (ctx.gprAt 6), regOf (ctx.gprAt 7),
         regOf ctx.faultIP, regOf ctx.sp, regOf ctx.lr, regOf ctx.spsr,
         regOf syscallNumber]
   | .userException number code =>
       #[regOf ctx.faultIP, regOf ctx.sp, regOf ctx.spsr, regOf number, regOf code])

-- ============================================================================
-- §6  RR4.5 — the inverse, and the round trip
-- ============================================================================

/-- WS-RR RR4.5: recover a fault from the message it was delivered as.

Fail-closed on three axes, each of which a malformed or forged message could
otherwise slip past: the label must be a fault tag, the declared `length` must
be exactly the tag's layout length, and the register array must actually hold
that many words.  A `capFault` additionally requires its reason word to be a
real `KernelError` discriminant. -/
def decodeFault (mi : MessageInfo) (regs : Array SeLe4n.RegValue) : Option Fault :=
  if regs.size < mi.length then none
  else if mi.label = FaultLabel.vmFault ∧ mi.length = 4 then
    some (.vmFault (wordAt regs 1) (wordAt regs 3) (decodeFlag (wordAt regs 2)))
  else if mi.label = FaultLabel.capFault ∧ mi.length = 4 then
    match KernelError.ofDiscriminant? (wordAt regs 3).toNat with
    | some e => some (.capFault (wordAt regs 1) (decodeFlag (wordAt regs 2)) e)
    | none   => none
  else if mi.label = FaultLabel.unknownSyscall ∧ mi.length = 13 then
    some (.unknownSyscall (wordAt regs 12))
  else if mi.label = FaultLabel.userException ∧ mi.length = 5 then
    some (.userException (wordAt regs 3) (wordAt regs 4))
  else none

/-- WS-RR RR4.5 (**the round trip**): encoding a fault and decoding the result
is the identity, for every fault and **every** context.

The context-independence is the point: the contextual words seL4 splices in
(`getRestartPC`, SP, LR, SPSR, `x0`-`x7`) sit at indices no fault-specific
word occupies, so a handler's view of *which fault this is* cannot be
perturbed by the faulting thread's register content. -/
theorem decodeFault_encodeFault (f : Fault) (ctx : FaultContext) :
    decodeFault (encodeFault f ctx).1 (encodeFault f ctx).2 = some f := by
  cases f with
  | vmFault address status prefetch =>
      simp [encodeFault, decodeFault, faultMessageLength, faultLabel, wordAt,
        FaultLabel.vmFault]
  | capFault capAddress inReceivePhase lookupFailure =>
      have hLt : KernelError.toDiscriminant lookupFailure < 57 :=
        KernelError.toDiscriminant_lt lookupFailure
      have hMod : KernelError.toDiscriminant lookupFailure % 18446744073709551616
          = KernelError.toDiscriminant lookupFailure := Nat.mod_eq_of_lt (by omega)
      have hDisc : KernelError.ofDiscriminant? (KernelError.toDiscriminant lookupFailure)
          = some lookupFailure := KernelError.ofDiscriminant?_toDiscriminant lookupFailure
      simp [encodeFault, decodeFault, faultMessageLength, faultLabel, wordAt,
        FaultLabel.vmFault, FaultLabel.capFault, hMod, hDisc]
  | unknownSyscall syscallNumber =>
      simp [encodeFault, decodeFault, faultMessageLength, faultLabel, wordAt,
        FaultLabel.vmFault, FaultLabel.capFault, FaultLabel.unknownSyscall]
  | userException number code =>
      simp [encodeFault, decodeFault, faultMessageLength, faultLabel, wordAt,
        FaultLabel.vmFault, FaultLabel.capFault, FaultLabel.unknownSyscall,
        FaultLabel.userException]

/-- WS-RR RR4.5 (corollary): the encoding is injective — two faults that
encode to the same message under the same context are the same fault. -/
theorem encodeFault_injective (f g : Fault) (ctx : FaultContext)
    (h : encodeFault f ctx = encodeFault g ctx) : f = g := by
  have hf := decodeFault_encodeFault f ctx
  have hg := decodeFault_encodeFault g ctx
  rw [h] at hf
  exact Option.some.inj (hf.symm.trans hg)

/-- WS-RR RR4.5: the restart PC reaches the handler on every fault kind — the
word a handler needs to decide between resume and restart.  `unknownSyscall`
carries it at MR8 (after the `x0`-`x7` window), every other kind at MR0. -/
theorem encodeFault_carries_faultIP (f : Fault) (ctx : FaultContext) :
    ∃ i, i < (encodeFault f ctx).2.size ∧
      wordAt (encodeFault f ctx).2 i = ctx.faultIP := by
  cases f with
  | vmFault a s p => exact ⟨0, by simp [encodeFault], by simp [encodeFault, wordAt]⟩
  | capFault a r e => exact ⟨0, by simp [encodeFault], by simp [encodeFault, wordAt]⟩
  | unknownSyscall n => exact ⟨8, by simp [encodeFault], by simp [encodeFault, wordAt]⟩
  | userException n c => exact ⟨0, by simp [encodeFault], by simp [encodeFault, wordAt]⟩

-- ============================================================================
-- §7  RR4.6 — the message-register budget
-- ============================================================================

/-- WS-RR RR4.6: the declared length is the real one — the encoder never
declares a window it did not fill, which is what makes `decodeFault`'s
`regs.size < mi.length` guard a check on the *sender* rather than a
tautology. -/
@[simp] theorem encodeFault_size_eq_length (f : Fault) (ctx : FaultContext) :
    (encodeFault f ctx).2.size = (encodeFault f ctx).1.length := by
  cases f <;> simp [encodeFault, faultMessageLength]

/-- WS-RR RR4.6 (**the budget**): every fault encodes inside the seL4
message-register bound, so a fault IPC never trips the `ipcMessageTooLarge`
prefilter the delivery transition inherits from `endpointCall`. -/
theorem encodeFault_within_budget (f : Fault) (ctx : FaultContext) :
    (encodeFault f ctx).2.size ≤ maxMessageRegisters := by
  cases f <;> simp [encodeFault, maxMessageRegisters]

/-- WS-RR RR4.6: and it carries no capabilities, so the extra-cap prefilter is
never tripped either. -/
@[simp] theorem encodeFault_extraCaps (f : Fault) (ctx : FaultContext) :
    (encodeFault f ctx).1.extraCaps = 0 := by cases f <;> rfl

/-- WS-RR RR4.6: the encoded `MessageInfo` is well-formed — length, extraCaps
and the 20-bit label all inside their seL4 bounds, so the word encodes and
decodes losslessly through `MessageInfo.encode`. -/
theorem encodeFault_messageInfo_wellFormed (f : Fault) (ctx : FaultContext) :
    (encodeFault f ctx).1.wellFormed := by
  refine ⟨?_, ?_, ?_⟩ <;> cases f <;>
    simp [encodeFault, faultMessageLength, faultLabel, maxMessageRegisters,
      Model.maxExtraCaps, MessageInfo.maxLabel, FaultLabel.vmFault, FaultLabel.capFault,
      FaultLabel.unknownSyscall, FaultLabel.userException]

-- ============================================================================
-- §8  RR4.14/RR4.15 — what a fault reply does
-- ============================================================================

/-- WS-RR RR4.14/RR4.15: the disposition a fault reply gives the faulted
thread, mirroring seL4's `doReplyTransfer` fault branch: `handleFaultReply`
returns whether to restart, and the thread is set `Restart` or `Inactive`
accordingly. -/
inductive FaultReplyOutcome where
  /-- Restart the thread with this register frame.  A **resume** is the case
      where the frame is the saved context unchanged (RR4.14); a **restart**
      (RR4.15) is the case where the reply overrode the PC and registers. -/
  | restart (frame : FaultRestartFrame)
  /-- The handler declined to resume the thread: it stays `.Inactive`
      (seL4's `setThreadState(receiver, ThreadState_Inactive)`). -/
  | abandon
  deriving Repr, DecidableEq, Inhabited

namespace FaultReplyOutcome

/-- WS-RR RR4.15: the PC a reply outcome restarts the thread at, `none` when
the outcome abandons it.  Named because it is the quantity every statement
about "where does the thread go next" is really about — including RR4.19's,
where the answer for an abandoned thread being `none` *is* the progress
property. -/
def restartPC? : FaultReplyOutcome → Option UInt64
  | .restart f => some f.pc
  | .abandon   => none

end FaultReplyOutcome

/-- WS-RR RR4.14: the **resume** frame — the faulted thread's own saved
context, unchanged.  A reply that overrides nothing restarts the thread at
the faulting instruction with the registers it had, which is the right
behaviour once the handler has repaired what faulted (mapped the page,
grown the stack). -/
def faultRestartFrameOfContext (ctx : FaultContext) : FaultRestartFrame :=
  { pc := ctx.faultIP, sp := ctx.sp, lr := ctx.lr
    x0 := ctx.gprAt 0, x1 := ctx.gprAt 1, x2 := ctx.gprAt 2, x3 := ctx.gprAt 3
    x4 := ctx.gprAt 4, x5 := ctx.gprAt 5, x6 := ctx.gprAt 6, x7 := ctx.gprAt 7 }

/-- WS-RR RR4.14: a resume restarts the thread at the instruction that
faulted — the word `faultOfExceptionContext`'s caller took from `ELR_EL1`. -/
@[simp] theorem faultRestartFrameOfContext_pc (ctx : FaultContext) :
    (faultRestartFrameOfContext ctx).pc = ctx.faultIP := rfl

/-- WS-RR RR4.15: read reply word `i`, or keep the faulted thread's own value
when the reply did not supply it.

Bounded on **both** the declared length and the array actually delivered:
seL4 takes `MIN(length, n_syscallMessage)`, and a reply whose declared length
outruns its payload must not read a fabricated zero into the faulted thread's
program counter. -/
def replyWordOr (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (i : Nat)
    (fallback : UInt64) : UInt64 :=
  if i < min mi.length regs.size then wordAt regs i else fallback

/-- WS-RR RR4.15: a reply that declares no register payload overrides
nothing — the fallback is returned for every index. -/
@[simp] theorem replyWordOr_of_empty (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (i : Nat) (fallback : UInt64) (h : mi.length = 0) :
    replyWordOr mi regs i fallback = fallback := by
  simp [replyWordOr, h]

/-- WS-RR RR4.15: and one that does supply the word delivers it. -/
theorem replyWordOr_of_covered (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (i : Nat) (fallback : UInt64) (hLen : i < mi.length) (hArr : i < regs.size) :
    replyWordOr mi regs i fallback = wordAt regs i := by
  simp [replyWordOr, Nat.lt_min.mpr ⟨hLen, hArr⟩]

/-- WS-RR RR4.14/RR4.15 (**the reply semantics**): decide what a handler's
reply does to the faulted thread.

Exactly seL4's `handleFaultReply`, arm for arm:

* **VM fault, cap fault** — restart unconditionally with the saved context.
  seL4 returns `true` from these arms without inspecting the reply at all:
  the handler's job was to repair the address space, and there is no
  register payload defined for either message.
* **Unknown syscall** — `label = 0` restarts, installing
  `MIN(length, n_syscallMessage)` reply words over `x0`-`x7`, the restart PC,
  SP and LR (seL4's `fault_messages[MessageID_Syscall]`); any other label
  abandons the thread.  This is the arm a handler uses to *emulate* the
  trapped call and reply with its results.
* **User exception** — `label = 0` restarts, installing
  `MIN(length, n_exceptionMessage)` words over the restart PC and SP; any
  other label abandons.

The `SPSR_EL1` slot each of those two lists ends with is deliberately not
installed — see `Model.FaultContext.spsr`: this model keeps PSTATE out of a
handler's reach, which is strictly the fail-closed side of seL4's
`sanitiseRegister`.

**One further divergence, on the abandon arms, and it is the fail-closed
direction.**  seL4 calls `copyMRsFaultReply` *before* it tests the label, so a
reply with a nonzero label installs the handler's registers into a thread it
then leaves `ThreadState_Inactive` — and a later `seL4_TCB_Resume` runs that
thread on registers chosen by a handler that had just declared it unfit to
continue.  This decoder returns `.abandon` without a frame, so the register
write never happens: a handler that abandons a thread influences nothing about
how that thread would run if some other authority resumes it.  Restarting is
the only path by which a reply reaches the register file. -/
def decodeFaultReply (f : Fault) (ctx : FaultContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) : FaultReplyOutcome :=
  let base := faultRestartFrameOfContext ctx
  match f with
  | .vmFault _ _ _  => .restart base
  | .capFault _ _ _ => .restart base
  | .unknownSyscall _ =>
      if mi.label ≠ 0 then .abandon
      else .restart
        { pc := replyWordOr mi regs 8 base.pc
          sp := replyWordOr mi regs 9 base.sp
          lr := replyWordOr mi regs 10 base.lr
          x0 := replyWordOr mi regs 0 base.x0
          x1 := replyWordOr mi regs 1 base.x1
          x2 := replyWordOr mi regs 2 base.x2
          x3 := replyWordOr mi regs 3 base.x3
          x4 := replyWordOr mi regs 4 base.x4
          x5 := replyWordOr mi regs 5 base.x5
          x6 := replyWordOr mi regs 6 base.x6
          x7 := replyWordOr mi regs 7 base.x7 }
  | .userException _ _ =>
      if mi.label ≠ 0 then .abandon
      else .restart
        { base with
          pc := replyWordOr mi regs 0 base.pc
          sp := replyWordOr mi regs 1 base.sp }

/-- WS-RR RR4.14: a VM fault's reply resumes the thread at the faulting
instruction with its registers intact — whatever the reply said.  seL4's
arm returns `true` without reading the message, and so does this one: a
handler that mapped the page has nothing to install. -/
@[simp] theorem decodeFaultReply_vmFault (a s : UInt64) (p : Bool)
    (ctx : FaultContext) (mi : MessageInfo) (regs : Array SeLe4n.RegValue) :
    decodeFaultReply (.vmFault a s p) ctx mi regs
      = .restart (faultRestartFrameOfContext ctx) := rfl

/-- WS-RR RR4.14: and a cap fault's, identically. -/
@[simp] theorem decodeFaultReply_capFault (a : UInt64) (r : Bool)
    (e : Model.KernelError) (ctx : FaultContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) :
    decodeFaultReply (.capFault a r e) ctx mi regs
      = .restart (faultRestartFrameOfContext ctx) := rfl

/-- WS-RR RR4.15: a **nonzero reply label abandons** the thread on the two
arms that admit a register payload — the handler's way of saying "this
thread must not continue".  The thread stays `.Inactive`; nothing resumes
it. -/
theorem decodeFaultReply_abandon_of_label (f : Fault) (ctx : FaultContext)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (hLabel : mi.label ≠ 0)
    (hArm : (∃ n, f = .unknownSyscall n) ∨ (∃ n c, f = .userException n c)) :
    decodeFaultReply f ctx mi regs = .abandon := by
  rcases hArm with ⟨n, rfl⟩ | ⟨n, c, rfl⟩ <;> simp [decodeFaultReply, hLabel]

/-- WS-RR RR4.15 (**the restart**): an unknown-syscall reply carrying a
restart PC moves the thread there.  This is the sub-task's content — the
faulted thread does not resume at the instruction that trapped; it resumes
where the handler said. -/
theorem decodeFaultReply_unknownSyscall_restartPC (n : UInt64) (ctx : FaultContext)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (hLabel : mi.label = 0) (hLen : 8 < mi.length) (hArr : 8 < regs.size) :
    (decodeFaultReply (.unknownSyscall n) ctx mi regs).restartPC?
      = some (wordAt regs 8) := by
  simp [decodeFaultReply, FaultReplyOutcome.restartPC?, hLabel,
    replyWordOr_of_covered mi regs 8 ctx.faultIP hLen hArr]

/-- WS-RR RR4.15: a user-exception reply's restart PC is its MR0 — seL4's
`fault_messages[MessageID_Exception][0] = FaultIP`. -/
theorem decodeFaultReply_userException_restartPC (n c : UInt64) (ctx : FaultContext)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (hLabel : mi.label = 0) (hLen : 0 < mi.length) (hArr : 0 < regs.size) :
    (decodeFaultReply (.userException n c) ctx mi regs).restartPC?
      = some (wordAt regs 0) := by
  simp [decodeFaultReply, FaultReplyOutcome.restartPC?, hLabel,
    replyWordOr_of_covered mi regs 0 ctx.faultIP hLen hArr]

/-- WS-RR RR4.14: a **payload-free** reply on either register-carrying arm is
a plain resume — the whole saved context comes back unchanged, so the
`length = 0` reply a handler sends after repairing state behaves exactly like
the VM-fault arm. -/
theorem decodeFaultReply_resume_of_empty (f : Fault) (ctx : FaultContext)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue)
    (hLabel : mi.label = 0) (hLen : mi.length = 0) :
    decodeFaultReply f ctx mi regs = .restart (faultRestartFrameOfContext ctx) := by
  cases f <;>
    simp [decodeFaultReply, faultRestartFrameOfContext, hLabel, replyWordOr, hLen]

/-- WS-RR RR4.15: the outcome is total and binary — a fault reply either
restarts the thread or abandons it.  There is no third disposition, and in
particular none that leaves the thread runnable at the faulting instruction
with no handler decision behind it (the RR4.19 progress argument consumes
this exhaustiveness). -/
theorem decodeFaultReply_total (f : Fault) (ctx : FaultContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) :
    (∃ frame, decodeFaultReply f ctx mi regs = .restart frame) ∨
    decodeFaultReply f ctx mi regs = .abandon := by
  cases h : decodeFaultReply f ctx mi regs with
  | restart frame => exact Or.inl ⟨frame, rfl⟩
  | abandon => exact Or.inr rfl

end SeLe4n.Kernel.Architecture
