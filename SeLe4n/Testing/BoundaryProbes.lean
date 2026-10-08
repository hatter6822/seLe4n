-- SPDX-License-Identifier: GPL-3.0-or-later
-- seLe4n  - A Lean Microkernel
-- Copyright (C) 2026  Adam Hall
-- This program comes with ABSOLUTELY NO WARRANTY.
-- This is free software, and you are welcome to redistribute it
-- under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

import SeLe4n.Machine
import SeLe4n.Kernel.Architecture.ContextRestore

/-!
# The boundary-layout probes

**Test-only exports** for `rust/sele4n-lean-boundary`, the host test that
executes the compiled Lean layout of the two scalar-words contexts —
`Architecture.TrapContext` (35 `UInt64` fields) and `FpContext` (66) —
against the offsets the HAL reads and writes (`rust/sele4n-hal/src/ffi.rs`,
`scalar_words_to_lean` / `scalar_words_of_lean`: field `i` at scalar offset
`8 · i`).

What the proofs pin is Lean-internal: `TrapContext.word_ofWords` and
`FpContext.word_ofWords` say declared position `i` is layout word `i`, and the
HAL's exact-size refusal catches a field added or removed on one side.  Neither
reaches a same-size permutation applied consistently on one side — the
structure, `word` and `ofWords` reordered together, which every proof survives
— nor a compiler that lays scalar fields out other than in declaration order.
These probes are what makes that executable: the Rust test builds an object
with a distinct value at every offset `8 · i`, asks this module for `word i`,
and compares; and reads an object this module built back at the same offsets.
A permutation on either side alone fails it (checked by swapping two fields,
`word` and `ofWords` together, and watching the test fail).

This module is outside `SeLe4n.lean`'s import closure, so none of it reaches
the kernel's archive (`scripts/build_lean_aarch64_archive.py` holds
`SeLe4n.Testing.*` out of the closure); `lakefile.toml`'s `SeLe4nBoundaryProbes`
library is what the host test links, beside `SeLe4n:static`.
-/

namespace SeLe4n.Testing.BoundaryProbes

open SeLe4n.Kernel.Architecture

/-- Word `i` of a `TrapContext` the caller built, read by field name
(`TrapContext.word`).

Every parameter of an `@[export]` is **owned** — the compiled probe releases
its argument, and a `@&` here is ignored — so a caller that keeps the object
hands each call a reference of its own (`rust/sele4n-lean-boundary`'s
`handed_over`). -/
@[export sele4n_probe_trap_context_word]
def trapContextWord (c : TrapContext) (i : UInt64) : UInt64 :=
  c.word i.toNat

/-- The context the kernel would hand back for the context handed over: the
model's register file of it, as a context again — the save and restore
conversions composed.  The argument is consumed, a fresh object answered. -/
@[export sele4n_probe_trap_context_round_trip]
def trapContextRoundTrip (c : TrapContext) : TrapContext :=
  trapContextOfRegisterFile (registerFileOfTrapContext c)

/-- A context the Lean side built: word `i` is `seed + i · 0x0101`, so the Rust
side reads a distinct value at every offset `8 · i` — the Lean → Rust direction,
independent of any object Rust wrote. -/
@[export sele4n_probe_trap_context_of_seed]
def trapContextOfSeed (seed : UInt64) : TrapContext :=
  TrapContext.ofWords fun i => seed + i.toUInt64 * 0x0101

/-- Word `i` of an `Option TrapContext` the caller built — the encoding
`ffi_trap_context` answers (`none` is `lean_box(0)`, `some c` constructor tag
`1` with one object field) — or every bit set for `none`.  Owned, as above. -/
@[export sele4n_probe_option_trap_context_word]
def optionTrapContextWord (c : Option TrapContext) (i : UInt64) : UInt64 :=
  match c with
  | none => 0xFFFF_FFFF_FFFF_FFFF
  | some c => c.word i.toNat

/-- Word `i` of an `FpContext` the caller built, read by field name
(`FpContext.word`).  Owned, as above. -/
@[export sele4n_probe_fp_context_word]
def fpContextWord (c : SeLe4n.FpContext) (i : UInt64) : UInt64 :=
  c.word i.toNat

/-- The context the kernel would stage for the context captured: decoded to
its words and encoded again (`FpContext.ofWords` on `FpContext.word`), a fresh
object. -/
@[export sele4n_probe_fp_context_round_trip]
def fpContextRoundTrip (c : SeLe4n.FpContext) : SeLe4n.FpContext :=
  SeLe4n.FpContext.ofWords c.word

/-- An FP/SIMD context the Lean side built: word `i` is `seed + i · 0x0101`. -/
@[export sele4n_probe_fp_context_of_seed]
def fpContextOfSeed (seed : UInt64) : SeLe4n.FpContext :=
  SeLe4n.FpContext.ofWords fun i => seed + i.toUInt64 * 0x0101

/-! ## The two-trap hazard: the save path over a context the HAL reuses

The HAL writes each trap's words into a per-core context object; whether the
kernel's save of trap 1 survives trap 2 being written into **the same object**
is a property of the compiled save path, so it is executed here: the Rust side
builds trap 1's object (`trapContextOfSeed`), saves it into a probe state's
current thread (`saveProbeCapturedSyscallFrame`), overwrites the object's words
with trap 2's (`sele4n_boundary_ctor_set_u64`, what the HAL does to a reused
object) and reads the thread's saved context back (`saveProbeContextWord`).
Today the register file keeps the general-purpose registers as a closure over
the object (`registerFileOfTrapContext`), so words 0–30 read trap 2's after the
overwrite while words 31–34, read when the file was built, stay trap 1's —
the hazard the context-by-value workstream (WS-CV) removes. -/

/-- The probe state: one TCB, id `tid`, current on the boot core and in no run
queue (dequeue-on-dispatch), nothing else.  Built from the model's own
constructors, since the test builder lives outside the archives the host test
links. -/
@[export sele4n_probe_save_state]
def saveProbeState (tid : UInt64) : SeLe4n.Model.SystemState :=
  let t : SeLe4n.ThreadId := ⟨tid.toNat⟩
  let objs : List (SeLe4n.ObjId × SeLe4n.Model.KernelObject) :=
    [(t.toObjId, .tcb
      { tid := t, priority := ⟨0⟩, domain := ⟨0⟩,
        cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
        ipcBuffer := SeLe4n.VAddr.ofNat 0, ipcState := .ready,
        threadState := .Running })]
  { (default : SeLe4n.Model.SystemState) with
    objects := SeLe4n.Kernel.RobinHood.RHTable.ofList objs
    objectIndex := objs.map Prod.fst
    objectIndexSet := SeLe4n.Kernel.RobinHood.RHSet.ofList (objs.map Prod.fst)
    scheduler := (default : SeLe4n.Model.SchedulerState).setCurrentOnCore
      SeLe4n.Kernel.Concurrency.bootCoreId (some t) }

/-- The syscall entry's save on the boot core, of the context handed over —
`saveCapturedSyscallFrame` over `registerFileOfTrapContext`, the binding the
entry uses.  Both arguments owned. -/
@[export sele4n_probe_save_captured_syscall_frame]
def saveProbeCapturedSyscallFrame (st : SeLe4n.Model.SystemState) (c : TrapContext) :
    SeLe4n.Model.SystemState :=
  saveCapturedSyscallFrame st SeLe4n.Kernel.Concurrency.bootCoreId
    (some (registerFileOfTrapContext c))

/-- Word `i` of the context saved in thread `tid`'s TCB, at the trap frame's
layout (`trapWordsOfRegisterFile`), or every bit set when `tid` has no TCB.
Owned, as above. -/
@[export sele4n_probe_saved_context_word]
def saveProbeContextWord (st : SeLe4n.Model.SystemState) (tid i : UInt64) : UInt64 :=
  match st.getTcb? ⟨tid.toNat⟩ with
  | some tcb => trapWordsOfRegisterFile tcb.registerContext i.toNat
  | none => 0xFFFF_FFFF_FFFF_FFFF

end SeLe4n.Testing.BoundaryProbes
