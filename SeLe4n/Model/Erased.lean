-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# Erased values (ghost state)

WS-ZA ZA4.5: `Erased α` holds a value of `α` that proofs can read and the
compiled kernel never stores.  It is the predicate "equals some fixed `a`",
a `Prop`-valued function, so the compiler erases it: a structure field of
this type costs nothing at run time, and a write through `map` computes
nothing.  Reading the value back (`out`) is `noncomputable`, so executable
code cannot depend on ghost state — a definition that tries fails to
compile, which is how the kernel proves it runs on the concrete state alone.
-/

namespace SeLe4n

universe u v

/-- A value of `α` kept for proofs only; erased by the compiler. -/
def Erased (α : Sort u) : Sort (max 1 u) :=
  { s : α → Prop // ∃ a, (fun b => a = b) = s }

namespace Erased

/-- Wrap a value as ghost state. -/
@[inline] def mk {α : Sort u} (a : α) : Erased α := ⟨fun b => a = b, a, rfl⟩

/-- The ghost value, for proofs. -/
noncomputable def out {α : Sort u} (a : Erased α) : α := Classical.choose a.2

/-- Apply a function to the ghost value; computes nothing at run time. -/
@[inline] def map {α : Sort u} {β : Sort v} (f : α → β) (a : Erased α) : Erased β :=
  mk (f a.out)

@[simp] theorem out_mk {α : Sort u} (a : α) : (mk a).out = a := by
  have h := Classical.choose_spec (mk a).2
  exact (congrFun h a).mpr rfl

@[simp] theorem mk_out {α : Sort u} (a : Erased α) : mk a.out = a := by
  obtain ⟨s, x, rfl⟩ := a
  apply Subtype.ext
  show (fun b => out ⟨_, x, rfl⟩ = b) = fun b => x = b
  have : out (⟨fun b => x = b, x, rfl⟩ : Erased α) = x := out_mk x
  rw [this]

theorem ext {α : Sort u} {a b : Erased α} (h : a.out = b.out) : a = b := by
  rw [← mk_out a, ← mk_out b, h]

@[simp] theorem out_map {α : Sort u} {β : Sort v} (f : α → β) (a : Erased α) :
    (a.map f).out = f a.out := out_mk _

instance {α : Sort u} [Inhabited α] : Inhabited (Erased α) := ⟨mk default⟩

instance {α : Type u} : Repr (Erased α) := ⟨fun _ _ => "<ghost>"⟩

end Erased

end SeLe4n
