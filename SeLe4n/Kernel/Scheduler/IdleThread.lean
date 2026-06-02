-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types

/-!
# Per-core idle-thread identities

The per-core idle-thread *identifiers* (`idleThreadIdBase`, `idleThreadId`, and
their injectivity witnesses).  These live in the scheduler layer (rather than in
`Platform.Boot` where the WS-SM SM4.G *bootstrap* installs them) because the
per-core scheduler dispatcher — `scheduleEffectiveOnCore`
(`Scheduler/Operations/Core.lean`) — must reference `idleThreadId` to run a
core's idle thread when nothing else is runnable, and the dispatcher is
*upstream* of `Platform.Boot` in the import graph.

The idle *TCB constructor* (`createIdleThread`) and the *boot installer*
(`installIdleThread`, `bootFromPlatformWithIdleThreads`) remain in
`Platform.Boot` (they need the `IntermediateState` / `Builder` machinery); the
SM5.E theorems (`Scheduler/Operations/PerCoreIdle.lean`) consume both.
-/

namespace SeLe4n.Kernel

open SeLe4n.Kernel.Concurrency (CoreId)

/-- **WS-SM SM4.G** (plan §3.7): reserved base ObjId for per-core idle
    threads.  The idle thread for core `c` lives at the `ObjId`
    `idleThreadIdBase + c.val`.  The value sits above the 16-bit ObjId space
    (`0x1_0000 = 65536`) that platform configs assign their objects from, so
    on the canonical platforms the per-core idle range
    `[idleThreadIdBase, idleThreadIdBase + numCores)` is disjoint from the
    config objects.

    The boot-install theorems (`bootFromPlatformWithIdleThreads_all_cores_have_idle`
    and the scheduler-bundle theorems) hold **unconditionally** — the idle TCB
    is installed regardless of the base config, because `createObject`'s insert
    is overwriting.  The disjointness is what guarantees the install does not
    *clobber* a config object: `idleSlotsFreshAt` is the freshness precondition,
    `bootFromPlatformWithIdleThreads_preserves_platform_objects` proves the
    install is purely additive under it, and
    `idleSlotsFreshAt_of_initialObjects_below_base` discharges freshness for any
    config whose objects live below `idleThreadIdBase` (the canonical case).
    The bound is **not** assumed for arbitrary configs. -/
def idleThreadIdBase : Nat := 0x1_0000

/-- **WS-SM SM4.G** (plan §3.7): the per-core idle thread's `ThreadId`.  Idle
    threads are injective in the core (`idleThreadId_injective`), so the
    per-core idle objects never alias one another. -/
def idleThreadId (c : CoreId) : SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofNat (idleThreadIdBase + c.val)

/-- **WS-SM SM4.G**: `idleThreadId` is injective in the core. -/
theorem idleThreadId_injective {c₁ c₂ : CoreId}
    (h : idleThreadId c₁ = idleThreadId c₂) : c₁ = c₂ := by
  unfold idleThreadId at h
  have hv : idleThreadIdBase + c₁.val = idleThreadIdBase + c₂.val :=
    SeLe4n.ThreadId.ofNat_injective h
  exact Fin.ext (Nat.add_left_cancel hv)

/-- **WS-SM SM4.G**: distinct cores get distinct idle-thread ids. -/
theorem idleThreadId_ne {c₁ c₂ : CoreId}
    (h : c₁ ≠ c₂) : idleThreadId c₁ ≠ idleThreadId c₂ :=
  fun hEq => h (idleThreadId_injective hEq)

/-- **WS-SM SM4.G**: distinct cores get distinct idle-thread `ObjId`s
    (the object-store key form of `idleThreadId_ne`). -/
theorem idleThreadId_toObjId_ne {c₁ c₂ : CoreId}
    (h : c₁ ≠ c₂) : (idleThreadId c₁).toObjId ≠ (idleThreadId c₂).toObjId := by
  intro hEq
  apply idleThreadId_ne h
  -- toObjId is `ObjId.ofNat ∘ toNat`; recover the ThreadId equality.
  have : (idleThreadId c₁).toNat = (idleThreadId c₂).toNat := by
    have h1 : (idleThreadId c₁).toObjId.val = (idleThreadId c₁).toNat := rfl
    have h2 : (idleThreadId c₂).toObjId.val = (idleThreadId c₂).toNat := rfl
    rw [← h1, ← h2, hEq]
  calc idleThreadId c₁ = SeLe4n.ThreadId.ofNat (idleThreadId c₁).toNat :=
          (SeLe4n.ThreadId.ofNat_toNat _).symm
    _ = SeLe4n.ThreadId.ofNat (idleThreadId c₂).toNat := by rw [this]
    _ = idleThreadId c₂ := SeLe4n.ThreadId.ofNat_toNat _

end SeLe4n.Kernel
