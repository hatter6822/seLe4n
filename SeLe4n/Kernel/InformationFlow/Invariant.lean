-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Invariant.Helpers
import SeLe4n.Kernel.InformationFlow.Invariant.Operations
import SeLe4n.Kernel.InformationFlow.Invariant.Composition

/-! # Information Flow Invariant — Re-export Hub

Decomposed into:
- **Helpers**: Shared NI proof infrastructure (projection preservation for
  storeObject, scheduler, TCB state mutations, list filtering, notification ops).
- **Operations**: Per-operation NI proofs (service, enforcement bridges,
  scheduler compound, VSpace, CSpace CRUD, IPC endpoint operations).
- **Composition**: NonInterferenceStep inductive bundle (30+ operations),
  step/trace composition, declassification, preservesLowEquivalence.
-/
