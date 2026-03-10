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
