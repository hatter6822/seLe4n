import SeLe4n.Model.Object.Types
import SeLe4n.Model.Object.Structures

/-! # Kernel Objects — Re-export Hub

Decomposed into:
- **Types**: Core data type definitions (ServiceStatus, Capability, IpcMessage,
  TCB, IntrusiveQueue, Endpoint, Notification, CNode basics, UntypedObject).
- **Structures**: Complex kernel object structures (PagePermissions, VSpaceRoot
  with lookup/map/unmap and overlap invariants, CNode with resolve/insert/remove
  and slot-uniqueness/count-bound proofs, KernelObject sum type).
-/
