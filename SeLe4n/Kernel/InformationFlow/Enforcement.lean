import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers
import SeLe4n.Kernel.InformationFlow.Enforcement.Soundness

/-! # Information-Flow Enforcement — Re-export Hub

Decomposed into:
- **Wrappers**: Policy-gated operation wrappers (endpointSendDualChecked,
  cspaceMintChecked, serviceRestartChecked, notificationSignalChecked,
  cspaceCopyChecked, cspaceMoveChecked, endpointReceiveDualChecked) and
  enforcement boundary specification.
- **Soundness**: Correctness theorems, enforcement soundness meta-theorem,
  declassification enforcement, and IF config invariant bundle.
-/
