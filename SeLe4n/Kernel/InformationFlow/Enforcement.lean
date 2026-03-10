/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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
