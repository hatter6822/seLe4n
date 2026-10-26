-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry.Invariant

/-! # Service Invariant Preservation — Re-export Hub (seLe4n Extension)

**The Service subsystem is a seLe4n-specific extension** — seL4 has no
kernel-level service management. See `Service/Registry.lean` for rationale.

Re-exports **Registry/Invariant**: the WS-Q1-C registry invariant
(endpoint/interface validity) and its preservation under the registry
operations.

WS-ZA ZA5.4 part 32 removed the kernel's service dependency graph and, with
it, the two modules this hub also re-exported: the graph's policy surface and
its acyclicity proofs.  No kernel entry wrote the graph and no check read it;
isolation between services comes from capabilities, and dependency policy
belongs to a user-level service manager, as in seL4.
-/
