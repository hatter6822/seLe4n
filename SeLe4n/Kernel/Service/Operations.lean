-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry

/-! # Service Operations — Re-export Hub (seLe4n Extension)

**This subsystem is a seLe4n-specific extension with no analogue in real seL4.**

seL4 provides no kernel-level service management: service dependencies and
orchestration are left to user-level components (a component framework such
as CAmkES).  seLe4n keeps one kernel table for services, the
capability-indexed **service registry** (`Service/Registry.lean`): a
registration names an interface and an endpoint capability, the endpoint
records the registration it carries (`Endpoint.serviceCode`), and the
operations are `registerInterface`, `registerService`, `revokeService` and the
O(1) lookup `lookupServiceByRecordedCode` (specified by `lookupServiceByCap`).

This module re-exports those operations, beside `Service/Invariant.lean`,
which re-exports their invariants, as every subsystem splits its operations
from its proofs.

WS-ZA ZA5.4 part 32 removed the kernel's service dependency graph, whose
operations lived here (the dependency registration with its cycle check and
the bounded reachability walk).  No kernel entry wrote the graph and no check
read its isolation edges: isolation between services comes from capabilities,
and dependency policy belongs to a user-level service manager, as in seL4. -/
