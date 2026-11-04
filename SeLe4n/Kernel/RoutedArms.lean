-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Dispatch

/-!
# The routed syscall entry's arms, out of line

Import-only hub.  `RoutedArms/Report.lean` is the report word an arm hands its
result back on; one module per route holds that route's arm as its own
function (`Signal`, `Wait`, `Yield`, `Send`, `Call`, `Reply`, `Receive`,
`ReplyRecv`, `Invocation`, `OverflowOne`, `Audited`, `Decoded`); and
`RoutedArms/Dispatch.lean` is the dispatch over them, the compiled form of the
continued entry (`syscallEntryCheckedK_eq_routed`).
-/
