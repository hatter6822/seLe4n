-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import Lean

/-!
# The simp set that carries the machine's physical-address width

WS-ZA ZA6.37.  No kernel write sets the machine's physical-address width, so a
step's width goal closes by rewriting each write's machine (or the width itself)
back to the state it started from.  Each such lemma carries this attribute, and
the `records_width` tactic (`KernelRecords.Frame`) rewrites with the set.
-/

register_simp_attr records_width_simp
