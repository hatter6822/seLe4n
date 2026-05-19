-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-SM SM2.C-defer D-6 — Lean-side RwLock oracle binary

This file implements the Lean half of the Tier-5 cross-language
correspondence harness.  See:
`docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` §5.6

## Operation

The binary reads an op-sequence on stdin (textual wire format), folds
`RwLockState.applyOp` over the parsed ops starting from `unheld`, and
prints the canonical serialised post-state on stdout.

## Wire format

* `R<core>` — `tryAcquireRead core`
* `r<core>` — `releaseRead core`
* `W<core>` — `tryAcquireWrite core`
* `w<core>` — `releaseWrite core`

Each op is terminated by a comma `,`.  Whitespace between ops is
ignored.  Example: `"R0,R1,r0,W2,w2,"` is the 5-op sequence
`tryAcquireRead 0; tryAcquireRead 1; releaseRead 0; tryAcquireWrite 2; releaseWrite 2`.

## Output format

`W=<flag>;R=<count>;Q=<n>`

where:
* `<flag>` is `1` if writerHeld.isSome else `0`
* `<count>` is `readers.length`
* `<n>` is `waiters.length`

This canonical short form decouples the abstract spec's richer state
(which tracks WHICH cores are readers) from the Rust impl's bit-packed
state (which only tracks counts).  Both sides agree on the count form.
-/

namespace SeLe4n.Tier5.RwLockOracle

open SeLe4n.Kernel.Concurrency

/-- Parse a decimal `CoreId` from a string slice.  Returns `none` if
the value is out of range or the string is not a valid decimal. -/
def parseCoreId (s : String) : Option CoreId :=
  match s.toNat? with
  | none => none
  | some n =>
    if h : n < numCores then some ⟨n, h⟩ else none

/-- Parse one op from a single token (no comma).  -/
def parseOp (token : String) : Option RwLockOp :=
  if token.isEmpty then none
  else
    let head := token.toList.headD ' '
    let rest := token.toList.tailD [] |> String.ofList
    let coreId := parseCoreId rest
    coreId.bind fun c =>
      match head with
      | 'R' => some (.tryAcquireRead  c)
      | 'r' => some (.releaseRead     c)
      | 'W' => some (.tryAcquireWrite c)
      | 'w' => some (.releaseWrite    c)
      | _   => none

/-- Parse a comma-separated sequence of ops.  Returns `none` on any
parse error. -/
def parseTrace (input : String) : Option (List RwLockOp) :=
  let tokens := input.splitOn ","
    |>.map (fun s => s.trimAscii.toString)
    |>.filter (fun s => !s.isEmpty)
  tokens.foldr
    (fun tok acc =>
      acc.bind fun ops =>
        (parseOp tok).map fun op => op :: ops)
    (some [])

/-- Serialise a final state to the canonical textual form. -/
def renderState (s : RwLockState) : String :=
  let flag := if s.writerHeld.isSome then "1" else "0"
  let count := toString s.readers.length
  let waiters := toString s.waiters.length
  s!"W={flag};R={count};Q={waiters}"

/-- Main: read stdin, parse, fold, print. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseTrace input with
  | none =>
      IO.eprintln "rw_lock_oracle: parse error"
      IO.Process.exit 1
  | some ops =>
      let finalState := ops.foldl RwLockState.applyOp RwLockState.unheld
      IO.println (renderState finalState)

end SeLe4n.Tier5.RwLockOracle

/-- Lake-callable entry point. -/
def main : IO Unit := SeLe4n.Tier5.RwLockOracle.main
