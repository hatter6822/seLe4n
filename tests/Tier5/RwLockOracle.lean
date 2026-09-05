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
prints the serialised state on stdout — one line per state: the initial
state, then the state after every op (PR #890 review round 5).

## Wire format

* `R<core>` — `tryAcquireRead core`
* `r<core>` — `releaseRead core`
* `W<core>` — `tryAcquireWrite core`
* `w<core>` — `releaseWrite core`
* `c<core>` — `cancel core` (WS-LC LC3.6)

Each op is terminated by a comma `,`.  Whitespace between ops is
ignored.  Example: `"R0,R1,r0,W2,w2,"` is the 5-op sequence
`tryAcquireRead 0; tryAcquireRead 1; releaseRead 0; tryAcquireWrite 2; releaseWrite 2`.

**`c` is the withdrawal**, and it means something on the Rust side only
because that side now drives *queued* waiters: the oracle's driver takes a
real ticket for every acquisition, admitted or not, so a withdrawal has a
request to withdraw.  The CAS-retry lock takes no part — it has no queue —
which is the same asymmetry `opCorresponds.cancel_no_queue` states.

## Output format

One line per state, each `W=<core|->;R=<sorted reader cores>;Q=<core:r|w,...>`:

* `W=` is the writer's core id, or `-` when `writerHeld` is `none`;
* `R=` is `readers` as a **sorted** list of core ids, since the order of
  `readers` is not semantic (`promoteWaitersOnWriterRelease` prepends a
  promoted batch, the Rust driver admits one core at a time);
* `Q=` is `waiters` **in order**, each core with its mode, `r` or `w`.

Until PR #890 review round 5 both oracles printed a "canonical short form"
`W=<flag>;R=<count>;Q=<length>` — the writer flag, the reader count and
the queue length — chosen so that the Rust side could report what its
bit-packed word held.  That form collapsed identity: a spec regression
promoting the wrong waiter, reordering the queue or changing a queued
mode agreed with the implementation on every count while disagreeing on
every core.  The Rust oracle now reads the identities back out of the
deployed ticket lock's per-core words, so both sides print the same
identity line, and both print it after every step, so a divergence that
later converges is caught as well.
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
      | 'c' => some (.cancel          c)
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

/-- Insert `n` into an ascending list, keeping it ascending. -/
def insertAscending (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs => if n ≤ x then n :: x :: xs else x :: insertAscending n xs

/-- Sort a list of naturals ascending (insertion sort — the lists here
have at most `numCores` elements). -/
def sortAscending (xs : List Nat) : List Nat :=
  xs.foldr insertAscending []

/-- Serialise a state to the identity form: the writer's core, the
sorted reader cores, the queue in order with each request's mode. -/
def renderState (s : RwLockState) : String :=
  let writer := match s.writerHeld with
    | some c => toString c.val
    | none => "-"
  let readers := String.intercalate ","
    ((sortAscending (s.readers.map (·.val))).map toString)
  let queue := String.intercalate ","
    (s.waiters.map fun (c, m) =>
      s!"{c.val}:{match m with | .read => "r" | .write => "w"}")
  s!"W={writer};R={readers};Q={queue}"

/-- Exit status on a trace that does not parse — the Rust oracle's too,
so the harness reads one number for one condition on both sides. -/
def parseErrorStatus : UInt8 := 2

/-- Main: read stdin, parse, fold, printing the state before the first op
and after each one. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match parseTrace input with
  | none =>
      IO.eprintln "rw_lock_oracle: parse error"
      IO.Process.exit parseErrorStatus
  | some ops =>
      IO.println (renderState RwLockState.unheld)
      let _ ← ops.foldlM (init := RwLockState.unheld) fun s op => do
        let s' := s.applyOp op
        IO.println (renderState s')
        pure s'

end SeLe4n.Tier5.RwLockOracle

/-- Lake-callable entry point. -/
def main : IO Unit := SeLe4n.Tier5.RwLockOracle.main
