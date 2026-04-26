/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# S2-I: Shared Test Helpers

Common test assertion helpers extracted from individual test suites to eliminate
duplication. All test suites should import this module rather than defining
private copies of these functions.
-/

open SeLe4n.Model

namespace SeLe4n.Testing

/-- Boolean assertion with labeled pass/fail output.

AN11-E.9 (TST-M09): a runtime guard rejects empty `tag`/`label` strings
to surface mistaken empty-string callers immediately rather than letting
them produce uninterpretable `[]` output.  Existing call sites all pass
non-empty literals, so the guard is a tightening on the test surface
only. -/
def expectCond (tag : String) (label : String) (cond : Bool) : IO Unit := do
  if tag.isEmpty then
    throw <| IO.userError "expectCond: tag must be non-empty (AN11-E.9 / TST-M09)"
  if label.isEmpty then
    throw <| IO.userError "expectCond: label must be non-empty (AN11-E.9 / TST-M09)"
  if cond then
    IO.println s!"{tag} check passed [{label}]"
  else
    throw <| IO.userError s!"{tag} check failed [{label}]"

/-- Assert that a kernel operation returned an error matching `expected`.
    The optional `msgPrefix` parameter supports suite-specific message formatting.

AN11-E.9 (TST-M09): a runtime guard rejects empty `label`/`msgPrefix`
strings.  Same rationale as `expectCond` — surfaces caller mistakes
immediately rather than producing an unhelpful `[]:` message. -/
def expectError
    (label : String)
    (actual : Except KernelError α)
    (expected : KernelError)
    (msgPrefix : String := "check") : IO Unit := do
  if label.isEmpty then
    throw <| IO.userError "expectError: label must be non-empty (AN11-E.9 / TST-M09)"
  if msgPrefix.isEmpty then
    throw <| IO.userError "expectError: msgPrefix must be non-empty (AN11-E.9 / TST-M09)"
  match actual with
  | .ok _ =>
      throw <| IO.userError s!"{label}: expected error {toString expected}, got success"
  | .error err =>
      if err = expected then
        IO.println s!"{msgPrefix} passed [{label}]: {toString err}"
      else
        throw <| IO.userError s!"{label}: expected {toString expected}, got {toString err}"

/-- Assert that a kernel operation returned `.ok` and return the value. -/
def expectOk
    (label : String)
    (actual : Except KernelError α)
    (msgPrefix : String := "check") : IO α :=
  match actual with
  | .ok value => do
      IO.println s!"{msgPrefix} passed [{label}]"
      pure value
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

/-- Assert that a kernel operation returned `.ok` with a state pair. -/
def expectOkState
    (label : String)
    (actual : Except KernelError (α × SystemState))
    (msgPrefix : String := "check") : IO (α × SystemState) :=
  match actual with
  | .ok result => do
      IO.println s!"{msgPrefix} passed [{label}]"
      pure result
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

/-- Extract the state from a successful kernel operation, discarding the unit value. -/
def runKernelState
    (label : String)
    (actual : Except KernelError (Unit × SystemState)) : IO SystemState :=
  match actual with
  | .ok (_, st) => pure st
  | .error err =>
      throw <| IO.userError s!"{label}: expected success, got {toString err}"

/-! W5-B: Test fixture OID ranges (prevent collisions between suites).
Each test suite reserves a disjoint range of ObjId values to avoid
accidental interference when suites are run independently.

  Suite                    OID Range   Notes
  MainTraceHarness         1-40        threads: 1-5, objects: 6-40
  OperationChainSuite      200-962     chains use 200+, syscall chains 500+, svc lifecycle 960+
  NegativeStateSuite       6-99        overlaps MainTrace (runs independently)
  FrozenOpsSuite           10-11       frozen kernel monad tests
  FrozenStateSuite         1-7         FrozenMap/FrozenSet unit tests
  FreezeProofSuite         1-20        freeze proof verification
  TwoPhaseArchSuite        1-100       builder-to-freeze-to-execution pipeline
  RobinHoodSuite           N/A         uses RHTable keys, not ObjId
  RadixTreeSuite           N/A         uses CNodeRadix keys, not ObjId
  InformationFlowSuite     1-30        info flow policy checks
  TraceSequenceProbe       1-40        mirrors MainTraceHarness

Suites with overlapping ranges run independently and do not share state. -/

end SeLe4n.Testing
