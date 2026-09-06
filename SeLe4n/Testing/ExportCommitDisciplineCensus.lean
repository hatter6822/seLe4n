-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import Lean.Elab.Command
-- Both roots, for the reason `BootEntryContract` records: `SeLe4n` is the
-- production library — the import closure Lake compiles into `SeLe4n:static`,
-- and therefore the set of modules whose `@[export]` can emit a symbol a kernel
-- image links — and `Platform.Staged` pulls the staged modules in beside it.
-- With `Staged` alone, a seam defined in a module only `SeLe4n.lean` imports
-- would read as absent and this census would pass vacuously about it.
import SeLe4n
import SeLe4n.Platform.Staged

/-!
# WS-RR RR7.13 — every state-committing `@[export]` is classified

RR7.12 made the syscall seam acquire the footprint `lockSetForSyscall` declares
for the operation it runs.  What keeps that true is not the code that does it —
it is that **the next seam cannot quietly skip it**.

The subject is every `@[export]` declaration whose body can reach a kernel-state
commit, and the question is whether that commit runs inside a lock bracket.  The
answers are two, and both are legitimate:

* **bracketed** — the body reaches `runUnderDeclaredLockSet` or
  `Concurrency.withLockSet`, so its transition runs inside a declared footprint;
* **unbracketed** — it commits without one, which is *sound* (the SM5.I global
  kernel-entry ticket lock still serialises every commit) but is the state
  RR7.12 exists to shrink.  It is admitted only with a **recorded reason**.

The set of state-committing exports is **derived**, not listed: a new seam that
commits and is not classified fails this module's elaboration, which is the
enumeration-versus-derivation shape the key conventions warn about, applied to
the one place a fine-lock claim can silently stop being true.

## Why the elaborator and not a scanner

This is a question about *which constants a declaration's body reaches*, and
`Expr.getUsedConstants` answers it: by the time a declaration is in the
environment its references are resolved constants, and a constant has one
definition.  A text scanner asking the same question has eleven rounds of
review findings against it in `scripts/check_kernel_entry_exports.py`'s history
— a name is not a definition, an alias is not the callee, a comment is not code.
None of those questions can be asked here.

## What the reachability is, exactly

`reachesConstant` is the transitive closure of `getUsedConstants`, which
**over-approximates**: a body that merely mentions a constant in a branch it
never takes still counts as reaching it.  That is the fail-closed direction for
this census — a seam that mentions `modifyGetKernelState` anywhere must be
classified — and it is *not* the direction that would let an unbracketed commit
pass, since the bracket half is checked the same way and a body that mentions
the bracket without running it would be a lie a reader of the registry could
still catch.  Deciding "the commit is *dominated* by the acquire" is a question
about what a program does, and this file does not ask it: PR #889 rounds 18–21
are four consecutive findings against a hand-written analysis that tried.

The walk is fuel-bounded and reports exhaustion as a violation, so a
pathological constant graph fails the census rather than passing it.
-/

namespace SeLe4n.Testing.ExportCommitDisciplineCensus

open Lean Elab Command

/-- The primitives that install kernel state.  Every one is a write to
`Platform.FFI.kernelStateRef`; a body that can reach any of them commits. -/
def commitPrimitives : List Name :=
  [ `SeLe4n.Platform.FFI.modifyGetKernelState
  , `SeLe4n.Platform.FFI.updateKernelState
  , `SeLe4n.Platform.FFI.initialiseKernelState ]

/-- The bracket forms a committing body may run its transition inside.

`runUnderDeclaredLockSet` is RR7.12's revalidated bracket at the ABI seam;
`Concurrency.withLockSet` is SM3's plain one, which the raw
`suspend_thread_cross_core` seam has used since SM3.C.9. -/
def bracketForms : List Name :=
  [ `SeLe4n.Kernel.runUnderDeclaredLockSet
  , `SeLe4n.Kernel.Concurrency.withLockSet ]

/-- How an exported seam commits. -/
inductive CommitDiscipline where
  /-- Its transition runs inside a declared per-object footprint. -/
  | bracketed
  /-- It commits under the SM5.I global kernel-entry lock alone.  Sound, and the
  state RR7.12 exists to shrink — admitted only with a reason recorded here. -/
  | unbracketed (reason : String)
  deriving Inhabited

/-- `true` for a constant this project defines — including the compiler's
auxiliaries (`…match_1`, `…proof_2`) and private declarations, whose mangled
names keep the `SeLe4n` components.

The walk below descends only into these.  A Lean-core or `Std` constant cannot
call back into `SeLe4n`, and where a project body hands a project function to a
core combinator that function is in the *caller's* `getUsedConstants` already —
so confining the descent loses no reachability while keeping the walk over this
kernel's constant graph rather than over the whole toolchain's. -/
def isProjectConstant (n : Name) : Bool :=
  n.components.any (· == `SeLe4n)

/-- `true` when `n`'s body can reach any of `targets`, following project
constants transitively.

Fuel-bounded, and an exhausted walk answers **`true`**: this predicate decides
"must be classified" and "claims a bracket", and in both the conservative answer
is the one that makes the census demand more rather than less.  The bound is far
above the closure of any seam in this tree (measured in the hundreds), so
exhaustion means the graph changed shape and the census should be looked at. -/
partial def reachesAny (env : Environment) (targets : List Name) (n : Name) : Bool :=
  go [n] {} 200000
where
  go (worklist : List Name) (seen : NameSet) (fuel : Nat) : Bool :=
    match fuel, worklist with
    | 0, _ => true            -- fail closed: an exhausted walk answers "reaches"
    | _, [] => false
    | fuel' + 1, c :: rest =>
      if targets.contains c then true
      else if seen.contains c || !isProjectConstant c then go rest seen fuel'
      else
        let seen := seen.insert c
        match (env.find? c).bind (·.value? (allowOpaque := true)) with
        | none => go rest seen fuel'
        | some v => go (v.getUsedConstants.toList ++ rest) seen fuel'

/-- `true` when `n` can reach a kernel-state commit. -/
def commitsState (env : Environment) (n : Name) : Bool :=
  reachesAny env commitPrimitives n

/-- `true` when `n` can reach a lock bracket. -/
def runsBracketed (env : Environment) (n : Name) : Bool :=
  reachesAny env bracketForms n

/-- Why `n`'s recorded discipline does not match what its body reaches; `[]`
when it does.

Both directions.  A `bracketed` claim that the body cannot substantiate is the
dangerous one — a reader of the registry would take the seam for covered.  An
`unbracketed` record on a body that *has* since been bracketed is the harmless
one, and is still a failure: the registry is the project's statement of how much
of the kernel is covered, and an out-of-date one understates progress as
silently as it overstates it. -/
def disciplineViolations (env : Environment) (n : Name) (declared : CommitDiscipline) :
    List String :=
  match declared with
  | .bracketed =>
      if runsBracketed env n then []
      else [s!"`{n}` is recorded as running inside a lock bracket, and its body reaches \
              neither `runUnderDeclaredLockSet` nor `Concurrency.withLockSet`"]
  | .unbracketed reason =>
      if reason.isEmpty then
        [s!"`{n}` is recorded as committing unbracketed with an empty reason; an unbracketed \
            commit is admitted only with one"]
      else if runsBracketed env n then
        [s!"`{n}` is recorded as committing unbracketed, and its body now reaches a lock \
            bracket — the record understates what the kernel covers and must be updated"]
      else []

/-! ## The registry

One entry per state-committing `@[export]`.  The **set** is derived from the
environment and reconciled against this list in both directions below, so a new
committing seam is a failure here on the day it is written — not a silent
addition to the unbracketed majority. -/

/-- Every state-committing `@[export]` of this kernel, with how it commits.

Two of seven bracket today.  The five that do not each name the row that closes
them, so this list is the project's honest statement of how much of the kernel
the fine-lock discipline actually covers — the figure a release claim has to
quote. -/
def commitDisciplineRegistry : List (Name × CommitDiscipline) :=
  [ -- SM3.C.9's first bracketed seam: resolves `lockSetForSyscall .tcbSuspend`
    -- and runs `suspendThreadOnCore` inside it.
    (`SeLe4n.Kernel.suspendThreadCrossCoreEntry, .bracketed)
    -- WS-RR RR7.12: the ABI seam, revalidated.  Bracketed for the eight
    -- declared arms and falling back — bit-identically — for the rest.
  , (`SeLe4n.Kernel.syscallDispatchCrossCoreEntry, .bracketed)
    -- The three per-core scheduler entries.  They commit run-queue and
    -- replenish-queue state, which lives in the `SchedLockId` domain rather
    -- than the object-lock domain a `LockSet` names, so bracketing them needs
    -- the scheduler-domain footprints composed first — the registered
    -- `UncoveredLockDomain.schedulerDomain`, closed by WS-RR's Track C closure
    -- rows.
  , (`SeLe4n.Kernel.perCoreTimerTickEntry,
      .unbracketed "scheduler domain: commits per-core run-queue and replenish-queue \
        state, whose locks are `SchedLockId`s and not members of any `LockSet`; \
        registered as `UncoveredLockDomain.schedulerDomain`")
  , (`SeLe4n.Kernel.perCoreRescheduleEntry,
      .unbracketed "scheduler domain: same as the timer tick — the `.reschedule` SGI \
        receiver dispatches a successor on the receiving core")
  , (`SeLe4n.Kernel.secondaryKernelMain,
      .unbracketed "scheduler domain: the secondary bring-up entry installs a core's \
        first current thread before any footprint could name it")
    -- The two fault-delivery entries.  A fault is not a syscall, so
    -- `lockSetForSyscall` has no arm for it; its footprint is the `.call`
    -- chain's plus the faulting thread's TCB, and declaring that is WS-RR RR4's
    -- surface extended rather than an existing arm reused.
  , (`SeLe4n.Kernel.faultEntry,
      .unbracketed "fault delivery: a fault is not a syscall, so `lockSetForSyscall` \
        declares no footprint for it; the delivery composes the `.call` chain, whose \
        footprint would have to be resolved from the fault rather than from a decode")
  , (`SeLe4n.Kernel.unknownSyscallEntry,
      .unbracketed "fault delivery: an unknown syscall number is delivered through the \
        same entry, with the same missing declaration") ]

/-- The seams that commit and are recorded as bracketed. -/
def bracketedSeams : List Name :=
  commitDisciplineRegistry.filterMap
    (fun (n, d) => match d with | .bracketed => some n | .unbracketed _ => none)

/-- Where the derived set of state-committing exports and the registry disagree;
`[]` when they are the same set.

**Both directions, and both matter.**  An *unrecorded* seam is the dangerous one:
a new `@[export]` that commits kernel state and is nowhere in the registry has
silently joined the unbracketed majority, which is exactly how a fine-lock claim
stops being true without anyone editing it.  A *stale* entry is the other: the
registry is what the project's coverage figure is read off, so an entry naming a
declaration that no longer commits — or no longer exports — overstates it.

Pure, over two lists, so the reconciliation is self-tested on synthetic inputs
below.  The derived half cannot be exercised in place: planting a committing
`@[export]` to test the census would emit a real symbol into the kernel's
archive. -/
def reconciliationViolations (derived recorded : List Name) : List String :=
  let unrecorded := derived.filter (fun n => !recorded.contains n)
  let stale := recorded.filter (fun n => !derived.contains n)
  (if unrecorded.isEmpty then [] else
    [s!"{unrecorded.length} state-committing `@[export]` declaration(s) are not classified \
        ({unrecorded}).  Every seam that commits kernel state either runs inside a lock \
        bracket or is recorded with the reason it does not"]) ++
  (if stale.isEmpty then [] else
    [s!"{stale.length} registry entr(ies) name declarations that are not state-committing \
        exports of this environment ({stale}) — the registry is what the coverage claim is \
        read off, so a stale entry overstates it"])

/-! ## Witnesses

The census is only as good as its ability to *refuse*, and a census that
accepted everything would read exactly like a passing one.  These are ordinary
private declarations — **not** exported, so they add no symbol and enter no
derived set — held against the same predicate the registry entries are.

Each plants the shape the plan names: a body that commits with no bracket at
all, one that commits through a helper (so the walk must be transitive rather
than one level deep), and one that commits nothing. -/

/-- Commits inside RR7.12's bracket. -/
private def censusWitnessBracketed : BaseIO Unit := do
  let _ ← SeLe4n.Platform.FFI.modifyGetKernelState (fun st =>
    match SeLe4n.Kernel.runUnderDeclaredLockSet (fun _ => none) SeLe4n.Kernel.Concurrency.bootCoreId
        (fun s => ((), s)) st with
    | .undeclared r => r
    | .committed r => r
    | .refused u => ((), u))
  pure ()

/-- **The bare commit the plan asks this gate to catch**: a state-committing
body with no bracket anywhere in it. -/
private def censusWitnessBareCommit : BaseIO Unit := do
  let _ ← SeLe4n.Platform.FFI.modifyGetKernelState (fun st => ((), st))
  pure ()

/-- Commits through a helper, so a one-level `getUsedConstants` check would miss
it and the transitive walk must not. -/
private def censusWitnessCommitHelper (st : SeLe4n.Model.SystemState) : BaseIO Unit :=
  SeLe4n.Platform.FFI.initialiseKernelState st

private def censusWitnessIndirectCommit : BaseIO Unit :=
  censusWitnessCommitHelper default

/-- Commits nothing: reads the state and returns. -/
private def censusWitnessNoCommit : BaseIO Unit := do
  let _ ← SeLe4n.Platform.FFI.getKernelState
  pure ()

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- The environment is the production one; a seam defined in a module only
  -- `SeLe4n.lean` imports must be visible here or the census would be silent
  -- about exactly the declarations that link.
  unless env.header.moduleNames.contains `SeLe4n do
    throwError "export-commit census: the production library root `SeLe4n` is not in this \
      environment, so a seam defined in a module only it imports would read as absent"
  -- The subjects exist: a census whose commit primitives or bracket forms had
  -- been renamed would classify everything as non-committing and pass.
  for n in commitPrimitives ++ bracketForms do
    unless (env.find? n).isSome do
      throwError "export-commit census: `{n}` is not a declaration of this environment, so \
        the property this census decides does not exist"
  -- Witnesses, both directions.
  unless commitsState env ``censusWitnessBareCommit do
    throwError "export-commit census: the bare-commit witness is not seen to commit"
  unless commitsState env ``censusWitnessIndirectCommit do
    throwError "export-commit census: a commit reached through a helper is not seen — the \
      walk is not transitive"
  if commitsState env ``censusWitnessNoCommit then
    throwError "export-commit census: a body that only reads the state is seen to commit"
  unless (disciplineViolations env ``censusWitnessBracketed .bracketed).isEmpty do
    throwError "export-commit census: the bracketed witness was refused as bracketed"
  if (disciplineViolations env ``censusWitnessBareCommit .bracketed).isEmpty then
    throwError "export-commit census: a BARE COMMIT was accepted as bracketed — the gate \
      does not detect the shape it exists for"
  unless (disciplineViolations env ``censusWitnessBareCommit (.unbracketed "recorded")).isEmpty do
    throwError "export-commit census: a bare commit was refused even with a recorded reason"
  if (disciplineViolations env ``censusWitnessBareCommit (.unbracketed "")).isEmpty then
    throwError "export-commit census: an unbracketed record with an empty reason was accepted"
  if (disciplineViolations env ``censusWitnessBracketed (.unbracketed "stale")).isEmpty then
    throwError "export-commit census: a bracketed body recorded as unbracketed was accepted — \
      the registry may understate coverage silently"
  -- The derived-set reconciliation, on synthetic inputs.  Planting a committing
  -- `@[export]` to exercise it in place would emit a real symbol into the
  -- kernel's archive, so the reconciliation is a pure function and this is its
  -- self-test: an unrecorded seam is caught, a stale entry is caught, and the
  -- agreeing case is not.
  unless (reconciliationViolations [`a, `b] [`a, `b]).isEmpty do
    throwError "export-commit census: agreeing derived/registry sets were reported as \
      disagreeing"
  if (reconciliationViolations [`a, `b] [`a]).isEmpty then
    throwError "export-commit census: an UNRECORDED state-committing export was accepted — \
      the shape this gate exists to catch"
  if (reconciliationViolations [`a] [`a, `b]).isEmpty then
    throwError "export-commit census: a stale registry entry was accepted"
  unless (reconciliationViolations [] []).isEmpty do
    throwError "export-commit census: two empty sets were reported as disagreeing"
  -- The census.  The set is derived; the registry is reconciled against it in
  -- both directions.
  let derived : List Name :=
    env.constants.toList.foldl
      (fun acc (n, _) =>
        if isProjectConstant n && (getExportNameFor? env n).isSome && commitsState env n
        then n :: acc else acc) []
  let recorded : List Name := commitDisciplineRegistry.map (·.1)
  let mismatches := reconciliationViolations derived recorded
  unless mismatches.isEmpty do
    throwError "export-commit census: {mismatches}"
  for (n, d) in commitDisciplineRegistry do
    let violations := disciplineViolations env n d
    unless violations.isEmpty do
      throwError "export-commit census: {violations}"
  logInfo m!"export-commit census: {derived.length} state-committing `@[export]` seams, \
    {bracketedSeams.length} of them bracketed ({bracketedSeams}); the rest are recorded \
    unbracketed with reasons"

end SeLe4n.Testing.ExportCommitDisciplineCensus
