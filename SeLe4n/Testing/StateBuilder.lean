-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n
import SeLe4n.Model.FrozenState

open SeLe4n.Model

namespace SeLe4n.Testing

/--
Testing DSL for composing bootstrap states from finite override tables.

Later entries win because DSL combinators prepend to each list.
-/
structure BootstrapBuilder where
  machine : SeLe4n.MachineState := default
  objects : List (SeLe4n.ObjId × KernelObject) := []
  runnable : List SeLe4n.ThreadId := []
  current : Option SeLe4n.ThreadId := none
  /-- The lines at seL4's `IRQSignal` (WS-ZA ZA6.32). -/
  irqSignalLines : List SeLe4n.Irq := []
  lifecycleObjectTypes : List (SeLe4n.ObjId × KernelObjectType) := []
  -- AN11-F (LOW): `panic!` in `withObject` requires `Inhabited
  -- BootstrapBuilder` for the return type.  Every field above carries a
  -- default, so the derivation is total.
  deriving Inhabited

/-- WS-ZA ZA5.4: a ledger entry read back as the write it encodes (the suites'
addresses all fit a word), or `none` for a tag the HAL does not decode. -/
def physicalWriteOfWords : UInt64 × UInt64 × UInt64 → Option Kernel.Architecture.PhysicalWrite
  | (0, a, _) => some (.zeroPage (SeLe4n.PAddr.ofNat a.toNat))
  | (1, a, v) => some (.storeDescriptor (SeLe4n.PAddr.ofNat a.toNat) v)
  | (2, a, _) => some (.invalidateAsid (SeLe4n.ASID.ofNat a.toNat))
  | (3, a, v) => some (.storeUserWord (SeLe4n.PAddr.ofNat a.toNat) v)
  | (4, a, v) => some (.storeTableDescriptor (SeLe4n.PAddr.ofNat a.toNat) v)
  | _ => none

/-- The writes a ledger holds, read off its buffer as the HAL reads them. -/
def ledgerWrites (l : Kernel.Architecture.PhysicalWriteLedger) : List Kernel.Architecture.PhysicalWrite :=
  (Kernel.Architecture.decodeLedger l.bytes l.count).filterMap physicalWriteOfWords

/-- The writes a state owes, read off its ledger. -/
def pendingWrites (st : SystemState) : List Kernel.Architecture.PhysicalWrite :=
  ledgerWrites st.drainedPhysicalWrites

namespace BootstrapBuilder

def empty : BootstrapBuilder := {}

/-- AN11-F (LOW): runtime guard against sentinel ObjId at `withObject`
entry.  `ObjId.sentinel` (val = 0xFFFFFFFFFFFFFFFF) is the typed-helper
"this id is reserved" marker; placing a real object at the sentinel
would corrupt the AK7-E type-level discipline (every `Valid*Id` lookup
treats sentinel as the unconditional reject case).  Test fixtures that
try this almost always have a typo elsewhere. -/
def withObject (builder : BootstrapBuilder) (oid : SeLe4n.ObjId) (obj : KernelObject) : BootstrapBuilder :=
  if oid = SeLe4n.ObjId.sentinel then
    panic! "BootstrapBuilder.withObject: refusing to insert at ObjId.sentinel (AN11-F / TST LOW). Use a non-reserved OID per Helpers.lean's range table."
  else
    { builder with objects := (oid, obj) :: builder.objects }

def withRunnable (builder : BootstrapBuilder) (queue : List SeLe4n.ThreadId) : BootstrapBuilder :=
  { builder with runnable := queue }

def withCurrent (builder : BootstrapBuilder) (tid : Option SeLe4n.ThreadId) : BootstrapBuilder :=
  { builder with current := tid }

/-- WS-ZA ZA6.32: **line `irq` at `IRQSignal`, bound to notification `oid`**, as
`seL4_IRQControl_Get` then `seL4_IRQHandler_SetNotification` leave it: the line
in the signal set and its interrupt node (`irqNodeId`) holding a notification
capability to `oid` with the send right, carrying `badge` when one is given. -/
def withIrqHandler
    (builder : BootstrapBuilder)
    (irq : SeLe4n.Irq)
    (oid : SeLe4n.ObjId) (badge : Option SeLe4n.Badge := none) : BootstrapBuilder :=
  let cap : Capability :=
    ({ target := .object oid, rights := AccessRightSet.ofList [.write] } : Capability).withBadge badge
  { builder with
    irqSignalLines := irq :: builder.irqSignalLines
    objects := (irqNodeId irq.toNat, .cnode (CNode.ofList 0 0 0 0 [(irqNodeSlot, cap)])) ::
      builder.objects }

def withLifecycleObjectType
    (builder : BootstrapBuilder)
    (oid : SeLe4n.ObjId)
    (objTy : KernelObjectType) : BootstrapBuilder :=
  { builder with lifecycleObjectTypes := (oid, objTy) :: builder.lifecycleObjectTypes }

/-- Extract the actual TCB priority for a thread from the builder's object list.
    Falls back to Priority 0 if the thread has no TCB entry. -/
private def lookupThreadPriority (objects : List (SeLe4n.ObjId × KernelObject)) (tid : SeLe4n.ThreadId) : SeLe4n.Priority :=
  match objects.find? (fun (oid, _) => oid == tid.toObjId) with
  | some (_, .tcb tcb) => tcb.priority
  | _ => ⟨0⟩

/-- Materialize a full `SystemState` from the builder tables, before the run
queue is populated. -/
private def buildUnqueued (builder : BootstrapBuilder) : SystemState :=
  {
    machine := builder.machine
    objects := SeLe4n.Kernel.RobinHood.RHTable.ofList builder.objects
    objectIndexGhost := SeLe4n.Erased.mk (builder.objects.map Prod.fst)
    objectIndexSetGhost := SeLe4n.Erased.mk
      (SeLe4n.Kernel.RobinHood.RHSet.ofList (builder.objects.map Prod.fst))
    -- SM4.B: per-core scheduler fields; the test builder populates only the boot core.
    scheduler := (default : SchedulerState).setCurrentOnCore
          SeLe4n.Kernel.Concurrency.bootCoreId builder.current
    cdt := builder.irqSignalLines.foldl
      (fun c l => c.withIrqLineIssued l.toNat true) CapDerivationTree.empty
    lifecycle := {
      objectTypesGhost :=
        SeLe4n.Erased.mk (SeLe4n.Kernel.RobinHood.RHTable.ofList builder.lifecycleObjectTypes)
    }
    -- WS-G3/F-P06: Populate ASID table from VSpaceRoot objects
    asidTable := SeLe4n.Kernel.RobinHood.RHTable.ofList (builder.objects.filterMap fun (oid, obj) =>
      match obj with
      | .vspaceRoot root => some (root.asid, oid)
      | _ => none)
  }

/-- Link every supplied reply-blocked thread onto its server's reply-waiter
queue through the kernel's own link (`SystemState.linkReplyWaiter`), in object
order, so priority inheritance reads the waiters the TCBs name (WS-ZA ZA4.6). -/
private def linkReplyWaiters (objects : List (SeLe4n.ObjId × KernelObject))
    (st : SystemState) : SystemState :=
  objects.foldl (fun st (oid, obj) =>
    match obj with
    | .tcb t =>
      match t.blockingServer? with
      | some server => st.linkReplyWaiter (SeLe4n.ThreadId.ofNat oid.toNat) server
      | none => st
    | _ => st) st

/-- Materialize a full `SystemState` from the builder tables.  The boot core's
run queue is filled by the kernel's own enqueue (`runEnqueueOnCore`), so each
runnable thread's TCB carries the run-queue links the selector walks (WS-ZA
ZA4.5), and each reply-blocked thread is linked under its server (ZA4.6). -/
def build (builder : BootstrapBuilder) : SystemState :=
  builder.runnable.foldl (fun st tid =>
      st.runEnqueueOnCore SeLe4n.Kernel.Concurrency.bootCoreId tid
        (lookupThreadPriority builder.objects tid))
    (linkReplyWaiters builder.objects builder.buildUnqueued)

/-- S2-F: Build a `SystemState` with post-construction invariant validation.
    Returns the state or throws if structural invariants are violated.
    Validates (runtime approximation of formal Builder invariants):
    1. No duplicate object IDs
    2. Lifecycle objectTypes reference existing objects with correct type tags
    3. Scheduler runnable threads reference existing TCB objects
    4. CNode slot table capacity bounds (4 ≤ capacity, size < capacity)
    5. IRQ handlers reference existing objects
    6. VSpaceRoot ASID uniqueness (no two VSpaceRoots share an ASID)
    7. Current thread (if set) is not in the runnable list
    8. No supplied TCB claims a run-queue place (`runCoreCode = 0`, as
       `bootSafeTcbCheck` requires of a boot TCB): `build` places exactly the
       `runnable` threads, and a TCB naming a core would make its enqueue
       skip (boot core) or be refused (another core) -/
def buildValidated (builder : BootstrapBuilder) : Except String SystemState :=
  let st := builder.build
  let oids := builder.objects.map Prod.fst
  let uniqueOids := oids.eraseDups
  -- W5-D: Each check includes its number for debuggability
  -- Check 1: No duplicate object IDs in builder input
  if oids.length ≠ uniqueOids.length then
    .error s!"BuilderTestState check 1 failed: duplicate object IDs (got {oids.length} entries, {uniqueOids.length} unique)"
  -- Check 2: Lifecycle objectTypes reference existing objects with correct type
  else if builder.lifecycleObjectTypes.any (fun (oid, _) => !oids.contains oid) then
    let bad := builder.lifecycleObjectTypes.filter (fun (oid, _) => !oids.contains oid)
    .error s!"BuilderTestState check 2a failed: lifecycleObjectTypes references non-existent object ID(s): {bad.map Prod.fst}"
  else if builder.lifecycleObjectTypes.any (fun (oid, ty) =>
    match builder.objects.find? (fun (o, _) => o == oid) with
    | some (_, obj) => obj.objectType != ty
    | none => true) then
    .error "BuilderTestState check 2b failed: lifecycleObjectTypes type tag mismatch with actual object"
  -- Check 3: Runnable threads reference existing TCB objects
  else if builder.runnable.any (fun tid =>
    !builder.objects.any (fun (oid, obj) =>
      oid.toNat = tid.toNat && match obj with | .tcb _ => true | _ => false)) then
    let bad := builder.runnable.filter (fun tid =>
      !builder.objects.any (fun (oid, obj) =>
        oid.toNat = tid.toNat && match obj with | .tcb _ => true | _ => false))
    .error s!"BuilderTestState check 3 failed: runnable thread(s) do not reference existing TCB(s): {bad}"
  -- Check 8 (PR #932 review): no supplied TCB already claims a run-queue
  -- place, so the fold over `runnable` builds the queue the builder names.
  else if builder.objects.any (fun (_, obj) =>
    match obj with | .tcb t => t.runCoreCode != 0 | _ => false) then
    let bad := builder.objects.filterMap (fun (oid, obj) =>
      match obj with | .tcb t => if t.runCoreCode != 0 then some oid else none | _ => none)
    .error s!"BuilderTestState check 8 failed: supplied TCB(s) carry run-queue placement (runCoreCode ≠ 0): {bad}"
  -- Check 9 (WS-ZA ZA4.6): no supplied TCB already carries reply-waiter links;
  -- `build` links each reply-blocked thread under the server it names.
  else if builder.objects.any (fun (_, obj) =>
    match obj with
    | .tcb t => t.replyWaiterPrevCode != 0 || t.replyWaiterNextCode != 0 ||
        t.replyWaitersHeadCode != 0 || t.replyWaitersCount != 0
    | _ => false) then
    let bad := builder.objects.filterMap (fun (oid, obj) =>
      match obj with
      | .tcb t => if t.replyWaiterPrevCode != 0 || t.replyWaiterNextCode != 0 ||
          t.replyWaitersHeadCode != 0 || t.replyWaitersCount != 0 then some oid else none
      | _ => none)
    .error s!"BuilderTestState check 9 failed: supplied TCB(s) carry reply-waiter links: {bad}"
  -- Check 5: every signalled line's interrupt node exists
  else if builder.irqSignalLines.any (fun l => !oids.contains (irqNodeId l.toNat)) then
    .error "BuilderTestState check 5 failed: a signalled line has no interrupt node"
  -- Check 6: VSpaceRoot ASID uniqueness
  else
    let asids := builder.objects.filterMap (fun (_, obj) =>
      match obj with | .vspaceRoot vs => some vs.asid | _ => none)
    let uniqueAsids := asids.eraseDups
    if asids.length ≠ uniqueAsids.length then
      .error "BuilderTestState check 6 failed: duplicate ASIDs across VSpaceRoot objects"
    -- Check 7: Dequeue-on-dispatch (WS-H12b) — current thread must NOT be in
    -- the runnable list. The scheduler removes the dispatched thread from the
    -- run queue before setting it as current. If current is set AND also in
    -- runnable, the state violates queueCurrentConsistent.
    else match builder.current with
    | some tid =>
      if builder.runnable.any (fun t => t.toNat == tid.toNat) then
        .error s!"BuilderTestState check 7 failed: current thread {tid.toNat} must not be in runnable list (dequeue-on-dispatch, WS-H12b)"
      else .ok st
    | none => .ok st

/-- S2-F: Build a `SystemState` with invariant validation, panicking on failure.
    Drop-in replacement for `build` that catches structural violations at test time.
    Use this for new test states instead of `build` to ensure test states satisfy
    the same structural invariants as the formal Builder. -/
def buildChecked (builder : BootstrapBuilder) : SystemState :=
  match builder.buildValidated with
  | .ok st => st
  | .error msg => panic! s!"BootstrapBuilder.buildChecked: {msg}"

end BootstrapBuilder

/-! ## Frozen fixtures

`freeze` turns a live `IntermediateState` into a `FrozenSystemState`; a test that
wants an arbitrary frozen state builds one directly instead.  Six suites each
grew their own copy of that builder, and all six left the scheduler at its empty
default — modelling a state in which objects exist and no thread is runnable,
which the live kernel cannot reach, since a thread only ever blocks from being
runnable.

That is not a cosmetic difference.  `frozenChooseThread` selects by folding
`scheduler.byPriority`, so a fixture with no buckets cannot show a wake failing
to refill one, which is how the frozen operations went five review rounds
without maintaining the run queue at all.  One builder, used by every suite, so
the shape cannot drift back per-file. -/

/-- The frozen state with nothing in it.

Six suites each carried a byte-for-byte copy of this literal.  A required frozen
field with no default (the audit epoch, the refusal ledger, the per-core caches)
then has to be added in six places, and a suite that lags behind stops
compiling — the duplication has no upside and one clear downside. -/
def emptyFrozenSystemState : FrozenSystemState :=
  { objects := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    asidTable := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    interfaceRegistry := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
    cdt := .empty
    scheduler :=
      { byPriority := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        threadPriority := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        membership := freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
        current := none
        activeDomain := ⟨0⟩
        domainTimeRemaining := 5
        domainSchedule := []
        domainScheduleIndex := 0
        configDefaultTimeSlice := 5
        replenishQueue := { entries := [], size := 0 } }
    objectTypesGhost := SeLe4n.Erased.mk (freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16))
    machine := default
    objectIndexGhost := SeLe4n.Erased.mk []
    objectIndexSetGhost := SeLe4n.Erased.mk (freezeMap (SeLe4n.Kernel.RobinHood.RHTable.empty 16))
    tlb := TlbState.empty
    perCoreTlb := _root_.Vector.replicate SeLe4n.Kernel.Concurrency.numCores TlbState.empty
    declassificationAuditLog := []
    declassificationAuditEpoch := 0
    declassificationRefusals := SeLe4n.Kernel.RefusalLedger.initial
    perCoreICache :=
      _root_.Vector.replicate SeLe4n.Kernel.Concurrency.numCores ICacheState.empty
    pendingIcacheMaintenance := []
    physicalWrites := .empty }

/-- A `FrozenSystemState` holding `objs`, with the run queue a live state would
have: a bucket per distinct TCB priority, holding the threads that are `.ready`.

Buckets for priorities whose threads are all blocked exist but are empty — which
is what a real freeze produces for a thread that had run before blocking, and
what lets a wake enqueue back into them. -/
def frozenStateOf (objs : List (SeLe4n.ObjId × FrozenKernelObject))
    : FrozenSystemState :=
  let rt := objs.foldl (fun acc kv =>
    acc.insert kv.1 kv.2) (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
  let tcbs := objs.filterMap (fun kv =>
    match kv.2 with | .tcb t => some t | _ => none)
  let prios := tcbs.foldl (fun acc t =>
    if acc.contains t.priority then acc else acc ++ [t.priority]) []
  let byPrio := prios.foldl (fun acc p =>
    acc.insert p ((tcbs.filter (fun t => t.priority == p && t.ipcState == .ready)).map
      (fun t => t.tid))) (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
  let thrPrio := tcbs.foldl (fun acc t =>
    acc.insert t.tid t.priority) (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
  let memb := tcbs.foldl (fun acc t =>
    acc.insert t.tid ()) (SeLe4n.Kernel.RobinHood.RHTable.empty 16)
  { emptyFrozenSystemState with
      objects := freezeMap rt
      scheduler := { emptyFrozenSystemState.scheduler with
                       byPriority := freezeMap byPrio
                       threadPriority := freezeMap thrPrio
                       membership := freezeMap memb } }

/-- **WS-BP BP7.2**: the fixture address `offset` bytes into the user window
(`VAddr.userWindowBase`) — the lowest addresses a thread may map, and the ones
`fixtureMappableRoot`'s walk covers for `offset < 0x200000`. -/
def fixtureUserVAddr (offset : Nat) : SeLe4n.VAddr :=
  SeLe4n.VAddr.ofNat (SeLe4n.VAddr.userWindowBase + offset)

/-- **WS-BP BP7.1 (`v0.36.13`)**: a fixture address space a frame can be mapped
into directly — a table page, and table slots at all three levels for the first
2 MiB of the user window (WS-BP BP7.2: every level's index is the one the walk
to `VAddr.userWindowBase` takes), so `VSpaceRoot.translationReady` holds at
every `fixtureUserVAddr offset` with `offset < 0x200000`.  Since `v0.36.13` a
root with no table page maps nothing, so a fixture that means to exercise a map
rather than the walk starts from this.  The slots name table ids the fixture
does not install: the walk's *presence* is what the map arm reads, and a
scenario about the tables themselves builds them through `.pageTableMap`
instead (`tests/VSpaceCapabilityBindingSuite.lean` §5k). -/
def fixtureMappableRoot (asid : SeLe4n.ASID)
    (tableBase : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x7F000) : VSpaceRoot :=
  { asid := asid, mappings := {}, tableBase := some tableBase,
    tables := [1, 2, 3].map fun l =>
      { level := l, index := PageTableSlot.indexOf l (fixtureUserVAddr 0),
        table := SeLe4n.ObjId.ofNat (0xF_0000 + l) } }

/-- Install `tid` as the thread current on `core`.  The dispatchers refuse a
caller that is not current on the executing core
(`dispatchSyscall_refuses_mismatched_core`), so a fixture that drives a dispatcher
directly makes its caller current first, exactly as the trap entry finds it. -/
def withCurrentOnCore (st : SystemState) (core : SeLe4n.Kernel.Concurrency.CoreId) (tid : SeLe4n.ThreadId) :
    SystemState :=
  { st with scheduler := st.scheduler.setCurrentOnCore core (some tid) }

/-- `dispatchSyscall` from a fixture whose caller is made current on `core`
first (`withCurrentOnCore`) — the consistent caller/core pair the entry
supplies. -/
def dispatchSyscallAsCurrent (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (core : SeLe4n.Kernel.Concurrency.CoreId) (st : SystemState) :
    Except KernelError (Unit × SystemState) :=
  SeLe4n.Kernel.dispatchSyscall decoded tid core (withCurrentOnCore st core tid)

/-- The checked twin of `dispatchSyscallAsCurrent`. -/
def dispatchSyscallCheckedAsCurrent (ctx : SeLe4n.Kernel.LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (core : SeLe4n.Kernel.Concurrency.CoreId)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  SeLe4n.Kernel.dispatchSyscallChecked ctx decoded tid core (withCurrentOnCore st core tid)

/-- Queue `entries` on core `c`, in order, through the kernel's own enqueue
(`runEnqueueOnCore`): each thread's TCB carries the run-queue links the kernel
reads (WS-ZA ZA4.5), so a fixture built this way is one the kernel could have
reached.  Each thread's TCB must already be in `st`. -/
def enqueueAllOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (entries : List (SeLe4n.ThreadId × SeLe4n.Priority)) : SystemState :=
  entries.foldl (fun s e => s.runEnqueueOnCore c e.1 e.2) st

/-- Replace core `c`'s run queue with `entries`: every thread now queued on `c` is
removed and `entries` are queued in order, all through the kernel's own removal
and enqueue, so the TCB links the kernel reads describe the new queue.  A write
to the scheduler's ghost queue alone (`setRunQueueOnCore`) changes nothing the
compiled kernel reads. -/
def replaceRunQueueOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (entries : List (SeLe4n.ThreadId × SeLe4n.Priority)) : SystemState :=
  enqueueAllOnCore ((st.runQueueWalk c).foldl (fun s t => s.runRemoveOnCore c t) st) c entries

/-- Queue scheduling context `s` on core `c`'s release queue, due at `t`: the
context's earliest pending refill becomes one refill of its full budget at `t`
and its head is used up (`budgetRemaining = 0`: seL4-MCS queues only a context
whose head refill is not yet ready; the queue's key is that refill, `SchedContext.releaseKey?`, as seL4-MCS keys
its release queue by the head refill's release time), and the context is placed
through the kernel's own `replenishOnCore`, which writes the contexts' release
links and the abstract queue together (WS-ZA ZA6.3).  A write to the
scheduler's ghost queue alone (`setReplenishQueueOnCore`) changes nothing the
compiled kernel reads.  A context the store does not hold is left unqueued. -/
def withReleaseEntryOnCore (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (s : SeLe4n.SchedContextId) (t : Nat) : SystemState :=
  SeLe4n.Kernel.replenishOnCore (st.updateSchedContext s fun sc =>
    { sc with budgetRemaining := ⟨0⟩, refillHeadPresent := true,
              refillHeadAmount := sc.budget.val, refillHeadEligibleAt := t,
              refillTailCount := 0 }) c s

/-- Runtime form of `chooseThreadOnCoreSelects`: core `c`'s selection read
through the threads' run-queue links (`chooseThreadOnCoreByLinks`, equal to
`chooseThreadOnCore` under the link refinement by `chooseThreadOnCoreByLinks_eq`). -/
def selectsByLinks (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) : Bool :=
  match SeLe4n.Kernel.chooseThreadOnCoreByLinks st c with
  | .ok (some t) => t == tid
  | _ => false

/-- Runtime form of `chooseThreadOnCoreIdleFallback` (see `selectsByLinks`). -/
def idleFallbackByLinks (st : SystemState) (c : SeLe4n.Kernel.Concurrency.CoreId) : Bool :=
  match SeLe4n.Kernel.chooseThreadOnCoreByLinks st c with
  | .ok none => true
  | _ => false

/-- WS-ZA ZA4.7: **put a message in a sender's saved registers**, where a send
syscall finds it: syscall number `x7` = send, message-info word `x1` carrying
the length and `extraCaps`, and the first four message words in `x2`–`x5`
(`arm64DefaultLayout`).  A blocked sender keeps its message there and a receive
reads it at the rendezvous (`blockedSenderMessage`), so a fixture that calls a
send transition directly stages the frame first, exactly as the trap entry
saves it.  Words past the fourth would live in the IPC buffer, as the extra
capability addresses do (`withSenderCapAddrs`); fixtures here send at most four
words. -/
def tcbWithSenderFrame (tcb : TCB) (msg : IpcMessage) (extraCaps : Nat := 0) : TCB :=
  let w (i : Nat) : UInt64 :=
    ((msg.registers[i]?.map (fun (r : SeLe4n.RegValue) => r.val)).getD 0).toUInt64
  let info : Nat := ({ length := msg.registers.size, extraCaps := extraCaps, label := 0 } : MessageInfo).encode
  let regs := SeLe4n.RegisterFile.withGprs tcb.registerContext.pc tcb.registerContext.sp
    (fun r => if r == 1 then info.toUInt64 else if r == 2 then w 0
      else if r == 3 then w 1 else if r == 4 then w 2 else if r == 5 then w 3 else 0)
  { tcb with registerContext := regs }

/-- **Give thread `tid` an IPC buffer with a receive path** (seL4's
`seL4_SetCapReceivePath`): a VSpace `vsId` of its own maps the buffer page at
`va` (page-aligned) writable onto the frame at `pa` (a RAM region is declared
over that frame when none holds it), and the buffer's
`receive_cnode` / `receive_index` / `receive_depth` words hold `cnodeCPtr`,
`index` and `depth`.  The receive slot is then what seL4's `getReceiveSlots`
reads (`receiveSlot?`): `cnodeCPtr` looked up in the thread's CSpace must name a
CNode, in which `index` resolves `depth` bits deep to an empty slot. -/
def withReceivePath (st : SystemState) (tid : SeLe4n.ThreadId) (vsId : SeLe4n.ObjId)
    (va : SeLe4n.VAddr) (pa : SeLe4n.PAddr) (cnodeCPtr index depth : Nat) : SystemState :=
  match st.getTcb? tid with
  | none => st
  | some tcb =>
    let vs : VSpaceRoot :=
      { asid := ⟨vsId.toNat⟩
        mappings := SeLe4n.Kernel.RobinHood.RHTable.ofList [(va, (pa, { read := true, write := true }))] }
    let tcb' := { tcb with ipcBuffer := va, spaceCells := TCB.spaceCellsOf tcb.cspaceRoot vsId }
    let word (i : Nat) : SeLe4n.PAddr := SeLe4n.PAddr.ofNat
      (pa.toNat + 8 * (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferOverflowBaseWord + i))
    let mem := SeLe4n.Kernel.Architecture.writeUInt64
      (SeLe4n.Kernel.Architecture.writeUInt64
        (SeLe4n.Kernel.Architecture.writeUInt64 st.machine.memory
          (word SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReceiveCNodeWord)
          cnodeCPtr.toUInt64)
        (word SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReceiveIndexWord) index.toUInt64)
      (word SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferReceiveDepthWord) depth.toUInt64
    let region : MemoryRegion :=
      { base := SeLe4n.PAddr.ofNat (pa.toNat - pa.toNat % 4096), size := 4096, kind := .ram }
    let map := if st.machine.addrInRange pa then st.machine.memoryMap
      else region :: st.machine.memoryMap
    let st0 := { st with machine := { st.machine with memory := mem, memoryMap := map } }
    match storeObject vsId (.vspaceRoot vs) st0 with
    | .error _ => st
    | .ok ((), st1) =>
      match storeObject tid.toObjId (.tcb tcb') st1 with
      | .ok ((), st2) => st2
      | .error _ => st

/-- **Name a sender's extra capability addresses** where seL4's
`lookupExtraCaps` reads them: the `caps_or_badges` words of its IPC buffer.  A
thread whose buffer the kernel cannot read is first given one, in a VSpace of
its own, with an empty receive path (`withReceivePath`, depth 0); the frame is a
page per thread, apart from `withReceiveSlot`'s. -/
def withSenderCapAddrs (st : SystemState) (tid : SeLe4n.ThreadId)
    (addrs : Array SeLe4n.CPtr) : SystemState :=
  if addrs.isEmpty then st else
  match st.getTcb? tid with
  | none => st
  | some tcb =>
    let st1 :=
      if (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferWordPAddr? st tcb
          (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferCapsOrBadgesWord 0) false).isSome then st
      else withReceivePath st tid ⟨0x7E000000 + tid.toNat⟩ (SeLe4n.VAddr.ofNat 0x7e0000)
        (SeLe4n.PAddr.ofNat (0x2000000 + 0x1000 * (tid.toNat % 4096))) 0 0 0
    match st1.getTcb? tid with
    | none => st1
    | some tcb1 =>
      let mem := (List.range addrs.size).foldl (fun mem i =>
        match SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferWordPAddr? st1 tcb1
            (SeLe4n.Kernel.Architecture.IpcBufferRead.ipcBufferCapsOrBadgesWord i) false,
            addrs[i]? with
        | some pa, some a => SeLe4n.Kernel.Architecture.writeUInt64 mem pa a.toNat.toUInt64
        | _, _ => mem) st1.machine.memory
      { st1 with machine := { st1.machine with memory := mem } }

/-- `tcbWithSenderFrame` on the thread `tid` of a live state, its extra
capability addresses `capAddrs` in its IPC buffer (`withSenderCapAddrs`). -/
def withSenderFrame (st : SystemState) (tid : SeLe4n.ThreadId) (msg : IpcMessage)
    (capAddrs : Array SeLe4n.CPtr := #[]) : SystemState :=
  match st.getTcb? tid with
  | none => st
  | some tcb =>
      match storeObject tid.toObjId (.tcb (tcbWithSenderFrame tcb msg capAddrs.size)) st with
      | .ok ((), st') => withSenderCapAddrs st' tid capAddrs
      | .error _ => st

/-- **Give thread `tid` the receive slot `index` of its own root CNode**: slot
`pathSlot` of that CNode is given a capability to the CNode itself (when empty),
and the thread's receive path names it — `receive_cnode = pathSlot`,
`receive_index = index`, `receive_depth` the CNode's depth — through a buffer in a
VSpace `vsId` of its own (`withReceivePath`).  The buffer's frame is a page per
thread, so several receivers in one state do not share one. -/
def withReceiveSlot (st : SystemState) (tid : SeLe4n.ThreadId) (vsId : SeLe4n.ObjId)
    (index : Nat) (pathSlot : Nat := 15) : SystemState :=
  match st.getTcb? tid with
  | none => st
  | some tcb =>
    match st.getCNode? tcb.cspaceRoot with
    | none => st
    | some cn =>
      let root := tcb.cspaceRoot
      let st1 :=
        if (cn.lookup (SeLe4n.Slot.ofNat pathSlot)).isSome then st
        else st.storeCNodeWith root (·.insert (SeLe4n.Slot.ofNat pathSlot)
          { target := .object root, rights := AccessRightSet.ofList [.read, .write, .grant] })
      withReceivePath st1 tid vsId (SeLe4n.VAddr.ofNat 0x7f0000)
        (SeLe4n.PAddr.ofNat (0x1000000 + 0x1000 * (tid.toNat % 4096))) pathSlot index cn.depth

end SeLe4n.Testing

/-- Test fixtures: a slot an edge names holds a capability (`cdtCompleteness`),
so an empty one is given a read capability to its own CNode first. -/
def SeLe4n.Model.SystemState.withSlotPopulated (st : SeLe4n.Model.SystemState)
    (r : SeLe4n.Model.SlotRef) : SeLe4n.Model.SystemState :=
  match SeLe4n.Model.SystemState.lookupSlotCap st r with
  | some _ => st
  | none =>
    st.storeCNodeWith r.cnode (·.insert r.slot
      { target := .object r.cnode, rights := SeLe4n.Model.AccessRightSet.ofList [.read] })

/-- Test fixtures: record each `(parent, child, op)` derivation edge through the
kernel's paired tree-and-link ops, so the fixture's slot links agree with its
tree; each slot an edge names holds a capability (`withSlotPopulated`).  The
tree names every source, as it names every capability-holding slot: a source no
earlier edge named goes to the end of the root chain first (`cdtAppendRoot`).
The fixture's tree starts empty, and an edge's child is a slot no earlier edge
named. -/
def SeLe4n.Model.SystemState.withDerivationEdges (st : SeLe4n.Model.SystemState)
    (es : List (SeLe4n.Model.SlotRef × SeLe4n.Model.SlotRef × SeLe4n.Model.DerivationOp)) :
    SeLe4n.Model.SystemState :=
  (es.foldl (fun (acc : SeLe4n.Model.SystemState × Option SeLe4n.Model.SlotRef ×
      List SeLe4n.Model.SlotRef) e =>
    let (s, last, named) := acc
    let (s, last, named) :=
      if named.contains e.1 then (s, last, named)
      else ((s.withSlotPopulated e.1).cdtAppendRoot last e.1, some e.1, e.1 :: named)
    ((s.withSlotPopulated e.2.1).cdtAddChild e.1 e.2.1 e.2.2, last, e.2.1 :: named))
    (st, none, [])).1
