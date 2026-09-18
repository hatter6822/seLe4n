/-
  SeLe4n — the kernel-transition reachability census.

  Copyright (C) 2025 seLe4n contributors
  SPDX-License-Identifier: GPL-3.0-or-later
-/
import Lean.Elab.Command
import SeLe4n
import SeLe4n.Platform.Staged
import SeLe4n.Testing.ExportCommitDisciplineCensus
import SeLe4n.Testing.ReplyStackWriteCensus

/-!
# Which kernel transitions are on an executed path

`ExportCommitDisciplineCensus` walks *outward* from each state-committing
`@[export]` and asks how it commits.  This census walks the same graph the other
way: it derives every definition that **transforms kernel state**, partitions
that domain by whether a committing export can reach it, and reconciles the
unreachable half against a pin in both directions.

## Why the tree needs it

WS-RR RR8.12 (`v0.35.90`) found two verified behavioural steps — WS-OD OD1.7's
aborted-donation-holder wake and WS-RR RR7.22/RR8.11's replenishment migration —
sitting in `cancelIpcBlockingOnCore`, a composite **no production path calls**,
while the live `.tcbSuspend` arm re-composed that composite's parts and so
carried neither.  The consequence was a permanent denial of service against a
passive server.  Nothing in the tree could say that the composite was not on an
executed path: the fact was true, checkable and unstated.

## What this census claims, and what it does not

It claims: **every state-transforming definition is either reachable from a
committing export, or recorded in the pin below** — and the pin is reconciled
both ways, so a new non-executed transition fails and so does an entry that has
become live.  The pin carries no per-entry prose, deliberately: 240 shallow
reasons would read as justification while asserting nothing, and the obligation
that does the work falls on whoever adds the 241st, who must either wire it or
say there why it exists.

It does **not** claim that a recorded surface agrees with whatever live code
re-composes it.  A bare reachability partition cannot: the offending composite
already existed before the step was added to it, so its entry would have
predated the defect and no reconciliation would have moved.  The mechanism for
*that* is `standsBesideLive` below, whose rows name the live counterpart **and a
pin theorem relating the two**; a step added to one side and not the other
breaks the pin.  A recorded surface with no such row makes no agreement claim at
all, and extending the pinned set is what closes the class rather than the
instance.

This distinction is why `docs/REGISTERED_DEBT.md`'s row registering this census
was corrected in the same cut that landed it: the row said a reachability census
"would have failed on the day" the step was introduced, and that is only true of
the pinned category, not of reachability alone.
-/

namespace SeLe4n.Testing.KernelTransitionReachabilityCensus

open Lean Elab Command Meta
open SeLe4n.Testing.ExportCommitDisciplineCensus (isProjectConstant commitsState)
open SeLe4n.Testing.ReplyStackWriteCensus (privateIn conclusionOf)

/-- The state this kernel transforms.  A definition whose **result** mentions it
is a transition, a resolver over it, or a step of one; a definition that merely
*takes* one is a reader or a predicate and is not this census's subject. -/
def kernelStateType : Name := `SeLe4n.Model.SystemState

/-- The compiler's own generated declarations, which are not definitions anyone
wrote.

The general answer is `ReplyStackWriteCensus.isAuxiliary`, which asks the
environment (macro scopes, `isAuxRecursor`, `isRecCore`, `Meta.isMatcherCore`)
rather than matching name shapes, and whose docstring records why a name list
was retired in favour of it.  Reusing it is deliberate: a second auxiliary
filter beside a derived one is this project's one-question-two-answers hazard,
and the two would diverge on the next compiler change.

What that predicate does **not** reach is the three generated shapes whose
result type mentions `SystemState` and which therefore land in *this* census's
domain but not in its sibling's: the compiler's own lowering stages
(`_cstage1` / `_cstage2`, and the `_sunfold` / `_unsafe_rec` pair a `partial`
or well-founded definition gets), the flat constructor a structure gets, and a
module's `initFn`.  Each is named here
rather than pattern-matched loosely, and each was measured in the environment
before being added — a filter entry with no member is an exclusion nobody can
justify. -/
def isCompilerGenerated (env : Environment) (n : Name) : Bool :=
  SeLe4n.Testing.ReplyStackWriteCensus.isAuxiliary env n ||
  n.components.any fun c =>
    let s := c.toString
    s == "_cstage1" || s == "_cstage2" || s == "_flat_ctor"
      || s == "_sunfold" || s == "_unsafe_rec" || s.startsWith "initFn"

/-- `true` when `n` is a definition whose result type mentions `SystemState`.

`forallTelescopeReducing` strips the binders, so a predicate
`SystemState → Prop` has body `Prop` and is **not** in the domain, while
`SystemState → Except KernelError SystemState` is.  The test
over-approximates — an `Option SystemState` resolver and a pure reader that
returns its argument both qualify — and that is the safe direction for a
*domain*: a member wrongly included must be explained, a member wrongly excluded
is never looked at. -/
def isStateTransformer (env : Environment) (n : Name) (ci : ConstantInfo) :
    MetaM Bool := do
  match ci with
  | .defnInfo _ =>
    if !isProjectConstant n || isCompilerGenerated env n then return false
    forallTelescopeReducing ci.type fun _ body =>
      pure (body.find? (·.isConstOf kernelStateType)).isSome
  | _ => return false

/-- Every constant a committing export can reach, following project constants
transitively.

Fuel-bounded like its sibling, and an exhausted walk returns what it has —
which makes the *reachable* set smaller and so makes the census demand more.
The bound is far above the closure of this kernel's seams. -/
partial def liveClosure (env : Environment) (roots : List Name) : NameSet :=
  go roots {} 400000
where
  go (worklist : List Name) (seen : NameSet) (fuel : Nat) : NameSet :=
    match fuel, worklist with
    | 0, _ => seen
    | _, [] => seen
    | fuel' + 1, c :: rest =>
      if seen.contains c || !isProjectConstant c then go rest seen fuel'
      else
        let seen := seen.insert c
        match (env.find? c).bind (·.value? (allowOpaque := true)) with
        | none => go rest seen fuel'
        | some v => go (v.getUsedConstants.toList ++ rest) seen fuel'

/-- The committing exports, derived exactly as `ExportCommitDisciplineCensus`
derives them — through that census's own `commitsState`, so the two cannot
disagree about what installs kernel state. -/
def committingExports (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isProjectConstant n && (getExportNameFor? env n).isSome && commitsState env n then
      out := out.push n
  return out

/-- Every state transformer the live closure does not reach, as of this cut.

A **pin**, in the shape `scripts/identifier_naming_baseline.json` uses for the
same reason: the set is derived above, and this list is what makes a *change* to
it visible.  It carries no per-entry prose, deliberately — 240 shallow reasons
would read as justification while asserting nothing, and the obligation that
does the work falls on whoever adds the 241st, who must either wire it or say
here why it exists.

**Two known residues inside this list, both registered rather than absorbed.**
The whole `cspaceRevoke*` / `revokeCdt*` / `streamingRevokeBFS` family is here
because `API.lean` has no revocation syscall arm at all — verified machinery
with no ABI path — and four members (`cleanupActiveDonation`, `timerTickChecked`,
`switchDomainChecked`, `endpointCallWithDonation`) are consumed by nothing in the
tree: no live path, no theorem, no suite, no gate.  Each needs the wire-or-retire
judgement `v0.35.78` made for the capability-reference table, which is a
measurement and a decision rather than a line in a list, so both carry rows in
`docs/REGISTERED_DEBT.md`.  Naming them here keeps a *known* residue from reading
like an unexamined one. -/
def nonExecutedTransitionsPlain : List Name :=
  [ `SeLe4n.Kernel.Architecture.TlbCacheJointState.sysState
  , `SeLe4n.Kernel.Architecture.ackInterruptAudit
  , `SeLe4n.Kernel.Architecture.adapterAdvanceTimer
  , `SeLe4n.Kernel.Architecture.adapterContextSwitch
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbByAsidHw
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbByVAddrHw
  , `SeLe4n.Kernel.Architecture.adapterFlushTlbHw
  , `SeLe4n.Kernel.Architecture.adapterReadMemory
  , `SeLe4n.Kernel.Architecture.adapterWriteRegister
  , `SeLe4n.Kernel.Architecture.advanceTimerState
  , `SeLe4n.Kernel.Architecture.asidAllocateWithShootdown
  , `SeLe4n.Kernel.Architecture.contextSwitchState
  , `SeLe4n.Kernel.Architecture.dispatchException
  , `SeLe4n.Kernel.Architecture.dispatchSynchronousException
  , `SeLe4n.Kernel.Architecture.endOfInterrupt
  , `SeLe4n.Kernel.Architecture.handleInterrupt
  , `SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCore
  , `SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCorePerCore
  , `SeLe4n.Kernel.Architecture.icFetchOnCore
  , `SeLe4n.Kernel.Architecture.icInvalidateOnCore
  , `SeLe4n.Kernel.Architecture.interruptDispatchSequence
  , `SeLe4n.Kernel.Architecture.markTlbBarriered
  , `SeLe4n.Kernel.Architecture.markTlbDirty
  , `SeLe4n.Kernel.Architecture.setIcacheOnCore
  , `SeLe4n.Kernel.Architecture.shootdownCatchUpPerCore
  , `SeLe4n.Kernel.Architecture.shootdownRound
  , `SeLe4n.Kernel.Architecture.shootdownRoundPerCore
  , `SeLe4n.Kernel.Architecture.stageCancelledIpcFrame
  , `SeLe4n.Kernel.Architecture.stageTimeoutFrame
  , `SeLe4n.Kernel.Architecture.timerInterruptHandler
  , `SeLe4n.Kernel.Architecture.tlbFlushByPage
  , `SeLe4n.Kernel.Architecture.tlbFlushByPageWithShootdown
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnAllCores
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnAllCoresCoalescing
  , `SeLe4n.Kernel.Architecture.tlbInvalidateOnCore
  , `SeLe4n.Kernel.Architecture.tlbShootdownBroadcast
  , `SeLe4n.Kernel.Architecture.tlbShootdownBroadcastIn
  , `SeLe4n.Kernel.Architecture.tlbShootdownDrainOnCore
  , `SeLe4n.Kernel.Architecture.tlbShootdownLocal
  , `SeLe4n.Kernel.Architecture.tlbShootdownLocalPerCore
  , `SeLe4n.Kernel.Architecture.vspaceLookup
  , `SeLe4n.Kernel.Architecture.vspaceLookupFull
  , `SeLe4n.Kernel.Architecture.vspaceMapPageChecked
  , `SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlush
  , `SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushPlatform
  , `SeLe4n.Kernel.Architecture.writeRegisterState
  , `SeLe4n.Kernel.Architecture.writeRestartFrameToTcb
  , `SeLe4n.Kernel.Concurrency.KernelTransitionInstance.action
  , `SeLe4n.Kernel.Concurrency.applySequential
  , `SeLe4n.Kernel.Concurrency.applySequentialWithLockSet
  , `SeLe4n.Kernel.Concurrency.runChainExtension
  , `SeLe4n.Kernel.Concurrency.setObjStoreLockAction
  , `SeLe4n.Kernel.Concurrency.setSchedulerAction
  , `SeLe4n.Kernel.Concurrency.withDynamicChainExtension
  , `SeLe4n.Kernel.Internal.lifecycleRetypeObject
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelBoundDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonatedDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonation
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelDonationValid
  , `SeLe4n.Kernel.Lifecycle.Suspend.cancelIpcBlockingValid
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyMidState
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyOnCore
  , `SeLe4n.Kernel.Lifecycle.Suspend.restoreToReadyWithWake
  , `SeLe4n.Kernel.Lifecycle.Suspend.resumeThread
  , `SeLe4n.Kernel.Lifecycle.Suspend.suspendThread
  , `SeLe4n.Kernel.Liveness.CanonicalDeploymentProgress.exitState
  , `SeLe4n.Kernel.Liveness.CanonicalDeploymentProgressOnCore.exitState
  , `SeLe4n.Kernel.Liveness.stepPost
  , `SeLe4n.Kernel.Liveness.traceStateAt
  , `SeLe4n.Kernel.PriorityInheritance.propagatePipChainCrossCoreState
  , `SeLe4n.Kernel.PriorityInheritance.propagatePriorityInheritance
  , `SeLe4n.Kernel.PriorityInheritance.withPipChainSchedExtension
  , `SeLe4n.Kernel.RevokeTraversalOutcome.state
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.migrateRunQueueBucket
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOp
  , `SeLe4n.Kernel.SchedContext.PriorityManagement.setPriorityOp
  , `SeLe4n.Kernel.SchedContextOps.schedContextYieldTo
  , `SeLe4n.Kernel.advanceDomainOnCore
  , `SeLe4n.Kernel.advanceDomainOnCoreN
  , `SeLe4n.Kernel.applyReplyDonation
  , `SeLe4n.Kernel.cancelDonationOnCore
  , `SeLe4n.Kernel.cancelIpcBlockingOnCore
  , `SeLe4n.Kernel.chooseThread
  , `SeLe4n.Kernel.chooseThreadEffective
  , `SeLe4n.Kernel.chooseThreadInDomain
  , `SeLe4n.Kernel.cleanupActiveDonation
  , `SeLe4n.Kernel.cleanupPreReceiveDonation
  , `SeLe4n.Kernel.cleanupPreReceiveDonation_never_errors_under_ipcInvariantFull
  , `SeLe4n.Kernel.commitKernelAction
  , `SeLe4n.Kernel.continueFromAcquired
  , `SeLe4n.Kernel.cspaceLookupMultiLevel
  , `SeLe4n.Kernel.cspaceLookupPath
  , `SeLe4n.Kernel.cspaceMutate
  , `SeLe4n.Kernel.cspaceResolvePath
  , `SeLe4n.Kernel.cspaceRevoke
  , `SeLe4n.Kernel.cspaceRevokeCdt
  , `SeLe4n.Kernel.cspaceRevokeCdtStreaming
  , `SeLe4n.Kernel.cspaceRevokeCdtStrict
  , `SeLe4n.Kernel.cspaceRevokeCdtTransactional
  , `SeLe4n.Kernel.declassifyRun
  , `SeLe4n.Kernel.declassifyStore
  , `SeLe4n.Kernel.declassifyStoreFromCore
  , `SeLe4n.Kernel.declassifyStoreOnCore
  , `SeLe4n.Kernel.descheduleThread
  , `SeLe4n.Kernel.dispatchSyscall
  , `SeLe4n.Kernel.dispatchWithCap
  , `SeLe4n.Kernel.donationChainWitness
  , `SeLe4n.Kernel.endpointCall
  , `SeLe4n.Kernel.endpointCallChecked
  , `SeLe4n.Kernel.endpointCallWithCaps
  , `SeLe4n.Kernel.endpointCallWithDonation
  , `SeLe4n.Kernel.endpointReceiveDual
  , `SeLe4n.Kernel.endpointReceiveDualChecked
  , `SeLe4n.Kernel.endpointReceiveDualWithCaps
  , `SeLe4n.Kernel.endpointReply
  , `SeLe4n.Kernel.endpointReplyChecked
  , `SeLe4n.Kernel.endpointReplyRecv
  , `SeLe4n.Kernel.endpointReplyRecvChecked
  , `SeLe4n.Kernel.endpointReplyRecvOnCore
  , `SeLe4n.Kernel.endpointReplyRecvWithDonation
  , `SeLe4n.Kernel.endpointReplyWithDonation
  , `SeLe4n.Kernel.endpointSendDual
  , `SeLe4n.Kernel.endpointSendDualChecked
  , `SeLe4n.Kernel.endpointSendDualWithCaps
  , `SeLe4n.Kernel.endpointSweepBody
  , `SeLe4n.Kernel.enqueueIdleThreadOnCore
  , `SeLe4n.Kernel.ensureRunnable
  , `SeLe4n.Kernel.faultAbandon
  , `SeLe4n.Kernel.faultSuspend
  , `SeLe4n.Kernel.handleYield
  , `SeLe4n.Kernel.handleYieldChecked
  , `SeLe4n.Kernel.handleYieldWithBudget
  , `SeLe4n.Kernel.lifecycleCleanupPipeline
  , `SeLe4n.Kernel.lifecyclePreRetypeCleanupWithToken
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanup
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore
  , `SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCoreIcache
  , `SeLe4n.Kernel.lifecycleRevokeDeleteRetype
  , `SeLe4n.Kernel.lockSetAcquiredState
  , `SeLe4n.Kernel.notificationPurgeBody
  , `SeLe4n.Kernel.notificationSignal
  , `SeLe4n.Kernel.notificationSignalBound
  , `SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatch
  , `SeLe4n.Kernel.notificationSignalChecked
  , `SeLe4n.Kernel.notificationWait
  , `SeLe4n.Kernel.notificationWaitChecked
  , `SeLe4n.Kernel.notificationWaitCrossCoreDispatch
  , `SeLe4n.Kernel.processReplenishmentsDue
  , `SeLe4n.Kernel.processRevokeNode
  , `SeLe4n.Kernel.purgedAndRestored
  , `SeLe4n.Kernel.registerInterface
  , `SeLe4n.Kernel.removeRunnable
  , `SeLe4n.Kernel.removeRunnableValid
  , `SeLe4n.Kernel.replenishScOnCore
  , `SeLe4n.Kernel.replyRecvPostPopState
  , `SeLe4n.Kernel.replyTransferOnCore
  , `SeLe4n.Kernel.restoreIncomingContext
  , `SeLe4n.Kernel.restoreIncomingContextChecked
  , `SeLe4n.Kernel.restoredAndConsumed
  , `SeLe4n.Kernel.returnDonatedSchedContextValid
  , `SeLe4n.Kernel.retypeAsidRoundFold
  , `SeLe4n.Kernel.retypeAsidRoundStep
  , `SeLe4n.Kernel.retypeFromUntyped
  , `SeLe4n.Kernel.revokeCdtFoldBody
  , `SeLe4n.Kernel.revokeCdtReportingStep
  , `SeLe4n.Kernel.revokeCdtScaffold
  , `SeLe4n.Kernel.revokePendingTransfersFrom
  , `SeLe4n.Kernel.saveOutgoingContext
  , `SeLe4n.Kernel.saveOutgoingContextChecked
  , `SeLe4n.Kernel.schedule
  , `SeLe4n.Kernel.scheduleChecked
  , `SeLe4n.Kernel.scheduleDomain
  , `SeLe4n.Kernel.scheduleEffective
  , `SeLe4n.Kernel.scheduleOrIdleOnCore
  , `SeLe4n.Kernel.serviceRegisterDependency
  , `SeLe4n.Kernel.setObjectLockAt
  , `SeLe4n.Kernel.setThreadCpuAffinityOp
  , `SeLe4n.Kernel.storeServiceEntry
  , `SeLe4n.Kernel.storeTcbIpcState_fromTcb
  , `SeLe4n.Kernel.storeTcbPendingMessage
  , `SeLe4n.Kernel.streamingRevokeBFS
  , `SeLe4n.Kernel.sweptAndRestored
  , `SeLe4n.Kernel.switchDomain
  , `SeLe4n.Kernel.switchDomainChecked
  , `SeLe4n.Kernel.syncThreadStates
  , `SeLe4n.Kernel.syscallEntry
  , `SeLe4n.Kernel.syscallEntryFromAcquired
  , `SeLe4n.Kernel.syscallEntryUnderDeclaredLockSet
  , `SeLe4n.Kernel.syscallEntryUnderLockSet
  , `SeLe4n.Kernel.syscallLookupReplyId
  , `SeLe4n.Kernel.timeoutAwareReceive
  , `SeLe4n.Kernel.timerTick
  , `SeLe4n.Kernel.timerTickBudget
  , `SeLe4n.Kernel.timerTickChecked
  , `SeLe4n.Kernel.timerTickOnCorePreDomain
  , `SeLe4n.Kernel.timerTickOnCorePrepared
  , `SeLe4n.Kernel.timerTickWithBudget
  , `SeLe4n.Kernel.withObjects
  , `SeLe4n.Model.IntermediateState.state
  , `SeLe4n.Model.SystemState._sizeOf_inst
  , `SeLe4n.Model.SystemState.withObjectStored
  , `SeLe4n.Model.lookupObject
  , `SeLe4n.Model.lookupVSpaceRoot
  , `SeLe4n.Model.setCurrentThread
  , `SeLe4n.Model.setDomainScheduleChecked
  , `SeLe4n.Model.storeObjectChecked
  , `SeLe4n.Model.storeObjectKindChecked
  , `SeLe4n.Model.storeServiceState
  , `SeLe4n.Platform.FFI.bootAndInitialiseFromPlatform
  , `SeLe4n.Platform.FFI.bootAndInitialiseFromPlatformOn
  , `SeLe4n.Platform.FFI.bootAndInitialisePlatform
  , `SeLe4n.Platform.FFI.bootAndInitialiseRPi5
  , `SeLe4n.Platform.FFI.getKernelState
  , `SeLe4n.Platform.RPi5.mmioRead
  , `SeLe4n.Platform.RPi5.mmioRead32
  , `SeLe4n.Platform.RPi5.mmioRead64
  , `SeLe4n.Platform.RPi5.mmioReadByte
  , `SeLe4n.Platform.RPi5.mmioWrite
  , `SeLe4n.Platform.RPi5.mmioWrite32
  , `SeLe4n.Platform.RPi5.mmioWrite32W1C
  , `SeLe4n.Platform.RPi5.mmioWrite64
  ]

/-- The `private` members of the same set.

Lean mangles a `private def` to `_private.<Module>.0.<userName>`, which no name
literal can spell, so each is built with the compiler's own mangling through
`ReplyStackWriteCensus.privateIn`.  Eight of these are that census's own planted
witnesses, which enter this domain because this module imports it for
`isAuxiliary`; they are deliberately not executed, and their presence here is
the derivation working rather than noise to carve out. -/
def nonExecutedTransitionsPrivate : List Name :=
  [ privateIn `SeLe4n.Kernel.API `SeLe4n.Kernel.resolveExtraCapsDetailed
  , privateIn `SeLe4n.Kernel.API `SeLe4n.Kernel.resolveExtraCapsGated
  , privateIn `SeLe4n.Kernel.Capability.Invariant.Defs `SeLe4n.Kernel.ScrubTokenImpl.stPre
  , privateIn `SeLe4n.Kernel.Capability.Operations `SeLe4n.Kernel.revokePendingTransfersStep
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt1
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt2
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt3
  , privateIn `SeLe4n.Kernel.IPC.Invariant.DispatchPayoff `SeLe4n.Kernel.witnessSt4
  , privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt1
  , privateIn `SeLe4n.Kernel.IPC.Invariant.Reachability `SeLe4n.Kernel.chainWitnessSt2
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessBareConsume
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDelegatedStoreHelper
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDelegatedStoreWriter
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessDirectLinkWrite
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessRawTableWrite
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.censusWitnessSplitWriter
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.eq_1
  , privateIn `SeLe4n.Testing.ReplyStackWriteCensus `SeLe4n.Testing.ReplyStackWriteCensus.eq_censusWitnessUserNamed
  ]

/-- The whole pin. -/
def nonExecutedTransitions : List Name :=
  nonExecutedTransitionsPlain ++ nonExecutedTransitionsPrivate

/-! ## The surfaces that stand beside a live re-composition

The category that carries an obligation.  A **non-executed composite** whose
parts the live path re-composes is the shape WS-RR RR8.12 found: the composite
reads as the transition — its name says `OnCore`, its theorems are the
transition's theorems — while a syscall runs something else built from the same
pieces.  A step added to one side and not the other is then invisible, which is
how a permanent denial of service against a passive server survived two cuts.

Reachability alone cannot see that: the composite existed before the step, so
its entry in the pin above would not have moved.  What sees it is a **theorem
relating the two**, which this list requires: each row names the non-executed
surface, the live definition that re-composes it, and the pin.  Adding a step to
the surface and not to the live path breaks the pin at build time.

A row claims that `pin` relates `surface` to code the live path actually runs,
and the checks below are exactly that: the surface is outside the live closure,
the counterpart is inside it, and the pin's *statement* mentions both.  The
counterpart need not be the whole live program — the second row's pin relates
the surface to the arm functions the suspend pipeline's G3 inlines, and naming
one of them is what makes "the live side of this pin" checkable rather than
asserted.  The list is short because the claim is strong; a composite with no
such pin belongs in the pin above instead. -/
def standsBesideLive : List (Name × Name × Name) :=
  [ -- WS-RR RR8.12 (second cut): `cancelIpcBlockingOnCore` is the teardown, its
    -- reclaim and the victim's deschedule; the live `.tcbSuspend` pipeline runs
    -- the reclaim as its G2 and descheduls at G4.  This pin is what the cut
    -- that found the defect added.
    (`SeLe4n.Kernel.cancelIpcBlockingOnCore,
     `SeLe4n.Kernel.cancelIpcBlockingReclaimed,
     `SeLe4n.Kernel.cancelIpcBlockingOnCore_eq_reclaimed_deschedule)
    -- WS-RR RR8.12 (second cut), the sweep's own finding one level down: the
    -- suspend pipeline's G3 re-spells the dispatcher rather than calling it.
  , (`SeLe4n.Kernel.cancelDonationOnCore,
     `SeLe4n.Kernel.cancelBoundDonationOnCore,
     `SeLe4n.Kernel.suspendDonationArm_eq_cancelDonationOnCore)
  ]

/-! ## Reconciliation -/

/-- Where the derived partition and the pin disagree.

Both directions, for the reason `ExportCommitDisciplineCensus` gives for its
own: a **new** non-executed transformer is the dangerous one, since it is a
transition nobody runs that nobody has had to explain; a **stale** entry is the
harmless one and is still a failure, because a pin that no longer describes the
tree understates coverage as silently as it overstates it. -/
def reconciliationViolations (live unreachable : NameSet)
    (recorded : List Name) : List String := Id.run do
  let recordedSet : NameSet := recorded.foldl (fun acc n => acc.insert n) {}
  let mut out : List String := []
  for n in unreachable.toList do
    if !recordedSet.contains n then
      out := out ++ [s!"`{n}` transforms kernel state and no committing `@[export]` can \
        reach it, and it is not in `nonExecutedTransitions`.  Either wire it to the seam \
        that should run it, or record it there — a transition nobody runs and nobody has \
        explained is the shape WS-RR RR8.12 found."]
  for n in recorded do
    if !unreachable.contains n then
      if live.contains n then
        out := out ++ [s!"`{n}` is recorded as not on an executed path and a committing \
          `@[export]` now reaches it; delete the entry, the pin understates what this \
          kernel runs."]
      else
        out := out ++ [s!"`{n}` is recorded in `nonExecutedTransitions` and is not a state \
          transformer in this environment — a stale entry, or a module this census no \
          longer imports."]
  return out

/-- The two sides of a two-sided relation, or `none` if the conclusion is not one.

`Eq` and `Iff` are the two shapes a pin between two programs can take; anything
else -- a conjunction, an implication, a bare predicate -- relates nothing that
this check can read.

The telescope is stripped by `ReplyStackWriteCensus.conclusionOf`, which this
module already imports and which strips `letE` and `mdata` as well as `forallE`:
*before writing a helper, find the one this tree already has.*  The binders are
not instantiated, which is exactly right here -- loose bound variables carry no
constants, and `getUsedConstants` is the only thing read. -/
def pinSides (ty : Expr) : Option (Expr × Expr) :=
  let concl := conclusionOf ty
  match concl.eq? with
  | some (_, l, r) => some (l, r)
  | none =>
    match concl with
    | .app (.app (.const ``Iff _) l) r => some (l, r)
    | _ => none

/-- **Is this pin a RELATION between the two programs?** (PR #897 review.)

The question this replaces was *does the statement mention both constants*, which
is this project's oldest rule failing in the gate written to enforce a different
one: **a presence check is not a relation check.**  A conjunction of reflexive
equations mentions both and says nothing; so does a reflexive equation over a
pair built from both; so does an equation with both programs on one side.  Each
of those satisfies "mentions both" and leaves a step free to be added to either
program alone, which is the whole content of the claim.

What is required instead: the conclusion is `Eq` or `Iff`, and **each program
occurs on exactly one side, on opposite sides**.  A statement of that shape has
one side built from the surface without naming the counterpart and the other
built from the counterpart without naming the surface, so it necessarily connects
the two.  The structural inequality of the sides falls out of it rather than
being asked for separately.

**What it still cannot decide**, stated rather than left to be rediscovered: that
the equation is about the *whole* program rather than a projection of it
(`(surface ..).1 = (counterpart ..).1` passes), and that the two sides are
applied at corresponding arguments.  Those are questions about what a proposition
*means*, and no reading of its syntax answers them; the check over-approximates
there, so it fails closed on shape and admits a narrow-but-real relation. -/
def pinRelatesPrograms (ty : Expr) (surface counterpart : Name) : Bool :=
  match pinSides ty with
  | none => false
  | some (l, r) =>
    let lc := l.getUsedConstants
    let rc := r.getUsedConstants
    -- Each program on exactly one side...
    (lc.contains surface != rc.contains surface)
      && (lc.contains counterpart != rc.contains counterpart)
      -- ...and not the same side.
      && (lc.contains surface != lc.contains counterpart)

/-- Where a `standsBesideLive` row does not hold up. -/
def pinViolations (env : Environment) (live unreachable : NameSet)
    (rows : List (Name × Name × Name)) : List String := Id.run do
  let mut out : List String := []
  for (surface, counterpart, pin) in rows do
    if !unreachable.contains surface then
      out := out ++ [s!"`{surface}` is recorded as standing beside a live re-composition \
        and is not itself outside the live closure; the row's subject has changed."]
    if !live.contains counterpart then
      out := out ++ [s!"`{surface}`'s recorded live counterpart `{counterpart}` is not \
        reachable from any committing `@[export]`, so the row relates two things neither \
        of which runs."]
    match env.find? pin with
    | none =>
        out := out ++ [s!"`{surface}`'s pin `{pin}` does not exist; without it nothing \
          relates the surface to `{counterpart}` and a step may be added to either alone."]
    | some ci =>
        match ci with
        | .thmInfo ti =>
            if !pinRelatesPrograms ti.type surface counterpart then
              out := out ++ [s!"`{pin}` does not RELATE `{surface}` to `{counterpart}`: a \
                pin's conclusion must be an `Eq` or an `Iff` with each program on exactly \
                one side and the two on opposite sides.  Merely mentioning both is a \
                presence check -- a conjunction of reflexive equations passes it -- and \
                leaves a step free to be added to either program alone."]
        | _ =>
            out := out ++ [s!"`{pin}` is not a theorem; a pin between two programs is a \
              proposition about both."]
  return out

/-! ### Witnesses that the pin check decides

Both live rows pass, so nothing on this tree exercises the refusal: a check that
cannot fire is indistinguishable from one that is wrong.  The three theorems
below are the shapes the superseded *presence* check accepted -- each mentions
both programs and relates nothing -- and the census asserts that all three are
refused, beside a control asserting the live pin is accepted, so the refusal is
known to be about the shape rather than about the row. -/

/-- Witness: a conjunction of reflexive equations.  Mentions both programs,
relates nothing; the shape the review named. -/
theorem pinWitnessConjunctionOfReflexivity :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore = @SeLe4n.Kernel.cancelIpcBlockingOnCore)
      ∧ (@SeLe4n.Kernel.cancelIpcBlockingReclaimed
          = @SeLe4n.Kernel.cancelIpcBlockingReclaimed) :=
  ⟨rfl, rfl⟩

/-- Witness: one equation, both programs on **both** sides.  `Eq`-headed, so a
head test alone admits it, and reflexive, so it asserts nothing. -/
theorem pinWitnessReflexiveOverBoth :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore, @SeLe4n.Kernel.cancelIpcBlockingReclaimed)
      = (@SeLe4n.Kernel.cancelIpcBlockingOnCore,
         @SeLe4n.Kernel.cancelIpcBlockingReclaimed) := rfl

/-- Witness: both programs on **one** side.  The sides differ structurally, so a
"not reflexive" test admits it, and the projection discards the counterpart. -/
theorem pinWitnessBothOnOneSide :
    (@SeLe4n.Kernel.cancelIpcBlockingOnCore, @SeLe4n.Kernel.cancelIpcBlockingReclaimed).1
      = @SeLe4n.Kernel.cancelIpcBlockingOnCore := rfl

/-- The three shapes above, each of which must be refused. -/
def pinCheckWitnesses : List Name :=
  [ ``pinWitnessConjunctionOfReflexivity
  , ``pinWitnessReflexiveOverBoth
  , ``pinWitnessBothOnOneSide ]

/-- Every witness shape is refused.

The **acceptance** direction needs no witness of its own: `pinViolations` runs
over `standsBesideLive` in the same block, and both live rows are real relations,
so a change that refused everything would fail there.  Keeping the rows a fix does
not change is what distinguishes a narrowing from a disabling, and those rows are
them. -/
def pinCheckWitnessViolations (env : Environment) : List String := Id.run do
  let surface := `SeLe4n.Kernel.cancelIpcBlockingOnCore
  let counterpart := `SeLe4n.Kernel.cancelIpcBlockingReclaimed
  let mut out : List String := []
  for w in pinCheckWitnesses do
    match env.find? w with
    | some (.thmInfo ti) =>
        if pinRelatesPrograms ti.type surface counterpart then
          out := out ++ [s!"the pin check ACCEPTS `{w}`, which mentions both programs and \
            relates nothing -- it has degenerated into the presence check PR #897's review \
            named, and a step may again be added to either program alone."]
    | _ =>
        out := out ++ [s!"pin-check witness `{w}` is missing or is not a theorem; without \
          it nothing on this tree exercises the refusal, and a check that cannot fire is \
          indistinguishable from one that is wrong."]
  return out

/-! ## The census -/

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let roots := committingExports env
  let live := liveClosure env roots.toList
  let mut domainSize : Nat := 0
  let mut unreachable : NameSet := {}
  for (n, ci) in env.constants.toList do
    if (← isStateTransformer env n ci) then
      domainSize := domainSize + 1
      if !live.contains n then unreachable := unreachable.insert n
  let recorded := nonExecutedTransitions
  let violations :=
    reconciliationViolations live unreachable recorded ++
    pinViolations env live unreachable standsBesideLive ++
    pinCheckWitnessViolations env
  if violations.isEmpty then
    let unreachableCount := unreachable.toList.length
    logInfo s!"kernel-transition reachability census: {domainSize} state transformers, \
      {domainSize - unreachableCount} reachable from one of {roots.size} committing \
      `@[export]`s, {unreachableCount} not — every one of them recorded, and \
      {standsBesideLive.length} RELATED to code the live path runs, with \
      {pinCheckWitnesses.length} witness shapes refused."
  else
    throwError "kernel-transition reachability census failed:\n{
      String.intercalate "\n" (violations.map ("  - " ++ ·))}"

end SeLe4n.Testing.KernelTransitionReachabilityCensus
