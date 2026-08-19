-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
/-!
# WS-SM SM3.C.9 — the syscall → lock-set dispatcher

SM3 built the per-object lock discipline: `LockId` (kind level 0..9 ×
object), a proven total order on it, forty-one `lockSet_*` footprints,
`permittedKinds : SyscallId → List LockKind`, and `withLockSet`'s 2PL /
serializability / observer-atomicity theorems.  What it never built is
the piece that connects them to a running syscall: a function from *the
syscall the dispatcher is about to run* to *the lock set that syscall's
footprint needs*.  Without it the SM3 theorems are statements about an
intended discipline rather than properties of the live path, which is
what SM3.C.9 was deferred to close.

## `Option LockSet`, and why the `none` is the point

Thirty syscalls have footprints; this module declares them one at a
time.  The result is `Option LockSet`:

* `some S` — this syscall's footprint **is** `S`, and every write it
  performs is covered by a member of `S` (the `lockSet_*_write_mem`
  families are the per-op proofs of exactly that);
* `none` — not yet declared.  The caller must fall back to whatever
  coarser serialisation it already has.

The alternative — returning a "best effort" set for undeclared syscalls
— is the one shape this must not take.  A declared lock set that does
not cover a write is not a smaller optimisation, it is a **false
footprint**: the 2PL argument would then rest on exclusion the runtime
never established, and the failure appears as a corrupted object under
contention rather than as a failed proof.  `none` cannot be wrong, and
it makes the migration monotone — each future cut converts one `none`
into a `some` together with its coverage proof, and nothing regresses.

## Runtime scope (read this before wiring more callers)

Declaring a footprint does **not** make per-object locks operative.
`Platform.FFI.modifyGetKernelState` is `IO.Ref.modifyGet` over one
global `SystemState` — a whole-state read-then-write — so two cores
holding disjoint per-object locks would still lose one commit whole.
The lock granularity that matters for that is the granularity of the
*commit*, not of the footprint.  Until the commit is partitioned, the
SM5.I kernel-entry lock stays, and what this dispatcher buys is the
model-level property: the SM3 theorems apply to the transition the
kernel actually runs.  See `rust/sele4n-hal/src/kernel_entry.rs`.
-/


namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

/-- **WS-SM SM3.C.9**: resolve `tcbSuspend`'s state-dependent footprint
arguments from the pre-state.

The five optional members are exactly the writes the suspend pipeline
can make beyond the victim's own TCB, and each is read here from the
same field the transition branches on:

* the endpoint it is blocked on (`blockedOnSend` / `blockedOnReceive` /
  `blockedOnCall` / `blockedOnReply` all name one) — the cancellation
  sweep unlinks the victim from its queue;
* the notification it is blocked on — same, for the notification queue;
* the Reply object consumed when the victim is `blockedOnReply`;
* its bound or donated SchedContext — the donation teardown writes it;
* the original owner a donated SchedContext returns to.

The CNode member is the **caller's** CSpace root, not the victim's.
`cnodeRootObjId` is the cap-resolution root — the CNode the syscall
actually reads to turn the caller's capability pointer into the target
capability (`syscallLookupCap` builds its gate from the *caller's*
`tcb.cspaceRoot`), which is why it is paired with the caller's TCB read
in every `lockSet_*` that has one.  An earlier cut passed
`victim.cspaceRoot`, so whenever caller and victim held different
CSpace roots the declared set locked a CNode the syscall never touches
and omitted the one it reads — a coverage hole in exactly the direction
a declared footprint exists to prevent.  Not a live defect (SM3.C.9
still defers `withLockSet` at the `@[export]` bodies), but the whole
value of the declaration is that it covers the operation's accesses.

`none` for the whole set when **either** thread fails to resolve to a
TCB: with no victim there is no transition to bound, and with no caller
there is no CSpace root to name. -/
def suspendFootprintOf (st : SystemState) (callerTid targetTid : ThreadId) :
    Option LockSet :=
  -- Read through the AL2-A typed accessor, not a raw `objects[...]?`
  -- match: the footprint is a statement ABOUT the object store, so it
  -- has no business reading it in a way the AK7 cascade counts as an
  -- un-migrated raw access.
  match st.getTcb? callerTid, st.getTcb? targetTid with
  | some caller, some victim =>
      let blockedEndpoint : Option ObjId :=
        match victim.ipcState with
        | .blockedOnSend ep => some ep
        | .blockedOnReceive ep => some ep
        | .blockedOnCall ep => some ep
        | .blockedOnReply ep _ => some ep
        | _ => none
      let blockedNotification : Option ObjId :=
        match victim.ipcState with
        | .blockedOnNotification n => some n
        | _ => none
      let consumedReply : Option ReplyId :=
        match victim.ipcState with
        | .blockedOnReply _ _ => victim.replyObject
        | _ => none
      let bindingSc : Option SchedContextId :=
        victim.schedContextBinding.scId?
      let donatedOwner : Option ThreadId :=
        match victim.schedContextBinding with
        | .donated _ owner => some owner
        | _ => none
      some (lockSet_tcbSuspend callerTid caller.cspaceRoot targetTid
              blockedEndpoint blockedNotification bindingSc
              donatedOwner consumedReply)
  | _, _ => none

/-- **WS-SM SM3.C.9**: the declared lock-set footprint of a syscall, or
`none` where one has not been established yet.

Total over `SyscallId` by construction — a new syscall variant makes
this fail to compile rather than silently inherit a neighbour's
footprint.  See the module docstring for why undeclared arms return
`none` instead of an approximation. -/
def lockSetForSyscall (sid : SyscallId) (callerTid targetTid : ThreadId)
    (st : SystemState) : Option LockSet :=
  match sid with
  | .tcbSuspend => suspendFootprintOf st callerTid targetTid
  -- Undeclared: the caller keeps its existing serialisation.  Each of
  -- these becomes a `some` in a later cut, paired with the coverage
  -- proof that its footprint contains every write the op performs.
  | .send | .receive | .call | .reply | .replyRecv
  | .notificationSignal | .notificationWait
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete
  | .mintReplyCap
  | .lifecycleRetype
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind
  | .tcbResume | .tcbSetPriority | .tcbSetMCPriority
  | .tcbSetIPCBuffer | .tcbSetAffinity
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify
  -- WS-SM SM9.C.8: `.declassifySignal` is undeclared here for the same reason,
  -- and its per-object footprint (`lockSet_declassifySignal`) is the ordinary
  -- signal's set plus the state-level write its trail append needs.  The
  -- caller TCB stays `.read` — the syscall is `.unit`-shaped, so unlike the
  -- audit pair the committed dispatch stages nothing into the caller's TCB.
  | .declassifySignal
  -- WS-SM SM9.A.12: the audit reader and the drain are undeclared here for the
  -- same reason as every other arm — the declared-footprint bracket is SM3.C.9
  -- work, not SM9.A work.  Their per-object footprints (`lockSet_auditRead` /
  -- `lockSet_auditDrain`) carry the caller TCB in **write** mode (PR #870
  -- round 6): the transitions write no object, but the committed dispatch
  -- stages the returned word into the caller's TCB via WS-RA's
  -- `writeReturnFrameToTcb`, and a footprint covers the committed dispatch.
  | .auditRead | .auditDrain => none

/-- **WS-SM SM3.C.9**: the `tcbSuspend` arm is wired to the resolver.

Pins the dispatch itself, so a future edit that redirects the arm or
drops the resolver fails here rather than silently returning `none` and
sending the caller back to coarse serialisation without anyone noticing
the footprint stopped being declared. -/
@[simp] theorem lockSetForSyscall_tcbSuspend
    (callerTid targetTid : ThreadId) (st : SystemState) :
    lockSetForSyscall .tcbSuspend callerTid targetTid st
      = suspendFootprintOf st callerTid targetTid := rfl

/-- **WS-SM SM3.C.9**: every arm other than `tcbSuspend` is undeclared.

The load-bearing direction. A caller reading `some S` treats `S` as the
complete set of objects the transition writes, so an arm that returned a
footprint before its coverage proof existed would hand out exclusion the
runtime never established. This is the negative that keeps the migration
honest: exactly one arm is declared today, and adding the next one must
change this theorem. -/
theorem lockSetForSyscall_undeclared_none
    (sid : SyscallId) (callerTid targetTid : ThreadId) (st : SystemState)
    (h : sid ≠ .tcbSuspend) :
    lockSetForSyscall sid callerTid targetTid st = none := by
  cases sid <;> first | rfl | exact absurd rfl h

/-- **WS-SM SM3.C.9**: the suspend footprint resolves exactly when the
target names a TCB.

`none` is not a failure mode here — a target that is not a TCB has no
suspend transition to bound, so there is no footprint to declare and the
caller correctly falls back. -/
theorem suspendFootprintOf_isSome_iff
    (st : SystemState) (callerTid targetTid : ThreadId) :
    (suspendFootprintOf st callerTid targetTid).isSome
      ↔ (∃ caller, st.getTcb? callerTid = some caller) ∧
        ∃ victim, st.getTcb? targetTid = some victim := by
  unfold suspendFootprintOf
  constructor
  · intro h
    split at h
    · next caller victim hc hv => exact ⟨⟨caller, hc⟩, victim, hv⟩
    · simp at h
  · rintro ⟨⟨caller, hc⟩, victim, hv⟩
    rw [hc, hv]
    simp

end SeLe4n.Kernel.Concurrency
