# WS-RA — Syscall Return ABI: full seL4-ABI x0 compliance

> **Workstream**: WS-RA (Return ABI)
> **Relationship to WS-SM**: prerequisite for SM10.E (bootable image) and for
> SM9.C (data-carrying declassification); orthogonal to the SMP phases
> **Audited cut**: `v0.33.30`; **pre-implementation refinement pass**: `v0.33.36`
> — every §1.1 claim re-verified against the tree, and the corrections folded
> in where found (the §3.1 label offset, the §3.4 shape vocabulary, RA.B.10's
> projection premise, the §6.2 trace-fixture story, the discovered Rust-side
> defects now in RA.C/RA.D)
> **Sub-task count**: 41 across ~12-15 PRs (the plan's estimate; the landing
> collapsed to 6 commits because the flip is one atomic cut — see the landing
> record below)
> **Status**: **COMPLETE — core LANDED at v0.33.37; RA.B.5b + RA.B.8 LANDED
> at v0.33.38.**  Both return orderings are staged end to end (the immediate
> half returned at the boundary, the blocked half staged by the unblocking
> arm), and the per-arm shape-coherence family is proven.  What remains is
> owed to SM10.E, not to this workstream: frame *delivery* at the context
> restore, and the cancellation/timeout error-frame staging (§9).  §1 below
> records the **pre-flip** state the workstream removed.

## Landing record — core landed at v0.33.37; completed at v0.33.38

Six commits, sequenced as §5 prescribed: the RA.E.1 witness suite landed
first and **failed on the pre-migration tree** (its assertions then inverted
to post-flip pins in the same file); RA.A landed the model
(`SeLe4n/Kernel/Architecture/SyscallReturn.lean`, ~800 lines — the total
`syscallReturnShape`, the offset error label with all 55 discriminants
round-tripped, the frame codec, `SyscallOutcome`, the staging seam, and
`bit63Encoding_not_injective_on_badges` as the retained hazard); RA.B landed
the staging seam and the **arm-level** staging of all five value-returning
syscalls (`.notificationWait` ×2 → `returnFrameOfBadge`; `.receive` /
`.replyRecv` ×2 each → `stageDeliveredMessage`; `.serviceQuery` →
`returnFrameOfWord`) plus `writeReturnFrameToTcb_preserves_projection` for
**every** observer; and the flip cut RA.C + RA.D + RA.E.2-E.5 atomically —
`syscallDispatchFromAbi : … → Kernel Architecture.SyscallOutcome`, the
per-core return-frame mailbox (`ffi_syscall_return_frame` /
`ReturnFrameMailbox`), `trap.rs` restoring all six registers
(`set_return_frame`), `decode_response` rewritten to the label convention,
`encodeOk` / `encodeError` / `syscallDispatchInner` **deleted** with Tier-3
negative anchors, `SYSCALL_ABI_VERSION = 2` pinned on all three sides
(Lean `decide` theorem; Rust test-compile-time `const` assertion), the five
unreachable-wrapper prefilter defects fixed, and the golden fixture
`tests/fixtures/syscall_return_abi.expected` byte-verified in-suite.
Validated at the flip: full Lean library, all 68 suites, main trace
byte-identical, Rust workspace green + clippy-clean, routing gate at zero
exceptions, partition + axiom sweeps + Tier 3 green.

**Completion record — RA.B.5b and RA.B.8 landed at v0.33.38.**

**RA.B.5b** landed at the **arms**, not at the transitions — the same design
sharpening RA.B.6 recorded for the immediate half, applied to the blocked
half once the delivery shape was verified against the tree: every wake in
the tree delivers through `.ready` + `pendingMessage := msg`
(`storeTcbIpcStateAndMessage` / `storeTcbReceiveComplete`), so the payload
is recoverable at the arm post-state and the plan's drafted store-sibling
mechanism (`storeTcbReadyWithFrame`, one-call swaps inside the transitions,
the per-site invariant re-proof bulk of the XL) was **not needed** — zero
IPC transitions changed, zero of the ~1900-reference invariant surface
moved.  Two Option-lifted stagers (`Architecture.stageWokenDelivery` over
`stageDeliveredMessage`; `stageWokenSendCompletion` staging the zero frame
for a completed **plain sender**, guarded `.ready` ∧ consumed so a `Call`
sender and a payload wake are skipped) compose at eleven sites: the
`.send`/`.call` arms (×2 each — pre-resolved receive-queue head), the
`.reply` arms (×2 — the resolved caller), the `.receive` arms (×2 — the
send-queue head's unit frame beside the existing caller staging), the
`.notificationSignal` arms (×2 — plain head waiter + bound target, mutually
exclusive), and `replyRecvBody` (×1, both legs, shared by both `.replyRecv`
arms).  The plan-named theorems: `blockedReturn_staged_in_waiter_frame` (a
payload wake's staged frame is exactly `returnFrameOfMessage msg`,
recovered bit-for-bit by the boundary read) and its unit dual
`blockedUnitReturn_staged_in_sender_frame`; both stagers carry
scheduler/machine frames and every-observer projection preservation via
RA.B.10's blanket.  Theorem fallout: eight delegation RHS
(`dispatchWithCap{,Checked}_send_delegates`, `_receive_delegates`,
`_send_uses_withCaps`, `_call_uses_crossCoreDispatch`,
`_reply_populates_msg`, the two `syscallDelegates` arms) updated in
lockstep; the `checkedDispatch_{reply,replyRecv}_eq_unchecked_when_allowed`
equivalences survived unchanged (both sides move together; `replyRecvBody`
is shared); SM8.B's `replyRecvBody_confinedToCores` re-proven by
transporting the donation leg's confinement across the staging steps
(`observableSlotsConfinedToCores_of_framed_suffix` — the stagers frame
scheduler and machine).  Evidence: `SyscallReturnAbiSuite` §9 (five
end-to-end two-core scenarios through the live per-core dispatch —
wait-before-signal with the stale-args negative control, blocked receiver,
completed plain sender incl. its pre-receive stale-x0 control, the reply
delivering `.call`'s frame, and `replyRecvBody`'s own composition) plus
three new golden-fixture lines computed from the staged frames.

**RA.B.8** landed as the five-theorem value-half family plus the structural
unit half.  The draft's phrasing — "a `.unit` arm leaves the caller's
staged frame untouched" — is deliberately **not** the theorem: it is false
of any arm that context-switches (`saveOutgoingContext` writes
`registerContext`) and unnecessary, because `frameForShape_unit` makes the
boundary **construct** unit frames without reading staged registers, so no
arm can disagree with a `.unit` classification structurally.  The value
half is per-arm over the live dispatch:
`dispatchArm_notificationWait_matches_returnShape` (`.badge`),
`dispatchArm_serviceQuery_matches_returnShape` (`.word`),
`dispatchArm_receive_matches_returnShape` and
`dispatchArm_replyRecv_matches_returnShape` (`.message`), and
`dispatchArm_call_frame_delivered_by_reply` — the cross-arm form of §3.5's
"a call never returns at its own boundary": the `.reply` dispatch stages
the *caller's* `.message` frame and the boundary read at the caller
recovers it.  With `syscallReturnShape_value_returning` pinning the value
surface at exactly those five syscalls, the family covers it.

**Still owed elsewhere (registered in §9, owner SM10.E)**: frame *delivery*
(the context restore — `contextRestoreSeamLive = false` until SM10.E) and
the cancellation/timeout **error-frame** staging (`cancelIpcBlocking` /
`timeoutThread` stage nothing; before the restore seam flips they must
stage an error frame).  Neither is WS-RA scope: the workstream's staging
obligations are complete.

**Audit cut (v0.33.39)** — a post-completion audit of the whole PR,
checked against the code rather than the documentation describing it.  No
false theorem and no live vulnerability; five findings, all closed:
(1) **`ipcStateBlocksReturn` carried a wildcard** — the exact pattern
§3.4 forbids for `syscallReturnShape`, and here the failure mode is
sharper: a future `ThreadIpcState` constructor would silently classify as
"blocks", and a returning caller misclassified as blocked gets no
writeback — it resumes with its spilled arguments under the *request's*
`MessageInfo`, which decodes as a **false success** carrying the
capability pointer.  Now an exhaustive six-arm match.  (2) **The
return-frame mailbox's writer and reader keyed on different core-id
sources** — `ffi_syscall_return_frame` on the software-initialized
TPIDR-derived id, `dispatch_svc`'s read (and its entry-lock bracket) on
the MPIDR-derived hardware id.  Correct under the boot invariant, but one
mis-set `TPIDR_EL1` and a return frame lands in another core's slot — to
be handed to a *different* thread's next syscall as its return value.
Both now read `cpu::current_core_id()`; the pairing carries no
two-sources-agree obligation.  (3) **`.serviceQuery` had no runtime
staging witness** — the one value shape §9's blocked orderings do not
pass through; §9f registers a service, dispatches the query end to end
and pins the staged word, the outcome frame and the decode, with a
`word query` golden-fixture line completing the fixture's coverage of
the value surface.  (4) **The `.serviceQuery` RA.B.8 theorem's `hLookup`
was decorative** (the defect class SM8.D's review history names): it
concluded only the arm's state-generic function equality, which holds
without the hypothesis.  Restated like its four siblings — over the live
dispatch at the given state, where the lookup equation drives the match.
(5) **The suite's fixtures were lifecycle-inconsistent** —
`TCB.threadState` defaults to `.Inactive`, the fixtures never set it, and
the IPC scenarios masked it because the IPC transitions read `ipcState`
only; the new §9g self-suspend witness surfaced it when `suspendThread`'s
guard (correctly) refused to suspend an `.Inactive` thread.  Fixtures now
carry `.Running` / `.BlockedReply`, and §9g pins §3.5's parenthetical at
runtime: a self-`.tcbSuspend` deschedules (current cleared), does not
IPC-block, and **returns** the constructed unit frame.  Verified sound
along the way: staging creates no new information flow (every stager
copies a payload the gated transition already delivered into the *same*
thread's own projection-stripped `registerContext`); the arm-level
counterparty pre-resolutions agree with what each transition wakes, with
the `.ready`/`pendingMessage` guards making every divergence case inert;
the bound/plain signal targets are structurally exclusive
(`boundDeliveryTarget?` requires an empty wait queue); the error arms
commit exactly the argument-spill state; a unit syscall's constructed
frame survives the context-switch `registerContext` clobber
(`saveOutgoingContext`) precisely because it is constructed; the Rust
`error_frame_regs` matches `Architecture.errorFrame` label-for-label;
`returnMessageInfo` is clamped inside the 7/2/20-bit fields; and the
whole surface is axiom-clean (2,025 elaborated constants swept).  One
deprecation warning (`String.mk`) and the unused-hypothesis warning were
the tree's only two; both fixed — the build is warning-free.

**PR #866 review (Codex P1, same cut) — the blocked-resume sentinel.**
The review observed that a `Blocked` outcome reaches a no-op trap arm
while `contextRestoreSeamLive = false`, so `trap.S` restores and `eret`s
through the blocked caller's own saved frame — and the caller's request
registers (an `x1` whose label is typically `0`) then decode as a
**false success** whose `x0` "badge" is the caller's own capability
pointer, the exact fail-open class WS-RA exists to close, live for every
genuine block rather than only for the audit's misclassification case.
Valid; two halves.  The demanded successor-install *is* the SM10.E
context-restore seam (save the outgoing frame, choose a successor,
restore its `registerContext` — the delivery half §9 already owes to
SM10.E, tracked in `SMP_RELEASE_CLOSURE_PLAN.md`), and pulling a whole
scheduled phase into a review fix would be the wrong cut.  The
observable-harm half is closed **now**: the `Blocked` arm poisons the
frame with `blocked_resume_sentinel_regs()` — `x1` label
`BLOCKED_RESUME_SENTINEL_LABEL = 0xFFFFF`, the maximum in-field
`MessageInfo` label, compile-time-asserted outside the kernel-emittable
set `{0} ∪ {1..=55}` — which `decode_response` collapses to
`UnknownKernelError`: an error the verified kernel never emits, so a
premature resume reads fail-closed, never as success and never as a real
kernel error (a real `KernelError` would lie twice — the syscall did not
fail, and for `.call` the request was already *sent*, so an error verdict
would drive a userspace retry into a double-send).  The sentinel is an
interim HAL artifact, deliberately **not** part of the verified
convention (`SyscallOutcome.mailboxFrame .blocks = .zero` is unchanged;
the model stages real frames only), and the SM10.E flip replaces the
write with the successor's install.  Pinned by
`blocked_resume_sentinel_shape` (raw shape; the hand-duplicated label
equals `sele4n-abi`'s `MAX_LABEL`; in-field; collides with no
discriminant's error frame) and `blocked_resume_sentinel_decodes_fail_closed`
(the canonical decoder reads it as `UnknownKernelError`, with the
load-bearing negative that an *unpoisoned* stale request frame decodes as
the false success the review describes — the fail-open path the sentinel
closes), via a new test-only `sele4n-abi` dev-dependency following the
`sele4n-types` cross-check precedent.  HAL 821 → 823 tests.

**PR #866 review round 2 (v0.33.40)** — three further Codex findings,
each verified against the code; one corrects the v0.33.39 audit's own
fix.  **(1) Installed-caps honesty (P1, valid).**  `returnMessageInfo`
read `extraCaps` off the delivered message's `caps.size` — the
*requested* count — while `ipcUnwrapCaps` succeeds with zero installs
(grant denied, no free slot) and the delivered `pendingMessage` keeps
the requested caps either way, so a receiver was told capabilities
arrived when none did and would interpret its receive slots' existing
contents as fresh authority.  The synthesis now takes an explicit,
deliberately-undefaulted `installedCaps`; the send/call arms pass the
transfer summary's new `CapTransferSummary.installedCount` (the summary
those dispatches already returned and the arms **discarded** — the
computed-but-unconsumed case), reply and notification arms pass `0`
(`caps := #[]` by construction / badge-only), and
`returnMessageInfo_extraCaps_le_installed` is the honesty bound.  Suite
§9h drives a grant-denied and a granted transfer through the live
dispatch (staged `extraCaps` 0 vs 1, the delivered message still
carrying the requested cap as the load-bearing negative; 13th golden
fixture line).  **Tracked debt registered (receive-side unwrap)**:
verifying the finding found that the live receive paths (`.receive`,
`.replyRecv`'s receive leg → `endpointReceiveDualOnCore`) run **no
unwrap at all** — `endpointReceiveDualWithCaps` has never had a live
caller — so a sender that parks with caps never has them installed when
the receiver arrives second.  Fail-closed (no authority is installed
without the transfer machinery; the sender retains the originals) and
now *honestly reported* (those arms pass installed = 0), but a
completeness gap: closure is an OnCore WithCaps composition mirroring
`endpointSendDualWithCapsOnCore` (the receive rendezvous, then
`ipcUnwrapCaps` keyed on the dequeued sender's CSpace root, with the
delegation/equivalence family updated in lockstep) — **and it is a
design cut, not a wiring one**: the unwired single-core
`endpointReceiveDualWithCaps` gates the transfer on the **receiver's**
endpoint-cap `.grant` right (its `endpointRights` parameter is the
caller's gate), while seL4's transfer gate is the **sender's** grant —
and at receive-time dequeue the parked sender's cap rights were consumed
when it parked and are recorded nowhere, so a faithful closure must
first capture the sender's grant at park time (a parked-message or TCB
field, with its freeze/projection carriage).  Wiring the existing form
verbatim would install caps under the wrong subject's authority — worse
than the honest zero.  Owner: the IPC subsystem, alongside SM6.D's
WithCaps carriage items; until then the one live transfer ordering is
receiver-first.  **(2) The core index is
the TPIDR logical id (P2, valid — and it reverses the v0.33.39 fix's
direction).**  The audit unified the mailbox's writer and reader on ONE
source, but chose the packed MPIDR value, whose own contract forbids
array indexing: on the BCM2712's two-cluster topology a second-cluster
core reads `0x100`, which aborts every syscall at the mailbox bounds
assert AND silently disables the kernel-entry spin's shootdown
self-service (its out-of-range guard fails closed to "no self-service"
— the ack deadlock it exists to prevent, restored).  All three
packed-index sites — `ffi_syscall_return_frame`, `dispatch_svc`, and
the pre-existing `sele4n_suspend_thread` bracket key — now read
`per_cpu::current_core_id_from_tpidr()`: the boot-validated logical
index (`core_id < coreCount` via `check_per_cpu_invariants`) and the
space the Lean dispatch's own `executingCore : Fin numCores` lives in
(`ffi_current_core_id`).  One source still — the audit's principle
stands, re-grounded on the index the rest of the per-core state
(timer, trap-IRQ, shootdown, stats) already uses.  **(3) Typed
`ServiceId` (P1, valid).**  `service_query` returned a bare `u64` while
`service_revoke` takes a `ServiceId`; the wrapper now returns
`KernelResult<ServiceId>`, so the query→revoke composition typechecks
without an untyped detour.

**PR #866 review round 3 (v0.33.41)** — five further findings; two are
code defects (fixed, with the architectural cause removed), three
challenge deliberate designs or registered deferrals (answered with the
rationale; one adds new tracked debt).  **(1) Four more unreachable
wrappers + the table that could not see them (P2, valid — the RA.D.1
class again, and its root cause).**  The HAL prefilter minima for
`tcbSuspend` / `tcbResume` / `schedContextUnbind` (1/1/1) and
`schedContextBind` (2) exceeded what the Lean decoders — the authority —
require (0/0/0/1: suspend, resume and unbind are `pure {}`
capability-only decodes; bind reads exactly one register), so all four
real wrappers were rejected with `InvalidArgument` before reaching the
kernel.  The conformance table that existed to prevent exactly this
stayed green because **both of its columns were hand-duplicated
literals**: it recorded length 1 for suspend/resume (the wrappers send
0) and omitted the schedContext pair entirely.  The minima are
corrected, and the table is rebuilt so neither column can drift again:
the mock trap (`sele4n-abi`, host builds) now records the request
registers it is handed (`trap::host_capture`), and
`wrapper_lengths_clear_prefilter_minimums` drives **every real
wrapper**, reads back the exact registers its encode produced, and
compares the decoded length against the **real**
`sele4n_hal::svc_dispatch::SyscallId::min_inline_args()` through a
test-only `sele4n-hal` dev-dependency (dev-edges both ways between the
two crates; no build-graph cycle — dev-dependencies do not participate
in library resolution).  Run against the old minima the rebuilt sweep
fails on exactly the four; against the fix it is green.  Coverage is
the whole canonical surface: the three syscalls that had **no**
`sele4n-sys` wrapper at all (`tcbBindNotification` /
`tcbUnbindNotification` / `mintReplyCap` — callable only via
hand-encoded requests) got their wrappers implemented in the same cut
(bind resolves the notification through a capability in the caller's
CSpace, MR0, per the SM6.B v0.31.74 arm; unbind is capability-only;
mint reuses the `cspaceCopy` register shape against `.grant`), so the
sweep pins all 31.  **(2) `endpoint_call` joins the `.message`
signature contract (P2, valid).**  The shape table classifies `.call`
as `.message` and the signature pin says message-shaped wrappers return
`(Badge, SyscallResponse)` — but the pin listed only receive and
reply-recv, and `endpoint_call` returned a bare `SyscallResponse`.  The
wrapper now returns the badge tuple (a call's reply-delivered frame
carries the badge in `x0` exactly as a receive's does), and the pin
covers `endpoint_call` and `endpoint_receive_with_reply`.  **(3)
Self-suspend outcome (P1, challenged — the design stands).**  The
review asked that a self-suspended caller's outcome account for
scheduler state and its unit frame be delivered "only after an actual
resume".  The outcome deliberately classifies *whether the caller has a
return value*, and a self-suspend has one — the constructed unit
success frame, which is true (the suspend committed) and is exactly
what the thread must observe when later resumed; under SM10.E the
restore seam writes it to the trap frame, saves that frame into the
descheduled TCB, and installs a successor, so delivery-at-resume falls
out of the seam.  Classifying it `.blocks` instead would be wrong
twice: nothing ever wakes-and-stages a suspended thread (resume
re-enqueues; it delivers no payload), so the frame would never exist,
and the interim sentinel would then hand the resumed thread
`UnknownKernelError` for a syscall that succeeded.  The interim
keeps-running gap is the universal absence of hardware context
switching (every scheduling decision, not this arm), and the vacated
core fails closed meanwhile (`vacatedCore_next_syscall_rejected`).
§9g pins the value half at runtime.  **(4) Application IPC labels (P1,
valid observation — pre-existing model gap, now TRACKED DEBT with the
design constraint recorded).**  The sender-side API accepts a
`MessageInfo.label` that the kernel model drops at decode
(`IpcMessage` carries no label — pre-WS-RA the model never delivered
one), and WS-RA's return convention makes `x1`'s label the **status**
channel, so a delivered sender label cannot simply ride `x1`: label
`L` would alias error discriminant `L − 1`, the exact aliasing the
offset encoding exists to prevent.  Closure therefore needs an ABI
design decision, not a patch: candidate designs are (a) shape-aware
decode — message-shaped successes carry the sender's label and errors
for those syscalls move off the label channel (closest to seL4, whose
receive path has no kernel-error channel at all), or (b) delivering
the sender's label out of band (a reserved message register or IPC
buffer field).  Either changes `IpcMessage`, the delivery sites, the
synthesis, `decode_response` and the conformance surface together —
registered here as WS-RA follow-on debt, owner the ABI surface, to be
cut as one coherent slice.  **(5) Timeout error frames (P1 — the
registered §9 deferral, restated).**  The review re-derives that
`timeoutThread` wakes a timed-out caller without staging
`errorFrame .ipcTimeout`; that is precisely the
"cancellation/timeout error-frame staging" this plan's §9 already owes
to SM10.E, deliberately deferred WITH the delivery seam because the
involuntary-unblock family (timeout, suspend-of-blocked,
`cancelIpcBlocking`) lives inside scheduler transitions whose staging
lands with the restore seam that makes any staged frame reachable;
until that seam exists the interim hardware outcome is governed by the
blocked-resume sentinel either way.  No claim is weakened: the RA.B.5b
guarantee is stated over the IPC unblocking arms, and §9 names the
involuntary family as owed.

## 1. Phase goal

**The kernel has no syscall return path.**  It writes exactly one register on
exit — `x0` — and the value it writes is not a return value.  Everything a
syscall is supposed to hand back to userspace (badges, allocated slots, message
registers) is never written at all, and userspace reads its own pre-syscall
register contents back.

This is not one broken syscall.  It is the return half of the ABI, unimplemented
and documented as such.

### 1.1 What is actually there, verified

| Step | Code | Behaviour |
|---|---|---|
| Lean stages args | `writeFfiRegistersToTcb` (`FFI.lean`) | writes the **incoming** `x0..x5` into `tcb.registerContext`; `x0 ← capPtrReg` |
| Lean returns | `syscallDispatchFromAbi` | `.ok (encodeOk (readReturnValue st' tid), st')` — reads `gpr ⟨0⟩` back out |
| Nothing writes it | — | **no transition anywhere writes a return value into `gpr ⟨0⟩`** (verified by exhaustive grep) |
| Rust decodes | `dispatch_svc` | bit 63 set → `Err(DispatchError::Kernel(disc))`; else `Ok(raw)` |
| Trap writes | `dispatch_svc`'s caller in `trap.rs` | `frame.set_x0(retval)` — and **nothing else**; `set_x1` exists and is called only in a unit test; `x2`-`x5` are never written back |
| Userspace decodes | `decode_response` (`sele4n-abi/src/decode.rs`) | **`regs[0] != 0` means error** — `x0 == 0` *is* the success discriminant |

`FFI.lean` documents the middle of this honestly: *"x0 post-syscall therefore
equals the caller's own pre-syscall x0 (since `writeFfiRegistersToTcb` populates
`pos[0]` with the FFI-passed x0 argument) … This is the documented current
behaviour — full seL4-ABI x0 compliance for value-returning syscalls"* is
deferred.

### 1.2 The consequence, stated precisely

Compose the last two rows.  On a **successful** syscall the kernel returns the
caller's own `x0` — the capability pointer — and userspace tests `regs[0] != 0`.
For any capability pointer other than `0`, **a successful syscall decodes as a
`KernelError`**, with the cap pointer reinterpreted as the discriminant.

This is a derivation from two independently documented facts, not an observed
failure: no end-to-end test can exist until SM10.E produces a bootable image, so
nothing has ever executed this path.  RA.E.1 makes it observable before it makes
it correct.

### 1.3 The value-returning surface, enumerated

`SyscallId` has 31 variants.  Five of them are **value-returning today and
return nothing**; SM9 adds two more.  Each row below is verified against the
dispatch arm, not inferred from the name:

| Syscall | Should return | What the arm does today |
|---|---|---|
| `.notificationWait` | badge | `notificationWaitOnCore` returns `.ok (some badge)`; both live arms match `(st', .ok _)` and discard it |
| `.receive` | badge + message registers | delivery lands in `tcb.pendingMessage`, which no code moves to a register |
| `.call` | badge + message registers | same |
| `.replyRecv` | badge + message registers | same |
| `.serviceQuery` | the resolved service | `lookupServiceByCap` is called and its result **discarded**: `.ok (_, st')` |
| `.auditRead` (SM9.A) | the selected audit word | blocked on this workstream — `dispatchWithCapChecked` is `Kernel Unit` |
| `.auditDrain` (SM9.A) | the new visible length | same |

The remaining 26 are genuinely `Unit`-returning and need only `x0 = 0`, which
they do not produce today either — they return the caller's cap pointer like
everything else.

`.serviceQuery` is worth singling out: it is a **query** whose entire purpose is
to answer, and it computes the answer and throws it away.  That is the same
shape as `.notificationWait`, at a syscall nobody had reason to look at, which is
the argument for fixing the convention rather than the two syscalls someone
noticed.

### 1.4 Three further consequences

Beyond the enumerated surface, the same gap produces:

- `sele4n-sys::notification_wait` returns `KernelResult<Badge>` and reads
  `resp.badge()` = **x1**, which the kernel never writes — so it returns the
  caller's own pre-syscall x1 presented as a badge.  Badge-based sender
  discrimination is entirely non-functional.  (This is the defect registered as
  **SM9.C.0**; it is closed by this workstream, not by a local patch, because
  `tcb.pendingMessage` — where the signal path stores the badge — has no register
  path either.)
- `endpoint_receive` and friends return `msg_regs` read from `x2`-`x5`, likewise
  never written.
- `cspace_mint` and the retype family return a `SyscallResponse` whose only real
  content is the error field, so an allocated slot cannot be reported.

### 1.5 Why "x0 compliance" and not "write x1"

Writing `x1` would close SM9.C.0 with a much smaller diff, because
`decode.rs::badge()` already reads x1.  It was considered and **rejected by the
maintainer** in favour of the correct ABI, and the reasoning holds up: the x1
route leaves `x0` a status word that seL4 does not have, leaves `x2`-`x5`
unwritten, and leaves the `regs[0] != 0` success test in place — so every other
value-returning syscall stays broken and the ABI drifts further from the
reference it claims to follow.  Fixing one register is a patch; this workstream
fixes the convention.

## 2. Dependencies

- **None blocking.**  The work is self-contained in `Platform/FFI.lean`,
  `Kernel/API.lean`'s dispatch arms, and the three Rust crates.
- **SM5.I** (kernel-entry serialisation) is already live, so the return path has
  a single well-defined commit point.
- **Blocks**: SM9.C (a data-carrying declassification cannot ship over a path
  that delivers nothing) and SM10.E (a bootable image whose syscalls all report
  spurious errors is not bootable in any useful sense).

## 3. Architectural choices

### 3.1 The target convention

seL4's ARM64 syscall convention on **return** (libsel4
`arch/arm/arch64/sel4/sel4_arch/syscalls.h`):

| Register | On return |
|---|---|
| `x0` | **badge** (Recv/Wait/ReplyRecv) or the invocation's primary result |
| `x1` | `seL4_MessageInfo` — whose **label** carries `seL4_Error` |
| `x2`-`x5` | message registers |

Errors are **not** a separate status register.  They ride the message-info
label, which is why seL4 can hand back a full-width badge in `x0` without any
aliasing question.  That is the property this codebase currently lacks and the
reason its status word has nowhere else to live.

**Decision.**  Adopt it exactly:

- `x0` = primary return value (badge / queried word / `0` for `Unit`-returning
  syscalls)
- `x1` = `MessageInfo` with `label` = **`KernelError` discriminant + 1**, and
  label `0` = success
- `x2`-`x5` = message registers
- **`encodeOk` / `encodeError` and the bit-63 protocol are retired.**  Bit 63 was
  a workaround for multiplexing status into the value register; with the channels
  separated there is nothing to multiplex, and a badge may use all 64 bits.

**The `+ 1` is load-bearing, not a convention.**  `KernelError`'s discriminants
run 0..54 (55 variants — `.invalidCapability = 0` through
`.auditLogCapacityExceeded = 54`), so a label that carried the discriminant
directly would alias `.invalidCapability` with success — the exact
silent-aliasing class this workstream exists to remove, reproduced in its own
design.  seL4 avoids it by numbering `seL4_NoError = 0` and real errors from 1;
we cannot renumber (the discriminants are pinned by the Rust mirror and the
`KernelErrorMatrixSuite` ordering guard), so the label is offset instead:
`errorLabel e = toDiscriminant e + 1`, decoded as `0 → success`,
`n+1 → ofDiscriminant? n` (fail-closed on unknown).  `errorLabel_never_zero` is
the theorem that pins the non-aliasing.

The carrier already exists: `MessageInfo.label` is a 20-bit field documented as
"seL4 convention" (`maxLabel = 2^20 - 1`, mirrored and compile-time-checked in
`sele4n-abi/src/message_info.rs`), and the offset labels occupy 1..55.  No new
register, no new structure.  One inverse is missing and must be authored:
`KernelError.toUInt32` (`Platform/FFI.lean`) is the only Lean-side numeric
map today and it is one-directional — RA.A.5 adds the canonical
`KernelError.toDiscriminant` / `KernelError.ofDiscriminant?` pair (the 55-arm
map moves down to the new module; `toUInt32` becomes its instance so the
discriminant table exists exactly once).

### 3.2 Why the label, and what it costs

The alternative — keep `x0` as status and put values in `x1` — is the x1 route
§1.5 rejects.  The alternative *within* x0 compliance is a dedicated error
register (say `x6`), which is simpler to implement but is not seL4 and buys
nothing: the label is already decoded on every receive path.

The cost is honest and belongs here: **`decode_response` is the single funnel
every `sele4n-sys` wrapper passes through**, so its signature change touches
every wrapper's error handling in one commit.  That is a feature of the design,
not an accident — there is exactly one place to get it right, and RA.D.1 changes
it once.

### 3.3 The staging seam: TCB register context, not a wider FFI return

A syscall must be able to return **six** registers.  Widening
`syscallDispatchFromAbi`'s return type to carry them (`Kernel (UInt64 × …)`)
would thread six values through every dispatch arm and every theorem that names
the entry.

**Decision.**  Return values are **staged in `tcb.registerContext`**, exactly as
arguments already are, and the FFI boundary reads them back out.  The seam
already exists in both directions:

- `writeFfiRegistersToTcb` writes args in (live).
- `readReturnValue` reads `gpr ⟨0⟩` out (live, and already consumed by
  `syscallDispatchFromAbi`).

So the change is to **generalise `readReturnValue` to a register range**
(`readReturnFrame : SystemState → ThreadId → SyscallReturnFrame`) and give the
Lean transitions a way to write into that range.  `syscallDispatchFromAbi`'s
return type changes once, from `Kernel UInt64` to `Kernel SyscallOutcome`
(§3.5's outcome carrying the frame in its `returns` arm), and no dispatch arm
grows a tuple.

This also matches how a real kernel works — the trap handler restores the thread's
register context — which means RA.C.2 is a context restore rather than a special
case bolted onto the SVC path.  Two mechanics discovered against the tree,
recorded here so the implementation does not rediscover them:

- **The boundary read is shape-driven.**  For a `.unit`-shaped syscall nothing
  stages, and blindly reading `gpr ⟨0⟩..⟨5⟩` back out would return the caller's
  own staged *arguments* — the §1.2 defect, reproduced.  The boundary therefore
  composes the frame per `syscallReturnShape`: `.unit` → the zero frame
  (constructed, not read), value shapes → `readReturnFrame` on the staged
  registers.  `dispatchArm_matches_returnShape` (RA.B.8) is what makes the read
  side safe: a value-shaped arm provably staged before the boundary reads.

- **How six registers cross the C boundary.**  `lean_syscall_dispatch_cross_core`
  returns one `u64` and the FFI deliberately carries no `lean_object*`; a
  six-word C struct return is not something Lean's `@[export]` emits.  The frame
  crosses through a **per-core return-frame mailbox** — a Rust-side
  `ffi_syscall_return_frame(x0..x5)` writer called from the export seam, read
  back by `dispatch_svc` inside the same `with_kernel_entry` critical section —
  which is the `ShootdownOpMailbox` publish pattern SM7.B already established
  for exactly this shape of problem (the export's scalar return becomes the
  §3.5 outcome tag).  The new `@[extern]` must be **called only from
  `SyscallDispatchEntry.lean`**: host executables link `Platform/FFI.lean`'s
  object (the suites call `syscallDispatchFromAbi` directly), and an extern
  call reachable from host-linked code is an unresolved symbol at link time —
  the same link-gating constraint that keeps `icMaintenanceBroadcast` out of
  `syscallDispatchInner` (v0.32.98).  `syscallDispatchFromAbi` itself stays
  pure, so the suites keep testing the full convention without the FFI.

### 3.4 Which syscall returns what: a total function

Six rounds of review on the SM9 plan established one lesson repeatedly: a
**hand-maintained list plus a completeness theorem cannot force a new member to
join it**, because the theorem stays true when a new arm joins neither the list
nor the classification.  It was learned three times there (`ReadableStructure`,
`ContentFlowSite`, `declassificationSyscalls`) and it applies here directly.

**Decision.**  `syscallReturnShape : SyscallId → ReturnShape` is a **total
function** over the `SyscallId` enumeration the ABI already forces to be
complete, with `ReturnShape` naming what each syscall puts in `x0` and the
message registers.  A new syscall is a missing case at elaboration, not a
silent omission.  `syscallReturnShape_total` is the theorem;
`returnShape_list_gate_insufficient` keeps the refuted design refuted.

The shape vocabulary, corrected against the actual surface (the first draft
said `unit / badge / slot / message n` and both of the last two were wrong):

- **`.unit`** — `x0 = 0`, no message.  26 of 31 syscalls.
- **`.badge`** — `x0` = full-width badge, no message registers
  (`.notificationWait`).
- **`.word`** — `x0` = a queried scalar (`.serviceQuery`'s resolved
  `ServiceId`; SM9.A's `.auditRead` selected word and `.auditDrain` new
  length join here).  Distinct from `.badge` because the Rust conformance
  layer types them differently (`Badge` vs `u64`), not because the frames
  differ.
- **`.message`** — `x0` = badge, `x1` = `MessageInfo`, `x2`-`x5` = message
  registers (`.receive`, `.call`, `.replyRecv`).

There is **no `slot` shape**: RA.B.7's parenthetical already establishes that
`cspaceMint` / `cspaceCopy` and the retype family select their own destination
slot in their arguments, so no syscall returns one — and a shape with no
inhabiting syscall is a hand-maintained fiction of exactly the kind §3.4
forbids.  And `message` carries **no static arity**: a receive's length is
dynamic (0..4 inline), so the length rides the returned `MessageInfo` where
seL4 puts it, bounded by the window theorem rather than indexed by a type
parameter.

The conformance layer then checks the Rust mirror against it per-variant, in the
idiom `SyscallId` conformance already uses.

### 3.5 A blocking syscall has no return frame yet

The design above reads a return frame at the FFI boundary, for the thread that
made the call.  **That is wrong for a syscall that blocks**, and
`.notificationWait` is the case that matters: in the wait-before-signal ordering
`notificationWaitOnCore` blocks the caller, deschedules it
(`removeRunnableOnCore`) and returns `.ok none` — the badge does not exist yet,
and by the time it does the caller is not the current thread.  No amount of
return-frame plumbing at the entry can conjure a value that has not been produced.

**Decision.**  A syscall's outcome is `SyscallOutcome`, either
**`returns frame`** or **`blocks`**, and the FFI boundary writes a frame only in
the first case.  For the second:

- the **unblocking** transition writes the return frame into the blocked
  thread's `registerContext` — which is where `storeTcbIpcStateAndMessage`'s
  badge should have been going all along, and is exactly the staging seam §3.3
  already establishes;
- delivery happens when the scheduler **restores that thread's context**.

This costs an honest sequencing statement rather than a hidden assumption.  The
context-restore seam is not live — `restore_context` exists in the assembly
macros and the trap layer has a recorded dead-code note about it, and it is
SM10.E work.  So WS-RA's reach splits, and the acceptance gate (§8) splits with
it:

| Ordering | WS-RA delivers |
|---|---|
| Non-blocking (signal-before-wait; every query; every `Unit` return) | **Complete** — value produced, staged and returned at the boundary |
| Blocking (wait-before-signal, `.receive` on an empty endpoint, `.call` always, `.send` with no receiver) | **Staged** — the unblocking transition writes the waiter's frame, and `blockedReturn_staged_in_waiter_frame` proves it; the final hop is the SM10.E context restore |

Claiming "both orderings" without this split would be the same shape of
overstatement this workstream exists to remove: a documented behaviour that the
code does not have.  RA.B.5a and RA.C.9 carry the work; the SM10.E dependency is
recorded in §9 rather than discovered during SM10.

Four facts sharpen the split, each verified against the dispatch arms rather
than assumed:

- **`SyscallOutcome` is computed from the post-state, not from the syscall
  id.**  Whether `.notificationWait` blocks depends on `pendingBadge`; whether
  `.receive` blocks depends on the sender queue; `.send` blocks when no
  receiver waits (`endpointSendDual`'s stash arm parks the sender
  `blockedOnSend`).  So the outcome is decided at the boundary by the caller's
  post-state IPC state — `blocks` iff the caller left the transition
  IPC-blocked — and `syscallReturnShape` classifies the *frame* a returning
  syscall carries, not whether this execution returned.  (A self-`.tcbSuspend`
  deschedules without IPC-blocking; its outcome is `returns` with the unit
  frame, which is also the value the thread should observe when later resumed.)
- **`.call` never returns at the boundary.**  A successful call leaves the
  caller `blockedOnReply` in *every* ordering (`endpointCallOnCore` blocks the
  caller whether or not a receiver was waiting), so its `.message` frame is
  always delivered by the **reply** path's staging (`endpointReplyOnCore`), and
  §1.3's row for `.call` is satisfied entirely through RA.B.5b.
- **The unblocking transitions, enumerated.**  Staging must land at every site
  that today delivers via `pendingMessage` (or fails to deliver at all), and
  the list is finite and known: `notificationWaitOnCore`'s pending-badge arm
  (the caller itself — delivers *nothing* today, not even a `pendingMessage`);
  `notificationSignalOnCore`'s waiter-wake arm; `notificationSignalBoundOnCore`'s
  bound-TCB arm (`storeTcbReceiveComplete`); `endpointSendDual` /
  `endpointSendDualOnCore`'s rendezvous arm (receiver); `endpointReceiveDual` /
  `endpointReceiveDualOnCore`'s consume-queued-sender arm (delivers to the
  *receiver*, and additionally unblocks a plain **sender**, whose unit frame
  must be staged too — the one case the first draft missed); `endpointCallOnCore`'s
  receiver-present arm (receiver); `endpointReplyOnCore` (the woken caller);
  and `endpointReplyRecvOnCore` (both legs compose the previous two).
- **Cancellation stages nothing, and that is registered debt, not an
  accident.**  `cancelIpcBlocking` / `timeoutThread` forcibly unblock a waiter
  with no value to deliver; the honest frame there is an *error* frame, and
  choosing its error (seL4 restarts the thread; we have no restart) is a
  design question this workstream does not need to answer because delivery is
  SM10.E-gated either way.  Recorded as a named obligation in §9: before
  `contextRestoreSeamLive` flips, the cancellation and timeout unblock paths
  must stage an error frame, or a cancelled waiter resumes reading its stale
  staged arguments as a return value.

### 3.6 An ABI break needs a structural guard, not a changelog note

Kernel and userspace ship from one tree, so an atomic flip is available and no
compatibility shim is warranted.  But a **half-migrated** system does not fail
loudly: it silently reinterprets registers, which is exactly the failure mode
§1.2 describes.

**Decision.**  A compile-time `SYSCALL_ABI_VERSION` constant, mirrored in Lean
and Rust and checked by the existing conformance suite, so a half-migrated tree
fails the build rather than mis-decoding at runtime.  This is the same mechanism
`SyscallId` conformance already uses, extended to the return convention.

### 3.7 What this workstream does *not* change

Recorded so scope cannot drift:

- **Argument passing** is untouched — `writeFfiRegistersToTcb`, the `x7` syscall
  number, `x0` as cap pointer *on entry*.  Only the return direction moves.
- **`KernelError` discriminants** keep their numeric values; only their carrier
  moves from `x0` to the label (offset by one, §3.1).
- **The IPC buffer path** (`ipcBufferReadMr`) is unrelated: it is how *arguments*
  beyond the register file are read, not how results are returned.  The dual
  consequence is a **bounded return window**: the frame delivers at most 4
  message registers (`x2`-`x5`), and a delivered `IpcMessage` whose
  `registers.size > 4` keeps its full payload in `pendingMessage` while the
  frame reports the inline window.  seL4 writes the receiver's IPC buffer for
  MRs beyond the hardware registers; that write path does not exist here and
  building it is out of scope.  Not theoretical debt to hide: the live
  `sele4n-sys` surface sends at most 4 MRs (`IpcMessage.regs : [u64; 4]`), so
  no wrapper-reachable message truncates today — but the model admits up to
  120, so the window is stated as a theorem
  (`returnFrame_message_window`) and registered in §9.
- **`DispatchError`** stays the Rust-internal dispatch-layer type; only its
  encoding across the FFI boundary changes — which also retires the documented
  discriminant collision (`svc_dispatch.rs`'s `DispatchError`: `InvalidSyscallId = 7`
  colliding with `EndpointStateMismatch`, `InvalidArgument = 6` with
  `SchedulerInvariantViolation`, deferred there to "a post-1.0 ABI cleanup").
  This is that cleanup: the prefilter rejections stop writing raw discriminants
  into `x0` and ride the label as `KernelError.invalidSyscallNumber` /
  `.invalidSyscallArgument` like every other error.
- **`syscallEntry` / `syscallEntryChecked` stay `Kernel Unit`.**  The frame is
  staged in state and read at the FFI boundary, so the kernel-side entry types
  — and the ~35 `dispatchWithCap*_delegates` theorems plus the
  `checkedDispatch_*_eq_unchecked` equivalence family that quantify over them —
  keep their shapes.  Arms that stage do so *inside* their existing
  `Kernel Unit` bodies.
- **One deletion, not a migration**: the vestigial `syscallDispatchInner`
  (`@[export syscall_dispatch_inner]`, `FFI.lean`) has no Rust caller
  (the extern was flipped to `lean_syscall_dispatch_cross_core` at v0.31.67;
  `rust/` declares no `syscall_dispatch_inner`), and it is the only consumer
  of `encodeOk` / `encodeError` besides the live seam.  The acceptance gate
  says the bit-63 protocol is *gone*; a dead export still speaking it would be
  a half-migrated artifact.  Its planned SM10.E removal moves here, into the
  flip PR, together with its `suspendThreadInner` sibling's export note being
  left alone (`suspend_thread_cross_core` uses the bare-discriminant `u32`
  convention, which is a kernel-internal seam, not the userspace syscall ABI —
  out of scope).

## 4. Detailed sub-task breakdown

Sizes: **T** trivial, **S** small, **M** medium, **L** large, **XL** very large.

### RA.A — The convention, modelled (3-4 PRs, 8 sub-tasks)

Pure model work.  Nothing live changes; the old path keeps running until RA.C.

The module lands as `SeLe4n/Kernel/Architecture/SyscallReturn.lean` — beside
`RegisterDecode.lean` / `SyscallArgDecode.lean`, whose argument-direction twin
it is — importing `Model.State` only, so `Platform/FFI.lean` and `Kernel/API.lean`
both sit above it without a cycle.  (The first draft said
`Platform/SyscallReturn.lean`; the decode layer's home is the honest one.)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.A.1 | `ReturnShape` inductive (`unit` / `badge` / `word` / `message`, §3.4 — no `slot`, no static arity) + `Repr`/`DecidableEq` | new production leaf `Kernel/Architecture/SyscallReturn.lean` | S |
| RA.A.2 | **`syscallReturnShape : SyscallId → ReturnShape`** — a *total* function (§3.4), with `syscallReturnShape_total` and `returnShape_list_gate_insufficient` | same | M |
| RA.A.3 | `SyscallReturnFrame` (the six-register result) + `zero` (the unit/success frame) + accessors; `returnFrame_unit_is_zero`; `returnFrameOfMessage : IpcMessage → SyscallReturnFrame` — the **single** place a delivered message becomes a frame (badge → `x0`, synthesized `MessageInfo` → `x1`, inline window → `x2`-`x5`), since `IpcMessage` carries no `MessageInfo` and every delivery site must synthesize the same way; `returnFrame_message_window` (§3.7) | same | M |
| RA.A.4 | `SyscallOutcome` (`returns frame` / `blocks`) — moved here from RA.B.5a so RA.B.3's signature change lands against the finished type; plus the boundary composer `frameForShape` (`.unit` → zero frame *constructed*, value shapes → read staged registers — §3.3's shape-driven read) | same | M |
| RA.A.5 | Error carriage: `KernelError.toDiscriminant` / `KernelError.ofDiscriminant?` (the canonical pair — the 55-arm map moves here; `Platform.FFI.KernelError.toUInt32` becomes its instance so the table exists once), `errorLabel e = toDiscriminant e + 1`, `errorFrame : KernelError → SyscallReturnFrame`, `errorLabel_roundtrip` both ways, `errorLabel_never_zero` (§3.1 — the non-aliasing), and `errorLabel_zero_iff_success` on the decode side (label 0 ⇔ no error) | same | M |
| RA.A.6 | `kernelErrorFitsLabel` — all 55 offset labels (1..55) inside `MessageInfo.maxLabel`, by `decide`; the negative that an over-wide label is rejected by `MessageInfo.decode` (which fail-closes on bits ≥ 29), so the bound is load-bearing | same | S |
| RA.A.7 | `SYSCALL_ABI_VERSION` (§3.6) + the Lean half of the conformance pin | same | T |
| RA.A.8 | **Retirement of the bit-63 protocol, stated**: `encodeOk_not_injective_on_badges` (the theorem that motivates the change — two valid badges differing only at bit 63 collide under the old encoding, since `encodeOk` masks it), kept as a negative so the protocol cannot return | `Platform/FFI.lean` (while `encodeOk` still exists), moving to `SyscallReturn.lean` as a historical statement at the flip | S |

### RA.B — The Lean return path (3-4 PRs, 12 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.B.1 | `writeReturnFrameToTcb` — the dual of `writeFfiRegistersToTcb`, staging results into `tcb.registerContext` via a pure `TCB.withReturnFrame : TCB → SyscallReturnFrame → TCB` record update (one simp surface for every downstream proof: `ipcState`, queue links, `pendingMessage`, every non-`registerContext` field pinned unchanged); frame lemmas (`_objects_eq` off the target, `_scheduler_eq`, `_machine_eq`).  **Deliberately does not touch `machine.regs` / `regsOnCore`** — that mirror is already stale for x6, x8..x30 after `writeFfiRegistersToTcb` (the `ContextRestoreSeam` note), the SM10.E outgoing-frame save is the registered closure for the whole staleness class, and keeping the write out of `machine` is what makes RA.B.10's projection theorem hold | `Platform/FFI.lean` | M |
| RA.B.2 | `readReturnFrame` generalising `readReturnValue` to the register range; `readReturnFrame_writeReturnFrame` round trip; `readReturnValue` retained as its `x0` instance so existing theorems and the two Tier-3 anchors on it stand | same | M |
| RA.B.3 | `syscallDispatchFromAbi : … → Kernel SyscallOutcome` — the signature change.  The theorems that name it, enumerated (the first draft said "6"; the true set is **five `unfold`-based theorems in `FFI.lean`** — `_total`, `_ok_of_syscallEntryChecked_ok`, `_error_of_syscallEntryChecked_error`, `_illegalState_when_no_current`, `_abiMismatch_rejected` — **plus two in `SyscallDispatchEntry.lean`**: `vacatedCore_next_syscall_rejected`, which applies the illegal-state theorem at the entry, and the `rfl`-pinned `syscallDispatchCrossCoreEntry_def` body marker, which breaks on any entry change *by design* and is restated with it in RA.B.9).  Error arms return `.returns (errorFrame ke)` with the state exactly as today (`stRegs` / `st`), so the error path stays state-preserving | same | L |
| RA.B.4 | The "an error changes nothing" proofs — **verified to survive, not re-proven**.  `syscallEntry_error_perCore_NI` and `syscallEntry_error_preserves_proofLayerInvariantBundle` are trivial (`rfl` / `hInv`) precisely because the error path returns the pre-state unchanged, and RA.B.3's design keeps it so (error frames are *computed at the boundary*, never staged into the TCB).  The work here is the negative that pins the design: `syscallDispatchFromAbi_error_stages_no_frame` — on every error arm the returned state carries no return-frame write | `Platform/FFI.lean` | S |
| RA.B.5 | **`.notificationWait`** returns its badge — the SM9.C.0 defect, closed here.  The pending-badge arm of `notificationWaitOnCore` (which today runs `storeTcbIpcState` and delivers *nothing*) stages the badge frame into the caller's `registerContext`; both live arms (`dispatchWithCap` / `dispatchWithCapChecked` in `API.lean`) keep their `Kernel Unit` shape per §3.7 | `IPC/CrossCore/NotificationSignal.lean` | M |
| RA.B.5a | Outcome classification at the boundary: `syscallOutcomeOf` decides `blocks` from the caller's post-state IPC state (§3.5 — outcome is state-dependent, not id-dependent); `blockingArm_returns_no_frame`; `frameForShape` wired so a `.unit` syscall's frame is constructed, never read (§3.3) | `Platform/FFI.lean`, `Kernel/Architecture/SyscallReturn.lean` | M |
| RA.B.5b | **LANDED v0.33.38 — at the arms, not the transitions (see the landing record; the store-sibling mechanism below was not needed).**  The **unblocking transitions stage the blocked waiter's frame** — scoped, after the implementation split below, to the *blocked-waiter* half only: `notificationSignalOnCore` waiter arm, `notificationSignalBoundOnCore` bound arm, `endpointSendDual`(+`OnCore`) rendezvous arm (the blocked receiver), `endpointReceiveDual`(+`OnCore`)'s unblocked plain **sender**'s unit frame, `endpointCallOnCore` receiver arm, `endpointReplyOnCore` woken-caller arm.  Mechanism: new store siblings (`storeTcbReadyWithFrame`-shaped) that write `ipcState` + `pendingMessage` + `registerContext := stage (returnFrameOfMessage msg)` in **one** object write, so each site is a one-call swap and the frame-lemma family (`_objects_ne`, `_scheduler_eq`, `_ipcState_eq`, `_preserves_ipcInvariant`, …) is proven once per sibling, not once per site.  The per-site invariant-preservation re-proofs (the `Signal.lean` / `EndpointReply.lean` / `Transport.lean` families that unfold the old helpers) are the honest bulk of the XL.  **Rides with its consumer**: a blocked waiter's staged frame is delivered only by the SM10.E context restore (§3.5), so this half lands with the restore seam's workstream slice rather than blocking the flip — recorded as the same named obligation §9 already carries | `IPC/Operations/Endpoint.lean` (the siblings), `IPC/CrossCore/{NotificationSignal,NotificationBind,EndpointSend,EndpointReply,EndpointCall}.lean`, `IPC/DualQueue/Transport.lean` | XL |
| RA.B.6 | **`.receive` / `.replyRecv` / the immediate half generally — staged at the ARMS** (implemented; a design sharpening over the first draft, which routed everything through RA.B.5b's delivery sites): every immediate value is already in the arm's hands (`notificationWaitCrossCoreDispatch` returns `.ok (some badge)` and the arm was discarding it) or in the caller's own `pendingMessage` (the receive/replyRecv consume paths deliver there), so `stageDeliveredMessage` — guarded on the caller's post-state being `.ready`, since a blocked caller's `pendingMessage` may be stale — closes the immediate half while touching **zero** IPC transitions and zero of the ~1900-reference invariant surface.  Theorem fallout was exactly two: `dispatchWithCapChecked_receive_delegates` and the `syscallDelegates` `.receive` obligation gain the staging in their pinned RHS; the checked/unchecked equivalence family survives because both arms change in lockstep | `API.lean` | M |
| RA.B.7 | **`.serviceQuery`** returns its resolved service — `x0` = the `ServiceRegistration.sid` the arm currently discards (the `.serviceQuery` arm of `dispatchCapabilityOnly` in `API.lean`); staged in the arm via `writeReturnFrameToTcb`.  (`.cspaceMint`, `.cspaceCopy` and the retype family are deliberately **not** here: their decoded arguments already carry the destination slot, the kernel allocates no slot of its own, and inventing a result for them would be adding an ABI value rather than repairing a missing one — §3.7's boundary) | `API.lean` | M |
| RA.B.8 | **LANDED v0.33.38 (see the landing record — the unit half is structural via `frameForShape_unit`, the value half per-arm).**  The classification and the arms cannot disagree: `dispatchArm_matches_returnShape` — for every `.unit`-shaped syscall the dispatch arm leaves the caller's staged frame untouched (so the constructed zero frame is honest), and for every value-shaped syscall the success path staged (so the read is of fresh data, not the caller's arguments).  Driven per-variant by `syscallReturnShape` | `API.lean` | L |
| RA.B.9 | `syscallDispatchCrossCoreEntry` threads the outcome: mailbox write via the new link-gated `@[extern]` (§3.3), outcome tag as the export's scalar return; `syscallDispatchCrossCoreEntry_def` and `vacatedCore_next_syscall_rejected` restated | `Kernel/SyscallDispatchEntry.lean`, `Platform/FFI.lean` (extern decl) | M |
| RA.B.10 | Information flow — **the premise checked against the tree first**: `projectKernelObject` already strips `registerContext` from every projected TCB (WS-H12c, `projectKernelObject` in `InformationFlow/Projection.lean`), so the first draft's "an observer that can see the caller sees its register context" was wrong and the **blanket theorem is provable**: `writeReturnFrameToTcb_preserves_projection` (and `_preserves_projectionOnCore` / `lowEquivalent_smp`), for *every* observer.  What remains and is stated honestly: (a) the caller-visible content channel is the hardware `TrapFrame` write at the boundary — outside `ObservableState`, the same class as the registered covert channels, and by construction data the caller's own syscall produced; (b) the *authority* for each returned value is each receive/wait arm's existing flow gate (`endpointFlowGate`, the SM6.B notification→waiter gate), and per-value theorems name that: a staged badge reaches only a thread the gate admitted.  RA.B.5b's staging sites each carry their projection-preservation lemma via (a)'s blanket | `InformationFlow/Invariant/Operations.lean`, `Platform/FFI.lean` | M |

### RA.C — The Rust boundary (2-3 PRs, 9 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.C.1 | The frame crossing: `ffi_syscall_return_frame` per-core mailbox (§3.3, the `ShootdownOpMailbox` pattern) + `dispatch_svc` returning `Frame` / `Blocked` assembled from the export's outcome-tag return and the mailbox, read inside the same `with_kernel_entry` critical section; the `#[cfg(test)]` stub flipped to the new convention in lockstep (that stub is what `trap.rs`'s `handle_sync_reads_esr_from_frame` assertion drives through) | `rust/sele4n-hal/src/{svc_dispatch,ffi}.rs` | M |
| RA.C.2 | **Trap-frame writeback** — `set_x0`…`set_x5` from the returned frame, as a context restore (§3.3).  `set_x1` stops being dead code; **`set_x2`..`set_x5` do not exist and are added** beside it.  The prefilter rejections (`InvalidSyscallId` / `InvalidArgument`) stop writing raw `DispatchError` discriminants into `x0` and write label-encoded error frames (`InvalidSyscallNumber` / `InvalidSyscallArgument`) — closing the documented discriminant collision (§3.7) | `rust/sele4n-hal/src/trap.rs` | M |
| RA.C.3 | Retire the bit-63 decode in `dispatch_svc`; errors now sourced from the label − 1.  **Fix the second MessageInfo layout while here**: `SyscallArgs::message_length()` reads `msg_info & 0x0FFF` under a doc comment claiming `length[11:0] / extraCaps[13:12] / label[63:14]` — contradicting the abi crate, the Lean model and the conformance vectors (all `length[6:0] / extraCaps[8:7] / label[28:9]`), so any request with a nonzero label over-reads its length (harmless today only because the authoritative Lean decode re-validates fail-closed; this workstream makes `x1` layouts load-bearing in both directions).  Reads `& 0x7F`; the `message_length` unit test's 14-bit fixture corrected | `rust/sele4n-hal/src/svc_dispatch.rs` | M |
| RA.C.4 | `SYSCALL_ABI_VERSION` Rust mirror — in `sele4n-types` (the crate the abi crate re-exports and the HAL's dev-dep mirror tests can reach), with conformance pins asserting every mirror equals the same literal so a half-bumped tree fails its own suite (§3.6) | `rust/sele4n-types/src/lib.rs`, `rust/sele4n-abi/tests/conformance.rs` | S |
| RA.C.5 | `decode_response` rewritten to the §3.1 layout: error from the **label** (`0` success; `n+1` → `from_u32(n)`; unknown → `UnknownKernelError`, fail-closed), `x0` a full-width value, `x2`-`x5` real message registers; the non-aarch64 `raw_syscall` mock re-encoded to the new convention (it currently writes its error into `regs[0]`) | `rust/sele4n-abi/src/{decode,trap}.rs` | L |
| RA.C.6 | `SyscallResponse` reshaped — `x1_raw`'s context-dependent dual meaning (badge *or* msg_info) collapses, since the badge moves to `x0`; `badge()` reads `x0`, `msg_info()` reads the decoded `x1`; the vestigial always-`None` `error` field (errors ride `Err`) dropped rather than carried | `rust/sele4n-abi/src/decode.rs` | M |
| RA.C.7 | The `regs[0] > u32::MAX` guard is retired with the convention that motivated it, and its replacement — the fail-closed `MessageInfo::decode` width check on `x1` — takes its place with the same posture | same | S |
| RA.C.8 | Rust-side unit tests for the new decode, including the **regression witness** that a nonzero `x0` is a value and not an error; two stale pins corrected while the files are open (`dispatch_error_kernel_variant_…` iterates `0..=51` against a real max of 54; `test_rust_conformance.sh --dump`'s `KE-003` row cites `from_u32(38) = None` against a live boundary of 55) | `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/src/decode.rs`, `scripts/test_rust_conformance.sh` | M |
| RA.C.9 | The blocked-return handoff at the boundary: a `blocks` outcome carries **no return frame** for the caller (a distinct `dispatch_svc` variant, not an error), and the SM10.E context-restore seam is where the staged frame is delivered — documented as the dependency it is, with the trap-layer hook shaped now so SM10.E wires rather than redesigns.  **Sharpened by the PR #866 review** (see the review paragraph above §1): until the seam flips the hardware resumes the blocked caller anyway, so the `Blocked` arm poisons the frame with the fail-closed `blocked_resume_sentinel_regs()` rather than leaving the caller's stale request registers to decode as a false success | `rust/sele4n-hal/src/{trap,svc_dispatch}.rs` | M |

### RA.D — Wrappers and conformance (2 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.D.1 | Every `sele4n-sys` wrapper's error handling, through the single `decode_response` funnel (§3.2).  **Three pre-existing prefilter mismatches fixed in the same pass**, since the flip PR owns both sides of them: `cspace_mint` sends `msg_info.length = 4` against `min_inline_args = 5`, `cspace_copy` and `cspace_move` send 2 against 4 — each is rejected `InvalidArgument` by `dispatch_svc` before reaching the kernel, so those wrappers are unreachable on hardware today; the `min_inline_args` table entries are reconciled with the Lean per-syscall decoders (which are the authority) and a conformance test pins wrapper length ≥ table minimum for every wrapper | `rust/sele4n-sys/src/*.rs`, `rust/sele4n-hal/src/svc_dispatch.rs` | L |
| RA.D.2 | `notification_wait` returns a **real** badge (from `x0`, not `x1`); `endpoint_receive` / `reply_recv` / `endpoint_reply_recv_checked` return real badges and message registers | `rust/sele4n-sys/src/ipc.rs` | M |
| RA.D.3 | `service_query` returns its resolved `ServiceId` word instead of an opaque `SyscallResponse`; `cspace_mint` and the retype family keep their `Unit` shape, since they select their own destination slot | `rust/sele4n-sys/src/{service,cspace,lifecycle}.rs` | M |
| RA.D.4 | Per-variant conformance: every `SyscallId`'s `ReturnShape` checked against the Rust mirror, driven by RA.A.2's total function; plus the response-side `verify_regs` mirror helper the encode-only conformance idiom lacks | `rust/sele4n-abi/tests/conformance.rs` | M |
| RA.D.5 | Round-trip conformance: encode a return frame under the Lean layout rules, decode with the real `decode_response`, for each shape and for the label offset (a Lean-side mirror of the Rust decoder rides in `SyscallReturnAbiSuite`, the `AbiRoundtripSuite` idiom in the return direction) | same | M |
| RA.D.6 | Doc comments corrected across the wrapper surface — several currently describe returns the ABI never delivered (`notification_wait`'s "returns the accumulated badge" being the one that started this) | `rust/sele4n-sys/src/*.rs` | S |

### RA.E — Tests, fixtures, closure (2-3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.E.1 | **The observable-failure test, written first** (§1.2): a harness-level round trip — `syscallDispatchFromAbi` on a successful syscall with a nonzero cap pointer, decoded by an in-suite Lean mirror of `decode_response` (the `AbiRoundtripSuite` simulate-the-Rust-side idiom) — that today decodes the caller's cap pointer as a `KernelError`.  Realisation, since CI cannot carry a red test: the suite lands **asserting the defect** as a pre-migration witness (the repo's load-bearing-negative idiom — "a successful syscall's word decodes as an error, which is the §1.2 defect; the flip must break this assertion"), and the flip PR inverts those assertions to the correct convention in the same commit that changes the behaviour.  Both trees are green; the flip provably moved the observable | new `tests/SyscallReturnAbiSuite.lean` | L |
| RA.E.2 | Per-shape acceptance: badge round trip (signal-before-wait **and** wait-before-signal, the SM9.C.0 orderings — the second asserting the *staged* frame per §3.5), word return (`.serviceQuery`), message-register return, `Unit` returning zero with a nonzero incoming cap pointer (the load-bearing case), and the blocked-outcome witness (`.call` never returns at the boundary) | same | XL |
| RA.E.3 | Error carriage: every `KernelError` discriminant survives the label round trip, by enumeration not by sampling | same | M |
| RA.E.4 | Golden fixture `tests/fixtures/syscall_return_abi.expected` + `.sha256`, in-suite byte-verified; `tests/fixtures/README.md` row | `tests/fixtures/` | M |
| RA.E.5 | Tier-3 anchors: the total-function gate, the retired bit-63 protocol (**negative** anchors — `encodeOk`/`encodeError` must not come back), the ABI version pin | `scripts/test_tier3_invariant_surface.sh` | M |
| RA.E.6 | Documentation sync + closure record: spec, GitBook, `CLAIM_EVIDENCE_INDEX`, `WORKSTREAM_HISTORY`, `CLAUDE.md`/`AGENTS.md`; **correct `readReturnValue`'s docstring** in `Platform/FFI.lean`, whose "documented current behaviour" paragraph is the artefact this workstream removes | spec + docs | M |

## 5. Sequencing and the migration window

The order is forced by one property: **the tree must never sit in a state where
Lean and Rust disagree about the convention**, because that state mis-decodes
silently rather than failing.

1. **RA.A** — model only; nothing live reads it.  Safe to land alone.
2. **RA.B** — Lean writes return frames, but `syscallDispatchFromAbi` still
   encodes the old way at its outermost edge.  Safe to land alone.
3. **RA.B.9 + RA.C.1-C.9 + RA.D.1-D.3 in one PR** — the flip, and it must
   include the **decoder**.  A first draft left `decode_response` and the
   `sele4n-sys` consumers to a following PR; that intermediate tree has the
   kernel on the new convention and userspace still testing `regs[0] != 0`,
   which silently decodes every nonzero badge as an error — precisely the
   half-migrated state §3.6 says must never exist.  The version pin cannot catch
   it either, since both constants would be bumped while the decoder still
   implements the old semantics.  The PR is large by necessity; the alternative
   is a version-selected compatibility decoder, which is more code and more
   surface than the single flip it exists to avoid.
4. **RA.D.4-D.6** — conformance and doc comments, behind the flip, since they
   describe rather than implement the convention.
5. **RA.E** — except RA.E.1, which lands **first**, before RA.A (§1.2: the
   failure must be observable before it is fixed).

## 6. Verification strategy

### 6.1 Per PR

```bash
source ~/.elan/env
lake build <each edited module>
lake exe syscall_return_abi_suite
./scripts/test_rust.sh
./scripts/test_full.sh                       # Tier 0-3
```

### 6.2 For the flip PR specifically

```bash
./scripts/test_rust_conformance.sh           # both mirrors + the version pin
./scripts/test_abi_roundtrip.sh              # the argument-direction round trip, unbroken
lake exe sele4n                              # golden trace
```

(The first draft named a `test_abi_conformance.sh` that does not exist; the two
scripts above are the real conformance surface.)

**The honest trace-fixture story, corrected.**  The first draft claimed the
`[XVAL-002]` line would move at the flip; it will not — that line prints
`SyscallId.count`, which this workstream does not change, and the trace harness
drives `syscallEntry` / `syscallEntryChecked` (both `Kernel Unit`, both staying
so per §3.7) rather than the FFI encode edge, while no existing trace line
prints register-context content.  A byte-identical `main_trace_smoke.expected`
across the flip is therefore the *expected* outcome, not evidence of an
unexercised path — the flip's observable evidence lives where the encode edge
is actually driven: `SyscallReturnAbiSuite`'s inverted pre-migration witnesses
(RA.E.1), the rewritten `SyscallDispatchSuite` SD-002/SD-003 (which pin the
old protocol today and pin the new one after), and the RA.E.4 golden fixture,
which is *new* and exists precisely to make the return path trace-visible.
If the smoke trace does move, each moved line must trace to a staging write
that some printed observable legitimately reads — anything else is a bug the
diff caught.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| A half-migrated tree mis-decodes silently | HIGH | **HIGH** | `SYSCALL_ABI_VERSION` pinned in both mirrors and checked by conformance (§3.6); the flip is one PR (§5) |
| A blocking syscall's return claimed as delivered | MED | **HIGH** | The badge does not exist when a blocking wait returns, and the context-restore seam is SM10.E work.  §3.5 splits the orderings and the acceptance gate states the split rather than claiming both |
| The fix is unobservable because nothing boots | HIGH | MED | RA.E.1 lands **first** and must fail pre-migration; a workstream that cannot demonstrate the failure cannot demonstrate the fix |
| A new syscall omits its return shape | MED | HIGH | `syscallReturnShape` is a **total function** over the ABI's own enumeration (§3.4), not a list — the lesson from six SM9 review rounds |
| Badge ≥ 2^63 aliases an error | — | — | Structurally impossible after the flip: the channels separate, which is the point.  `encodeOk_not_injective_on_badges` (RA.A.8) keeps the old hazard on the record |
| The error-carriage change breaks `DispatchError` consumers | MED | MED | `DispatchError` stays Rust-internal (§3.6); only its FFI encoding moves, and `decode_response` is the single funnel (§3.2) |
| Return values leak across a security boundary | LOW | HIGH | The frame is written into the target's **own** TCB `registerContext`, which WS-H12c already strips from every projected object — `writeReturnFrameToTcb_preserves_projection` (RA.B.10) states it for every observer rather than assuming it, and the *authority* for each value is the arm's existing flow gate |
| Staging into the caller's `registerContext` breaks a register-mirror invariant | LOW | MED | `contextMatchesCurrent` ties `machine.regs` to the current thread's context, and `machine.regsOnCore` is already stale for x6, x8..x30 after `writeFfiRegistersToTcb` (the `ContextRestoreSeam` note).  Staging follows the same precedent — TCB only, never `machine` — and the SM10.E outgoing-frame save is the registered closure for the whole mirror-staleness class.  Verified at implementation: the syscall-path preservation bundles do not carry the mirror equality |
| Scope creep into argument passing or the IPC buffer | MED | LOW | §3.6 fixes the boundary explicitly |

## 8. Acceptance gate

- [x] A successful syscall returns a value userspace decodes **as a value**, and
      RA.E.1 — which failed on the pre-migration tree — passes (inverted to
      post-flip assertions in `SyscallReturnAbiSuite` §1 at the flip).
- [x] `notification_wait` returns the badge that was signalled in the
      **signal-before-wait** ordering — delivered end to end (suite §5;
      full-width badge in §6).
- [x] In the **wait-before-signal** ordering the badge is **staged** into the
      waiter's saved frame by the unblocking transition
      (`blockedReturn_staged_in_waiter_frame`), with delivery completing at the
      SM10.E context restore.  Stated as a split rather than claimed as one
      result, because the context-restore seam is not live (§3.5).
      **Landed at v0.33.38** — `SyscallReturnAbiSuite` §9a runs the ordering
      end to end through the live two-core dispatch, with the pre-signal
      stale-args negative control.
- [x] `endpoint_receive` returns real message registers, not the caller's own —
      both orderings: the immediate rendezvous (`stageDeliveredMessage` at the
      arm) and the blocked receiver (staged by the unblocking `.send`/`.call`
      arm, §9b).
- [x] Every `SyscallId` has a `ReturnShape` by construction, and a new syscall
      cannot be added without one (`syscallReturnShape` is a total match;
      `returnShape_list_gate_insufficient` records why a list gate was
      rejected).
- [x] Every `KernelError` discriminant — all 55, `0..54` — round-trips through
      the offset message label (§3.1), by enumeration, and
      `errorLabel_never_zero` pins that no error aliases success.
- [x] `encodeOk` / `encodeError` and the bit-63 protocol are **gone**, with
      Tier-3 negative anchors preventing their return.
- [x] Lean and Rust agree on `SYSCALL_ABI_VERSION`, enforced at build time —
      Lean by a `decide` theorem (`syscallAbiVersion_pinned`, kernel build);
      Rust by a `const` assertion in the HAL's test lane (test compilation,
      the strongest form available under the HAL's zero-runtime-deps mirror
      discipline) plus the abi-crate conformance pin.
- [x] `FFI.lean`'s "documented current behaviour" note is deleted, because the
      behaviour it documents no longer exists.
- [x] Zero `sorry`/`axiom`; Tier 0-3 green; the trace fixture at the flip is
      **byte-identical** (return frames live in `registerContext` and the
      mailbox, neither of which the trace projects — §6.2's honest story),
      with the `[XVAL-002]` variant count the only historical WS-RA-adjacent
      fixture motion (26→31 across the SyscallId growth, none in this cut).

## 9. Cross-references and registered debt

- **Blocks**: [`SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](SMP_DECLASSIFICATION_COMPLETION_PLAN.md)
  SM9.C.0 (the badge defect this closes), and
  [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) SM10.E.
- **Depends on, for one half of one result**: SM10.E's context-restore seam
  (`contextRestoreSeamLive`, `Kernel/Concurrency/ContextRestoreSeam.lean` —
  `false` until SM10.E).  §3.5 splits the blocking orderings out for this
  reason — WS-RA stages the waiter's frame and SM10.E delivers it.  Recorded
  here so SM10 inherits a named obligation rather than discovering one.
- **Registered debt, owner SM10.E — cancellation frames** (§3.5): the
  cancellation and timeout unblock paths (`cancelIpcBlocking`,
  `timeoutThread`) stage no frame; before `contextRestoreSeamLive` flips they
  must stage an error frame, or a cancelled waiter resumes reading its stale
  staged arguments as a return value.
- **Registered debt, no current consumer — the 4-register return window**
  (§3.7): a delivered `IpcMessage` with more than 4 registers returns only the
  inline window in `x2`-`x5`; the receiver-IPC-buffer write path for return
  overflow does not exist.  Unreachable from the live `sele4n-sys` surface
  (its `IpcMessage.regs` is `[u64; 4]`); becomes real work only if a wrapper
  ever grows an overflow send.
- **Consistency note owed to the SM9 plan at closure** (RA.E.6) —
  **DISCHARGED at v0.33.37**: SM9.A's design was written against the
  pre-WS-RA constraint that "the payload is 63 bits, not 64" (`encodeOk`
  masking bit 63) and sized its chunk protocol accordingly.  The SM9 plan's
  §2 dependency entry, §3.3 payload arithmetic, risk row, acceptance gate and
  theorem inventory are re-anchored to the frame convention
  (`auditReadWord_fits_payload` retired before it was built; the chunking
  itself survives for the unbounded-`Nat` reason, which was never about the
  flag).
- **Reference**: seL4 ARM64 syscall convention, libsel4
  `arch/arm/arch64/sel4/sel4_arch/syscalls.h`.
- **The note this workstream removes**: `SeLe4n/Platform/FFI.lean`, the
  `readReturnValue` docstring's "documented current behaviour" paragraph.

## 10. Theorem catalogue

~30 substantive theorems.  Headline set:

- `syscallReturnShape_total` + `returnShape_list_gate_insufficient` (RA.A.2)
- `decodeReturnFrame_encodeReturnFrame` — losslessness at full 64-bit width
  (RA.A.4)
- `errorLabel_roundtrip` + `errorLabel_never_zero` + `errorLabel_zero_iff_success`
  (RA.A.5, §3.1 — the offset carriage and its non-aliasing)
- `kernelErrorFitsLabel` — all 55 offset labels inside the 20-bit field — + the
  fail-closed over-wide negative (RA.A.6)
- `encodeOk_not_injective_on_badges` — the hazard the flip removes, retained as a
  negative (RA.A.8)
- `returnFrame_message_window` — the 4-register inline bound, stated rather than
  implied (RA.A.3, §3.7)
- `readReturnFrame_writeReturnFrame` (RA.B.2)
- `syscallDispatchFromAbi_total` at the new type (RA.B.3)
- `syscallDispatchFromAbi_error_stages_no_frame` — the error path stays
  state-preserving, which is what keeps `syscallEntry_error_perCore_NI` and
  `syscallEntry_error_preserves_proofLayerInvariantBundle` standing (RA.B.4)
- `dispatchArm_matches_returnShape` — the arms and the classification cannot
  disagree (RA.B.8)
- `writeReturnFrameToTcb_preserves_projection` — for **every** observer, since
  WS-H12c already strips `registerContext` from projected TCBs (RA.B.10)
- `blockingArm_returns_no_frame` + `blockedReturn_staged_in_waiter_frame` — a
  blocking syscall has no frame yet, and the unblocking transition stages it
  (RA.B.5a, RA.B.5b, §3.5)
- the per-value authority statements riding each arm's existing flow gate
  (RA.B.10)
- `notificationWait_delivers_badge_signal_first` — the SM9.C.0 closure on the
  non-blocking ordering (RA.B.5, RA.E.2)

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.Architecture.SyscallReturn
lake build SeLe4n.Platform.FFI
lake exe syscall_return_abi_suite
./scripts/test_rust.sh
./scripts/test_rust_conformance.sh
./scripts/test_abi_roundtrip.sh
./scripts/test_full.sh
```
