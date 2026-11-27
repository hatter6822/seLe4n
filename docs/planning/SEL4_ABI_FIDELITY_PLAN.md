# WS-SX — seL4 ABI fidelity

> **Workstream**: WS-SX (the syscall and invocation ABI made seL4's).
> **Status**: **ACTIVE** — registered at `v0.37.19` (this plan, docs only);
> SX1 landed at `v0.37.20`; SX5 landed at `v0.37.31`; SX6 at `v0.37.32`;
> SX7 at `v0.37.33`, which split its remainder into SX8 and SX28–SX31 (D20);
> SX8 at `v0.37.36` (SX8.1 the conformance table, SX8.2 donation and return,
> SX8.3 label 36 and the unbind of a donated holder, D22), which split its own
> remainder into SX9, SX12 and SX25 (D32). The rows after SX8 were renumbered then:
> SX9–SX17 became SX12–SX20. SX9 landed at `v0.37.38` (the two-run theorem, the
> conformance rows, the bind-gate heap steps that SX9.3 substitutes); it added a row, SX10 (the binding-labels invariant,
> D36, D37), and SX10–SX20 became SX11–SX21. SX10 landed at `v0.37.39`, wrapped
> at its validated point (D38: the boot base case, the owner clause, the slot
> toolkit); its remainder became SX11 (blocked threads carry their endpoint's
> label) and SX12 (the equal-binding-labels invariant, completed), and SX11–SX21
> became SX13–SX23; the decisions below cite the new numbers. SX11 landed at
> `v0.37.40` (blocked threads carry their endpoint's label, at boot and across
> every committing entry). When the binding-invariant row started, its reply
> path met the origin redirect, which no clause of the invariant covers; the
> redirect row runs first (D39), so the two rows swapped: the redirect deleted
> is SX12 and the equal-binding-labels invariant completed is SX13. SX12 landed
> at `v0.37.41` (the pop gives the context to the answered caller; the origin
> fields deleted). SX13 landed at `v0.37.42`, wrapped at its validated point
> (D40: the binding grow and the binding-words leaf lemmas); its remainder
> became SX14 (the frame family threaded, the pops as labelled steps), SX17
> (the creating sites) and SX18 (the premise moved, the refusals deleted), and
> SX14–SX23 became SX17–SX26. SX14 landed at `v0.37.43` (the cancel pops to the
> frame's recorded caller, D41), wrapped at its validated point; its remainder
> became SX15 (the binding siblings and the one-slot grow toolkit) and SX16 (the
> frame family threaded, the pops as labelled steps) (D42), and SX15–SX26
> became SX17–SX28. SX15 landed at `v0.37.44` (the binding siblings, the
> finalisation's binding shrink and the one-slot grow toolkit). SX16 landed at
> `v0.37.45` (the frame family threaded with the binding words, the pops as
> labelled steps). SX17 landed at `v0.37.46` (the creating sites' label
> equations proved from their gates and SX11's waiters). SX18 landed at
> `v0.37.47`, wrapped at SX18.1 (D44: the premise moved to the standing
> per-state slot); the notification lend's label check stays until the
> notification waiters' labels are carried (D43); its remainder became SX19
> (the Call lend's refusal deleted, the lend parameter retired), SX20
> (notification label coherence carried) and SX21 (the notification lend's
> check deleted), and SX19–SX28 became SX22–SX31. SX19 landed at
> `v0.37.48` (the Call lend's refusal deleted as unreachable, the lend
> parameter retired). When SX20 started, its measurement found that no carried
> frame keeps what coherence reads, so the records view is extended first
> (D45): SX20 became the records view extended, landed at `v0.37.49`;
> coherence carried became SX21 and the notification lend's check deleted
> SX22, and SX22–SX31 became SX23–SX32. SX21 landed at `v0.37.50` (the
> label part of coherence carried across every committing entry, D46); the
> queue arms' teardown projection, which does not fall out of it, became
> SX22.2. SX22 landed at `v0.37.51`, wrapped at SX22.1 (D47: the notification
> lend's check deleted as unreachable at its four sites); SX22.2's measurement
> found that no carried frame keeps an endpoint queue's links, so its remainder
> became SX23 (the records view extended with the endpoint queue links) and
> SX24 (the endpoint queue links' labels carried, the queue arms' teardown
> projection discharged), and SX23–SX32 became SX25–SX34. SX23 landed at
> `v0.37.52` (the records view extended with the endpoint queue links; their
> writers are endpoint-queue frames, core frames that keep the notification
> queues). SX24 landed at `v0.37.53` (the endpoint queue links'
> labels carried beside the waiters' and the notifications', and the queue
> arms' teardown projection discharged from them: the cancellation's
> non-interference takes no `hTeardownProj`). SX25's measurement put one
> composed ReplyRecv path over all 90 shapes at 6–8 sessions against 3, so it
> was wrapped before the bulk (D48): SX25 keeps the reply leg over the five
> arms and the composed blocking receive, its remainder became SX26 (the
> Send-take leg composed) and SX27 (the Call take, and the composed path's
> acceptance), and SX26–SX34 became SX28–SX36. SX25 landed at `v0.37.54` (one
> in-place reply leg over every reply arm, the composed blocking receive for
> every answer and length under one `_eq`, the held arm reachable in place,
> and the blocking per-arm modules retired). SX26 landed at `v0.37.55` (the
> Send-take leg composed over every reply arm, answer and length under one
> `_eq`, the per-arm take modules retired; the QEMU steps of eight take shapes
> with no scenario to build on carried to SX27.1). SX27's measurement put its
> remaining Call-take shapes at about 4.5–5.5 sessions against 2–3, so it was
> wrapped (D49): SX27 keeps the Call take composed and the composed path's
> acceptance, its remaining QEMU scenarios and the context-holding server's
> measurement became a new SX28, and SX28–SX37 became SX29–SX38. SX27
> landed at `v0.37.56`. SX28's measurement found the context-holding server's
> Call take reachable and allocating on the rendezvous, unlinked and unheld
> arms, with QEMU work beside it, so it was wrapped (D50): SX28 keeps that
> Call take in place (measured at 3.25–4.25 sessions against 2, kept whole)
> and its QEMU steps, the remaining QEMU scenarios became a new SX29, and
> SX29–SX38 became SX30–SX39. During SX28 the general path's table copy was
> traced to the refusal wrappers, and by the owner's ruling (D50, 2026-11-26)
> their sweep became a new SX29, with ReplyRecv moved to seL4's order, and
> SX29–SX39 became SX30–SX40. SX28 landed at `v0.37.57`. SX29's measurement put the sweep at about 17–24
> sessions, so by the owner's ruling (D51, 2026-11-26) SX29 keeps ReplyRecv in
> seL4's order with its legs' checks first, the gate became a new SX30, the
> rest of the sweep became WS-CK after WS-SX, and SX30–SX40 became SX31–SX41.
> SX29 ran past its estimate with the composite still waiting on the owner,
> so it was wrapped at its validated legs (D52): SX29 keeps the legs checks
> first, the composite in seL4's order became a new SX30, and SX30–SX41
> became SX31–SX42. SX29 landed at `v0.37.58`.
> SX30's measurement found that the composite answers its caller last, so
> SX30 was split (D53): SX30 moves the answer into the reply step, the
> refusals in seL4's order became a new SX31, and SX31–SX42 became SX32–SX43.
> SX30 was wrapped again (D54): SX30 lands the commutation toolkit and the
> answer-first equality, the switch became a new SX31, and SX31–SX43 became
> SX32–SX44.
> SX30 was wrapped at its toolkit (D55): the rest of the toolkit and the
> answer-first equality became a new SX31, and SX31–SX44 became SX32–SX45.
> SX30 landed at `v0.37.59`.
> SX33 was wrapped at its validated pieces (D61): the refusal-carrying
> composite and its wrappers became a new SX34, and SX34–SX45 became
> SX35–SX46. SX33 landed at `v0.37.62`.
> SX34 found ReplyRecv's receive capability resolved before the reply (D63):
> its fix became a new SX35, and SX35–SX46 became SX36–SX47.
> SX34 ran past its stop line, so it was wrapped at its validated point (D64):
> the install checked first and the C bound became a new SX35, and SX35–SX47
> became SX36–SX48. SX34 landed at `v0.37.63`.
> **Baseline**: the tree at `v0.37.18` (WS-UC UC5). Every `file:line` below was
> read against it.
> **Rows**: SX1–SX48, numbered in the order they are implemented, one PR each.
> Each row consumes only lower-numbered rows. A row that changes a transition
> carries the proofs that cover it. No two rows run in parallel.
> **Decisions**: D1–D32, D34, D36–D64 (§3). D1–D17 are each **default taken; owner card open**;
> D7 follows the owner's standing rule (implement seL4's behaviour, never defer
> it). D18–D21 were decided by the owner when SX7 closed; D22 when SX8 started;
> D23–D32 during SX8; D34 when SX9 started; D36 and D37 during SX9; D38 during SX10; D39 when the binding-invariant row
> started; D40 during SX13 (confirmed by the owner's merge of PR #1101); D41 and D42 during SX14
> (each confirmed by the owner, 2026-11-24); D43 and D44 during SX18 (the owner's,
> 2026-11-24); D45 during SX20 (the owner's, 2026-11-24); D46 during SX21
> (default taken, 2026-11-25); D47 during SX22 (SX22's wrap under the owner's D32 rule,
> 2026-11-25); D48 during SX25 (SX25's wrap under the same rule, 2026-11-25); D49 during
> SX27 (SX27's wrap under the same rule, 2026-11-25); D50 during SX28 (SX28's
> wrap under the same rule, and the owner's ruling, 2026-11-26); D51 during
> SX29 (the owner's rulings on its measurement, 2026-11-26); D52 during SX29
> (SX29's wrap under the owner's D32 rule, 2026-11-26); D53–D60 during SX30–SX33;
> D61 during SX33 (SX33's wrap under the owner's D32 rule, 2026-11-26); D62 and
> D63 during SX34 (the coordinator's rulings, 2026-11-27); D64 during SX34
> (SX34's wrap under the owner's D32 rule, 2026-11-27).
> **Supersedes**: the "Next PR" scope in
> `docs/agent_guide/WORKSTREAM_CONTEXT.md` (the root task's boot IPC buffer
> and the guard in the capability with `CNode_Mutate`). Both are rows here
> (SX5, SX2 and SX44). Neither was debt, and neither is now.

## 1. The problem

The kernel's transitions follow seL4. Its ABI does not, in seven places.

- **Errors carry no data.** `KernelError` is a 61-code enum
  (`SeLe4n/Model/KernelError.lean:54`). An error frame is the label alone,
  with length 0 (`SeLe4n/Kernel/Architecture/SyscallReturn.lean:1514`). seL4
  returns a payload in the message registers (`setMRs_syscall_error`,
  `src/object/tcb.c:2091`; `setMRs_lookup_failure`, `src/api/faults.c:29`).
- **Lookups report no lookup fault.**
  - The resolver (`resolveCapAddress`, `SeLe4n/Kernel/Capability/Operations.lean:197`)
    answers `illegalState`, `invalidCapability` or `objectNotFound`.
  - It never stops at a non-CNode capability.
  - It resolves at the root CNode's `depth`, not at 64 (`SeLe4n/Platform/FFI.lean:3085`).
  - UC4 added a second, CNode-only walk beside it (`resolveCNodeOpAddress`, `:328`).
  - seL4 has one resolver: `resolveAddressBits` (`src/kernel/cspace.c:126`).
- **The guard is in the object.** `CNode` holds `guardWidth`, `guardValue` and
  `depth` (`SeLe4n/Model/Object/Types.lean:4210`). seL4's `cnode_cap` holds the
  guard (`include/object/structures_64.bf:71`).
- **The syscall set is not seL4's.**
  - The tree has 47 syscall numbers, one per operation (`Types.lean:4683`).
  - seL4-MCS has 11 (`libsel4/include/api/syscall.xml`, `api-mcs`).
  - seL4 selects an object operation by the invoked capability's type and the
    message label.
  - The tree reads `Recv`'s reply capability from message register 0
    (`SeLe4n/Kernel/Architecture/RegisterDecode.lean:1190`). seL4 reads it
    from `replyRegister` = x6 (`include/arch/arm/arch/64/mode/machine/registerset.h:112`).
- **Capability arguments are words.** Invocations take CPtr words
  (`SeLe4n/Kernel/Architecture/SyscallArgDecode.lean:216`, `:276`, `:300`,
  `:1428`, `:1455`, `:1554`, `:1575`, `:1593`, `:2012`, `:2110`, `:2142`).
  seL4 passes them as extra capabilities, looked up at decode
  (`lookupExtraCaps`, `tcb.c:386`).
- **The thread state model has no Restart, and timeouts unblock blocked IPC.**
  - A cancelled IPC returns `ipcCancelled`.
  - A blocked thread whose budget expires is taken off its queue with
    `ipcTimeout` (`timeoutThread`, `SeLe4n/Kernel/IPC/Operations/Timeout.lean:511`).
  - seL4 restarts the syscall (`ThreadState_Restart`) and raises a timeout
    fault to the thread's timeout handler (`SetTimeoutEndpoint`). Neither
    exists here, and neither does `SetSchedParams`.
- **The root task's IPC buffer is not built by the boot.**
  - The QEMU exerciser gets one from nine kernel invocations after boot
    (`qemuVirtExerciserRootInvoke`, `SeLe4n/Platform/QemuVirt/Exerciser.lean:289`).
    No bundle proof covers them.
  - seL4's boot builds it (`create_ipcbuf_frame_cap`, `src/kernel/boot.c:303`).
- **The CNode invocation set is short.**
  - Missing: Mutate, Rotate and CancelBadgedSends.
  - Delete and Revoke take a bare slot word (`SyscallArgDecode.lean:254`), not seL4's
    index and depth (`decodeCNodeInvocation`, `src/object/cnode.c:42`).
  - Mint overwrites any badge and never sets a CNode capability's guard
    (`mintDerivedCap`, `Operations.lean:1327`). seL4 uses `updateCapData`
    (`src/object/objecttype.c:395`).

The design read behind this plan is at
`/mnt/project-files/za/sel4-error-abi/design.md` (not in the tree). The
facts it rests on are restated here.

## 2. Facts the rows rest on

- **F1. Errors reach only a Call.**
  - `handleInvocation` replies with an error only when `isCall`
    (`src/api/syscall.c:371`).
  - `handleRecv` answers every failure with a capability fault: a failed lookup,
    a capability of the wrong kind, a missing receive right, a notification bound
    to another thread, and a failed `lookupReply` (`syscall.c:387`–`:513`).
  - A cancelled IPC restarts.
  - A budget overrun raises a timeout fault.
  - So no receive ever returns an error frame.
- **F2. D1 resolved by F1.**
  - Today the label carries `errorLabelBase + code` so that a receive's fault tag
    (1–6) or delivered label is never read as an error
    (`ofErrorLabel?_none_of_lt_base`, `faultLabel_lt_errorLabelBase`).
  - Once SX3, SX4, SX7 and SX43 make F1 true here, a receive never yields an error
    frame. seL4's codes 1–10 can then sit in the label with no receive-side collision.
  - One overlap remains, and it is seL4's own: a Call on an endpoint can answer
    `seL4_InvalidCapability` (a capability without the send right,
    `decodeInvocation`, `objecttype.c`) or the server's reply, whose label the
    server chooses.
  - SX45 makes the switch and proves the receive half as a theorem.
- **F3. Extra capabilities need an IPC buffer.** `lookupExtraCaps` with no
  buffer finds none (`tcb.c:392`). So the exerciser's boot-time invocations
  must be gone (SX5) before invocations take extra capabilities (SX6).
- **F4. The heap gate holds every non-carve kernel entry at 0 cells**
  (WS-UC, `scripts/qemu_exerciser_lib.sh`).
  - A nullary `KernelError` is a boxed scalar.
  - A constructor with fields allocates.
  - So a refusal that carries data allocates unless its compiled arm passes the
    data unboxed (D2b).

## 3. Owner decisions

D1–D17 are each **default taken; owner card open**; D18–D32, D34 and D36–D42 are the owner's.
A different answer changes only the rows that cite it.

- **D1. The error label.** *Default:* **seL4's error codes (1–10) in the
  label** (SX45), and the payload in seL4's MR layout (SX1).
  - Every model-only code maps to the seL4 code that shares its meaning, by
    `KernelError.sel4Error`:
    - `objectStoreCapacityExceeded` and `resourceExhausted` map to NotEnoughMemory;
    - `alignmentError` and `mmioUnaligned` map to AlignmentError;
    - every other model-only refusal maps to IllegalOperation.
  - The model code is kept in the refusal ledger.
  - `errorLabelBase` retires. This is F2.
- **D2. Payload codes.** *Default:* all five seL4 payload codes carry their data:
  - `invalidArgument (argNumber)`;
  - `invalidCapability (capNumber)`;
  - `rangeError (min max)`;
  - `failedLookup (wasSource) (LookupFault)`, replacing `depthMismatch`;
  - `untypedRegionExhausted (memoryLeft)`.

  Each site picks its number (`invalidCapability` 558 sites, `invalidArgument` 330).
- **D2b. Heap cost.** *Default:* compiled refusal arms pass the payload as
  unboxed words through their `onErr` continuations, joined to the
  specification by `@[csimp]`, so every refusal reading stays 0 (F4).
- **D3. The fifth FailedLookup word** (a guard mismatch is 5 MRs). *Default:*
  seL4. MR4 is written to the caller's IPC buffer `msg[4]` when the buffer
  resolves, and the length clamps to 4 when it does not.
- **D4. The resolver.** *Default:* `resolveAddressBits`, under seL4's name.
  Lookups are at 64 bits, and the CNode `depth` field retires.
- **D5. Root guards.** *Default:* each deployment keeps its guard, moved into
  the root capability: `virt` 2^58 (the heap gate's large-CPtr reading),
  RPi5 0.
- **D6. Page_Map.** *Default:* seL4. Invoked on the **frame** capability; the
  address space is extra capability 0; the words are vaddr, rights and attr.
  The ASID word goes.
- **D7. SetIPCBuffer.** *Decided by the owner's standing rule:* seL4.
  - The frame capability is extra capability 0, derived into a TCB buffer slot.
  - The kernel reads the buffer through that capability (`lookupIPCBuffer`).
  - The page-table-walk read (`ipcBufferWordPAddr?`, `tlbFillIpcBufferOnCore`)
    retires.
- **D8. Fault handler.** *Default:* MCS.
  - A capability in a TCB slot, set by SetSpace's extra capability 0
    (`tcb.c:1539`).
  - `tcbSetFaultHandler` retires, and fault delivery looks nothing up.
- **D9. Untyped_Retype.** *Default:* seL4's operands.
  - The root is extra capability 0.
  - The words are node_index, node_depth, node_offset and num_objects.
  - num_objects is checked against RangeError(1, the fan-out limit), and the carve loops.
  - The model's caller-chosen object id stays as one word after seL4's six, a
    stated model-only operand.
- **D10. IRQControl_Get.** *Default:* the root is extra capability 0, with
  index and depth.
- **D11. SetPriority / SetMCPriority.** *Default:* the authority TCB is extra
  capability 0 (`tcb.c:1217`).
- **D12. CNode words.** *Default:* seL4's separate words, and `CNodeOpWord`
  retires.
- **D13. Boot buffer placement.** *Default:* a root-server reservation in RAM.
  It is cut from the extension below the region map and subtracted by
  `untypedExtentOf`, as seL4 cuts its rootserver region before making
  untypeds.
- **D14. Boot buffer owners.** *Default:* the root task only (seL4's initial
  thread). The second initial thread is unchanged.
- **D15. Boot-owed writes.** *Default:* the boot entry performs and drains the
  page zeroing and descriptor stores before the first schedule. The base case
  is stated on the drained state.
- **D16. CancelBadgedSends wake.** *Default:* Restart, as seL4 does (SX4
  supplies it).
- **D17. Mint and Mutate data.** *Default:* seL4's `updateCapData`.
  - Re-badging a badged endpoint or notification is IllegalOperation.
  - A CNode capability's data word sets its guard.
- **D18. SchedContext_Unbind of the running thread's context.** *Decided by
  the owner (2026-11-19, "Match seL4"):* refused `IllegalOperation`
  (`illegalState`), as seL4's decode refuses `sc->scTcb == ksCurThread`; the
  model's unbind-and-reschedule path for that case is deleted.
- **D19. A context donated through a notification.** *Decided by the owner
  (2026-11-19, "Map to bound"):* recorded as the receiving thread's `.bound`
  binding, with the notification link kept on the context. seLe4n's
  `.donated scId owner` needs an owner blocked on a reply
  (`donationOwnerValid`), which a notification donation does not have.
- **D20. SX7's remainder.** *Decided by the owner (2026-11-19, "Close and
  split"):* SX7 closes at `v0.37.33` and adds no further behaviour; context
  donation through a notification (SX8), PageTable_Unmap's teardown and
  per-frame W^X (SX39), per-invocation rights (SX40), the Running state per
  core (SX41) and the compound syscalls' invoke phase (SX42) are rows of
  their own.
- **D21. The seL4 conformance table.** *Approved by the owner
  (2026-11-19):* one row per invocation label, sourced from the seL4 source,
  held in code or test data and checked by a test against the decode and the
  return code (SX8.1).
- **D22. SchedContext_Unbind of a context donated through a reply.** *Decided
  by the owner (2026-11-19, "Match seL4"):* Unbind succeeds on a donated
  context, as seL4-MCS's `schedContext_unbindTCB` with `unbindReply` does: the
  context's reply link is cleared, and `donationOwnerValid` is restated so that
  a donation chain may be cut (SX8.3).
- **D23. The seL4 invocations seLe4n lacks.** *Decided by the owner
  (2026-11-20, "New row"):* every invocation label SX8.1's table marks absent
  that no earlier row owns gets one new row, SX46, landed before the closure
  (now SX48). `ARM_SMC_Call` stays absent, as in seL4's default build.
- **D24. A thread with no scheduling context.** *Decided by the owner
  (2026-11-20, "Match in SX11", the row now numbered SX41):* in SX41 a thread
  with no scheduling context (`.unbound`, including one whose context SX8.2's
  `maybeReturnSchedContext` returned) becomes unschedulable, as in seL4-MCS,
  which never runs a thread without one. SX8 leaves the scheduler's run rule
  unchanged (SX41.1).
- **D25. SchedContext_Bind of a context heading a reply stack.** *Decided by
  the owner during SX8 ("Flow-checked Bind"):* the two refusals seL4 does not
  make (a context heading a stack, a thread whose frame is on a live stack)
  are lifted, and the checked dispatch admits a bind of a stack's head only
  where every lender on that stack flows to the bound thread. D27 gives the
  rule its static form: the context's label flows to the thread
  (`schedContextBindLabelGate`).
- **D26. The notification lend's lender.** *Decided by the owner during SX8
  ("flow-checked donation"):* a notification lends a context heading another
  thread's reply stack only where that stack's lenders flow to the woken
  thread; otherwise it donates nothing, seL4's "do nothing" branch.
- **D27. The lenders' flow as an invariant.** *Decided by the owner during SX8
  ("Adopt A*"):* every lender on a context's stack flows to the context's label
  (`contextLendersFlow`), carried by every kernel entry, so the lend and bind
  checks read two static labels and no reply object (D25 and D26 in their
  static form).
- **D28. A refused lend.** *Decided by the owner during SX8 ("Donate
  nothing"):* a Call, a received Call or a fault whose lend the label check
  refuses proceeds and lends nothing (`callLendAdmits`, `receiveLendAdmits`).
- **D29. Carrying the reachable pack across a trace.** *Decided by the owner
  during SX8 ("Register and follow"):* the per-entry lender theorems take the
  chain facts as entry premises; carrying `ipcReachable` across a trace is
  registered (`docs/REGISTERED_DEBT.md` table C, two rows) and owned by WS-PK,
  which opens right after WS-SX closes.
- **D30. The notification lend's label rule.** *Decided by the owner
  (2026-11-23, "Equal labels"):* a notification lends its context only where the
  context's label and the woken thread's are equal (each flows to the other).
  The lend is decided by the thread's own binding and writes the context's
  thread end, so a context below the thread would show its domain one bit of
  the thread's state.
- **D31. The donation-origin redirect.** *Decided by the owner (2026-11-23,
  "Match seL4"):* reply_pop gives a context back to the answered frame's own
  caller, as seL4-MCS does; the origin redirect
  (`donationOriginRecipient?`, `SchedContext.donationOrigin`) is deleted (SX12).
- **D32. SX8's close.** *Decided by the owner (2026-11-23, "Wrap up SX8"):*
  SX8 closes at `v0.37.36` with no further kernel work; its remainder becomes
  SX9 (notification-lend assurance), SX12 (D31) and SX25 (one composed
  in-place ReplyRecv path), and the rows after them are renumbered.
- **D34. The cleared observer of the notification lend.** *Decided by the
  owner (2026-11-23, "Finer projection"):* for an observer the context's label
  flows to (and so, under D30, the woken thread's), the projection shows the
  words that decide the lend: the notification's context word
  (`Notification.schedContextCode`), the thread's binding words
  (`TCB.scBindingScCode`, `scBindingOwnerCode`) and the context's thread word
  (`SchedContext.boundThreadCode`).  SX9.1's two-run theorem is stated over
  that projection, not over premises that the two runs agree on those words.
- **D36. The holder-flow invariant.** *Decided by the owner (2026-11-23,
  "New row"):* the invariant that every binding pair (a thread holding a
  context, bound or lent) has the holder's label at or below the context's,
  `L(holder) ⊑ L(context)`, does not land in SX9. It measured as all of SX8's
  context-lender cut again plus about 33 more per-writer proofs (SX10's
  scope). SX9 ships the one receive step that needs it with an explicit
  per-step premise, `receiveLoanReturnHidden`, registered in
  `docs/REGISTERED_DEBT.md`; the new row SX10 holds the invariant and its
  acceptance is that premise's removal. SX10 runs next, so the rows after it
  are renumbered (SX10–SX20 became SX11–SX21). D37 replaces the one-way
  relation with equality and the premise with `bindingLabelsEqual`.
- **D37. Equal binding labels.** *Owner's decision (2026-11-23,
  "Equal labels"):* SX9.1's two-run theorem showed that the one-way relation
  of D36 is too weak. The lend's admission reads the context's thread word and
  the waiting thread's own binding word, and D34 shows each only where the
  object it names is visible. A pair of runs in which a visible thread is bound
  to a hidden context in one run and unbound in the other is low-equivalent,
  satisfies `L(holder) ⊑ L(context)`, and diverges at the lend. So the
  relation is equality: every binding pair (a thread holding a context, bound
  or lent; a context's thread word; a notification bound to a context) has
  equal labels (`bindingLabelsEqual`, read through `twoWayLabelGate_iff_eq`).
  SX9 replaces `receiveLoanReturnHidden` as the receive steps' premise with
  this one predicate, from which the loan-return shape is derived
  (`receiveLoanReturnHidden_of_bindingLabelsEqual`), and the two-run theorem
  takes it of both runs. Still one premise. SX10's invariant (completed in SX13–SX18,
  D38, D40) becomes this equality.  Two consequences recorded in SX10, following from D37 with no new owner
  decision: the return of a lent context to its owner binds the owner, so the
  invariant also says a lent binding's owner has the context's label; and the
  owner and each later owner come off the context's reply stack, so SX8's
  `contextLendersFlow` (D27: every lender on a context's stack flows to the
  context's label) is strengthened in place to label equality, which its
  creating sites discharge from the two-way gates (D33, D35, D30) and the
  invariant at the lend.  The one-way D27 predicate is superseded.
- **D38. SX10's wrap.** *Decided by the owner (2026-11-24, "Wrap, new rows"):*
  SX10 closes at `v0.37.39` at its validated point: the boot base case
  (SX10.1), the owner clause of `bindingLabelsEqual` and the slot-by-slot
  toolkit of its binding words. The rest of the invariant does not land in
  SX10, because one creating site cannot be discharged from the carried
  invariant. A Call lend gives the receiver the caller's context, so its
  thread clause needs `L(receiver) = L(context)`. The Call's gate is two-way
  but checks the caller against the endpoint only at the Call. The receiver
  passed its gate at its own earlier receive, and the state keeps no trace of
  that. The receive-take lend has the same gap the other way round. The only
  state facts are `blockedSenderFlowsToEndpoint` and
  `blockedReceiverFlowsFromEndpoint` (`InformationFlow/Invariant/Composition.lean`).
  Both are one-way and neither is carried across a trace (`ipcReachableUnder`,
  `docs/REGISTERED_DEBT.md` table C, owner WS-PK). So D37's "the step's gates
  make the receiver's label the lender's" needs a state invariant first. SX11
  makes it: every thread blocked on an endpoint carries the endpoint's label,
  as a per-entry stage. SX13 completes the equal-binding-labels invariant on
  it: the rest of the invariant as SX10 first stated it (its preservation, the
  premise moved, the refusals deleted), now SX13–SX18 (D40). The rows after
  SX10 are renumbered (SX11–SX21 became SX13–SX23). No live path was found
  that admits a donating Call or a receive take without the gate on both
  sides; the gap is in the proof, not the kernel.
- **D39. The redirect first.** *Decided by the owner (2026-11-24, "Redirect first").* The
  binding-invariant row (then SX12) stopped at its reply path: the reply's pop
  hands a lent context to `replyDonationRecipient`, which at the bottom of a
  depth-2 out-of-order stack is the context's recorded `donationOrigin` (the
  origin redirect, D31), and no clause of `bindingLabelsEqual` or
  `contextLendersLabelsEqual` names the origin or its back-link
  (`TCB.originScCode`), so the new owner's label cannot be shown to be the
  context's. Not a vulnerability: the back-link is written only on a first push,
  where the donor owns the context, and labels are static; the gap is in the
  invariant. The default deletes the redirect first, as D31 already decided, so
  the reply's recipient is always the answered caller. The two rows swap: the
  redirect deleted becomes SX12 and the binding invariant completed becomes
  SX13. The alternative, a fifth clause naming the origin, would be deleted with
  the field one row later.
- **D40. SX13's wrap.** *The owner's ("Wrap, new rows"; default taken
  2026-11-24, confirmed by the owner's merge of PR #1101).* SX13 closes at `v0.37.42` at its validated point: the binding
  grow and the binding-words leaf lemmas. Its first cut, measured by stubbing
  every failing lender declaration to a fixpoint, needs 37 declarations in 9
  files and a census witness, about 10 sibling lemmas for the summaries that
  forget the binding words, and, uncounted by the stubs, the restatement of 30
  `LendersFrame` theorems: the pops grow the binding views, so they are no
  longer links shrinks. That is well over 1.5 times the row's estimate (owner
  rule D32). The remainder becomes three rows: SX14 (the frame family threaded,
  the pops as labelled steps), SX17 (the creating sites and preservation over
  every writer) and SX18 (the premise moved and the refusals deleted, SX13.2
  and SX13.3 as first stated). The rows after SX13 are renumbered (SX14–SX23
  became SX17–SX26). No live path lends a context across unequal labels; the
  gap is in the proof, not the kernel.
- **D41. The cancel's pop returns to the frame's recorded caller ("Match
  seL4").** *The owner's (default taken 2026-11-24, confirmed by the owner
  the same day).* The cancel's
  donation return (`returnDonationToCancelledCaller`) popped to the cancelled
  thread itself, read from the thread's own reply link, and nothing in the
  pop's pre-state tied that thread to the frame it pops: the labelled pop's
  owner obligation (the recipient's label equals the context's) was not
  dischargeable from the carried invariant, since `contextLendersLabelsEqual`
  names the frame's recorded caller and the owner word, not the cancelled
  thread. seL4's `reply_pop` donates to `reply->replyTCB`, the frame's
  recorded caller. So the cancel's resolver (`cancelledCallerDonation?`) also
  requires the frame to record the cancelled thread as its caller
  (`replyRecordsCaller`, a word compare, allocation-free), and declines
  otherwise; the compiled head cancel (`headReplyCancelInPlace`) reads the same
  word. On every state where the reply linkage holds the two readings agree
  (`cancelledCallerDonation?_eq_unguarded_of_linkage`), as OD1.4's guard did;
  `cancelledCallerDonation?_independent_of_victim` is retired. The other pops
  already pop to a word their own pre-state names: the finalisation's unheld
  pop and head cancel to the reply's recorded caller (`finaliseReply` reads
  `c` off the reply), the pre-receive cleanup to the owner word, and the reply
  to the answered caller, whose obligation the dispatch premise pack's linkage
  discharges with the carry lemma across the reply leg. Alternatives not taken:
  a linkage premise at each cancel's pre-state (unnameable inside the
  finalisation fold, and the row's acceptance allows label equations only), or
  carrying the reply linkage in the lenders stage (its preservation over every
  writer).
- **D42. SX14's remainder split ("Split A then B").** *The owner's (default
  taken 2026-11-24, confirmed by the owner the same day).* SX14 lands SX14.1 at
  `v0.37.43` and wraps there (D32). Its remainder (SX14.2, the frame family
  threaded; SX14.3, the pops as labelled steps), measured on the landed guard at
  45 failing lender declarations in 10 files, a census witness, about 24 pops
  still stated as frames and the creating sites' hypotheses, splits into two
  rows: SX15, the additive part that lands alone on the committed base (the
  sibling lemmas for the summaries that forget the binding words, the
  finalisation steps' binding shrink kept separate from `finaliseWrite`, and the
  one-slot grow toolkit), and SX16, the frame family threaded and the pops as
  labelled steps, one unit because every lender module after Cancel consumes
  the frame family it changes. The rows after SX14 are renumbered (SX15–SX26
  became SX17–SX28). The alternative, one row holding both, would land nothing
  until all of it builds.
- **D43. The notification lend's check stays until coherence is carried
  ("Prove first").** *The owner's (2026-11-24).* SX18.2 first named the
  notification lend's label check (`donationContextFlows`, D30) among the
  refusals the completed invariant makes unreachable. It does not, under the
  carried invariants. The lend goes to the thread the signal wakes
  (`signalWokenThread?`: the notification's bound thread blocked receiving, or
  its wait-queue head), and the step needs that thread's label equal to the
  context's. `bindingLabelsEqual` gives the notification the context's label;
  the thread's equality with the notification is `notificationLabelsCoherent`
  (`IPC/CrossCore/NotificationBindDispatch.lean`), which the boot checks and no
  entry carries (the queue-label-uniformity row of `docs/REGISTERED_DEBT.md`);
  SX11's waiters leave `.blockedOnNotification` out. The live kernel never
  reaches the refusal (the wait and bind gates are two-way and the boot refuses
  an incoherent image); the gap is in the proof. So the check stays until a row
  carries coherence (SX21), and the row after it deletes it at its three sites,
  the signal arm, the declassified signal and the interrupt delivery (SX22).
  The alternatives, deleting it now with coherence as a premise of the three
  signal entries (as the declassified signal's second hop was, gate PR #1096)
  or keeping it for good, were not taken. The Call lend's refusal (D28) is
  unreachable under the carried invariant: the admission asks whether the
  caller flows to the context it holds, and `bindingLabelsEqual` makes them
  equal.
- **D44. SX18's wrap.** *The owner's D32 rule (2026-11-24, "Wrap at
  SX18.1").* SX18 closes at `v0.37.47` at SX18.1, the premise moved. The Call
  lend's refusal (D28), measured before any edit, cannot be deleted as one
  definition: the admission's answer is threaded as a `lend : Bool` argument
  through the gated donation (`applyCallDonationOnCoreWhen`), the gated
  resolver (`callLendSchedContext?`), the in-place unlent arms
  (`callWakesUnlentInPlace`, `receiveCallTakesUnlentInPlace`, the ReplyRecv
  unlent arms) and the Call, fault, receive and ReplyRecv legs, so retiring it
  restates 219 declarations in 57 files that take the argument, well over 1.5
  times the row's estimate. The remainder becomes three rows: SX19 (D28
  deleted, the lend parameter retired), SX20 (notification label coherence
  carried, D43) and SX21 (D30 deleted, D43). The rows after SX18 are
  renumbered (SX19–SX28 became SX22–SX31).
- **D45. Extend the records view, then the coherence stage.** *The owner's
  (2026-11-24, "Extend records view").* Measured when SX20 started:
  `notificationLabelsCoherent` reads a thread's two notification-queue links
  and a notification's bound thread and queue ends, and no frame carried
  per entry keeps them. The records view held a thread's reply view, IPC
  state, thread state and fault flag, and nothing of a notification, so none
  of the 228 records frames that SX11's waiters reused for free keeps
  coherence's reads (a coherence stage over them would be about 380
  theorems, some 2.5 times SX11). The records view gains those fields
  instead, so every records frame keeps them, and the writes of them (the
  bind and the unbind, the notification stores of the signal and the wait,
  the waiter's link, the head's detach and the link-only rewrites) are
  restated as core frames (`RecordsCoreFrame`), which keep the kernel
  records only. That is SX20; the stage is SX21 and the D30 deletion SX22.
  The alternatives, a separate coherence frame proved for every arm (a twin
  of the records family) or a smaller invariant whose queue-head clause is
  an entry premise, were not taken.
- **D46. The label part carried; the queue shape stays with `ipcReachable`.**
  *Default taken (2026-11-25).* Measured when SX21 started:
  `notificationLabelsCoherent` also asks that a thread blocked on no
  notification hold no notification-queue links, and that clause is not
  carriable with no added hypothesis: the send pops the receive queue's head
  and stores it `.ready` without reading its state
  (`endpointSendDualOnCore`), so "it held no links" needs the queues' shape,
  which `ipcReachable` owns (D29, WS-PK). Every consumer reads only the label
  clauses, so the stage carries `notificationLabelsAgree`: a notification's
  bound thread and queue ends pass its two-way gate, a thread blocked on a
  notification passes it, and a thread's queue links name threads of its own
  label. The boot keeps the full check, which implies the carried form
  (`notificationLabelsCoherent_agree`). The structural clause is a table C row
  of `docs/REGISTERED_DEBT.md`, owned by WS-PK beside `ipcReachable`.
- **D47. SX22's wrap.** *The owner's D32 rule (2026-11-25, "Land SX22.1
  alone").* SX22 closes at `v0.37.51` at SX22.1. The check was proved true at
  every site before any edit: the woken thread has its notification's label
  (`notificationLabelsAgree`, carried since SX21) and the notification its
  context's (`bindingLabelsEqual`), and the check is the two-way gate between
  those two labels. The measurement found a fourth site the row did not name:
  the completed-signal arm of a receive (`completeSignalArm`, and the ReplyRecv
  arm that completes a signal), whose lend runs after the checked wait, and
  the wait's two-way gate gives the same equality; the check is deleted there
  too. SX22.2, measured next, does not fit beside it: the records view keeps
  no endpoint queue link (`TcbRecordView`), so no carried frame keeps the
  neighbours' labels the teardown reads, and carrying them is the SX20 and
  SX21 pattern again (the view extended, its writers restated as core frames,
  then a stage), well over 1.5 times the row's estimate. The remainder becomes
  two rows: SX23 (the records view extended with the endpoint queue links,
  as D45 extended it with the notification fields) and SX24 (the endpoint
  queue links' labels carried, the queue arms' `hTeardownProj` discharged).
  The rows after SX22 are renumbered (SX23–SX32 became SX25–SX34).
- **D48. SX25's wrap.** *The owner's D32 rule (2026-11-25), applied before
  the bulk was written.* Measured before any edit: a reply-receive has five
  reply arms (no pop, donated, held, unheld, unlinked), three receive legs
  (block, Send take, Call take), three answers (message, capabilities, fault)
  and two lengths, 90 shapes in all; 37 are in place under 46 per-shape
  functions (16,891 lines across the thirteen modules, `RefusalCarryingReplyRecv`
  and the four modules that build on them), and 11 of the 15 guards the
  receive legs read across the reply arms exist, each written for its shape.
  One composed path over all 90 measured at 6–8 sessions against the row's 3.
  SX25 keeps the reply leg over all five arms, its guard family (the four
  missing guards filled), and the composed blocking receive for every answer
  and length under one `_eq`, and retires the blocking modules. The remainder
  becomes two rows: SX26 (the Send-take leg composed) and SX27 (the Call take
  with its donation and holder deschedule, and the row's final acceptance).
  The rows after SX25 are renumbered (SX26–SX34 became SX28–SX36). The
  narrowed row ran about twice its estimate (one QEMU run found the held arm's
  guard unreachable, and the retirement moved what surviving files read
  first); the coordinator ruled it finished whole rather than split again,
  because the superseded per-arm modules must be deleted in the cut that
  supersedes them.
- **D49. SX27's wrap.** *The owner's D32 rule (2026-11-25), applied by the
  coordinator during the row.* Measured before the bulk: the Call take still
  had 27 shapes to bring in, about 4.5–5.5 sessions against the row's 2–3.
  SX27 keeps the Call take composed for the five reply arms, the three answers
  and both lengths under one `_eq`, the Call-take arms of
  `RefusalCarryingReplyRecv.lean` restated over one out-of-line selector, the
  three Call-take modules retired, the store-reader hygiene rows regenerated,
  the final C size and compile-time acceptance, and the QEMU steps of the
  Call-take shapes with a scenario to build on. The remainder becomes one
  new row, SX28: QEMU scenarios for the remaining Call takes and the eight
  Send-take shapes carried from SX26.1, and a measurement of a server
  holding its own scheduling context taking a Call on any arm (brought in
  place if it is reachable and allocates). The rows after SX27 are
  renumbered (SX28–SX37 became SX29–SX38). During the row, the fault-answer
  Call takes were found to have no lane to build on: the fault lane's root
  task holds its own context, so a Call queued there is not lent, and a lane
  whose server holds none is new work. Their steps moved to SX28.1 with the
  other new scenarios. Before SX27 merged, the `queued-caller-*` scenarios
  its steps were built on were found to run the rendezvous arm, not the
  donated arm (the partner they answer holds no context, so its `Call` lent
  nothing; a debug-only build whose selector refuses the rendezvous arm
  confirmed it): SX27's QEMU steps are the rendezvous and unlinked arms'
  Call takes at 120 words, granting a capability and both (six shapes), and
  the donated arm's six Call-take shapes moved to SX28.1.
- **D50. SX28's wrap.** *The owner's D32 rule (2026-11-25), applied by the
  coordinator before the bulk.* SX28.2's measurement was run first: a server
  bound to its own scheduling context whose reply-receive takes a queued
  `Call` on the rendezvous arm read 141 heap cells (3,168,520 bytes) at the
  first call and at steady state, on both lanes; three of the cells (1 MB
  each) are the object store's table copied on the general path, which
  writes the store while it still shares it (twice under `storeObject`, once
  under `enqueueRunnableOnCore`'s `modifyObject`). On the rendezvous and
  unlinked arms the Call-take guard admits a server holding no context, or
  one whose context the receive returns, and on the unheld arm a server
  holding none; a server bound to its own falls to the specification's
  general path. The donated arm never meets one: its pop's guard
  (`replyPopsInPlace`) needs the context the reply heads bound to the
  server, so the server holds the lent context and the pop unbinds it. So
  18 shapes reach the general path (three arms, three answers, two lengths).
  The row measured at 3.25–4.25 sessions against 2. The coordinator kept it
  whole, because the guard split, the lend flag and the selector are shared
  by the three arms. SX28 keeps the context-holding server's Call take in
  place on the rendezvous, unlinked and unheld arms (no lend, as the held arm
  takes it), its equality over the arm, the restated selector and arms, and
  its QEMU steps.
  The remaining QEMU scenarios (SX28.1, including the donated arm's six Call
  takes) become one new row, SX29. The rows after SX28 are renumbered
  (SX29–SX38 became SX30–SX39).
  *The owner's ruling (2026-11-26).* During the row the general path's three
  1 MB copies were traced to their cause: the refusal-carrying wrapper keeps
  the pre-state live for its error arm across an `Except`-returning operation
  that writes (`replyRecvRendezvousR`, `match replyRecvTransferOnCore … st
  with … | .error e => .error (e, st)`), so every store write inside it meets
  a shared table and copies it. The reply-receive chain
  (`endpointReplyRecvAnsweringOnCore`) has about 33 refusal exits, about 28
  of them after a write, so no read-only check on the pre-state is cheap
  enough to absorb into SX28. The owner ruled:
  - the row is kept whole;
  - the donated arm gets no compiled own-context branch or instance: a lemma
    closes it (`replyPopsInPlace` needs the head context bound to the server,
    so the take always lends), and a Tier 3 negative anchor refuses such a
    branch;
  - SX28 does not carry the copy fix. Its measurement step goes through the
    in-place take, so it reads 0; the general path's copy, with its cause,
    is SX29's;
  - the sweep of every refusal wrapper that keeps the pre-state across a
    writing operation is a new row, SX29, with ReplyRecv moved to seL4's
    order (the reply leg commits, and a refusing receive reports the state
    it stopped in, as seL4's `handleReplyRecv` does, with no undo) and an
    IR- or C-reading gate. The rows after SX28 are renumbered again
    (SX29–SX39 became SX30–SX40).
  The own-context guard also requires that no notification is bound to the
  server, as the held arm's does; a server with a bound notification stays on
  the specification's path and is not refused.
- **D51. SX29's measurement and the owner's rulings.** *SX29.1 was run
  first; the owner ruled on it (2026-11-26).* The set was derived from the
  Lean IR the C emitter prints, over the closure of the 12 committing
  exports (8,241 IR declarations with the compiled closure's replacement
  edges): a call that passes the state at a destructive position while the
  caller keeps it live, so the callee meets a shared state and copies it.
  It found 1,548 such holds, 327 (caller, callee) pairs, over 147 source
  functions, in seven classes: (a) wrappers whose hold drops once their
  callee reports its stopped state (19); (b) ReplyRecv's refusal wrappers
  and its composite (12); (c) invocations that refuse after a write where
  seL4 decodes first (17); (d) specification bodies that refuse after a
  write and report their entry state, exits seL4's C does not have (35);
  (e) the pre-state read after a write, no refusal involved (50); (f) a
  field of the state held across a write (10); (g) the boot, run once (4).
  The closure applications whose callee the IR does not name (1,336 in
  305 declarations) are not counted. The text count of SX28 (58 sites) is
  only a pin. The measurement put the whole sweep at about 17–24 sessions
  against the 8–12 SX29 carried. The owner ruled:
  - *Placement.* SX29 keeps ReplyRecv (class b) and its legs' own holds.
    The gate is a new row, SX30, landing with a pinned list that may only
    shrink and refusing every closure call it cannot resolve. Classes (a),
    (c), (d), (e) and (f) away from the reply-receive chain become a new
    workstream, WS-CK, opening after WS-SX closes
    ([`REFUSAL_CHECKS_FIRST_PLAN.md`](REFUSAL_CHECKS_FIRST_PLAN.md)).
    Class (g) is out of scope: the boot runs once. The rows after SX29 are
    renumbered (SX30–SX40 became SX31–SX41).
  - *seL4's order, both ways.* seL4 has no `handleReplyRecv`: ReplyRecv is
    `handleSyscall`'s `case SysReplyRecv` (`src/api/syscall.c`), which runs
    `handleInvocation(false, false, true, true, reply)` and then
    `handleRecv(true, true)`, skipping the receive only on preemption.
    `handleInvocation` returns `EXCEPTION_NONE` on a syscall error, so a
    refused reply does not stop the receive; `handleRecv` undoes nothing
    the reply committed. A refused reply reports its error and the receive
    still runs (SX33, D60). A receive the kernel refuses after the reply
    step reports the state after the reply (SX34, D60's option (b)). A
    refused receive capability does not yet follow the ruling, which this
    record earlier stated it did. A capability that is not found, is of the
    wrong kind or lacks the receive right is resolved on the entry state,
    before the reply runs, and faults the whole syscall there. seL4's
    `handleRecv` resolves it after the reply, so the deviation is D63's and
    SX36 fixes it. seL4's receive-side capability refusals are capability
    faults on the caller (`handleFault`), and so are seLe4n's since SX3
    (`receiveGateRefuses`). The receive leg's other refusals, each off the
    invariant, are error returns; seL4's `receiveIPC` has none of them.
  - *Checks first.* Each refusal after a write on the reply-receive path
    moves before the first write, as a read-only check on the leg's entry
    state, and each fast form keeps an unconditional equality to its
    specification, with no invariant assumption.
  - seLe4n's features stay: the dual queue never holds a half-unlinked
    state, the flow gate runs before anything observable on each leg, the
    non-interference proofs are restated, not dropped, the lock sets stay
    and nothing allocates. A conflict with any of them goes to the owner.
  The seL4 sources read are `src/api/syscall.c`, `src/object/endpoint.c` and
  `src/kernel/thread.c` at seL4 commit
  `f6978b12e0662da10fc226c5e60ef1f0f7d6fec4` (2026-03-10, master); each file
  is byte-identical there and at `a95bf634`, the parent of `828de76c`, the
  next change to `syscall.c`, which touches only the interrupt entry.
- **D52. SX29's wrap.** *The owner's D32 rule (2026-11-25), applied by the
  coordinator (2026-11-26).* SX29 ran clearly past its 5–7 sessions, and
  the composite waits on two owner questions: what a reply-receive whose
  reply refused and whose receive then ran reports, and WS-CK's order
  beside WS-PK (D29). So SX29 is wrapped at its validated legs:
  - SX29 keeps the legs checks first, as landed: the reply, the splice, the
    pop, the receive's three steps (the migrated cleanup, the handoff, the
    capability receive), and the receive body for plain senders, blocking
    receivers and call senders. Each has an unconditional `@[csimp]`
    equality to its specification. The IR measurement fell from 1,548 holds
    to 1,498, and no hold has a checked form as its caller.
  - The composite in seL4's order (`endpointReplyRecvAnsweringOnCore` and the
    12 class (b) wrappers carrying their callee's state, with the invariant
    and non-interference proofs restated) becomes a new row, SX30. Its
    acceptance: the general path's step reads no 1 MB cell, and then the
    legs are measured again, since a copy made early hides a later hold.
  - The rows after SX29 are renumbered (SX30–SX41 became SX31–SX42): the
    gate is SX31, the QEMU scenarios SX32, the lock-set ceiling SX41 and
    the closure SX42.
  *The reading.* With the in-place take un-routed locally, the own-context
  reply-receive taking a queued `Call` through the general path read 110
  cells (1,061,184 bytes) on both lanes, at the first call and at steady
  state, against SX28's 141 cells (3,168,520 bytes, three 1 MB cells). One
  1 MB cell remains: the object table copied by the reply leg's first store
  (`storeObject` under `endpointReplyOnCoreChecked`), because the composite's
  later reads of the pre-state and the wrapper's error arm still hold it.
  That cell is SX30's.
  *The C.* `RefusalCarryingReplyRecv.c` is 12,944,474 bytes, 2,639 over
  SX28's 12,941,835, and its standalone compile took 488 s and 500 s on
  two quiet runs and 542 s cold, against 479 s and 476 s. Its source is
  unchanged, so the growth is inferred to be the legs' checked forms
  inlined into it. The bound is carried to SX30, which must bring the
  file back to 12,941,835 bytes or less and about 480 s or less,
  measured against a kept copy of SX29's generated C so that the
  difference can be localized.
  *The fallbacks.* Each checked form falls back to its specification where
  its read-only check fails, and the specification still holds its entry
  state there. The receive body takes the specification when a slot it
  writes is not found in place (`findsInPlace`, which can miss on a
  well-formed table at load 3/4 or more), when the receiver is reserved or
  is the sender, when the blocking receiver holds a donated context or is
  not admissible to the queue, or when the stasher's reply record is not in
  place. A call sender with a reply link or without one takes it on the
  same terms.
- **D53. SX30's split.** *The owner's D32 rule (2026-11-25), applied by the
  coordinator (2026-11-26).* SX30's measurement put the row at about 7.5
  sessions against its 2–3, and found why: the composite answers its caller
  last. `replyRecvAnswerCaller` runs after the receive and the
  priority-inheritance handoff, so on a refused receive the state "after the
  reply" has the caller ready with its fault record still set and its frame
  not written, and it fails `kernelRecordsSound`. A refused receive cannot
  report that state. So the row is split:
  - SX30 moves the caller's answer into the reply step on every path, in
    seL4's order (`doReplyTransfer` wakes the caller and writes its frame or
    answers its fault before `receiveIPC` runs). No refusal changes: what
    refuses today refuses the same way. The in-place equalities over the
    composite are restated, unconditionally, and the invariant and
    non-interference proofs the move touches with them. SX30 also states
    the lemma SX31 needs: the state after the reply step satisfies the
    invariant families. This is the owner's ruling, 2026-11-26
    ("seL4 order"). The alternative, a tail on the refusal path only, would
    make SX30 unnecessary.
  - SX31 is the refusal order and its proofs: a refused reply lets the
    receive run, a refused receive reports the state after the reply, the
    12 refusal-carrying wrappers carry their callee's state, the report's
    consumers gain that third case, the non-interference proofs cover it,
    and the last 1 MB cell goes (old SX30's acceptance). Two rulings
    are SX31's, each the owner's ruling, 2026-11-26: a flow-denied reply counts as a
    refused reply, so the receive runs; and a refused reply's error is
    dropped, as in seL4, so the thread sees the receive's outcome.
  - The rows after SX30 are renumbered (SX31–SX42 became SX32–SX43): the
    gate is SX32, the QEMU scenarios SX33, the lock-set ceiling SX42 and the
    closure SX43.
  *Decided (the owner, through the coordinator, 2026-11-26).* seL4's reply
  step also takes the server off the run queue when the pop takes its
  context (`reply_pop` → `schedContext_donate`), and seLe4n's
  priority-inheritance reversion belongs to the reply as well. Both stay
  after the receive on the successful path (`replyRecvPostReceiveDonation`),
  because seLe4n keeps the running thread on its run queue and the end state
  matches seL4's once `schedule()` re-enqueues the current thread: a server
  descheduled before a receive that takes a queued `Call` and is handed its
  context would otherwise be left ready but off every queue (PR #822's
  review). The refused receive (SX33) applies them as the outcome with
  nothing received, which is the state seL4 reaches there. A final state
  that differs from seL4's here is a defect, to be reported.
- **D54. SX30 wrapped again.** *The owner's D32 rule (2026-11-25), applied by
  the coordinator (2026-11-26).* SX30's second session measured the move at
  about 5–6 sessions: the composed in-place theorems state the composite at
  an abstract transfer output and answer, and moving the answer before the
  receive puts it under every receive-side step, which needs commutation
  lemmas that do not exist (`DeliveryCommute.lean` covers only message-slot
  writes). So:
  - SX30 lands the commutation toolkit (the answer's writes, including the
    fault record, the physical-write log and a run-queue removal, against
    the receive side's appends, requeues and walks) and a theorem that the
    answer-first composite equals today's, unconditionally where it can be,
    otherwise under the weakest premises, listed. The definition is not
    switched in SX30.
  - SX31 (new) switches the composite to answer-first and restates the
    composed in-place theorems, the invariant families and the write sets,
    and adds the lemma the refusal row reports from.
  - The rows after SX30 are renumbered (SX31–SX43 became SX32–SX44): the
    refusals are SX32, the gate SX33, the QEMU scenarios SX34, the lock-set
    ceiling SX43 and the closure SX44.
- **D55. SX30 wrapped at its toolkit.** *The owner's D32 rule (2026-11-25),
  applied by the coordinator (2026-11-26).* SX30's third session landed the
  answer as one answer-slot write, its commutation family (with the
  message-slot family restated as its identity instance), the receive
  side's stores, the queue pop and the physical-write log, and measured the
  rest of the toolkit and the equality at about 3–4 sessions. So:
  - SX30 lands what is built, proof-only, at `v0.37.59`. Its consumer is
    SX31.
  - SX31 (new) is the rest of the toolkit and the answer-first equality, one
    theorem over every answer kind. A fault abandon's run-queue removal
    commutes with the receive's appends, requeues and removals of other
    threads only when the run queue's links are consistent, so the theorem
    takes `runQueueRefined ∧ objects.invExt` for that case, inside the one
    statement. This is the default; the theorem is not split by answer kind.
  - *The physical-write log.* The answer's overflow words and the receive's
    capability transfer (which records an unwrapped badge) land in the log
    in different orders under the two compositions. Answer-first is seL4's
    order, the addresses written are distinct, and memory after the log is
    drained is equal. The equality therefore carries a log premise (an
    answer that writes no overflow word, or a transfer that records
    nothing) or states the log up to that order; it is not a defect.
  - The rows after SX30 are renumbered (SX31–SX44 became SX32–SX45): the
    switch is SX32, the refusals SX33, the gate SX34, the QEMU scenarios
    SX35, the lock-set ceiling SX44 and the closure SX45.
- **D56. A dequeued run-queue entry clears its links.** *Found in SX31;
  the coordinator's ruling (2026-11-26), taken inside SX31 under the rule
  that errors found along the way are fixed in the PR that finds them.*
  - *The finding.* `RunQueue.remove` marked the entry not queued but kept
    its four links (`prev`, `next`, `bucketPrev`, `bucketNext`), while
    `TCB.detachRun` already cleared the thread's own. An append writes the
    old tail's `next` (and the bucket tail's `bucketNext`), so a thread that
    was the tail when another thread joined and was dequeued afterwards kept
    a link to the joiner, and one dequeued first did not. The queue itself
    was the same either way: these are dead links in an unqueued entry,
    read only while the entry is queued and rewritten by any re-append. It
    is not a vulnerability. But the state depended on the order of a
    removal and another thread's append, so the fault abandon's equality
    across the receive leg (the reply leg wakes the caller as the tail, the
    receive leg wakes a plain sender onto the same core) was false as a
    state equality.
  - *The change.* `RunQueue.remove` (`unlinkLinks`) now clears the four
    links with the flag. This is seL4's own state: `tcb_queue_remove`
    (`src/object/tcb.c`, seL4 `f6978b12`), called from `tcbSchedDequeue`,
    sets whichever of the dequeued thread's `tcbSchedPrev` and
    `tcbSchedNext` is not already `NULL` to `NULL`.
    The clearing is in place, so nothing allocates, and no `@[csimp]`
    equality gains a premise.
  - *The second change* (the coordinator's ruling, 2026-11-26). With the
    links cleared, the resize check still depended on the order:
    `RunQueue.setLink` was `RHTable.insert`, which checks the load threshold
    on every call, a rewrite of a present entry included. A removal's
    rewrites made after another thread's first insert could grow the table
    where the same rewrites made before it did not (SX31's `RQ2`
    counterexample: a core whose link table holds 11 keys of 16 with only the
    caller queued ends at capacity 32 in one order and 16 in the other). So
    `setLink` now rewrites a present entry in place (`RHTable.mapValueAt`,
    no resize check: a rewrite adds no key) and inserts only a thread's first
    entry, the shape its compiled form already had; that compiled form and
    its `@[csimp]` are retired, the specification being the compiled shape.
  - SX31 is therefore not proof-only: these are its two compiled changes.
- **D57. The fault abandon leaves the answer-first equality.** *The
  coordinator's ruling (2026-11-26), reversing D55's "one theorem over every
  answer kind, not split by answer kind".* SX31's equality covers the
  ordinary answer and the fault restart, one theorem over those two. The
  abandon (a declined fault reply) deschedules the caller, and the RQ2
  counterexample (D56) showed the run queue's state depending on whether
  that removal ran before or after the receive's run-queue writes. D56
  removes the difference, but carrying the abandon through an equality
  still needs a commutation family for the run queue (the removal against
  the wake, the receiver's removal, the holder's deschedule and the
  priority requeue, at the queue record, the TCB links and the scheduler)
  and a thread-state generalisation of the answer slots, measured at 2–3.5
  sessions. SX32 switches the definition anyway, so it restates the
  abandon's downstream proofs directly on the switched composite; the
  commutation buys nothing SX32 does not already do.
- **D58. The quiet branch reads its buffer frame per consumer.** *SX32's
  finding 1, the coordinator's ruling (2026-11-26): route (a), the generic
  ledger family.* An ordinary answer longer than four words stages its
  overflow words by recording them in the physical-write log, so SX31's
  equality gains a second premise beside the short message (D55): the
  dequeued sender asks to transfer nothing, so the tail records nothing and
  commutes with the recording (`replyRecvReceiveTail_ledger`), and every
  result of the tail reads the caller's IPC buffer as the reply step left it
  (`ipcWordReadsAgree`). No generic buffer frame of the tail exists; each
  consumer proves it on its own path.
- **D59. Both fault kinds answer first in the compiled forms.** *SX32's
  finding 2, the coordinator's ruling (2026-11-26): option B.* seL4's
  `doReplyTransfer` runs `handleFaultReply` before `handleRecv` for a restart
  and an abandon alike, so the block, take and Call-take fault performers run
  the answer on the popped reply leg and the tail on the answered state. Each
  `@[csimp]` stays unconditional: the receive, take and Call-take guards the
  tail reads are carried across the answer (`answerGuardFrame`: every slot
  but the caller's agrees off its run links, and the caller's keeps the codes
  the guards read). The duplicate fault forms that answered last are retired.
- **D60. A refused reply lets the receive run; a pop refusal refuses the
  whole syscall.** *SX33's first piece and the coordinator's ruling
  (2026-11-26).* seL4's `doReplyTransfer` returns with nothing to do when
  the reply's caller is gone or not blocked on reply, and `handleRecv` then
  runs. So a reply-receive whose caller is not found or not waiting
  (`replyRecvCallerAwaitsReply`), or whose reply leg the flow gate denies, now
  takes the receive alone, the busy reply's holder cancelled where the flow
  admits it; the choice is made in one place (`replyRecvReplyAnswers`). Before,
  the first two refused the syscall at the pre-state. Both are reachable only
  off the invariant (`replyCallerLinkageReciprocal`: a reply's caller is a
  stored thread blocked on that reply), and a flow-denied reply's outcome is
  unchanged (the receive cancels no one and refuses `.replyCapInvalid` on the
  busy reply). seL4's `reply_pop` cannot fail, while seLe4n's pop
  (`replyRecvPopDonation`) has defensive refusals; under the ruling, a pop
  refusal is checked before the reply leg and refuses the whole syscall with
  nothing written, and it is not a refused reply. *Reachability, checked:* no
  pop refusal is reachable on a state that holds the IPC bundle, the chain
  invariant, the binding pair and the dispatch's stated coherence hypothesis.
  The caller's sentinel arm is excluded by the reply leg's own lookup (which
  refuses a reserved id). The holder's is excluded by the binding pair (the
  holder is a stored thread), since no transition stores a thread at the
  reserved id (retype validates its child through `validateObjIdArg`); no
  invariant states that, so it rests on this reasoning. The reply-stack
  resolver's refusals (head, frame below, its caller) are excluded by
  `replyStackOuterCallerResolves_of_chainWellFormed` (the relaxed chain form
  at the answered head is enough, since it reads only the frame below). The
  bound-thread guards are vacuous (`replyFrameHeadHolder?` reads them on the
  same state), and the late thread lookups and the holder's binding guard are
  excluded by the binding pair. The outer caller's guard (`outerCallerAcceptable`)
  is derived in part: the caller is a stored thread blocked on reply
  (`replyCallerLinkageReciprocal`'s backward half) and differs from the
  answered caller (the two hold different reply objects). Its other two
  clauses (it is not the holder, and it holds no loan) are the stated coherence
  hypothesis `replyStacksSettleOnWaitingDonors` (`replyStackOuterCallerValid`),
  which the dispatch payoff already takes and which is not derived. Each
  refusal therefore stays as a defensive check, not deleted. *The
  coordinator's ruling (2026-11-26):* accepted for SX33. Deriving the two
  clauses from a chain invariant over `Reply.caller`, and stating that nothing
  is stored at the reserved id, is registered debt ("The reply pop's
  outer-caller guard rests on a stated hypothesis" in
  `docs/REGISTERED_DEBT.md`), owned by WS-SX with SX48 as its closure row.
  *The check, placed (SX33's second piece).* The arm's transition
  (`replyRecvTransferOnCore`) reads the pop's admission (`replyRecvPopAdmits`)
  on its entry state and refuses `.invalidArgument 0` before the reply leg
  writes. The admission is the pop's own commit test read ahead of the leg
  (the leg writes no context, no other frame and no binding, and keeps a head
  frame's links), with one term the leg's wake would change: the kept pop's
  outer caller must not be the answered caller (`keptPopOuterIsNot`). It is
  exact against the pop on the leg's state (`replyRecvPopDonation_ok_of_admits`,
  `replyRecvPopAdmits_of_pop_ok`, under `objects.invExt`), and each fast form's
  in-place guard implies it with no invariant (`ReplyRecvArm.Admits.popAdmits`,
  `ReplyRecvArm.LegAdmits.popAdmits`), so every `@[csimp]` stays unconditional.
  One refusal is new: a caller whose reply link names a frame other than the
  one answered (`replyRecvCallerFrameIs`) is refused, since the leg's removal
  would then edit that frame's neighbours, which the admission cannot read
  ahead. It is off the invariant (`replyCallerLinkageReciprocal`). The new
  refusal's code is `.invalidArgument 0`, the pop's own sentinel code; before,
  a pop refusal reported the pop's own error. *The refusal arms the general
  path keeps (the coordinator's ruling, 2026-11-26).* The admission
  implies the pop on the leg's state only under `objects.invExt`, because
  every read across a store at another key needs it
  (`RHTable.getElem?_insert_ne`), and `invExt` is a proposition the code
  cannot test. So the composite keeps its post-leg pop `.error` arm and its
  leg `.error` arm, and they run only on a state whose object table fails
  `invExt`: defensive checks, as SX29's fallbacks are. The fast forms' in-place
  guards make the same reads without `invExt`, so their equalities stay
  unconditional. *The owner's ruling (2026-11-26):* `objects.invExt` goes
  into the object table's type, as WS-CK's first row, CK1
  ([`REFUSAL_CHECKS_FIRST_PLAN.md`](REFUSAL_CHECKS_FIRST_PLAN.md)), on which
  the checks-first rows build. There every checks-first form gets its
  unconditional equality without an in-place guard, and the two arms above
  (the composite's post-leg pop `.error` arm and its reply-leg `.error` arm),
  which run only off `invExt`, are retired as unreachable by type. Nothing
  else in SX33 changes. *A refused receive (the ruling's option (b)).* A receive the
  kernel refuses after the reply step reports the nothing-received outcome
  (the priority-inheritance reversion, and the holder's deschedule where the
  pop returned a context, D53) on the state the receive returned. That state
  carries the receive's own context return (`receiveReturnSchedContext`),
  which seLe4n runs before the receive's checks and seL4 runs after
  `handleRecv`'s lookup. That is the only difference from seL4 for a receive
  refused after the reply step, and each such refusal is off the invariant.
  The receive capability's refusals (not found, wrong kind, no receive
  right) are reachable on invariant states. They never reach this case
  because the capability is checked on the entry state, before the reply
  runs, and faults the whole syscall there. That is a deviation, recorded
  in D63 and fixed by SX36. Deciding the receive's refusals
  first, before the context return (option (c)), needs frames across that
  return, each under `invExt`; it becomes cheap once `invExt` is in the
  table's type, and belongs to WS-CK's CK1 under the owner's ruling above. The post-receive donation refuses at its
  sentinel (`applyRendezvousCallDonation`, `.invalidArgument 0`, read up
  front) and inside the donation it performs (`donateSchedContext`: the
  context missing or not bound to the donor, the donor's thread missing, its
  push frame refused), each off the invariant; an earlier reading of this
  record said the sentinel was its only refusal, which D61 corrects. The receive's capability transfer never refuses
  (`receiveTransferCaps_ok`: an install that fails transfers fewer
  capabilities, as seL4's `transferCaps` does). *The signal arm.* A
  reply-receive whose receive completes its bound notification
  (`replyRecvCompletesSignalArm`) replies through the `.reply` arm's transfer
  (`replyTransferOnCoreChecked`, `endpointReplyCrossCoreDispatch`), whose pop
  (`applyReplyDonationOnCore`) and recorded-server sentinel refuse after the
  reply leg's writes and report the entry state. The admission above does not
  cover that arm. Those exits are off the invariant only; under the
  coordinator's ruling (2026-11-26) they are not SX33's work and are listed,
  with the admission design (the two sentinels read on the entry state, the
  pop's commit test read before `endpointReplyOnCore`), in WS-CK's CK2 row
  (class (d)) in [`REFUSAL_CHECKS_FIRST_PLAN.md`](REFUSAL_CHECKS_FIRST_PLAN.md).

- **D61. SX33 wrapped at its validated pieces; the refusal-carrying
  composite is SX34.** *SX33's measurement and the coordinator's ruling
  (2026-11-26), under the owner's D32 rule.* The composite's refusal-carrying
  form has to report the state each step stopped in. The reply leg and the
  receive leg already hand back the state they stopped in, so those cost
  nothing. The pop (`replyRecvPopDonation`, off `objects.invExt` only) and the
  post-receive donation (`replyRecvPostReceiveDonation`, its refusals off the
  invariant, D60) return no state on a refusal. Reporting the state they were
  handed keeps it live across them, and their first store then copies the
  object table on the success path of every general-path call whose pop or
  donation writes: a regression on a real path, so it is refused. The ruling:
  refusal-carrying forms of the pop and the post-receive donation, down to
  their stores, each returning its input where its refusal precedes its first
  write (so nothing is held) and carrying the state at that point where it
  follows one, become a new row, SX34, with the rest of the composite's report
  change (the refusal-carrying composite, the 12 wrappers carrying their
  callee's state, the report consumers' third case and the non-interference
  proofs restated), the general path's 1 MB cell and the C bound. The report
  change lands whole in SX34, not in part in SX33. SX33 keeps pieces 1 and 2
  (a refused reply lets the receive run; the pop's admission read before the
  reply leg), the nothing-received outcome (`replyRecvNothingReceived`) and
  the composite's entry-state reads taken before the reply leg
  (`endpointReplyRecvAnsweringOnCoreChecked`, an unconditional `@[csimp]`).
  Where SX34's donation forms reach code WS-CK's CK2 also owns, SX34 does it
  for the reply-receive path only, and CK2 cites it.
  - The rows after SX33 are renumbered (SX34–SX45 became SX35–SX46): the
    gate is SX35, the QEMU scenarios SX36, the lock-set ceiling SX45 and the
    closure SX46.
- **D62. SX34's donation is admitted before its first write.** *SX34's
  measurement and the coordinator's ruling (2026-11-27), the owner's
  checks-first ruling (as for the pop's admission, D60), so no new card.*
  `donateSchedContext` refused at four points after a store: the pushed frame
  named as its own predecessor, a frame below that does not resolve, and the
  donor's and the server's thread lookups. A refusal-carrying form carries the
  state at that point, a donation half done, and the report consumers' families
  that take only `objects.invExt` cannot refute it. The ruling: an admission
  (`donationPushRefusal?`) asks the three of those the state handed in can
  answer, on that state, before the first store, with the error the later check
  gives. The donor's lookup needs no admission: its key holds a thread, and no
  store before it writes a thread.
  - **The pair, under `objects.invExt`.** An admitted donation refuses only on
    the state handed in (`donateSchedContextR_stops_at_entry`, lifted to the
    rendezvous donation as `applyRendezvousCallDonationR_stops_at_entry`), and
    a donation that succeeds was admitted (`donationPushRefusal?_eq_none_of_ok`).
  - **The fast forms.** The in-place donation's guard implies the admission
    with no invariant (`donateSchedContext_eq_inPlace` discharges it from its
    own hypotheses), so every `@[csimp]` stays unconditional.
  - **The defensive checks.** The four checks after the stores stay. They run
    only off `objects.invExt`, and WS-CK's CK1 retires them.
  - **Scope.** The admission is in the shared `donateSchedContext`, so the
    `.call` and `.receive` donations are checked first too. On a state with a
    well-formed object table their results are unchanged. The admission refuses
    exactly where a later check would have, with the same error, because the
    stores before those checks write a context, Replies and the donor's thread
    at keys that hold no Reply the admission reads and no thread but the donor.
    That is a theorem (`donationPushRefusal?_some_exact`): on an
    `objects.invExt` state whose earlier checks pass and whose admission
    refuses, the donation as it stood before the admission (the context's
    store, the frame push, the donor's lookup and store, the server's lookup,
    then any continuation) refuses with the admission's error.
- **D63. ReplyRecv's receive capability is resolved after the reply, as
  seL4's `handleRecv` resolves it; the passive server stays current until
  the scheduling point.** *SX34's sixth session's finding and the
  coordinator's decision (2026-11-27), under the owner's standing rules (an
  seL4 deviation is fixed; rows stay bounded under D32). The current slot
  follows the owner card's recommended option; the card is still pending.*
  - **The finding.** A ReplyRecv whose reply is valid and whose receive
    capability is not found, of the wrong kind or lacks the receive right
    faults the whole syscall on the entry state. The reply never runs, and
    the caller stays blocked on it. The receive capability is resolved before
    the arm: the operand lookup and the receive gate in
    `dispatchOperandCheckedKW` (`RoutedArms/Report.lean`, `receiveRefusedAt`),
    the arm's slot checks in `replyRecvOperandArmThenTaintR`
    (`RefusalCarryingReplyRecv.lean`), and the fault delivered on the state
    the lookup was handed (`FFI.lean`, the lookup arm of the syscall
    dispatch). These refusals are reachable on invariant-holding states.
  - **seL4's order.** seL4-MCS's `case SysReplyRecv` (`src/api/syscall.c`)
    runs `handleInvocation` on the reply capability first and then
    `handleRecv(true, true)`. `handleRecv` looks the receive capability up on
    the state after the reply, and a failed lookup, a capability of the wrong
    kind or one without the receive right raises
    `seL4_Fault_CapFault(epCPtr, true)` through `handleFault` on the current
    thread. The caller has its answer by then.
  - **Corrections.** D51's record of the ruling said a refused receive
    reports the state after the reply. That is true of the refusals after
    the reply step (D60's option (b)), not of the receive capability's, and
    D51's text now says so. Its sentence that seLe4n's receive-side refusals
    are error returns predates SX3: the capability refusals are capability
    faults, and only the receive leg's off-invariant refusals are errors.
    D60's "every receive refusal is off the invariant" holds only because
    the capability check runs before the reply; D60 now gives that reason.
  - **The fix is SX36.** ReplyRecv's receive-capability lookup and gate move
    after the reply step, so a bad receive capability answers the caller and
    then delivers the capability fault on the post-reply state. The receive's
    flow gate still runs before anything the receive makes observable.
  - **The passive server's current slot.** Once the fix lands, a passive
    server whose pop hands its context back (the holder is the caller of
    ReplyRecv) and whose receive capability is then refused is a reachable
    case on invariant states. seL4's `schedContext_donate` leaves
    `ksCurThread` on the server and calls `rescheduleRequired`, and
    `handleRecv`'s fault runs on that thread. seLe4n's holder deschedule
    (`replyRecvNothingReceived`, `descheduleAtPlacement`) clears the core's
    current slot at once. SX36 keeps the server current until the scheduling
    point, as `rescheduleRequired` leaves it. The scheduling point then takes
    a current thread with no context off the core without re-enqueueing it.
    No invariant requires a current thread to hold a context, so the interim
    state is on the invariant. SX34's measurement of that cost is the basis
    of SX36's estimate.
  - **SX34 needed no interim form** (SX34's seventh session's finding, the
    coordinator's ruling of 2026-11-27). Until SX36, the third case of the
    report's consumers (a refused receive after a pop that returned a
    context) is reachable only off the invariant. Its holder states are not
    refuted from the run-queue and kernel-records consumers' premises, and
    they need not be: those consumers read the current thread, the endpoint
    heads and the caller's readiness only to deliver a capability fault, and
    the third case raises one only where the transition stopped in the state
    it was handed, where the consumers' first case applies
    (`ReplyRecvAnsweringEntry.capFault_none`: the reply's lookup faults only
    on a lookup's refusal, and the transition's refusals are lookups' only
    there, `replyRecvTransferOnCore_refusal_notLookup`). Every other branch
    takes the family's stage of the stopped state. No consumer restates its
    current-thread fact. SX36 still decides the current slot once a bad
    receive capability reaches the post-reply state, since that case is then
    reachable on the invariant.
  - **The lock set.** The receive capability's walk on the post-reply state
    can differ from the entry state's: the reply's capability transfer can
    install a capability in a slot that walk passes through, where the
    caller and the server share a CNode. The declared lock set must cover
    the post-reply walk. SX36 measures it, and it stops and reports if the
    entry footprint cannot cover the walk without a second lock acquisition.
  - **SX42.1's share.** SX42.1 runs ReplyRecv's receive on the state after
    its invoke phase. For a reply capability, that part is SX36's, and both
    rows say so. SX42.1 keeps the invoke phase on any other capability
    (the full `decodeInvocation` on `dest`), and NBSendRecv and NBSendWait.
- **D64. SX34 wrapped at its validated point; the install checked first and
  the C bound are SX35.** *SX34's measurement, under the owner's D32 rule
  (2026-11-27).* SX34 ran about nine sessions against its 4.5–5.5, past its
  stop line, so it lands where its validation is complete: SX34.1 (the pop's
  and the post-receive donation's refusal-carrying forms), SX34.2 (the
  composite and the 12 wrappers carrying their callee's state, the refused
  receive's report, the consumers' third case, the non-interference proofs
  re-checked over it with their statements unchanged) and SX34.3's readings. Two of its bounds are not met, and both
  move to SX35.
  - **The C bound.** `RefusalCarryingReplyRecv.c` is 12,966,427 bytes
    against 12,941,835: 24,592 over, 6,989 over SX33's 12,959,438 and
    21,953 over SX29's 12,944,474. It compiles in 485 s against about 480.
    Against SX33, per function: the arm's new report function
    (`replyRecvAnsweringReport`, 5,337 bytes, its boxed form 465 and its
    match splitter 1,029) adds 6,831; a new match splitter for
    `replyRecvReplyRefused`, compiled from a proof's split, adds 2,357. The
    operand and arm reports lose their reduced-arity copies as their
    parameters grow (702 and 467 bytes net), the general arm loses one match
    splitter (1,051), and each rendezvous wrapper shrinks by 344. The general
    path's arm (943,247 bytes) and the other arms keep their size: removing
    the holds does not shrink the C.
  - **The 1 MB cell.** On the general path the own-context reply-receive
    reads 87 cells, 4,776 bytes, with no 1 MB cell (110 cells, one of them
    1 MB, at SX29). The donating Call takes read no 1 MB cell, except the
    four forms that install a capability (short and long, unlinked and
    queued caller): each reads one 1 MB cell (1,052,672 bytes, the object
    table's copy), on both lanes, on the first call and in the steady state,
    at lr `0x40311910` (virt) and `0x311c78` (rpi5). The copy is the CNode
    store under `ipcTransferSingleCap`, called from `ipcUnwrapCapsLoop`
    under `receiveTransferCaps` in the reply-receive's receive body. It
    comes from `ipcUnwrapCapsLoop`'s `.error` fallback, which returns the
    loop's entry state after a refused install and so holds that state
    across the install. That is a class (d) hold in a specification body.
    SX34 exposed it and did not add it: before SX34 the composite's own
    copy of the state came first and masked it.
  - **The IR measurement** reads 1,494 holds against 1,498. The class (b)
    holds of `endpointReplyRecvAnsweringOnCore`, `replyRecvRendezvousR`,
    `replyRecvLongRendezvousR` (one each) and `replyRecvPopDonation` (two)
    are gone. The class (b) holds left are over the signal arm's reply legs
    (WS-CK CK2) and the receive-alone arm (class (a), WS-CK).
    `donateSchedContext` reads five against four: a class (e) read of the
    state after its stores, in the specification body, which SX34 did not
    change.
  - **Every other reading met.** Every heap reading is 0 on both lanes
    (4,490 per lane, the 312 retype readings aside); `test_full.sh`,
    `test_rust.sh`, the archive build and `test_qemu.sh` in both modes pass
    at the wrapped tree.
  - **The remainder** is a new row, SX35: the install checked first, so the
    loop holds nothing across it; `RefusalCarryingReplyRecv.c` brought under
    its bound by the Operations/Invariant split; and the release with both
    readings taken again. The rows after SX34 are renumbered (SX35–SX47
    became SX36–SX48): D63's receive capability is SX36, the gate SX37, the
    lock-set ceiling SX47 and the closure SX48.

## 4. Rows

Every row is one PR.
- It bumps the patch version and syncs the documents CLAUDE.md lists.
- It runs `test_full.sh`. When `rust/` changes, it also runs `test_rust.sh` and
  `test_aarch64_cross_build.sh`.
- It runs the QEMU exerciser gate (`scripts/qemu_exerciser_lib.sh`, the one
  site of the scenario names and heap pins).

Every Tier 3 anchor scoped to a file a row touches is swept before Tier 3
runs. Every reading a row does not name stays as it was. A sub-task's proofs
land in that sub-task.

### SX1 — Error payloads (D2, D2b, D3)

**LANDED at `v0.37.20`.** Payload fields are machine words (`UInt64`, seL4's
`word_t`), so a refusal is its discriminant and five payload words. The routed
entry report carries five word stacks beside its code stack, and the FFI words
entry hands a refusal on as those words; the error is rebuilt only in the
declassification ledger's records branch. The QEMU exerciser also runs
`failed-lookup-guard-mismatch`, which checks x1–x5; its MR4 (`bitsFound`) goes to the
buffer's `msg[4]`, which the scenario does not read.

The label is unchanged until SX45.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX1.1 | `LookupFault` (`invalidRoot`, `missingCapability bitsLeft`, `depthMismatch bitsLeft bitsFound`, `guardMismatch bitsLeft guardFound bitsFound`, seL4's `lookup_fault`). The D2 payload fields; `depthMismatch` retires into `failedLookup`. Every site sets its number: `invalidCapability` is `0` for the invoked capability and `i + 1` for argument capability `i`, and every argument capability (a receive's or reply-receive's reply capability included) is resolved through one boundary that applies it (`syscallLookupArgumentCap`, and `KernelError.argumentCapRefusal` in the compiled forms). The CNode-op refusals take seL4's: an empty source is `failedLookup true (missingCapability srcDepth)` (`cnode.c:111`). | The discriminant round trip over codes (`toDiscriminant`, `ofDiscriminant?`), the payload ignored; every `cases e <;> decide` restated per code. | `main_trace_smoke.expected` (error `Repr`); Tier 3 `KernelError` anchors; the `rust/sele4n-types/src/error.rs` mirror; `test_rust_conformance.sh` |
| SX1.2 | `errorFrame` carries the payload in seL4's MR order (x2–x5), with MR4 written to the caller's buffer `msg[4]` (D3) and the length as `setMR` returns it. Compiled refusal arms pass the payload unboxed (D2b). `syscallAbiVersion` 4 → 5. | `errorFrame_payload_roundtrip`. The error path's frame theorem restated: it changes only the caller's `msg[4]`, on a 5-word payload with a buffer. `errorFrame_x1_decodes` gains the length. | `syscall_return_abi.expected`; `abi_layout.expected` (version, payload offsets); `rust/sele4n-abi` frame decode |
| SX1.3 | **LANDED at `v0.37.21`.** A user word at or above `2^63` stays a word on the entry path. `RegValue` is a `UInt64` (`RegValue.word`, `.val` its `toNat`); the syscall number, the message info and the capability address are decoded from the word (`@[csimp]` `decodeSyscallId_eq_word`, `decodeMsgInfo_eq_word` and the router's `registerRoutedSyscallOf_eq_word`; `decodeCapPtr` reads the word as the address, and the `invalidCapPtr` refusal of a value past `2^64` it can no longer meet is deleted, its code 35 retired beside 37, no other code renumbered). The routed decodes test a range on the word before making a `Nat` (`wordLtNat`): the VSpace map and unmap's ASID and address and a map's permissions (`pagePermissionsOfWord?`), and an affinity (`SetAffinityArgs.affinityRaw : UInt64`, `decodeAffinity` on the word). A mint's badge is tested on its word (`badge.word = 0`). The fault and overflow words are read as words (`pairAddrIs`, `syncedWordFromW`, `@[csimp] syncedWordFrom_eq_w`). A configure refuses a budget or period above seL4-MCS's `MAX_PERIOD` (`UINT64_MAX / 8` ticks) with `rangeError`, as `decodeSchedContextConfigureArgsChecked` and `validateSchedContextParams` now do, and a deadline word above it with `invalidArgument 4`, so no stored budget, period or deadline reaches `2^63`. The raw-slot decodes that SX6.3, SX6.6 and SX44.1 re-decode, and the model-only calls SX7.1 re-encodes, keep their conversion; they are a registered row. | The register round trips restated on the word (`regMessageBody_word`, `regReplyRecvBody_word`, `regMessageRegs_word`); `setAffinityArgs` round trip without its word hypothesis; `decodeSchedContextConfigureArgsChecked_invariants` and `validateSchedContextParams_implies_wellFormed` gain the bound; `cspaceMintPerformAt_eq_impl` on the badge word; the routed receive and reply-receive decode theorems on `replyAddr.word`. | QEMU: `vspace-map-wide-asid`, `vspace-map-wide-vaddr`, `vspace-map-wide-perms`, `vspace-unmap-wide-vaddr`, `tcb-set-affinity-wide`, `mint-wide-badged-notification` (now measured), `configure-wide-budget-and-period`, `configure-wide-deadline`; `configure-zero-budget-max-period` and `configure-budget-over-wide-period` now expect the `MAX_PERIOD` refusal |

**Acceptance (QEMU):**
- `range-error-payload`: Copy with depth 65 returns MR0 = 1, MR1 = 64.
- `failed-lookup-depth-mismatch`.
- `failed-lookup-missing-source`.
- Each reads 0 heap cells.

### SX2 — The guard in the capability, and `resolveAddressBits` (D4, D5, D17)

**LANDED at `v0.37.23`.** The compiled resolver recurses only for the
capability and the bits where the walk stops (`resolveAddressBitsWalk`) and
answers that level with the caller's continuations (`resolveAddressBitsLevel`),
so a refused second-capability lookup builds no result on the heap. The QEMU
heap gate also runs the five second-capability guard-mismatch refusals
(`receive-reply-cap-`, `reply-recv-reply-cap-`, `configure-sched-context-`,
`set-space-root-` and `bind-notification-guard-mismatch`), `cnode-mint-guardless`,
`cnode-multi-level-copy`, `cnode-mint-unbadge-refused` (data zero) and
`set-space-root-data`/`-refused` beside the acceptance scenarios below.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX2.1 | One sub-task, because neither half compiles alone. **Capability:** `Capability` gains `cnodeGuard` and `cnodeGuardSize`; `CNode` loses `guardWidth`, `guardValue` and `depth`; the boot configs move each guard into the root capability (D5). **Resolver:** `resolveAddressBits (nodeCap) (cptr) (nBits) : Except LookupFault (SlotRef × Nat)` follows `cspace.c:126`: InvalidRoot; the guard checked before the depth; a stop at a non-CNode capability. `lookupSlot` resolves at 64 from the TCB's root capability. `lookupSlotForCNodeOp` follows `cspace.c:64`. **Deleted with their theorems:** `resolveCapAddress`, `resolveCNodeOpAddress`, `resolveCNodeOpSlot`, `resolveCNodeOpSrcRoot`, `cspaceResolvePath`, `cspaceLookupPath`, `cspaceLookupMultiLevel`, `CNode.resolveSlot`, `ResolveError`, the old K forms and `SyscallGate.capDepth`. IPC extra capabilities use `lookupSlot`, still at the rendezvous. | The resolver family restated: congruence, valid CNode, guard reject/match, `resolveAddressBits_callers_check_rights`. The new K forms by `@[csimp]`. Termination on bits, from a carve fact (radix ≥ 1). `cnodeCapGeometry` (guardSize + radix ≤ 64, guard < 2^guardSize) replaces `cspaceDepthConsistent` as the fourth conjunct of `capabilityInvariantBundle`, the position `cspaceDepthConsistent` held, so no other conjunct is re-indexed. Every lock footprint over the root's geometry re-derived. | Tier 3 :4106, :8371, :10988, :11350–:11355, :23522; `main_trace_smoke.expected` |
| SX2.2 | `Fault.capFault` carries a `LookupFault`. `faultMessageLength` becomes 4–7, at seL4's `seL4_CapFault_*` offsets. `ThreadFaultWords.lookup` becomes two words. | The fault encode/decode round trip and `faultLabel` theorems restated. `syscallCapFaultOf` agrees with the arm's refusal. | `fault_handling_4core.expected`; the fault Tier 3 anchors |
| SX2.3 | `updateCapData` (`objecttype.c:395`) under Mint (D17), the parent's kind read from the store (`capDataKind`), and SetSpace's CSpace root guard from `cspace_root_data` through it, never copied from the source. | `mintDerivedCap_rebadge_refused`; `cnodeCapGeometry` kept by Mint and by SetSpace. | `main_trace_smoke.expected` |

**Acceptance:**
- `cap-fault-guard-mismatch`: the handler reads 7 words.
- `lookup-stops-at-non-cnode`.
- `cnode-mint-guard`: a two-level CPtr resolves through a minted guard.
- `cnode-mint-rebadge-refused`.
- Every existing `cap-fault-*` scenario at its new length.

### SX3 — Receive-side refusals are capability faults (F1)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX3.1 | **LANDED at `v0.37.24`.** The wrong-kind and missing-right faults were already the lookup's (`receiveGateRefuses`, scenarios `receive-wrong-type-cap-fault`, `wait-wrong-type-cap-fault`, `reply-recv-wrong-type-cap-fault`, `receive-no-right-cap-fault`); a notification bound to another thread now joins them (`receiveBoundRefuses`, `notificationBoundElsewhere`), checked in the lookup gate and again in the wait arm after the flow check. Recv and Wait answer `CapFault(cptr, inRecv)` with `missingCapability 0` for each of: a capability of the wrong kind, a missing receive right, or a notification bound to another thread (`syscall.c:470`–`:513`). | `capFaultReceivePhase?` partition restated. Every receive arm returns no error frame but the two that SX4 and SX43 retire. | `fault_handling_4core.expected`; `main_trace_smoke.expected` |
| SX3.2 | **LANDED at `v0.37.24`.** `lookupReplyCap` is seL4-MCS's `lookupReply`: a failed lookup is its own lookup fault, a slot that holds no usable reply capability `missingCapability 0`, and the receive and reply-receive refuse with `failedLookup` carrying it. `syscallCapFaultOf` raises it as `CapFault(replyCPtr, true)` when the reply capability's lookup, re-run on the refusal's state, fails with that fault (`receiveReplyFaults`); the compiled entry re-runs the same lookup in place (`lookupReplyCapK`, `replyLookupRefusalW`) and reports the fault under report kind 3. The argument-number refusals of the reply capability are deleted. A reply object that is not free (SX4) and a reply-receive with no caller (SX7.2) keep their error frames until their rows. A failed reply-capability lookup on a receive faults, as `lookupReply` does (`syscall.c:387`). This closes the note at `SeLe4n/Platform/FFI.lean:3073`. | `syscallCapFaultOf` covers the reply lookup. | the same |

**Acceptance:** `recv-wrong-kind-faults`, `recv-no-read-right-faults`,
`reply-recv-bad-reply-faults`. Landed as `receive-wrong-type-cap-fault` and
`receive-no-right-cap-fault` (already present), and `receive-reply-cap-guard-mismatch`,
`reply-recv-reply-cap-guard-mismatch`, `receive-reply-cap-wrong-kind`,
`reply-recv-reply-cap-wrong-kind` and `wait-notification-bound-elsewhere`, each
delivered to the handler in the receive phase with its address and lookup
failure type.

### SX4 — The Restart thread state

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX4.1 | **LANDED at `v0.37.27`.** `ThreadState.Restart` is a state of its own. A cancelled IPC sets it: the endpoint, notification and reply-blocked arms of `cancelIpcBlocking` (`restoreToReadyCancelled`, now `TCB.restoredToRestart`) and `cancelAllIPC`'s waiters (`cancelledEndpointWaiterTcb`); a `cancelAllIPC` waiter carrying a fault is left `Inactive` with the fault kept, as seL4's `restart_thread_if_no_fault` leaves it (`storeEndpointWaiterFaulted`). The restart PC is written when the thread leaves its blocked state, not at activation: the model has one program counter (seL4's `NextIP`), and a rewind at activation would also rewind a Resume of a thread that was not in a system call, where seL4's `FaultIP` equals `NextIP`. `TCB.restartPc` is seL4's `getRestartPC`: the `SVC` (`pc - 4`, as `lel_syscall` stores `ELR - 4`) for a thread blocked in a system call, and the recorded `faultIp` for one blocked on its fault handler. So the thread resumes at the `SVC` with its own arguments and re-issues the call, and its user-visible PC is seL4's `FaultIP` throughout. `ipcCancelled` and its frame (`cancelledIpcFrame`, `stageCancelledIpcFrame`) retire; discriminant 57 is reserved (`retiredDiscriminants`). **A receive on a busy reply cancels its holder**, as seL4-MCS `receiveIPC` runs `cancelIPC(replyTCB)` (`endpoint.c:152`): when the reply the receive presents is linked to another caller, or stashed by another receiver that still waits (`busyReplyHolder?`), and the receiver flows to that thread, the receive arm cancels the holder's IPC in place (`cancelRecvBusyReply`, `cancelReplyHolder`: the suspend's cancel and priority revert, then `Inactive`, as `cancelIPC` leaves it) after its checks and before it receives. The cancel commits as seL4's does: a refusal after it reports the cancelled state (`cancelReceiveBusyReply`), and compiled = specification holds with no condition. The receive's lock footprints name the cancel's writes (`lockSet_receiveCancellingHolder`, `schedLockSet_receiveCancellingHolderOnCore`), and every entry family composes across it. The cancel keeps `ipcInvariantFull` (`cancelReplyHolder_preserves_ipcInvariantFull`, over the head cut's `cutCancelledCallerHead_preserves_ipcInvariantFull`, taking the teardown's queue-connectivity premises at the holder as `cancelIpcBlockingOnCore_preserves_ipcInvariantFull` takes them), and under the same premises the receive refuses nothing after it (`cancelReplyHolder_frees_reply`, `resolveRecvReplyId_cancelRecvBusyReply`). The staged dispatch payoff keeps its scope at a receive whose reply is not busy (`recvReplyNotBusy`): its receive-stage fields describe the state the dispatch is handed, and a busy reply's receive runs on the cancelled state. **Suspend of a thread already `Inactive` succeeds and writes nothing**, as seL4's `suspend` (`suspendThreadOnCore_of_inactive`), where the model refused `illegalState`; the compiled suspend admits it and hands the state back (`suspendPerform`, `suspendThreadOnCore_of_admitted`), so the entry allocates nothing. The frozen suspend cancels a blocked thread through the same `TCB.restoredToRestart`, so the frozen restart resumes it at its `SVC`. | `restoredTcb_eq` names the restart's two fields; `restoreToReadyCancelled_restarts`; `restoreToReadyCancelled_then_switch_resumes_at_restartPc`; the cancellation staging theorems restated over `restart : Bool`. | `smp_ipc_4core.expected`; `main_trace_smoke.expected`; Tier 3 `ipcCancelled` anchors |
| SX4.2 | **LANDED at `v0.37.27`.** Suspend leaves a blocked victim `Inactive` with its PC at its restart PC (its cancel moves it, then G6 writes `Inactive`), and Resume sets `Restart` (seL4's `restart`): `resumeReadyMidState`, `resumeThreadReady`. Resume is seL4's `restart` throughout (`restartThreadOnCore`): it acts only on a stopped thread (`isStopped`), so a thread that is neither `Inactive` nor blocked is left as it is with no error, and one blocked in an IPC has the IPC cancelled through the suspend before it is resumed; the frozen resume follows the same arms, and the frozen suspend cancels the blocking in every arm as the live one does (`frozenCancelIpcBlocking`; the `.tcbSuspend` agreement branches compare it whole). | `resumeReadyMidState_getTcb?_restart`, `resumeThreadOnCore_sets_threadState`, `restoreToReadyWithWake_sets_threadState`. | the same |

**Acceptance:** `cancelled-send-restarts` (a deleted endpoint under a blocked
sender; the restarted send faults), `suspend-resume-restarts`.

### SX5 — The boot builds the root task's IPC buffer (D13, D14, D15)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX5.1 | **LANDED at `v0.37.31`.** `PlatformConfig.rootServer`, supplied by the binding (`PlatformBinding.rootServerFor`, bound by `bindPlatformConfig`): four pages directly below the last boot RAM extension's region map (`rootServerBaseOf`, `rootServerReservationOf`). The sixteenth `wellFormed` conjunct `rootServerPlaced` (its own diagnostic row) holds the memory (`rootServerMemoryPlaced`: in one `.ram` region, clear of every untyped, `kernelReserved`, `kernelDevices` and every region map), the thread (`rootServerTaskPlaced`: empty buffer slot, four empty root CNode slots, a VSpace root with its table page), fresh object ids and a page-aligned user buffer address; the object budget counts the four objects. The last extension's untyped stops below the reservation (`untypedExtentsOf`, `untypedExtentBelowRootServerOf`), and the boot hands the HAL those parts as the RAM each region map describes. `region::thread_ram_covered` decides through the pure `region::thread_ram_admitted`, which admits the reservation. `PlatformConfig.withoutExtents` erases the reservation's memory too. | The `virt`, exerciser and RPi5 layout theorems (`qemuVirtRegionMap_layout` extended); `rootServerPlaced` decided per config. | `boot_map.expected`, `boot_map_qemu_virt.expected`; `test_aarch64_cross_build.sh` |
| SX5.2 | **LANDED at `v0.37.31`.** `TCB.ipcBufferSlot` (slot 2 of `spaceCells`); every slot reader, invariant and teardown covers it. | Every slot invariant over the third slot (`capTargetKindBacked`, the derivation links, `bootDerivationTreeSound`). | Tier 3 slot anchors |
| SX5.3 | **LANDED at `v0.37.31`.** `installRootServer` (`Platform/Boot/RootServer.lean`) runs after `installIrqNodes` and before `linkBootCapabilities`, seL4's `create_ipcbuf_frame_cap` and `create_it_pt_cap`, and records the eight writes it owes (four page scrubs, three table descriptors, the buffer's page descriptor). Every hardware entry passes the HAL's performer (`completePhysicalWrites`) to the boot wrapper, which performs them and installs the drained state (`drainBootPhysicalWrites`), and the host and simulation entries refuse a boot that owes writes; the HAL prints the count at Phase 5. | `proofLayerInvariantBundle_of_bootShape` reproved: the vspace bundle, one recorded live mapping, lifecycle and bookkeeping, the capability bundle, untyped disjointness with the reservation, TLB and icache quiescence. `bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle`. | Tier 3 Boot.lean :3960, :3963 and the `bootSafeObjectCheck` anchors; `qemu_lean_boot_expected.txt` |
| SX5.4 | **LANDED at `v0.37.31`.** Deleted, with the exerciser's IPC-buffer pages, untyped, slots and tile theorem; the root CNode no longer holds an untyped for the buffer. No boot census was numerically pinned: the QEMU lane's census check is relational (the install allocates, with the heap's invariants intact). The boot's owed writes are pinned instead (`BOOT_WRITES`, eight on both platforms). | none (deletion) | Tier 3 negative anchor on the deleted names; `qemu_lean_boot_expected.txt` `BOOT_WRITES` |

**Acceptance:**
- `root-ipc-buffer-at-boot`: the first syscall's overflow word is read from the
  boot-built buffer.
- `root-ipc-buffer-cap`: an Unmap and remap round trip.
- The census re-pinned on both platforms' boot.

### SX6 — Capability arguments as extra capabilities (D6–D12)

`lookupExtraCaps` (`tcb.c:386`) runs in the dispatch prologue, as seL4's `handleInvocation` runs it: after the invoked capability's `lookupCapAndSlot` and before `decodeInvocation` (SX6.1).
- A failed lookup is `CapFault(that cptr, send phase)`.
- The receive-phase syscalls look none up; in SysReplyRecv a failed lookup skips the reply half with no fault.
- A missing extra capability is TruncatedMessage.
- A capability of the wrong kind is `invalidCapability (i + 1)`.
- IPC transfers still look their capabilities up at the rendezvous (`thread.c:213`).

Every sub-task re-derives `maxLockSetSize` for the lookup paths it adds.
SX6 routes and measures the 22 invocation arms that still fall back to `dispatchInvocationBy` on refusal, so each refusal reads 0.
SX6 also renumbers argument capabilities and words to seL4's operand layout, and owns the last open numbering items:
- SetSpace's CSpace root becomes argument 2 and its VSpace root argument 3, because the MCS fault endpoint is argument 1.
- The Untyped_Retype and IRQControl_Get destination lookups become `FailedLookup` with their depth operand.
- Page_Map's invoked and argument capabilities follow seL4: the frame capability is invoked, and the VSpace is extra capability 0.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX6.1 | **LANDED at `v0.37.32`.** seL4's `lookupExtraCaps` in the dispatch prologue (`handleInvocation`): for every invocation, after the invoked capability resolves and before decode and the type and right checks, the message's extra capabilities are looked up from the caller's IPC buffer `caps_or_badges` words (`lookupExtraCaps`, its allocation-free entry form `extraCapsLookupK`). A failed lookup raises `CapFault(that cptr, false)`, delivered through `deliverSyscallLookupFault` at the failing address. The receive-phase syscalls skip it (`handleRecv`). In SysReplyRecv a failed lookup skips the reply half with no fault, and the receive still runs (`handleInvocation` with `isBlocking = false` on the reply capability). An empty invoked slot is no lookup failure (`lookupCapAndSlot` hands the null capability on): the extra capabilities are looked up first, then `decodeInvocation` refuses it with `seL4_InvalidCapability`, an error and no fault, except in the receive phase (`handleRecv`); this is the empty-slot half of SX7.2's lookup rule, brought forward because the prologue fixes its order. A declared lock footprint covers every lookup the prologue makes, because the gate is declared only for a single-level root. | `syscallInvokeTyped_ok` (and `_extraCaps`); `dispatchSyscallChecked_extraCaps_before_null`; `abiEntryGate_lookupSlot_root`; `syscallCapFaultAt` and `syscallCapFaultOfW` at the failing address; `syscallEntryCheckedK_outcome_eq`; `extraCapsLookupK_eq`. | QEMU allocation gate: every non-carve reading 0 |
| SX6.2 | **LANDED at `v0.37.32`.** CNode Copy, Mint and Move: `srcRoot` is extra capability 0, and the words follow seL4 (D12); `CNodeOpWord` retires. | The decode round trips and `_error_iff`; the `capFaultReceivePhase?` send-phase case; the CNode arms' preservation. | `abi_layout.expected` (`cnodeCopyBit` block out, caps base in); `sele4n-abi` `args/cspace.rs`, `encode.rs` |
| SX6.3 | **LANDED at `v0.37.32`.** Untyped_Retype (D9) — a window of up to `CONFIG_RETYPE_FAN_OUT_LIMIT` objects, configured at 26 and derived from the lock ceiling (`retypeFanOutLimit := maxLockSetSize - retypeBaseLocks`), every refusal read before the first carve (`untypedRetypeWindow_admitsEveryCarve`), IRQControl_Get (D10), PageTable_Map, Page_Map on the frame capability (D6). The retype's object id, IRQControl_Get's line and PageTable_Map's address are read on the word (`windowWordOf`, `wordLtNat` before any `Nat`); a line past the board's last is seL4's `RangeError(0, maxIRQ)` and a table address past the user top seL4's `InvalidArgument 0`. | The retype loop's carve theorems; the map arms' preservation; the mapping-record stage; the retype, IRQControl_Get and PageTable_Map round trips below `windowWordBound`. | `args/lifecycle.rs`, `args/vspace.rs`; QEMU: `untyped-retype-wide-child-id`, `irq-control-get-wide-line`, `page-table-map-wide-vaddr` |
| SX6.4 | **LANDED at `v0.37.32`.** SetPriority and SetMCPriority with an authority TCB (D11); BindNotification; SchedContext_Bind; SchedControl_ConfigureFlags; IRQHandler_SetNotification. | The MCP authority theorems restated over the authority capability. | `args/tcb.rs`, `args/sched_context.rs` |
| SX6.5 | **LANDED at `v0.37.32`.** SetSpace in the MCS shape: the fault endpoint, CSpace root and VSpace root as extra capabilities 0–2. A TCB fault-handler slot (D8). `tcbSetFaultHandler` retires. Fault delivery reads the slot, and answers `missingCapability 0` when it holds no endpoint (`faulthandler.c:99`). A CSpace or VSpace root argument whose slot is empty or holds no object capability gets seL4's answer for it, where SX1 still answers `invalidCapability` through `resolveCallerCapSlot`. | The fault-delivery family over the slot; the slot invariants; `cnodeCapGeometry` kept by SetSpace. | `fault_handling_4core.expected` |
| SX6.6 | **LANDED at `v0.37.32`.** SetIPCBuffer: the frame capability is derived into SX5.2's slot (D7). Every buffer read goes through `lookupIPCBuffer`. `ipcBufferWordPAddr?` and `tlbFillIpcBufferOnCore` retire. The buffer address is read on the word (`ipcBufferAddrOfWord`), keeping its zero-ness and page offset, the only parts the kernel reads. | Every theorem citing the retired read, restated over the frame capability. The buffer-in-one-frame fact taken from the capability. `ipcBufferAddrOfWord_eq_zero_iff`, `ipcBufferAddrOfWord_mod_page`. | Tier 3 IPC-buffer anchors; `syscall_return_abi.expected`; QEMU: `tcb-set-ipc-buffer-wide-unaligned` |
| SX6.7 | **LANDED at `v0.37.32`.** The model-only calls get invocation targets of their own, so SX7's labels never select an operation on an endpoint or a notification (seL4: Send/Call on an endpoint is IPC and Send on a notification signals, whatever the label). `declassify` and `declassifySignal` are invoked on the `.auditTrail` capability, with the object or the notification as extra capability 0. A service-registry capability type is the target of `serviceRegister`, `serviceRevoke` and `serviceQuery`, with the endpoint as extra capability 0. Depends on SX6.2. | The service and declassification arms' preservation and non-interference restated over the new target and the extra capability. | The service and declassify QEMU scenarios re-encoded at their pins |

**Acceptance:**
- `extra-cap-lookup-fault`.
- `extra-cap-missing-truncated`.
- `extra-cap-wrong-kind`.
- `retype-num-objects`.
- `set-priority-authority`.
- `fault-handler-not-endpoint`.
- `set-ipc-buffer-frame-cap`.
- the service and declassify scenarios on their new targets.

### SX7 — seL4's syscall set and invocation labels

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX7.1 | **LANDED at `v0.37.33`.** **Labels:** Call or Send on a kernel-object capability selects its operation by the message label, numbered as seL4's generated `invocation_label` for aarch64 MCS. Model-only calls (service, audit, declassify, `mintReplyCap`, and `tcbSetAffinity`, which seL4-MCS does not have) take labels after seL4's last (56, `ARMIRQIssueIRQHandlerTriggerCore`). **Retired with the numbers:** `untypedReset`, whose reset seL4 performs inside `Untyped_Retype` (`resetUntypedCap`), as the model's carve already does (`retypeFreeIndex`). **Error delivery:** only Call receives an error; Send discards it (`syscall.c:371`). **Retired:** the per-operation syscall numbers. | The decode round trips; seam coverage per (capability type, label); the lock footprints per label; the dispatch non-interference cases; `#assert_decoder_arities`. | `abi_layout.expected` (the label table); `rust/sele4n-abi` `SyscallNumber` and labels, and the `sele4n-sys` wrappers; `check_live_arm_per_core_routing.py`; `main_trace_smoke.expected` |
| SX7.2 | **LANDED at `v0.37.33`.** The IPC syscalls become seL4-MCS's 11 (Call −1 … Yield −11, `syscall.xml`, order kept). Signal is Send on a notification; a reply is Send on a reply capability. `.reply`, `.notificationSignal` and `.notificationWait` are retired from the ABI: no register value names them, and the kernel selects each internally by the invoked capability's type after the lookup (Send, NBSend or Call on a reply capability; Send, NBSend or Call on a notification; Recv, NBRecv, Wait or NBWait on a notification), as seL4's `decodeInvocation` and `handleRecv` select `performInvocation_Reply`, `sendSignal` and `receiveSignal`. NBSend, NBRecv, NBWait, NBSendRecv and NBSendWait are added. A failed NBSend lookup is silent; NBRecv does not block. A ReplyRecv with no caller to answer replies to no one and still receives, and Recv on a notification and Wait on an endpoint follow `handleRecv`'s capability-type switch (left by SX3.2). SX7 also settles the invoked capability's two failures as seL4's `handleInvocation` (`syscall.c`) does: a failed lookup of the invoked capability (`lookupCapAndSlot`) is a capability fault on the blocking Send and Call and is dropped on NBSend, and an empty slot, which the lookup answers with a null capability, is `decodeInvocation`'s `seL4_InvalidCapability` error, delivered only to Call (`syscall.c`, `if (isCall) replyFromKernel_error`). The error itself landed in SX6.1; this row keeps its delivery only to Call. | `registerRoutedSyscall` and `syscallReadsOverflow` restated; the `capFaultReceivePhase?` partition; the IPC bundle for each NB arm. | the same; `syscall_return_abi.expected`; `smp_ipc_4core.expected` |
| SX7.3 | **LANDED at `v0.37.33`.** Recv, ReplyRecv and NBSendRecv read the reply capability from x6 (`replyRegister`). | The routed-decode theorems for the receive arms. | `abi_layout.expected` (`register reply x6`) |

**Landed beyond the three rows, at `v0.37.33`** (each a seL4 behaviour the
rows' ABI exposed): Page_Unmap is invoked on the frame capability with no
message words (`vspaceUnmapFrameCap`), and Page_Map onto an entry in use
answers `seL4_DeleteFirst` (`mappingConflict` retired); a syscall writes only
the registers seL4 writes (a Send, NBSend or Yield returns the caller's own
words, message delivery writes only `copyMRs`'s registers, a signal wake only
the badge register, and the value-returning invocations reply only on Call); a
capability fault is dropped by seL4's phase rule (`syscallDropsFault`); a
receive, and ReplyRecv's receive, complete the thread's active bound
notification first (`receiveIPC`); a Call that links no reply (no reply object
waiting, or a sender without Grant and GrantReply) delivers its message and
leaves the caller `Inactive` (`sendIPC` / `receiveIPC`), and a Call whose caller
has no TCB is refused `objectNotFound` on every arm; SchedContext_Bind takes a
notification capability (`schedContext_bindNtfn`), SchedContext_Unbind refuses
the executing core's current thread's context and unbinds the notification
(D18), finalisation clears the link at both ends, and the retire guards read
it. The rest of the piece moved to SX8 and SX39–SX42 (D20).

**Acceptance:**
- The whole exerciser suite re-encoded, at its current heap pins.
- `nb-send-bad-cap-silent`.
- `nb-recv-empty-returns`.
- `send-invocation-error-discarded`.

### SX8 — Notification scheduling-context donation, and the seL4 conformance table

Moved out of SX7 when it closed (owner's decision of 2026-11-19, "Close and
split"). SX7 landed the two link fields (`Notification.schedContextCode`,
`SchedContext.notificationCode`), SchedContext_Bind on a notification
capability, SchedContext_Unbind as seL4-MCS runs it (D18), the finalisation
clears of both ends, and the retire guards that read the link words; this
phase finishes the piece. SX8.1's table is the reference every later row
checks its operations against.

**Status: landed at `v0.37.36`.** SX8.3's restatement of `donationOwnerValid`
turned out to be unnecessary for the unbind: the invariant constrains
`.donated` holders only, and `donationChainWellFormed` constrains stacks from
the contexts that head them, so the state the unbind leaves (the holder
unbound, its caller blocked on a reply no context heads) was already admitted,
as context finalisation already reached it. The unbind and the finalisation
share one `schedContextUnbindReply` (`SchedContext/ReplyLink.lean`). Beyond
the three sub-tasks the row landed, under D25–D30: the lenders' flow invariant
`contextLendersFlow` carried by every entry, with the lend and bind checks in
static form (D27, D28); seL4's held `reply_pop` arm on every pop site, in
place, a bound holder kept bound and `donationOwnerValid`'s owner clause
relaxed from `.unbound` to "not donated"; destroy unbinding a donated context
as `schedContext_unbindTCB` does; SchedContext_Bind's two refusals lifted under
D25's label rule; the retired donation cancellation deleted and the suspend
footprint narrowed; and the notification lend at equal labels (D30). Its
remainder is SX9, SX12 and SX25 (D32).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX8.1 | **The seL4 conformance table** (D21). One row per invocation label and per syscall: the registers and IPC-buffer words read, the registers written on success and on each error, the seL4 error codes with their payloads, and whether it blocks, each sourced from the seL4 source (the decode and perform function, file and line, of the aarch64 MCS tree). It is held in code or test data (a Lean table under `SeLe4n/Testing/`, or a fixture a producer emits), never in a `.md` file. A Tier 2 suite checks every row against the decode (`decodeSyscallArgs` and its arities, `truncationMinimum`, the register reads), the selection (`Syscall.selectOperation`) and the return (`syscallReturnShape`, the error frame), so a row that changes an operation changes its table row in the same PR. Also moved here from SX7.1: the word-first decodes the debt register's raw-slot row still holds open at its families (2) (`mintReplyCap`'s two slots) and (7) (the service register's interface id), each testing the word before any `Nat` is made. | The table's agreement with the decode and the return shape, decided over every row. The two decodes' round trips below the word bound. | the new suite; QEMU: a word `≥ 2^63` in each of the two decodes, held to 0 |
| SX8.2 | **Donation and return** (consumes SX8.1's rows for Signal, Wait, Recv and SchedContext_Bind). seL4's `maybeDonateSchedContext` in `completeSignal` and in `sendSignal`'s waiter and bound-thread wakes, recorded as the woken thread's `.bound` binding with the notification link kept on the context (D19). **Chokepoints:** the receive and the Wait share `completeSignalArm` and its fast form `notificationWaitGatedR`, once `dispatchWithCapChecked`'s `.notificationWait` arm calls `completeSignalArm` instead of inlining its body (a pure refactor, landed first in the row); every signal (the Signal syscall, `declassifySignal`, IRQ delivery) runs `notificationSignalBoundOnCore` and its in-place form, so the donation lands there, after the wake. **Donation** is `schedContextBind`'s ok-state with a refusal as the identity (`maybeDonate st nid tid`): wake first, then donate, so the bind finds the thread placed and its only scheduler write is the home core's release; the fast form is `schedContextBindAdmitted` / `schedContextBindPerform` under a word guard, `@[noinline]`, the ids passed as `Nat` codes. **Return** (`maybeReturnSchedContext`) runs only on a blocking receive: Wait's block branch, and receiveIPC's blocking path with a bound notification, before the endpoint switch, so it runs even when a sender is then found. It clears the thread's binding and `sc.boundThreadCode`, keeps the notification link, and requests a reschedule if the thread is current. After Wait's block `schedContextUnbind`'s ok-state is the specification; a receive that does not block needs its own operation, since that state clears the running core's current slot. **Decided in the row:** (1) `notificationWaitOnCore_confinedToCores` is `{executingCore}` and the donation's release writes the waiter's home core: prove the thread homed on the executing core at the call site, or widen the write and lock sets by the context and its home core's run and replenish queues; (2) non-interference: `boundSignalHidden` gains the context, and the bind gets a real projection frame (`schedContextBind_preserves_projection` is a closure-form tautology); (3) `notificationWaitOnCore_consumed_scheduler_eq` stays the wait's, and the arm's scheduler change is the bind's. | Each family's arm lemma is the old one composed with the bind's: run-queue stage, readiness, kernel-records frame, mapping-record stage, key frame and step coverage, saved registers, `ipcInvariantFull` (with `schedContextBindingBidirectional` and not-an-owner at the intermediate state), cross-core non-interference, slot confinement; the lock sets name the context and its core's queues. | QEMU: donation on a signal to a waiter, on a bound wake and on a receive that completes a signal; return on a blocking Wait and a blocking receive; every reading 0 |
| SX8.3 | Label 36 `SchedContext_UnbindObject` (the thread or notification capability as extra capability 0). **Unbind of a donated holder** with seL4's `unbindReply` (D22): the unbind succeeds, the reply link is cleared, and `donationOwnerValid` is restated so that a chain may be cut. The frozen twins: `frozenSchedContextBind` on a notification, and `frozenSchedContextUnbind`'s notification half and its success on a context bound to no thread. The link-agreement invariant (template `yieldLinksAgree`, `SchedContext/YieldLinkInvariant.lean`; the retire guards already give an erased object both words 0). | The invariant's preservation over every transition that writes either word; frozen agreement for the two twins. | `frozen_ops_suite` rows; QEMU: UnbindObject on a thread and on a notification, at 0 |

**Acceptance:** the conformance suite passes over every label; each donation
and return path above measured at 0; `sched-context-unbind-object`.

### SX9 — Notification-lend assurance

SX8's remainder on the lend's evidence (D32). No transition changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX9.1 | **LANDED at `v0.37.38`.** **The two-run theorem for every observer** over the checked notification lend (`maybeDonateSchedContextFlowing`, D30). An observer the context's label does not flow to: the single-run `maybeDonateSchedContext_lowEquivalent` (`InformationFlow/PerCoreSchedulerNonInterference.lean:1956`) closes it, given that the woken thread is hidden (a thread/object label coherence fact). An observer cleared for the context (so, by D30, for the thread): the lend's writes are visible, and the projection erases the inputs that decide it (`Notification.schedContextCode`, `InformationFlow/Projection.lean:371`; `TCB.scBinding*`, `:214`). **Ruled by the owner (D34):** a finer projection for that observer, which shows those words. The lend's visible writes read three more inputs, ruled when the row started: the thread's `cpuAffinity` (which core it is placed on) is shown with the binding words to an observer cleared for the thread, as D34's principle gives; the machine timer (the context's `releaseReadyHead`) stays outside the projection (covert channel CC-2), and the theorem takes the two runs' agreement on it as a premise, as the tree's one two-run theorem over an unprojected read does (`activateThreadOnCore_lowEquivalent_pair`); the thread's run-core word is read off the run-queue refinement invariant. The NI theorems that were unconditional only because the projection erased those words (the donation push, pop and keep, the Call donation, the affinity write: WS-RR RR7.22, WS-OD OD3.2 and OD4.1, WS-SM SM5.H.4) are restated with the observability hypotheses they need, superseded by D34; each consumer step discharges them from the flow gates it passes (D27, D28, D30), or, where the step makes a legitimate visible flow, is proven in the two-run form with the pair lemmas. **One consumer could not be discharged** (D36): the receive's no-sender path (`endpointReceiveDual_preserves_projection`: `cleanupPreReceiveDonation`, then `popHeldReplyHead`, then return or keep) hands a hidden receiver's loaned context back to its owner, and no gate relates the receiver's label to the context's. It takes the per-step premise `bindingLabelsEqual` (D37: every binding pair has equal labels), from which the shape the receive theorems consume, `receiveLoanReturnHidden` (the returned context or its owner is hidden), is derived, on the `endpointReceiveDualHigh` and `endpointReplyRecvHigh` steps; the two-run theorem takes the same predicate of both runs; SX18 removes it (D38, D40). **Landed:** `maybeDonateSchedContextFlowing_lowEquivalent_pair` (`InformationFlow/NotificationLendTwoRun.lean`) takes `bindingLabelsEqual` of both runs, timer agreement, `runQueueRefined` of both runs (the invariant the run-core reads come off, ruling (ay).3) and the static labelling fact `threadObjectLabelsEqual` (each thread carries its TCB's label: `LabelingContextValid` gives only a flow, and the admission reads the waiter's binding words off its TCB); its corollary `maybeDonateSchedContextFlowing_lowEquivalent_pair_deployment` discharges the labelling fact for every deployment context. | The theorem; pair lemmas (two runs, one write) for `rewriteObject`, `updateTcb`, `runEnqueueOnCore`, `releasePlace` and `markReschedulePending`, none in the tree. | Tier 3 anchors on the theorem and its five pair lemmas |
| SX9.2 | **LANDED at `v0.37.38`.** **The remaining D21 behaviour rows** in `sel4BehaviourRows` (`Testing/Sel4ConformanceTable.lean:512`), each with its scenario in `runBehaviourRows` (`tests/Sel4ConformanceSuite.lean:301`): reply_pop's held arm; SchedContext_Unbind of a donated holder with `unbindReply` (D22); suspend keeps the victim's binding; a blocking receive returns the context; SchedContext_Bind of a lender. | none (rows and scenarios) | `sel4_conformance_suite` |
| SX9.3 | **LANDED at `v0.37.38`.** **Heap scenarios on the two labelled bands** of `Exerciser.deploymentLabeling` (`Platform/Exerciser/Deployment.lean:162`). **As measured** (owner's ruling, 2026-11-24): the row first named a Call whose lend the label check refuses (D28), a notification lend refused low to high and high to low (D30), and SchedContext_Bind of a context heading a stack (D25). Under D33, D35 and D37 the two refusals cannot be reached from a booted image: every way a thread comes to hold a context (Bind, `schedContextBindLabelAdmits`; the notification lend, D30; the Call and receive lends between equal-label endpoints, D33) gives the holder the context's label, so `callLendAdmits` never refuses; a waiter carries its notification's label (the two-way wait gate) and a notification its context's (`schedContextBindNotificationLabelAdmits`), so the lend's label check never refuses. Only a boot image binding unequal labels reaches them, which SX10.1's boot check refuses. So SX9.3 measures the gates that make them unreachable, on the upper band beside `bind-upper-notification-refused`: `sched-context-bind-upper-notification-refused` (the image's context bound to the notification carved at an upper id) and `sched-context-bind-upper-thread-refused` (bound to a thread carved at an upper id), each refused `flowDenied` before any write. D25's thread half (a lender whose frame is on a live stack) is the existing `held-pop-bind-lender`; its context half is unreachable: a bind needs the context bound to no thread, a context heading a stack is held by the stack's server, and an unbind lets go of the stack (`schedContext_unbindReply`), so no state holds an unbound context that heads a stack. The refusal branches stay until SX18 deletes them (SX18.2, D38, D40). | none | `scripts/qemu_exerciser_lib.sh` expected set; QEMU: each reads 0 |

**Acceptance:**
- one two-run theorem and five pair lemmas, with the owner's ruling on the
  cleared observer recorded here;
- five new behaviour rows, each with a passing scenario;
- two new heap steps (the substitution SX9.3 records), each reading 0 on both lanes, twice;
- the one premise (`bindingLabelsEqual`, D37) registered, owned by SX18 (D38, D40): on
  the two receive steps and on the two-run theorem.

### SX10 — The equal-binding-labels invariant, begun (D36, D37, D38)

**LANDED at `v0.37.39`, wrapped at its validated point (D38).** SX9's
remainder on the lend's evidence. It lands the boot base case, the owner
clause and the slot toolkit; the invariant's preservation, the premise's
removal and the refusal deletions move to SX13–SX18 (D40), on SX11's waiter-label
invariant.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX10.1 | **LANDED.** **The boot base case.** As found: the checked boot already refuses every configured binding pair, of equal labels or not (`bootSafeTcbCheck`: a boot thread is unbound; `bootSafeSchedContextCheck`: a boot context binds no thread; `bootSafeNotificationCheck`: a boot notification binds no context), and no boot stage creates one (the idle threads, the starts, the interrupt nodes, the root server and the capability links). The Low finding reported during SX9 (that a boot image binding unequal labels boots) is withdrawn, and no label check is added: its refusal could never run. The base case is the proof: `bootFromPlatformCheckedStartedFor_bindingLabelsEqual` (`Platform/Boot/InitialThreads.lean`), under every labelling, read off the linked boot shape. `bindingLabelsEqual` moves to its own kernel module (`SchedContext/Invariant/BindingLabels.lean`) below the projection. | The boot base case: a booted state satisfies the invariant. | `syscall_dispatch_suite`: the checked boot refuses a thread bound, a thread lent, a context bound and a notification bound across unequal labels, and the unbound control boots with no binding word; Tier 3 anchors |
| SX10.2 | **LANDED.** **The owner clause and the binding words, slot by slot.** `bindingLabelsEqual` gains its fourth clause, D37's first consequence: a lent binding's owner word (`TCB.scBindingOwnerCode`) names a thread with the context's label, because the return to the owner binds the owner. Its views read the four words through the typed readers (`threadContextView`, `threadOwnerView`, `contextThreadView`, `notificationContextView`), and a step after which every binding word was already there carries it (`bindingViewsShrink`, `bindingLabelsEqual_of_shrink`). The slot toolkit states the four words of one object slot (`objBindingWords`), each view as a read of its slot, and a slot's binding shrink (`objBindingShrink`, with its free, unchanged, thread, notification and context forms), lifted to the views (`bindingViewsShrink_of_objects`, `bindingViewsShrink_of_slot`): the leaf lemmas SX14's frame family consumes. | The views' agreement with the predicate; the shrink lemmas. | Tier 3 anchors on the clause and the toolkit |

**Acceptance:**
- the boot base case proves the invariant of every booted image;
- the owner clause and the slot toolkit build, with their anchors;
- the premise `bindingLabelsEqual` stays on the two receive steps and the
  two-run theorem, its debt row now owned by SX18.

### SX11 — Blocked threads carry their endpoint's label (D38)

**LANDED at `v0.37.40`.** `endpointWaitersLabelsEqual` holds of every booted
state and is carried by every committing entry (`QueueLabelsStage`,
`SeLe4n/Kernel/QueueLabels/`). The per-dispatch blocked-sender lifts and
both shrink relations it supersedes are retired.

The state fact the Call and receive-take lends need, which no gate at the lend
can give: every endpoint gate is two-way (`endpointFlowGate`, so equality by
`endpointFlowGate_implies_eq`), and each thread waiting on an endpoint passed
it when it blocked.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX11.1 | **LANDED.** **The equality forms** of `blockedSenderFlowsToEndpoint` and `blockedReceiverFlowsFromEndpoint` (`InformationFlow/Invariant/Composition.lean`): every thread blocked sending, calling or receiving on an endpoint has the endpoint's label. The one-way forms are derived from them and retired where nothing else reads them. **The boot base case**: a booted state blocks no thread. | The boot base case; the one-way forms as corollaries. | Tier 3 anchors |
| SX11.2 | **LANDED.** **A per-entry stage** over every writer of a thread's blocked state: a frame where the write keeps the thread's IPC state, a shrink where it writes a non-blocking state, a creator where it writes a blocking state, discharged from the gate the entry checks on that thread (the send, call, receive and reply-receive arms and fault delivery). Measured on the tree at `v0.37.39`, outside `InformationFlow/` and `Testing/`: 135 files write a thread's IPC state (3,428 matching lines, 76 files outside the invariant and proof modules); 17 files write a blocking state on the line (162 sites), the creators. The existing one-way facts have 111 references in 5 files. It narrows part of `docs/REGISTERED_DEBT.md` table C ("`ipcReachable` is not carried across a trace") to these two conjuncts per entry; carrying the pack across a trace stays WS-PK's. As landed: the frames are the records' frames (the record view holds the IPC state) and the writes that keep every thread's IPC state; the shrinks are the cancellations, restores, timeouts, signal wakes, the finalisation, the carve (a fresh thread is `.ready`) and the delete chain; the creators are the checked send, call and fault delivery, each from its own gate, and the receive and reply-receive, from the gate the dispatch checks before either runs. The capability table is a frame on every arm. Every entry reads the store's invariant at the state it runs from; the syscall entry reads it after the dispatch off the records' stage, as the lenders' entry does. | Preservation by every committing entry. | Tier 3 anchors on the stage and the creators |

**Acceptance:**
- the equality forms hold of every booted state and are kept by every
  committing entry;
- the one-way forms are corollaries.

### SX12 — The origin redirect deleted (D31, D39)

**LANDED at `v0.37.41`.** The reply pop, the dispatch's replenishment
migration and the frozen composite give the context to the answered caller;
`SchedContext.donationOrigin`, `TCB.originScCode` and every resolver, guard,
write, clear, projection clause, boot shape and frozen mirror of them are
deleted, and the reply-receive lenders premise lost its origin conjunct. The
middle-frame witness is `runMiddleFrameRecipientChecks` in
`tests/SmpIpcSuite.lean`. The suspend footprint's state-level member is
deleted: the suspend writes objects in place and changes no table structure.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX12.1 | **LANDED.** **reply_pop gives a context to the answered frame's caller**, as seL4-MCS does: `donationOriginRecipient?` (`IPC/Operations/Endpoint.lean:7518`) and the `SchedContext.donationOrigin` field (`SchedContext/Types.lean:368`) are deleted with every frame lemma, projection clause, boot shape and frozen mirror that reads them: 565 lines in 66 files at `v0.37.36` (`rg -c donationOrigin` outside `docs/`). This fixes the middle-frame recipient bug, also on `main` (Low, reported 2026-11-23): on a stack O→M→N under a server holding the context, a suspend of M and then a reply to N gives the context to O, still blocked on its orphaned reply, where seL4 gives it to N. | Every theorem that splits the redirect, restated or deleted. **Settled in the row:** the origin premise (`ReplyRecvLendersPremises`, `ContextLenders/ReplyRecv.lean:361`) may vanish with the redirect; if it does not, it folds into `contextLendersFlow` or gets a `docs/REGISTERED_DEBT.md` table C line owned by WS-PK. | `smp_ipc_suite`: the middle-frame scenario as a permanent test (N receives the context, O stays unbound); Tier 3 anchors refusing the retired names |
| SX12.2 | **LANDED.** **Prose that still names the code SX8 retired**: `cleanupDonatedSchedContext` (`Capability/Operations.lean:34`, `Lifecycle/Operations/Cleanup.lean:593`, `:623`), `cancelDonation`, `cancelDonationOnCore`, `cancelBoundDonation` and `cancelDonatedDonation` (`IPC/CrossCore/Cancellation.lean:57`–`:72`, `:437`, `:2965`, `:2979`, `:3469`, `:4000`; `IPC/Operations/Endpoint.lean:7575`; `Lifecycle/Operations/Cleanup.lean:642`; `InformationFlow/Invariant/Operations.lean:5392`, `:5437`), and the labels the retargeted checks print (`tests/SuspendResumeSuite.lean:462`–`:526`, `:1672`; `tests/LivenessSuite.lean:182`, `:389`; `tests/SmpCancellationSuite.lean:36`). | none | none (prose and printed labels; no gate reads them) |
| SX12.3 | **LANDED** (deleted). **The suspend footprint's state-level member** (`lockSet_tcbSuspendOnCore`, `IPC/CrossCore/Cancellation.lean:2193`), kept beside the context member when the donation cancellation retired, but never proven needed by the release removal: prove it needed, or delete it. | The suspend's coverage theorem over the narrowed set, if it narrows. | Tier 3 anchor on the footprint's shape |

**Acceptance:**
- `donationOrigin` has no use outside `docs/` and `CHANGELOG.md`;
- the middle-frame test passes, and every other reading is unchanged;
- the origin premise is gone, folded or registered;
- no source comment or printed label names a declaration SX8 retired;
- the suspend footprint has no unproven member.

### SX13 — The equal-binding-labels invariant: the toolkit for its creating sites (D36, D37, D38, D39, D40)

**LANDED at `v0.37.42`, wrapped at its validated point (D40).** SX10's
remainder (D38), on SX11 and SX12 (D39). It lands the binding grow and the
binding-words leaf lemmas. The frame family's threading, the creating sites,
the premise's move and the refusal deletions move to SX14–SX18. No transition
changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX13.1 | **LANDED.** **The binding grow** (`SchedContext/Invariant/BindingLabels.lean`): a step that writes a binding word to a new value (a bind, a lend, the return to an owner) is no shrink; it carries `bindingLabelsEqual` when every word after it was there before it or pairs equal labels (`bindingViewsGrow`, with `of_shrink` and `trans`; `bindingLabelsEqual_of_grow`). One slot written, read as a grow: `bindingViewsGrow_of_tcbSlot`, `bindingViewsGrow_of_schedContextSlot`, `bindingViewsGrow_of_notificationSlot`, each taking the label equation its creating site proves. The invariant read at a holder: `bindingLabelsEqual.donated` (a lent holder and its owner both carry the context's label) and `bindingLabelsEqual.bound`. A holder whose lender has gone: `objBindingShrink.ofTcbOwnerCleared`. | The grow lemmas. | Tier 3 anchors on the grow and the readers |
| SX13.2 | **LANDED.** **The binding-words leaf lemmas the frame family's summaries need**: a thread record written keeping its binding is a slot shrink (`objBindingShrink.ofTcbBinding`, lifted to the views as `bindingViewsShrink_of_tcbBinding`), and the priority-inheritance walk keeps every thread's context and owner words (`keepsScBindingAt`, `updatePipBoostOnCore_keepsScBindingAt`, `propagatePipChainCrossCore_keepsScBindingAt`, `Scheduler/PriorityInheritance/Propagate.lean`): the binding-words reading that the walk's pointwise summary leaves out, as a sibling lemma, not a widened summary. | The leaf lemmas. | Tier 3 anchors |

**As measured (D40).** The first cut threads the binding words through the
frame family (`contextStackViewsAgree` and `contextStackLinksShrink` gain them)
and strengthens `contextLendersFlow` in place to `contextLendersLabelsEqual`.
Measured by building every `ContextLenders/*` module on it and stubbing each
failing declaration to a fixpoint: 37 declarations in 9 files (Call 3, Timer 4,
Cancel 4, Reply 3, Receive 4, Interrupt 3, Capability 2, `CapabilityOnly` 13,
`SyscallDispatch` 1) and one census witness (`Testing/ReplyStackWriteCensus.lean`);
nothing outside the lender cut fails (`lake build SeLe4n` is clean, the cut is
staged-only). Of these, 12 sites are summary lemmas that forget the binding words,
needing about 10 sibling lemmas in about 8 files outside the 78 writer files.
A second finding the stubs do not count, because a stub keeps its statement:
the pops (the return to an owner, the keep, the unheld return) grow the binding
views, so they are no longer links shrinks, and the 30 `LendersFrame` theorems
that chain a pop (`CapabilityOnly` 12, Reply 8, Cancel 6, and one each in
Dispatch, `SyscallEntry`, `CapabilityDispatch` and `ReplyRecv`) must be restated
as labelled steps. Together well over 1.5 times the row's estimate. The first
cut, with Call and Timer building on it, is kept as a patch beside the row's
notes for SX14; it cannot land alone, because every lender module after Timer
consumes the frame family it changes.

**Acceptance:**
- the binding grow and the leaf lemmas build, with their anchors;
- the premise `bindingLabelsEqual` stays on the two receive steps and the
  two-run theorem, its debt row now owned by SX18.

### SX14 — The cancel pops to the frame's recorded caller (D40, D41)

**LANDED at `v0.37.43`, wrapped at its validated point (D32).** SX13's
remainder, first half. It lands SX14.1, which changes one transition: the
cancel's pop reads the frame's recorded caller (D41). The rest of the row as
first planned (the frame family threaded, the pops as labelled steps) is split
by D42 into SX15 (the binding siblings and the one-slot grow toolkit, additive)
and SX16 (the frame family threaded and the pops as labelled steps, one unit).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX14.1 | **LANDED.** **The cancel pops to the frame's recorded caller** (D41, "Match seL4": seL4's `reply_pop` donates to `reply->replyTCB`). `cancelledCallerDonation?` reads the victim's frame only where it records the victim as its caller (`replyRecordsCaller`, a word compare of the stored reply's caller code, allocation-free), and the compiled head cancel's gate (`headReplyCancelInPlace`) reads the same word, so the `@[csimp]` form agrees. The guard agrees with the unguarded read wherever the reply linkage holds (`cancelledCallerDonation?_eq_unguarded_of_linkage`, from `replyRecordsCaller_of_linkage`); its consumers that read the head case take the linkage from `ipcInvariantFull` or the reply's recorded caller from the finalisation (`replyCallerFinalisable_cases`). `cancelledCallerDonation?_independent_of_victim` is retired. So the cancel's pop recipient is the frame's recorded caller, whose label `contextLendersLabelsEqual` equates with the context's (SX16.2 discharges the owner obligation from it). | The agreement lemma; the guard's `some`/`none` cases; the in-place equality. | Tier 3 anchors on the guard, its agreement and the in-place gate; the cancellation suite's foreign-caller witness |

**As measured (D32).** On the landed guard, the cut that threads the frame
family and restates the cancel's pops as labelled steps builds through Call,
Timer and Cancel (the cancel's return now needs no premise:
`returnDonationToCancelledCaller` keeps the stage from the frame's caller).
Building every `ContextLenders/*` module on it and stubbing each failing
declaration to a fixpoint leaves 45 declarations in 10 files (`CapabilityOnly`
21, Receive 6, Interrupt 4, Reply 3, `ReplyRecv` 3, Capability 2, Dispatch 2,
`SyscallDispatch` 2, Fault 1, `SyscallEntry` 1) and the census witness. A stub
keeps its statement, so the count leaves out the pops still stated as frames
(about 24: `CapabilityOnly` 12, Reply 8, and one each in Dispatch,
`SyscallEntry`, `CapabilityDispatch` and `ReplyRecv`) and the creating sites'
hypotheses still to thread (the bind and the notification lend under the
interrupt, the declassified signal and the receive, the fault delivery's
receiver equation). Against the row's 3–4 sessions, two of them spent (the
stop on the cancel's owner obligation, then the guard and the cancel), the
remainder is about four more: well over 1.5 times the estimate. The cut is
kept as a patch beside the row's notes for SX16; it cannot land alone, because
every lender module after Cancel consumes the frame family it changes.

**Acceptance:**
- the cancel's resolver reads the frame's recorded caller, agreeing with the
  unguarded read wherever the reply linkage holds, with its anchors and the
  cancellation suite's foreign-caller witness.

### SX15 — The binding siblings and the one-slot grow toolkit (D40, D42)

**LANDED at `v0.37.44`.** Every sibling, the finalisation's binding shrink and
the toolkit landed as stated, within the measured scope; no transition changes.
The finalisation's binding shrink (`FinaliseBindingShrink`) takes one step
lemma per hypothesis of the finalisation's closure except the two reply pops
(`FinaliseReplyStep`, `FinaliseUnheldStep`), which hand a donated context back
and so write binding words anew: they are SX16's labelled steps.  The cut's
owner-word clear is read as a binding shrink (`bindingViewsShrink.ownerCleared`),
since it keeps the slot's context word.

SX14's remainder, first half (D42): what the frame family needs that does not
depend on threading it, landed alone on the committed base. Each sibling is a
lemma stated beside the summary it complements, never a widened summary, and
no twin of the frame family: it reads the binding words (`objBindingWords`)
the summary forgets. No transition changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX15.1 | **The binding siblings.** Each summary that forgets the binding words gets a sibling reading them, as an exact frame of every slot's binding words or as a slot-by-slot keep-or-clear (`bindingWordsKeptOrCleared`, a binding shrink): the capability transfer's object cases, the splice and the notification-queue removal, the slot links' reach, the VSpace-root-only write, the final retire, the off-taint agreement and the timeout abort. The finalisation's steps carry their binding shrink separately from `finaliseWrite` (not a new conjunct of it: 129 `rcases` sites), one sibling per step the finalisation folds over, on the primitive writes they compose. | The siblings. | Tier 3 presence anchors |
| SX15.2 | **The one-slot grow toolkit.** A thread, context or notification slot written by a creating site is read as a stack shrink (`contextStacksShrink`) with a binding grow (`bindingViewsGrow`), each form taking the label equation its creating site proves; the two carry the lenders' flow and equal binding labels together (`contextLendersFlow_bindingLabelsEqual_of_grow`). | The toolkit. | Tier 3 anchors, a relation anchor on the carrying theorem |

**As measured.** About 12 sibling lemmas in 9 files (SX13's measurement:
12 sites, about 10 lemmas in about 8 files), the finalisation's binding shrink
over the steps its fold takes (about 11, with the primitive writes they
compose), and the toolkit's three slot forms with the carrying theorem.

**Acceptance:**
- every sibling and toolkit lemma builds on the committed base, with its
  anchors; nothing in the frame family changes.

### SX16 — The frame family threaded, the pops as labelled steps (D40, D42)

**LANDED at `v0.37.45`.** Both sub-tasks landed as one unit, within the
measured scope, with no transition change and no stub.  The links shrink's
binding field is a keep-or-clear of every slot's binding words; SX15's
carrying theorem is restated over the lending labels
(`lendingLabelsEqual_of_grow`) with its stack half a stack-only slot lemma
(`contextStacksShrink_of_slot`), and the old form is retired.  The reply pops'
owner is the frame's recorded caller at the pre-reply state, carried across
the reply leg's links shrink (`calledFrame_labelEq`) from the reply linkage of
the dispatch's IPC bundle; the finalisation's two reply pops are labelled
steps, the unheld pop's owner read from its own admission
(`LendersStep.finaliseReplyUnheldPop`).  The creating sites' label equations
sit in the entries' premise packs (`LendersDispatchPremises`: `waiters`,
`bindThread`, `bindNotification`, `declassifySignal`; `ReceiveLendersPremises`,
`ReplyRecvLendersPremises`, `FaultLendPremises`), and the flow bridges they
replace are retired; SX17 discharges them.

SX14's remainder, second half (D42), on SX15. The frame family carries both
halves of the lending invariant, and every step that does not create a binding
is shown to keep it. One unit: every lender module after Cancel consumes the
frame family it changes, so nothing lands before all of them build.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX16.1 | **The frame family threaded** per ruling (ag): SX8's `contextLendersFlow` is strengthened in place to label equality and renamed `contextLendersLabelsEqual` (D37's second consequence); the carried stage is its conjunction with `bindingLabelsEqual` (`lendingLabelsEqual`). `contextStackViewsAgree` and `contextStackLinksShrink` gain the binding words, `chainObjectsKept` keeps them on thread and notification slots, and the leaf lemmas take a slot's binding shrink (SX13's toolkit). The leaf lemmas and summaries read the binding words through SX15's siblings and the creating writes through its toolkit. Every creating site takes its label equation as a hypothesis of its step, surfaced in the entry's premise pack, which SX17 discharges; no step is stubbed. | The frames and shrinks over the lender cut: of the 37 measured declarations, the 25 that create no binding (Call 2, Timer 4, Cancel 4, Reply 3, Capability 2, `CapabilityOnly` 8, `SyscallDispatch` 1, Receive 1) and the census witness. | Tier 3 anchors on the strengthened predicate and the threaded frame |
| SX16.2 | **The pops as labelled steps.** A labelled step (`LendersStep ctx st st'`: the stage carried from `st` to `st'`, and the store's invariant at `st'`), with its identity, composition, the frame read as a step and the stage. The 30 `LendersFrame` theorems that chain a pop are restated as labelled steps, each pop discharging its owner obligation inside the step at its own pre-state (FINDING 1: proof obligations, not premises): the cancel's return to the frame's recorded caller (D41: the cancel's guard makes the recipient the frame's caller, so `contextLendersLabelsEqual` names it), the reply's return from the answered caller (since SX12, the frame heading the context, through `contextLendersLabelsEqual` at the pre-reply state), the next owner from `replyStackOuterCaller?` through `contextLendersLabelsEqual`; the keep and the clears are shrinks. | Preservation by every pop, in place and cross-core. | Tier 3 anchors on the labelled step and the pops |

**As measured (D42).** The cut kept from SX14 (the cancel's pops already
labelled steps), the 45 failing declarations in 10 files and the census
witness, about 24 pops still stated as frames, and the creating sites'
hypotheses threaded into the entries' premise packs: about three sessions.

**Acceptance:**
- every lender module builds over the threaded frame family, with no stub;
- every pop is a labelled step whose owner obligation is discharged inside it;
- the creating sites' label equations are the only hypotheses the stage adds.

### SX17 — The creating sites, and preservation over every writer (D40)

**LANDED at `v0.37.46`.** Within the measured scope (17 declarations in 7
lender files, against the plan's 12), with no transition change and no stub.
The receive take and the reply-receive take read the dequeued thread at the
receive leg's own state: the receiver itself, or the send queue's head, which
is blocked on the endpoint and so has its label
(`endpointReceiveDualWithCapsOnCore_dequeued_labelEq`, from the receive gate,
`queueHeadBlockedConsistent` and SX11's `blockedSenderLabelsEqual`).  The Call
lend and the fault delivery read the waiters each entry takes at its own state
beside the records.  Bind reads its label gate
(`dispatchCapabilityOnlyChecked_bindLabels`).  The declassified signal's lend
was found checked, not unchecked: the dispatch runs it under the lifted
context, whose generic check is `donationContextFlows`, so its step takes no
premise.  The packs carry no label equation (Tier 3 negative anchors).  The 41
writer files that write no stack view needed no new theorem: every writer a
committing entry reaches is covered inside that entry's labelled steps since
SX16, and the in-place files are proof support for the `@[csimp]` fast forms.

SX13's remainder, second half: the label equation of every step that writes a
binding word to a new value, discharged, so the stage holds of every committing
entry with no added hypothesis.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX17.1 | **The creating sites.** Bind (D35) and the notification lend (D30) check equal labels directly. The Call lend and the receive-take lend get the receiver's label equal to the lender's from SX11 and the step's gate: the Call's `applyCallDonation` takes the receiver's equation from SX11's `endpointWaitersLabelsEqual` at the pre-state (the receiver blocked receiving on the endpoint) with the caller's gate (`endpointFlowGate_implies_eq`), and the server's from the caller's own binding (`bindingLabelsEqual.bound`); the receive take, from the receive gate and the dequeued caller blocked calling. `LendersDispatchPremises` gains `endpointWaitersLabelsEqual` and the queue heads' consistency at each syscall's pre-state; fault delivery takes its gate from its checked branch with the waiters at its state. Measured: 12 of the 37 declarations, at the binding writes (Call 1, Receive 3, Interrupt 3, `CapabilityOnly` 5: the notification bind and unbind, the context's thread word on Bind and Unbind, the reply unbind), and the 41 of the 78 writer files that write no stack view (SchedContext Bind, Unbind and BindingAffinity; notification bind, link, donation and signal; the lifecycle cleanup and finalise; `ReschedulePendingArms`; the in-place fast forms; `FrozenOps`). | Preservation over every writer: every committing entry carries the stage under SX11's and the records' stages alone. | Tier 3 anchors on the creating sites and the premise pack |

**Acceptance:**
- every writer of a binding view preserves the invariant;
- the stage holds of every committing entry with no hypothesis SX14 added.

### SX18 — The premise moved (D40, D43, D44)

**LANDED at `v0.37.47`, wrapped at SX18.1 (D44).** The premise is off both
receive steps: `NonInterferenceStep.endpointReceiveDualHigh` and
`endpointReplyRecvHigh` carry no `bindingLabelsEqual`, and the standing
per-state slot beside the object-store invariant takes it
(`step_preserves_projection`, `NonInterferenceTrace.cons`,
`composedNonInterference_step`, `composedNI_withSwitchDomain`,
`composedNI_two_steps`, `syscallNI_coverage_witness`, the per-core headline
`nonInterference_perCore` with its lifts and
`PerCoreNonInterferenceStep.kernel`, and
`syscallEntryChecked_success_perCore_NI`). The receive steps read the hidden
loan return off the slot (`receiveLoanReturnHidden_of_bindingLabelsEqual`).
The notification lend's two-run theorem already took it of both runs as a
standing hypothesis and is unchanged. No transition changes. SX18.2 as first
stated became SX19 (the Call lend's refusal, D28) and SX20–SX22 (the
notification lend's check, D30, which the carried invariants do not make
unreachable: D43, D45).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX18.1 | **LANDED at `v0.37.47`.** **The premise moved**, per ruling (a) under D29: `bindingLabelsEqual` leaves `endpointReceiveDualHigh` and `endpointReplyRecvHigh` and moves to the standing per-state slot beside the object-store invariant (`step_preserves_projection`, `NonInterferenceTrace.cons`); the notification lend's two-run theorem keeps it as a standing hypothesis of both runs. Its `docs/REGISTERED_DEBT.md` row narrows to a table C line owned by WS-PK (carrying it across a trace) and does not close. | `endpointReceiveDual_preserves_projection` and `endpointReplyRecv_preserves_projection` without the per-step premise. | Tier 3 anchor refusing the per-step premise |

**Acceptance:**
- the premise is off both receive steps, standing beside the object-store
  invariant, and its debt row narrowed.

### SX19 — The Call lend's refusal deleted, the lend parameter retired (D28, D44)

SX18.2's first half, as measured (D44).

**LANDED at `v0.37.48`.** Measured before the cut: 295 declarations in 73
files (1.35x SX18's 219/57, under D32's wrap). The admission was first
proved true at every committing entry's arm state from `bindingLabelsEqual`
(the fault leg reads the spilled state, which keeps it), so no reachable
behaviour changed. No heap scenario measured D28's refusal (unreachable from
a booted image), so the heap gate's expected set is unchanged.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX19.1 | **LANDED at `v0.37.48`.** **The Call lend's refusal deleted** as retired code: `callLendAdmits`' refusal (D28) and `receiveLendAdmits` with it, and the `lend : Bool` argument they feed: the gated donation (`applyCallDonationOnCoreWhen`) and resolver (`callLendSchedContext?`), the in-place unlent arms (`callWakesUnlentInPlace`, `receiveCallTakesUnlentInPlace`, the ReplyRecv unlent arms), the Call, fault, receive and ReplyRecv legs' argument, their compiled forms, NI case splits, refusal rows and heap scenarios. Measured at SX18: 219 declarations in 57 files take the argument. | Each consumer restated over the unchecked lend; the Call lend's label equation stays SX17's (the waiters and the gate). | Tier 3 negative anchors on the deleted definitions; the census and anchor sweep over every file the cut touches; the heap gate's expected set |

**Acceptance:**
- no lend admission and no `lend` argument remain; every Call, fault and
  receive-take lend is seL4's.

### SX20 — The records view extended (D45)

**LANDED at `v0.37.49`.** Measured before the cut: the extension touched
17 files (358 lines added, 118 removed). The records view now holds every
field `notificationLabelsCoherent` reads, so each of the records frames keeps
it with no new proof; eight writers became core frames. No transition
changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX20.1 | **LANDED at `v0.37.49`.** **The records view extended**: `TcbRecordView` gains the thread's `ntfnPrevCode` and `ntfnNextCode`, and `recordViewOf` a notification's view (`Notification.recordView`: its bound thread, queue head and queue tail). Every records frame that writes or relinks those fields is restated as a core frame (`RecordsCoreFrame`, the view with the links erased and the notification view constant), which keeps the kernel records only: the bind and the unbind, the notification stores of the signal and the wait, `linkNtfnWaiter`, `detachNtfnHead` and `of_ntfnLinksRewritten`. Each consumer of a frame gains a core sibling. The unused `RecordsFrame.of_kept` and `recordViewOf_congr` are deleted. | Every records frame re-proved against the extended view; the core frame's preservation of the kernel records. | Tier 3 anchors on the extended view, the core frame and the restated writers; negative anchors on the deleted lemmas |

**Acceptance:**
- every records frame keeps coherence's reads, and every writer of them is a
  core frame.

### SX21 — Notification label coherence carried (D43, D45, D46)

**LANDED at `v0.37.50`.** Measured before the proofs, by a stub pass to its
fixpoint: the extended family (SX11's, renamed `QueueLabels*`) grew from 3554
to 4602 lines over 14 files, about 90 more in the agreement's definitions and
the boot implication, inside the row's estimate. The carried form is
`notificationLabelsAgree` (D46). No transition changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX21.1 | **LANDED at `v0.37.50`** (`QueueLabelsStage`, the label part, D46; the three queue arms' `hTeardownProj` moved to SX22.2, `abortHolderProjectionStable_of_neighbourHigh` having been retired with the holder abort at `v0.36.136`). **`notificationLabelsCoherent` as a per-entry stage**: a notification's bound thread, its wait queue's threads and their queue links carry its label (the two-way `notificationFlowGate`), carried across every kernel entry beside SX11's endpoint waiters. Its boot base case is the boot's check (`bootAndInitialiseFromPlatformOn`). Every records frame is a coherence frame (SX20); the stage's own proofs are the core frames (SX20.1) and the records steps and stages, classified as frame, shrink or creator, each creator (the Wait, the bind) taking the new member's label from its two-way gate. Closes the queue-label-uniformity row of `docs/REGISTERED_DEBT.md`. | Preservation over every writer of a notification's bound thread, its wait queue, the threads' queue links and their IPC states; the coherence hypotheses retired if they fall out of the stage: `declassifiedSignalReceiver_flow_ordinary_of_coherent` and `footprint_receiver_at_notification_label` (`InformationFlow/DeclassifiedSignal.lean`, `InformationFlow/NonInterferenceCrossCore.lean`, `API.lean`), and `abortHolderProjectionStable_of_neighbourHigh`'s neighbour clause with the three queue arms' `hTeardownProj` (`IPC/CrossCore/CancellationNI.lean`); any that does not fall out gets its own row. | Tier 3 anchors on the stage and its entry theorems |

**Acceptance:**
- every committing entry carries notification label coherence with no added
  hypothesis.

### SX22 — The notification lend's check deleted (D30, D43, D46, D47)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX22.1 | **LANDED at `v0.37.51`** (D47: proved true at every site before the deletion; the fourth site is the completed-signal arm of a receive, `completeSignalArm`, and the ReplyRecv arm that completes a signal, whose lend follows the checked wait and its two-way gate; the interrupt path's labelling context, read only for the check, retired with it). **`donationContextFlows` deleted** as retired code, with `maybeDonateSchedContextFlowing`, its generic and compiled forms, NI case splits and refusal rows, at its four sites: the signal arm, the declassified signal, the interrupt delivery and the completed-signal arm. The woken thread's label equation comes from SX21's coherence and `bindingLabelsEqual`'s notification clause. | Each consumer restated over `maybeDonateSchedContext`; the two-run theorem over `maybeDonateSchedContext`. | Tier 3 negative anchors on the deleted definitions; the census and anchor sweep; the heap gate's expected set |

**Acceptance:**
- the notification lend is seL4's, unchecked, and every entry still carries the
  lending labels.

### SX23 — The records view extended with the endpoint queue links (D45, D47)

**LANDED at `v0.37.52`.** Measured by a stub pass to its fixpoint over the 75
modules downstream of the records view: 18 Lean files (386 lines added, 148
removed), the size of SX20's extension. No transition changes.

Measured when SX22.2 started: the queue arms' teardown reads the victim's two
endpoint-queue neighbours and the endpoint's queue ends, and no frame carried
per entry keeps them (`TcbRecordView` holds a thread's reply view, IPC state,
thread state, fault flag and notification-queue links, and nothing of an
endpoint queue). As D45 did for the notification fields, the view gains them,
so every records frame keeps them, and their writers are restated as core
frames. No transition changes.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX23.1 | **LANDED at `v0.37.52`** (the view holds `queuePrevCode`, `queueNextCode` and `Endpoint.recordView`, the four queue-end codes; the back-pointer stays out, naming the same predecessor or the endpoint's head; the writers are `RecordsEndpointFrame`s, core frames that keep the notification queues' reads, so SX21's notification coherence still crosses them with no new proof; the modules named below that also write an IPC state reach the records family as `RecordsStep`s, which claim no view, or through the restated primitives: `storeTcbQueueLinks`, `endpointQueuePopHead`, `endpointQueueEnqueue`, `endpointQueueRemoveDual`, `endpointQueueRemove` with its neighbour patches, and `storePopHead`; `RecordsFrame.storeEndpoint`, `notParked` and `modifyObject` deleted as unused). **The records view gains a thread's endpoint-queue links** (`queuePrev`, `queueNext`) and an endpoint's queue ends, so every records frame keeps them. The writers of them are restated as core frames (`RecordsCoreFrame`): the dual queue's enqueue and remove (`IPC/DualQueue/Core`), the in-place pops and enqueues (`PopInPlace`, `EndpointEnqueueInPlace`), the transport and the Call legs, the four ReplyRecv take-in-place modules, the lifecycle's cleanup and suspend, and the cancellation arms (`ReschedulePendingArms/Cancellation`). | Each writer's core frame; the records family's existing frames re-proved over the wider view where they read it. | Tier 3 anchors on the view's new fields and the core frames |

**Acceptance:**
- every records frame keeps the endpoint queue links and ends, and every writer
  of them is a core frame.

### SX24 — The endpoint queue links' labels carried, the queue arms' teardown discharged (D46, D47)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX24.1 | **LANDED at `v0.37.53`** (`endpointQueueLabelsAgree`, an endpoint's queue ends at its label and a thread's endpoint-queue links at its own, the third part of `QueueLabelsStage`, its boot base `bootFromPlatformCheckedStartedFor_endpointQueueLabelsAgree`; the enqueue a growth under the gate's label equation, every other writer kept, the cancel's in-place pop and removal through `popHead_inPlace` / `queueRemove_inPlace` under the guards they already check; `cancelIpcBlocking_preserves_projection_high` and its per-core form prove the teardown invisible on every arm, so `cancelIpcBlockingOnCore_cancellation_NI` and its SMP form take the carried labels instead of `hTeardownProj`, and the reply-arm corollary is retired; measured at 13 files, about 1,600 lines added, inside the estimate, no wrap).  **The queue arms' teardown projection discharged**: `cancelIpcBlockingOnCore_cancellation_NI` and its SMP form lose `hTeardownProj` for the `.blockedOnSend`, `.blockedOnReceive`, `.blockedOnCall` and `.blockedOnNotification` arms. It did not fall out of SX21 (moved from SX22.2, D47): the dequeue rewrites the endpoint or notification object and splices the victim's neighbours, and no theorem proves those writes invisible for a high victim; and an endpoint queue's links carry no label fact (SX11 carries the waiters' labels, SX21 a notification queue's links). So the row carries, over SX23's view, an endpoint queue's link labels beside `endpointWaitersLabelsEqual`, as `notificationLabelsAgree` carries a notification's, and proves each arm's teardown projection-preserving from them. | The link-label clause carried across every entry; the teardown's projection theorem per arm, from the victim's label, its object's label and its neighbours'. | Tier 3 anchors on the hypothesis-free theorems; the negative anchor on `hTeardownProj` |

**Acceptance:**
- cancelling a high thread blocked on an endpoint or a notification is
  invisible with no teardown-projection hypothesis.

### SX25 — One in-place ReplyRecv reply leg and the composed blocking receive (ruling r, D48)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX25.1 | **LANDED at `v0.37.54`** (`ReplyRecvLegGuards.lean`, `ReplyRecvBlockComposed.lean`; the narrowed row ran about 2x its estimate and was finished whole, D48). **One in-place reply leg over the five reply arms** (no pop, donated, held, unheld, unlinked) with one family of carried guards: each arm's leg carries the receive guard, the Send-take guard and the Call-take guard (15 of 15, the four missing ones filled). **The composed blocking receive** for every answer (message, capabilities, fault) and length (four words, 120 words), one arm-generic performer per answer and length (`performReplyRecvArm{Delivered,CapsDelivered,FaultAnswer}{,Long}`) and one `_eq` to the specification (`replyRecvAnsweringOnCore_arm_inPlace`), the held arm gaining the long, capability and fault shapes. The held arm's guard reads the context the pop leaves the receiver (it owns it, or the popped frame is the stack's last: `replyIsStackBottom`), so a server lent its context by the call it answers blocks in place. | The per-arm leg equalities cased over once; the arm proofs in `RefusalCarryingReplyRecv.lean` restated over one arm selector (`replyRecvBlockArmCode`, out of line). | QEMU: the held reply-receive at one and 120 words, installing at one and 120 words, and answering a fault at one and 120 words, each 0 |
| SX25.2 | **The blocking per-arm modules retired**: `EndpointReplyRecv{,Donated,Unheld}InPlace`, `LongReplyRecv{,Pop}InPlace` and the ReplyRecv half of `EndpointReplyHeldInPlace`, with the per-arm blocking performers of `ReplyRecvCapsDelivered`, `FaultAnswerInPlace` and `LongFaultAnswerInPlace`; what the surviving files use moved first (the reply-leg and pop frames into `ReplyLegFrame`, `ReplyPopFrame`, `ReplyUnheldPopFrame` and `LongReplyRecvFrame`, the per-arm leg equalities and receive guards into `ReplyRecvBlockComposed`). | none beyond SX25.1 | Tier 3 anchors refusing the retired names |

Baseline at `v0.37.53` (`leanc -c -O3 -DNDEBUG`, standalone): `RefusalCarryingReplyRecv.c`
is 21,021,237 bytes and compiles in 769 s.

**Acceptance:**
- every blocking ReplyRecv shape answered in place over every reply arm, under one proof;
- the blocking per-arm modules deleted;
- `RefusalCarryingReplyRecv.c` and its compile time no larger than the baseline (met at `v0.37.54`: 14,643,899 bytes, 607 s);
- every heap reading 0.

### SX26 — The Send-take receive leg composed (D48)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX26.1 | **LANDED at `v0.37.55`** (`ReplyRecvTakeComposed.lean`: `replyRecvAnsweringOnCore_arm_take`, one performer per answer and length `performReplyRecvArm{Take,TakeCaps,FaultTake}Delivered{,Long}`; the take arms of `RefusalCarryingReplyRecv.lean` routed by one out-of-line selector `replyRecvTakeArmCode`; QEMU steps for 13 of the 21 shapes it brings in place: the unheld and unlinked takes at 120 words, inert and installing, the held arm's four takes, and the fault answer's take on the rendezvous arm at 120 words and on the held and unlinked arms at one and 120 words, each 0; the donated arm's six take shapes and the unheld fault take's two have no exerciser scenario to build on, so their steps are carried to SX27.1). **The Send-take leg composed for every arm and answer**: a reply-receive whose receive leg meets a queued sender takes it in place over SX25's reply leg and guard family, for the five reply arms, the three answers and both lengths, under one `_eq`. | The take leg's equality over the arm; the take arms of `RefusalCarryingReplyRecv.lean` restated over it. | QEMU: one step per shape it brings in place, each 0 |
| SX26.2 | **LANDED at `v0.37.55`** (what the Call takes, the leg guards and the composed take read moved first, measured over the constants they use, into `ReplyRecvTakeFrame.lean`). **The take modules retired**: `ReplyRecvTakeInPlace`, `LongReplyRecvTakeInPlace`, `ReplyRecvFaultTakeInPlace`, `ReplyRecvUnlinkedTakeInPlace`. | none beyond SX26.1 | Tier 3 anchors refusing the retired names |

**Acceptance:**
- every Send-take ReplyRecv shape answered in place over every reply arm, under one proof;
- the per-arm take modules deleted;
- `RefusalCarryingReplyRecv.c` and its compile time no larger than SX25's (met at `v0.37.55`: 13,204,415 bytes, 535 s, against 14,643,899 bytes and 607 s);
- every heap reading 0.

### SX27 — The Call take composed, and the composed path's acceptance (D48, D49)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX27.1 | **LANDED at `v0.37.56`** (`ReplyRecvCallTakeComposed.lean`: `replyRecvAnsweringOnCore_arm_callTake`, one performer per answer and length `performReplyRecvArmCall{Take,TakeCaps,FaultTake}Delivered{,Long}`; the Call-take arms of `RefusalCarryingReplyRecv.lean` routed by one out-of-line selector `replyRecvCallTakeArmCode`). **The Call take with its donation for every arm and answer**: a reply-receive whose receive leg meets a caller queued by a capability-free `Call` takes it in place over SX25's reply leg, for the five reply arms, the three answers and both lengths, under one `_eq`; the caller's context is lent to a server holding none (`callLend`), and the held arm, whose server keeps its own context, takes the Call without a lend. | The Call take's equality over the arm; the Call-take arms of `RefusalCarryingReplyRecv.lean` restated over it. | QEMU: the rendezvous and unlinked arms' Call take at 120 words, granting a capability, and both (six shapes, each 0; the `queued-caller-*` scenarios answer a partner whose `Call` lent nothing, so they run the rendezvous arm); the donated arm's six shapes, the rendezvous and unlinked arms' fault-answer shapes and the rest of the QEMU work moved to SX28 (D49) |
| SX27.2 | **LANDED at `v0.37.56`** (what the surviving modules read moved first, measured by a Lean environment closure, into `ReplyRecvCallTakeFrame.lean`). **The Call-take modules retired**: `ReplyRecv{Call,DonatedCall,UnlinkedCall}TakeInPlace`; the store-reader hygiene rows regenerated. The composed path's final acceptance: every ReplyRecv shape (90) in place under one proof; `RefusalCarryingReplyRecv.c` size and compile time against SX25's baseline and SX26's. | none beyond SX27.1 | Tier 3 anchors refusing the retired names and imports, break-tested |

**Acceptance:**
- every ReplyRecv shape (5 reply arms × 3 receive legs × 3 answers × 2 lengths, 90) answered in place under one proof per receive leg;
- the per-arm Call-take modules deleted;
- `RefusalCarryingReplyRecv.c` and its compile time no larger than SX26's (**met at `v0.37.56`**: 13,074,785 bytes against 13,204,415; 480 s and 477 s on two quiet runs against 535 s; the four Call-take and Call-fault arms inline over out-of-line admission tests (a `Bool`, or the selector's code on the fault arms) and out-of-line answers returning the state and taking the reply's inline words, read once by the arm on the pre-state, in place of the replier's register file, so nothing is allocated and the server's frame write copies nothing);
- every heap reading 0.

### SX28 — The context-holding server's Call take in place (D49, D50)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX28.1 | **LANDED at `v0.37.57`** (`ReplyRecvCallTakeComposed.lean`: `ReplyRecvArm.CallAdmitsOwn`, `ReplyRecvArm.CallAdmitsAt`, `ReplyRecvArm.callTakeGuardOwn`, `ReplyRecvArm.callOwnGuard`, `ReplyRecvArm.donated_serverBound_head`; every Call-take performer takes `lends`; `RefusalCarryingReplyRecv.lean`: own-context codes 6 to 8 through `replyRecvArmCallCode`, `replyRecvCallLendsOfCode`; `RefusalCarryingReplyRecv.c` 12,941,835 bytes, standalone compile took 479 s and 476 s on two quiet runs (SX27: 480 s and 477 s); `own-context-reply-recv-takes-call` reads 0 on both lanes, the other the long form at 120 words, the granting forms at one and 120 words and the fault answer at one and 120 words on the rendezvous arm, and all six shapes on the unheld and unlinked arms (17 shapes) left to SX38). **The Call take for a server bound to its own scheduling context, on the rendezvous, unlinked and unheld arms** (the donated arm never meets one, D50): seL4-MCS's `receiveIPC` with `reply_push (canDonate)` and a server that has a context, so nothing is lent and the caller stays bound to its own. It extends the held arm's no-lend shape (`callLends = false`) to the server that holds its own context on the other arms, for every answer and both lengths; the selector and the four Call-take arms of `RefusalCarryingReplyRecv.lean` route it ahead of the specification's general path, in the word form (no register file passed out of line). | The no-lend Call take's equality over the arm to `endpointReplyRecvAnsweringOnCore`; the selector's guard and the four Call-take arms restated over it. | QEMU: the measurement scenario (`own-context-reply-recv-takes-call`) a step, 0 on both lanes, and the other answers and lengths where they build on it, each 0 |

**Acceptance:**
- a server bound to its own context taking a capability-free `Call` on the rendezvous, unlinked and unheld arms answered in place, under one proof with the Call take's; the guard also requires no bound notification (a server with one stays on the specification's path, not refused);
- the donated arm closed by a lemma (the take always lends there), with no compiled own-context branch, held by a Tier 3 negative anchor;
- the measurement scenario reads 0 because it goes through the in-place take; the general path's table copy is SX29's (D50);
- `RefusalCarryingReplyRecv.c` and its compile time no larger than SX27's (13,074,785 bytes, about 480 s);
- every heap reading 0.

### SX29 — ReplyRecv's legs checks first (D50, D51, D52)

**LANDED at `v0.37.58`** (wrapped at its validated legs, D52; the composite in seL4's order is SX30).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX29.1 | **Measured** (D51): the holds derived from the Lean IR over the committing exports' closure, 1,548 holds, 327 (caller, callee) pairs, 147 source functions in seven classes; ReplyRecv's 12 class (b) functions and its legs' holds are this row's, the rest WS-CK's. | none | the derived set recorded with the IR it was read from |
| SX29.2 | **LANDED at `v0.37.58`** (`endpointReplyOnCoreChecked`, `removeCallerReplyFrameState` and `storeTcbIpcStateAndMessageState` for the reply; `cutReplyFrameOutOrSelfChecked` with `cutReplyFrameStoresState` and `severReplyFrameBelowStoresState` for the splice; `replyRecvPopDonationChecked` for the pop; `cleanupPreReceiveDonationMigratedChecked`, `applyReceiveRendezvousHandoffChecked` and `endpointReceiveDualWithCapsOnCoreChecked` for the receive's three steps; `endpointReceiveDualOnCoreChecked` for the receive body, taking plain senders, call senders with a reply link and without one, and blocking receivers in place, with the specification as its fallback (D52); each with an unconditional `@[csimp]` equality; the IR measurement fell from 1,548 holds to 1,498, none with a checked form as its caller; `RefusalCarryingReplyRecv.c` 12,944,474 bytes against SX28's 12,941,835, its standalone compile 488 s and 500 s on two quiet runs against 479 s and 476 s, the bound carried to SX30; the composite's reply transfer read moved to SX30.1). The legs' checks first. Each leg of the reply-receive path that refuses after a write (`endpointReplyOnCore`, `replyRecvPopDonation`, `endpointReceiveDualOnCore` and `endpointReceiveDualWithCapsOnCore`, `cleanupPreReceiveDonationMigrated`, `applyReceiveRendezvousHandoff`) gets a read-only check on its entry state equal to its post-write refusals, then a perform that writes and does not refuse. | Each leg's unconditional equality to its specification, no invariant assumption. | Tier 3 anchors; the IR measurement shows each leg's hold gone |

**Acceptance:**
- each leg of the reply-receive path checks first, under an unconditional equality to its specification (**met at `v0.37.58`**);
- no checked form holds its entry state across a writing call, by the IR measurement (**met**);
- every heap reading 0 (**met**; the general path, reached only with the in-place take un-routed, keeps one 1 MB cell, which is SX33's, D52 and D53).

### SX30 — The answer's commutation toolkit (D53, D54, D55)

**LANDED at `v0.37.59`** (wrapped at its toolkit, D55; proof-only, no definition changes; the rest of the toolkit and the answer-first equality are SX31).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX30.1 | **LANDED at `v0.37.59`.** The caller's answer as one write, `TCB.withAnswerSlots` (registers, the pending message, the pending receive code and the fault record), with `withMessageSlots`, a delivered frame and a fault restart's frame as its instances; its commutation family in `DeliveryCommute.lean` (the run queue's append, enqueue, removal, deschedule and requeue, the reply link and unlink, a TCB update, and the priority walk with its boosts), each on a table with no resize due, for distinct threads. The message-slot family is now that family's identity instance, each lemma restated, none kept beside it. `AnswerCommute.lean`: the receive side's stores, the queue pop, the physical-write log through every receive-side step that does not record, and the answer's two staging forms (`stageDeliveredMessage`, `applyFaultRestart`) as answer-slot writes that commute with any step that keeps the table and the log. | the toolkit | Tier 3 anchors (13, each break-tested); `RefusalCarryingReplyRecv.c` unchanged against SX29's kept copy (12,944,474 bytes) |

**Acceptance:**
- the toolkit builds, with every premise stated in its lemma (**met**);
- `RefusalCarryingReplyRecv.c` unchanged against SX29's kept copy, or its difference reported;
- every heap reading 0.

### SX31 — The rest of the toolkit and the answer-first equality (D55, D56, D57)

**LANDED at `v0.37.60`** (not proof-only: the run queue's two compiled changes, D56; the equality covers the ordinary answer and the fault restart, and the abandon is SX32's, D57). The frame family `answerReadsKept` (the caller's IPC state and message kept across the tail), the post-receive donation's and the priority hand-off's commutation, the tail's reordering (`replyRecvReceiveTail_answerFirst`), and `endpointReplyRecvAnsweringOnCore_answerFirst` over `answer ≠ some .abandon`. Premises, on every state the reply step can leave: the caller is not the receiver and not the send queue's head at the receive's entry, no resize of the object table is due, and on an ordinary answer a held message of at most four words.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX31.1 | The toolkit's rest, per step of the receive chain, each commuting with the answer at a caller that is neither the receiver nor the send queue's head and keeping the table free of a due resize and the log: the receiver's state and message stores, the reply stasher's record, the caller's reply link, the wake, the queue append, the pre-receive donation's cleanup, the context return, the capability transfer and the post-receive donation; the reads the receive makes, equal through the answer. A theorem, in one statement over every answer kind, that the answer-first composite equals today's composite. Its premises: the caller is not the receiver and not the send queue's head at the receive's entry; the table has no resize due; for a fault abandon, the run queue's links are consistent (`runQueueRefined ∧ objects.invExt`, D55); and the log premise (D55). The definition is not switched. | the toolkit's rest and the equality | Tier 3 anchors, each break-tested; `RefusalCarryingReplyRecv.c` unchanged against SX29's kept copy (12,944,474 bytes) |

**Acceptance:**
- the equality builds over the ordinary answer and the fault restart (D57), its premises the ones listed (**met**);
- `RefusalCarryingReplyRecv.c` unchanged against SX29's kept copy, or its difference reported;
- every heap reading 0.

### SX32 — The caller's answer in the reply step (D53, D54, D58, D59)

**LANDED at `v0.37.61`** (not proof-only: the fault fast forms answer first, D59). `endpointReplyRecvAnsweringOnCore` answers the caller after the reply leg, the pop and the reply's capability transfer and before the receive leg. The in-place theorems are restated through SX31's equality for the ordinary answer and the restart, at a known reply step (`_answerFirst_at`), and directly for the abandon; the take and Call-take guards are carried across the fault answer (`answerGuardFrame`) with no invariant premise. The families (records, run queues, readiness, saved registers, lenders, queue labels, the IPC bundle) and the write and lock sets follow the new order; KernelRecords closes the caller's fault record before the receive. SX33's lemma is `replyRecvReplyStepState` with each family at it. Weakenings: the CapsDelivered `_transfer` theorems and `held_transfer` take `tid ≠ c`, and `take_of_pop` and `callTake_of_pop` take the head and the caller apart and no resize due, all discharged by their callers from the arm's facts; the quiet branch takes a buffer-read frame per consumer (D58).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX32.1 | The reply step answers the caller before the receive, on every path, as seL4's `doReplyTransfer` does: the reply leg, the pop and the reply's capability transfer, then the caller's frame written or its fault answered (`replyRecvAnswerCaller`), all before the receive leg. No refusal changes. The priority-inheritance reversion and the holder's deschedule stay after the receive (D53). | The composed in-place theorems, the invariant families and the write sets restated through SX31's equality, unconditionally where it holds, and directly on the switched composite for a fault abandon, which SX31's equality does not cover (D57); the lemma SX33 reports from: the state after the reply step satisfies the invariant families. | Tier 3 anchors, censuses and conformance rows; `RefusalCarryingReplyRecv.c` no larger than SX29's (12,944,474 bytes) and its compile about 500 s or less |

**Acceptance:**
- the caller answered in the reply step on every path, each in-place equality restated without an invariant premise (**met**);
- `RefusalCarryingReplyRecv.c` no larger than 12,944,474 bytes and its compile about 500 s or less (**met**: byte-identical to SX29's, the performers' signatures unchanged);
- every heap reading 0, `own-context-reply-recv-takes-call` among them;
- the IR measurement run again and its count reported against 1,498 (**met**: 1,498, the same lines).

### SX33 — ReplyRecv's refusals in seL4's order, begun (D51, D52, D53, D60, D61)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX33.1 | **LANDED at `v0.37.62`.** A refused reply lets the receive run, as seL4's `doReplyTransfer` returns with nothing to do: a caller not found, not blocked on reply, or a reply leg the flow gate denies, decided in one place (`replyRecvReplyAnswers`), takes the receive alone, the busy reply's holder cancelled where the flow admits it; the reply's error is dropped (D53, D60). | The spec arm and the three refusal-carrying mirrors restated; every invariant family, the dispatch payoff, the seam coverage and the lock footprint over the new skip case (`replyRecvSkipsReply`); a flow-denied reply's outcome shown unchanged (`receiveResolvedArm_error_of_replyFlowDenied`). | Tier 3 anchors, relation-break-tested; the lock-footprint fixture for a caller not waiting |
| SX33.2 | **LANDED at `v0.37.62`.** Checks first for the pop: its admission (`replyRecvPopAdmits`) read on the entry state, before the reply leg writes, refusing the whole syscall with nothing written (D60); a caller whose reply link names another frame is refused there too. The composite's entry-state reads (the recorded server, the reply's capability request and the caller's receive target) taken before the reply leg (`endpointReplyRecvAnsweringOnCoreChecked`). A refused reply takes the receive site of a reply with no caller: the reply test filters the caller where it is looked up (`replyRecvAnsweredReply?`, `replyRecvAnsweredCaller?`), so no further copy of the receive arm is compiled. The nothing-received outcome (`replyRecvNothingReceived`) the refused receive will report. | The admission exact against the pop on the leg's state under `objects.invExt` (`replyRecvPopDonation_ok_of_admits`, `replyRecvPopAdmits_of_pop_ok`); each fast form's in-place guard implies it with no invariant; the reads-first composite an unconditional `@[csimp]` (`endpointReplyRecvAnsweringOnCore_eq_checked`); `replyRecvPostReceiveDonation_of_not_call`. | Tier 3 anchors, relation-break-tested; the pop-admission scenarios |

**Acceptance:**
- a refused reply lets the receive run, in seL4's order (**met**);
- the pop's refusals checked before the first write, every `@[csimp]` unconditional (**met**);
- the refused receive's report, the wrappers carrying their callee's state and the general path's 1 MB cell moved to SX34 (D61);
- `RefusalCarryingReplyRecv.c` no larger than SX29's (12,944,474 bytes) (**not met**: 12,959,438 bytes, 14,964 bytes (0.12%) over, compiled in 427 s; the bound moves to SX34 with the general path's 1 MB cell);
- every heap reading 0; the IR measurement run again and its count reported against 1,498 (**met**: 1,498, the same lines as SX32's).

### SX34 — ReplyRecv's refused receive, and its wrappers carrying their callee's state (D53, D60, D61, D62, D63, D64)

**LANDED at `v0.37.63`, wrapped at its validated point (D64).** Its C bound and the 1 MB cell on the general path's capability installs moved to SX35.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX34.1 | **LANDED at `v0.37.63`.** Refusal-carrying forms of the reply-receive's pop and post-receive donation, down to their stores: where a refusal precedes the operation's first write the form returns its input, so nothing is held; where it follows one, the form carries the state at that point. Where this reaches code WS-CK's CK2 owns, it is done for the reply-receive path only. The donation is admitted before its first write (`donationPushRefusal?`, D62). | Each form's unconditional equality to its specification. | Tier 3 anchors, relation-break-tested |
| SX34.2 | **LANDED at `v0.37.63`** (its C bound moved to SX35.2, D64). The refusal-carrying composite and the arm's transition over it, each refusal carrying the state its step stopped in; a refused receive reports the nothing-received outcome (the priority-inheritance reversion, and the holder's deschedule where the pop returned a context, D53) on the state the receive returned (D60's option (b)); the 12 refusal-carrying reply-receive wrappers carry their callee's state, not the entry state. | The composite's and each wrapper's equality to its specification restated; the report's consumers gain the refused-receive case (the invariant families at the stopped states; the capability-fault delivery on the two cases it always took, since the stopped state raises a fault only where it stopped where it started, so no consumer restates its current-thread fact, D63); the entry and cross-core non-interference proofs restated. | Tier 3 anchors; `RefusalCarryingReplyRecv.c` back to 12,941,835 bytes or less and its compile to about 480 s or less (SX28's), measured against a kept copy of SX29's generated C |
| SX34.3 | **LANDED at `v0.37.63`** (the capability installs' 1 MB cell moved to SX35, D64). QEMU: the own-context reply-receive on the general path (before the in-place take routes it), and a donating one. | none | the step reading no 1 MB cell on both lanes (110 cells, one of them 1 MB, at SX29, D52), then the legs measured again; every other heap reading 0 |

**Acceptance:**
- no hold of the reply-receive chain's state across a writing call, by the IR measurement (**met** for the chain's own holds: 1,494 against 1,498, the composite's, both rendezvous wrappers' and the pop's gone; `ipcUnwrapCapsLoop`'s class (d) hold, which SX34 exposed, moved to SX35.1, D64);
- ReplyRecv in seL4's order both ways, its invariant and non-interference proofs restated (**met**; the receive capability's order is SX36, D63);
- `RefusalCarryingReplyRecv.c` at 12,941,835 bytes or less and its compile about 480 s or less (**not met**: 12,966,427 bytes, 24,592 over, compiled in 485 s; the bound moves to SX35.2, D64);
- the general path's step reads no 1 MB cell (**met** for the own-context step, 87 cells and 4,776 bytes, and the donating Call takes; **not met** for the four that install a capability, one 1 MB cell each, moved to SX35, D64); every other heap reading 0 (**met**).

### SX35 — The install checked first, and the C bound (D64)

SX34's remainder (D64): the general path's 1 MB cell on the capability
installs, and `RefusalCarryingReplyRecv.c`'s size and compile bound.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX35.1 | `ipcUnwrapCapsLoop` holds nothing across an install: it reads each install's admission (`ipcTransferSingleCap`'s CNode, revocability, derivation and insert checks) on the state before the install writes, or it calls a refusal-carrying install that hands back the state it stopped in, so the `.error` fallback no longer keeps the loop's entry state live. This covers the reply-receive path's capability transfer (`receiveTransferCaps` under `endpointReplyRecvAnsweringBodyR`); WS-CK's class (d) row (CK2) cites it and does not redo the loop. | The loop's (or the install's) unconditional equality to its specification; `ipcUnwrapCapsLoop_rel` and the capability-transfer consumers restated over it. | Tier 3 anchors, relation-break-tested; the IR measurement shows no hold in `ipcUnwrapCapsLoop` |
| SX35.2 | `RefusalCarryingReplyRecv.lean`'s proofs move into a proofs module of their own, following the Operations/Invariant split, so their compiled match splitters leave `RefusalCarryingReplyRecv.c`. The two splits SX34 added (`replyRecvReplyRefused`'s and `replyRecvAnsweringReport`'s) are avoided where a proof can do without them. | The moved proofs unchanged in statement; every consumer's import updated. | `RefusalCarryingReplyRecv.c` at 12,941,835 bytes or less and its compile about 480 s or less, measured against kept copies of SX29's and SX34's generated C |
| SX35.3 | Release, with the debug QEMU run on the general path (the in-place takes unrouted, the patch never committed) over the own-context reply-receive and the donating Call takes that install a capability. | none | no 1 MB cell on either lane (one per installs-cap form at SX34, D64); every other heap reading 0 |

**Acceptance:**
- no hold of the loop's state across an install, by the IR measurement;
- `RefusalCarryingReplyRecv.c` at 12,941,835 bytes or less and its compile about 480 s or less;
- the general path's own-context and installs-cap steps read no 1 MB cell; every other heap reading 0.

### SX36 — ReplyRecv's receive capability resolved after the reply (D53, D60, D63)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX36.1 | ReplyRecv's receive-capability lookup and receive gate move after the reply step, as seL4's `handleRecv` places them (D63). The entry resolves the reply capability and runs the reply step. It then resolves the receive capability on the post-reply state: the operand lookup, the slot checks, the kind and the receive right. A bad receive capability answers the caller, then delivers `CapFault(epCPtr, true)` on the post-reply state. The receive's flow gate still runs before anything the receive makes observable. This takes ReplyRecv's part of SX42.1 (the receive on the state after the invoke phase, for a reply capability), and SX42.1 says so. The declared lock set is measured against the post-reply walk; if the entry footprint cannot cover it, the row stops and reports (D63). | The arm's and the dispatch's equalities to their specifications restated; every family over the reply-receive's report (the run-queue, kernel-records, queue-label, lender, mapping and reschedule stages, the seam coverage and its refusal footprint, the lock bracket, `FaultEntry`) over a lookup on the post-reply state; the entry and cross-core non-interference proofs. | Tier 3 anchors, relation-break-tested; QEMU: a valid reply with a receive capability not found, of the wrong kind and without the receive right, each answering the caller and faulting, at 0 |
| SX36.2 | The passive server stays current until the scheduling point, as seL4's `rescheduleRequired` leaves `ksCurThread` (D63). The holder's deschedule in the nothing-received outcome and on the reply-receive's success path keeps the current slot, in a holder-only form (`descheduleAtPlacement` itself is unchanged). The scheduling point's successor step also fires on a current thread that cannot be scheduled. It takes a current thread with no context off the core without re-enqueueing it, so no thread runs without a context. | Every success-path family over the holder's deschedule and the nothing-received outcome restated; the scheduling point's drop step with its invariant suite and seam coverage; the non-interference proofs of the reply-receive step and the scheduling point. The run-queue and kernel-records consumers' fault-delivery branch takes the post-reply case SX36.1 makes reachable (D63: SX34 needed no interim form). | Tier 3 anchors; QEMU: a passive server's ReplyRecv with a refused receive capability after its pop, at 0 |
| SX36.3 | Release: the generated C's size and compile time, and the heap readings, measured again. | none | every heap reading 0 |

**Acceptance:**
- ReplyRecv in seL4's order for a refused receive capability: the caller answered, the fault on the post-reply state;
- the passive server current until the scheduling point, and never run without a context;
- every heap reading 0.

### SX37 — The state-hold gate (D51)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX37.1 | A gate over the IR of the committing exports' closure that finds each call passing the state at a destructive position while the caller keeps it live, against a pinned list of the holds WS-CK has still to remove. The list may only shrink: a hold not on it fails, and an entry with no hold behind it fails. A closure call whose callee the gate cannot resolve fails closed. The closure does not reach a `@[csimp]` source through its replacement: a specification the compiler replaces keeps its own IR, and it is counted only where compiled code still calls it (a checked form's fallback does), since counting it otherwise would pin holds no list could shrink. | none | the gate, break-tested by restoring one ReplyRecv wrapper's pre-state hold |

**Acceptance:**
- the gate runs in Tier 2 and passes on the tree, with SX29's, SX32's, SX33's and SX34's holds absent from the pinned list;
- an unresolved closure call fails the gate.

### SX38 — The composed path's remaining QEMU scenarios (D49, D50)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX38.1 | QEMU scenarios for the Call takes with no scenario to build on at `v0.37.56`: the held and unheld arms' Call takes (12 shapes), the donated arm's Call takes (6 shapes, carried from SX27.1: no scenario runs the donated arm's Call take), and the rendezvous and unlinked arms' Call takes answering a fault at one and 120 words (4 shapes); every fault-answer shape needs a fault lane whose server holds no context; carried from SX26.1, the Send take's eight shapes (the donated arm at one and 120 words, inert, installing and answering a fault; the unheld arm answering a fault at one and 120 words); and the context-holding server's Call-take shapes SX28.1 leaves without a step. | none | QEMU: one step per shape, each 0 |

### SX39 — Page-table teardown and per-frame W^X

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX39.1 | PageTable_Unmap as seL4's `performPageTableInvocationUnmap`: the table is unmapped from its address space and cleared even while mappings pass through it, where the model refuses `revocationRequired`; every frame capability whose recorded mapping passed through the table has its mapping record cleared (seL4 leaves `capFMappedASID` stale; the model's record drives teardown, so it is cleared). | The mapping-record stage, `pageTableInstallLive` and the teardown theorems over the cleared table and records; the lock footprint names each cleared capability's CNode. | SX8.1's row; QEMU: unmap of a populated table, at 0 |
| SX39.2 | Per-frame W^X as an invariant: no frame is mapped writable and executable at once, in one address space or across two, held in the proof-layer bundle rather than by the map's check alone. | Preservation over Page_Map, Page_Unmap, PageTable_Unmap and every teardown. | Tier 3 anchors |

### SX40 — Per-invocation rights as `Option AccessRight`

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX40.1 | Each invocation's required right becomes `Option AccessRight`, `none` where seL4 checks no right: SchedContext_Bind's `.write` and Page_Unmap's `.read` go; Untyped_Retype's rights and Page_Map's `maskVMRights` follow seL4 (consumes SX8.1's rows). The flow gates stay, before anything observable, with their non-interference proofs. | The gate theorems and the dispatch non-interference cases over the optional right. | SX8.1's rows; QEMU: each changed invocation through a capability without the old right, at 0 |

### SX41 — seL4's Running thread state per core

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX41.1 | The thread state seL4 calls Running, held per core, including self-suspend by Call: seL4's `suspend` leaves the caller `Inactive`, so `handleInvocation` writes no reply and the restart PC stays at the `SVC`. The no-reply half landed with SX7 at `v0.37.33` (`syscallReturnOutcome` answers only a runnable caller); this row makes a thread stopped inside its own syscall (a self-suspend, a Call that links no reply) resume at its `SVC`, where it now resumes past it with its request registers. Gap closed here (D24, "Match in SX11", this row before D32 renumbered it): until this row, a thread whose context SX8.2 returned (`.unbound`) is still scheduled at its legacy priority, where seL4 never runs a thread with no scheduling context; this row makes a thread with no scheduling context unschedulable, as in seL4-MCS. The scheduler's run rule is not changed in SX8. The row also owns the boot's half: seL4-MCS's boot gives the root thread its initial scheduling context, bound (`create_initial_thread` binding the root server's context), so the root thread can run; the checked boot today binds no thread (`bootSafeTcbCheck`, SX10.1), so once a thread with no context is unschedulable the boot must create the initial threads' contexts and bind them. Each such binding is a binding pair, so it is created at equal labels (the thread's and its context's, D37), and the boot base case `bootFromPlatformCheckedStartedFor_bindingLabelsEqual` is restated over it. | The thread-state invariants and the scheduler's per-core current-thread theorems over the new state. | `smp_4core_scheduler.expected`; QEMU: `tcb-suspend-self-by-call` |

### SX42 — The invoke phase of NBSendRecv, NBSendWait and ReplyRecv

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX42.1 | seL4 runs `handleInvocation(isCall = false, isBlocking = false, canDonate = true, firstPhase = true, dest)` and then `handleRecv`: `dest` is x8 for NBSendRecv and x6 for NBSendWait and ReplyRecv. A lookup fault is dropped and an error discarded, and the receive still runs; only preemption skips it. The invoke phase is a full `decodeInvocation` on `dest`'s capability (consumes SX8.1's rows and SX41.1's state). In `API.syscallEntryChecked`, before the receive decode, when x7 is one of the three words: select the operation on `dest`'s capability type and the label, decode with `capAddr := CPtr.ofWord dest`, dispatch, keep the handed state on an error and continue on the new state on success, then the receive on it. The frame is already in the TCB (`saveCapturedSyscallFrame`), and `captureEntryWords` captures the invoke phase's overflow words and extra capabilities for `dest`. For ReplyRecv with a reply capability, the receive on the post-reply state (its capability lookup and gate after the reply) is SX36.1's (D63); this row keeps ReplyRecv's invoke phase on any other capability. | Every family over `syscallEntryChecked` takes the two-phase case: the compiled entry (`RefusalCarryingEntry`, `syscallEntryRoutedK`, which runs the routed dispatch twice), the seam and its refusal record (receive phase only), `FineLockFlow`, `SyscallLockBracket` (both phases' sets), the per-entry stage lemmas and `FaultEntry`. | `smp_ipc_4core.expected`; QEMU: each of the three with a send-phase fault, an error and a success, at 0 |

### SX43 — Timeout faults and the MCS TCB calls

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX43.1 | A TCB timeout-handler slot, and `SetTimeoutEndpoint` (extra capability 0). | The slot invariants. | `sele4n-abi` `args/tcb.rs` |
| SX43.2 | `SetSchedParams`: the authority, scheduling context and fault endpoint as extra capabilities; MCP and priority as words. | The MCP authority and binding theorems. | the same |
| SX43.3 | A running thread's budget overrun with a valid timeout handler raises `seL4_Fault_Timeout` (MCS tag 5, with the context's badge and consumed time). A blocked IPC is no longer timed out: `timeoutThread` and `ipcTimeout` retire, and the discriminant is reserved. | The budget and CBS theorems; the donation-chain (WS-OD, WS-HP) theorems that cited `timeoutThread`; `faultLabel_ne_timeout` retires into the timeout fault's label theorem. | `fault_handling_4core.expected`; `smp_4core_scheduler.expected` |

**Acceptance:** `timeout-fault-delivered`, `blocked-call-not-timed-out`,
`set-sched-params`.

### SX44 — seL4's CNode invocation set (D16, D17)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX44.1 | Delete and Revoke address their target by index and depth (`lookupTargetSlot`). | The two arms' decode and preservation. | `args/cspace.rs` |
| SX44.2 | Mutate: a Move with `updateCapData` preserving. A null result is IllegalOperation. | `cspaceMove`'s CDT, link and occupancy theorems over a rewritten capability. | the same |
| SX44.3 | Rotate, per `cnode.c:231`. | The CDT, `cdtLinksAgree` and `CapTreeShape` preservation for two moves; the footprint (3 slots, 2 roots). | the same |
| SX44.4 | CancelBadgedSends: all four endpoint rights; the senders with the badge are removed and set to Restart; badge 0 does nothing (`endpoint.c:489`). | Endpoint queue well-formedness; run-queue insertion; non-interference for the arm. | `smp_ipc_4core.expected` |

**Acceptance:**
- `cnode-delete-index-depth` and `cnode-revoke-index-depth`.
- `cnode-mutate-guard` and `cnode-mutate-badged-refused`.
- `cnode-rotate` and `cnode-rotate-pivot-is-source-refused`.
- `cnode-cancel-badged-sends`: only the matching senders restart.

### SX45 — seL4's error codes in the label (D1)

This row needs F1 to hold. SX3, SX4, SX7 and SX43 made it hold.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX45.1 | `KernelError.sel4Error`, total (D1). The error frame's label is the seL4 code. `errorLabelBase` retires. | `receivePhase_noErrorFrame`: no receive-phase syscall returns an error frame. `sendInvocation_noErrorFrame`. The label round trip over seL4 codes with the payload. The `faultLabel_lt_errorLabelBase` family retires into these. | `abi_layout.expected` (`errorLabelBase` out); `syscall_return_abi.expected`; the `sele4n-types` error table; `test_rust_conformance.sh` |

**Acceptance:** every error scenario re-pinned to seL4's codes; a fault
handler's receive reads fault tags only.

### SX46 — seL4's remaining invocations (D23)

SX8.1's conformance table marks every seL4 invocation label seLe4n does not
implement as absent; the ones no earlier row owns are this row's. Each is
implemented as seL4-MCS's decode and perform (aarch64, the default build) with
its specification, a proven-equal fast form, the flow gate before anything
observable, its NI and invariant obligations, an exact SMP lock set and zero
allocation per entry. `ARM_SMC_Call` stays absent, as in seL4's default build
(`CONFIG_ALLOW_SMC_CALLS` off).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX46.1 | **The invocations no earlier row owns** (labels 2–5, 16, 17, 30–32, 39–41, 48–56 of SX8.1's table, and label 1's argument list). TCB: `ReadRegisters`, `WriteRegisters`, `CopyRegisters` (`tcb.c`, the suspend and resume flags and the arch register order), `Configure`, `SetTLSBase` and `SetFlags` (`UnbindNotification` is implemented already). Domain: `DomainSet_Set` and the domain schedule invocations `DomainSchedule_Configure` and `DomainSchedule_SetStart`. VSpace and page: `ARM_VSpace_Clean_Data`, `Invalidate_Data` and `CleanInvalidate_Data` (`Unify_Instruction` is implemented already), and the page's `Clean_Data`, `Invalidate_Data`, `CleanInvalidate_Data`, `Unify_Instruction` and `GetAddress`. ASID: `ARM_ASIDControl_MakePool` and `ARM_ASIDPool_Assign`. IRQ: `ARM_IRQ_IssueIRQHandlerTrigger` and, in the SMP build, `ARM_IRQ_IssueIRQHandlerTriggerCore`. `Untyped_Retype` drops the extra `childId` word to seL4's six-word argument list, the child placed at the untyped's free index as seL4 places it. Every absent conformance-table row this row owns becomes implemented, its decode, arity, return shape and errors checked by the suite. | Each invocation's preservation obligations (`ipcInvariantFull`, the scheduler bundle, the records and mapping stages, saved registers, slot confinement, cross-core NI) and its fast form's `_eq`; the retype's decode round trip without `childId`. | the conformance suite (every row implemented but `ARM_SMC_Call`); QEMU: each invocation's success and first refusal at 0; `abi_layout.expected` for the retype's arguments |

**Acceptance:** the conformance table has no absent row but `ARM_SMC_Call`;
every new path measured at 0.

### SX47 — The lock-set ceiling lowered to the kernel's largest footprint

The owner's request (2026-11-25): "Remember to reduce the max lock set from 32
to what the max is after all the changes."  The row runs after every
other WS-SX change has landed, so the footprints it measures are final, and
before the closure (SX48).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX47.1 | **`Concurrency.maxLockSetSize` lowered from 32** (`SeLe4n/Kernel/Concurrency/Locks/LockSet.lean`) to the largest lock-set footprint the kernel can request with every WS-SX change in place. The value is derived from the code's static size theorems, not estimated: the `_size_le_maxLockSetSize` family (the per-operation lock-set bounds in the IPC, scheduler, CBS, timer and choose-thread footprints) and the CSpace walk's refusal (`declaredLockSetForCSpaceWalk_some_size_le`, the walk refusing a footprint past the ceiling). The largest of them is the new value. `retypeFanOutLimit` is defined from the ceiling (`maxLockSetSize - retypeBaseLocks`), so the row states what the retype fan-out becomes and checks it against seL4's retype fan-out; if lowering the ceiling would refuse a retype seL4 performs, the row stops and reports rather than lowering past it. | Every bound in the family and every consumer of `boundedWait_under_2pl` (`Locks/Deadlock.lean`) and the WCRT results re-proved at the new value. | A Tier 3 anchor pins `maxLockSetSize`'s value; the existing footprint anchors re-read at it |

**Acceptance:**
- `maxLockSetSize` equals the largest footprint the size theorems bound, and every bound and bounded-wait consumer is proved at that value.

### SX48 — Closure

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX48.1 | WS-CV's CV1.2, folded into WS-SX (maintainer's decision; WS-CV closes alongside WS-SX at `v0.38.0`): the information-flow surface (`ObservableState.machineRegs`, the per-core fragments, `lowEquivalentSliceOnCoreCheckWithRegs`) moves to lawful equality, and `RegisterFile.beq_iff_eq'` / `beq_self` / `beq_symm` / `beq_trans` (`SeLe4n/Machine.lean:528-539`) retire with their last consumer. At `origin/main` that is 51 citing sites in 13 files; the build enumerates them when the lemmas are deleted. The spec's information-flow equality passages and the evidence-index rows of the re-proved unwinding relations change in the same row. **Zero allocation**: proofs and the test-side `…CheckWithRegs` comparison only, no compiled entry. | The `machineRegs` unwinding relations re-proved on lawful equality; every `beq_*` citing site rewritten to `beq_iff_eq` / decidable equality before the lemmas are deleted. | Tier 3 anchor `machineRegs_beq_self` retires |
| SX48.2 | `docs/CLAIM_EVIDENCE_INDEX.md` gets a row per seL4 behaviour this plan follows. The spec's syscall-boundary section is rewritten to the seL4 ABI. The workstream is closed in `docs/REGISTERED_DEBT.md` and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, and this plan moves to `docs/dev_history/planning/`. **Full documentation sweep against the final tree:** the spec, every GitBook chapter on the syscall ABI and CSpace, README metrics, `docs/DEVELOPMENT.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, the `docs/REGISTERED_DEBT.md` index row, and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, whose WS-SX section moves to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`. **Refresh every not-yet-started plan** against WS-SX's final tree: the remaining WS-UC rows UC6–UC10, `CONTEXT_BY_VALUE_PLAN.md`, `HIERARCHICAL_CBS_PLAN.md`, `LOCK_STATE_SEPARATION_PLAN.md`, and every other plan under `docs/planning/` — file:line citations, names, rows the new ABI makes obsolete or newly needs, and the decisions it affects. If the refresh is too large for SX48, it is the very next PR, landed before any next-row code. **WS-CV's closure (its CV5.2), in the same row** (consumes SX48.1): the `v0.36.47` register-file debt row is deleted from `docs/REGISTERED_DEBT.md`; the WS-CV section of `docs/agent_guide/WORKSTREAM_CONTEXT.md` moves to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`; `CONTEXT_BY_VALUE_PLAN.md` moves to `docs/dev_history/planning/`, every live link to it (a search for `CONTEXT_BY_VALUE_PLAN` outside `docs/dev_history/`) repointed to cite it by workstream ID; and `HIERARCHICAL_CBS_PLAN.md` is re-checked against it, which the plan refresh above covers. | none | `check_claim_evidence_citations.py` |

## 5. Estimate

| Row | Sessions |
|---|---|
| SX1 | 2 |
| SX2 | 3–4 |
| SX3 | 1 |
| SX4 | 2 |
| SX5 | 3–4 |
| SX6 | 5–6 |
| SX7 | 3–4 |
| SX8 | 3 |
| SX9 | 2 |
| SX10 | 2 (landed) |
| SX11 | 3–4 |
| SX12 | 3 |
| SX13 | 3 (landed) |
| SX14 | 3 (landed) |
| SX15 | 1–2 (landed) |
| SX16 | 3 (landed) |
| SX17 | 2–3 (landed) |
| SX18 | 1 (landed) |
| SX19 | 3–4 (landed) |
| SX20 | 1 (landed) |
| SX21 | 2–3 (landed) |
| SX22 | 1 (landed) |
| SX23 | 1–2 (landed) |
| SX24 | 2–3 |
| SX25 | 3 (ran about 6, D48) |
| SX26 | 2–3 (landed) |
| SX27 | 2–3 (landed, D49) |
| SX28 | 2 (measured 3.25–4.25, about 3.5, D50) |
| SX29 | 5–7 (measured at SX29.1: the whole sweep about 17–24, its remainder WS-CK's, D51; landed, ran about 7, D52) |
| SX30 | 2–2.5 (the answer's move measured at about 5–6 and wrapped, D54; landed at its toolkit, ran about 3, D55) |
| SX31 | 3–4 (measured at SX30's third session, D55) |
| SX32 | 2.5–3.5 (less where SX31's equality carries a theorem by rewriting) |
| SX33 | 4–5 (wrapped at its validated pieces, ran about 4.5, D61) |
| SX34 | 4.5–5.5 (measured at SX33, D61; wrapped at its validated point, ran about 9, D64) |
| SX35 | 3–4.5 (measured at SX34, D64: the install 1.5–2, the proofs module 1–1.5, the release 0.5–1) |
| SX36 | 6.5–9 (measured at SX34, D63: the move 2.5–3.5, the current slot 3.5–4.5, the release 0.5–1) |
| SX37 | 1 |
| SX38 | 2–3 |
| SX39 | 2 |
| SX40 | 1 |
| SX41 | 1–2 |
| SX42 | 2 |
| SX43 | 2–3 |
| SX44 | 2 |
| SX45 | 1 |
| SX46 | 4–5 |
| SX47 | 1–2 |
| SX48 | 2 |

About 121–150 sessions in all. The largest risks:
- the boot base case (SX5.3);
- the IPC-buffer read path (SX6.6);
- keeping refusals at 0 heap cells (D2b).

## 6. Asides recorded at planning

- `tcbSetAffinity` has no seL4-MCS counterpart: a thread's core follows its
  scheduling context's `SchedControl` core. SX7.1 gives it a model-only label.
  Retiring it is the owner's call, and it is not registered as debt.
- The `partialResolution` row of `docs/REGISTERED_DEBT.md` table C is
  unaffected. IPC keeps seL4's drop-on-failure, and invocations fault, as seL4
  does.
