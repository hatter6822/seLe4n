# WS-SX — seL4 ABI fidelity

> **Workstream**: WS-SX (the syscall and invocation ABI made seL4's).
> **Status**: **ACTIVE** — registered at `v0.37.19` (this plan, docs only);
> SX1 landed at `v0.37.20`; SX5 landed at `v0.37.31`; SX6 at `v0.37.32`;
> SX7 at `v0.37.33`, which split its remainder into SX8 and SX18–SX21 (D20);
> SX8 at `v0.37.36` (SX8.1 the conformance table, SX8.2 donation and return,
> SX8.3 label 36 and the unbind of a donated holder, D22), which split its own
> remainder into SX9, SX12 and SX17 (D32). The rows after SX8 were renumbered then:
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
> became SX14 (the frame family threaded, the pops as labelled steps), SX15
> (the creating sites) and SX16 (the premise moved, the refusals deleted), and
> SX14–SX23 became SX17–SX26.
> **Baseline**: the tree at `v0.37.18` (WS-UC UC5). Every `file:line` below was
> read against it.
> **Rows**: SX1–SX26, numbered in the order they are implemented, one PR each.
> Each row consumes only lower-numbered rows. A row that changes a transition
> carries the proofs that cover it. No two rows run in parallel.
> **Decisions**: D1–D32, D34, D36–D41 (§3). D1–D17, D40 and D41 are each **default taken; owner card open**;
> D7 follows the owner's standing rule (implement seL4's behaviour, never defer
> it). D18–D21 were decided by the owner when SX7 closed; D22 when SX8 started;
> D23–D32 during SX8; D34 when SX9 started; D36 and D37 during SX9; D38 during SX10; D39 when the binding-invariant row
> started; D40 during SX13; D41 during SX14.
> **Supersedes**: the "Next PR" scope in
> `docs/agent_guide/WORKSTREAM_CONTEXT.md` (the root task's boot IPC buffer
> and the guard in the capability with `CNode_Mutate`). Both are rows here
> (SX5, SX2 and SX23). Neither was debt, and neither is now.

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
  - Once SX3, SX4, SX7 and SX22 make F1 true here, a receive never yields an error
    frame. seL4's codes 1–10 can then sit in the label with no receive-side collision.
  - One overlap remains, and it is seL4's own: a Call on an endpoint can answer
    `seL4_InvalidCapability` (a capability without the send right,
    `decodeInvocation`, `objecttype.c`) or the server's reply, whose label the
    server chooses.
  - SX24 makes the switch and proves the receive half as a theorem.
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

D1–D17, D40 and D41 are each **default taken; owner card open**; D18–D32, D34 and D36–D39 are the owner's.
A different answer changes only the rows that cite it.

- **D1. The error label.** *Default:* **seL4's error codes (1–10) in the
  label** (SX24), and the payload in seL4's MR layout (SX1).
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
  per-frame W^X (SX18), per-invocation rights (SX19), the Running state per
  core (SX20) and the compound syscalls' invoke phase (SX21) are rows of
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
  that no earlier row owns gets one new row, SX25, landed before the closure
  (now SX26). `ARM_SMC_Call` stays absent, as in seL4's default build.
- **D24. A thread with no scheduling context.** *Decided by the owner
  (2026-11-20, "Match in SX11", the row now numbered SX20):* in SX20 a thread
  with no scheduling context (`.unbound`, including one whose context SX8.2's
  `maybeReturnSchedContext` returned) becomes unschedulable, as in seL4-MCS,
  which never runs a thread without one. SX8 leaves the scheduler's run rule
  unchanged (SX20.1).
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
  SX9 (notification-lend assurance), SX12 (D31) and SX17 (one composed
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
  takes it of both runs. Still one premise. SX10's invariant (completed in SX13–SX16,
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
  premise moved, the refusals deleted), now SX13–SX16 (D40). The rows after
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
- **D40. SX13's wrap.** *Default taken (2026-11-24, "Wrap, new rows"); owner
  card open.* SX13 closes at `v0.37.42` at its validated point: the binding
  grow and the binding-words leaf lemmas. Its first cut, measured by stubbing
  every failing lender declaration to a fixpoint, needs 37 declarations in 9
  files and a census witness, about 10 sibling lemmas for the summaries that
  forget the binding words, and, uncounted by the stubs, the restatement of 30
  `LendersFrame` theorems: the pops grow the binding views, so they are no
  longer links shrinks. That is well over 1.5 times the row's estimate (owner
  rule D32). The remainder becomes three rows: SX14 (the frame family threaded,
  the pops as labelled steps), SX15 (the creating sites and preservation over
  every writer) and SX16 (the premise moved and the refusals deleted, SX13.2
  and SX13.3 as first stated). The rows after SX13 are renumbered (SX14–SX23
  became SX17–SX26). No live path lends a context across unequal labels; the
  gap is in the proof, not the kernel.
- **D41. The cancel's pop returns to the frame's recorded caller ("Match
  seL4").** *Default taken (2026-11-24); owner card open.* The cancel's
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

The label is unchanged until SX24.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX1.1 | `LookupFault` (`invalidRoot`, `missingCapability bitsLeft`, `depthMismatch bitsLeft bitsFound`, `guardMismatch bitsLeft guardFound bitsFound`, seL4's `lookup_fault`). The D2 payload fields; `depthMismatch` retires into `failedLookup`. Every site sets its number: `invalidCapability` is `0` for the invoked capability and `i + 1` for argument capability `i`, and every argument capability (a receive's or reply-receive's reply capability included) is resolved through one boundary that applies it (`syscallLookupArgumentCap`, and `KernelError.argumentCapRefusal` in the compiled forms). The CNode-op refusals take seL4's: an empty source is `failedLookup true (missingCapability srcDepth)` (`cnode.c:111`). | The discriminant round trip over codes (`toDiscriminant`, `ofDiscriminant?`), the payload ignored; every `cases e <;> decide` restated per code. | `main_trace_smoke.expected` (error `Repr`); Tier 3 `KernelError` anchors; the `rust/sele4n-types/src/error.rs` mirror; `test_rust_conformance.sh` |
| SX1.2 | `errorFrame` carries the payload in seL4's MR order (x2–x5), with MR4 written to the caller's buffer `msg[4]` (D3) and the length as `setMR` returns it. Compiled refusal arms pass the payload unboxed (D2b). `syscallAbiVersion` 4 → 5. | `errorFrame_payload_roundtrip`. The error path's frame theorem restated: it changes only the caller's `msg[4]`, on a 5-word payload with a buffer. `errorFrame_x1_decodes` gains the length. | `syscall_return_abi.expected`; `abi_layout.expected` (version, payload offsets); `rust/sele4n-abi` frame decode |
| SX1.3 | **LANDED at `v0.37.21`.** A user word at or above `2^63` stays a word on the entry path. `RegValue` is a `UInt64` (`RegValue.word`, `.val` its `toNat`); the syscall number, the message info and the capability address are decoded from the word (`@[csimp]` `decodeSyscallId_eq_word`, `decodeMsgInfo_eq_word` and the router's `registerRoutedSyscallOf_eq_word`; `decodeCapPtr` reads the word as the address, and the `invalidCapPtr` refusal of a value past `2^64` it can no longer meet is deleted, its code 35 retired beside 37, no other code renumbered). The routed decodes test a range on the word before making a `Nat` (`wordLtNat`): the VSpace map and unmap's ASID and address and a map's permissions (`pagePermissionsOfWord?`), and an affinity (`SetAffinityArgs.affinityRaw : UInt64`, `decodeAffinity` on the word). A mint's badge is tested on its word (`badge.word = 0`). The fault and overflow words are read as words (`pairAddrIs`, `syncedWordFromW`, `@[csimp] syncedWordFrom_eq_w`). A configure refuses a budget or period above seL4-MCS's `MAX_PERIOD` (`UINT64_MAX / 8` ticks) with `rangeError`, as `decodeSchedContextConfigureArgsChecked` and `validateSchedContextParams` now do, and a deadline word above it with `invalidArgument 4`, so no stored budget, period or deadline reaches `2^63`. The raw-slot decodes that SX6.3, SX6.6 and SX23.1 re-decode, and the model-only calls SX7.1 re-encodes, keep their conversion; they are a registered row. | The register round trips restated on the word (`regMessageBody_word`, `regReplyRecvBody_word`, `regMessageRegs_word`); `setAffinityArgs` round trip without its word hypothesis; `decodeSchedContextConfigureArgsChecked_invariants` and `validateSchedContextParams_implies_wellFormed` gain the bound; `cspaceMintPerformAt_eq_impl` on the badge word; the routed receive and reply-receive decode theorems on `replyAddr.word`. | QEMU: `vspace-map-wide-asid`, `vspace-map-wide-vaddr`, `vspace-map-wide-perms`, `vspace-unmap-wide-vaddr`, `tcb-set-affinity-wide`, `mint-wide-badged-notification` (now measured), `configure-wide-budget-and-period`, `configure-wide-deadline`; `configure-zero-budget-max-period` and `configure-budget-over-wide-period` now expect the `MAX_PERIOD` refusal |

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
| SX3.1 | **LANDED at `v0.37.24`.** The wrong-kind and missing-right faults were already the lookup's (`receiveGateRefuses`, scenarios `receive-wrong-type-cap-fault`, `wait-wrong-type-cap-fault`, `reply-recv-wrong-type-cap-fault`, `receive-no-right-cap-fault`); a notification bound to another thread now joins them (`receiveBoundRefuses`, `notificationBoundElsewhere`), checked in the lookup gate and again in the wait arm after the flow check. Recv and Wait answer `CapFault(cptr, inRecv)` with `missingCapability 0` for each of: a capability of the wrong kind, a missing receive right, or a notification bound to another thread (`syscall.c:470`–`:513`). | `capFaultReceivePhase?` partition restated. Every receive arm returns no error frame but the two that SX4 and SX22 retire. | `fault_handling_4core.expected`; `main_trace_smoke.expected` |
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
it. The rest of the piece moved to SX8 and SX18–SX21 (D20).

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
remainder is SX9, SX12 and SX17 (D32).

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
| SX9.1 | **LANDED at `v0.37.38`.** **The two-run theorem for every observer** over the checked notification lend (`maybeDonateSchedContextFlowing`, D30). An observer the context's label does not flow to: the single-run `maybeDonateSchedContext_lowEquivalent` (`InformationFlow/PerCoreSchedulerNonInterference.lean:1956`) closes it, given that the woken thread is hidden (a thread/object label coherence fact). An observer cleared for the context (so, by D30, for the thread): the lend's writes are visible, and the projection erases the inputs that decide it (`Notification.schedContextCode`, `InformationFlow/Projection.lean:371`; `TCB.scBinding*`, `:214`). **Ruled by the owner (D34):** a finer projection for that observer, which shows those words. The lend's visible writes read three more inputs, ruled when the row started: the thread's `cpuAffinity` (which core it is placed on) is shown with the binding words to an observer cleared for the thread, as D34's principle gives; the machine timer (the context's `releaseReadyHead`) stays outside the projection (covert channel CC-2), and the theorem takes the two runs' agreement on it as a premise, as the tree's one two-run theorem over an unprojected read does (`activateThreadOnCore_lowEquivalent_pair`); the thread's run-core word is read off the run-queue refinement invariant. The NI theorems that were unconditional only because the projection erased those words (the donation push, pop and keep, the Call donation, the affinity write: WS-RR RR7.22, WS-OD OD3.2 and OD4.1, WS-SM SM5.H.4) are restated with the observability hypotheses they need, superseded by D34; each consumer step discharges them from the flow gates it passes (D27, D28, D30), or, where the step makes a legitimate visible flow, is proven in the two-run form with the pair lemmas. **One consumer could not be discharged** (D36): the receive's no-sender path (`endpointReceiveDual_preserves_projection`: `cleanupPreReceiveDonation`, then `popHeldReplyHead`, then return or keep) hands a hidden receiver's loaned context back to its owner, and no gate relates the receiver's label to the context's. It takes the per-step premise `bindingLabelsEqual` (D37: every binding pair has equal labels), from which the shape the receive theorems consume, `receiveLoanReturnHidden` (the returned context or its owner is hidden), is derived, on the `endpointReceiveDualHigh` and `endpointReplyRecvHigh` steps; the two-run theorem takes the same predicate of both runs; SX16 removes it (D38, D40). **Landed:** `maybeDonateSchedContextFlowing_lowEquivalent_pair` (`InformationFlow/NotificationLendTwoRun.lean`) takes `bindingLabelsEqual` of both runs, timer agreement, `runQueueRefined` of both runs (the invariant the run-core reads come off, ruling (ay).3) and the static labelling fact `threadObjectLabelsEqual` (each thread carries its TCB's label: `LabelingContextValid` gives only a flow, and the admission reads the waiter's binding words off its TCB); its corollary `maybeDonateSchedContextFlowing_lowEquivalent_pair_deployment` discharges the labelling fact for every deployment context. | The theorem; pair lemmas (two runs, one write) for `rewriteObject`, `updateTcb`, `runEnqueueOnCore`, `releasePlace` and `markReschedulePending`, none in the tree. | Tier 3 anchors on the theorem and its five pair lemmas |
| SX9.2 | **LANDED at `v0.37.38`.** **The remaining D21 behaviour rows** in `sel4BehaviourRows` (`Testing/Sel4ConformanceTable.lean:512`), each with its scenario in `runBehaviourRows` (`tests/Sel4ConformanceSuite.lean:301`): reply_pop's held arm; SchedContext_Unbind of a donated holder with `unbindReply` (D22); suspend keeps the victim's binding; a blocking receive returns the context; SchedContext_Bind of a lender. | none (rows and scenarios) | `sel4_conformance_suite` |
| SX9.3 | **LANDED at `v0.37.38`.** **Heap scenarios on the two labelled bands** of `Exerciser.deploymentLabeling` (`Platform/Exerciser/Deployment.lean:162`). **As measured** (owner's ruling, 2026-11-24): the row first named a Call whose lend the label check refuses (D28), a notification lend refused low to high and high to low (D30), and SchedContext_Bind of a context heading a stack (D25). Under D33, D35 and D37 the two refusals cannot be reached from a booted image: every way a thread comes to hold a context (Bind, `schedContextBindLabelAdmits`; the notification lend, D30; the Call and receive lends between equal-label endpoints, D33) gives the holder the context's label, so `callLendAdmits` never refuses; a waiter carries its notification's label (the two-way wait gate) and a notification its context's (`schedContextBindNotificationLabelAdmits`), so the lend's label check never refuses. Only a boot image binding unequal labels reaches them, which SX10.1's boot check refuses. So SX9.3 measures the gates that make them unreachable, on the upper band beside `bind-upper-notification-refused`: `sched-context-bind-upper-notification-refused` (the image's context bound to the notification carved at an upper id) and `sched-context-bind-upper-thread-refused` (bound to a thread carved at an upper id), each refused `flowDenied` before any write. D25's thread half (a lender whose frame is on a live stack) is the existing `held-pop-bind-lender`; its context half is unreachable: a bind needs the context bound to no thread, a context heading a stack is held by the stack's server, and an unbind lets go of the stack (`schedContext_unbindReply`), so no state holds an unbound context that heads a stack. The refusal branches stay until SX16 deletes them (SX16.2, D38, D40). | none | `scripts/qemu_exerciser_lib.sh` expected set; QEMU: each reads 0 |

**Acceptance:**
- one two-run theorem and five pair lemmas, with the owner's ruling on the
  cleared observer recorded here;
- five new behaviour rows, each with a passing scenario;
- two new heap steps (the substitution SX9.3 records), each reading 0 on both lanes, twice;
- the one premise (`bindingLabelsEqual`, D37) registered, owned by SX16 (D38, D40): on
  the two receive steps and on the two-run theorem.

### SX10 — The equal-binding-labels invariant, begun (D36, D37, D38)

**LANDED at `v0.37.39`, wrapped at its validated point (D38).** SX9's
remainder on the lend's evidence. It lands the boot base case, the owner
clause and the slot toolkit; the invariant's preservation, the premise's
removal and the refusal deletions move to SX13–SX16 (D40), on SX11's waiter-label
invariant.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX10.1 | **LANDED.** **The boot base case.** As found: the checked boot already refuses every configured binding pair, of equal labels or not (`bootSafeTcbCheck`: a boot thread is unbound; `bootSafeSchedContextCheck`: a boot context binds no thread; `bootSafeNotificationCheck`: a boot notification binds no context), and no boot stage creates one (the idle threads, the starts, the interrupt nodes, the root server and the capability links). The Low finding reported during SX9 (that a boot image binding unequal labels boots) is withdrawn, and no label check is added: its refusal could never run. The base case is the proof: `bootFromPlatformCheckedStartedFor_bindingLabelsEqual` (`Platform/Boot/InitialThreads.lean`), under every labelling, read off the linked boot shape. `bindingLabelsEqual` moves to its own kernel module (`SchedContext/Invariant/BindingLabels.lean`) below the projection. | The boot base case: a booted state satisfies the invariant. | `syscall_dispatch_suite`: the checked boot refuses a thread bound, a thread lent, a context bound and a notification bound across unequal labels, and the unbound control boots with no binding word; Tier 3 anchors |
| SX10.2 | **LANDED.** **The owner clause and the binding words, slot by slot.** `bindingLabelsEqual` gains its fourth clause, D37's first consequence: a lent binding's owner word (`TCB.scBindingOwnerCode`) names a thread with the context's label, because the return to the owner binds the owner. Its views read the four words through the typed readers (`threadContextView`, `threadOwnerView`, `contextThreadView`, `notificationContextView`), and a step after which every binding word was already there carries it (`bindingViewsShrink`, `bindingLabelsEqual_of_shrink`). The slot toolkit states the four words of one object slot (`objBindingWords`), each view as a read of its slot, and a slot's binding shrink (`objBindingShrink`, with its free, unchanged, thread, notification and context forms), lifted to the views (`bindingViewsShrink_of_objects`, `bindingViewsShrink_of_slot`): the leaf lemmas SX14's frame family consumes. | The views' agreement with the predicate; the shrink lemmas. | Tier 3 anchors on the clause and the toolkit |

**Acceptance:**
- the boot base case proves the invariant of every booted image;
- the owner clause and the slot toolkit build, with their anchors;
- the premise `bindingLabelsEqual` stays on the two receive steps and the
  two-run theorem, its debt row now owned by SX16.

### SX11 — Blocked threads carry their endpoint's label (D38)

**LANDED at `v0.37.40`.** `endpointWaitersLabelsEqual` holds of every booted
state and is carried by every committing entry (`EndpointWaitersStage`,
`SeLe4n/Kernel/EndpointWaiters/`). The per-dispatch blocked-sender lifts and
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
the premise's move and the refusal deletions move to SX14–SX16. No transition
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
  two-run theorem, its debt row now owned by SX16.

### SX14 — The frame family threaded, the pops as labelled steps (D40)

**SX14.1 LANDED at `v0.37.43`; the row wrapped at that validated point
(D32), SX14.2 and SX14.3 open pending the owner's split.** SX13's remainder,
first half. The frame family carries both halves of the lending invariant, and
every step that does not create a binding is shown to keep it. The landed
sub-task changes one transition: the cancel's pop reads the frame's recorded
caller (D41).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX14.1 | **LANDED.** **The cancel pops to the frame's recorded caller** (D41, "Match seL4": seL4's `reply_pop` donates to `reply->replyTCB`). `cancelledCallerDonation?` reads the victim's frame only where it records the victim as its caller (`replyRecordsCaller`, a word compare of the stored reply's caller code, allocation-free), and the compiled head cancel's gate (`headReplyCancelInPlace`) reads the same word, so the `@[csimp]` form agrees. The guard agrees with the unguarded read wherever the reply linkage holds (`cancelledCallerDonation?_eq_unguarded_of_linkage`, from `replyRecordsCaller_of_linkage`); its consumers that read the head case take the linkage from `ipcInvariantFull` or the reply's recorded caller from the finalisation (`replyCallerFinalisable_cases`). `cancelledCallerDonation?_independent_of_victim` is retired. So the cancel's pop recipient is the frame's recorded caller, whose label `contextLendersLabelsEqual` equates with the context's (SX14.3 discharges the owner obligation from it). | The agreement lemma; the guard's `some`/`none` cases; the in-place equality. | Tier 3 anchors on the guard, its agreement and the in-place gate; the cancellation suite's foreign-caller witness |
| SX14.2 | **The frame family threaded** per ruling (ag): SX8's `contextLendersFlow` is strengthened in place to label equality and renamed `contextLendersLabelsEqual` (D37's second consequence); the carried stage is its conjunction with `bindingLabelsEqual` (`lendingLabelsEqual`). `contextStackViewsAgree` and `contextStackLinksShrink` gain the binding words, `chainObjectsKept` keeps them on thread and notification slots, and the leaf lemmas take a slot's binding shrink (SX13's toolkit). The sibling lemmas for the summaries that forget the binding words, measured at 12 sites in about 8 files: the capability transfer's object cases, the priority-inheritance walk (landed in SX13.2), the splice and notification-queue cleanups, the slot links' reach, the VSpace-root-only write, the final retire, the off-taint agreement, the timeout abort and the frame insert. The finalisation steps (about 11) carry a separate binding shrink beside `finaliseWrite`, not a new conjunct of it (129 `rcases` sites). Every creating site takes its label equation as a hypothesis of its step, surfaced in the entry's premise pack, which SX15 discharges; no step is stubbed. | The frames and shrinks over the lender cut: of the 37 measured declarations, the 25 that create no binding (Call 2, Timer 4, Cancel 4, Reply 3, Capability 2, `CapabilityOnly` 8, `SyscallDispatch` 1, Receive 1) and the census witness. | Tier 3 anchors on the strengthened predicate and the threaded frame |
| SX14.3 | **The pops as labelled steps.** A labelled step (`LendersStep ctx st st'`: the stage carried from `st` to `st'`, and the store's invariant at `st'`), with its identity, composition, the frame read as a step and the stage. The 30 `LendersFrame` theorems that chain a pop are restated as labelled steps, each pop discharging its owner obligation inside the step at its own pre-state (FINDING 1: proof obligations, not premises): the cancel's return to the frame's recorded caller (D41: the cancel's guard makes the recipient the frame's caller, so `contextLendersLabelsEqual` names it), the reply's return from the answered caller (since SX12, the frame heading the context, through `contextLendersLabelsEqual` at the pre-reply state), the next owner from `replyStackOuterCaller?` through `contextLendersLabelsEqual`; the keep and the clears are shrinks. | Preservation by every pop, in place and cross-core. | Tier 3 anchors on the labelled step and the pops |

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
kept as a patch beside the row's notes; it cannot land alone, because every
lender module after Cancel consumes the frame family it changes.

**Acceptance:**
- every lender module builds over the threaded frame family, with no stub;
- every pop is a labelled step whose owner obligation is discharged inside it;
- the creating sites' label equations are the only hypotheses the stage adds.

### SX15 — The creating sites, and preservation over every writer (D40)

SX13's remainder, second half: the label equation of every step that writes a
binding word to a new value, discharged, so the stage holds of every committing
entry with no added hypothesis.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX15.1 | **The creating sites.** Bind (D35) and the notification lend (D30) check equal labels directly. The Call lend and the receive-take lend get the receiver's label equal to the lender's from SX11 and the step's gate: the Call's `applyCallDonation` takes the receiver's equation from SX11's `endpointWaitersLabelsEqual` at the pre-state (the receiver blocked receiving on the endpoint) with the caller's gate (`endpointFlowGate_implies_eq`), and the server's from the caller's own binding (`bindingLabelsEqual.bound`); the receive take, from the receive gate and the dequeued caller blocked calling. `LendersDispatchPremises` gains `endpointWaitersLabelsEqual` and the queue heads' consistency at each syscall's pre-state; fault delivery takes its gate from its checked branch with the waiters at its state. Measured: 12 of the 37 declarations, at the binding writes (Call 1, Receive 3, Interrupt 3, `CapabilityOnly` 5: the notification bind and unbind, the context's thread word on Bind and Unbind, the reply unbind), and the 41 of the 78 writer files that write no stack view (SchedContext Bind, Unbind and BindingAffinity; notification bind, link, donation and signal; the lifecycle cleanup and finalise; `ReschedulePendingArms`; the in-place fast forms; `FrozenOps`). | Preservation over every writer: every committing entry carries the stage under SX11's and the records' stages alone. | Tier 3 anchors on the creating sites and the premise pack |

**Acceptance:**
- every writer of a binding view preserves the invariant;
- the stage holds of every committing entry with no hypothesis SX14 added.

### SX16 — The premise moved and the refusals deleted (D40)

SX13's remainder, last: what the completed invariant makes possible.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX16.1 | **The premise moved**, per ruling (a) under D29: `bindingLabelsEqual` leaves `endpointReceiveDualHigh` and `endpointReplyRecvHigh` and moves to the standing per-state slot beside the object-store invariant (`step_preserves_projection`, `NonInterferenceTrace.cons`); the notification lend's two-run theorem keeps it as a standing hypothesis of both runs. Its `docs/REGISTERED_DEBT.md` row narrows to a table C line owned by WS-PK (carrying it across a trace) and does not close. | `endpointReceiveDual_preserves_projection` and `endpointReplyRecv_preserves_projection` without the per-step premise. | Tier 3 anchor refusing the per-step premise |
| SX16.2 | **The unreachable refusal branches deleted** as retired code, once SX15 proves every committing entry keeps the invariant and SX10.1's base case makes it hold of every booted image (the owner's choice for the declassified signal's second hop, gate PR #1096): `callLendAdmits`' refusal (D28) and the notification lend's label check (`donationContextFlows`, D30), with their compiled forms, NI case splits and the refusal rows and heap scenarios that measure them. | Each consumer restated over the unchecked lend; the two-run theorem over `maybeDonateSchedContext`. | Tier 3 negative anchors on the deleted definitions; the census and anchor sweep over every file the cut touches; the heap gate's expected set |

**Acceptance:**
- the premise is off both receive steps, standing beside the object-store
  invariant, and its debt row narrowed;
- the lend refusals the invariant makes unreachable are deleted.

### SX17 — One composed in-place ReplyRecv path (ruling r)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX17.1 | **One composed in-place ReplyRecv**: the reply leg, the pop on either arm (donated, held, unheld, unlinked), the capability transfer and the receive leg (block or take), written once in place and joined to `replyRecvOnCore` by one proof. It covers the long, faulted and capability-carrying shapes still on the spec path, among them the held arm's (four words, no fault and no transfer today) and those of a reply object linked to nothing that `main` also leaves on the spec path. | One `_eq` to the specification, replacing the per-shape equalities; the arm proofs in `RefusalCarryingReplyRecv.lean` restated over it. | QEMU: every existing ReplyRecv reading stays 0; one new step per shape it brings in place, each 0 |
| SX17.2 | **The per-shape modules it retires are deleted**: the twelve ReplyRecv modules under `IPC/CrossCore/` (`EndpointReplyRecv{,Donated,Unheld}InPlace`, `LongReplyRecv{,Pop,Take}InPlace`, `ReplyRecv{,Call,DonatedCall,Fault,Unlinked,UnlinkedCall}TakeInPlace`; 8,680 lines at `v0.37.36`) and the ReplyRecv half of `EndpointReplyHeldInPlace`, with their Tier 3 anchors and census rows. | none beyond SX17.1 | Tier 3 anchors refusing the retired names |

Baseline at `v0.37.36`: `RefusalCarryingReplyRecv.c` is 22.5 MB and compiles
in 915 s at `-O3`.

**Acceptance:**
- every ReplyRecv shape answered in place, under one proof;
- the twelve modules deleted;
- `RefusalCarryingReplyRecv.c` and its compile time no larger than the
  baseline;
- every heap reading 0.

### SX18 — Page-table teardown and per-frame W^X

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX18.1 | PageTable_Unmap as seL4's `performPageTableInvocationUnmap`: the table is unmapped from its address space and cleared even while mappings pass through it, where the model refuses `revocationRequired`; every frame capability whose recorded mapping passed through the table has its mapping record cleared (seL4 leaves `capFMappedASID` stale; the model's record drives teardown, so it is cleared). | The mapping-record stage, `pageTableInstallLive` and the teardown theorems over the cleared table and records; the lock footprint names each cleared capability's CNode. | SX8.1's row; QEMU: unmap of a populated table, at 0 |
| SX18.2 | Per-frame W^X as an invariant: no frame is mapped writable and executable at once, in one address space or across two, held in the proof-layer bundle rather than by the map's check alone. | Preservation over Page_Map, Page_Unmap, PageTable_Unmap and every teardown. | Tier 3 anchors |

### SX19 — Per-invocation rights as `Option AccessRight`

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX19.1 | Each invocation's required right becomes `Option AccessRight`, `none` where seL4 checks no right: SchedContext_Bind's `.write` and Page_Unmap's `.read` go; Untyped_Retype's rights and Page_Map's `maskVMRights` follow seL4 (consumes SX8.1's rows). The flow gates stay, before anything observable, with their non-interference proofs. | The gate theorems and the dispatch non-interference cases over the optional right. | SX8.1's rows; QEMU: each changed invocation through a capability without the old right, at 0 |

### SX20 — seL4's Running thread state per core

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX20.1 | The thread state seL4 calls Running, held per core, including self-suspend by Call: seL4's `suspend` leaves the caller `Inactive`, so `handleInvocation` writes no reply and the restart PC stays at the `SVC`. The no-reply half landed with SX7 at `v0.37.33` (`syscallReturnOutcome` answers only a runnable caller); this row makes a thread stopped inside its own syscall (a self-suspend, a Call that links no reply) resume at its `SVC`, where it now resumes past it with its request registers. Gap closed here (D24, "Match in SX11", this row before D32 renumbered it): until this row, a thread whose context SX8.2 returned (`.unbound`) is still scheduled at its legacy priority, where seL4 never runs a thread with no scheduling context; this row makes a thread with no scheduling context unschedulable, as in seL4-MCS. The scheduler's run rule is not changed in SX8. The row also owns the boot's half: seL4-MCS's boot gives the root thread its initial scheduling context, bound (`create_initial_thread` binding the root server's context), so the root thread can run; the checked boot today binds no thread (`bootSafeTcbCheck`, SX10.1), so once a thread with no context is unschedulable the boot must create the initial threads' contexts and bind them. Each such binding is a binding pair, so it is created at equal labels (the thread's and its context's, D37), and the boot base case `bootFromPlatformCheckedStartedFor_bindingLabelsEqual` is restated over it. | The thread-state invariants and the scheduler's per-core current-thread theorems over the new state. | `smp_4core_scheduler.expected`; QEMU: `tcb-suspend-self-by-call` |

### SX21 — The invoke phase of NBSendRecv, NBSendWait and ReplyRecv

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX21.1 | seL4 runs `handleInvocation(isCall = false, isBlocking = false, canDonate = true, firstPhase = true, dest)` and then `handleRecv`: `dest` is x8 for NBSendRecv and x6 for NBSendWait and ReplyRecv. A lookup fault is dropped and an error discarded, and the receive still runs; only preemption skips it. The invoke phase is a full `decodeInvocation` on `dest`'s capability (consumes SX8.1's rows and SX20.1's state). In `API.syscallEntryChecked`, before the receive decode, when x7 is one of the three words: select the operation on `dest`'s capability type and the label, decode with `capAddr := CPtr.ofWord dest`, dispatch, keep the handed state on an error and continue on the new state on success, then the receive on it. The frame is already in the TCB (`saveCapturedSyscallFrame`), and `captureEntryWords` captures the invoke phase's overflow words and extra capabilities for `dest`. | Every family over `syscallEntryChecked` takes the two-phase case: the compiled entry (`RefusalCarryingEntry`, `syscallEntryRoutedK`, which runs the routed dispatch twice), the seam and its refusal record (receive phase only), `FineLockFlow`, `SyscallLockBracket` (both phases' sets), the per-entry stage lemmas and `FaultEntry`. | `smp_ipc_4core.expected`; QEMU: each of the three with a send-phase fault, an error and a success, at 0 |

### SX22 — Timeout faults and the MCS TCB calls

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX22.1 | A TCB timeout-handler slot, and `SetTimeoutEndpoint` (extra capability 0). | The slot invariants. | `sele4n-abi` `args/tcb.rs` |
| SX22.2 | `SetSchedParams`: the authority, scheduling context and fault endpoint as extra capabilities; MCP and priority as words. | The MCP authority and binding theorems. | the same |
| SX22.3 | A running thread's budget overrun with a valid timeout handler raises `seL4_Fault_Timeout` (MCS tag 5, with the context's badge and consumed time). A blocked IPC is no longer timed out: `timeoutThread` and `ipcTimeout` retire, and the discriminant is reserved. | The budget and CBS theorems; the donation-chain (WS-OD, WS-HP) theorems that cited `timeoutThread`; `faultLabel_ne_timeout` retires into the timeout fault's label theorem. | `fault_handling_4core.expected`; `smp_4core_scheduler.expected` |

**Acceptance:** `timeout-fault-delivered`, `blocked-call-not-timed-out`,
`set-sched-params`.

### SX23 — seL4's CNode invocation set (D16, D17)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX23.1 | Delete and Revoke address their target by index and depth (`lookupTargetSlot`). | The two arms' decode and preservation. | `args/cspace.rs` |
| SX23.2 | Mutate: a Move with `updateCapData` preserving. A null result is IllegalOperation. | `cspaceMove`'s CDT, link and occupancy theorems over a rewritten capability. | the same |
| SX23.3 | Rotate, per `cnode.c:231`. | The CDT, `cdtLinksAgree` and `CapTreeShape` preservation for two moves; the footprint (3 slots, 2 roots). | the same |
| SX23.4 | CancelBadgedSends: all four endpoint rights; the senders with the badge are removed and set to Restart; badge 0 does nothing (`endpoint.c:489`). | Endpoint queue well-formedness; run-queue insertion; non-interference for the arm. | `smp_ipc_4core.expected` |

**Acceptance:**
- `cnode-delete-index-depth` and `cnode-revoke-index-depth`.
- `cnode-mutate-guard` and `cnode-mutate-badged-refused`.
- `cnode-rotate` and `cnode-rotate-pivot-is-source-refused`.
- `cnode-cancel-badged-sends`: only the matching senders restart.

### SX24 — seL4's error codes in the label (D1)

This row needs F1 to hold. SX3, SX4, SX7 and SX22 made it hold.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX24.1 | `KernelError.sel4Error`, total (D1). The error frame's label is the seL4 code. `errorLabelBase` retires. | `receivePhase_noErrorFrame`: no receive-phase syscall returns an error frame. `sendInvocation_noErrorFrame`. The label round trip over seL4 codes with the payload. The `faultLabel_lt_errorLabelBase` family retires into these. | `abi_layout.expected` (`errorLabelBase` out); `syscall_return_abi.expected`; the `sele4n-types` error table; `test_rust_conformance.sh` |

**Acceptance:** every error scenario re-pinned to seL4's codes; a fault
handler's receive reads fault tags only.

### SX25 — seL4's remaining invocations (D23)

SX8.1's conformance table marks every seL4 invocation label seLe4n does not
implement as absent; the ones no earlier row owns are this row's. Each is
implemented as seL4-MCS's decode and perform (aarch64, the default build) with
its specification, a proven-equal fast form, the flow gate before anything
observable, its NI and invariant obligations, an exact SMP lock set and zero
allocation per entry. `ARM_SMC_Call` stays absent, as in seL4's default build
(`CONFIG_ALLOW_SMC_CALLS` off).

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX25.1 | **The invocations no earlier row owns** (labels 2–5, 16, 17, 30–32, 39–41, 48–56 of SX8.1's table, and label 1's argument list). TCB: `ReadRegisters`, `WriteRegisters`, `CopyRegisters` (`tcb.c`, the suspend and resume flags and the arch register order), `Configure`, `SetTLSBase` and `SetFlags` (`UnbindNotification` is implemented already). Domain: `DomainSet_Set` and the domain schedule invocations `DomainSchedule_Configure` and `DomainSchedule_SetStart`. VSpace and page: `ARM_VSpace_Clean_Data`, `Invalidate_Data` and `CleanInvalidate_Data` (`Unify_Instruction` is implemented already), and the page's `Clean_Data`, `Invalidate_Data`, `CleanInvalidate_Data`, `Unify_Instruction` and `GetAddress`. ASID: `ARM_ASIDControl_MakePool` and `ARM_ASIDPool_Assign`. IRQ: `ARM_IRQ_IssueIRQHandlerTrigger` and, in the SMP build, `ARM_IRQ_IssueIRQHandlerTriggerCore`. `Untyped_Retype` drops the extra `childId` word to seL4's six-word argument list, the child placed at the untyped's free index as seL4 places it. Every absent conformance-table row this row owns becomes implemented, its decode, arity, return shape and errors checked by the suite. | Each invocation's preservation obligations (`ipcInvariantFull`, the scheduler bundle, the records and mapping stages, saved registers, slot confinement, cross-core NI) and its fast form's `_eq`; the retype's decode round trip without `childId`. | the conformance suite (every row implemented but `ARM_SMC_Call`); QEMU: each invocation's success and first refusal at 0; `abi_layout.expected` for the retype's arguments |

**Acceptance:** the conformance table has no absent row but `ARM_SMC_Call`;
every new path measured at 0.

### SX26 — Closure

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX26.1 | WS-CV's CV1.2, folded into WS-SX (maintainer's decision; WS-CV closes alongside WS-SX at `v0.38.0`): the information-flow surface (`ObservableState.machineRegs`, the per-core fragments, `lowEquivalentSliceOnCoreCheckWithRegs`) moves to lawful equality, and `RegisterFile.beq_iff_eq'` / `beq_self` / `beq_symm` / `beq_trans` (`SeLe4n/Machine.lean:528-539`) retire with their last consumer. At `origin/main` that is 51 citing sites in 13 files; the build enumerates them when the lemmas are deleted. The spec's information-flow equality passages and the evidence-index rows of the re-proved unwinding relations change in the same row. **Zero allocation**: proofs and the test-side `…CheckWithRegs` comparison only, no compiled entry. | The `machineRegs` unwinding relations re-proved on lawful equality; every `beq_*` citing site rewritten to `beq_iff_eq` / decidable equality before the lemmas are deleted. | Tier 3 anchor `machineRegs_beq_self` retires |
| SX26.2 | `docs/CLAIM_EVIDENCE_INDEX.md` gets a row per seL4 behaviour this plan follows. The spec's syscall-boundary section is rewritten to the seL4 ABI. The workstream is closed in `docs/REGISTERED_DEBT.md` and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, and this plan moves to `docs/dev_history/planning/`. **Full documentation sweep against the final tree:** the spec, every GitBook chapter on the syscall ABI and CSpace, README metrics, `docs/DEVELOPMENT.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, the `docs/REGISTERED_DEBT.md` index row, and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, whose WS-SX section moves to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`. **Refresh every not-yet-started plan** against WS-SX's final tree: the remaining WS-UC rows UC6–UC10, `CONTEXT_BY_VALUE_PLAN.md`, `HIERARCHICAL_CBS_PLAN.md`, `LOCK_STATE_SEPARATION_PLAN.md`, and every other plan under `docs/planning/` — file:line citations, names, rows the new ABI makes obsolete or newly needs, and the decisions it affects. If the refresh is too large for SX26, it is the very next PR, landed before any next-row code. **WS-CV's closure (its CV5.2), in the same row** (consumes SX26.1): the `v0.36.47` register-file debt row is deleted from `docs/REGISTERED_DEBT.md`; the WS-CV section of `docs/agent_guide/WORKSTREAM_CONTEXT.md` moves to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`; `CONTEXT_BY_VALUE_PLAN.md` moves to `docs/dev_history/planning/`, every live link to it (a search for `CONTEXT_BY_VALUE_PLAN` outside `docs/dev_history/`) repointed to cite it by workstream ID; and `HIERARCHICAL_CBS_PLAN.md` is re-checked against it, which the plan refresh above covers. | none | `check_claim_evidence_citations.py` |

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
| SX14 | 3–4 |
| SX15 | 2–3 |
| SX16 | 2 |
| SX17 | 3 |
| SX18 | 2 |
| SX19 | 1 |
| SX20 | 1–2 |
| SX21 | 2 |
| SX22 | 2–3 |
| SX23 | 2 |
| SX24 | 1 |
| SX25 | 4–5 |
| SX26 | 2 |

About 63–71 sessions in all. The largest risks:
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
