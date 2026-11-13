# WS-SX — seL4 ABI fidelity

> **Workstream**: WS-SX (the syscall and invocation ABI made seL4's).
> **Status**: **ACTIVE** — registered at `v0.37.19` (this plan, docs only);
> SX1 landed at `v0.37.20`.
> **Baseline**: the tree at `v0.37.18` (WS-UC UC5). Every `file:line` below was
> read against it.
> **Rows**: SX1–SX11, numbered in the order they are implemented, one PR each.
> Each row consumes only lower-numbered rows. A row that changes a transition
> carries the proofs that cover it. No two rows run in parallel.
> **Decisions**: D1–D17 (§3), each **default taken; owner card open**. D7 follows
> the owner's standing rule (implement seL4's behaviour, never defer it).
> **Supersedes**: the "Next PR" scope in
> `docs/agent_guide/WORKSTREAM_CONTEXT.md` (the root task's boot IPC buffer
> and the guard in the capability with `CNode_Mutate`). Both are rows here
> (SX5, SX2 and SX9). Neither was debt, and neither is now.

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
  - Once SX3, SX4, SX6 and SX8 make F1 true here, a receive never yields an error
    frame. seL4's codes 1–10 can then sit in the label with no receive-side collision.
  - One overlap remains, and it is seL4's own: a Call on an endpoint can answer
    `seL4_InvalidCapability` (a capability without the send right,
    `decodeInvocation`, `objecttype.c`) or the server's reply, whose label the
    server chooses.
  - SX10 makes the switch and proves the receive half as a theorem.
- **F3. Extra capabilities need an IPC buffer.** `lookupExtraCaps` with no
  buffer finds none (`tcb.c:392`). So the exerciser's boot-time invocations
  must be gone (SX5) before invocations take extra capabilities (SX7).
- **F4. The heap gate holds every non-carve kernel entry at 0 cells**
  (WS-UC, `scripts/qemu_exerciser_lib.sh`).
  - A nullary `KernelError` is a boxed scalar.
  - A constructor with fields allocates.
  - So a refusal that carries data allocates unless its compiled arm passes the
    data unboxed (D2b).

## 3. Owner decisions

Each is **default taken; owner card open**. A different answer changes only
the rows that cite it.

- **D1. The error label.** *Default:* **seL4's error codes (1–10) in the
  label** (SX10), and the payload in seL4's MR layout (SX1).
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

The label is unchanged until SX10.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX1.1 | `LookupFault` (`invalidRoot`, `missingCapability bitsLeft`, `depthMismatch bitsLeft bitsFound`, `guardMismatch bitsLeft guardFound bitsFound`, seL4's `lookup_fault`). The D2 payload fields; `depthMismatch` retires into `failedLookup`. Every site sets its number: `invalidCapability` is `0` for the invoked capability and `i + 1` for argument capability `i`, and every argument capability (a receive's or reply-receive's reply capability included) is resolved through one boundary that applies it (`syscallLookupArgumentCap`, and `KernelError.argumentCapRefusal` in the compiled forms). The CNode-op refusals take seL4's: an empty source is `failedLookup true (missingCapability srcDepth)` (`cnode.c:111`). | The discriminant round trip over codes (`toDiscriminant`, `ofDiscriminant?`), the payload ignored; every `cases e <;> decide` restated per code. | `main_trace_smoke.expected` (error `Repr`); Tier 3 `KernelError` anchors; the `rust/sele4n-types/src/error.rs` mirror; `test_rust_conformance.sh` |
| SX1.2 | `errorFrame` carries the payload in seL4's MR order (x2–x5), with MR4 written to the caller's buffer `msg[4]` (D3) and the length as `setMR` returns it. Compiled refusal arms pass the payload unboxed (D2b). `syscallAbiVersion` 4 → 5. | `errorFrame_payload_roundtrip`. The error path's frame theorem restated: it changes only the caller's `msg[4]`, on a 5-word payload with a buffer. `errorFrame_x1_decodes` gains the length. | `syscall_return_abi.expected`; `abi_layout.expected` (version, payload offsets); `rust/sele4n-abi` frame decode |

**Acceptance (QEMU):**
- `range-error-payload`: Copy with depth 65 returns MR0 = 1, MR1 = 64.
- `failed-lookup-depth-mismatch`.
- `failed-lookup-missing-source`.
- Each reads 0 heap cells.

### SX2 — The guard in the capability, and `resolveAddressBits` (D4, D5, D17)

**LANDED at `v0.37.22`.** The compiled resolver recurses only for the
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
| SX3.1 | Recv and Wait answer `CapFault(cptr, inRecv)` with `missingCapability 0` for each of: a capability of the wrong kind, a missing receive right, or a notification bound to another thread (`syscall.c:470`–`:513`). | `capFaultReceivePhase?` partition restated. Every receive arm returns no error frame but the two that SX4 and SX8 retire. | `fault_handling_4core.expected`; `main_trace_smoke.expected` |
| SX3.2 | A failed reply-capability lookup on a receive faults, as `lookupReply` does (`syscall.c:387`). This closes the note at `SeLe4n/Platform/FFI.lean:3073`. | `syscallCapFaultOf` covers the reply lookup. | the same |

**Acceptance:** `recv-wrong-kind-faults`, `recv-no-read-right-faults`,
`reply-recv-bad-reply-faults`.

### SX4 — The Restart thread state

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX4.1 | `ThreadState.Restart`: activation rewinds the PC to the `svc` (`svcFaultIP`) and re-runs the syscall. A cancelled IPC (endpoint or notification deleted, object retyped, `cancelAllIPC`) sets Restart. `ipcCancelled` retires and its discriminant is reserved. | The scheduler bundle with Restart runnable; `ipcInvariantFull`; the restart-PC frame. The cancellation staging theorems replaced. | `smp_ipc_4core.expected`; `main_trace_smoke.expected`; Tier 3 `ipcCancelled` anchors |
| SX4.2 | Suspend leaves a blocked victim Inactive, and Resume sets Restart (seL4's `restart`). | The suspend/resume preservation family. | the same |

**Acceptance:** `cancelled-send-restarts` (a deleted endpoint under a blocked
sender; the restarted send faults), `suspend-resume-restarts`.

### SX5 — The boot builds the root task's IPC buffer (D13, D14, D15)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX5.1 | `PlatformConfig` gains a root-server reservation. A new `wellFormed` conjunct `rootServerPlaced` requires it to be in one `.ram` region, clear of every untyped, `kernelReserved` (the image and the table pool), `kernelDevices` and every region-map reservation, with distinct pages. `untypedExtentOf` subtracts it. `region::thread_ram_covered` admits it. | The `virt`, exerciser and RPi5 layout theorems (`qemuVirtRegionMap_layout` extended); `rootServerPlaced` decided per config. | `boot_map.expected`, `boot_map_qemu_virt.expected`; `test_aarch64_cross_build.sh` |
| SX5.2 | A TCB buffer slot (seL4's `tcbBuffer`), empty on every thread. | Every slot invariant over the third slot (`capTargetKindBacked`, the derivation links, `bootDerivationTreeSound`). | Tier 3 slot anchors |
| SX5.3 | The boot builds the frame, three page tables, the root's `tables`, `mappings` and `mappingEpochs`, the mapped frame capability in a root CNode slot and in the buffer slot, and `ipcBuffer`. `bootObjectShape` gains the frame, table and mapped-root arms. The boot entry performs and drains the owed writes (D15). | `proofLayerInvariantBundle_of_bootShape` reproved: the vspace bundle, one recorded live mapping, lifecycle and bookkeeping, the capability bundle, untyped disjointness with the reservation, TLB and icache quiescence. `bootFromPlatformCheckedStartedFor_proofLayerInvariantBundle`. | Tier 3 Boot.lean :3960, :3963 and the `bootSafeObjectCheck` anchors; `qemu_lean_boot_expected.txt` |
| SX5.4 | Delete `qemuVirtExerciserRootInvoke`, `…RootIpcBufferInvocations`, `…GiveRootIpcBuffer(OrHalt)` and the IPC-buffer untyped. | none (deletion) | the boot heap census pins |

**Acceptance:**
- `root-ipc-buffer-at-boot`: the first syscall's overflow word is read from the
  boot-built buffer.
- `root-ipc-buffer-cap`: an Unmap and remap round trip.
- The census re-pinned on both platforms' boot.

### SX6 — seL4's syscall set and invocation labels

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX6.1 | **Labels:** Call or Send on a kernel-object capability selects its operation by the message label, numbered as seL4's generated `invocation_label` for aarch64 MCS. Model-only calls (service, audit, declassify, `mintReplyCap`) take labels after seL4's last. **Error delivery:** only Call receives an error; Send discards it (`syscall.c:371`). **Retired:** the per-operation syscall numbers. | The decode round trips; seam coverage per (capability type, label); the lock footprints per label; the dispatch non-interference cases; `#assert_decoder_arities`. | `abi_layout.expected` (the label table); `rust/sele4n-abi` `SyscallNumber` and labels, and the `sele4n-sys` wrappers; `check_live_arm_per_core_routing.py`; `main_trace_smoke.expected` |
| SX6.2 | The IPC syscalls become seL4-MCS's 11 (Call −1 … Yield −11, `syscall.xml`, order kept). Signal is Send on a notification; a reply is Send on a reply capability. `.reply`, `.notificationSignal` and `.notificationWait` retire, and NBSend, NBRecv, NBWait, NBSendRecv and NBSendWait are added. A failed NBSend lookup is silent; NBRecv does not block. SX6 also settles the invoked capability's two failures as seL4's `handleInvocation` (`syscall.c`) does: a failed lookup of the invoked capability (`lookupCapAndSlot`) is a capability fault on the blocking Send and Call and is dropped on NBSend, and an empty slot, which the lookup answers with a null capability, is `decodeInvocation`'s `seL4_InvalidCapability` error, delivered only to Call (`syscall.c`, `if (isCall) replyFromKernel_error`). | `registerRoutedSyscall` and `syscallReadsOverflow` restated; the `capFaultReceivePhase?` partition; the IPC bundle for each NB arm. | the same; `syscall_return_abi.expected`; `smp_ipc_4core.expected` |
| SX6.3 | Recv, ReplyRecv and NBSendRecv read the reply capability from x6 (`replyRegister`). | The routed-decode theorems for the receive arms. | `abi_layout.expected` (`register reply x6`) |

**Acceptance:**
- The whole exerciser suite re-encoded, at its current heap pins.
- `nb-send-bad-cap-silent`.
- `nb-recv-empty-returns`.
- `send-invocation-error-discarded`.

### SX7 — Capability arguments as extra capabilities (D6–D12)

`lookupExtraCaps` runs at decode (`tcb.c:386`).
- A failed lookup is `CapFault(that cptr, send phase)`.
- A missing extra capability is TruncatedMessage.
- A capability of the wrong kind is `invalidCapability (i + 1)`.
- IPC transfers still look their capabilities up at the rendezvous (`thread.c:213`).

Every sub-task re-derives `maxLockSetSize` for the lookup paths it adds.
SX7 routes and measures the 22 invocation arms that still fall back to `dispatchInvocationBy` on refusal, so each refusal reads 0.
SX7 also renumbers argument capabilities and words to seL4's operand layout, and owns the last open numbering items:
- SetSpace's CSpace root becomes argument 2 and its VSpace root argument 3, because the MCS fault endpoint is argument 1.
- The Untyped_Retype and IRQControl_Get destination lookups become `FailedLookup` with their depth operand.
- Page_Map's invoked and argument capabilities follow seL4: the frame capability is invoked, and the VSpace is extra capability 0.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX7.1 | The lookup itself. CNode Copy, Mint and Move: `srcRoot` is extra capability 0, and the words follow seL4 (D12); `CNodeOpWord` retires. | The decode round trips and `_error_iff`; the `capFaultReceivePhase?` send-phase case; the CNode arms' preservation. | `abi_layout.expected` (`cnodeCopyBit` block out, caps base in); `sele4n-abi` `args/cspace.rs`, `encode.rs` |
| SX7.2 | Untyped_Retype (D9), IRQControl_Get (D10), PageTable_Map, Page_Map on the frame capability (D6). | The retype loop's carve theorems; the map arms' preservation; the mapping-record stage. | `args/lifecycle.rs`, `args/vspace.rs` |
| SX7.3 | SetPriority and SetMCPriority with an authority TCB (D11); BindNotification; SchedContext_Bind; SchedControl_ConfigureFlags; IRQHandler_SetNotification. | The MCP authority theorems restated over the authority capability. | `args/tcb.rs`, `args/sched_context.rs` |
| SX7.4 | SetSpace in the MCS shape: the fault endpoint, CSpace root and VSpace root as extra capabilities 0–2. A TCB fault-handler slot (D8). `tcbSetFaultHandler` retires. Fault delivery reads the slot, and answers `missingCapability 0` when it holds no endpoint (`faulthandler.c:99`). A CSpace or VSpace root argument whose slot is empty or holds no object capability gets seL4's answer for it, where SX1 still answers `invalidCapability` through `resolveCallerCapSlot`. | The fault-delivery family over the slot; the slot invariants; `cnodeCapGeometry` kept by SetSpace. | `fault_handling_4core.expected` |
| SX7.5 | SetIPCBuffer: the frame capability is derived into SX5.2's slot (D7). Every buffer read goes through `lookupIPCBuffer`. `ipcBufferWordPAddr?` and `tlbFillIpcBufferOnCore` retire. | Every theorem citing the retired read, restated over the frame capability. The buffer-in-one-frame fact taken from the capability. | Tier 3 IPC-buffer anchors; `syscall_return_abi.expected` |

**Acceptance:**
- `extra-cap-lookup-fault`.
- `extra-cap-missing-truncated`.
- `extra-cap-wrong-kind`.
- `retype-num-objects`.
- `set-priority-authority`.
- `fault-handler-not-endpoint`.
- `set-ipc-buffer-frame-cap`.

### SX8 — Timeout faults and the MCS TCB calls

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX8.1 | A TCB timeout-handler slot, and `SetTimeoutEndpoint` (extra capability 0). | The slot invariants. | `sele4n-abi` `args/tcb.rs` |
| SX8.2 | `SetSchedParams`: the authority, scheduling context and fault endpoint as extra capabilities; MCP and priority as words. | The MCP authority and binding theorems. | the same |
| SX8.3 | A running thread's budget overrun with a valid timeout handler raises `seL4_Fault_Timeout` (MCS tag 5, with the context's badge and consumed time). A blocked IPC is no longer timed out: `timeoutThread` and `ipcTimeout` retire, and the discriminant is reserved. | The budget and CBS theorems; the donation-chain (WS-OD, WS-HP) theorems that cited `timeoutThread`; `faultLabel_ne_timeout` retires into the timeout fault's label theorem. | `fault_handling_4core.expected`; `smp_4core_scheduler.expected` |

**Acceptance:** `timeout-fault-delivered`, `blocked-call-not-timed-out`,
`set-sched-params`.

### SX9 — seL4's CNode invocation set (D16, D17)

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX9.1 | Delete and Revoke address their target by index and depth (`lookupTargetSlot`). | The two arms' decode and preservation. | `args/cspace.rs` |
| SX9.2 | Mutate: a Move with `updateCapData` preserving. A null result is IllegalOperation. | `cspaceMove`'s CDT, link and occupancy theorems over a rewritten capability. | the same |
| SX9.3 | Rotate, per `cnode.c:231`. | The CDT, `cdtLinksAgree` and `CapTreeShape` preservation for two moves; the footprint (3 slots, 2 roots). | the same |
| SX9.4 | CancelBadgedSends: all four endpoint rights; the senders with the badge are removed and set to Restart; badge 0 does nothing (`endpoint.c:489`). | Endpoint queue well-formedness; run-queue insertion; non-interference for the arm. | `smp_ipc_4core.expected` |

**Acceptance:**
- `cnode-delete-index-depth` and `cnode-revoke-index-depth`.
- `cnode-mutate-guard` and `cnode-mutate-badged-refused`.
- `cnode-rotate` and `cnode-rotate-pivot-is-source-refused`.
- `cnode-cancel-badged-sends`: only the matching senders restart.

### SX10 — seL4's error codes in the label (D1)

This row needs F1 to hold. SX3, SX4, SX6 and SX8 made it hold.

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX10.1 | `KernelError.sel4Error`, total (D1). The error frame's label is the seL4 code. `errorLabelBase` retires. | `receivePhase_noErrorFrame`: no receive-phase syscall returns an error frame. `sendInvocation_noErrorFrame`. The label round trip over seL4 codes with the payload. The `faultLabel_lt_errorLabelBase` family retires into these. | `abi_layout.expected` (`errorLabelBase` out); `syscall_return_abi.expected`; the `sele4n-types` error table; `test_rust_conformance.sh` |

**Acceptance:** every error scenario re-pinned to seL4's codes; a fault
handler's receive reads fault tags only.

### SX11 — Closure

| Sub-task | Change | Proofs | Gates and fixtures |
|---|---|---|---|
| SX11.1 | `docs/CLAIM_EVIDENCE_INDEX.md` gets a row per seL4 behaviour this plan follows. The spec's syscall-boundary section is rewritten to the seL4 ABI. The workstream is closed in `docs/REGISTERED_DEBT.md` and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, and this plan moves to `docs/dev_history/planning/`. **Full documentation sweep against the final tree:** the spec, every GitBook chapter on the syscall ABI and CSpace, README metrics, `docs/DEVELOPMENT.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, the `docs/REGISTERED_DEBT.md` index row, and `docs/agent_guide/WORKSTREAM_CONTEXT.md`, whose WS-SX section moves to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`. **Refresh every not-yet-started plan** against WS-SX's final tree: the remaining WS-UC rows UC6–UC10, `CONTEXT_BY_VALUE_PLAN.md`, `HIERARCHICAL_CBS_PLAN.md`, `LOCK_STATE_SEPARATION_PLAN.md`, and every other plan under `docs/planning/` — file:line citations, names, rows the new ABI makes obsolete or newly needs, and the decisions it affects. If the refresh is too large for SX11, it is the very next PR, landed before any next-row code. | none | `check_claim_evidence_citations.py` |

## 5. Estimate

| Row | Sessions |
|---|---|
| SX1 | 2 |
| SX2 | 3–4 |
| SX3 | 1 |
| SX4 | 2 |
| SX5 | 3–4 |
| SX6 | 3–4 |
| SX7 | 5–6 |
| SX8 | 2–3 |
| SX9 | 2 |
| SX10 | 1 |
| SX11 | 1 |

About 25–30 sessions in all. The largest risks:
- the boot base case (SX5.3);
- the IPC-buffer read path (SX7.5);
- keeping refusals at 0 heap cells (D2b).

## 6. Asides recorded at planning

- `tcbSetAffinity` has no seL4-MCS counterpart: a thread's core follows its
  scheduling context's `SchedControl` core. SX6.1 gives it a model-only label.
  Retiring it is the owner's call, and it is not registered as debt.
- The `partialResolution` row of `docs/REGISTERED_DEBT.md` table C is
  unaffected. IPC keeps seL4's drop-on-failure, and invocations fault, as seL4
  does.
