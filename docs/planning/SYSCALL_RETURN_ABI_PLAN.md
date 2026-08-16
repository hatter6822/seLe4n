# WS-RA — Syscall Return ABI: full seL4-ABI x0 compliance

> **Workstream**: WS-RA (Return ABI)
> **Relationship to WS-SM**: prerequisite for SM10.E (bootable image) and for
> SM9.C (data-carrying declassification); orthogonal to the SMP phases
> **Audited cut**: `v0.33.30`
> **Target releases**: v0.34.x
> **Calendar estimate**: 5-8 weeks
> **Sub-task count**: 38 across ~12-15 PRs
> **Status**: PENDING

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

Three further consequences fall out of the same gap:

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

### 1.3 Why "x0 compliance" and not "write x1"

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

- `x0` = primary return value (badge / slot / `0` for `Unit`-returning syscalls)
- `x1` = `MessageInfo` with `label` = `KernelError` discriminant, `0` = success
- `x2`-`x5` = message registers
- **`encodeOk` / `encodeError` and the bit-63 protocol are retired.**  Bit 63 was
  a workaround for multiplexing status into the value register; with the channels
  separated there is nothing to multiplex, and a badge may use all 64 bits.

The carrier already exists: `MessageInfo.label` is a 20-bit field documented as
"seL4 convention", and `KernelError` has 54 discriminants.  No new register, no
new structure.

### 3.2 Why the label, and what it costs

The alternative — keep `x0` as status and put values in `x1` — is the x1 route
§1.3 rejects.  The alternative *within* x0 compliance is a dedicated error
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
return type changes once, from `Kernel UInt64` to `Kernel SyscallReturnFrame`,
and no dispatch arm grows a tuple.

This also matches how a real kernel works — the trap handler restores the thread's
register context — which means RA.C.2 is a context restore rather than a special
case bolted onto the SVC path.

### 3.4 Which syscall returns what: a total function

Six rounds of review on the SM9 plan established one lesson repeatedly: a
**hand-maintained list plus a completeness theorem cannot force a new member to
join it**, because the theorem stays true when a new arm joins neither the list
nor the classification.  It was learned three times there (`ReadableStructure`,
`ContentFlowSite`, `declassificationSyscalls`) and it applies here directly.

**Decision.**  `syscallReturnShape : SyscallId → ReturnShape` is a **total
function** over the `SyscallId` enumeration the ABI already forces to be
complete, with `ReturnShape` naming what each syscall puts in `x0` and the
message registers (`unit` / `badge` / `slot` / `message n`).  A new syscall is a
missing case at elaboration, not a silent omission.  `syscallReturnShape_total`
is the theorem; `returnShape_list_gate_insufficient` keeps the refuted design
refuted.

The conformance layer then checks the Rust mirror against it per-variant, in the
idiom `SyscallId` conformance already uses.

### 3.5 An ABI break needs a structural guard, not a changelog note

Kernel and userspace ship from one tree, so an atomic flip is available and no
compatibility shim is warranted.  But a **half-migrated** system does not fail
loudly: it silently reinterprets registers, which is exactly the failure mode
§1.2 describes.

**Decision.**  A compile-time `SYSCALL_ABI_VERSION` constant, mirrored in Lean
and Rust and checked by the existing conformance suite, so a half-migrated tree
fails the build rather than mis-decoding at runtime.  This is the same mechanism
`SyscallId` conformance already uses, extended to the return convention.

### 3.6 What this workstream does *not* change

Recorded so scope cannot drift:

- **Argument passing** is untouched — `writeFfiRegistersToTcb`, the `x7` syscall
  number, `x0` as cap pointer *on entry*.  Only the return direction moves.
- **`KernelError` discriminants** keep their numeric values; only their carrier
  moves from `x0` to the label.
- **The IPC buffer path** (`ipcBufferReadMr`) is unrelated: it is how *arguments*
  beyond the register file are read, not how results are returned.
- **`DispatchError`** stays the Rust-internal dispatch-layer type; only its
  encoding across the FFI boundary changes.

## 4. Detailed sub-task breakdown

Sizes: **T** trivial, **S** small, **M** medium, **L** large, **XL** very large.

### RA.A — The convention, modelled (3-4 PRs, 8 sub-tasks)

Pure model work.  Nothing live changes; the old path keeps running until RA.C.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.A.1 | `ReturnShape` inductive (`unit` / `badge` / `slot` / `message n`) + `Repr`/`DecidableEq`; `ReturnShape.registerCount` | new production leaf `Platform/SyscallReturn.lean` | S |
| RA.A.2 | **`syscallReturnShape : SyscallId → ReturnShape`** — a *total* function (§3.4), with `syscallReturnShape_total` and `returnShape_list_gate_insufficient` | same | M |
| RA.A.3 | `SyscallReturnFrame` (the six-register result) + `default` (all zero) + accessors; `returnFrame_unit_is_zero` | same | S |
| RA.A.4 | `encodeReturnFrame` / `decodeReturnFrame` against the §3.1 layout, and the **round-trip** theorem `decodeReturnFrame_encodeReturnFrame` — losslessness, since `x0` now carries a full 64-bit badge | same | M |
| RA.A.5 | Error carriage: `MessageInfo.label` ⇄ `KernelError`, `errorLabel_roundtrip` both ways, and `errorLabel_zero_iff_success` (label 0 ⇔ no error) | `Platform/SyscallReturn.lean` | M |
| RA.A.6 | `kernelErrorFitsLabel` — all 54 discriminants inside 20 bits, by `decide`; the negative that a 21-bit discriminant is rejected, so the bound is load-bearing | same | S |
| RA.A.7 | `SYSCALL_ABI_VERSION` (§3.5) + the Lean half of the conformance pin | same | T |
| RA.A.8 | **Retirement of the bit-63 protocol, stated**: `encodeOk_not_injective_on_badges` (the theorem that motivates the change — a badge ≥ 2^63 aliases an error under the old encoding), kept as a negative so the protocol cannot return | same | S |

### RA.B — The Lean return path (3-4 PRs, 10 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.B.1 | `writeReturnFrameToTcb` — the dual of `writeFfiRegistersToTcb`, staging results into `tcb.registerContext`; frame lemmas (`_objects_eq` off the target, `_scheduler_eq`, `_machine_eq`) | `Platform/FFI.lean` | M |
| RA.B.2 | `readReturnFrame` generalising `readReturnValue` to the register range; `readReturnFrame_writeReturnFrame` round trip; `readReturnValue` retained as its `x0` instance so existing theorems stand | same | M |
| RA.B.3 | `syscallDispatchFromAbi : Kernel SyscallReturnFrame` — the signature change, and the **6 theorems that name it** re-stated: `_total`, `_error_of_syscallEntryChecked_error`, `_illegalState_when_no_current`, and the three bridges | same | L |
| RA.B.4 | The "an error changes nothing" proofs, re-checked against the new shape — `syscallEntry_error_perCore_NI` and `syscallEntry_error_preserves_proofLayerInvariantBundle` both bake in the old encoding | `API.lean`, `CovertChannelPerCore.lean` | L |
| RA.B.5 | **`.notificationWait`** returns its badge — the SM9.C.0 defect, closed here; both live arms and the pending-badge arm of `notificationWaitOnCore` | `API.lean`, `IPC/CrossCore/NotificationSignal.lean` | M |
| RA.B.6 | **`.receive` / `.replyRecv`** return badge + message registers | `API.lean` | L |
| RA.B.7 | **`.cspaceMint` / `.cspaceCopy` / the retype family** return their allocated slot | `API.lean` | M |
| RA.B.8 | Every remaining arm returns `SyscallReturnFrame.default`, driven by `syscallReturnShape` so the classification and the arms cannot disagree; `dispatchArm_matches_returnShape` | `API.lean` | L |
| RA.B.9 | `syscallDispatchCrossCoreEntry` threads the frame; the `@[export]` seam and its Rust-visible signature | `Kernel/SyscallDispatchEntry.lean` | M |
| RA.B.10 | Information flow: the return frame is written into a TCB the caller already owns, so `writeReturnFrameToTcb_preserves_projection` is owed — a return value is *by construction* data the caller may see, but the theorem is what says so | `InformationFlow/Invariant/Operations.lean` | M |

### RA.C — The Rust boundary (2-3 PRs, 8 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.C.1 | `lean_syscall_dispatch_cross_core`'s new signature; `dispatch_svc` returns the frame rather than a bit-63 word | `rust/sele4n-hal/src/svc_dispatch.rs` | M |
| RA.C.2 | **Trap-frame writeback** — `set_x0`…`set_x5` from the returned frame, as a context restore (§3.3).  `set_x1` stops being dead code | `rust/sele4n-hal/src/trap.rs` | M |
| RA.C.3 | Retire the bit-63 decode in `dispatch_svc`; `DispatchError::Kernel` now sourced from the label | same | S |
| RA.C.4 | `SYSCALL_ABI_VERSION` Rust mirror + the conformance pin that fails the build on a half-migrated tree (§3.5) | `rust/sele4n-abi/src/lib.rs` | S |
| RA.C.5 | `decode_response` rewritten to the §3.1 layout: error from the **label**, `x0` a full-width value, `x2`-`x5` real message registers | `rust/sele4n-abi/src/decode.rs` | L |
| RA.C.6 | `SyscallResponse` reshaped — `x1_raw`'s context-dependent dual meaning (badge *or* msg_info) collapses, since the badge moves to `x0`; `badge()` reads `x0`, `msg_info()` reads `x1` | same | M |
| RA.C.7 | The `regs[0] > u32::MAX` guard is retired with the convention that motivated it, and its replacement — a label-width check — takes its place with the same fail-closed posture | same | S |
| RA.C.8 | Rust-side unit tests for the new decode, including the **regression witness** that a nonzero `x0` is a value and not an error | same | M |

### RA.D — Wrappers and conformance (2 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.D.1 | Every `sele4n-sys` wrapper's error handling, through the single `decode_response` funnel (§3.2) | `rust/sele4n-sys/src/*.rs` | L |
| RA.D.2 | `notification_wait` returns a **real** badge; `endpoint_receive` / `reply_recv` return real badges and message registers | `rust/sele4n-sys/src/ipc.rs` | M |
| RA.D.3 | `cspace_mint` and the retype family return their slot instead of an opaque `SyscallResponse` | `rust/sele4n-sys/src/{cspace,lifecycle}.rs` | M |
| RA.D.4 | Per-variant conformance: every `SyscallId`'s `ReturnShape` checked against the Rust mirror, driven by RA.A.2's total function | `rust/sele4n-abi/tests/conformance.rs` | M |
| RA.D.5 | Round-trip conformance: encode in Lean, decode in Rust, for each shape | same | M |
| RA.D.6 | Doc comments corrected across the wrapper surface — several currently describe returns the ABI never delivered (`notification_wait`'s "returns the accumulated badge" being the one that started this) | `rust/sele4n-sys/src/*.rs` | S |

### RA.E — Tests, fixtures, closure (2-3 PRs, 6 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RA.E.1 | **The observable-failure test, written first** (§1.2): a harness-level round trip that today decodes a successful syscall's cap pointer as a `KernelError`.  It must **fail on the pre-migration tree** and pass after — otherwise the workstream has no witness that it fixed anything | new `tests/SyscallReturnAbiSuite.lean` | L |
| RA.E.2 | Per-shape acceptance: badge round trip (signal-before-wait **and** wait-before-signal, the SM9.C.0 orderings), slot return, message-register return, `Unit` returning zero | same | XL |
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
3. **RA.C.1-C.4 + RA.B.9 in one PR** — the flip.  This is the only PR that must
   change both languages atomically, which is why RA.A.7/RA.C.4's version pin
   exists: a partial flip fails the build.
4. **RA.C.5-C.8, RA.D** — userspace catches up behind the flip.
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
./scripts/test_abi_conformance.sh            # both mirrors + the version pin
lake exe sele4n                              # golden trace: expected to move
```

The trace fixture **will** change at the flip — the `[XVAL-002]` line and any
line reporting a syscall return.  That diff is the evidence the flip worked, and
RA.E.4 pins the new value.  A byte-identical trace across the flip would mean the
return path is still unexercised.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| A half-migrated tree mis-decodes silently | HIGH | **HIGH** | `SYSCALL_ABI_VERSION` pinned in both mirrors and checked by conformance (§3.5); the flip is one PR (§5) |
| The fix is unobservable because nothing boots | HIGH | MED | RA.E.1 lands **first** and must fail pre-migration; a workstream that cannot demonstrate the failure cannot demonstrate the fix |
| A new syscall omits its return shape | MED | HIGH | `syscallReturnShape` is a **total function** over the ABI's own enumeration (§3.4), not a list — the lesson from six SM9 review rounds |
| Badge ≥ 2^63 aliases an error | — | — | Structurally impossible after the flip: the channels separate, which is the point.  `encodeOk_not_injective_on_badges` (RA.A.8) keeps the old hazard on the record |
| The error-carriage change breaks `DispatchError` consumers | MED | MED | `DispatchError` stays Rust-internal (§3.6); only its FFI encoding moves, and `decode_response` is the single funnel (§3.2) |
| Return values leak across a security boundary | LOW | HIGH | The frame is written into the caller's **own** TCB, so a return value is by construction data the caller may see — but `writeReturnFrameToTcb_preserves_projection` (RA.B.10) is what says so rather than assuming it |
| Scope creep into argument passing or the IPC buffer | MED | LOW | §3.6 fixes the boundary explicitly |

## 8. Acceptance gate

- [ ] A successful syscall returns a value userspace decodes **as a value**, and
      RA.E.1 — which failed on the pre-migration tree — passes.
- [ ] `notification_wait` returns the badge that was signalled, in **both**
      orderings (signal-before-wait and wait-before-signal), closing SM9.C.0.
- [ ] `endpoint_receive` returns real message registers, not the caller's own.
- [ ] Every `SyscallId` has a `ReturnShape` by construction, and a new syscall
      cannot be added without one.
- [ ] Every `KernelError` discriminant round-trips through the message label, by
      enumeration.
- [ ] `encodeOk` / `encodeError` and the bit-63 protocol are **gone**, with
      Tier-3 negative anchors preventing their return.
- [ ] Lean and Rust agree on `SYSCALL_ABI_VERSION`, enforced at build time.
- [ ] `FFI.lean`'s "documented current behaviour" note is deleted, because the
      behaviour it documents no longer exists.
- [ ] Zero `sorry`/`axiom`; Tier 0-3 green; the trace-fixture diff at the flip is
      explained and pinned.

## 9. Cross-references

- **Blocks**: [`SMP_DECLASSIFICATION_COMPLETION_PLAN.md`](SMP_DECLASSIFICATION_COMPLETION_PLAN.md)
  SM9.C.0 (the badge defect this closes), and
  [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) SM10.E.
- **Reference**: seL4 ARM64 syscall convention, libsel4
  `arch/arm/arch64/sel4/sel4_arch/syscalls.h`.
- **The note this workstream removes**: `SeLe4n/Platform/FFI.lean`, the
  `readReturnValue` docstring's "documented current behaviour" paragraph.

## 10. Theorem catalogue

~24 substantive theorems.  Headline set:

- `syscallReturnShape_total` + `returnShape_list_gate_insufficient` (RA.A.2)
- `decodeReturnFrame_encodeReturnFrame` — losslessness at full 64-bit width
  (RA.A.4)
- `errorLabel_roundtrip` + `errorLabel_zero_iff_success` (RA.A.5)
- `kernelErrorFitsLabel` + its 21-bit negative (RA.A.6)
- `encodeOk_not_injective_on_badges` — the hazard the flip removes, retained as a
  negative (RA.A.8)
- `readReturnFrame_writeReturnFrame` (RA.B.2)
- `syscallDispatchFromAbi_total` at the new type (RA.B.3)
- `dispatchArm_matches_returnShape` — the arms and the classification cannot
  disagree (RA.B.8)
- `writeReturnFrameToTcb_preserves_projection` (RA.B.10)
- `notificationWait_delivers_badge_both_orderings` — the SM9.C.0 closure
  (RA.B.5, RA.E.2)

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Platform.SyscallReturn
lake build SeLe4n.Platform.FFI
lake exe syscall_return_abi_suite
./scripts/test_rust.sh
./scripts/test_abi_conformance.sh
./scripts/test_full.sh
```
