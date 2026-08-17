# SM9 — Declassification Completion (WS-SM Phase 9)

> **Phase**: SM9 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Predecessor**: [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md) (SM8, CLOSED v0.33.23)
> **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10)
> **Audited cut**: `v0.33.23`
> **Target releases**: v0.33.24 → v0.34.x
> **Calendar estimate**: 12-16 weeks
> **Sub-task count**: 61 across ~21-26 PRs
> **Status**: PENDING

## 1. Phase goal

SM8 shipped a **live `.declassify` syscall** (`SyscallId` 30) with a mounted,
bounded, fail-closed audit trail — and registered four follow-ons it did not
close.  SM9 closes all four, so that v1.0.0 can claim declassification as a
working capability rather than a half-built one.

The four, as SM8 registered them:

| # | Gap | Consequence today |
|---|-----|-------------------|
| 1 | **No interface reads the trail** | The trail is write-only.  Its 256-entry bound is fail-closed, so a deployment that performs 256 authorized downgrades **stops being able to declassify at all** until reboot. |
| 2 | **Refused declassifications are unaudited** | A monitor cannot distinguish "no attempts" from "many attempts, all denied".  A detection gap, not an enforcement one. |
| 3 | **`.declassify` moves no data** | It authorizes and records a downgrade; no bytes cross.  The primitive an MLS downgrader needs is half-built. |
| 4 | **Chain linkage is syntactic** | `declassificationChainLinked` matches domains and increasing timestamps with no data-dependency behind it, so the laundering detector over-approximates. |

**Why this is a phase and not an SM10 fold-in.**  SM8 provisionally scoped all
four to "SM9", which at the time meant release closure.  Release closure is
documentation sync, test completion, the version bump and QEMU validation — it
has no room for kernel work, and all four items are kernel work.  This phase
takes the SM9 slot; release closure moved to SM10.

**Why before v1.0.0.**  The project's implement-the-improvement rule is directly
on point: *"a capability claim while the path is non-functional → make the path
functional, never qualify the claim with a stub-status caveat."*  v1.0.0
currently ships a declassification syscall whose trail cannot be read and whose
bound bricks the feature after 256 uses.  Either the path becomes functional, or
v1.0.0 must not claim declassification.

**Concrete deliverables**:

1. **A privileged audit reader** (SM9.A): clearance-filtered read + drain, which
   is what makes the fail-closed 256-entry bound survivable.
2. **Refusal auditing** (SM9.B): a saturating attempt counter plus a bounded
   ring of recent attributed refusals, neither able to displace an authorized
   entry.
3. **A data-carrying declassification** (SM9.C): a badge crossing a label
   boundary on the SM6.B notification path, with declassification-relative
   non-interference.
4. **Causal declassification provenance** (SM9.D): taint propagated through
   ordinary IPC delivery, so the laundering detector becomes sound rather than
   syntactic.  The phase's largest sub-phase — see §3.6 for why declassification
   edges alone cannot do it.
5. **Tests + closure** (SM9.E).

## 2. Dependencies

- **SM6.B**: the cross-core notification signal path (SM9.C rides it).
- **SM8.C**: the mounted trail, `declassificationDecision`, the rule inventory.
- **SM8.E**: `KernelOperation.all` + `mem_all` — what makes SM9.C.7's inventory
  growth safe (a 36th operation either fails `mem_all` or moves all three
  counts).
- **WS-RA** ([`SYSCALL_RETURN_ABI_PLAN.md`](SYSCALL_RETURN_ABI_PLAN.md)) —
  **was blocking for SM9.A and SM9.C; the core landed at v0.33.37.**  The
  audit reader is a *value-returning* syscall: returning a word is its entire
  purpose.  Before WS-RA, `dispatchWithCapChecked` was `Kernel Unit` and
  `syscallDispatchFromAbi` took its success value from `readReturnValue` on
  the post-state TCB, which no transition wrote — so `.auditRead` would have
  gated correctly, computed correctly, and handed back the caller's own
  preloaded `x0` capability argument.  WS-RA built the missing path: value
  syscalls stage a seL4 ARM64 return frame
  (`Architecture.writeReturnFrameToTcb` + `returnFrameOfBadge` /
  `returnFrameOfWord` / `returnFrameOfMessage`) into the caller's
  `registerContext` at their dispatch arms, and the boundary reads it back
  shape-driven (`syscallReturnShape` — a **total** function whose `.auditRead`
  / `.auditDrain` arms SM9 must add, so forgetting one is a compile error,
  never a silent `.unit`).  SM9.A.10 declares those two `ReturnShape` arms and
  stages with `returnFrameOfWord`.  **§3.3's payload arithmetic predates the
  flip and is updated in place below**: the bit-63 `encodeOk` encoding is
  retired, a returned word is a full 64 bits, and a frame additionally
  carries `x2`–`x5` as message registers.

## 3. Architectural choices

### 3.1 Refusal attribution: re-derive nothing

The tempting design is to widen `syscallEntryChecked`'s error so it carries the
decoded syscall.  **Rejected.**  The blast radius is ~40 theorems whose
statements name the entry (8 in `API.lean`, 3 in `CovertChannelPerCore.lean`,
4 in `FFI.lean`, ~25 in `FineLockFlow.lean`), ~40 Tier-3 grep anchors, two
computed-`Prop` inventories and 10 golden-fixture lines.  Two proofs bake in
*"an error changes nothing"* and would break outright:
`syscallEntry_error_perCore_NI` (`CovertChannelPerCore.lean`, proved by `rfl` +
`observableSlotsConfinedToCore_refl`) and
`syscallEntry_error_preserves_proofLayerInvariantBundle` (`API.lean`, proved by
`exact hInv`).  `entryDecode_some_entry_dispatches` (`FineLockFlow.lean`)
already carries a recorded argument against exactly this refactor.

It is also unnecessary.  `Kernel α = SystemState → Except KernelError (α × SystemState)`
does give an `.error` arm no post-state — but one layer up,
`syscallDispatchFromAbi` (`Platform/FFI.lean`) already converts every kernel
error into `.ok (.returns (Architecture.errorFrame ke), stRegs)` (the WS-RA
error frame, whose `x1` label carries `discriminant + 1`), and
`syscallDispatchCrossCoreEntry` commits that state.  **A refused syscall
already commits a post-state.**  And
every field a refusal record needs is already an argument there:

| Field | Source at the seam |
|---|---|
| executing core | `executingCore` parameter |
| subject thread | `st.scheduler.currentOnCore executingCore` (already matched on) |
| **failed hop** | which authorization was refused — `callerToNotification` or `notificationToReceiver` (§3.5) — plus the **resolved receiver** when it is the second.  Without it a refusal reduces to the original capability operand and a generic reason, so a monitor cannot identify the bound waiter an attempted downgrade actually targeted — while the *success* path is required to audit exactly that destination.  `refusalRecord_names_failed_hop` |
| **source domain** | `ctx.threadLabelOf` of that subject, **resolved at the seam** — `LabelingContext` is an *argument* to `syscallDispatchFromAbi`, not persistent state, so a later reader cannot reconstruct the domain from the subject id (the context may differ, or the id may have been reused).  The authorized-event trail already stores its domains for the same reason |
| syscall | `syscallId : UInt32`, via the pure total `SyscallId.ofNat?` |
| refusal reason | `ke : KernelError` |
| requested target | `x0` — the raw `CPtr` the caller supplied |

No decode replay, no anti-drift tie, no entry-shape change.  The record stores
the **raw `CPtr`**, not a resolved `ObjId`: it is what the caller asked for (the
more useful datum for detection), and resolving it would reintroduce the
CSpace-walk duplication this design exists to avoid.

Exactly **one** existing theorem changes shape —
`syscallDispatchFromAbi_error_of_syscallEntryChecked_error`, whose conclusion
names the committed state as exactly `writeFfiRegistersToTcb …`.
`syscallDispatchFromAbi_total` is re-proved mechanically.

The two *earlier* error paths in `syscallDispatchFromAbi` (ABI mismatch, no
current thread) record **nothing** — there is no subject to attribute to, the
same fail-closed discipline `declassifyStoreFromCore_no_subject` applies.

**The seam's filter is derived, not written out.**  A draft of this section
filtered on the literal `.declassify`, which SM9.C then silently defeats: it adds
a *second* declassifying syscall, `.declassifySignal`, whose refusals would
bypass `recordRefusal` entirely — leaving a monitor unable to distinguish "no
data-carrying downgrade attempts" from "many, all denied", which is the exact gap
SM9.B exists to close.  A **list plus a completeness theorem does not achieve that**, and this is the
third time the same shape has been tried in this plan (after `ReadableStructure`
and `ContentFlowSite`, both §3.7): a theorem quantified over a hand-maintained
"consults `declassificationDecision`" classification stays true when a new
dispatch arm consults it and joins neither the list nor the classification.  The
gate has to be keyed to something exhaustive *independently* of the gate.

So the seam reads a **total function** `SyscallId → RefusalSeamClass`
(`records` / `exempt`) over the `SyscallId` enumeration the ABI already forces to
be complete — every arm must be classified or the function does not elaborate —
with `refusalSeamClass_total` and `refusalSeam_list_gate_insufficient`.  SM9.C.8
then classifies `.declassifySignal` as part of adding it, because it cannot
compile otherwise.  SM9.E carries a denied-`.declassifySignal` acceptance
case so the wiring is exercised rather than merely declared.

### 3.2 Refusal state: structural bounds, not an invariant conjunct

`declassificationAuditLog` is a `List` whose bound is the 16th
`proofLayerInvariantBundle` conjunct, carried by a five-lemma block in
`Architecture/Invariant.lean`.  **Do not repeat that here.**  CLAUDE.md prefers
*"enforce it structurally (record field, refinement type, smart-constructor
obligation)"* over an invariant held by convention, and a refusal ledger can be
bounded by its type:

```lean
structure RefusalLedger where
  attemptCount : Fin (maxRefusalCount + 1)
  recent       : Vector (Option DeclassificationRefusal) refusalRingSize
  nextSlot     : Fin refusalRingSize
  droppedCount : Fin (maxRefusalCount + 1)
```

A `Vector` cannot exceed its size, so there is **no 17th bundle conjunct, no
five-lemma carriage block, and no `refine ⟨?_,…⟩` arity re-count** — which
matters, because those destructurings are right-nested and a trailing
under-listing elaborates *silently*.  `default_perCoreICache`
(`Model/State.lean`) is the precedent for the `default_*` discharge shape.

**The two counters are `Fin`, not `Nat`.**  An earlier draft made them `Nat`
with "saturating" as a convention of `recordRefusal` — which is exactly the
convention-not-structure shape this section rejects one paragraph above, applied
inconsistently to two fields of the same record.  A `Nat` bounded only by its
updater leaves every *other* way of building the structure unconstrained: an
arbitrary `SystemState` or `FrozenSystemState` literal (the freeze layer, the six
test literals of SM9.B.5, a future boot path) can carry an out-of-range value and
nothing rejects it.  With `Fin (maxRefusalCount + 1)` the saturation is the
type's, so `recordRefusal` *cannot* overflow it and no theorem is needed to say
so — the structural-enforcement argument now covers the whole record rather than
one field of it.  Cost: saturating increment is `min (n + 1) maxRefusalCount`
lifted into `Fin`, one helper with two lemmas (saturates, monotone).

**Reads of the ledger need a version, for the same reason the trail's do.**  A
refusal record takes several `.auditRead` calls — more with the §3.3 chunk
protocol — and any denied syscall in between can overwrite the selected ring
slot.  The trail's `status` token does not help: it moves on trail *drains*, not
on ledger writes, so a monitor can assemble a **hybrid record** whose fields came
from two different attempts and never detect it.  So `RefusalLedger` carries a
`version` advanced by **every** `recordRefusal`, and a read is bracketed by it
exactly as a trail read is bracketed by the drain generation
(`refusalLedger_version_advances_on_record`,
`refusalRead_bracketed_detects_overwrite`).  This is §3.3's atomicity argument
applied to the second readable structure — the §3.7 discipline says a readable
structure owes both obligations, and consistency-under-concurrent-write is part
of what a reader is owed.

**The ledger is readable only under full dominance** (§3.7 obligation (b)).  A
single global ring evicts: once a low-visible refusal occupies a slot, enough
higher-domain refusals *that the reader cannot see* wrap the ring and overwrite
it, so a hidden write removes an entry from a low reader's view — a channel from
every refusing subject to every reader.  The counters carry the same defect
independently: a saturating global `attemptCount` moves on hidden activity, so
returning it to a partial reader leaks the same bit even with the ring fixed.

Partitioning by domain does **not** type: `SecurityDomain.id` is an unbounded
`Nat`, so there is no finite family of domains to give a `Vector` per domain.
Requiring full dominance discharges the obligation instead of dodging it — a
partial reader observes *nothing* of the ledger, so no hidden write can move its
view, and the dominating reader sees every write by definition.

**Dominance over *what*, though — and the obvious answer is wrong.**  A first
draft reused drain's gate, which quantifies over the domains *represented in the
current records*.  That is unsound here, because the ledger's two halves age
differently: the ring **evicts** while the counters are **cumulative**.  Let a
run of hidden high-domain refusals bump `attemptCount` and `droppedCount`, then
let a ringful of low-domain refusals wrap the ring and overwrite every high
entry.  A low reader now dominates every *surviving* row — so a
records-derived gate admits it — and reads counters that still carry the hidden
history.  The gate would be computed from a set that shrinks while the data it
guards does not.

So the ledger is gated on the **configured system-wide audit clearance**
(`LabelingContext.auditMonitorClearance`, the single privileged-reader gate
§3.4 names), not on the ring's contents: a fixed
deployment parameter, deny-by-default when unset, that cannot be lowered by
eviction.  `refusalLedger_gate_is_configuration_derived` is the theorem, and
`refusalLedger_records_gate_unsound` keeps the counterexample above as a
negative so a later cut cannot quietly revert to the cheaper gate.  Drain's own
gate is left as-is: the trail has no cumulative counter, so nothing there
survives what a drain removes — but see §3.3 on the one quantity that *does*
survive, and what it leaks.

The operator consequence is unchanged and, if anything, clearer: refusal
monitoring wants one fully-cleared monitor, named in configuration.

### 3.3 Reader interface: indexed read, no new kernel→user write path

**Updated for WS-RA (v0.33.37).**  This section was drafted against the
pre-WS-RA boundary, where a syscall returned exactly one word
(`frame.set_x0(retval)`) whose bit 63 was reserved as the `encodeOk` /
`encodeError` error flag.  Both premises are retired: the trap handler now
restores a full seL4 ARM64 return frame (`set_return_frame` writes `x0`–`x5`;
the error travels in `x1`'s `MessageInfo` label, offset by one), so **a
returned word is a full 64 bits**, and one call can additionally carry up to
four message-register words in `x2`–`x5` (`returnFrameOfMessage`).  The reader
below stays at one *value* word per call (`x0`, staged via
`returnFrameOfWord`) — the conservative shape; 64-bit chunks halve the call
count relative to the old arithmetic, and packing four chunks per call
through the message registers is an SM9.A optimisation the frame permits but
this design does not require.  What does **not** survive is the bit-63
aliasing constraint and the `auditReadWord_fits_payload` theorem built on it:
a full-width word cannot alias the error channel, because value and error now
travel in separate registers.  The chunking itself survives for the deeper
reason in the bullets.  Consequences for SM9.A.2, all of them design
constraints rather than notes:

- `core ⊕ kernelIssued` packs comfortably into one word — but the trust bit
  is **not** the whole of `authorizationBasis`.
  `AuditRecord.lean` defines the basis as a designation *paired with* that bit
  (`renderTagged` ships both, and `renderTagged_injective` is why), so exporting
  the bit alone collapses every `integratorOverride` to one externally-readable
  value and leaves a monitor unable to say *which* out-of-band authority
  permitted an event — the question that record exists to answer.  The
  designation is therefore a chunked field like the others, with
  `auditReadBasis_reconstructs_designation`; structurally excluding
  integrator-authored entries from readable trails was the alternative and is
  worse, since those are exactly the entries a monitor most needs to see.
- The value fields — `srcDomain.id`, `dstDomain.id`, `targetObject.val`,
  `timestamp`, and (per below) the authorization basis's designation — are
  unbounded `Nat` in the model (`SecurityDomain.id : Nat`, `ObjId.val : Nat`),
  so each is read through a 32-bit chunk protocol: `AuditReadOp.field w
  chunkIndex` plus `fieldChunkCount w`.
- **The chunk coordinates are themselves single words, so "total for any `Nat`"
  was false** — a value needing 2^64 chunks cannot have its own count returned
  in one word, nor every chunk index named through the `UInt64` ABI.  Chasing that with a cursor protocol would need
  per-caller state, which §3.3's other half has just finished showing is not
  constructible.  So the export is **structurally bounded** instead:
  `maxAuditFieldChunks` caps the exported width and the reader **fails closed**
  with `.auditFieldTooLarge` above it.  `auditReadField_reconstructs` then holds
  unconditionally on the values the reader accepts, which is the honest shape —
  a total theorem about a bounded domain rather than a false theorem about an
  unbounded one.  The cap is **arithmetic, not a hope**, which matters because
  the SM9.A.1a epoch is an unbounded monotone `Nat` that every drain advances —
  so "bounded in practice" is not available for timestamps the way it is for
  object ids.  `maxAuditFieldChunks = 4` gives 128 bits: reaching it needs 2^128
  drains, and at one drain per nanosecond that is ~10^22 years.
  `auditFieldBound_unreachable_in_kernel` states that as the concrete inequality
  (`maxDeclassificationAuditEntries` + total drains < 2^128) rather than as a
  claim about typical use, and the reader still **fails closed** above it, so the
  worst case is a refused read and never a silently truncated one.
- `auditReadField_reconstructs` (§11) is the losslessness theorem: folding a
  field's chunks recovers the value exactly.

A fixed two-chunk (low/high) design was drafted and is **wrong**: two 32-bit
chunks bound a field at 2^64, so values differing above bit 63 produce identical
chunks — it moves the truncation point rather than removing it — and it left the
two domain fields as single words while the surrounding prose called the design
lossless.  `auditReadWord_fits_payload` was the **ABI-safety** half of that draft (every
returned word `< 2^63`, so the old `encodeOk` was the identity on it); WS-RA
retires the encoding and the theorem with it — a 32-bit chunk fits any word
trivially now — but the lesson stands: proving each fragment survives the
boundary says nothing about whether the record can be reconstructed from the
fragments, and conflating the two is what made the two-chunk design look
adequate.

**`status` is chunked too, for the same reason one field over.**  A draft fixed
the record fields and left `status` packing the visible length *and* the drain
generation into one word, which aliases once the monotone generation wraps.
The obvious repair — chunk `status` too — was drafted and is **worse**, and
the reason is instructive: a multi-call read is not atomic, so a drain landing
between two chunk calls yields a reconstructed generation assembled from two
different states, corresponding to no generation that ever existed.  Chunking
traded *aliasing after ~2^55 drains* for *tearing on the very first one*.

`status` therefore returns in **one call**, with both components structurally
bounded: the visible length is bounded by `maxDeclassificationAuditEntries`
(256, so 9 bits) and the generation takes the remaining payload, with a
**stated** `noGenerationWrap` premise on the retry theorem rather than a silent
assumption.  `auditReadStatus_atomic` is the property chunking cannot have.  A
premise that is written down is the honest form of a bound that cannot be made
unconditional.

**Two classes of reader, and what each is promised.**  Raised partly here and
partly in review, and they resolve together.  A `DeclassificationEvent`'s
timestamp is its **global** position (§3.4's `epoch + index`), so exporting it to
a partial reader tells that reader how many entries preceded the one it can see —
hidden ones included.  That is §3.7(b) violated on the trail, exactly parallel to
the refusal counters, and it is **pre-existing in SM8's design** rather than
introduced by the epoch (the old `log.length` producer counted hidden entries
just as well); §3.7 is what turns it from an inheritance into an obligation.

But the first fix — export view-local indices to everyone — broke something else:
the taint table and the causal detector identify predecessors by the *global*
identifier, so after a drain a **fully-dominating monitor** could no longer
correlate a later event with an archived predecessor.  "Nothing is lost because a
monitor dominates" was wrong: the monitor could still see the entries, but not
their stable identities.

So the protocol distinguishes the two readers explicitly:

| | Partial reader | Fully-dominating monitor |
|---|---|---|
| Entry identity | **view-local index** — reveals nothing about hidden entries | **global timestamp** — stable across drains, so archived predecessors correlate |
| `status` generation | none; a view change is detected from the visible length, fail-closed | the **global epoch**, which it may see because it holds the configured monitor clearance (§3.4) — *not* because it dominates the rows that happen to survive |
| Retry guarantee | none promised | `auditRead_stable_under_append` under `noGenerationWrap` |

`auditReadIndex_is_view_local`, `auditRead_hides_global_position` and
`dominatingReader_sees_global_identity` are the three; the partial reader's lack
of a retry guarantee is stated rather than papered over, because a partial reader
is a monitoring convenience and the trail's consumer of record is the monitor.

**This also removes a mount that could not exist.**  An observer-scoped drain
generation was specified with no state to hold it — and per-label state is not
constructible, since `SecurityDomain.id` is an unbounded `Nat`, so there is no
finite family of readers to key a `Vector` by.  With the generation exposed only
to the configured monitor it *is* the global epoch, already mounted by SM9.A.1a,
and no per-observer structure is needed.  `observerScopedGeneration_not_mountable`
records why the earlier design was not merely unbuilt but unbuildable.

**Indexed read.**  `ipcBufferReadMr` (`Architecture/IpcBufferRead.lean`) does
page-granular translation and a write mirror is feasible (`writeUInt64` in
`Architecture/VSpaceARMv8.lean`) — but it would add a **new kernel→user memory
write path** to the trusted computing base, and note that `ipcBufferReadMr`
ignores `PagePermissions` entirely, which a write path must not.  A monitor
draining a 256-entry trail does not need the throughput.  Recorded as a
deliberate non-goal, revisitable if throughput ever demands it.

Two new `SyscallId`s, not one, so authority stays per-operation
(`syscallRequiredRight` is keyed on `SyscallId`):

| Syscall | Capability target | Right | `msgRegs` | Returns in `x0` |
|---|---|---|---|---|
| `.auditRead` | `.auditTrail` | `.read` | `[op, index, word]` | selected word, or an encoded error |
| `.auditDrain` | `.auditTrail` | `.write` | `[count]` | new visible length |

**The right is the second gate, never the only one.**  `syscallLookupCap`
(`API.lean`) checks `cap.hasRight gate.requiredRight` and **nothing about
`cap.target`** — so "requires `.read`" would make the audit reader available to
any thread holding any readable capability, which in practice is every thread
(its own TCB suffices).  That is precisely the confused deputy the project closed
at **v0.32.97**, where `syscallLookupCap` *"verified only that the caller held a
capability carrying the required right, never that the capability's target
matched the operand"* and a thread holding only a writable capability to its own
TCB unmapped a page in a different address space.  The fix there was
`vspaceCapAuthorizesAsid`; the fix here is the same shape and cheaper, because
the trail is a singleton with no operand to bind against:

- A new `CapTarget` variant **`.auditTrail`** (SM9.A.9 owns the constructor and
  its ABI, lock-set and frozen-ops consequences).
- `extractAuditAuthority : Capability → Except KernelError Unit`, binding the
  target in the shape `extractReplyId` already uses for `.replyCap` — so
  authority comes from *holding an audit capability*, not from holding any
  readable one.
- Rights stay as a second gate: `.read` for the reader, `.write` for the drain,
  so a monitoring deployment can hand out a read-only audit capability that
  cannot drain.

Because the capability is minted only where the boot/CSpace layer chooses to
mint it, an unconfigured deployment has no audit reader at all — the same
deny-by-default posture `LabelingContext.declassificationPolicy` already has.
Registered in §8 as a risk row naming the bug class, so a later cut cannot
quietly re-introduce a rights-only gate.

`.auditRead` sub-operations are enumerated **as data**, each naming the
`ReadableStructure` it reads (§3.7's fusion, not a bare `mem_all` list): `status` (visible length + the observer-scoped drain generation),
`fieldChunkCount w`, and `field w chunkIndex` for w ∈ {srcDomain, dstDomain,
targetObject, timestamp, core⊕kernelIssued} — the four unbounded fields read
through the chunk protocol above, `core⊕kernelIssued` in one word because both
components are structurally bounded (`CoreId` is a `Fin numCores`, the trust bit
is a `Bool`).

**Concurrency contract.**  The trail is append-only and drain removes a prefix,
so an index is stable under concurrent *append* and shifts only under concurrent
*drain*.  The `drainGeneration` in `status` lets a reader bracket its reads and
retry.  The kernel stays simple; the protocol gets a theorem.

**`drainGeneration` is observer-scoped, not global.**  A single global counter
incremented by every drain is itself a channel: a monitor cleared for `high`
drains entries no `low` reader can see, and every low reader's `status` moves in
response — a one-bit signal per drain from the dominating subject to every
subject in the system, out of the very boundary this phase polices.  The token
must therefore change only when *this reader's own visible indexing* changes,
which by construction is only when an entry the reader can see is removed.
Stated as `auditReadStatus_generation_observer_scoped` (§11), with the negative
that a global counter is refutable — otherwise the natural implementation is the
leaky one and nothing catches it.

### 3.4 Reader flow argument: a re-indexed, clearance-filtered view

Template in tree: `auditLogOnCore` (`DeclassificationPerCore.lean`) is a
`List.filter` with `auditLogOnCore_sublist`.

- `auditLogVisibleTo ctx L` keeps entries whose `srcDomain` the reader dominates.
- The view is **re-indexed** — a filtered sublist, not a sparse global index — so
  the *count* of hidden entries cannot leak through index gaps.
- Reader clearance is `ctx.threadLabelOf callerTid`; no new policy field.
- **Drain** is authorized only for a caller whose clearance dominates **every**
  recorded `srcDomain`.  A partially-cleared reader may read its filtered view
  but may not drain at all.

**Why drain requires full dominance.**  An earlier draft let any reader drain
"the longest prefix all of whose entries it can see", which leaks: on a trail
`[A, H, B]` where the reader sees `A` and `B` but not `H`, the drain stops after
one entry, and the reader learns that entry 2 is invisible — the *position* of a
hidden entry, which is what re-indexing exists to hide.  Worse, the visible
length after the drain then depends on how many hidden entries sit between the
visible ones, so repeated drains enumerate the hidden layout.  Requiring full
dominance removes the case entirely: either the caller sees the whole trail and
drains all of it, or it drains nothing.  This is also the shape SM8's own
registered follow-on described — *"confined to a domain dominating every recorded
`srcDomain`"* — so it is a return to the registered design rather than a new
restriction.

**But "dominates every recorded domain" must not be computed from the records.**
§3.2 established this for the refusal ledger, where the ring evicts while its
counters do not; the trail has the same defect through a different door.  Drain a
trail to `[]` and the current-record dominance predicate becomes **vacuously
true** — so a low audit-capability holder is then classified as a fully
dominating monitor and reads the global epoch, which counts the very entries the
drain removed.  A predicate over rows that drains delete cannot gate access to a
quantity that drains preserve.

So there is **one privileged-reader gate in this phase**, not two: the configured
`LabelingContext.auditMonitorClearance`.  Drain, the refusal ledger (§3.2),
global-identity access (§3.3) and `predecessorTags` (§3.6) all key off it, and
none of them off the trail's or the ledger's current contents.
`auditMonitorGate_is_configuration_derived` and
`auditMonitorGate_records_derived_unsound` (the drained-to-empty counterexample)
are the pair, stated once and cited by all four consumers rather than
re-established at each.

**Drain needs a persistent timestamp epoch, and this is a change to landed SM8
code.**  `declassifyStoreOnCore` assigns `timestamp := log.length`
(`Declassification.lean`), and `declassificationAuditLogWellFormed_iff` says a
well-formed trail's timestamps are *exactly its indices*, anchored at 0.  Removing
a prefix breaks both halves: the surviving timestamps run `k, k+1, …` so the
predicate fails, and — the sharper problem — the shortened log's `length` is now
`k` less, so the **next append reuses a timestamp still present in the trail**
(drain 1 from `[0,1,2]`, append, and the new entry is timestamp `2` alongside the
old one).  That falsifies `declassificationAuditLog_timestamp_identifies_event`
in substance, not merely in its hypothesis, and breaks
`declassificationChainLinked`'s strictly-increasing conjunct along with it.

So SM9.A.1a adds `SystemState.declassificationAuditEpoch` — entries drained so
far — with `timestamp := epoch + log.length` and drain advancing the epoch by the
number removed, so timestamps are never reused and never decrease.  The
generalisation is cheaper than it sounds because **the general lemma is already
in the tree**: `auditTimestampsFrom` takes a `start` parameter and
`auditTimestampsFrom_iff` is stated over it, so `declassificationAuditLogWellFormed`
becomes the `start = 0` boot instance and the two identification theorems
generalise rather than move.  `DeclassificationPerCore.lean`'s claim that *"a
running system's trail is well-formed throughout"* is corrected to name the
epoch, since with drain it is false as written.

**The trade-off, recorded rather than buried.**  A deployment whose monitor does
not dominate every recorded domain **cannot drain**, and the 256-entry cliff
returns for it.  That is the correct conservative default — a leaky drain is
worse than an un-drainable trail, and the deployment shape that fixes the cliff
(one fully-cleared monitor) is exactly the shape a trail like this is for — but
it is a real constraint on operators and belongs in the acceptance gate (§9),
not in a footnote.

**Why this is not an eighth covert channel.**  Registering CC-8 costs nine steps
(a `CovertChannelId` constructor + `all` + four total-match tables + a witness
theorem + five numeric theorems + Tier-3 anchors + the
`smp_information_flow.expected` fixture).  It is not owed: a covert channel is an
*unauthorized* information path.  The reader is capability-gated, right-gated and
clearance-filtered — an authorized, audited read.  What it *is* owed is an
observation relation that describes what an audit reader can see, which the next
subsection supplies.

### 3.4a Adding a reader changes what is observable

SM8 could keep the trail out of `ObservableState` for a reason it stated
plainly: nothing could read it, so `declassificationAuditLog_write_preserves_projection`
is `rfl`.  **SM9.A makes it readable, and that changes the observation relation.**

The consequence is concrete and was nearly missed.  An earlier draft of SM9.A.4
read *"two states low-equivalent at `L` give identical visible views"*.  That
statement is **false**: `lowEquivalent` compares `ObservableState`, which does
not contain the trail, so two low-equivalent states can differ by an audit entry
whose `srcDomain` flows to `L` — and their `auditLogVisibleTo ctx L` results then
differ.  The lemma cannot be proved because it is not true, and shipping it as a
sub-task would have surfaced mid-implementation.

Two ways to make the relation match the reader:

- **(a) Extend `ObservableState`** with the clearance-filtered trail as a
  fourteenth component.  Honest — it *is* now observable — but the SM8.A field
  partition is a bijection with `ObservableState.ofFragments_eta`, deliberately
  built so a fourteenth field is a compile error, and every SM8.B NI theorem
  moves with it.
- **(b) A separate `auditObservationalEquivalence ctx L s s'`**, conjoining
  `lowEquivalent` with agreement on `auditLogVisibleTo ctx L`.  Contained; every
  SM8 theorem stands unchanged; and the flow argument is stated in the relation
  that actually describes an audit reader's observations rather than in one that
  describes a subject with no reader.

**Decision: (b).**  `ObservableState` stays a thirteen-component partition and
its tripwire keeps working.  (a) becomes the right move only if a later phase
adds a *second* readable-but-unprojected structure — at that point one relation
per reader stops scaling and the partition should absorb them.  Recorded here so
that decision is made on evidence rather than rediscovered.

Either way the work is a relation plus its congruence lemmas rather than a single
theorem, which is why the old SM9.A.4 splits into **SM9.A.4a** (the relation) and
**SM9.A.4b** (the flow argument over it), why `.4a` is **XL**, and why SM9.A
ships as two PRs (§4).

### 3.5 Declassification-relative non-interference

A data-carrying declassification is the first **deliberately visible** flow in
the tree.  Every existing NI theorem says a high write is invisible to low; this
one is not, by design.  SM9.C's real content is therefore *intransitive*
non-interference: every low-observable difference lies inside the **authorized
effect footprint**, **and** every such difference is recorded in the trail.  Both
halves are load-bearing — the first alone would permit an unrecorded downgrade,
the second alone would permit an unbounded one.

**The footprint is three things, not one.**  An earlier draft said the difference
is "confined to the declassified target", which under-states what the live path
writes.  `notificationSignalOnCore` (`IPC/CrossCore/NotificationSignal.lean`) on
the waiter path writes the notification object, **and** the delivered waiter's
TCB (via `storeTcbIpcStateAndMessage`), **and** the waiter's home-core scheduler
slots (via `wakeThread` — run queue, and the SGI when the home core is remote).
A confinement theorem naming only the notification would be false of the
transition it is about, so the footprint is:

1. the notification object (the badge that crosses the boundary),
2. the delivered waiter's TCB, and
3. the waiter's home-core scheduler slots.

**A footprint is not an authorization, and conflating them re-opens a closed
leak.**  Naming the waiter TCB in the effect footprint says *where the writes
land*; it says nothing about whether that second sink is *permitted*.  The live
`notificationSignalBoundCrossCoreDispatchChecked` already gates **two** flows —
`signaler → notification` and then `notification → receiver` — and the second was
added at **v0.31.73 (review #3)** for exactly this reason: without it a signal
authorized to the notification delivers the badge onward into a low bound TCB.
A declassifying signal gated only by `declassificationDecision` on the
notification would re-introduce that leak in the declassifying variant, with a
*stronger* authority behind it.

So SM9.C gates the **resolved destination** as well: the receiver (bound TCB or
head waiter, whichever the transition actually delivers to) must be authorized to
receive from the notification — by the ordinary flow check when that hop is not a
downgrade, or by its own `declassificationDecision` when it is — and the audit
event records the **actual destination**, not merely the notification.
`declassifiedSignal_gates_resolved_receiver` and
`declassifiedSignal_audits_actual_destination` are the two, with
`footprint_does_not_authorize` keeping the distinction on the record.

**Two authorizations need two records.**  Gating both hops immediately raises
what a single event can honestly say.  On a `high → mid` notification followed by
a `mid → low` receiver, one event naming only the final destination must either
drop the first downgrade or collapse two different domain pairs — and two
potentially different authorization bases — into a direct `high → low` edge that
no policy actually authorized.  Either way the trail misrepresents what happened,
and the causal detector inherits the misrepresentation.  So the transition emits
**one event per authorized downgrade**, in hop order, sharing the subject:
`declassifiedSignal_audits_each_hop` and `declassifiedSignal_no_invented_edge`
(no recorded event names a domain pair no decision returned).

**And the second hop's `srcDomain` is not its actor's domain.**  SM8.C's
`attributionFromRunningSubject` rule defines an event's source domain as the
*running subject's* domain, which is exactly right while one event describes one
subject's downgrade.  Per-hop events break that: on `high → mid` then
`mid → low` both events are performed by the same **high** executing subject, so
recording the second event's source as `mid` under that rule would assert the
high subject *is* mid — a false attribution written into the audit trail by the
fix meant to make it honest.

So the event separates the two identities it had conflated:

- **`actorSubject` / `actorDomain`** — who performed the downgrade, read off the
  running subject.  `attributionFromRunningSubject` is restated over *this*, and
  becomes true of every event rather than only of single-hop ones.
- **`srcDomain` / `dstDomain`** — the endpoints of the *flow* this hop
  authorized, which for hop 2 are the notification's and the receiver's.

For a single-hop downgrade the two coincide (`actorDomain = srcDomain`), which is
why the conflation went unnoticed; `secondHop_actor_differs_from_flowSource` is
the witness that they genuinely separate, and
`attributionFromRunningSubject_over_actor` the restated rule.

**They cannot share one tag snapshot, though** — and a first draft said they
should, which is self-defeating.  Hop 2 is causally downstream of hop 1 *within
the same transition*, but a snapshot taken before the transition cannot contain
hop 1's timestamp, because that timestamp is allocated by recording hop 1.  So
D.14 would reject the very two-hop chain this design exists to record.  The
second event's `predecessorTags` are therefore the pre-transition snapshot
**extended with hop 1's freshly allocated timestamp**
(`secondHopEvent_names_firstHop`), and SM9.E.2a covers a two-downgrade delivery
as its own case rather than only the cross-transition chain.  A composite single record was the alternative and is worse —
it invents a fourth record shape for the detector, the reader's chunk protocol and
the fixtures, where per-hop events are the shape all three already handle.  Both are
SM9.C.1 obligations, not SM9.C.5 ones: the footprint work stays where it is and
does not grow to cover them.

Stated as `declassificationEffectFootprint` in SM9.C.5, alongside the write set
and `observableSlotsConfinedToCores` that already have to name the same cores —
so the footprint is defined once and the NI theorem and the confinement proof
read the same definition rather than two copies of it (the failure mode
`retypeIcacheOp_cleans_scrub_extent` hit at v0.32.101 and the splice arm hit
again at v0.33.16).  SM9.C.6 then carries the load-bearing negative that a
difference **outside** the footprint is refutable, which is what stops the
theorem from being satisfiable by a footprint that swallows the whole state.

### 3.6 Provenance: the registered wording was right

SM8 registered follow-on #4 as needing "a provenance relation on the object
store" — recording, for every IPC, which object's content flowed into which.  A
draft of this section called that over-scoped and narrowed SM9.D to
declassification **edges** (source object → target object, per downgrade).  That
narrowing does not work, and the reason is worth stating because it is not
obvious.

**Declassification-only edges cannot link consecutive hops.**  Take the chain the
detector exists to catch, on the very path SM9.C builds: downgrade #1 writes a
badge into notification `N`; an **ordinary**, non-declassifying delivery moves
that badge from `N` into waiter TCB `T`; the thread owning `T` then performs
downgrade #2.  Hop 1's target is `N`, hop 2's input is `T`, and *no
declassification edge relates them* — the link was forged by an ordinary IPC.  So
an edge-only detector has exactly two options and both are wrong: keep matching
on domains alone (the false positives SM9.D claims to remove survive untouched)
or require hop 2's source to be hop 1's target (a **false negative** on the real
chain above — strictly worse than the honest over-approximation SM8 shipped).

Causality therefore has to follow the content, which means propagating a tag
through ordinary IPC delivery — SM8's registered wording, expressed as taint
rather than as an edge relation.  It is genuinely large, and it is sized as such
below (SM9.D 5 → 18 sub-tasks; the phase 6-9 → 12-16 weeks).  What it buys is a
detector that is *sound* rather than one that looks causal and is not.

**Shape** (details in §4):

- Taint is a **bounded set of event timestamps** — the SM9.A.1a epoch makes those
  identifiers stable across drains, which is what lets a tag outlive the entry
  that created it.
- It lives in a **side table** `SystemState.declassificationTaint`, not a field
  on all seven object kinds: the audit trail's own precedent, and it leaves
  object well-formedness and the frozen mirror untouched.
- Propagation sites are policed by a gate **whose domain is exhaustive of what it
  polices** — and getting there took three attempts, each of which is worth
  recording because the first two look right.

  A hand-maintained `ContentFlowSite.all` with `mem_all` fails for the reason
  §3.7 gives for `ReadableStructure`: `mem_all` proves the new type's own
  constructors are listed, while a content-moving transition can simply never
  acquire one.  Replacing it with a **total function**
  `KernelOperation → ContentFlowClass` looks like the §3.7 fix applied — but it
  is not, because `KernelOperation` **has no `ipcUnwrapCaps` constructor**, and
  SM9.D.11 names that live transition as a propagation site.  The function is
  total and the propagation is still missing.  *Totality over the wrong domain
  proves nothing about the right one*, which is the sharper form of the lesson
  and the one §3.7 now states.

  The honest diagnosis: propagation sites are **sub-transitions** reachable from
  live dispatch arms, and no type in the tree enumerates those.  `SyscallId` is
  exhaustive of *arms*, `KernelOperation` of *NI steps*; neither is exhaustive of
  the call graph beneath them.  So the gate is a **call-graph gate**, in the
  idiom `scripts/check_live_arm_per_core_routing.py` already established for
  exactly this shape of obligation: start from the live arms, walk the
  transitive callees, and fail on any that touches the object store's content
  channels without a propagation or frame classification.  `ContentFlowClass`
  stays as the *classification*; what changes is that its completeness is
  established by reach rather than asserted by totality over a convenient type.
  Tier 1, like its sibling, since it needs a built environment — and with a
  `--self-test` that plants a known content-moving callee and requires the gate
  to find it, because a gate that loses its reach fails silently.
- Overflow **saturates upward** to "tainted by everything".  For a detector the
  safe direction is over-approximation — more false positives, never a missed
  chain — and `taintSaturate_over_approximates` states that direction rather than
  leaving it to a comment.
- The taint table is **not readable** by any SM9 syscall, so §3.7 records that it
  owes no equivalence clause *yet* and what a future reader would owe.

**Two things the first draft of this shape got wrong, both found in review.**

*Taint must not outlive the object it describes.*  Keying by `ObjId` and framing
through `storeObject` leaves stale provenance attached across a **retype**:
`lifecycleRetypeObject` commits `storeObject target newObj` at the *same* id
(verified — `RetypeWrappers.lean`), so an object destroyed and re-created keeps
its predecessor's tags, and a later downgrade from the unrelated new object reads
as causally linked to the old one's timestamps.  That is a false positive with
**nothing to do with saturation**, which would have made D.15's "the residual
imprecision is saturation" claim false the day it was written.  So retype
**clears** the target's taint (`retypeClearsTaint`, at the two production
wrappers — the same entry points SM7.D's initiator drain already enumerates),
with `retypedObject_taint_empty` as the property and
`staleTaint_is_not_saturation` keeping the distinction on the record.  Framing
`storeObject` in general stays right: ordinary object writes are exactly where
propagation *sets* taint, so a blanket clear-on-store would erase what D.8–.11
exist to record.

*The detector needs data the event does not carry, and a subject identity is not
enough.*  D.14 checks whether hop 2's **source** object's taint contains hop 1's
timestamp — but the detector runs on the *event list*, and
`DeclassificationEvent` records only `targetObject`, the two domains, the basis,
the timestamp and the core (verified — `AuditRecord.lean`).  Two same-domain
subjects where only one received hop 1's data produce indistinguishable events,
so the predicate is not well-defined from the data the detector has: it must
accept both or reject both.

Adding a `sourceSubject : ObjId` was the first repair and is **insufficient**,
because the taint it points at lives in a *mutable* side table while the events
are a historical record.  Evaluating an old event against current taint is wrong
in both directions: if the subject acquires hop 1's tag *after* hop 2 already
happened, re-reading the table invents a causal link that never existed; and if
that TCB is later retyped — which §3.6 now requires to **clear** its taint — a
genuine historical link silently disappears.  A detector whose verdict on a fixed
pair of events changes with unrelated later activity is not a detector.

So the event carries the causality itself: a **bounded snapshot of the subject's
taint at production time** (`predecessorTags`), taken in the same step that
records the event, plus `sourceSubject` retained for attribution.  The predicate
then reads only the event list, which is what makes it a property of the trail
rather than of the current store — `chainCausal_is_history_local` states exactly
that, and `chainCausal_not_table_derived` keeps the refuted design refuted.  Both
fields change landed SM8 code and ride the §6 mount checklist.

**And the snapshot must not become an export channel.**  `predecessorTags` are
*global* timestamps, including those of events a partial reader cannot see: a
hidden high-source event tags a subject, that subject later produces an event the
partial reader *can* see, and the tags ride out through the reader's chunk
protocol carrying the hidden event's global position.  That defeats both §3.3's
view-local identities and §3.7(b) in one step — the round-4 fix for the mutable
table created an export surface the round-3 index fix had just closed.  So the
tags follow the same two-class rule as identity (§3.3), keyed on the configured
monitor clearance of §3.4: a **monitor** reads them, and every other reader gets
at most an *opaque* causality verdict — a `Bool` computed by the kernel, carrying
no timestamps —
(`predecessorTags_dominating_only`, `partialReader_gets_opaque_causality`).  The
general lesson is now explicit in §3.7: adding a field to a *readable* record is
adding a read channel, and inherits both obligations.

### 3.7 The reader-visibility discipline

§3.4a found that adding a reader changes what is observable, and fixed it *for
the audit trail*.  The refusal ledger is a **second** readable-but-unprojected
structure and inherited both halves of the same problem — absent from the
equivalence, and evicting a low reader's entries on hidden writes.  Patching each
structure as it is noticed is how a third one gets missed, so the obligation is
stated once here and every readable structure is checked against it.

**For each kernel structure a clearance-filtered reader can observe:**

- **(a) Inclusion.**  It appears in the reader's observation relation.  Otherwise
  `auditRead_no_channel` does not cover the API that exposes it: two states
  agreeing on the relation can disagree on what the reader returns.
- **(b) Hidden-write non-interference.**  A write the reader cannot see does not
  change what that reader sees.

Three of the findings this plan has absorbed are the *same violation of (b)*:
prefix drain revealed the positions of hidden entries, a global `drainGeneration`
signalled hidden drains, and a global refusal ring evicted visible entries on
hidden writes.  Reading them as one clause is what makes the pattern visible.

**Mechanised — and the obvious mechanisation is not enough.**  A draft stated
`auditObservationalEquivalence` over a `ReadableStructure.all` list with
`mem_all`, in the `CovertChannelId.all` / `KernelOperation.all` idiom.  That
mechanism is weaker than it looks, and in precisely the way SM8.E's own finding
was weaker than it looked: `mem_all` proves every constructor of a
**hand-maintained** type appears in `all`, and nothing forces a newly mounted
readable field — or a new `AuditReadOp` — to add a constructor at all.  With the
reader operations kept as a *separate* taxonomy, a future structure can be
mounted, exposed through a new read operation, and given neither a
`ReadableStructure` constructor nor an equivalence clause, while `mem_all` keeps
compiling.  A gate that a new structure can simply not join is not a gate.

So the two taxonomies are **fused**: `AuditReadOp` carries the
`ReadableStructure` it reads, so a read operation cannot exist without naming
one, and the equivalence's clauses are a **total function** on
`ReadableStructure` rather than a list to append to.  Then a new readable
structure is a new constructor (forced by the read operation that motivated it),
and a new constructor is a missing case in a total function — a compile error,
not a silent pass.  `auditReadOp_structure_total` and
`auditObservationalEquivalence_clause_total` are the two halves;
`readableStructure_list_gate_insufficient` keeps the weaker `mem_all`-only
design refuted, so it cannot come back as a simplification.

**Current inventory** (SM9.A.4a owns it):

| Structure | (a) inclusion | (b) hidden-write non-interference |
|---|---|---|
| `declassificationAuditLog` | `auditLogVisibleTo ctx L` clause | drain and global identity gated on the configured monitor clearance (§3.4), never on surviving rows |
| `declassificationRefusals` | ledger view clause, gated | readable only under the configured monitor clearance (§3.2, §3.4) |
| `declassificationTaint` (SM9.D) | **not readable** — no clause owed | vacuous while unreadable; a reader added later owes both |

The third row is load-bearing rather than filler: SM9.D mounts a taint table and
deliberately exposes no reader for it, so the discipline records *why* it owes
nothing yet and what a future reader would owe.

**And the sharper form, which cost a third.**  "Use a total function instead of a
list" is not the lesson.  The content-flow gate was moved from a list, to
`mem_all` over a hand-maintained type, to a **total function** over
`KernelOperation` — and was *still* not exhaustive of what it polices, because
`KernelOperation` has no `ipcUnwrapCaps` constructor while that transition is a
propagation site.  **Totality over the wrong domain proves nothing about the
right one.**  So the obligation is: name the set the gate is *about*, check that
the domain quantified over is exhaustive of that set, and where no type is —
propagation sites are sub-transitions, and nothing enumerates those — use a
reach-based gate (§3.6) rather than a totality claim that cannot reach.

**A corollary that cost two rounds to learn.**  Adding a field to an *already
readable* record is adding a read channel, and inherits both obligations exactly
as a new structure does.  `predecessorTags` (§3.6) is the case: a field added to
fix a causality defect carried hidden events' global timestamps straight through
the reader that §3.3 had just been narrowed to hide them from.  So the inventory
is keyed by **field**, not by structure, and a field whose content is derived
from hidden state is dominating-reader-only or exported opaquely.

## 4. Detailed sub-task breakdown

Sizes: **T** trivial, **S** small, **M** medium, **L** large, **XL** very large.

### SM9.A — The audit trail reader (15 sub-tasks) — **LANDED**

Ships as **two PRs' worth of work at minimum**: SM9.A.1-.A.5 (the pure reader
plus its observation relation) and SM9.A.6-.A.13 (the ABI, the live arms and
their registries).  SM9.A.4a alone is a relation with congruence lemmas — see
§3.4a — which is why the split is structural rather than a convenience.

**Landing record.**  All fifteen sub-tasks landed in one cut.  The pure reader
is the production leaf `InformationFlow/AuditRead.lean` (131 declarations,
axiom-clean), placed **below** the projection layer so the live syscall arms
consume it without pulling the SM8.A/B non-interference closure into the
dispatch path — which is why `auditDrain_preserves_projection{,OnCore}` and the
observation relation live in the staged `DeclassificationPerCore.lean` instead.
Three design points moved during implementation, each because the drafted form
was not available:

1. **`auditMonitorClearanceIsTop` is unsatisfiable under the live lift.**  The
   plan's §3.4 gate reads "∀ domain, `canFlow d m`", but `liftLegacyContext`'s
   `legacyLattice` (PR #863) admits an unembedded `SecurityDomain` only to
   itself, so no clearance is a top and the gate could never be discharged for
   a real deployment.  It is kept (it is the right statement where a policy has
   a top), and the **satisfiable** obligation `auditMonitorDominatesSubjects` —
   ∀ *thread*, the monitor dominates that thread's domain — is what
   `auditDrain_requires_full_dominance_of_subjects` consumes, bridged by
   `auditTrailSourcesFromLabeling` (every recorded source is some thread's
   domain: established by the producer, preserved by `drop`).  Both remain
   configuration-derived, and the source predicate becomes *more* true as
   entries vanish, so unlike a records-derived gate it cannot age.
2. **The chunk protocol needed a fail-closed width.**  §3.3's "total for any
   `Nat`" is not available, because the chunk *coordinates* are themselves
   single words: `maxAuditFieldChunks = 4` with `KernelError.auditFieldTooLarge`
   is the fail-closed ceiling, and `auditFieldBound_unreachable_in_kernel` is
   the arithmetic that the ceiling is not reachable in practice.
3. **The observation relation compares the raw filtered view plus the gated
   epoch**, per §3.4a option (b), rather than the exported observations — which
   keeps `auditRead_no_channel` a substantive theorem rather than a definitional
   one.  The producer congruence needs `hSameEvent`, because a global timestamp
   differs across states with different hidden histories; that a partial reader
   still cannot tell is `auditRead_hides_global_position`.

**Acceptance discharged**: `tests/SmpInformationFlowSuite.lean` §9.8 runs the
gate's own scenario for effect on the live transition — fill the trail to
`maxDeclassificationAuditEntries` through real authorized downgrades, observe
`.auditLogCapacityExceeded`, read the status word and a field, drain, declassify
again — with the post-drain timestamp provably fresh and the pre-epoch collision
exhibited as the load-bearing negative.  620 assertions / 78 groups overall.

**Audit cut (same branch).**  A code-first audit of the landing found no
security defect in any reachable state and no false theorem, and closed seven
findings — each by code where code was the honest direction: the drain's
boundary-narrowing witnesses (`auditDrain_returned_length_le` / `_fits` /
`_toUInt64_lossless`); the retry bracket lifted to the `UInt64` words a caller
actually holds (`auditReadFromCore_bracketed_detects_drain_u64`, with the
positive dual demonstrated at runtime); the acceptance witness strengthened to
the four-fact conjunction its docstring promised (the mint-unforgeability
conjunct discharged by `mintDerivedCap_no_audit_forgery`); a genuine `u128`
overflow in `sele4n-sys`'s `audit_fold_chunks` on malformed input, closed by a
radix guard with a boundary-pinning regression witness; the RA.D.1 wrapper
sweep given a completeness tripwire over `SyscallId::COUNT` so the next syscall
cannot skip it silently; the reader's fail-closed arms witnessed at runtime
(the 2^128 field bound through `auditReadWord`, the chunk-past-width refusal,
the live 2^64 guard refusing rather than wrapping); and two docstrings
corrected in the direction the mathematics forces.

**PR #870 review cut.**  Three Codex findings, all closed by code.  P1: the
dominance obligation was an unused hypothesis — the live arms now consume
`validatedAuditMonitorClearance` (a non-dominating clearance validates to
`none`; decidable because the live context's subject domains are the four
embedded labels), and the drain gains the `auditDrainViewComplete` destruction
guard, refusing any caller that cannot see the whole trail — so the §3.4
operator obligation became a machine-checked property of the configuration and
the misconfigured deployment fails closed at two independent layers.  P2s: the
`sele4n-sys` byte extractor returns `Option<u8>` (the masked shift aliased
`k = 8` onto `k = 0` in release builds), and the enforcement boundary's
`.auditRead` entry names the live `auditReadFromCore` rather than the inner
caller-supplied-domain query.

**PR #870 round-2 cut (v0.33.44).**  One further Codex finding, valid: the
"no audit reader by default" claim was silent about capability provisioning —
with `auditMonitorClearance = none` but a boot-provisioned readable
`.auditTrail` capability, the live `.auditRead` served that capability a
partial-reader view, so the claim was false in exactly the deployment shape
that provisions one (the acceptance witness's capability conjunct covered only
an ordinary `.object` shape).  Closed by making the claim true:
`auditReadFromCore` opens with a configuration gate — no validated monitor
clearance ⇒ `.illegalAuthority` before any subject is resolved
(`auditRead_unconfigured_denied`; `misconfiguredDeployment_cannot_read`) — the
same error as the drain's monitor gate, so refusal causes stay
indistinguishable, and partial readers are unchanged in *configured*
deployments.  The validated clearance is thereby the facility's single on/off
switch — the SM9.B "single configured privileged-reader gate" direction
realised on the read side.  At the arm:
`dispatchWithCapChecked_auditRead_default_denied` and the universal
`unconfiguredDeployment_audit_never_succeeds` (no capability whatsoever makes
an audit syscall succeed unconfigured), now the acceptance witness's first
conjunct.  `auditRead_gates_are_three` → `auditRead_gates_are_four`;
`SyscallReturnAbiSuite` §10f is the full-ABI witness.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.A.1 | `auditLogVisibleTo ctx L` + `_sublist` / `_reindexed` / `_length_le`; the no-gap-leak theorem (the visible view is a function of the reader's clearance alone) | new production leaf `InformationFlow/AuditRead.lean` | M |
| SM9.A.1a | **The persistent timestamp epoch** (§3.4) — `SystemState.declassificationAuditEpoch`, `timestamp := epoch + log.length`, well-formedness generalised to `auditTimestampsFrom epoch log` (the `start`-parameterised lemma already exists) with the 0-anchored form as the boot instance; both identification theorems generalised; the three `_preserves_wellFormed` theorems restated; full §6 mount carriage (freeze required field, `OffSchedulerAgrees`, four boot frames, `storeObject` frame, `…_write_preserves_projection`); the corrected "well-formed throughout" contract.  **Sequenced before SM9.A.3 — drain is unsound without it** | `Model/State.lean`, `Model/{FrozenState,FreezeProofs}.lean`, `Platform/Boot.lean`, `InformationFlow/{Declassification,DeclassificationPerCore}.lean` | L |
| SM9.A.2 | `AuditReadOp` — **fused with `ReadableStructure`** (§3.7: each operation names the structure it reads) + `all` / `mem_all` / `all_nodup` + `auditReadOp_structure_total`; the §3.3 **arbitrary-length chunk protocol** (`fieldChunkCount w`, `field w chunkIndex`) over all four unbounded fields **and over the basis designation** (exporting the trust bit alone collapses every `integratorOverride`); `maxAuditFieldChunks` with fail-closed `.auditFieldTooLarge`, since the chunk *coordinates* are themselves single words and "total for any `Nat`" was false; `auditReadField_reconstructs` (unconditional on the accepted domain) + `auditReadBasis_reconstructs_designation` (`auditReadWord_fits_payload` retired with the bit-63 encoding — WS-RA v0.33.37, §3.3); **single-call `status`** with both components structurally bounded + `auditReadStatus_atomic` (chunking `status` traded aliasing for tearing on the first interleaved drain); the **two reader classes** — `auditReadIndex_is_view_local` and `auditRead_hides_global_position` for a partial reader, `dominatingReader_sees_global_identity` so a monitor can still correlate across drains, plus `observerScopedGeneration_not_mountable` | same | XL |
| SM9.A.3 | `auditDrainVisiblePrefix` under the §3.4 dominance gate, advancing the SM9.A.1a epoch; `auditDrain_requires_full_dominance`, `_preserves_auditLogBounded`, `_preserves_wellFormed_at_epoch`, `_monotone_generation`, `_monotone_epoch`, `_fully_clears_for_dominating_reader`, and the negative that a partially-cleared caller drains nothing | same | M |
| SM9.A.4a | **`auditObservationalEquivalence ctx L`** (§3.4a option b, §3.7 discipline): the clause set is a **total function on `ReadableStructure`**, not a list — a `mem_all` over a hand-maintained type cannot force a new structure to join it (`readableStructure_list_gate_insufficient` refutes that design), whereas a missing case in a total function is a compile error; `auditObservationalEquivalence_clause_total`; clauses for the trail **and** the refusal ledger; reflexivity / symmetry / transitivity; the congruence lemmas carrying it through every writer of a readable structure; the negative that plain `lowEquivalent` does **not** imply equal visible views | `InformationFlow/DeclassificationPerCore.lean` (staged) | XL |
| SM9.A.4b | The flow argument over that relation: the reader is a function of the visible view alone, so it opens no channel; the **not-CC-8** argument stated once | same | L |
| SM9.A.5 | `auditRead_stable_under_append` + the reader retry protocol as a theorem | `InformationFlow/AuditRead.lean` | S |
| SM9.A.6 | ABI, Lean half: `SyscallId.auditRead`/`.auditDrain`, count 31→33, `toNat`/`ofNat?`/`ToString`/`all` + both `toNat_ofNat` match arms | `Model/Object/Types.lean` | M |
| SM9.A.7 | ABI, Rust half: both mirrors + conformance roundtrips + boundary test | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/tests/conformance.rs` | M |
| SM9.A.8 | `sele4n-sys` safe wrappers | `rust/sele4n-sys/src/audit.rs`, `lib.rs` | S |
| SM9.A.9 | **`CapTarget.auditTrail`** constructor + `extractAuditAuthority` (§3.3): the total-match consequences across `Capability`'s `Repr`/`DecidableEq`/well-formedness, the frozen mirror, and every existing `CapTarget` match; the mint path (which boot/CSpace layer creates one); the negative that a non-`.auditTrail` capability carrying `.read` is rejected, and the acceptance witness that an unconfigured deployment has **no** audit reader | `Model/Object/{Types,Structures}.lean`, `Model/FrozenState.lean`, `Platform/Boot.lean` | XL |
| SM9.A.10 | Live arms in `dispatchWithCapChecked` gated on `extractAuditAuthority` **then** `syscallRequiredRight`; **each arm writes its result into the caller's return register** (the selected word for `.auditRead`, the new visible length for `.auditDrain`) via WS-RA's `writeReturnFrameToTcb` — without which the reader computes correctly and hands back the caller's own preloaded `x0`; unchecked arms fail closed; `syscallDelegates_auditRead` / `_auditDrain` + an end-to-end `syscallDispatchFromAbi` assertion that the returned word is the *selected* one | `Kernel/API.lean` | XL |
| SM9.A.11 | Enforcement boundary 40→42 canonical, 55→57 per-core; `syscallIdToEnforcementName{,PerCore}`; completeness + class-match re-decided | `Enforcement/Wrappers.lean`, `CovertChannelPerCore.lean` | M |
| SM9.A.12 | Lock sets: `lockSet_auditRead` (universal reads), `lockSet_auditDrain`; `permittedKinds`; inventory counts 103→105; `_size_le` + deadlock aggregate | `Concurrency/Locks/{LockSetTransitions,LockSetForSyscall,LockSetInventory,Deadlock,DeadlockInventory}.lean` | M |
| SM9.A.13 | Frozen-ops classifier arm + count; per-core routing gate registration | `Kernel/FrozenOps/Operations.lean`, `scripts/per_core_routing_aliases.json` | S |

**Acceptance**: a monitor reads every entry it is cleared for and drains the
trail; the 256-entry cliff is gone.

### SM9.B — Refusal auditing (10 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.B.1 | `DeclassificationRefusal` record (core, subject, **source domain resolved at the seam**, syscall, reason class incl. `.auditLogCapacityExceeded`, raw `CPtr`) + `Repr`/`DecidableEq`; `refusalRecord_domain_is_seam_resolved` (the context is an argument, not state, so a later reader cannot reconstruct it) | new leaf `InformationFlow/RefusalRecord.lean` | M |
| SM9.B.2 | `RefusalLedger` (§3.2 shape) + `recordRefusal`; saturation, no-loss, drop-count and ring-wrap theorems; `maxRefusalCount` / `refusalRingSize` constants | same | M |
| SM9.B.3 | Mount `SystemState.declassificationRefusals`: field, `Inhabited` listing, `default_*`, `storeObject_*_eq` | `Model/State.lean` | S |
| SM9.B.4 | Freeze carriage: required `FrozenSystemState` field, `freeze` forwarding, `freeze_preserves_*`, the `apiInvariantBundle_frozenDirectFull` conjunct + bullet | `Model/FrozenState.lean`, `Model/FreezeProofs.lean` | M |
| SM9.B.5 | The six `FrozenSystemState` test literals | `tests/{Ak8Coverage,FrozenOps,IpcBuffer,PriorityManagement,SuspendResume,TwoPhaseArch}Suite.lean` | S |
| SM9.B.6 | `OffSchedulerAgrees` clause + **all six** builders | `IPC/Invariant/LookupCongruence.lean` | M |
| SM9.B.7 | Boot frames ×4 (`applyMachineConfig`, `foldIrqs`, `foldObjects`, `bootFromPlatform`) | `Platform/Boot.lean` | S |
| SM9.B.8 | Information flow: `declassificationRefusals_write_preserves_projection := rfl` **and** `onCore_declassificationRefusals` as the tenth read-set corollary | `InformationFlow/Invariant/Operations.lean`, `ObservableStatePerCore.lean` | S |
| SM9.B.9 | Write at the seam, filtered by the **total** `SyscallId → RefusalSeamClass` classification (§3.1) rather than a hardcoded `.declassify` or a hand-maintained list; `refusalSeamClass_total` + `refusalSeam_list_gate_insufficient`; re-shape `syscallDispatchFromAbi_error_of_syscallEntryChecked_error`; re-prove `_total`; the three security theorems (below) | `Platform/FFI.lean` | L |
| SM9.B.10 | Extend `.auditRead` with refusal sub-operations, gated on the **configured** `LabelingContext.auditClearance` (§3.2) — ring *and* counters, and deliberately **not** on the domains present in the current records, since the ring evicts while the counters are cumulative (`refusalLedger_gate_is_configuration_derived`, with `refusalLedger_records_gate_unsound` keeping the eviction counterexample refuted); the `ReadableStructure` clause + congruences this adds to SM9.A.4a's relation; the negative that an under-cleared caller reads nothing of the ledger; **retire `DeclassificationRuleId.refusalIsUnrecorded`** | `InformationFlow/AuditRead.lean`, `DeclassificationPerCore.lean`, `InformationFlow/Policy.lean` | XL |

**SM9.B.10 retires a registered claim, and must do so properly.**
`DeclassificationRuleId.refusalIsUnrecorded` is data, not prose: arms in `all`,
`evidenceProp`, `declassificationRuleEvidence`, `declassificationRuleEvidenceName`
and `declassificationRuleStatement`, pinned by `declassificationRules_count = 12`
and `declassificationRuleEvidence_distinct`, plus a Tier-3 anchor.  SM9.B makes
its statement **false**.  Follow the SM8.E precedent for
`enforcementBoundaryPerCore_entry_is_new`: retire the constructor, move both
counts, add a Tier-3 *negative* anchor forbidding its return, and replace it with
the property that survives — *refusals are counted and attributed, and still
cannot displace an authorized-downgrade entry*.

**Security constraints, each stated as a theorem:**

- `refusalWrite_declassificationAuditLog_eq` — the ledger is **not** the trail
  and cannot displace an entry in it.  An unprivileged caller appending on
  refusal must not be able to exhaust the 256 authorized-downgrade entries.
- **No distinguishable record of the `auditLogCapacityExceeded` reason.**  A
  reason field a reader can resolve to "the trail is full" re-opens the channel
  `authorizeDeclassificationOnCore_denied_before_capacity` closed.  That theorem
  **and** the suite's existing `NEGATIVE: a policy-refused caller learns nothing
  about trail occupancy` assertion must both still hold — an explicit acceptance
  item, not a hope.
- Outside `ObservableState`, with the clearance gate of SM9.A applying to the
  ledger too.

### SM9.C — Data-carrying declassification (10 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.C.0 | **Prerequisite — the wait path drops the badge.**  `notificationWaitOnCore`'s pending-badge arm clears `pendingBadge`, marks the waiter `.ready` with plain `storeTcbIpcState` (no message), and returns `.ok (some badge)`; both live `.notificationWait` arms in `API.lean` match `(st', .ok _)` and discard it, and the wrapper's type is `Kernel Unit`.  So in the ordinary signal-before-wait ordering the badge is consumed and delivered nowhere — while the waiter-present path delivers via `storeTcbIpcStateAndMessage`.  `FFI.lean`'s own ABI note says `x0` carries *"a badge for `notificationWait`"*, so this is a documented contract the code does not meet.  **SM9.C cannot ship a data-carrying declassification over a path that loses data in one of its two orderings.**  **Closed by WS-RA, not here**: [`SYSCALL_RETURN_ABI_PLAN.md`](SYSCALL_RETURN_ABI_PLAN.md) establishes that the kernel writes *no* return register except a status word, so `tcb.pendingMessage` — where the signal path stores the badge — has no register path either and a local mirror-the-signal-path patch would not deliver anything.  SM9.C is blocked on RA.B.5 | `IPC/CrossCore/NotificationSignal.lean`, `Kernel/API.lean` | L |
| SM9.C.1 | `notificationSignalDeclassified` — the SM6.B signal gated by `declassificationDecision` **and by the resolved destination's own authorization**, emitting **one event per authorized hop** (`declassifiedSignal_audits_each_hop`, `declassifiedSignal_no_invented_edge` — a single record would collapse two domain pairs into a direct edge no policy authorized) (§3.5): the live `notificationSignalBoundCrossCoreDispatchChecked` gates `signaler → notification` *and* `notification → receiver`, the second added at v0.31.73 to stop a badge leak into a low bound TCB, so a declassifying variant gated only on the notification would re-open it with stronger authority behind it.  `declassifiedSignal_gates_resolved_receiver` + `declassifiedSignal_audits_actual_destination` + `footprint_does_not_authorize`; badge delivered, event recording the **actual destination**; error arms fail closed | `IPC/CrossCore/NotificationSignal.lean` | XL |
| SM9.C.2 | Per-core + cross-core forms (`…OnCore`, `…CrossCoreDispatchChecked`), SGI emission, home-core wake | same | L |
| SM9.C.3 | `ipcInvariantFull{,_perCore}` preservation — rides `notificationSignal_preserves_*` plus the audit frame | `IPC/Invariant/PerCoreBundlePreservation.lean` | L |
| SM9.C.4 | `proofLayerInvariantBundle` preservation + `auditLogBounded` carriage | `InformationFlow/Declassification.lean` | M |
| SM9.C.5 | **`declassificationEffectFootprint`** (§3.5: notification ⊕ waiter TCB ⊕ waiter home-core scheduler slots) defined **once** and read by both consumers; lock set + write set + `observableSlotsConfinedToCores`; inventory counts | `Concurrency/Locks/*`, `InformationFlow/NonInterferenceCrossCore.lean` | L |
| SM9.C.6 | **`declassificationRelativeNonInterference`** — both halves (§3.5) over the SM9.C.5 footprint, with two load-bearing negatives: an *unrecorded* difference is refutable, and a difference **outside** the footprint is refutable | `InformationFlow/NonInterferencePerCore.lean` | XL |
| SM9.C.7 | NI inventory growth: `KernelOperation.all` 35→36, `niStepConstructorCoverage` arm, `perCoreConfinementDerived` arm, all three counts + the complement | `InformationFlow/Invariant/Composition.lean`, `NonInterferencePerCore.lean` | M |
| SM9.C.8 | Live arm + ABI: `SyscallId.declassifySignal`, count 33→34, both Rust mirrors, conformance, `sele4n-sys`, enforcement boundary 42→43 / 57→58, lock-set inventory; **and its `RefusalSeamClass` arm (§3.1) supplied**, which the total classification forces as part of adding the syscall, so its refusals reach the SM9.B seam rather than bypassing it | ~14 files (§5) | L |
| SM9.C.9 | `syscallDelegates_declassifySignal`; per-core routing gate; cross-core NI inventory entry | `Kernel/API.lean`, `NonInterferenceCrossCore.lean` | M |

### SM9.D — Causal declassification provenance (19 sub-tasks)

The phase's largest sub-phase, and the reason the calendar estimate moved.  §3.6
records why declassification-only edges cannot do this job.  Sequenced in four
blocks: type and mount (D.1–D.6), the propagation surface (D.7–D.12), the
saturation policy and the event's subject identity (D.13, D.13a), the detector
and its consequences (D.14–D.18).

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.D.1 | `DeclassificationTaint` — a **bounded** set of event timestamps (SM9.A.1a makes them stable across drains) with a `saturated` top, `join`, and a `covers` preorder; join-semilattice laws; no-loss theorems | new production leaf `InformationFlow/Taint.lean` | M |
| SM9.D.2 | Mount `SystemState.declassificationTaint` as a **side table** keyed by `ObjId` (not a field on seven object kinds — the audit-trail precedent); `default_*`; `storeObject_declassificationTaint_eq` (the frame stays right — ordinary object writes are where propagation *sets* taint, so a blanket clear-on-store would erase D.8–.11's work) | `Model/State.lean` | M |
| SM9.D.3 | Freeze carriage: required `FrozenSystemState` field, `freeze` forwarding, `freeze_preserves_*`, the `apiInvariantBundle_frozenDirectFull` conjunct + bullet | `Model/FrozenState.lean`, `Model/FreezeProofs.lean` | M |
| SM9.D.4 | The `FrozenSystemState` test literals (the same six SM9.B.5 touches) | `tests/*Suite.lean` | S |
| SM9.D.5 | `OffSchedulerAgrees` clause + **all six** builders; boot frames ×4 | `IPC/Invariant/LookupCongruence.lean`, `Platform/Boot.lean` | M |
| SM9.D.6 | Information flow: `declassificationTaint_write_preserves_projection := rfl`; `onCore_declassificationTaint`; the §3.7 inventory row recording that it is **not readable** and therefore owes no equivalence clause yet | `InformationFlow/Invariant/Operations.lean`, `ObservableStatePerCore.lean` | M |
| SM9.D.7 | **The content-flow gate** (§3.6) — `ContentFlowClass` as the classification, with completeness established by a **call-graph gate** (`scripts/check_content_flow_coverage.py`, Tier 1, `--self-test` planting a known content-moving callee) rather than by totality over a type that is not exhaustive of the propagation sites: `KernelOperation` has no `ipcUnwrapCaps` constructor while SM9.D.11 names that transition as one, so the total function would be total and the propagation still missing.  The soundness keystone: a missed site is a detector that misses real laundering | `InformationFlow/Taint.lean`, `scripts/check_content_flow_coverage.py` | XL |
| SM9.D.8 | Propagation at IPC send/receive (message registers → receiver TCB), single-core and `…OnCore` | `IPC/Operations/Endpoint.lean`, `IPC/CrossCore/EndpointSend.lean` | L |
| SM9.D.9 | Propagation at call / reply / replyRecv, including the cross-core dispatch wrappers | `IPC/CrossCore/{EndpointCall,EndpointReply}*.lean` | L |
| SM9.D.10 | Propagation at notification signal — **where SM9.C's downgrade originates a tag** — plus the bound-TCB delivery path **and `notificationWaitOnCore`'s pending-badge arm**.  The last is not optional: in the signal-before-wait ordering the tag sits on the notification and the *wait* is what moves the badge to the waiter, so omitting it means the waiter's later downgrade carries no hop 1 and the detector misses §3.6's own downgrade → ordinary delivery → downgrade scenario in one of its two orderings | `IPC/CrossCore/NotificationSignal.lean` | XL |
| SM9.D.11 | Propagation at capability transfer (`ipcUnwrapCaps`) | `IPC/Operations/CapTransfer.lean` | M |
| SM9.D.12 | Taint **frames** for every non-content transition (scheduler, VSpace, cache/TLB), so D.7's completeness is checkable rather than declared — **except retype, which clears** (§3.6): `lifecycleRetypeObject` commits `storeObject target newObj` at the same id, so a framed retype leaves a destroyed object's tags on its replacement.  `retypeClearsTaint` at the two production wrappers (the entry points SM7.D's initiator drain already enumerates) + `retypedObject_taint_empty` + `staleTaint_is_not_saturation`, which keeps D.15's residual-imprecision claim true | ~12 files | XL |
| SM9.D.13 | Saturation: the structural bound, upward-saturating overflow, `taintSaturate_over_approximates` (the safe direction for a detector, stated as a theorem) | `InformationFlow/Taint.lean` | M |
| SM9.D.13a | **`DeclassificationEvent.sourceSubject : ObjId` + `predecessorTags`** (§3.6) — the declassifying thread's TCB *and* a bounded snapshot of its taint at production time, the tags **dominating-reader-only** with an opaque causality verdict for partial readers (`predecessorTags_dominating_only`, `partialReader_gets_opaque_causality`), since the tags are global timestamps of events a partial reader may not see.  The subject alone is insufficient: the taint it names lives in a mutable side table, so re-evaluating a historical event against current taint invents links (tag acquired after the fact) and loses real ones (retype clears it).  `chainCausal_is_history_local` + `chainCausal_not_table_derived`.  A change to landed SM8 code, riding the §6 mount checklist (record type, producer, well-formedness, the reader's chunk protocol, the golden fixtures) | `InformationFlow/AuditRecord.lean`, `Declassification.lean`, `AuditRead.lean` | XL |
| SM9.D.14 | `declassificationChainCausal` — hop 2's **recorded `predecessorTags`** contain hop 1's timestamp — conjoined into `declassificationChainLinked`, read from the event list rather than from the live taint table, so the verdict on a fixed pair of events cannot change with later unrelated activity | `InformationFlow/DeclassificationPerCore.lean` | L |
| SM9.D.15 | **Retire `declassificationChainLinked_is_syntactic`** (now genuinely false) for a soundness theorem on the causal detector; a negative pinning the residual saturation-induced over-approximation, so the remaining imprecision is stated rather than implied absent | same | M |
| SM9.D.16 | `chainLaunders` consumes it; the rule-inventory `evidenceProp` moves with the theorem; counts + Tier-3 anchors incl. the retirement negative | same | M |
| SM9.D.17 | Lock sets and write sets: the propagation writes sit inside existing transitions, so declared footprints and `permittedKinds` grow with them; inventory counts | `Concurrency/Locks/*` | L |
| SM9.D.18 | NI carriage: propagation is projection-invisible, but every touched transition's write set moves, so `observableSlotsConfinedToCores` proofs and the cross-core inventory need the new frames | `InformationFlow/NonInterference{PerCore,CrossCore}.lean` | L |

### SM9.E — Tests + closure (7 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.E.1 | Runtime groups §9 (SM9.A), §10 (SM9.B), §11 (SM9.C), §12 (SM9.D) — every group with a load-bearing negative | `tests/SmpInformationFlowSuite.lean` | XL |
| SM9.E.2 | **The cliff acceptance scenario**: fill the trail to `maxDeclassificationAuditEntries`, observe `.declassify` failing with `.auditLogCapacityExceeded`, drain via `.auditDrain`, observe it succeeding again — and, post-drain, that the next event's timestamp does **not** collide with a surviving entry (the SM9.A.1a epoch, exercised rather than asserted); plus a denied-`.declassifySignal` case proving the §3.1 seam filter covers both declassifying syscalls | same | L |
| SM9.E.2a | **The causal-detector acceptance scenario** (SM9.D): the §3.6 chain — downgrade writes a badge into a notification, an *ordinary* delivery moves it to a waiter TCB, that thread downgrades again — detected as laundering, with three load-bearing negatives: a domain-only detector produces a false positive on an unrelated pair, an object-adjacency detector produces a false negative on this very chain, and **two same-domain subjects where only one received hop 1's data are distinguished** (the SM9.D.13a identity doing its job).  Plus the lifecycle case: retype an object that carried taint, downgrade from its replacement, and confirm no causal link is reported | same | XL |
| SM9.E.3 | Golden fixtures `tests/fixtures/declassification_reader.expected` and `…_taint.expected` + `.sha256`, verified byte-for-byte in-suite; `tests/fixtures/README.md` rows | `tests/fixtures/` | M |
| SM9.E.4 | Headline anchors in `tests/SmpSurfaceAnchors.lean` §9; Tier-3 anchor block per sub-phase incl. the two retirement negatives and a negative against a hardcoded `.declassify` seam filter | `tests/SmpSurfaceAnchors.lean`, `scripts/test_tier3_invariant_surface.sh` | M |
| SM9.E.5 | `scripts/check_module_axioms.py` module list += each new module; axiom-clean sweep | `scripts/check_module_axioms.py` | T |
| SM9.E.6 | Documentation sync + phase closure record | spec, GitBook 12, `CLAIM_EVIDENCE_INDEX`, `WORKSTREAM_HISTORY`, `CLAUDE.md`/`AGENTS.md` | M |

## 5. The ABI slice (SM9.A.6-.A.8, SM9.C.8)

Adding a `SyscallId` touches ~14 files, established by the `.declassify = 30`
cut: `Model/Object/Types.lean` (constructor, `toNat`, `count`, `ofNat?`,
`ToString`, `all`, **and both match arms of `toNat_ofNat`**), `Kernel/API.lean`
(`syscallRequiredRight`, checked + unchecked arms, two syscall-list literals,
delegation theorems, `syscallDelegates`), `FrozenOps/Operations.lean`,
`Enforcement/Wrappers.lean`, `CovertChannelPerCore.lean`,
`Concurrency/Locks/{LockSetTransitions,LockSetForSyscall,LockSetInventory,Deadlock}.lean`
(+4 count theorems), `rust/sele4n-types/src/syscall.rs`,
`rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/tests/conformance.rs`,
`rust/sele4n-sys/src/<name>.rs` + `lib.rs`.  Plus the Tier-3 anchor block
(including `rg '<Name> = <n>'` against **both** Rust mirrors) and the
`main_trace_smoke.expected` `[XVAL-002]` line + `.sha256`.

## 6. The `SystemState` mount checklist (SM9.A.1a, SM9.B.3-.B.8, SM9.D.2-.D.6)

Three structures ride this checklist, and running it three times is the point of
writing it once: the SM9.A.1a **timestamp epoch**, the SM9.B **refusal ledger**,
and the SM9.D **taint side table**.  Verified against the
`declassificationAuditLog` and `pendingIcacheMaintenance` precedents:

1. Payload in a **leaf** module so `Model/State.lean` does not import the owning
   subsystem (`AuditRecord.lean` / `CacheInvalidation.lean` precedent).
2. `Model/State.lean`: field + docstring (Algebra / Lifecycle / Capacity /
   Information flow), **explicit** listing in `instance : Inhabited SystemState`,
   `@[simp] default_<field>`, `storeObject_<field>_eq`.
3. `Model/FrozenState.lean`: **required** (no default) field, so a silent drop is
   a compile error; `freeze` forwarding; `freeze_preserves_<field> := rfl`.
4. `Model/FreezeProofs.lean`: conjunct in `apiInvariantBundle_frozenDirectFull`
   and a bullet in `freeze_preserves_direct_invariants_full`.
5. The six `FrozenSystemState` test literals (SM9.B.5).
6. `IPC/Invariant/LookupCongruence.lean`: the `OffSchedulerAgrees` clause + **all
   six** builders (`refl`, `symm`, `trans`,
   `offSchedulerAgrees_scheduler_update`,
   `enqueueRunnableOnCore_offSchedulerAgrees_of_ready`,
   `storeObject_offSchedulerAgrees`).
7. `Platform/Boot.lean`: four frames — `applyMachineConfig_*_eq` (`rfl`),
   `private foldIrqs_*`, `private foldObjects_*`, `bootFromPlatform_*_eq`.
8. **No** `proofLayerInvariantBundle` conjunct for any of the three — the ledger's
   `Vector` ring and the taint set are bounded by their types (§3.2, §3.6), and
   the epoch is a monotone counter with nothing to bound.  If that decision is
   ever reversed, the 17th conjunct also costs the five-lemma carriage block in
   `Architecture/Invariant.lean` and a hand re-count of every
   `refine ⟨?_,…⟩` / `obtain ⟨…⟩` over the bundle, which under-list **silently**.
8a. **§3.7 check.**  For each mounted structure, decide whether any syscall can
   read it, and record the answer in the §3.7 inventory: the trail and the ledger
   are readable and owe both obligations; the taint table is not readable and
   owes neither *yet*.  Skipping this step is how the ledger reached round 2
   without an equivalence clause.
9. `scripts/check_module_axioms.py` — add each new module to the
   `SMP_INFORMATION_FLOW` list, or `--all-smp-information-flow` silently skips it.

**Staged vs production** is decided by reachability, not a marker:
`check_production_staging_partition.sh` computes
`staged_only = closure(Staged.lean) \ closure(SeLe4n.lean)` and requires it to
equal `staged_module_allowlist.txt` exactly, in both directions.
`AuditRead.lean`, `RefusalRecord.lean` and `Taint.lean` are imported by live
dispatch arms and live IPC transitions, so they are **production and must not be
allowlisted** — the same reason
`AuditRecord.lean` and `Declassification.lean` are not.

## 7. Verification strategy

### 7.1 Per PR

```bash
source ~/.elan/env
lake build <each edited module>              # the pre-commit hook enforces this
lake exe smp_information_flow_suite
lake exe information_flow_suite              # boundary counts
lake exe smp_surface_anchors
./scripts/check_module_axioms.py --all-smp-information-flow
./scripts/test_full.sh                       # Tier 0-3
```

For ABI-touching sub-tasks (SM9.A.6-.A.8, SM9.C.8) additionally:

```bash
lake exe abi_roundtrip_suite && lake exe syscall_dispatch_suite
lake exe decoding_suite && lake exe kernel_error_matrix_suite
./scripts/test_rust.sh                       # both mirrors + conformance
```

### 7.2 Conventions that are not optional

- **A cut that changes a count must run the whole suite surface.**  SM8.C's
  follow-up recorded it and SM8.E confirmed it.
- The identifier-naming gate reads the **git index** — stage before running it.
- Tier-3 `run_check` / `run_negative_check` run against the **code view** (a
  comment-free, byte-aligned overlay), so a docstring can neither satisfy nor
  trip an anchor; use `run_prose_check` when the subject really is the text.
  `_run_with_view` fails closed on a `bash -lc` that both invokes a tool and
  greps Lean source — split those.
- A load-bearing negative's **label text is part of the API**: Tier-3 greps the
  literal string.
- Golden-fixture content is **counts and verdicts, not identifiers** — a fixture
  outside `docs/` is code to the identifier-naming gate.
- Each new `run*Checks` group needs its own Tier-3 anchor.

## 8. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| **An audit syscall gated on a right rather than a target** | MED | HIGH | The **v0.32.97 confused-deputy class**: `syscallLookupCap` never constrains `cap.target`, so a `.read`-gated reader is reachable by any thread holding its own TCB.  `CapTarget.auditTrail` + `extractAuditAuthority` (§3.3), with a negative that a non-`.auditTrail` capability carrying `.read` is rejected |
| SM9.C.6's NI statement is wrong in a way that looks right | MED | HIGH | State both halves — the confined difference **and** the trail entry recording it — over a footprint defined once (§3.5), with two load-bearing negatives: an *unrecorded* difference and a difference *outside the footprint* must both be refutable |
| The refusal ledger becomes a channel | LOW | HIGH | Outside `ObservableState`; the capacity reason is **recorded** (see below) but readable only under the monitor gate, so the occupancy channel is closed by the gate rather than by discarding evidence; **readable only under full dominance** (§3.2), so a hidden write cannot evict a partial reader's entry or move its counters; `_denied_before_capacity` re-verified as an SM9.B acceptance item |
| A readable structure is added with no equivalence clause | MED | HIGH | §3.7's fused `AuditReadOp`/`ReadableStructure` + a **total** clause function — a `mem_all` list cannot force a new structure to join it |
| Drain breaks the trail's timestamp discipline | HIGH | HIGH | **Realised, not hypothetical**: `timestamp := log.length` reuses a timestamp after any prefix removal.  Closed by the SM9.A.1a epoch, sequenced before drain exists, with the reuse as a load-bearing negative (§3.4) |
| Taint propagation misses a content-moving transition | MED | HIGH | A **total** `KernelOperation → ContentFlowClass` over SM8.E's exhaustive enumeration (SM9.D.7) + non-content frames (SM9.D.12) — a missed site is a detector that misses real laundering |
| A privileged gate computed from rows a drain removes | MED | **HIGH** | Drain a trail to `[]` and a rows-derived dominance predicate is vacuously true, admitting a low reader to the global epoch that counts the drained entries.  One configured `auditMonitorClearance` gates drain, the ledger, global identity and `predecessorTags` (§3.4) |
| A reader that computes correctly and returns garbage | **HIGH** | **HIGH** | `dispatchWithCapChecked` is `Kernel Unit` and nothing writes the TCB return register, so `.auditRead` would hand back the caller's own `x0`.  Blocked on WS-RA (§2); SM9.A.10 writes the result and asserts it end to end |
| A detector that rejects the scenario it was built for | MED | HIGH | The second per-hop event extends the snapshot with hop 1's timestamp (§3.5); taint propagates on the wait arm as well as the signal arm (SM9.D.10) |
| An audit trail that reports an edge no policy authorized | MED | **HIGH** | Two gated hops emit two events (§3.5); one record would collapse `high → mid` and `mid → low` into a direct `high → low` edge |
| A downgrade authorized to one sink reaching a second | MED | **HIGH** | The live bound-signal path gates `notification → receiver` as well as `signaler → notification` (v0.31.73), and a footprint is not an authorization.  SM9.C.1 gates the resolved destination and audits it (§3.5) |
| A field added to a readable record becoming a channel | MED | HIGH | §3.7's inventory is keyed by **field**, not structure: `predecessorTags` carries global timestamps and is dominating-reader-only, with an opaque verdict for partial readers |
| A historical verdict that moves with current state | MED | HIGH | The causal predicate reads `predecessorTags` snapshotted into the event, not the mutable taint table — otherwise a tag acquired late invents a link and a retype-cleared TCB loses a real one (§3.6) |
| A multi-call read that tears | MED | MED | `status` is one call with bounded components (§3.3); the chunked design it replaces could assemble a generation from two states |
| A completeness gate a new structure can decline to join | MED | HIGH | `mem_all` over a hand-maintained type cannot force a new readable field to add a constructor.  `AuditReadOp` is fused with `ReadableStructure` and the clause set is a total function (§3.7), so the gate fails at elaboration rather than passing silently |
| A visibility gate computed from data that ages | MED | HIGH | The refusal ring evicts while its counters are cumulative, so a records-derived gate shrinks while the guarded data does not.  Gated on configured clearance instead (§3.2), with the eviction counterexample kept as a negative |
| Taint outliving the object it describes | MED | MED | Retype commits `storeObject` at the same id, so a framed retype leaves a destroyed object's tags on its replacement — a false positive unrelated to saturation.  Retype clears (§3.6, SM9.D.12) |
| SM9.D's size swamps the phase | HIGH | MED | Acknowledged in the estimate rather than absorbed: 18 sub-tasks, 6-8 PRs, and the phase moved 6-9 → 12-16 weeks.  Sequenced in four blocks so mount, propagation and detector land separately |
| The reader leaks hidden-entry counts through index gaps | LOW | HIGH | Re-indexed filtered view, not sparse global indices; the visible view is a function of the reader's clearance alone; **drain requires full dominance** so there is no partial-visibility prefix to probe (§3.4) |
| A global drain generation signals a dominating monitor's drains to every reader | MED | HIGH | `drainGeneration` is observer-scoped (§3.3), with the negative that a global counter is refutable |
| The reader's flow argument is stated over a relation that cannot see the trail | MED | HIGH | `lowEquivalent` does not imply equal visible views once a reader exists — the naive lemma is **false** (§3.4a).  `auditObservationalEquivalence` is the relation SM9.A.4a/.4b are stated over |
| A read word aliases the ABI error flag | — | — | Structurally impossible since WS-RA (v0.33.37): value and error travel in separate registers (`x0` vs `x1`'s `MessageInfo` label), so no returned word can alias the error channel.  Unbounded fields are still chunked (§3.3) — that constraint was never about the flag |
| A retired rule leaves stale inventory counts | MED | MED | Both retirements (SM9.B.10, SM9.D.15) follow the SM8.E pattern: retire, move counts, add a negative anchor |
| SM9.C.3's invariant surface is larger than estimated | MED | MED | The transition is `notificationSignal` + an audit write; if preservation does not ride the existing family, split SM9.C.3 into per-conjunct PRs |
| Scope creep into a general syscall-failure audit | MED | LOW | The seam filters to the `declassificationSyscalls` list (§3.1) — narrow, but *derived*, so SM9.C's second declassifying syscall joins it automatically; generalisation beyond declassification recorded as future work |

## 9. Acceptance gate

- [ ] A clearance-filtered reader exists; a dominating monitor can drain the
      trail; the 256-entry cliff is demonstrably gone (SM9.E.2 scenario).
- [ ] The reader is gated on a **`.auditTrail` capability**, not merely on a
      right, and an unconfigured deployment has no audit reader at all.
- [ ] **Drain requires full dominance**, and the operator consequence is stated
      in the shipped documentation rather than only here: a deployment whose
      monitor does not dominate every recorded `srcDomain` cannot drain, and
      the 256-entry cliff returns for it.  That is the conservative default,
      and it is the operator's to know about.
- [ ] `drainGeneration` is observer-scoped; the global-counter form is refuted
      by a negative rather than merely avoided.
- [ ] Refusals are counted and attributed, and provably cannot displace an
      authorized-downgrade entry.
- [ ] `authorizeDeclassificationOnCore_denied_before_capacity` still holds for the
      **caller-facing** error, and the refusal record still carries
      `.auditLogCapacityExceeded` for the monitor — the occupancy channel is
      closed by the read gate, not by discarding the only durable evidence that
      an authorized downgrade hit the 256-entry cliff.
- [ ] A data-carrying declassification exists, with
      `declassificationRelativeNonInterference` in both halves.
- [ ] Timestamps survive drains: after a drain, a fresh event's timestamp
      collides with no surviving entry, and the well-formedness contract names
      the epoch rather than claiming index-anchoring.
- [ ] Every value the reader exports — record fields **and** `status` — is
      reconstructible from its chunks, not merely small enough to fit one
      return word; and a partial reader cannot infer hidden-entry counts from
      an exported index.
- [ ] Every visibility gate is computed from something that does not age out
      from under it: the refusal ledger's gate is configuration, not the ring's
      surviving rows.
- [ ] A retyped object carries no taint from its predecessor, with a lifecycle
      test rather than a frame lemma.
- [ ] The causal verdict on a fixed pair of events is stable under later
      unrelated activity, including a retype of the subject.
- [ ] Every completeness gate is keyed to a taxonomy that is exhaustive
      *independently* of the gate — `KernelOperation.all` for content flow,
      `ReadableStructure` fused with the reader for visibility — so a new live
      transition or a new readable field cannot decline to join it.
- [ ] SM9.C.0 is closed: the notification wait path delivers the badge, so a
      data-carrying declassification is not built over a path that loses data in
      one of its two orderings.
- [ ] The declassifying signal authorizes its **resolved destination**, not only
      its notification, and the audit event names that destination — the
      v0.31.73 leak is not re-opened under declassification authority.
- [ ] A two-hop delivery within one transition is **detected as a chain**: the
      second event names the first, so the design's own scenario is not rejected
      by its own detector.
- [ ] Taint propagates on **both** notification orderings, so the causal
      scenario holds whether the signal or the wait comes first.
- [ ] Every content-moving sub-transition reachable from a live arm is
      classified, established by **reach** (the call-graph gate) and not by
      totality over a type that does not enumerate them.
- [ ] An event's **actor** and its **flow source** are separate fields, so a
      second-hop record never asserts that a high subject is mid.
- [ ] A refused second hop names the **resolved receiver**, not the original
      capability operand.
- [ ] A refusal read that races a `recordRefusal` is **detected**, not silently
      assembled from two attempts.
- [ ] `.auditRead` and `.auditDrain` return their computed word to the caller —
      verified end to end through `syscallDispatchFromAbi`, not just at the
      transition — which requires WS-RA to have landed.
- [ ] No field derived from hidden state reaches a partial reader, including
      fields added to fix something else.
- [ ] Every readable structure has an equivalence clause and a hidden-write
      non-interference argument (§3.7), enforced by `auditReadOp_structure_total`
      and `auditObservationalEquivalence_clause_total` — **not** by a `mem_all`
      list, which §3.7 refutes.
- [ ] Both declassifying syscalls reach the refusal seam, enforced by the total
      `refusalSeamClass_total` and exercised by a denied `.declassifySignal`.
- [ ] The laundering detector is **causal**: the §3.6 chain (downgrade →
      ordinary delivery → downgrade) is detected, the syntactic-scope theorem is
      retired rather than weakened, and the residual saturation-induced
      over-approximation is pinned by its own negative.
- [ ] `KernelOperation.all` grew by exactly one, with `mem_all` and all three
      counts moved.
- [ ] Zero `sorry`/`axiom`; `check_module_axioms.py --all-smp-information-flow`
      green including every new module.
- [ ] Tier 0..3 green; trace fixture diffs explained.

## 10. Cross-references

- **Previous**: [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md) (SM8)
- **Next**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10)
- **Registered source**: SM8's four follow-ons — see
  [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md) §5 SM8.C
  "Registered follow-on".

## 11. Theorem catalogue for SM9

~82 substantive theorems.  Headline set:

- `auditLogVisibleTo_sublist` + the clearance-determines-view theorem (SM9.A.1)
- `auditTimestampsFrom_epoch_preserved` + `auditDrain_monotone_epoch` — the
  timestamp epoch, and the negative that the pre-epoch `log.length` producer
  **reuses** a timestamp after a drain (SM9.A.1a)
- `auditReadField_reconstructs` + `auditReadBasis_reconstructs_designation` —
  folding the chunks recovers the value, over the domain `maxAuditFieldChunks`
  admits, with `.auditFieldTooLarge` fail-closed above it (SM9.A.2)
- `auditReadStatus_atomic` — `status` is one call, because chunking it traded
  aliasing for tearing on the first interleaved drain (SM9.A.2)
- `auditReadIndex_is_view_local` + `auditRead_hides_global_position` +
  `dominatingReader_sees_global_identity` — a partial reader cannot count hidden
  entries, and a monitor can still correlate across drains (SM9.A.2)
- `observerScopedGeneration_not_mountable` — why the per-observer token was not
  merely unbuilt but unbuildable (SM9.A.2)
- `auditReadOp_structure_total` + `auditObservationalEquivalence_clause_total` +
  `readableStructure_list_gate_insufficient` — the §3.7 gate a new structure
  cannot decline to join (SM9.A.2, SM9.A.4a)
- `refusalLedger_gate_is_configuration_derived` +
  `refusalLedger_records_gate_unsound` — the ring evicts, the counters do not, so
  the gate is configuration and not current records (SM9.B.10)
- `retypeClearsTaint` + `retypedObject_taint_empty` +
  `staleTaint_is_not_saturation` — taint must not outlive its object (SM9.D.12)
- ~~`auditReadWord_fits_payload`~~ — **retired by WS-RA (v0.33.37)** before it
  was ever built: the bit-63 `encodeOk` encoding it guarded against is gone,
  and a full-width word cannot alias the error channel (§3.3).  The
  losslessness half it was explicitly *not* — `auditReadField_reconstructs` —
  is unaffected (SM9.A.2)
- `auditReadStatus_generation_observer_scoped` + the negative that a global
  drain counter is refutable (SM9.A.2)
- `auditDrain_requires_full_dominance` (SM9.A.3)
- `auditDrainVisiblePrefix_preserves_auditLogBounded` +
  `_preserves_wellFormed_at_epoch` + `_fully_clears_for_dominating_reader`
  (SM9.A.3)
- `auditObservationalEquivalence` over a **total** clause function + its
  congruences, and the negative that plain `lowEquivalent` does **not** imply
  equal visible views (SM9.A.4a, §3.7)
- `auditRead_no_channel` — the reader's flow argument, over that relation
  (SM9.A.4b)
- `extractAuditAuthority_rejects_non_audit_capability` (SM9.A.9)
- `auditRead_stable_under_append` (SM9.A.5)
- `recordRefusal_saturates` / `_no_loss` / `_ring_wraps_counted` (SM9.B.2)
- `refusalLedger_requires_full_dominance` + the negative that a partially-cleared
  caller reads nothing of it (SM9.B.10, §3.7)
- `refusalSeamClass_total` + `refusalSeam_list_gate_insufficient` — every
  syscall arm is classified for the refusal seam or does not elaborate (SM9.B.9)
- `refusalWrite_declassificationAuditLog_eq` (SM9.B.9)
- `declassificationRefusals_write_preserves_projection` +
  `onCore_declassificationRefusals` (SM9.B.8)
- `notificationSignalDeclassified_preserves_ipcInvariantFull{,_perCore}` (SM9.C.3)
- **`declassificationRelativeNonInterference`** (SM9.C.6) — the phase headline
- `contentFlowClass_total` + `contentFlowSite_list_gate_insufficient` — the
  taint-propagation soundness keystone, classified from an exhaustive taxonomy
  rather than enumerated in a fresh one (SM9.D.7)
- `chainCausal_is_history_local` + `chainCausal_not_table_derived` — the verdict
  on a fixed pair of events cannot change with later unrelated activity
  (SM9.D.13a, SM9.D.14)
- `predecessorTags_dominating_only` + `partialReader_gets_opaque_causality` — a
  field added to a readable record is a read channel (SM9.D.13a, §3.7)
- `attributionFromRunningSubject_over_actor` +
  `secondHop_actor_differs_from_flowSource` — who performed a downgrade and
  where the flow came from are two identities (§3.5)
- `refusalRecord_names_failed_hop` — a denied second hop names the resolved
  receiver, not the original operand (SM9.B.1)
- `refusalLedger_version_advances_on_record` +
  `refusalRead_bracketed_detects_overwrite` — the ledger's reads need a version
  for the same reason the trail's do (SM9.B.2, §3.2)
- `declassifiedSignal_gates_resolved_receiver` +
  `declassifiedSignal_audits_actual_destination` + `footprint_does_not_authorize`
  — naming a sink in the footprint does not permit it (SM9.C.1)
- `declassifiedSignal_audits_each_hop` + `declassifiedSignal_no_invented_edge` +
  `secondHopEvent_names_firstHop` — two authorizations need two records, and the
  second must name the first or the detector rejects the chain the design exists
  to record (SM9.C.1, §3.5)
- `auditMonitorGate_is_configuration_derived` +
  `auditMonitorGate_records_derived_unsound` — the single privileged-reader gate,
  and why a rows-derived one goes vacuous on a drained-empty trail (§3.4)
- `refusalSeamClass_total` + `refusalSeam_list_gate_insufficient` — the third
  taxonomy fixed the same way as the first two (§3.1, §3.7)
- `refusalRecord_domain_is_seam_resolved` (SM9.B.1)
- `taintPropagation_*` per content-flow site + the non-content frames (SM9.D.8–.12)
- `taintSaturate_over_approximates` — overflow errs toward false positives,
  never a missed chain (SM9.D.13)
- **`chainLaunders_sound_under_causal_provenance`** (SM9.D.15) — the sub-phase
  headline, replacing the retired `declassificationChainLinked_is_syntactic`,
  with a negative pinning the residual saturation-induced over-approximation

## Appendix A — Verification commands

```bash
source ~/.elan/env
lake build SeLe4n.Kernel.InformationFlow.AuditRead
lake build SeLe4n.Kernel.InformationFlow.RefusalRecord
lake exe smp_information_flow_suite
./scripts/check_module_axioms.py --all-smp-information-flow
```

---

*SM9 makes the declassification path functional.  SM8 proved the boundary and
recorded the crossings; SM9 lets an operator read that record, counts the
attempts that were refused, moves the data the boundary exists to move, and
gives the laundering detector something causal to reason about.*
