# SM9 — Declassification Completion (WS-SM Phase 9)

> **Phase**: SM9 of WS-SM
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Predecessor**: [`SMP_INFORMATION_FLOW_PLAN.md`](SMP_INFORMATION_FLOW_PLAN.md) (SM8, CLOSED v0.33.23)
> **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10)
> **Audited cut**: `v0.33.23`
> **Target releases**: v0.33.24 → v0.34.x
> **Calendar estimate**: 12-16 weeks
> **Sub-task count**: 59 across ~20-24 PRs
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
error into `.ok (encodeError ke, stRegs)`, and `syscallDispatchCrossCoreEntry`
commits that state.  **A refused syscall already commits a post-state.**  And
every field a refusal record needs is already an argument there:

| Field | Source at the seam |
|---|---|
| executing core | `executingCore` parameter |
| subject thread | `st.scheduler.currentOnCore executingCore` (already matched on) |
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
SM9.B exists to close.  So the filter reads a **`declassificationSyscalls` list**
with a `declassificationSyscalls_complete` theorem (every `SyscallId` whose
transition consults `declassificationDecision` is a member), and SM9.C.8 extends
that list rather than a second copy of the predicate.  A third declassifying
syscall then cannot be added without joining the seam, because the completeness
theorem stops elaborating.  SM9.E carries a denied-`.declassifySignal` acceptance
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
view, and the dominating reader sees every write by definition.  This is the same
gate drain already takes (§3.4), so the two are one decision rather than two, and
the operator consequence is the same: refusal monitoring, like drain, wants one
fully-cleared monitor.

### 3.3 Reader interface: indexed read, no new kernel→user write path

A syscall returns exactly one word: `rust/sele4n-hal/src/trap.rs` is
`frame.set_x0(retval)` and nothing else in the trap frame is written back.  So a
reader either returns one word per call, or the kernel writes into the caller's
IPC buffer.

**The payload is 63 bits, not 64.**  `Platform/FFI.lean`'s
`encodeOk v := v &&& 0x7FFFFFFFFFFFFFFF` reserves **bit 63** as the error flag,
which `encodeError` sets — so a return value with bit 63 set is
indistinguishable from an error code, and a naive 64-bit field would alias
silently rather than fail closed.  Consequences for SM9.A.2, all of them design
constraints rather than notes:

- `core ⊕ kernelIssued` is packed into the **low** bits and must not touch
  bit 63.
- **All four** value fields — `srcDomain.id`, `dstDomain.id`,
  `targetObject.val`, `timestamp` — are unbounded `Nat` in the model
  (`SecurityDomain.id : Nat`, `ObjId.val : Nat`), so each is read through an
  **arbitrary-length 32-bit chunk protocol**: `AuditReadOp.field w chunkIndex`
  plus a `fieldChunkCount w` sub-operation telling the reader how many chunks
  that field occupies.  Total for any `Nat`, and terminating because any
  particular value is finite.
- `auditReadField_reconstructs` (§11) is the losslessness theorem: folding a
  field's chunks recovers the value exactly.

A fixed two-chunk (low/high) design was drafted and is **wrong**: two 32-bit
chunks bound a field at 2^64, so values differing above bit 63 produce identical
chunks — it moves the truncation point rather than removing it — and it left the
two domain fields as single words while the surrounding prose called the design
lossless.  `auditReadWord_fits_payload` is retained, but its role is now stated
precisely: it is the **ABI-safety** half (every returned word is `< 2^63`, so
`encodeOk` is the identity on it) and is *not* the losslessness claim.  Proving
each fragment survives the encoding says nothing about whether the record can be
reconstructed from the fragments; conflating the two is what made the two-chunk
design look adequate.

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

`.auditRead` sub-operations are enumerated **as data** with a `mem_all`
completeness theorem, in the idiom `CovertChannelId.all` / `KernelOperation.all`
already use: `status` (visible length + the observer-scoped drain generation),
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
restriction.  `auditDrain_requires_full_dominance` (§11) is the theorem.

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
- Propagation sites are enumerated **as data** with a completeness theorem.  This
  is the soundness keystone: propagation that misses a content-moving transition
  is a detector that misses real laundering, so the enumeration is checked rather
  than asserted, in the `KernelOperation.all` idiom.
- Overflow **saturates upward** to "tainted by everything".  For a detector the
  safe direction is over-approximation — more false positives, never a missed
  chain — and `taintSaturate_over_approximates` states that direction rather than
  leaving it to a comment.
- The taint table is **not readable** by any SM9 syscall, so §3.7 records that it
  owes no equivalence clause *yet* and what a future reader would owe.

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

**Mechanised, not asserted.**  `auditObservationalEquivalence` is stated over a
**list** of readable structures rather than one named field, with
`ReadableStructure.all` / `mem_all` / `all_nodup` in the `CovertChannelId.all`
and `KernelOperation.all` idiom — so a structure added without an equivalence
clause fails `mem_all` rather than passing silently.  This is the same
completeness mechanism SM8.E installed after finding that three separate count
theorems were counting list literals rather than constructors.

**Current inventory** (SM9.A.4a owns it):

| Structure | (a) inclusion | (b) hidden-write non-interference |
|---|---|---|
| `declassificationAuditLog` | `auditLogVisibleTo ctx L` clause | drain requires full dominance (§3.4); generation observer-scoped (§3.3) |
| `declassificationRefusals` | ledger view clause, gated | readable only under full dominance (§3.2) |
| `declassificationTaint` (SM9.D) | **not readable** — no clause owed | vacuous while unreadable; a reader added later owes both |

The third row is load-bearing rather than filler: SM9.D mounts a taint table and
deliberately exposes no reader for it, so the discipline records *why* it owes
nothing yet and what a future reader would owe.

## 4. Detailed sub-task breakdown

Sizes: **T** trivial, **S** small, **M** medium, **L** large, **XL** very large.

### SM9.A — The audit trail reader (5-6 PRs, 15 sub-tasks)

Ships as **two PRs' worth of work at minimum**: SM9.A.1-.A.5 (the pure reader
plus its observation relation) and SM9.A.6-.A.13 (the ABI, the live arms and
their registries).  SM9.A.4a alone is a relation with congruence lemmas — see
§3.4a — which is why the split is structural rather than a convenience.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.A.1 | `auditLogVisibleTo ctx L` + `_sublist` / `_reindexed` / `_length_le`; the no-gap-leak theorem (the visible view is a function of the reader's clearance alone) | new production leaf `InformationFlow/AuditRead.lean` | M |
| SM9.A.1a | **The persistent timestamp epoch** (§3.4) — `SystemState.declassificationAuditEpoch`, `timestamp := epoch + log.length`, well-formedness generalised to `auditTimestampsFrom epoch log` (the `start`-parameterised lemma already exists) with the 0-anchored form as the boot instance; both identification theorems generalised; the three `_preserves_wellFormed` theorems restated; full §6 mount carriage (freeze required field, `OffSchedulerAgrees`, four boot frames, `storeObject` frame, `…_write_preserves_projection`); the corrected "well-formed throughout" contract.  **Sequenced before SM9.A.3 — drain is unsound without it** | `Model/State.lean`, `Model/{FrozenState,FreezeProofs}.lean`, `Platform/Boot.lean`, `InformationFlow/{Declassification,DeclassificationPerCore}.lean` | L |
| SM9.A.2 | `AuditReadOp` sub-operation inductive + `all` / `mem_all` / `all_nodup`; the §3.3 **arbitrary-length chunk protocol** (`fieldChunkCount w`, `field w chunkIndex`) over all four unbounded fields; `auditReadField_reconstructs` (folding a field's chunks recovers the value — the losslessness claim) and `auditReadWord_fits_payload` (the ABI-safety half, explicitly *not* losslessness); `auditReadStatus` (visible length ⊕ observer-scoped drain generation) + `_generation_observer_scoped` and the negative that a global counter is refutable | same | XL |
| SM9.A.3 | `auditDrainVisiblePrefix` under the §3.4 dominance gate, advancing the SM9.A.1a epoch; `auditDrain_requires_full_dominance`, `_preserves_auditLogBounded`, `_preserves_wellFormed_at_epoch`, `_monotone_generation`, `_monotone_epoch`, `_fully_clears_for_dominating_reader`, and the negative that a partially-cleared caller drains nothing | same | M |
| SM9.A.4a | **`auditObservationalEquivalence ctx L`** (§3.4a option b, §3.7 discipline): the relation stated over `ReadableStructure.all` (+ `mem_all` / `all_nodup`) rather than one named field, so a readable structure without a clause fails completeness; clauses for the trail **and** the refusal ledger; reflexivity / symmetry / transitivity; the congruence lemmas carrying it through every writer of a readable structure; the negative that plain `lowEquivalent` does **not** imply equal visible views (which is why the relation exists) | `InformationFlow/DeclassificationPerCore.lean` (staged) | XL |
| SM9.A.4b | The flow argument over that relation: the reader is a function of the visible view alone, so it opens no channel; the **not-CC-8** argument stated once | same | L |
| SM9.A.5 | `auditRead_stable_under_append` + the reader retry protocol as a theorem | `InformationFlow/AuditRead.lean` | S |
| SM9.A.6 | ABI, Lean half: `SyscallId.auditRead`/`.auditDrain`, count 31→33, `toNat`/`ofNat?`/`ToString`/`all` + both `toNat_ofNat` match arms | `Model/Object/Types.lean` | M |
| SM9.A.7 | ABI, Rust half: both mirrors + conformance roundtrips + boundary test | `rust/sele4n-types/src/syscall.rs`, `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-abi/tests/conformance.rs` | M |
| SM9.A.8 | `sele4n-sys` safe wrappers | `rust/sele4n-sys/src/audit.rs`, `lib.rs` | S |
| SM9.A.9 | **`CapTarget.auditTrail`** constructor + `extractAuditAuthority` (§3.3): the total-match consequences across `Capability`'s `Repr`/`DecidableEq`/well-formedness, the frozen mirror, and every existing `CapTarget` match; the mint path (which boot/CSpace layer creates one); the negative that a non-`.auditTrail` capability carrying `.read` is rejected, and the acceptance witness that an unconfigured deployment has **no** audit reader | `Model/Object/{Types,Structures}.lean`, `Model/FrozenState.lean`, `Platform/Boot.lean` | XL |
| SM9.A.10 | Live arms in `dispatchWithCapChecked` gated on `extractAuditAuthority` **then** `syscallRequiredRight`; unchecked arms fail closed; `syscallDelegates_auditRead` / `_auditDrain` | `Kernel/API.lean` | L |
| SM9.A.11 | Enforcement boundary 40→42 canonical, 55→57 per-core; `syscallIdToEnforcementName{,PerCore}`; completeness + class-match re-decided | `Enforcement/Wrappers.lean`, `CovertChannelPerCore.lean` | M |
| SM9.A.12 | Lock sets: `lockSet_auditRead` (universal reads), `lockSet_auditDrain`; `permittedKinds`; inventory counts 103→105; `_size_le` + deadlock aggregate | `Concurrency/Locks/{LockSetTransitions,LockSetForSyscall,LockSetInventory,Deadlock,DeadlockInventory}.lean` | M |
| SM9.A.13 | Frozen-ops classifier arm + count; per-core routing gate registration | `Kernel/FrozenOps/Operations.lean`, `scripts/per_core_routing_aliases.json` | S |

**Acceptance**: a monitor reads every entry it is cleared for and drains the
trail; the 256-entry cliff is gone.

### SM9.B — Refusal auditing (3-4 PRs, 10 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.B.1 | `DeclassificationRefusal` record (core, subject, syscall, reason class, raw `CPtr`) + `Repr`/`DecidableEq` | new leaf `InformationFlow/RefusalRecord.lean` | S |
| SM9.B.2 | `RefusalLedger` (§3.2 shape) + `recordRefusal`; saturation, no-loss, drop-count and ring-wrap theorems; `maxRefusalCount` / `refusalRingSize` constants | same | M |
| SM9.B.3 | Mount `SystemState.declassificationRefusals`: field, `Inhabited` listing, `default_*`, `storeObject_*_eq` | `Model/State.lean` | S |
| SM9.B.4 | Freeze carriage: required `FrozenSystemState` field, `freeze` forwarding, `freeze_preserves_*`, the `apiInvariantBundle_frozenDirectFull` conjunct + bullet | `Model/FrozenState.lean`, `Model/FreezeProofs.lean` | M |
| SM9.B.5 | The six `FrozenSystemState` test literals | `tests/{Ak8Coverage,FrozenOps,IpcBuffer,PriorityManagement,SuspendResume,TwoPhaseArch}Suite.lean` | S |
| SM9.B.6 | `OffSchedulerAgrees` clause + **all six** builders | `IPC/Invariant/LookupCongruence.lean` | M |
| SM9.B.7 | Boot frames ×4 (`applyMachineConfig`, `foldIrqs`, `foldObjects`, `bootFromPlatform`) | `Platform/Boot.lean` | S |
| SM9.B.8 | Information flow: `declassificationRefusals_write_preserves_projection := rfl` **and** `onCore_declassificationRefusals` as the tenth read-set corollary | `InformationFlow/Invariant/Operations.lean`, `ObservableStatePerCore.lean` | S |
| SM9.B.9 | Write at the seam, filtered by the **derived** `declassificationSyscalls` list (§3.1) rather than a hardcoded `.declassify`; `declassificationSyscalls_complete`; re-shape `syscallDispatchFromAbi_error_of_syscallEntryChecked_error`; re-prove `_total`; the three security theorems (below) | `Platform/FFI.lean` | L |
| SM9.B.10 | Extend `.auditRead` with refusal sub-operations, **gated on full dominance** (§3.2/§3.7) — ring *and* counters, since a saturating global count leaks hidden activity independently of the ring; the `ReadableStructure` clause + congruences this adds to SM9.A.4a's relation; the negative that a partially-cleared caller reads nothing of the ledger; **retire `DeclassificationRuleId.refusalIsUnrecorded`** | `InformationFlow/AuditRead.lean`, `DeclassificationPerCore.lean` | L |

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

### SM9.C — Data-carrying declassification (3-4 PRs, 9 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.C.1 | `notificationSignalDeclassified` — the SM6.B signal gated by `declassificationDecision`, badge delivered, event recorded; error arms fail closed | `IPC/CrossCore/NotificationSignal.lean` | L |
| SM9.C.2 | Per-core + cross-core forms (`…OnCore`, `…CrossCoreDispatchChecked`), SGI emission, home-core wake | same | L |
| SM9.C.3 | `ipcInvariantFull{,_perCore}` preservation — rides `notificationSignal_preserves_*` plus the audit frame | `IPC/Invariant/PerCoreBundlePreservation.lean` | L |
| SM9.C.4 | `proofLayerInvariantBundle` preservation + `auditLogBounded` carriage | `InformationFlow/Declassification.lean` | M |
| SM9.C.5 | **`declassificationEffectFootprint`** (§3.5: notification ⊕ waiter TCB ⊕ waiter home-core scheduler slots) defined **once** and read by both consumers; lock set + write set + `observableSlotsConfinedToCores`; inventory counts | `Concurrency/Locks/*`, `InformationFlow/NonInterferenceCrossCore.lean` | L |
| SM9.C.6 | **`declassificationRelativeNonInterference`** — both halves (§3.5) over the SM9.C.5 footprint, with two load-bearing negatives: an *unrecorded* difference is refutable, and a difference **outside** the footprint is refutable | `InformationFlow/NonInterferencePerCore.lean` | XL |
| SM9.C.7 | NI inventory growth: `KernelOperation.all` 35→36, `niStepConstructorCoverage` arm, `perCoreConfinementDerived` arm, all three counts + the complement | `InformationFlow/Invariant/Composition.lean`, `NonInterferencePerCore.lean` | M |
| SM9.C.8 | Live arm + ABI: `SyscallId.declassifySignal`, count 33→34, both Rust mirrors, conformance, `sele4n-sys`, enforcement boundary 42→43 / 57→58, lock-set inventory; **and the `declassificationSyscalls` list (§3.1) extended**, so this syscall's refusals reach the SM9.B seam rather than bypassing it | ~14 files (§5) | L |
| SM9.C.9 | `syscallDelegates_declassifySignal`; per-core routing gate; cross-core NI inventory entry | `Kernel/API.lean`, `NonInterferenceCrossCore.lean` | M |

### SM9.D — Causal declassification provenance (6-8 PRs, 18 sub-tasks)

The phase's largest sub-phase, and the reason the calendar estimate moved.  §3.6
records why declassification-only edges cannot do this job.  Sequenced in four
blocks: type and mount (D.1–D.6), the propagation surface (D.7–D.12), the
saturation policy (D.13), the detector and its consequences (D.14–D.18).

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.D.1 | `DeclassificationTaint` — a **bounded** set of event timestamps (SM9.A.1a makes them stable across drains) with a `saturated` top, `join`, and a `covers` preorder; join-semilattice laws; no-loss theorems | new production leaf `InformationFlow/Taint.lean` | M |
| SM9.D.2 | Mount `SystemState.declassificationTaint` as a **side table** keyed by `ObjId` (not a field on seven object kinds — the audit-trail precedent); `default_*`; `storeObject_declassificationTaint_eq` | `Model/State.lean` | M |
| SM9.D.3 | Freeze carriage: required `FrozenSystemState` field, `freeze` forwarding, `freeze_preserves_*`, the `apiInvariantBundle_frozenDirectFull` conjunct + bullet | `Model/FrozenState.lean`, `Model/FreezeProofs.lean` | M |
| SM9.D.4 | The `FrozenSystemState` test literals (the same six SM9.B.5 touches) | `tests/*Suite.lean` | S |
| SM9.D.5 | `OffSchedulerAgrees` clause + **all six** builders; boot frames ×4 | `IPC/Invariant/LookupCongruence.lean`, `Platform/Boot.lean` | M |
| SM9.D.6 | Information flow: `declassificationTaint_write_preserves_projection := rfl`; `onCore_declassificationTaint`; the §3.7 inventory row recording that it is **not readable** and therefore owes no equivalence clause yet | `InformationFlow/Invariant/Operations.lean`, `ObservableStatePerCore.lean` | M |
| SM9.D.7 | **The content-flow inventory** — `ContentFlowSite` as data + `all` / `mem_all` / `all_nodup` + the completeness theorem.  The soundness keystone: propagation that misses a content-moving transition is a detector that misses real laundering | `InformationFlow/Taint.lean` | L |
| SM9.D.8 | Propagation at IPC send/receive (message registers → receiver TCB), single-core and `…OnCore` | `IPC/Operations/Endpoint.lean`, `IPC/CrossCore/EndpointSend.lean` | L |
| SM9.D.9 | Propagation at call / reply / replyRecv, including the cross-core dispatch wrappers | `IPC/CrossCore/{EndpointCall,EndpointReply}*.lean` | L |
| SM9.D.10 | Propagation at notification signal — **where SM9.C's downgrade originates a tag** — plus the bound-TCB delivery path | `IPC/CrossCore/NotificationSignal.lean` | L |
| SM9.D.11 | Propagation at capability transfer (`ipcUnwrapCaps`) | `IPC/Operations/CapTransfer.lean` | M |
| SM9.D.12 | Taint **frames** for every non-content transition (scheduler, VSpace, lifecycle, cache/TLB), so D.7's completeness is checkable rather than declared | ~12 files | L |
| SM9.D.13 | Saturation: the structural bound, upward-saturating overflow, `taintSaturate_over_approximates` (the safe direction for a detector, stated as a theorem) | `InformationFlow/Taint.lean` | M |
| SM9.D.14 | `declassificationChainCausal` — hop 2's source object's taint contains hop 1's timestamp — conjoined into `declassificationChainLinked` | `InformationFlow/DeclassificationPerCore.lean` | L |
| SM9.D.15 | **Retire `declassificationChainLinked_is_syntactic`** (now genuinely false) for a soundness theorem on the causal detector; a negative pinning the residual saturation-induced over-approximation, so the remaining imprecision is stated rather than implied absent | same | M |
| SM9.D.16 | `chainLaunders` consumes it; the rule-inventory `evidenceProp` moves with the theorem; counts + Tier-3 anchors incl. the retirement negative | same | M |
| SM9.D.17 | Lock sets and write sets: the propagation writes sit inside existing transitions, so declared footprints and `permittedKinds` grow with them; inventory counts | `Concurrency/Locks/*` | L |
| SM9.D.18 | NI carriage: propagation is projection-invisible, but every touched transition's write set moves, so `observableSlotsConfinedToCores` proofs and the cross-core inventory need the new frames | `InformationFlow/NonInterference{PerCore,CrossCore}.lean` | L |

### SM9.E — Tests + closure (3-4 PRs, 7 sub-tasks)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| SM9.E.1 | Runtime groups §9 (SM9.A), §10 (SM9.B), §11 (SM9.C), §12 (SM9.D) — every group with a load-bearing negative | `tests/SmpInformationFlowSuite.lean` | XL |
| SM9.E.2 | **The cliff acceptance scenario**: fill the trail to `maxDeclassificationAuditEntries`, observe `.declassify` failing with `.auditLogCapacityExceeded`, drain via `.auditDrain`, observe it succeeding again — and, post-drain, that the next event's timestamp does **not** collide with a surviving entry (the SM9.A.1a epoch, exercised rather than asserted); plus a denied-`.declassifySignal` case proving the §3.1 seam filter covers both declassifying syscalls | same | L |
| SM9.E.2a | **The causal-detector acceptance scenario** (SM9.D): the §3.6 chain — downgrade writes a badge into a notification, an *ordinary* delivery moves it to a waiter TCB, that thread downgrades again — detected as laundering, with the two load-bearing negatives that a domain-only detector produces a false positive on an unrelated pair and an object-adjacency detector produces a false negative on this very chain | same | L |
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
| The refusal ledger becomes a channel | LOW | HIGH | No distinguishable capacity reason; outside `ObservableState`; **readable only under full dominance** (§3.2), so a hidden write cannot evict a partial reader's entry or move its counters; `_denied_before_capacity` re-verified as an SM9.B acceptance item |
| A readable structure is added with no equivalence clause | MED | HIGH | §3.7's `ReadableStructure.all` + `mem_all` — a structure without a clause fails completeness rather than passing silently.  Three findings so far were the same violation seen at three sites |
| Drain breaks the trail's timestamp discipline | HIGH | HIGH | **Realised, not hypothetical**: `timestamp := log.length` reuses a timestamp after any prefix removal.  Closed by the SM9.A.1a epoch, sequenced before drain exists, with the reuse as a load-bearing negative (§3.4) |
| Taint propagation misses a content-moving transition | MED | HIGH | `ContentFlowSite.all` + `mem_all` + non-content frames (SM9.D.7/.12) — a missed site is a detector that misses real laundering, so the enumeration is checked, not asserted |
| SM9.D's size swamps the phase | HIGH | MED | Acknowledged in the estimate rather than absorbed: 18 sub-tasks, 6-8 PRs, and the phase moved 6-9 → 12-16 weeks.  Sequenced in four blocks so mount, propagation and detector land separately |
| The reader leaks hidden-entry counts through index gaps | LOW | HIGH | Re-indexed filtered view, not sparse global indices; the visible view is a function of the reader's clearance alone; **drain requires full dominance** so there is no partial-visibility prefix to probe (§3.4) |
| A global drain generation signals a dominating monitor's drains to every reader | MED | HIGH | `drainGeneration` is observer-scoped (§3.3), with the negative that a global counter is refutable |
| The reader's flow argument is stated over a relation that cannot see the trail | MED | HIGH | `lowEquivalent` does not imply equal visible views once a reader exists — the naive lemma is **false** (§3.4a).  `auditObservationalEquivalence` is the relation SM9.A.4a/.4b are stated over |
| A read word aliases the ABI error flag | MED | MED | The payload is **63** bits (`encodeOk` masks bit 63); unbounded fields are chunked; `auditReadWord_fits_payload` (§3.3) |
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
- [ ] `authorizeDeclassificationOnCore_denied_before_capacity` still holds, and
      the suite's trail-occupancy negative still passes.
- [ ] A data-carrying declassification exists, with
      `declassificationRelativeNonInterference` in both halves.
- [ ] Timestamps survive drains: after a drain, a fresh event's timestamp
      collides with no surviving entry, and the well-formedness contract names
      the epoch rather than claiming index-anchoring.
- [ ] Every field the reader exports is reconstructible from its chunks, not
      merely small enough to survive `encodeOk`.
- [ ] Every readable structure has an equivalence clause and a hidden-write
      non-interference argument (§3.7), checked by `mem_all` rather than by
      review.
- [ ] Both declassifying syscalls reach the refusal seam, proven by
      `declassificationSyscalls_complete` and exercised by a denied
      `.declassifySignal`.
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

~45 substantive theorems.  Headline set:

- `auditLogVisibleTo_sublist` + the clearance-determines-view theorem (SM9.A.1)
- `auditTimestampsFrom_epoch_preserved` + `auditDrain_monotone_epoch` — the
  timestamp epoch, and the negative that the pre-epoch `log.length` producer
  **reuses** a timestamp after a drain (SM9.A.1a)
- `auditReadField_reconstructs` — folding a field's chunks recovers the value;
  the losslessness claim (SM9.A.2)
- `auditReadWord_fits_payload` — every returned word is `< 2^63`, so `encodeOk`
  is the identity on it; the **ABI-safety** half, explicitly not losslessness
  (SM9.A.2)
- `auditReadStatus_generation_observer_scoped` + the negative that a global
  drain counter is refutable (SM9.A.2)
- `auditDrain_requires_full_dominance` (SM9.A.3)
- `auditDrainVisiblePrefix_preserves_auditLogBounded` +
  `_preserves_wellFormed_at_epoch` + `_fully_clears_for_dominating_reader`
  (SM9.A.3)
- `auditObservationalEquivalence` over `ReadableStructure.all` + `mem_all` + its
  congruences, and the negative that plain `lowEquivalent` does **not** imply
  equal visible views (SM9.A.4a, §3.7)
- `auditRead_no_channel` — the reader's flow argument, over that relation
  (SM9.A.4b)
- `extractAuditAuthority_rejects_non_audit_capability` (SM9.A.9)
- `auditRead_stable_under_append` (SM9.A.5)
- `recordRefusal_saturates` / `_no_loss` / `_ring_wraps_counted` (SM9.B.2)
- `refusalLedger_requires_full_dominance` + the negative that a partially-cleared
  caller reads nothing of it (SM9.B.10, §3.7)
- `declassificationSyscalls_complete` — every syscall consulting
  `declassificationDecision` reaches the refusal seam (SM9.B.9)
- `refusalWrite_declassificationAuditLog_eq` (SM9.B.9)
- `declassificationRefusals_write_preserves_projection` +
  `onCore_declassificationRefusals` (SM9.B.8)
- `notificationSignalDeclassified_preserves_ipcInvariantFull{,_perCore}` (SM9.C.3)
- **`declassificationRelativeNonInterference`** (SM9.C.6) — the phase headline
- `contentFlowSites_complete` — the taint-propagation soundness keystone
  (SM9.D.7)
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
