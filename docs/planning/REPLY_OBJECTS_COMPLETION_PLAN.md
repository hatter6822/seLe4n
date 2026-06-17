# Reply Objects (seL4-MCS) — Completion Plan: deferred Phase-C-invariants / D6 / H items

> Companion to the SM6.C/SM6.D reply-object slices in
> [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md) and the
> in-flight PR #822 hardening pass (landed v0.31.132–v0.31.138). This plan covers
> the three remaining **completeness** items — the Prop-invariant / ABI tail.

## Context & status

The reply-object workstream landed the first-class `Reply` object, single-use
`.replyCap rid` capabilities, faithful Call/Receive/Reply/ReplyRecv linkage, the
cross-core dispatch, and the full PR-#822 hardening pass. Three items remain. **All
three are fail-closed-safe at runtime today** — the live `.reply` path rejects a
dangling reply cap via `getReply?`, and the live dispatch always links `replyObject`
— so these close **model/ABI completeness gaps, not safety holes**.

| # | Item | Layer | Codex thread(s) |
|---|------|-------|-----------------|
| **#2** | retype → reply-cap authority | ABI (Phase H) | "Produce a reply cap for retyped Reply objects" |
| **#1** | `replyCapPointsToValidReply` | Capability invariant (Phase C-inv) | "Cover replyCap targets in lifecycle invariants" / "Extend lifecycle invariants to cover reply caps" |
| **#7** | `blockedOnReply ⇒ replyObject` | IPC invariant + transitions (Phase D6) | "Require blocked replies to name a Reply object" |

## Sequencing: #2 → #1 → #7

- **#2 first** — most self-contained (an ABI feature); unblocks dynamically-usable
  Reply caps and establishes the `.replyCap`-from-retype production path that #1's
  invariant reasons about as "backed".
- **#1 second** — the Prop-invariant completeness; cleanest once the cap-acquisition
  story (#2) is settled so the invariant covers the production path.
- **#7 last** — the deepest re-base (fold reply-linking into the IPC transitions);
  the plan's D6 contract, the natural culmination.

---

## #2 — retype → reply-cap authority

**Problem.** `lifecycleRetypeDirect` (`RetypeWrappers.lean:246`) retypes an ObjId
**in place**: the authority cap stays `.object target` while the object becomes
`.reply`. `resolveRecvReplyId`/`extractReplyId` require `.replyCap rid`, so a retyped
Reply's `.object` cap yields `.invalidCapability` — dynamically-retyped Reply objects
are unusable; only boot-preinstalled reply caps work.

**Optimal approach (decision).** Add a verified **mint-reply-cap** production path: a
`cspaceMint`-family op that, given an `.object target` cap (with `.write`/`.retype`
right) where `target` holds a `.reply` object, installs `.replyCap (ReplyId.ofObjId
target)` into a destination slot — CDT-tracked exactly like `cspaceMint`. Authority:
the holder of the `.object` cap to the Reply object may derive its reply cap (the
object *is* the reply object). Single-use semantics unchanged (consume clears
`reply.caller`).

*Alternative considered + rejected:* make `extractReplyId` accept an `.object target`
cap that points at a `.reply` — rejected; it dilutes the deliberate `.replyCap`
authority distinction the C-wire swap established.

**Green sub-steps**
- **#2.a** — `mintReplyCap` in `Capability/Operations.lean` (resolve `.object target`
  → require `getReply? (ReplyId.ofObjId target) ≠ none` → CDT-tracked insert
  `.replyCap rid` at dst) + spec lemmas mirroring `cspaceMint`.
- **#2.b** — `mintReplyCap_preserves_capabilityInvariantBundle` (it inserts a
  `.replyCap` whose rid is backed by construction — depends only on the existing
  6-tuple until #1 adds the 7th conjunct).
- **#2.c** — ABI: `mintReplyCap` SyscallId + decode + dispatch arm + Rust
  `sele4n-types`/`sele4n-hal` mirror + conformance.
- **#2.d** — end-to-end test: retype Untyped→Reply, `mintReplyCap`, use the resulting
  `.replyCap` in `endpoint_receive_with_reply`.

---

## #1 — `replyCapPointsToValidReply`

**Problem.** The step-preserved `capabilityInvariantBundle` (and
`lifecycleStaleReferenceExclusionInvariant`) only constrain `.object` cap targets; a
`.replyCap rid` slot pointing at an absent/non-Reply object satisfies them while live
`.reply` rejects it. The model admits a dangling reply cap. (The runtime check
`cspaceSlotCoherencyChecks` in `InvariantChecks.lean` already validates
`.replyCap rid => getReply? rid .isSome`; only the **Prop** invariant is blind.)

**Optimal approach.** Add, mirroring the runtime check:
```
def replyCapPointsToValidReply (st) : Prop :=
  ∀ oid cn slot cap rid, st.objects[oid]? = some (.cnode cn) →
    cn.lookup slot = some cap → cap.target = .replyCap rid → st.getReply? rid ≠ none
```
as the **7th conjunct of `capabilityInvariantBundle`** (`Capability/Invariant/Defs.lean:176`)
— the only *step-preserved* home (`cdtMintCompleteness` and the cross-subsystem
composition are **boot-only**, so adding there is vacuous-enforcement). Follow the
AN4-F.5 named-projection idiom: tuple + `structure CapabilityInvariantBundle` field +
bidirectional bridge + `@[simp]` projection abbrev.

**Preservation (uniform).**
- Cap ops change CNodes, not Reply objects ⇒ `getReply? rid` frame-stable; an inserted
  `.replyCap` copies a backed source (or #2.a's mint, backed by construction) ⇒ backed.
- Delete/revoke remove caps ⇒ fewer reply caps ⇒ preserved.
- Retype: `lifecyclePreRetypeCleanup` + CDT-revoke remove a Reply's caps before destroy
  ⇒ no dangling.

**Green sub-steps**
- **#1-prep (LANDED)** — define `replyCapPointsToValidReply` + `_of_objects_eq` frame
  (`Capability/Invariant/Defs.lean`, after the `capabilityInvariantBundle` projections).
  Standalone-green; not yet bundled.
- **#1.b (the keystone — do BEFORE #1.a)** — the preservation lemmas, so #1.a's tuple
  expansion is mechanical. **Key unifying insight:** most cap ops delegate to
  `cspaceInsertSlot_preserves_capabilityInvariantBundle`, so extend the predicate's
  preservation via the *one* lemma `cspaceInsertSlot_preserves_replyCapPointsToValidReply
  (… hCapBacked : ∀ rid, cap.target = .replyCap rid → st.getReply? rid ≠ none …)` and let
  `cspaceCopy`/`Move`/`Mint`/`mintReplyCap`/`ipcUnwrap` discharge `hCapBacked` (the inserted
  cap copies a backed source, or — for `mintReplyCap` — is backed by construction).
  **Proof argument (worked out):** a CNode store never affects `getReply?` (it reads only
  `.reply` objects; the stored object is a `.cnode`), so `st'.getReply? rid = st.getReply?
  rid`; then case-split the post-state reply cap `(oid, slot)` — if `oid = addr.cnode` use
  `CNode.lookup_insert_eq` (slot = addr.slot ⇒ the inserted cap, backed by `hCapBacked`) /
  `lookup_insert_ne` (slot ≠ addr.slot ⇒ a pre-existing cap, backed by the pre-invariant);
  if `oid ≠ addr.cnode` the slot is unchanged (pre-invariant).  `cspaceDeleteSlotCore` (and
  revoke) only *remove* caps ⇒ trivially preserved.  Then the per-op `_preserves_*` theorems
  build the 7th conjunct from these.
- **#1.a (contract)** — add `replyCapPointsToValidReply` as the 7th `capabilityInvariantBundle`
  conjunct (tuple `… ∧ st.objects.invExt ∧ replyCapPointsToValidReply st`): the FIRST FIVE
  `@[simp] abbrev` projections are unchanged (prefixes); only `objectsInvExt` shifts
  `.2.2.2.2.2 → .2.2.2.2.2.1` and the new projection is `.2.2.2.2.2.2`.  `lake build` to
  enumerate the ~60 construct/destructure breaks (each preservation theorem appends the #1.b
  witness; raw `⟨…6…⟩` destructures gain a 7th binder), fix systematically.
- **#1.c** — `default_capabilityInvariantBundle` (`Architecture/Invariant.lean`) gains
  `default_replyCapPointsToValidReply` (empty objects ⇒ vacuous); `Boot.lean` carries it
  (boot has no reply caps); `crossSubsystemInvariantWithCdtCoverage` threads it.
- **#1.d** — `ModelIntegritySuite` test: dangling reply cap rejected by the Prop predicate;
  backed reply cap admitted.

**Risk.** The tuple expansion (#1.a) is atomic (one commit). Mitigate: do #1.b FIRST (the
preservation lemmas exist), then change the def, `lake build` to enumerate every break, fix
systematically, commit only when fully green.

---

## #7 — `blockedOnReply ⇒ replyObject` (D6 contract)

**Problem.** `replyCallerLinkage` (`IPC/Invariant/Defs.lean:~623`) only constrains TCBs
that *already* have `replyObject` set; `ipcInvariantFull` admits `.blockedOnReply` with
`replyObject = none`. The raw single-core `endpointCall`/`endpointReceiveDual` produce
exactly that intermediate (the caller blocks before the server-supplied reply cap is
linked by the **separate** dispatch step `linkServerFirstCaller`/`linkReceivedCaller`).

**Root cause.** Reply-linking is a *dispatch-layer* step composed **after** the blocking
transition; the rid is server-supplied and unknown to the raw transition. So
`blockedOnReply ⇒ replyObject` holds at **syscall boundaries**, not **transition
boundaries** — and `ipcInvariantFull` is a transition-level invariant.

**Optimal approach (faithful seL4-MCS fold).** Make reply-linking **atomic** with the
blocking transition by threading the resolved `rid` into the receive/call transitions, so
the dequeued `Call` caller is set `.blockedOnReply` **and** `replyObject := some rid` in
one store. `blockedOnCall` (the enqueue path, no server yet) carries no reply and is
*excluded* from the new clause; the later dequeue→`blockedOnReply` transition links the
rid atomically.

**Green sub-steps (parallel-change)**
- **#7.a** — thread `replyId : Option ReplyId := none` through `endpointReceiveDual{,OnCore}`
  + `endpointCall`'s server-waiting rendezvous; set `replyObject` in the same store that
  sets `.blockedOnReply` (defaulted ⇒ existing call sites unchanged; the dispatch passes the
  resolved rid). Re-prove the transition preservation suite additively.
- **#7.b** — **remove** the now-redundant separate `linkReceivedCaller`/`linkServerFirstCaller`
  dispatch composition (per the standing "remove redundant code" directive) once the
  transition links atomically.
- **#7.c** — strengthen `replyCallerLinkage` with the third clause
  `(∀ tid tcb ep rt, getTcb? tid = some tcb → tcb.ipcState = .blockedOnReply ep rt →
  ∃ rid, tcb.replyObject = some rid)`; update `default`/`boot`/frame + the 3 concrete
  `linkCallerReply`/`consumeCallerReply` preservation proofs + the folded transitions.
- **#7.d** — tests: the receive/call transitions establish `blockedOnReply ⇒ replyObject`
  directly; no raw transition produces an unanswerable state.

**Risk.** Highest of the three (SM6.A/C transition + preservation surface). Parallel-change
keeps each sub-step green: #7.a is additive (defaulted param), #7.b removes now-dead steps,
#7.c strengthens the invariant only once the transitions establish it.

---

## Verification (every sub-step)

Per-module `lake build`; `/tmp/smoke_lean.sh` (Tier 0–2); `test_tier3_invariant_surface.sh`
for invariant changes (#1.a, #7.c); assert trace byte-identical; `bump_version.sh` +
`CHANGELOG.md`; regenerate `docs/codebase_map.json`. Rust ABI mirror (#2.c) verified via
`cargo check --profile test` (cargo test hangs in-container; CI runs the full suite).

## Out-of-scope / tracked debt
- Reply-cap **rights/badge** model (seL4 reply caps are rights-less) — confirm after #2.
- Full HW-tier reply-lock contention stress — CI/QEMU.

Refs: docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md (SM6.C/SM6.D Reply objects)
