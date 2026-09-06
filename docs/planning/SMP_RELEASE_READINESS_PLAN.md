# WS-RR — SMP Release Readiness (pre-SM10 remediation)

> **Status**: IN FLIGHT — **RR0 LANDED at v0.34.26** (all eleven sub-tasks);
> **RR1 LANDED at v0.34.41** (all twelve sub-tasks); **RR2 LANDED at v0.34.42**
> (all twenty sub-tasks; RR2.18 partial — see its acceptance note);
> **RR3 LANDED at v0.34.43** (all twenty-six); **RR4 LANDED at v0.34.44** (all
> twenty-seven); **RR5 LANDED at v0.34.48** (all eighteen);
> **RR6 LANDED at v0.34.50** (all twenty-seven).  **RR7 IN FLIGHT**:
> RR7.1–RR7.4 landed at v0.34.57, RR7.26–RR7.27 at v0.34.58 (and RR7.6 at
> v0.34.47); RR8 not started.
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Source register**: [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) (171 confirmed findings)
> **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10) — opens when this phase closes
> **Audited cut**: `v0.34.3`
> **Target releases**: v0.35.0 → v0.99.x (SM10 then cuts v1.0.0)
> **Sub-task count**: 187 across 9 phases (RR0..RR8), each phase numbered in
> the order it is to be implemented

## 1. Phase goal

WS-RR closes everything the pre-SM10 completeness audit found open, so that
SM10 can be the release-closure phase it was scoped as rather than a phase
that discovers its own prerequisites are unmet.

The audit's verdict was that the project is **not** ready to begin SM10: three
findings block starting it, SM10's own scope statement is wrong, and a set of
fail-open latents become reachable exactly when the boot path goes live. None
of that is a "the proofs are missing" problem — SM0..SM9 are substantively
real — so this phase is remediation and completion, not new architecture.

**Concrete deliverables**, in the order the phases deliver them:

1. **RR0** — every open workstream carries a durable registry entry with a
   closure target, so no phase can close over work nobody is tracking.
2. **RR1** — aarch64 code is compiled somewhere, so the 67 cfg-gated blocks
   and 57 `asm!` sites SM10.1 depends on are not first exercised at
   image-build time; the result also sizes SM10's estimate.  (This bullet
   read "60 `asm!` sites" until RR1.10 measured it: 60 was a transcription
   of the register's 59, which counted two docstring mentions of the token.
   57 is the figure over the comment-free code view.)
3. **RR2** — the four live SMP dispatch arms carry `ipcInvariantFull`
   bundles, and cross-core SchedContext donation migrates the CBS replenish
   queue.
4. **RR3** — `ipcInvariantFull` is end-to-end machine-checked: no bundle
   carries a post-state conjunct as a hypothesis, and the top-level dispatch
   payoff theorems exist.
5. **RR4** — full seL4-style fault IPC with reply-based restart, so a
   faulting thread can never livelock its core.
6. **RR5** — the boot path fails closed: a production labeling context is
   required, the readiness gate covers every seam, idle threads are
   installed, and the kernel entries a linked image needs are
   production-reachable.
7. **RR6** — the verified lock primitives match their deployed Rust
   counterparts: refinement against the real locks, not transliterations.
8. **RR7**, then **RR8** — the medium-severity findings are closed, and the
   phase hands SM10 a green, registered, accurate starting state.

## 2. Scope and sequencing

### 2.1 What this phase covers, and what it hands to SM10

The audit produced 171 confirmed findings. They are divided by **who is best
placed to close them**, not by severity alone:

| Finding class | Count | Owner | Rationale |
|---------------|-------|-------|-----------|
| Blockers | 3 | RR0, RR2 | SM10 cannot correctly start over them |
| Security / soundness | 11 | RR4, RR5, RR6, RR7 | Become reachable when the boot path goes live |
| High (other) | 12 | RR1..RR6 | Real incomplete work in phases marked complete |
| Medium | 46 | RR7 (and RR0..RR6 where thematic) | Genuine gaps SM10 would otherwise absorb |
| Low | 99 | RR0.11 triage → **SM10.2**, RR7.33–RR7.37, or the debt register | Triaged at v0.34.26 (register §7.1): 20 closed by the RR0 cut, 9 closed by registration, 18 already owned by a phase reworking the same artefact, **15 needed code and became RR7.33–RR7.37**, 37 are SM10.2's work-list |

Most of the 99 lows are documentation drift, and those are deliberately **not**
duplicated into this phase: re-homing a documentation sweep into a remediation
phase, and then running SM10.2's sweep over the same files, is two passes for
one outcome.

But the section is **not** uniformly doc-sync, and handing it wholesale to a
documentation sweep would let real work reach release closure as prose. At
least fourteen rows are classed `improvement`, `debt`, `gates` or `bootpath` —
finding 98, for instance, is four per-core statistics accessors that are
declared, wrapped and proven with zero consumers, which is an
implement-the-improvement case, not a stale sentence; finding 8 in §4 is a
`soundness` item that happens to carry low severity. RR0.11 therefore
**triages** §7 before handing anything over: doc-sync rows go to SM10.2 as its
work-list, and every row that needs code, a proof or a wiring change becomes a
numbered RR7 row or an explicitly registered deferral with an owner. A low
severity means the consequence is small, not that the remedy is a sentence.
**Triage result at `v0.34.26`** (register §7.1, per-row): 20 closed by the RR0
cut, 9 closed by registration in the debt register, 18 already owned by a phase
reworking the same artefact, **15 routed to new rows RR7.33–RR7.37**, and 37
to SM10.2's work-list — 20 + 9 + 18 + 15 + 37 = 99.

### 2.2 Why a separate phase rather than SM10 sub-tasks

SM10's acceptance gate is a release checklist: spec rewritten, chapters
published, version bumped, tag cut. Adding a fault-IPC implementation and an
invariant de-threading closure to that gate would make "is the release ready"
and "is the kernel finished" the same question, which is exactly the
conflation that let the tier-4 gates certify phases nothing had run. Keeping
them separate means SM10 can be judged on whether the release is
well-formed, and WS-RR on whether the kernel is complete.

### 2.3 Ordering constraints

**Phase number is implementation order.** RR0 runs first, RR8 last, and a
phase's number is the only sequencing signal a reader needs — there is no
separate "but actually do this one early" note, because a plan whose
numbering disagrees with its execution order is a plan that has to be read
twice. The dependencies that produced this order:

- **RR0 before everything.** Registration is cheap and stops further work
  being lost while the rest of the phase runs.
- **RR1 second, though nothing blocks on it.** The aarch64 compile check is
  cheap, and every later Rust change then lands on paths already proven to
  compile — the value is in going early, not in being a prerequisite. It also
  owns both halves of the SM10 estimate: RR1.10 records the measured aarch64
  surface and RR1.11 revises the estimate from it, in that order, so no phase
  has to reach back to a later one for its input.
- **RR2 before RR3.** The de-threading payoff theorems (RR3.24, RR3.25)
  quantify over dispatch arms that must carry bundles first.
- **RR4 before RR5, and never concurrent.** Both touch the trap and boot
  seams; running them in parallel means two phases editing the same files.
- **RR6 is independent** of everything above; it sits late because nothing
  depends on it, not because it is optional.
- **RR7 is not independent, despite being a sweep.** Several of its rows own
  findings whose primary owner is an earlier phase — RR7.25 the RwLock-deferred
  mediums that RR6 implements, RR7.28 the IPC de-threading medium RR3 closes,
  and its cross-core IPC batches touch RR2 and RR3 surfaces. It therefore runs
  **after** those phases, and its overlapping rows are verification that the
  owning phase actually closed the finding, not a second attempt at it.
- **RR8 last** by construction: it verifies the other eight.

A team with capacity to parallelise can overlap RR6 with any earlier phase, and
RR1 with RR0. **RR7 may not overlap RR2, RR3 or RR6** — it would send two
numbered tasks into the same findings and files before their owner finished.
Nothing else may overlap without re-reading the dependency list above.

## 3. Dependencies

- SM0..SM9 landed (they are; see the register's per-plan verified evidence).
- Tier 0..3 green at HEAD — true at `v0.34.3`.
- Tier 4 gate accounting honest — landed at `v0.34.2`; the gates themselves
  still cannot run until SM10.1.1 produces an image, which is SM10's work
  and deliberately not a WS-RR dependency.
- No dependency on SM10. WS-RR closes first.

## 4. Phase map

| Phase | Scope (one line) | Subs | Est |
|-------|------------------|------|-----|
| RR0 | Registration and plan correction — nothing further is lost.  **LANDED v0.34.26** | 11 | S–M |
| RR1 | aarch64 compile coverage, plus the Rust HAL gate no other phase owns.  **LANDED v0.34.41** (RR1.12 hardened the gates through six review rounds in the same cut) | 12 | M |
| RR2 | Live-path correctness: dispatch-arm bundles + donation queue migration, wired live.  **LANDED v0.34.42** | 20 | M–L |
| RR3 | `ipcInvariantFull` de-threading closure (D1, D6, D8).  **LANDED v0.34.43** (RR3.1–RR3.26, the dispatch payoff included) | 26 | XL |
| RR4 | Fault handling: full fault IPC with reply-based restart.  **LANDED v0.34.44** (RR4.1–RR4.27) | 27 | XL |
| RR5 | Boot-path fail-open closure.  **LANDED v0.34.48** (RR5.1–RR5.18) | 18 | M–L |
| RR6 | Verified lock primitives completion (SM2.C-defer, pre-v1.0.0).  **LANDED v0.34.50** (RR6.1–RR6.27) | 27 | L |
| RR7 | Medium-severity sweep, plus the §7 rows RR0.11 routes here | 41 | M |
| RR8 | Phase closure and hand-off to SM10 | 5 | S |

## 5. Sub-tasks

Estimates: **T** trivial (<1h) · **S** small (<½ day) · **M** medium (1–2 days)
· **L** large (3–5 days) · **XL** extra-large (>1 week, expect to split further).
Each sub-task is sized to be one coherent PR or less, per the PR checklist.

### RR0 — Registration and plan correction

Cheap, ordered first, and load-bearing: every later phase assumes the
register is accurate. RR0.1–RR0.3 close audit blocker 1's registration half.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR0.1 | Add an IPC de-threading workstream row to `docs/REGISTERED_DEBT.md` recording per-slice state (D0/D2/D2′/D3/D4/D5/D7 closed; D1/D6/D8 open) with closure target RR3 | `docs/REGISTERED_DEBT.md` | S |
| RR0.2 | Add it to `SMP_RELEASE_CLOSURE_PLAN.md` §2 Dependencies | (1 file) | T |
| RR0.3 | Add a CLAUDE.md standing-constraint bullet naming the two still-threaded conjuncts, so new code does not assume `ipcInvariantFull` is end-to-end machine-checked; mirror to `AGENTS.md` | `CLAUDE.md`, `AGENTS.md` | S |
| RR0.4 | Rewrite `SMP_RELEASE_CLOSURE_PLAN.md` §1 phase goal against the real SM10.1 scope (§2.2 of the register) | (1 file) | S |
| RR0.5 | Add the missing SM9 term to the §5 theorem tally | (1 file) | T |
| RR0.6 | Replace the hand-summed `wsm_theorem_count` literal with a generated manifest, so the marker theorem cannot certify a stale number | `scripts/`, `SeLe4n/Kernel/Concurrency/` | M |
| RR0.7 | Correct the SM10.6.3 archive list: add the SM9 plan, this plan, and the register; update the file-move count | (1 file) | T |
| RR0.8 | Refresh the SM10.3 sub-task table against the tree — five of six suites and two of three fixtures already exist | (1 file) | S |
| RR0.9 | Register the remaining unregistered debt the debt sweep found, each with an owner and closure target | `docs/REGISTERED_DEBT.md` | M |
| RR0.10 | Fix SM4.C.11's circular closure target (the phase that owns it is marked LANDED); re-home it to a phase that can close it | (2 files) | S |
| RR0.11 | Triage the register's §7 low-severity table by remedy, not by severity: rows fixed by editing prose become SM10.2's documentation work-list (cross-referenced from `SMP_RELEASE_CLOSURE_PLAN.md`); rows needing code, a proof or a wiring change become numbered RR7 rows or registered deferrals with owners. Handing all 99 to a documentation sweep would close the release over unwired proven structures | (2 files) | S |

**Acceptance**: `grep` for each open workstream name returns a hit in
`docs/REGISTERED_DEBT.md`; no plan in `docs/planning/` lacks a status
header; the SM10 tally arithmetic includes every landed phase.

**Met at `v0.34.26`.**  Every plan under `docs/planning/` is cited from
`docs/REGISTERED_DEBT.md` and carries a status header — five did not, and
two (`SMP_PANIC_HANG_REMEDIATION_PLAN.md`,
`WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md`) were cited from nowhere.  The SM10
tally is no longer arithmetic at all: `smpInventoriedTheoremCount` is a
`List.sum` over one manifest entry per phase SM0..SM10, and
`smpPhaseTheoremManifest_covers_all` makes an omitted phase fail elaboration —
so "includes every landed phase" is now a proof obligation rather than a
property of a sentence.  Two open workstreams that existed only as plan files,
**WS-DT** and **WS-SL**, are registered with owners and closure targets, and
the *Registered debt index* gives every deferred item a home.


### RR1 — aarch64 compile coverage

Cheap, early, and it de-risks every later Rust change. At the audited cut no
aarch64 target was compiled anywhere in the tree or CI, so 67 cfg-gated
blocks, 57 `asm!` sites and all three `.S` files had **zero** compile
coverage. SM10.1 would otherwise have been the first thing that ever compiled
them, while also being the first thing that linked and booted them. (Present
tense throughout the rows below is the plan as written; what landed is in
*Met at `v0.34.41`* after the acceptance.)

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR1.1 | Add the `aarch64-unknown-none` target to the Rust toolchain file | `rust/rust-toolchain.toml` | T |
| RR1.2 | Run `cargo check --target aarch64-unknown-none -p sele4n-hal --features hw_target` **from `rust/`** and record the complete error inventory — this is the diagnostic pass, not a green gate; `rust-toolchain.toml` lives under `rust/`, so rustup's directory override selects the pinned toolchain only inside it, and `--manifest-path` from the repo root silently uses the default toolchain that RR1.1 never added the target to | `rust/sele4n-hal/` | M |
| RR1.3 | Fix what it surfaces in the cfg-gated blocks | (same) | L |
| RR1.4 | Fix what it surfaces in the `asm!` sites | (same) | L |
| RR1.5 | The cross target now **builds**: `cargo build --target aarch64-unknown-none -p sele4n-hal --features hw_target` is clean from `rust/`, with the RR1.2 inventory discharged. **`--features hw_target` is not optional here**: the feature is empty by default and guards the hardware-only paths — the Lean calls in `timer.rs`, `trap.rs` and `smp.rs` — so a build without it compiles none of the code this phase exists to cover, and later regressions in exactly those cfg-gated blocks would merge with the aarch64 gate green. `cargo check` stops before code generation, so it never reaches the backend and cannot surface an `asm!` or codegen error — the diagnostic pass uses `check` for speed, but the gate must be a real build | `rust/sele4n-hal/` | M |
| RR1.6 | Assemble the three `.S` files under the cross target | `rust/sele4n-hal/build.rs` | M |
| RR1.7 | CI job running `cargo build --target aarch64-unknown-none -p sele4n-hal --features hw_target` on every PR — a build not a `check`, for the codegen reason in RR1.5, and with the feature named, since without it the job compiles none of the hardware-only paths and stays green through a regression in them | `.github/workflows/` | M |
| RR1.8 | Tier 0 check that the cross target stays configured, so it cannot be silently dropped | `scripts/test_tier0_hygiene.sh` | S |
| RR1.9 | Implement the Tier-0 grep gate banning non-IS TLBI that `SMP_RUST_HAL_PLAN.md` §4.4 claims exists — a high finding that no other phase owns, and Rust HAL hygiene like the rest of this phase | `scripts/test_tier0_hygiene.sh` | M |
| RR1.10 | Record the measured aarch64 surface in the register — the input the next sub-task consumes | `docs/planning/UNFINISHED_SMP_WORK.md` | S |
| RR1.11 | Revise SM10's calendar estimate from that measurement, replacing the plan's 4–6 week guess with a figure derived from the real aarch64 surface | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | S |
| RR1.12 | Give the Rust-scanning gates a shared structural view, so a check about a program stops being answered by a slice of text.  Consumes RR1.8 and RR1.9, whose scanners it re-points: one quote-aware Rust code view (`scripts/rust_code_view.py`, and `rust_code_views` in `build.rs` for the build script, which cannot import it), plus a shell command/argv layer so a flag is read on the command that receives it.  The self-test harnesses additionally require every check to carry a token-preserving negative case, since stating that rule in `CLAUDE.md` did not stop the following round from shipping eight more presence-for-relation substitutions | `scripts/rust_code_view.py`, `scripts/check_aarch64_cross_target.py`, `scripts/check_tlbi_broadcast_discipline.py`, `rust/sele4n-hal/build.rs` | M |

**Acceptance**: `cargo build --target aarch64-unknown-none -p sele4n-hal
--features hw_target` passes in CI — a real code
generation over all 57 `asm!` sites, not a type-check that stops before the
backend; the `.S` files assemble; SM10.1's estimate is derived from a real
compile rather than a guess.

**Met at `v0.34.41`.**  `scripts/test_aarch64_cross_build.sh` builds the
crate for `aarch64-unknown-none` in **both** profiles, verifies all three
`.S` sources reached the archive rather than assuming the assembly step
ran, and lints the cross target with `-D warnings` — the lane where every
`#[cfg(target_arch = "aarch64")]` block lives, and which the host-only
clippy pass had excluded from the project's zero-warning claim.  CI runs it
as the `aarch64 Cross Build` job on every PR;
`scripts/check_aarch64_cross_target.py` (Tier 0, with a 14-case self-test)
keeps the target, the feature flag and the `build`-not-`check` choice from
being dropped or weakened; and `scripts/check_tlbi_broadcast_discipline.py`
(Tier 0, 12-case self-test) implements the §4.4 TLBI gate RR1.9 owed.

*Met. What the cut changed, the defects it found and its review rounds are in
[`CHANGELOG.md`](../../CHANGELOG.md) at the version above.*

### RR2 — Live-path correctness

Closes audit blockers 2 and 3. Both are implement-the-improvement cases whose
groundwork is already staged, and this phase is a prerequisite for RR3's
payoff theorems.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR2.1 | Add `applyCallDonationOnCore` threading donor and donee home cores | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | M |
| RR2.2 | Call `migrateSchedContextReplenishment` from it (donor home → donee home), mirroring the cancellation path that already does this | (same) | M |
| RR2.3 | Prove the call path preserves the SM5.H affinity invariant | `SeLe4n/Kernel/SchedContext/` | M |
| RR2.4 | Extend `lockSet_endpointCall` with `migrateSchedContextReplenishmentLockSet` (both home cores' replenish queues) and re-prove its coverage. Without this the migration writes scheduler queues outside the declared `withLockSet` footprint, which invalidates the SM3 serializability argument | `SeLe4n/Kernel/IPC/CrossCore/EndpointCall.lean` | L |
| RR2.5 | Invariant-preservation theorems for the donation primitives themselves, which carry none today — required before either live switch below, since after them the primitives sit on a reachable path | `SeLe4n/Kernel/IPC/Operations/Donation.lean` | L |
| RR2.6 | `endpointCallCrossCoreDispatch` preservation bundle | `SeLe4n/Kernel/IPC/CrossCore/` | M |
| RR2.7 | Replace the live `applyCallDonation` call in `endpointCallCrossCoreDispatch` with `applyCallDonationOnCore`, threading the resolved home cores. Adding and proving the helper leaves the reachable `.call` path still unmigrated — this is the sub-task that closes the blocker rather than modelling it | `SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean` | M |
| RR2.8 | Add the mirror migration inside `applyReplyDonationOnCore` (replier home → original-owner home) | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | M |
| RR2.9 | Prove the reply path preserves the affinity invariant | (same) | M |
| RR2.10 | Extend `lockSet_endpointReply` with the same migration footprint and re-prove coverage | `SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean` | L |
| RR2.11 | `endpointReplyCrossCoreDispatch` preservation bundle | `SeLe4n/Kernel/IPC/CrossCore/` | M |
| RR2.12 | Replace the live `applyReplyDonation` call in `endpointReplyCrossCoreDispatch` with `applyReplyDonationOnCore` | `SeLe4n/Kernel/IPC/CrossCore/EndpointReplyDispatch.lean` | M |
| RR2.13 | Bridge theorem: boot-core instantiation of both migrations reduces to the single-core forms | (2 files) | S |
| RR2.14 | `endpointSendDualWithCapsOnCore_preserves_ipcInvariantFull` — use the staged `endpointSendDualOnCore_bootCore_{block,rendezvous}_eq_single` rewrites | `SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean` | L |
| RR2.15 | Per-core form `…_preserves_ipcInvariantFull_perCore` | (same) | M |
| RR2.16 | `clearWokenReceiverStash` preservation bundle | `SeLe4n/Kernel/IPC/` | M |
| RR2.17 | Extend the cancellation `ipcInvariant` closure to the operation that actually runs on `.tcbSuspend` — today's claim excludes it | `SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean` | L |
| RR2.18 | Discharge the `hTeardownProj` hypothesis whose closure form returns its own premise | `SeLe4n/Kernel/IPC/CrossCore/CancellationNI.lean` | L |
| RR2.19 | Tests: donation-migration and dispatch-arm coverage; extend the cross-core IPC suite | `tests/SmpIpcSuite.lean` | M |
| RR2.20 | Migrate the replenish queue on the **third** live donation path — `.replyRecv`'s return-and-re-donate pair, which the audit's blocker 2 did not name — prove it preserves the SM5.H invariant, and carry its own suite coverage | `SeLe4n/Kernel/API.lean`, `tests/SmpIpcSuite.lean` | M |

**Acceptance**: every arm reachable from `SeLe4n/Kernel/API.lean`'s SMP
dispatch carries a `_preserves_ipcInvariantFull` theorem; the donation paths
migrate the replenish queue; no cancellation theorem rests on an
unproven teardown hypothesis.

> **RR2.20 is out of numeric execution order and says so.**  It was found during
> RR2's own closure review, after RR2.13–RR2.19 had landed and their IDs were
> already in commit messages, so renumbering would have cost more than it bought
> (see the plan-authoring rule in `CLAUDE.md`).  It introduces no backward
> dependency: it consumes RR2.1's `applyCallDonationOnCore` and RR2.9's shared
> return-plus-migration lemma, both lower-numbered, and it carries its own suite
> coverage rather than depending on RR2.19's.

**Met at v0.34.42**, with one clause partial and named as such: the three
*queue* arms of the cancellation closure still take `hTeardownProj`, which
needs an endpoint/notification queue label-uniformity invariant — a
workstream, not a sub-task.  It is registered in
[`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §4 finding 2 with closure
target **RR3**, and RR2 is recorded as landing with it open rather than as
closing a clause it did not close.

*Met. What the cut changed, the defects it found and its review rounds are in
[`CHANGELOG.md`](../../CHANGELOG.md) at the version above.*

*Met. What the cut changed, the defects it found and its review rounds are in
[`CHANGELOG.md`](../../CHANGELOG.md) at the version above.*

### RR3 — `ipcInvariantFull` de-threading closure (D1, D6, D8)

> **Status**: RR3.1–RR3.26 **LANDED** — the phase is closed.  The RR3.1 gate
> reports zero post-state bindings of any conjunct across the whole
> `_preserves_ipcInvariantFull` / `_establishes_ipcInvariantFull` family, the
> pending register is empty, and all three payoff tiers exist.  What the
> theorems say, what their quiescence packs confine and what new code may
> assume is in `CLAUDE.md`'s *Standing constraints* section; what each cut
> changed is in [`CHANGELOG.md`](../../CHANGELOG.md).
Closes [`IPC_INVARIANT_DETHREADING_PLAN.md`](../dev_history/planning/IPC_INVARIANT_DETHREADING_PLAN.md).
At authoring time its D1, D6 and D8 slices were open, two of the twenty
conjuncts were still assumed as post-state hypotheses on nearly every bundle —
`blockedThreadsPendingMessageConsistent` on 33 of 35 and
`replyCallerLinkageReciprocal` on 31 of 35 — and `ipcInvariantFull` was not
then an end-to-end machine-checked property of the live kernel; the status
blockquote above records the closure.

*Met. What the cut changed, the defects it found and its review rounds are in
[`CHANGELOG.md`](../../CHANGELOG.md) at the version above.*

The per-transition establishers for all seven base transitions already exist,
so D1's residue is module ordering rather than missing mathematics. RR3.24 and
RR3.25 depend on RR2: the payoff theorems quantify over dispatch arms that
must carry bundles first.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR3.1 | Build the de-threading gate: over the code view, report every `_preserves_ipcInvariantFull` statement that binds a conjunct applied to the **post** state, independent of binder name. Establishes the true baseline and becomes the phase's progress meter | `scripts/check_ipc_invariant_dethreading.py` (new) | M |
| RR3.2 | Resolve the module-ordering obstruction blocking `blockedThreadsPendingMessageConsistent` composition | `SeLe4n/Kernel/IPC/Invariant/` | M |
| RR3.3 | De-thread the post-state `blockedThreadsPendingMessageConsistent` hypothesis across the endpoint bundles (send / receive / call) — measured by the RR3.1 gate, not by binder name | `SeLe4n/Kernel/IPC/Invariant/Structural/` | L |
| RR3.4 | De-thread that same post-state hypothesis across the reply and replyRecv bundles | (same) | L |
| RR3.5 | De-thread it across the notification bundles | (same) | M |
| RR3.6 | De-thread it across the lifecycle and cancellation bundles | (same) | L |
| RR3.7 | Prove the per-transition establishers for `replyCallerLinkageReciprocal`'s forward clause | `SeLe4n/Kernel/IPC/Invariant/` | L |
| RR3.8 | De-thread the post-state `replyCallerLinkageReciprocal` hypothesis across the endpoint bundles | (same) | L |
| RR3.9 | De-thread it across the reply, notification and lifecycle bundles | (same) | L |
| RR3.10 | Decide the `consumeCallerReply` documented exception — close it, or re-record it with the reason it cannot close | (same) | M |
| RR3.11 | De-thread `dualQueueSystemInvariant` / `badgeWellFormed` at the eight remaining sites | (same) | M |
| RR3.12 | De-thread `donationOwnerValid` at the six remaining sites | (same) | M |
| RR3.13 | Build the reachability bundle that discharges the remaining pre-state preconditions | `SeLe4n/Kernel/IPC/Invariant/Reachability.lean` (new) | L |
| RR3.14 | Prove the boot state satisfies it, so the bundle is inhabited rather than vacuous | (same) | M |
| RR3.15 | `ipcInvariantFull` bundles for the **capability** dispatch arms (`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDelete`, `mintReplyCap`): CNode-only writes, so `capabilityBadgesWellFormed` is the only conjunct that moves and the rest transport through an object frame | `SeLe4n/Kernel/Capability/Invariant/` | L |
| RR3.16 | … the **lifecycle retype** arm.  Its per-conjunct halves exist (`lifecycleRetypeObject_preserves_*`); the bundle over them does not | `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` | M |
| RR3.17 | … the **VSpace** arms (`vspaceMap`, `vspaceUnmap`, `vspaceUnifyInstruction`): no conjunct reads a page table, so each is an object frame plus the store's own invariant | `SeLe4n/Kernel/Architecture/` | M |
| RR3.18 | … the **service** arms (`serviceRegister`, `serviceRevoke`, `serviceQuery`) | `SeLe4n/Kernel/Service/Invariant/` | M |
| RR3.19 | … the **sched-context** arms (`schedContextConfigure`, `schedContextBind`, `schedContextUnbind`).  These write `schedContextBinding`, so the donation quartet genuinely moves and the `donationOwnerFrame` / `sameSchedContextBindings` family is the lever | `SeLe4n/Kernel/SchedContext/` | L |
| RR3.20 | … the **TCB field** arms (`tcbSetPriority`, `tcbSetMCPriority`, `tcbSetIPCBuffer`, `tcbSetAffinity`, `tcbBindNotification`, `tcbUnbindNotification`): one-TCB rewrites leaving every conjunct-read field intact, which is exactly RR2.6's one-TCB-rewrite lever | `SeLe4n/Kernel/Lifecycle/`, `SeLe4n/Kernel/Scheduler/` | L |
| RR3.21 | … the **TCB lifecycle** arms (`tcbSuspend`, `tcbResume`), whose teardown rewrites `ipcState` and unlinks queues, so most of the bundle moves | `SeLe4n/Kernel/Lifecycle/Invariant/` | L |
| RR3.22 | The composition layer no transition bundle covers, which the RR2 hand-off assigned to the payoff row: the flow-`Checked` dispatch wrappers, the `replyRecvBody` three-stage composite, and the `Architecture.stage*` return-frame writes | `SeLe4n/Kernel/API.lean` | L |
| RR3.23 | `dispatchCapabilityOnly_preserves_ipcInvariantFull` — the argument-free dispatch tier, over RR3.15–RR3.21 | `SeLe4n/Kernel/API.lean` | M |
| RR3.24 | `dispatchWithCap_preserves_ipcInvariantFull` (**consumes RR3.15–RR3.23**; the `.call` arm's bundle is staged, so either state the payoff in the staged layer or relocate the call surface first) — and delete its line from `docs/planning/ipc_dethreading_pending.txt`, which the RR3.1 gate checks in both directions | `SeLe4n/Kernel/API.lean`, `docs/planning/ipc_dethreading_pending.txt` | L |
| RR3.25 | `dispatchSyscall_preserves_ipcInvariantFull` — the D8 payoff — **and** cite both payoff theorems from `docs/CLAIM_EVIDENCE_INDEX.md`, which this phase's acceptance requires and no other row owned: the theorem that changes the claim surface is the one that must update the claim.  Delete its line from the pending register too | `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/planning/ipc_dethreading_pending.txt` | L |
| RR3.26 | Retire `IPC_INVARIANT_DETHREADING_PLAN.md`: mark closed, record the closure version, move to `docs/dev_history/planning/` | (file move) | S |

**Acceptance**: the RR3.1 gate reports zero post-state bindings of
`blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal`
across the `_preserves_ipcInvariantFull` family; both payoff theorems exist
and are cited from `docs/CLAIM_EVIDENCE_INDEX.md`.

Both halves are **met**: no conjunct at all is bound on a post-state, both
payoff theorems exist and are cited from `docs/CLAIM_EVIDENCE_INDEX.md`, and
the pending register is empty — the gate still checks it in both directions
(a registration whose theorem has landed fails as stale, a registration
outside the payoff set fails as dangling, an absent unregistered payoff fails
as before), so the emptiness is a checked fact rather than a deleted file.

**A note on measuring this.** The ten conjuncts de-threaded by earlier slices
each had a canonical primed binder (`hQNBC'`, `hPRR'`, …), so "de-threaded"
could be checked by grepping the name to zero — and in the comment-free code
view all ten are indeed zero. The two remaining conjuncts have **no such
canonical name**: they appear under `hInv`, `hRecip`, `hWtpmn` and bare `h`
depending on the bundle. A name-based check would therefore report success
without measuring anything, which is the same failure shape as the tier-4
gates that scored a skip as a pass. RR3.1 exists so the criterion is
measured rather than assumed.


### RR4 — Fault handling: full fault IPC with reply-based restart — **LANDED v0.34.44**

All twenty-seven sub-tasks landed in one cut.  **Acceptance, met**: no
execution path returns a thread to its faulting instruction without handler
action (`faultDeliverOnCore_not_dispatchable`); `TCB.faultHandler` has a
consumer; `trap.rs` has one classification path; Tier 0–3 green.  The
standing constraints this phase established — a fault is delivered and never
returned, the flow-checked arm is the live one, `pendingFault` is the only
channel from a delivery to its reply — are in `CLAUDE.md`'s *Standing
constraints* section, which is where new code must read them.

*Met. What the cut changed, the defects it found and its review rounds are in
[`CHANGELOG.md`](../../CHANGELOG.md) at the version above.*

The finding, as the audit stated it:

The largest phase, and the one that closes the audit's most serious security
finding: data and instruction aborts today set `x0` and return to the
faulting instruction with `ELR_EL1` restored verbatim, so any user thread
touching an unmapped page wedges its core forever. It is not exploitable at
`v0.34.3` because nothing boots — it becomes reachable precisely when SM10.1
succeeds, which is the wrong moment to discover it.

**What already exists.** The TCB carries a `faultHandler : Option CPtr`
field with no consumer — an unwired field, so this is an
implement-the-improvement case rather than new architecture.
`SeLe4n/Kernel/Architecture/ExceptionModel.lean` already classifies
exceptions (`classifySynchronousException`), and its abort arms return
`.error .vmFault` as a pure error with no state change. Its only callers are
tests: the Rust `trap.rs` runs a *parallel* `esr_ec` match of its own, so
there are two classification paths and the Lean one is not live.

**What is missing.** A `Fault` type, fault-message encoding, handler
resolution, the delivery transition, reply-based resume and restart, and the
Rust wiring that makes the Lean path the live one.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR4.1 | `Fault` inductive, every constructor carrying the payload its message needs at seL4 parity: `vmFault` (address, FSR/status, prefetch flag), `capFault` (the faulting capability address and the receive-phase flag), `unknownSyscall` (the syscall number), `userException` (exception number and code). Nullary constructors would make the wire layout unable to carry what a handler needs to diagnose or restart the fault, and the round-trip theorem would then only preserve an already-impoverished value | `SeLe4n/Kernel/Architecture/Fault.lean` (new) | M |
| RR4.2 | `DecidableEq` + `BEq` + congruence lemmas for `Fault` | (same) | S |
| RR4.3 | Map `ExceptionContext` → `Fault`, replacing the `.error .vmFault` arms' classification role. **Not from `SynchronousExceptionClass`**: that inductive is nullary, while the fault address and syndrome exist only in `ExceptionContext.far` / `.esr`, so a class-to-fault map could only invent them and would corrupt the VM-fault message before the encoding round trip below. The nullary variants (unknown syscall, user exception) take their payload from the trap/syscall inputs on the same path | (same) | M |
| RR4.4 | Fault message layout: `Fault` → `MessageInfo` label + message registers, at seL4 parity | `SeLe4n/Kernel/Architecture/Fault.lean` | M |
| RR4.5 | Round-trip theorem: encoding then decoding a fault is the identity | (same) | M |
| RR4.6 | Length theorem: every fault encodes within the message-register budget | (same) | S |
| RR4.7 | Resolve `faultHandler : Option CPtr` to an endpoint capability through the thread's CSpace | `SeLe4n/Kernel/IPC/Operations/Fault.lean` (new) | M |
| RR4.8 | Rights check: the handler cap must carry send rights; fail closed otherwise | (same) | S |
| RR4.9 | No-handler policy: the thread is suspended fail-closed, never returned to the faulting instruction | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | M |
| RR4.10 | Negative: a thread with no `faultHandler`, or an unresolvable one, takes the RR4.9 fail-closed path | (same) | S |
| RR4.11 | Fault delivery transition — the faulting thread blocks and a fault IPC is sent to the handler endpoint, reusing the endpoint Call machinery rather than a parallel path | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | L |
| RR4.12 | Per-core form `faultDeliverOnCore`, with the cross-core SGI emission the other IPC paths use | `SeLe4n/Kernel/IPC/CrossCore/Fault.lean` (new) | L |
| RR4.13 | Reply object creation for the fault, so the handler receives a reply capability | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | M |
| RR4.14 | Reply-based **resume**: handler replies, faulted thread resumes at its saved `ELR` | (same) | M |
| RR4.15 | Reply-based **restart**: the reply carries a new PC and register values; the thread restarts there | (same) | L |
| RR4.16 | Restart register writeback into the TCB register file, reusing the syscall-return writeback rather than a second mechanism | `SeLe4n/Kernel/Architecture/SyscallReturn.lean` | M |
| RR4.17 | `faultDeliver_preserves_ipcInvariantFull` (+ per-core form) | `SeLe4n/Kernel/IPC/Invariant/` | L |
| RR4.18 | Fault reply preserves `ipcInvariantFull`; scheduler and capability invariants preserved on both paths | (same) | L |
| RR4.19 | **Progress theorem**: a faulted thread cannot re-execute the faulting instruction without an intervening handler action — the theorem that makes the livelock unrepresentable | `SeLe4n/Kernel/IPC/Invariant/FaultProgress.lean` (new) | L |
| RR4.20 | Non-interference: fault delivery respects the information-flow policy, and a fault message carries no data across a label boundary | `SeLe4n/Kernel/InformationFlow/` | L |
| RR4.21 | Wire `dispatchSynchronousException`'s `.dataAbort` / `.instrAbort` arms to the delivery transition, retiring the bare `.error .vmFault`. Deliberately **after** the preservation, progress and non-interference proofs above: this is the sub-task that makes the transition reachable, and a live kernel transition must not land ahead of its own invariant surface | `SeLe4n/Kernel/Architecture/ExceptionModel.lean` | M |
| RR4.22 | `trap.rs`'s four `set_x0`-only exception arms write a full status-label frame (ABI v3 since the audit round — the top-range status label, `error_frame_regs`) via `error_frame_regs`, retiring the raw-discriminant-in-`x0` convention that leaves `x1` untouched. **Before** the wiring below, not after: once aborts deliver, a resumed thread whose `x1` carries a label under 512 decodes a fault as a successful syscall. The defective arms are in `trap.rs` — `svc_dispatch.rs` already holds the correct helper | `rust/sele4n-hal/src/trap.rs` | S |
| RR4.23 | Rust: `trap.rs` abort arms call the Lean fault entry through a new `@[export]`, inside `with_kernel_entry` | `rust/sele4n-hal/src/trap.rs`, `SeLe4n/Platform/FFI.lean` | M |
| RR4.24 | Rust: `ELR_EL1` writeback on resume vs restart — the trap frame gains the mutator it currently lacks | `rust/sele4n-hal/src/trap.rs` | M |
| RR4.25 | Retire the duplicate classification path: `trap.rs` classifies via the Lean model rather than its own `esr_ec` match, so the two cannot diverge | `rust/sele4n-hal/src/trap.rs` | M |
| RR4.26 | Tests: fault delivery, resume, restart, no-handler suspend, and the negative that a fault never returns to the faulting instruction | `tests/FaultHandlingSuite.lean` (new) | L |
| RR4.27 | Golden fixture: a 4-core trace with a faulting thread and a handler | `tests/fixtures/` | M |

**Acceptance**: no execution path returns to a faulting instruction without
handler action (RR4.19); `faultHandler` has consumers; `trap.rs` has one
classification path, not two; Tier 0..3 green.

**Split guidance**: RR4.11, RR4.12, RR4.15, RR4.17, RR4.18, RR4.19, RR4.20 and
RR4.26 are each an L and should land as their own PR. If RR4.11 exceeds a week,
split it into the block-the-sender half and the enqueue-on-handler half.


### RR5 — Boot-path fail-open closure

Three latents that are unreachable today only because nothing boots. Each
becomes live the moment SM10.1 succeeds, so each must close before it.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR5.1 | Define a production `LabelingContext` — none exists; `testLabelingContext` maps every non-zero id to `publicLabel` | `SeLe4n/Kernel/InformationFlow/Policy.lean` | M |
| RR5.2 | Make the hardware boot path **require** a labeling context: `bootAndInitialiseFromPlatform`'s `Option` defaulting to `none` currently leaves the all-public test context installed | `SeLe4n/Platform/FFI.lean` | M |
| RR5.3 | Fail closed when absent on a hardware build, rather than silently proceeding | (same) | S |
| RR5.4 | Strengthen `isInsecureDefaultContext` to catch all-public contexts — it returns `false` for `testLabelingContext` today, so the guard does not fire on the very context the boot path installs | `SeLe4n/Kernel/InformationFlow/Policy.lean` | M |
| RR5.5 | Theorem: the production context passes the guard and the test context does not | (same) | S |
| RR5.6 | Add the `lean_ready` gate to the SVC dispatch seam, which has none despite `kernel_entry.rs`'s claim that every seam consults it | `rust/sele4n-hal/src/svc_dispatch.rs` | S |
| RR5.7 | Add it to the suspend seam | `rust/sele4n-hal/src/ffi.rs` | S |
| RR5.8 | Gate the SVC and suspend Lean `extern` declarations on `hw_target` rather than `cfg(not(test))`, the other half of the same finding: under `cfg(not(test))` a host non-test build still compiles call paths to bare-metal Lean symbols, so the readiness checks above do not close it | `rust/sele4n-hal/src/svc_dispatch.rs`, `rust/sele4n-hal/src/ffi.rs` | S |
| RR5.9 | Build-time or test-time check that every seam in the five-entry table consults the gate **and that no Lean extern is declared outside `hw_target`**, so neither a sixth seam nor an ungated extern can be added without one | `rust/sele4n-hal/build.rs` | M |
| RR5.10 | Lift the boot-core-pinned thread-state classification to the per-core shape: `inferThreadState` reads `currentOnCore bootCoreId` / `runQueueOnCore bootCoreId` only (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`), and `syncThreadStates` / `threadStateConsistent` inherit it.  **First, because the switch below makes it load-bearing**: `createIdleThread` sets `threadState := .Running`, so the instant a secondary core's idle TCB is installed on a path the harness reaches, `inferThreadState` classifies it `.Inactive` — its own core's current slot points at it, but no boot-core slot does — `threadStateConsistent` is false of the boot state, and `assertStateInvariantsFor` (which syncs before it checks) rewrites the field.  This is the second of the three SM5 integration deferrals `bootFromPlatformWithIdleThreads`'s docstring names, and the register's §7 finding 42 | `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | M |
| RR5.11 | The idle **run-queue** enqueue at `IntermediateState` level, with its frame and fold lemmas.  `enqueueIdleThreadOnCore` exists only over `SystemState` (`Scheduler/Operations/PerCoreIdle.lean`) and `installIdleThread` never touches `runQueueOnCore`, so there is today no operation that puts a boot idle thread on its own core's queue.  Add it beside `installIdleThread`, with the `installIdleThread_{objects,scheduler,currentOnCore_ne}` frame lemmas' analogues and the `Nodup`-fold reasoning `foldl_installIdleThread_installs` already models | `SeLe4n/Platform/Boot.lean` | M |
| RR5.12 | Prove `∀ c, idleThreadEnqueuedOnCore st c` of the idle-installing boot state — the premise `chooseThreadOnCore_always_succeeds` consumes, and the discharge `schedulerNoStall_smp`'s `hIdle` takes by hypothesis today.  Its three conjuncts land from three places already in the tree: run-queue membership from RR5.11's fold, TCB resolution from `foldl_installIdleThread_installs`, and the domain match from `createIdleThread_domain_zero` composed with `foldl_installIdleThread_activeDomainOnCore`; the purely-additive precondition is `idleSlotsFreshAt`, discharged for the canonical platforms by `idleSlotsFreshAt_of_initialObjects_below_base`.  **Before the switch, not after**: this is the proof surface that makes the live path worth switching to | `SeLe4n/Platform/Boot.lean` | M |
| RR5.13 | A checked boot entry that installs and enqueues idle, defined as a **thin composition over `bootFromPlatformChecked`** — never a second validation path.  Two paths that both validate a `PlatformConfig` is the `trap.rs` two-classifiers defect in miniature, and the composition shape is what keeps the seven existing `bootFromPlatformChecked_*` results (`_eq_bootFromPlatform`, `_admits_bootVSpace`, `_ok_implies_irqHandlersValid`, `_ok_implies_machineConfigWellFormed`, `_ok_implies_physicalAddressWidth_bound`, `_ok_interruptsEnabled`, `_rejects_invalid`) true verbatim: the new entry's own chain is derived from them by composition rather than restated.  Not yet the production base — nothing calls it at the end of this row | `SeLe4n/Platform/Boot.lean` | L |
| RR5.14 | Repoint the production boot wrapper `bootAndInitialiseFromPlatform` (and the RPi5 contract path) at it — **the row that closes the finding**, since RR5.13 leaves a correct entry with no caller, which is the same unwired-proof shape this row exists to remove — and resync what the extra per-core idle TCBs move: the `MainTraceHarness` boot trace and `tests/fixtures/main_trace_smoke.expected` (fixture change with its rationale, per the fixture rule), plus the boot-state assertions in the six suites that name the checked entry | `SeLe4n/Platform/FFI.lean`, `SeLe4n/Platform/RPi5/`, `SeLe4n/Testing/MainTraceHarness.lean`, `tests/fixtures/` | M |
| RR5.15 | Make the three staged state-committing kernel entries production-reachable, so a linked image carries their `@[export]` symbols | `SeLe4n.lean`, `scripts/staged_module_allowlist.txt` | M |
| RR5.16 | Verify each expected `@[export]` symbol is present in the built archive | `scripts/` | M |
| RR5.17 | Bracket `suspend_thread_inner`, which commits kernel state outside the kernel-entry lock | `SeLe4n/Platform/FFI.lean` | S |
| RR5.18 | Replace the two `debug_assert!` lock/vector tripwires, which vanish from the release image, with checks that survive it | `rust/sele4n-hal/src/` | S |

**Acceptance**: a hardware boot without an explicit production labeling
context fails closed; every seam consults the readiness gate; idle threads
are installed **and enqueued** on the production path, so `∀ c,
idleThreadEnqueuedOnCore st c` holds of the live boot state rather than being
assumed; the staged-module count falls by three.

**Acceptance met at v0.34.48**, with three deviations worth recording:

* *The staged-module count fell by **five**, not three.*  Promoting the three
  kernel entries pulls their import closure into production with them —
  `Scheduler.Operations.PerCoreRunLoop` and `.PerCoreTimerTick` — and the
  partition gate is what said so.  The acceptance number counted the entries,
  not the closure.
* *RR5.17 retired the export rather than bracketing it.*  The row said
  "bracket `suspend_thread_inner`"; the register's own remediation offered
  either that or retiring the `@[export]` and keeping the Lean definition for
  the suites (§5 finding 9), and retiring is the stronger outcome — it removes
  the hazard instead of mitigating it, and matches what WS-RA did to the twin
  `syscall_dispatch_inner`.  Bracketing would additionally have needed the Lean
  body to take the kernel-entry lock through new FFI, which the simulation build
  cannot link.  A Tier-3 negative anchor now keeps the export gone; the positive
  anchor moved to the definition.
* *The SVC seam's not-ready arm **halts**.*  PR #887 left that decision to RR5
  (`trap.rs`, round 3: "what a not-ready core should do with an `SVC` at all is
  RR5's question").  A fail-closed frame would be architecturally coherent — the
  `SVC` advanced the PC — but the timer seam consults the same readiness mask, so
  a thread on a not-ready core would never be preempted again; returning an error
  hands it the CPU forever.  The suspend seam, which has an error channel and no
  trapped thread, returns `KernelError::IllegalState` instead.

**Audit round (same version).**  A deep re-read of the cut against the code,
not the docstrings, found four things the rows above had shipped short of, all
closed at v0.34.48 before merge:

* *RR5.12's keystone took two hypotheses about the state it was discharged
  from.*  `bootFromPlatformCheckedWithIdleThreads_chooseThreadOnCore_succeeds`
  assumed the boot queue well-formed and its members resolvable.  The boot
  queue is now characterised exactly (on every core, the empty queue with idle
  enqueued — `…_runQueueOnCore_eq`), both premises are theorems of the boot
  state, the keystone takes nothing beyond the boot, and each core's first
  selection is pinned to its idle thread (`…_chooseThreadOnCore_idle`).
* *RR5.4's witness admissibility stopped at the sentinel.*  A labeling that
  gave only the four idle threads a label of their own — every user-visible
  entity `publicLabel` — could name two idle threads and pass.  Idle ids are
  excluded (`separationWitnessAdmissible`, `isIdleThreadId`), the
  index-partitioned family lifts its upper witness past the idle range so it
  stays total (`upperWitnessIndex`), and the refusal is tested for the
  exclusion rather than for equal labels.
* *RR5.1's "what a hardware boot installs" was a sentence.*  Nothing installed
  `confinedLabelingContext`.  `PlatformBinding` now carries
  `deploymentLabeling` (this round: the context with its admission proof; the
  review round below replaced it with the `DeploymentLabeling` source, so
  admission and validity are theorems of every binding), the RPi5 binding's
  labeling is the confined context at `rpi5UpperDomainBase`
  (`rpi5_deploymentLabeling`), the simulation bindings' is the harness
  labeling, and
  `bootAndInitialisePlatform` boots under the binding's — provably the checked
  idle boot with the refusal arm unreachable.
* *RR5.9's `hw_target` verdict was two substring tests.*  A `cfg_attr` or an
  `any(feature = "hw_target", …)` carried the token and read as a gate.  The
  verdict is computed over the parsed `cfg` predicate
  (`cfg_predicate_entailment`, under-approximating so it fails closed), and
  linker visibility now covers `#[unsafe(no_mangle)]` and `#[export_name]`;
  six more token-preserving mutations pin it.

**Review round (PR #889, same version).**  The pull-request review found six
more places where a relation was asserted at one site and not derived, all
closed before merge:

* *RR5.11 stored the dispatched idle form while queuing it.*  The enqueue
  stores `queuedIdleThread` (`.Ready`), `bootSafeObjectCheck` requires config
  TCBs `.Inactive`, and the production boot state is proved
  `threadStateConsistent` (`bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`).
* *RR5.6's gate came after the SVC prefilters.*  It now precedes every outcome
  — the prefilters in `dispatch_svc`, the `x7` narrowing and the
  unknown-syscall delivery in the trap arm — pinned structurally by
  `svc_arm_readiness_gate_status`, since an `extern "C"` halt aborts a host
  test rather than unwinding.
* *RR5.16 required the intersection of the two symbol sets.*  Every HAL
  declaration must now resolve (archive, assembly global, or a reconciled
  `EXPECTED_UNRESOLVED` entry), so a rename on either side fails.
* *RR5.13 folded over configs that occupied idle slots.*  `PlatformConfig.wellFormed`
  reserves them (`idleSlotsReserved`), and a successful checked boot is fresh
  by theorem, so the preservation result takes no hypothesis.
* *RR5.18's tripwire tested held-ness, not ownership.*  The round lock records
  its owner and the tripwire asks `round_lock_held_by(core)`; another core's
  shootdown makes an entering core wait, not halt.
* *RR5.1's binding proved admission only.*  It stores the `DeploymentLabeling`
  source, so admission and full validity are theorems of every binding
  (`PlatformBinding.labeling_valid`).

**Review round 2 (PR #889, same version).**  The second pass found seven more,
five of them the same shape and two of them scanners asking for a token where
the question was a predicate:

* *RR5.13's reservation covered object keys only.*  A boot CNode could carry a
  capability to `(idleThreadId c).toObjId`, which the idle fold then
  materialised, and a `.tcbSuspend` through it would remove the core's only
  guaranteed runnable thread.  The reservation now covers every object a config
  entry *references* (`bootObjectReferencesReservedIdleSlot`, total over
  `KernelObject`), and — the chokepoint form — `syscallResolveCap` refuses any
  capability naming a reserved idle object (`capTargetsReservedIdleObject`,
  `syscallResolveCap_ok_not_reserved`), so no syscall can act on an idle TCB
  through a capability a config or a transfer happened to carry.
* *RR5.13's refusal named the wrong fault.*  An otherwise valid config occupying
  an idle slot was reported as a duplicate object id; the checked boot now has
  an idle-slot branch ahead of that fallback.
* *RR5.1's source carried labels only.*  `DeploymentLabeling` now carries
  `memoryOwnership`, `endpointPolicy`, `declassificationPolicy` and
  `auditMonitorClearance` with their fail-closed defaults, so a binding can
  configure them where it declares its labeling; before, every hardware boot
  was forced to the constructor's defaults.
* *RR5.11's consistency claim stops at the boot.*  The scheduler's dispatch
  writes no `threadState`, so the full classification is a boot-state theorem
  and not a preserved invariant.  The relation the live decisions read — the
  stored flag says `.Inactive` iff the observable state does — is stated as
  `threadInactiveFlagConsistent`, proved of the boot state, and its
  preservation across the scheduler and IPC surfaces is registered debt owned
  by RR7.36.
* *RR5.18's tripwire scanner matched a token.*  A reversed predicate kept
  `2048` and the halt and halted every aligned boot; the scanner now requires
  the `if` condition to be the declared failure predicate, whitespace aside,
  with polarity mutations in its self-check.
* *RR5.7's export inventory read raw Lean text.*  A commented-out
  `@[export …]` counted as a live symbol; `build.rs` now derives the inventory
  over a comment-free, string-free Lean view and splits attribute lists, so
  `@[inline, export name]` and a line break before the name count.
* *The shell code view copied `$( … )` spans verbatim.*  A comment inside a
  substitution survived into the code view and a `)` inside it closed the
  substitution early; the body is now lexed recursively.

**Review round 3 (PR #889, same version).**  Four more:

* *RR5.2's boot entry had no enforced connection to SM10.1's caller.*
  `lean_kernel_main` stays SM10.1's to write (a transition goes live after
  its proofs, and the entry needs the DTB-derived configuration); the export
  gate now requires that whichever declaration exports it calls
  `bootAndInitialisePlatform` in its own body (`boot_entry_binding_failures`).
* *RR5.4's witnesses were ids, not threads.*  The boot wrapper refuses a boot
  whose labeling's declared witnesses are not installed threads of the boot
  state (`declaredWitnessesInstalled`), so a partition that separates no
  running thread does not boot.
* *RR5.16's assembly providers were `.global` directives.*  A provider is a
  defined symbol (directive and label) in a source `build.rs` assembles.
* *RR5.14's idle install ignored the binding's core count.*  The binding boot
  folds over `PlatformBinding.declaredCores`; the RPi5 binding declares every model
  core, so its boot is the all-cores form (`rpi5_cores_eq_allCores`).

**Review round 4 (PR #889, same version).**  Three precision gaps in the
previous closures: the reference check reads a notification's `boundTCB` (and
every SchedContext reference); an assembly provider is read outside
preprocessor conditionals, on the builder chain that reaches `.compile()`,
and against the assembled archive's object symbols when present.

**Review round 5 (PR #889, same version).**  Four: the labeling family's lower
witness was thread `1`, the boot VSpace root's object id on every binding, so a
hardware boot carrying its own root was refused for an uninstalled witness —
the witness is a parameter, the RPi5 binding declares `rpi5LowerWitnessIndex`,
and `PlatformBinding.witnessesOffBootVSpaceRoot` holds every binding's
witnesses apart from its root; the idle-slot reservation is model-wide by
design and now says so (an undeclared core's slot is absent, not free); the
boot-entry gate reads statements — an executed top-level call and no other
kernel-state installer, over a derived installer set — instead of an
identifier occurrence; and `coreCount ≤ numCores` is a class obligation
(`coreCountLe`), so `declaredCores` has exactly `coreCount` members.

**Review round 6 (PR #889, same version).**  Four, three of them in the
gates: the symbol inventories read the shared code views with strings
blanked; the idle-slot reservation reads an untyped's `children` and
`parent`; each release-surviving tripwire is pinned with the operation it
protects and must dominate it; and an expected-unresolved exemption expires
the moment its export appears.

**Review round 7 (PR #889, same version).**  Six: a boot TCB is stored under
its own thread id (`tcbIdentitiesMatchSlots`) and the reference check reads
its `tid`; the hardware entry is `bootAndInitialiseRPi5`, the generic entry
fixed at the RPi5 binding, and the platform entry boots the bound config
(`bindPlatformConfig`: the binding's machine configuration and boot VSpace
root); the tripwire branch must end in `fatal_halt`; the assembly providers
are read off the compile's executed chain; the export inventory includes the
library root.

**Review round 8 (PR #889, same version).**  Five: the raw suspend seam
refuses idle ids before the transition
(`suspendThreadCrossCoreStep_idle_refused`); the reservation reads `queuePPrev`
and is pinned by constructor arity, with the sweep's fields and the identity
relation over SchedContexts and Replies (`embeddedIdentitiesMatchSlots`); the
tripwire branch is a top-level statement of the helper or sits under an
unconditional block; function externs are satisfied by global text symbols
only; the assembled sources follow the compiled builder's binding instance.

**Review round 9 (PR #889, same version).**  Five: an unqualified
`lean_ready(..)` resolves to the gate only where the file imports it and
defines no function of that name (`bare_ready_call_resolves`, swept across
every scanner that asks); nothing may leave a tripwire helper before its
fail-closed branch (`statement_may_exit`); the boot entry must branch on the
checked boot's `Except` and halt on `.error` (`boot_entry_handles_failure`);
a receiver rebound by assignment is a binding boundary; and `build.rs`'s
readiness scanner reads the library root `SeLe4n.lean`.

**Review round 10 (PR #889, same version).**  Three, all against round 9's
failure-handling check and all the same class: the arms are parsed so the
`.error` arm's own body must halt, a diverging statement before the handling
match refuses, and the match must be on the binding the boot produced rather
than on a rebinding of its name.

**Review round 11 (PR #889, same version).**  Two: a **P1 in the kernel** — a
raw thread-id operand (`.schedContextBind`'s `args.threadId`) escaped the
capability chokepoint, so an ordinary SchedContext capability could bind and
re-prioritise a core's idle TCB; the refusal is at the raw-operand lift points
`validateThreadIdArg` / `validateObjIdArg` — and the boot entry's `.error` arm
must halt as its terminal action rather than merely mention a halt.

**Review round 12 (PR #889, same version).**  Four, all against
`check_kernel_entry_exports.py` and all one shape — *a name is not a
definition*.  The callee could be rebound (`let bootAndInitialiseRPi5 := fun _
=> pure (.ok default)`); the `.error` arm's halt could be `Fake.ffiFatalHalt`
or a local of that name; `@[inline, export lean_kernel_main]` was invisible to
the export inventory and the boot-entry locator, so the whole contract passed
vacuously; and `#[link_name = "…"]` renamed a symbol the requirement then got
wrong in both directions.  Every reference is now resolved by Lean's suffix
rule against fully-qualified declarations, must denote only the pinned one, and
is refused where the declaration binds the name locally; the halt set is
derived from the `@[extern "ffi_fatal_halt…"]` primitives and their aliases;
the attribute list is parsed by one parser shared with `build.rs`; and the link
requirement is the effective linker name, with `build.rs` refusing an alias of
a Lean symbol outright, since no readiness gate can be attributed to one.

**Review round 13 (PR #889, same version).**  One, against the arm parser: a
`match` nested inside an arm donated its `| .error _ => halt` to the
boot-result match's own arm list, because the statement's continuation lines
had been stripped of the indentation that distinguishes them.  Columns are
kept now, arms are those at the match's own column, and — the sweep, one level
down — an arm's terminal statement is the last line at its body's *minimum*
column, so a halt in the `else` branch of a multi-line conditional is no
longer read as what the arm does.

**Review round 14 (PR #889, same version).**  Five, four of which are the sweep
rule failing: `let` was not every binder (`have` shadows the boot result), an
exit is not always the whole statement (`if skip then return ()`, where
`build.rs` had asked the right question since PR #887), the halt-alias closure
resolved by suffix where `reference_failure` required a unique candidate, and
the recursive shell view lexed `$( … )` while the legacy backtick spelling was
copied verbatim.  The fifth is a view-selection defect: a string literal
supplied both the brace nesting and the `#[cfg]` attribute that decided an
`extern` block's gate, so structure is now located on the string-free view and
only the feature name read from the aligned kept one.

**Review round 15 (PR #889, same version).**  Five, one of them in the kernel:
a configured TCB's `cpuAffinity` was unconstrained, so a binding with
`coreCount < numCores` booted a thread pinned to a core it does not have and
`determineTargetCore` would enqueue it on a PE that does not exist.  The
refusal is at `bootFromPlatformCheckedWithIdleThreadsFor`, the point the core
list reaches, and is vacuous on `allCores` so the hardware boot is unchanged.
The other four harden the gates: a constructor pattern binds a name, both Lean
code views parse raw strings, `statement_may_exit` guards the statements inside
a tripwire's failure branch, and a value binding of `lean_ready` disables the
bare spelling.

**Review round 16 (PR #889, same version).**  Seven, four of them the shape
rounds 12, 14 and 15 had each fixed one spelling of.  The response is a
contract rather than another spelling: the boot entry names the checked boot
and the halt by their fully-qualified names — nothing local can shadow a dotted
name — and the accepted expression is the call and its arguments, not a prefix
of one; the readiness guard is written `crate::lean_ready::lean_ready(..)`,
which every guard in the HAL already does.  Three genuine parser defects are
fixed as such: the halt seed locates its attribute on the string-free view, an
`extern` block is split into items so an attribute binds to the item it
decorates, and an uninvoked `.macro` body is not an assembly provider.

**Review round 17 (PR #889, same version).**  Five findings, and a standing
instruction from the maintainer that decides the shape of the fix: a Lean
question goes to the Lean elaborator, never to a regular expression.  Round 16's
contract was the last patch this class accepts; round 17 removes the class.
The boot entry's contract now lives in
`SeLe4n/Testing/BootEntryContract.lean`, which reads the elaborated
`Environment` — `getExportNameFor?` for the exporting declaration,
`Expr.getUsedConstants` for what it calls, a reachability walk for what installs
kernel state — and fails its own elaboration, with four witnesses (a compliant
entry and three token-preserving deviations) keeping it decisive before SM10.1
writes the entry.  `Platform.FFI.bootAndInitialiseRPi5OrHalt` makes the error
path a definition, so the eight rounds spent reading an `.error` arm out of Lean
source have no subject left.  That retired 43 top-level names from
`scripts/check_kernel_entry_exports.py`; what remains is the link-level half,
where three of the five findings landed: an `extern <abi>? { … }` block is
resolved rather than spelled (three sites, two of them in `build.rs`), a
`#[link_name]` is located on the string-free view, and `.if 0` / `.rept` regions
provide no assembly symbols.  The self-test's case count is measured from the
harness's own source rather than bumped by hand.

**Review round 18 (PR #889, same version).**  Four, three against the round-17
replacement and one against the kernel model.  The first is this project's
oldest defect one level below text: `Expr.getUsedConstants` says a constant
*occurs*, not that it *runs*, so an entry that boots inside an `if` satisfied
the contract — resolved by walking the structure that cannot branch
(`unconditionalActions`) and requiring the approved call to head an action it
reaches.  The second is the seam's ABI: a C symbol carries no type, so the
contract now requires the entry's type to be `UInt64 → BaseIO Unit`, what
`boot.rs` calls it at.  The third is which environment the contract reads —
`Platform.Staged` alone would miss an entry in a `SeLe4n.lean`-only module, so
both roots are imported and the module list pins it.  The fourth: `wellFormed`
did not bound the object count while the idle fold adds one entry per core, so
a config filled to `maxObjects` booted past it; `objectBudgetRespected` reserves
the headroom and `objectIndexBounded` is now a theorem of the production boot.

**Review round 19 (PR #889, same version).**  Three, two of them against round
18's own answers and both the same shape — an `Expr` walk assuming something
about what it looks at.  A `Bind.bind` application sequences only under a lawful
*instance*, which is an argument: a `Bind` on a type definitionally equal to
`BaseIO Unit` may discard both, so the instance is now compared against the one
synthesis finds.  `ConstantInfo.value?` hides an `opaque` body by default, so an
`opaque` alias of a kernel-state installer read as a harmless leaf; the walk
passes `allowOpaque := true`, and what it still cannot see (a foreign
`@[extern]` body) is stated rather than assumed away.  The third: round 18's new
`wellFormed` conjunct had no branch in the boot error cascade, so a size fault
was reported as an embedded-identity mismatch — the defect round 2 fixed for the
idle-slot reservation, repeated by the same omission.

**Review round 25 (PR #889, same version).**  Three findings, three scanners,
three languages — and one defect: each, handed input it could not parse,
**silently did nothing**, and doing nothing was fail-open every time.  A Rust
raw identifier (`fn r#lean_real();`) matched no `fn` pattern, so the item
declared no link requirement at all.  GAS's `.pushsection` / `.popsection`
stack was unmodelled and a quoted `.section ".data"` matched no directive
pattern (the code view blanks a string's contents), so a `.data` label reported
as an executable provider — round 22's finding, reintroduced by spellings round
22 did not enumerate.  And both `@[export]` collectors read ASCII identifier
characters only, so a guillemet-spelled export (`@[export «suspend_generated»]`,
which Lean accepts and emits) left the readiness-gate seam set one entry short.

Two sweeps came with the fixes rather than with the next round.  The
raw-identifier question is asked in four places — the Python declaration
collector the review named, `build.rs`'s `extern_block_declarations` (which
feeds the readiness *seam set*) and both `enclosing_fn` implementations, which
key every allowlist entry and exemption on the function's name — and all four
now read the escape.  And the statement split this round introduced brought its
own edge: a `#define` body is a cpp *template*, so splitting it would set the
section from code that never executes there and register a macro parameter as a
provider (round 16's `.macro` hazard, arriving through the fix for a different
one).  A preprocessor line is never split.

The rule for this plan: **a scanner's default branch is a decision.**
Enumerate the inputs that legitimately produce nothing and stop the build on
anything else — round 21 had already established that shape for one case
(a macro inside an `extern` block) and it was not applied to the branch it was
a case of.  **And which direction is closed depends on what the scanner
produces**: a *requirements* scanner fails closed by refusing unreadable input,
a *providers* scanner by dropping it.  The same unreadable `.section` operand
therefore makes `executable_label_names` report the section unknown (and so not
executable) while it makes `extern_declarations_in` and both export inventories
stop outright.

**Review round 24 (PR #889, same version).**  One, against round 23's own fix.
The wait was paced with `cpu::wfe_bounded`, whose `max_ticks` is documented as
*informational* — "does not bound the actual `wfe`" — so a secondary that dies in
init sends no event, the first sleep never returns, and the topology refusal is
unreachable: a wait that cannot time out cannot fail closed.  The name was the
only thing that said bounded.

The deeper point for this plan: `shootdown::wait_all_acked_bounded_in` had
already hit the hazard and written the answer down, in the same words.  Writing
a third bounded-wait rather than using it is round 22's rule at the point where
the tree had already answered.  **Before writing a wait, a barrier, a retry or a
timeout, find the one this tree already has and read why it is shaped that way.**

**Review round 23 (PR #889, same version).**  Two, both against rounds 21/22's
own answers, and both corollaries of round 22's rule.  *A proxy is not the
fact*: the handoff compared PSCI `CPU_ON` acceptances against the declared PE
count, while the fact — `CORE_IRQ_READY`, published by each core after
`enable_irq` and already read by the shootdown protocol — says whether the PE
will service work at all; the wait for it is bounded so a PE that never
publishes fails the boot rather than hanging it.  *A bound has two sides*:
round 22 clamped `declaredCoreCount` from above and left zero, where the boot
installs no idle thread anywhere and returns `.ok` with nothing to run;
`declaredCoreCountInRange` is `wellFormed`'s sixth conjunct.

Two mechanical notes worth carrying: projection paths into the `wellFormed`
conjunction shift on every addition (the accessors are nesting-independent
now), and a Tier 3 anchor written against a line's *end* breaks when a conjunct
is appended (anchors name the conjunct-list pairing instead).

**Review round 22 (PR #889, same version).**  Three, and one shape: a question
implemented twice with only one implementation right.  The generic boot wrapper
passed `allCores` while the machine it installed carried a narrower
`declaredCoreCount` (round 20's relation at the one entry with no binding to tie
it); round 21's handoff refusal used the per-PE `fatal_halt` where the tree's
system-wide barrier is `gic::halt_all()`, so already-online secondaries kept
servicing interrupts after a refused handoff; and the assembly *source* fallback
accepted a `.data` label as a function provider, a question the *archive* parser
has answered correctly since round 8.

The rule this adds is the proactive form of the sweep already in `AGENTS.md`:
**derive both answers from one, or make the second impossible.**  Where a second
implementation must exist — a source fallback for when the object code is not
built — it must ask the same question and under-approximate, so divergence shows
up as a false missing symbol rather than a false provider.

**Review round 21 (PR #889, same version).**  Five, and four of them are one
defect that this plan should record because the *diagnosis* is the deliverable.
Round 17 applied "a Lean question goes to the elaborator" to **names** and
closed that class outright.  It did not apply it to *behaviour*, and nothing in
the environment answers what a program does — so round 17 also wrote a
hand-rolled abstract interpreter over `Expr`, and rounds 18, 19, 20 and 21 are
four consecutive findings against it (a conditional, a lawless `Bind`, a hidden
`opaque` body, a non-returning action, a `let`-bound head).  That is round 16's
sentence about regular expressions with one word changed: the set of inputs
defeating a partial analysis is unbounded, the set it has seen is finite.
Substituting `Expr` for text moved the class down a level rather than closing
it.

The exit is round 16's own, applied to the program rather than to its names:
the boot entry is no longer analysed but **required to be** one program —
`bootAndInitialiseRPi5OrHalt` applied to a configuration, decided by a single
`isDefEq`.  Stronger than the walk (which admitted any extra action that did
not write kernel state), and it deletes eleven analysis definitions.  The
corollary for scanners with no elaborator to ask is the rule already stated:
fail closed on what cannot be decided — a macro inside a Rust `extern` block is
refused rather than read past, and `${` alone opens a parameter expansion.

The fifth is the kernel one: round 20 gave `declaredCoreCount` a live consumer
while `rust_boot_main` computed `online` and passed it nowhere, so a
`smp_enabled=false` or capped bring-up could hand a 4-PE kernel a narrower
machine.  Refused at the `hw_target` handoff, with the constant pinned against
the binding.

**Review round 20 (PR #889, same version).**  Four.  Three are the same shape
one more time: a walk or a lexer assuming something about what it is looking at.
`unconditionalActions` treated the tail of a `Bind` chain as reachable, so an
entry that halted *before* the approved boot still reported it — the walk now
truncates at the first provably non-returning action, seeded from the
`@[extern]` halt primitives by *symbol* and closed over aliases.  The
reachability walk classified project modules by a `SeLe4n` prefix, which is an
enumeration of the project's roots and cannot see one that does not exist yet;
it now excludes the dependency roots and reconciles that list against the
environment's own, so a new dependency root fails the build rather than opening
a hole.  And the recursive shell view closed a `$( … )` at the first unbalanced
`)`, which `${x:-(}` supplies.

The fourth is a kernel defect and the reason this round is not purely about
gates: **a boot-time check with no live counterpart is a bound on the
configuration, not on the kernel.**  Round 15 refused a *configured* TCB pinned
outside the binding's declared cores; `decodeAffinity` accepts any
`v < numCores`, so `.tcbSetAffinity` could migrate a thread onto an absent PE
the instant after that boot succeeded — enqueued where nothing runs it, with the
reschedule SGI sent to a core that cannot take it, and success returned.  The
declared count now travels with the machine (`MachineConfig.declaredCoreCount` →
`applyMachineConfig` → `MachineState.declaredCoreCount`), because the machine is
what a transition can read; `PlatformBinding.declaredCoreCountAgrees` holds it
equal to the `coreCount` the boot enforces, so the two are one fact rather than
two that can drift — and the one binding whose machine config had to change is
the single-core simulation, which was sharing the four-PE `simMachineConfig`.
That is the gap, stated by the obligation that now refuses it.

**Note on RR5.10–RR5.14** (the rows that replaced one XL).  Two findings shape
the split, and the row they replaced named neither: one is an ordering defect
it inherited, the other is the reason its "cannot be separate PRs" claim is
approach-dependent rather than structural.

*The classification lift comes first because the switch needs it.*
`createIdleThread` sets `threadState := .Running` and `inferThreadState` reads
the boot core's slots only, so a secondary core's idle TCB classifies
`.Inactive` the moment it exists on a path anything synchronises.  That is
register finding 42, whose sweep row is RR7.36; the work lands here, and
RR7.36 verifies it closed — the same relation RR7.25 has to RR6 and RR7.28 to
RR3, per §2.3.  Scheduling it after the switch would be a backward dependency,
which is the defect the numbering rule exists to prevent.

*The switch and the theorem chain separate only under composition.*  The
replaced row said they could not be separate PRs, and that is true of the
approach it assumed — mutating `bootFromPlatformChecked`'s base in place makes
the seven downstream theorems, which characterize the result in terms of
`bootFromPlatform config`, either fail to compile or stop covering the live
path.  Defining the idle entry **as a composition over the checked one**
(the alternative `Platform/Boot.lean`'s own docstring offers) leaves those
seven true verbatim and derives the new chain from them, which is what lets
RR5.13 and RR5.14 land apart.  An implementer who mutates the base instead
should merge the two rows back into one rather than land a red tree.


### RR6 — Verified lock primitives completion (SM2.C-defer, pre-v1.0.0)

[`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md)
scopes itself post-v1.0.0. **This plan moves it before v1.0.0.** Shipping a
verified microkernel whose core concurrency primitive has a known-deferred
completeness story understates what "verified" means on the one component
every other subsystem's serialisability argument rests on.

Most of D-1..D-6 has landed. The residue is not spread evenly across the six
items — it concentrates in one theme: **the refinement bridges connect the
Lean specs to transliterations and to their own assumptions, rather than to
the locks the kernel actually deploys.**

Three verified facts frame the phase:

- `lock_bridge.rs` builds its static pool from `crate::rw_lock::RwLock` — the
  CAS-retry, non-FIFO implementation — while the Lean spec was tightened to
  strict FIFO.
- `QueuedRwLock`, the FIFO-preserving implementation D-5 landed, has **zero**
  consumers outside its own module.
- The Tier-5 oracle's own docstring states it is a software model, not the
  real lock, because the real one blocks under contention.

So the deployed lock is not the one the spec describes, and the harness that
would have caught that drives neither.

> **LANDED at v0.34.50.**  The three facts above are the state this phase was
> written against, not the state of the tree.  All three are closed:
> `STATIC_RW_LOCK_POOL` is `[QueuedRwLock; 4]` (with `build.rs` pinning the
> element type, so a revert fails the build), the queued lock's refinement to
> the FIFO spec was proved *before* the pool was repointed
> (`queuedRwLock_refines_rwLockSpec`, `queuedRwLock_admits_in_spec_order`), and
> the Tier-5 oracle drives both real implementations and checks them against
> each other, against the abstract ticket interval and against `encodeRwLock`
> after every operation.  The CAS-retry lock is **retained**, per RR6.11, for
> three reasons recorded in its own module docs: it is the oracle's second
> implementation, it owns the `WRITER_BIT` / `READER_MASK` layout the queued
> lock now imports rather than re-declares, and its D-4 refinement was
> *completed* (`rust_rwLock_refines_lean_honest`, stated without the
> `ListBlockBisim` premise it used to assume) rather than deleted.

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR6.1 | Add non-blocking `try_acquire_read` / `try_acquire_write` to the real `RwLock`, removing the oracle's stated reason for modelling instead of driving | `rust/sele4n-hal/src/rw_lock.rs` | M |
| RR6.2 | Rewrite the Tier-5 oracle to drive the real lock through those entry points | `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` | L |
| RR6.3 | Extend the oracle to the queued lock, so both implementations are covered | (same) | M |
| RR6.4 | The queued lock's concrete state and operation alphabet.  `ConcreteRwLockOp` / `concreteApplyOp` (`RwLock.lean` §D-4.1) model a **single** `AtomicU64`, and `QueuedRwLock` holds four atomic words — `state`, `next_ticket`, `now_serving`, `last_enqueued` — so the CAS-retry alphabet cannot express a ticket at all.  Define the concrete record and the ticket-carrying op set (`next_ticket.fetch_add`, `now_serving` load and `fetch_add`, `state.fetch_add` / `fetch_sub` / CAS `0 → WRITER_BIT` / `fetch_and READER_MASK`, `sev`, bounded `wfe`) with its `applyOp`, reusing the existing `writerBit` / `readerMask` bit-packing lemmas for the `state` word | `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean` (new) | S–M |
| RR6.5 | The ticket protocol's own well-formedness, stated over the concrete model alone and independent of the abstract spec: `now_serving ≤ next_ticket`, each issued ticket is held by at most one core, and `now_serving` advances exactly once per issued ticket (`pass_turn`'s `fetch_add`, which the implementation comment says is chosen over a store precisely so it cannot regress).  This is what the rest of the phase rests on — it is the mutual-exclusion argument, and it is what makes `await_turn`'s spin and `acquire_write`'s `compare_exchange(0, WRITER_BIT)` loop terminate: holding the ticket is what admits a reader, so no *new* reader can enter while a writer is being served and the reader count is monotonically decreasing | (same) | M |
| RR6.6 | The simulation relation.  `rwLockSim` relates only the writer bit and reader count, and says in as many words that the abstract `waiters` field is not represented — which is honest for the CAS-retry lock and useless here, because `waiters` is the whole of what the FIFO spec constrains.  Define `queuedSim`: the abstract `waiters : List (CoreId × AccessMode)` corresponds to the half-open ticket interval `[now_serving, next_ticket)` under the per-core ticket assignment, in order; plus the unheld / writer-held / readers-held characterizations that the block lemmas below consume | (same) | L |
| RR6.7 | Per-entry-point block step lemmas — one abstract `RwLockOp` to one concrete block, mirroring the `blockBisim_*` shape: `acquire_read` (take ticket, await turn, `state.fetch_add`, pass turn), `release_read` (`state.fetch_sub`, `sev`), `acquire_write` (take ticket, await turn, CAS loop), `release_write` (`fetch_and`, pass turn).  Each block admits an arbitrary `await_turn` stutter prefix, which is where the modelling actually bites: the spin is unbounded in the implementation and must appear as stuttering that leaves `queuedSim` intact, not as a step | (same) | L |
| RR6.8 | Trace-level composition: an abstract op list and its concrete block list preserve `queuedSim` from any sim-related initial pair, by induction over the chain with a case split over the four block lemmas.  Stated so that it does **not** take the per-block obligation as a hypothesis: the defect the CAS-retry rows later in this phase exist to remove is exactly a main theorem assuming its own per-block conclusion, and reproducing that shape in a new module would be shipping the known defect twice | (same) | M |
| RR6.9 | Corollary: `QueuedRwLock` refines the Lean FIFO spec end to end, closing the spec-to-implementation gap for the lock the next sub-task deploys — proved before the switch, so no version ships an unrefined core lock | (same) | L |
| RR6.10 | Point `STATIC_RW_LOCK_POOL` and the `ffi_rw_lock_*` entries at `QueuedRwLock`, so the deployed lock is the FIFO one the spec describes — **and** correct the FFI and information-flow docs naming the CAS-retry lock as deployed in the same slice, since landing them apart ships a version whose canonical Lean-side concurrency documentation names the wrong runtime primitive | `rust/sele4n-hal/src/lock_bridge.rs`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| RR6.11 | Decide and record the fate of `rw_lock.rs`: retained for compatibility, or retired | (2 files) | S |
| RR6.12 | `TicketLockConcrete` operational step function, mirroring the RwLock refinement's shape | `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean` | L |
| RR6.13 | Trace correspondence (`blockBisim` / `ListBlockBisim` analogue) replacing the counter arithmetic in `rust_ticketLock_refines_lean` | (same) | L |
| RR6.14 | Replace the tautological conjunct with a statement that can fail | (same) | M |
| RR6.15 | D-4, the trace-shape predicate: an *honest trace* is one in which every CAS's `expected` is the value the preceding `load` in the same block observed, and its `new` is what the implementation computes from that value.  The bare `opCorresponds` inductive parameterizes `tryRead_success` by arbitrary `(e n : UInt64)`, so without this the chain admits `tryRead_success c 999 999` — an abstract direct-acquire whose concrete CAS fails.  Landed first and alone, so the composition below has something to consume; this is also the phase's stated mitigation if the bisimulation proves hard | `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` | M |
| RR6.16 | D-4, the promoting release — **the crux, and the reason the composition cannot close as the row it replaces was written**.  `RwLockState.applyOp` enqueues a contended acquirer into `waiters` and `releaseWrite` then batch-promotes the head via `promoteWaitersOnWriterRelease`, while the CAS-retry lock has no queue: from `unheld`, the trace `tryAcquireWrite c₀ · tryAcquireRead c₁ · releaseWrite c₀` leaves the abstract state with `readers = [c₁]` (encoding `1`) and the concrete `fetch_and(READER_MASK)` at `0`, so `rwLockSim` is false — which is exactly why the four release discharges carry `_no_promote` / `_empty_queue` side conditions and dodge the only interesting case.  Extend the block-decomposition contract so a release block may carry the promoted waiters' re-acquisition, then prove the promoting discharges over it.  A block contract change, not a lemma, which is why it is its own row | (same) | L |
| RR6.17 | D-4, the two constructors with no discharge at all: `tryWrite_cas_retry` and `tryWrite_park_retry` are among `opCorresponds`'s ten constructors and are named by none of the nine `blockBisim_*` lemmas, so a case analysis over the inductive cannot close today whatever the trace shape.  Derived from the constructor inventory rather than a hand-kept list, so a constructor added later is a missing case rather than a silent gap | (same) | M |
| RR6.18 | D-4, the composition: `ListCorresponds` together with RR6.15's trace shape implies `ListBlockBisim`, by induction over the chain with a case split over all ten `opCorresponds` constructors, each discharged by the now-total `blockBisim_*` family.  This is the step that turns the discharge lemmas from a collection into a proof | (same) | L |
| RR6.19 | D-4, retire the hypothesis: restate `rust_rwLock_refines_lean` and `rust_rwLock_refines_lean_via_rustImplementsRwLock` without their `ListBlockBisim` premise — it becomes a consequence of RR6.18 rather than an assumption — and repoint the inventory and aggregator entries that register the assumed form, so no catalogue still advertises the theorem that took its own conclusion | `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean`, `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` | M |
| RR6.20 | Run the deployed queued lock under Loom: the dev-dependency alone explores nothing, because `queued_rw_lock.rs` imports `core::sync::atomic` directly and Loom only sees its own instrumented atomics. Add the `cfg(loom)` synchronisation aliases so the lock compiles against them, write `loom::model` tests over the bounded interleavings, and invoke them from CI or the nightly — otherwise §8's "loom gate runs" is satisfied by a manifest entry | `rust/sele4n-hal/Cargo.toml`, `rust/sele4n-hal/src/queued_rw_lock.rs`, `.github/workflows/` | L |
| RR6.21 | Add a nightly `miri` job for the queued lock | `.github/workflows/` | M |
| RR6.22 | Raise the FIFO and stress iteration counts to the plan's stated thresholds | `rust/sele4n-hal/src/queued_rw_lock.rs` | S |
| RR6.23 | Prove the D-2.5 writer-bounded-wait statement as specified — the ingredients exist; only a single-state `_weak` corollary landed | `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` | M |
| RR6.24 | Repoint the R-10 aggregator entry at the theorem that proves writer liveness; keep the safety theorem registered under its accurate name | `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` | S |
| RR6.25 | Plan corrections: the retired-MCS design section, the D-1.9 landed row, the false §3.2.6.1 theorem statement, and the Appendix A commands that name a nonexistent script | `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` | M |
| RR6.26 | Retitle the plan: it is no longer post-v1.0.0; add an SM2.C-defer row to `docs/REGISTERED_DEBT.md` with closure target RR6 — this phase, not the boot-path phase that precedes it | (2 files) | S |
| RR6.27 | Register Track D of `SMP_FINE_LOCK_MIGRATION_PLAN.md` — the commit-model partitioning, which that plan seam-gates to SM10.1 — as a named SM10.1 dependency in `SMP_RELEASE_CLOSURE_PLAN.md` §2 and the debt register, so the one part of the fine-lock work WS-RR cannot land is tracked rather than absorbed silently | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`, `docs/REGISTERED_DEBT.md` | S |

**Acceptance**: the deployed RwLock is the one the Lean spec describes; the
Tier-5 oracle drives real locks; neither refinement theorem assumes its own
conclusion or contains a tautological conjunct; `loom` and `miri` gates run.

**Note on RR6.4–RR6.8 and RR6.15–RR6.19** (the rows that replaced the phase's
two XLs).  The two refinements split along different seams, because the two
locks fail to be verified for different reasons.

*The queued lock has no concrete model at all* (RR6.4–RR6.8).  It is a **ticket**
protocol over four atomic words, and `ConcreteRwLockOp` models a single one, so
the alphabet, the ticket protocol's own well-formedness, the
waiters-to-ticket-interval simulation, the per-entry-point block lemmas and
their composition are five separable objects — and the ticket invariant
(RR6.5) is the load-bearing one: it is the mutual-exclusion argument and the
termination argument for both spin loops.

*The CAS-retry lock has a model whose main theorem assumes its own conclusion*
(RR6.15–RR6.19), and closing it is not uniformly hard.  Two constructors have
no discharge lemma at all (RR6.17), which is bookkeeping; the trace-shape
predicate (RR6.15) is the phase's stated mitigation and lands first so the
composition has something to consume; and one row, RR6.16, is the actual
obstacle — the abstract spec promotes a waiter on release and the concrete lock
has no queue to promote from, so the four existing release discharges sidestep
the case with `_no_promote` / `_empty_queue` side conditions and the
composition provably cannot close over them.  Its row carries the
counterexample, so the phase does not discover it mid-proof.

**RR6.11 decides the fate of `rw_lock.rs`, and RR6.15–RR6.19 complete its
refinement.**  Read together: if RR6.11 retires the CAS-retry lock once
RR6.10 has deployed the queued one, the D-4 rows retire with it and the
acceptance clause below is met by their deletion rather than their proof.  If
it is retained for compatibility, they are owed in full.  The decision is
RR6.11's; it is recorded here rather than in either row because a sub-task may
not point forward at one that has not run.

RR6.4–RR6.8 and RR6.9 sit **before** RR6.10 deliberately. RR6.10 changes which
lock the kernel deploys, and `RwLockRefinement.lean` models the CAS-retry
implementation — so deploying first would leave several versions shipping a core
concurrency primitive with no refinement to the spec it is claimed to satisfy.
The model, then the corollary, then the switch.

### RR7 — Medium-severity sweep

Every confirmed medium finding, batched so each PR touches one subsystem,
plus the §7 low-severity rows whose remedy is code rather than prose.
**65 findings**: the 45 still open of the register's §6 table — RR7.5's
re-sequencing item closed at v0.34.36 — the four §4 rows RR7.1–RR7.4 that are
remediation work rather than security fixes, the 15 §7 rows RR0.11's triage
routed here (RR7.33–RR7.37), and the one uncovered lock domain the RR0 review
round found with no owner that would close it (RR7.38). Every other
§4 item is owned by the phase carrying its siblings — the unhandled VM-fault
loop and the fault-return ABI convention by RR4, the cancellation-NI hypothesis
by RR2, the RwLock/Rust refinement gap by RR6, the `suspend_thread_inner`
bracket and the `debug_assert!` tripwires by RR5, and the stale `trap.rs`
comment with low finding 96 — and none is counted twice. The ownership is
stated per item rather than as a total because two §4 rows had no owner until
review found them.

The register's §6 table remains the authoritative per-item list; the batches
below say who owns what, and their counts sum to the register's totals so the
acceptance gate below can actually be checked against the work list.

**Reading the findings column across RR7.7–RR7.13.**  Those seven rows are the
fine-lock migration's Tracks B and C, and they close **one** register finding
between them — the false v1.0.0 "per-object reader-writer fine locks" claim,
which becomes true when the dispatch body brackets.  The count therefore sits
on RR7.12, the row that makes it true, and the other six carry `—` rather than
`0`: they are prerequisites of that row, not rows that own nothing.  The column
still sums to the acceptance total below, which is the point of keeping it a
count rather than a label.

| Sub | Description | Findings | Est |
|-----|-------------|----------|-----|
| RR7.1 | Boot MMU corrections: 960 MiB of RAM mapped as Device, and nothing mapped above 4 GiB (§4).  **LANDED v0.34.57**: the tables are derived from `mmu::boot_mapping_for` (mirroring `rpi5MemoryMapForConfig`) and sized to the board's own `/memory` node.  The same cut fixed a defect the finding did not name — the table `TTBR0_EL1` pointed at held *level-1* block descriptors while `T0SZ = 16` makes level 0 the initial lookup level, so the boot MMU enable would have translation-faulted on the first fetch | 1 | L |
| RR7.2 | Satisfy the FFI unqualified boot identity-map claim, which the boot tables do not provide above 3 GiB — per the implement-the-improvement rule, extend the tables rather than qualify the claim (§4).  **LANDED v0.34.57**: RR7.1 makes the claim true and this row makes it *enforced* — the whole `ICacheInvalidation` operand family, plus the sibling `cache_clean_pagetable_range` seam, refuses an out-of-window operand at the extent it maintains and halts rather than issuing an instruction whose address is not the address the kernel means | 1 | M |
| RR7.3 | Extend the flagship "syscall entry implies capability held" theorem to the live checked dispatch path; it covers only the legacy path today (§4).  **LANDED v0.34.57**: `dispatchSyscallChecked_requires_right` and `syscallEntryChecked_implies_capability_held` over the executing core, through **both** gate shapes (the audit pair checks its right in the arm, so a conclusion read off the gate alone is false for it); `…_of_pre_state` restates it on the trapped-in state via `resolveCapAddress_congr_objects`, and `syscallDispatchFromAbi_implies_capability_held` carries it to the exported seam | 1 | L |
| RR7.4 | Give the `_atomic_under_lockSet` family operation-specific content: its atomicity half is today a `rfl` instance of a body-agnostic lemma, and five `lockSet_observer_atomic_on` instantiations are missing (§4).  **LANDED v0.34.57**: all five landed (call, reply, replyRecv, signal, wait), each stated for *every* thread or notification rather than a chosen decisive one, over two observers and a packaged capstone declared once — which also removed the four hand-rolled copies the cancellation carried | 1 | M |
| RR7.5 | Add SM10's three `contextRestoreSeamLive` prerequisites, absent from its dependencies, sub-tasks and acceptance gate.  **LANDED v0.34.59**: the `VSpaceRoot → TTBR0` binding is `BP7.1`+`BP7.2`, the full outgoing-frame save `BP7.3`, and the per-core staging `BP7.4`, each a numbered sub-task of [`SMP_BOOT_PATH_PLAN.md`](SMP_BOOT_PATH_PLAN.md) with its own acceptance-gate box, and `BP7.6` is the flip they gate.  This row's two other items were already **closed**: §1's false "all substantive SMP work is complete" phase goal (RR0.4, v0.34.26) and the sub-phase re-sequencing (v0.34.36 — SM10 is now numbered SM10.1..SM10.6 in execution order) | 1 | M |
| RR7.6 | Production `native_decide`: six uses are live in Lean at HEAD while §5's release-note template claims zero. Per implement-the-improvement, replace them with proofs rather than weaken the claim.  **LANDED v0.34.47** (test-performance audit): the inventories store packed keys (`SeLe4n/PackedString.lean`), which made the kernel-checked proof cheap enough to use everywhere — production Lean now has zero `native_decide` | 1 | L |
| RR7.7 | Fine locks, Track B: the endpoint-caps footprint declaration and its algebra. Add the receiver-CNode optional to `lockSet_endpointSend` / `lockSet_endpointCall` as the outermost `lockSetExtendOpt`s (`some r` adds `(cnodeLock r, .write)` **and** `(stateLevelLock, .write)`; `none` is the identity, so every capless pin survives by `rfl`), fold `lockSet_endpointCallWithCaps` into it, raise the consistency tiers and `permittedKinds`, and **widen the `lockSetTransitions_within_bound` send/call conjunct arity** in `Deadlock.lean` — the silent-unbounding hazard, the same shape as the SM9.C `notificationSignal` fix. No coverage claim yet  **LANDED v0.34.60**: `destCnodeObjId` is the outermost pair of optionals on `lockSet_endpointSend` and `lockSet_endpointCall` — `some r` declares `(cnodeLock r, .write)` for the slot insert **and** `(stateLevelLock, .write)` for the CDT maps the install writes, `none` is the identity so every capless pin survives by `rfl` (`lockSet_endpointSend_capless`, `lockSet_endpointCall_capless`).  `lockSet_endpointCallWithCaps` **is** the base footprint at `some` (`lockSet_endpointCallWithCaps_eq_call_some`, by `rfl`), so the transfer's obligations are declared in one place rather than two that drift — which is how the state-level member came to be in neither.  `permittedKinds` gains `.objStore` on `.send` and `.call` (level 0, acquired first, ladder unchanged), the consistency theorems are restated over **every** `destCnode`, and the `lockSetTransitions_within_bound` send/call conjuncts are widened — the latter also closing a live instance of the same hazard, since the call conjunct bounded only the *reply-less* footprint while its lemma was general.  The size lemmas lost their default arguments so a bare reference cannot under-apply them again | — | L |
| RR7.8 | Fine locks, Track B: `ipcUnwrapCaps` coverage and the debt deletion — the closure. Route the state-resolved `lockSet_endpointCallOnCore` (and a new send-side twin) through RR7.7's optional, prove the transfer's write set is contained in the declared footprint on both arms, and only then delete `UncoveredLockDomain.capTransferReceiverCnode` — the constructor, the violation theorem, the inventory arithmetic, the Tier-3 anchors — replacing its `run_check`s with `run_negative_check` pins so the domain cannot come back. **The deletion is the last step, not the first**: an `UncoveredLockDomain` entry is deleted when the domain is covered, never to make a count fall  **LANDED v0.34.61**: `rendezvousCapsDestination?` is the destination both WithCaps arms evaluate, and since this cut both read it from the **pre**-state — the state whose locks the bracket took.  They read it from the post-state before; the two agree because nothing between them writes `TCB.cspaceRoot`, but that is a fact about the tree a later transition could falsify silently, where "both read the same state" is a fact about the code, so the property is made structural rather than proved.  `lockSet_endpointCallOnCore` takes the message and resolves the optional through it; `lockSet_endpointSendOnCore` is the new send-side twin (the send had no resolved footprint at all, since every capless member was an argument).  The closure is `endpointSendDualWithCaps_object_writes_declared` / `endpointCallWithCaps_object_writes_declared`: **every object either arm's transfer changes is declared write-mode in the footprint its bracket acquires**, composed from the existing `ipcUnwrapCaps_preserves_objects_ne`, the two new path reductions, and the four membership theorems.  Only then the deletion — constructor, violation theorem, inventory arithmetic and the fixture line that pinned the gap positively — with the Tier-3 `run_check`s replaced by `run_negative_check`s so none of them can come back.  Two things the cut also corrected: the inventory's "six of them today" prose, which had drifted to seven and is now not a number at all; and the fixture claim that the content-moving footprints carry no coarse table lock, which RR7.7 **narrowed** rather than broke — the capless hot path still carries none, and a caps-carrying rendezvous carries it for the CDT maps, both pinned | — | L |
| RR7.9 | Fine locks, Track B: CDT coverage on `cspaceMint` / `cspaceCopy` / `cspaceMove` / `cspaceDelete` — declare `(stateLevelLock, .write)` on each of the four footprints, prove the coverage (one write shape across all four), and correct `capabilityOp_modifiedFields` in `CrossSubsystem.lean`, which lists `[.objects, .lifecycle]` and omits the four CDT `StateField` constructors the operations actually write. An independent object from the two rows above, so it may land in either order relative to them.  **LANDED v0.34.62**: all four footprints declare `(stateLevelLock, .write)` unconditionally — `cspaceMint`, `cspaceCopy` and `cspaceMove` mint CDT nodes for both endpoints (advancing `cdtNextNode` and both keyed maps) and add an edge, and `cspaceDelete` removes one, none of which decomposes by object.  `permittedKinds` gains `.objStore` on all four plus `.mintReplyCap`; five membership theorems pin the member per footprint (one each, not one shared shape, so dropping it from any single definition stops elaboration); and `capabilityOps_footprints_share_serialization` is the statement the domain existed for — no two capability operations are ever disjoint, whatever CNodes they name.  `capabilityOp_modifiedFields` is corrected from `[.objects, .lifecycle]` to include the four CDT `StateField` constructors: these lists support *disjointness* arguments, so an omission made two contending operations look independent.  `UncoveredLockDomain.cdtNodeAllocation` is deleted, its Tier-3 `run_check`s replaced by a negative | — | M |
| RR7.10 | Fine locks, Track C: generalize the production `lockSetForSyscall` resolver from `(sid, callerTid, targetTid, st)` to decoded-driven resolution — IPC operands are endpoint and notification `ObjId`s, not `ThreadId`s, so the current signature cannot name the objects the IPC arms lock. Signature only: `.tcbSuspend` keeps its answer, the other 32 arms still answer `none`, and `lockSetForSyscall_undeclared_none` is restated over the new shape. Placed in production referencing production footprints only, so the staged resolvers stay staged.  **LANDED v0.34.63**: `SyscallLockOperands` carries the caller, an optional **thread** target (`.tcbSuspend`'s victim), an optional **object** target (an endpoint, a notification, a CNode, a SchedContext) and the message an IPC arm carries.  The two targets are separate fields rather than one because a syscall is directed at one or the other and never at both, and the message is there because whether a rendezvous footprint includes a capability-transfer destination is a property of what it carries (RR7.7).  The generalisation is behaviour-preserving and says so: `lockSetForSyscall_tcbSuspend_ofThreadTarget` is `rfl` against the answer this row's own predecessor gave, and `_no_target` pins the fail-closed arm.  A Tier-3 negative pins that the two-`ThreadId` signature cannot come back.  Also corrected in passing: the entry resolver reinterpreted a capability's `ObjId` **as** a thread id, which for an endpoint capability is a different object with the same number — that coercion is now confined to the thread-directed constructor rather than sitting on the resolver's only path | — | M |
| RR7.11 | Fine locks, Track C: the IPC hot-path footprint declarations — one step per arm for send, call, reply, replyRecv, receive, signal and wait, each declaring that arm's `lockSetForSyscall` footprint from the decoded operands together with its coverage proof (the transition's write set within the declared footprint). Send and call consume RR7.7's caps optional. The remaining arms stay `none`, and stay proven so.  **LANDED v0.34.64**: eight of the thirty-five arms are declared, each wired to the SM6 state-resolved footprint its cross-core transition is already stated against, so the declaration and the transition read one expression.  `SyscallLockOperands` gained `targetReply`, since `.reply` and `.replyRecv` name a `ReplyId` and `.replyRecv` names an endpoint *as well*; `lockSet_endpointReceiveOnCore` is the resolved receive footprint that did not exist.  Fail-closed where an operand is missing: `.send` and `.call` answer `none` without a **message**, because whether the receiver's CSpace root and the state-level lock are members is a property of what the message carries, and the capless guess is the false footprint this family exists to refuse.  The negative is restated over `declaredFootprintSyscall`, and `lockSetForSyscall_ofThreadTarget_undeclared` is why the staged SM8.D entry resolver is unchanged: it supplies a thread target, so the seven object- and reply-directed arms answer `none` there.  Supplying the rest at the production entry belongs to the bracketing row below, because the message is built by `resolveExtraCaps`, which mints CDT nodes — so which state the footprint is resolved at is inseparable from the acquire/re-resolve/refuse discipline.  **Two findings closed in passing.**  (a) The *receive* side writes the CDT: `ipcTransferSingleCap` is one function, so a receive dequeuing a caps-bearing sender mints a derivation node and adds an edge exactly as a send does, and `lockSet_endpointReceive` / `lockSet_replyRecv` declared the state-level write on neither — two receives into different CSpaces were provably disjoint while read-modify-writing one derivation map, the lost-update shape RR7.7 closed on the sending half.  Both now carry it, conditioned on the same `installsCaps` flag the transition branches on, with `capsCarryingIpcArms_footprints_share_serialization` the statement that no two of the four caps-reaching arms are ever disjoint.  That makes the widest footprint nine members, so **`maxLockSetSize` moves 8 → 9** and the WCRT headline widens by an eighth — the honest cost of a footprint that covers its own writes, and the same trade the hierarchical-CBS plan's D21 records for its own move of that constant.  Not exploitable at HEAD, since the `@[export]` bodies do not bracket yet; closed here because the row that makes these footprints operative is the next one, which is the plan's own ordering rule.  (b) Five scheduler `_size_le_maxLockSetSize` theorems stated `≤ 8` literally, so each was a claim about a numeral while its name promised a relation; raising the constant surfaced it, and the constant moved to `Locks/LockSet.lean` so every footprint-declaring module can name it.  Also generalised in passing: three membership theorems were stated at their optionals' defaults, so the shape a live arm actually declares was outside them, and `lockSet_endpointCall_caller_tcb_write_mem`'s receiver-distinctness hypothesis is gone — a coinciding key merges under `AccessMode.lub`, so it excluded a case the conclusion already covered | — | L |
| RR7.12 | Fine locks, Track C: bracket the dispatch body — wire `syscallDispatchCrossCoreEntry` through the revalidated `withLockSet` bracket (resolve, acquire, re-resolve, refuse on change) with the fail-closed `none` fallback that leaves undeclared syscalls running exactly as today, keeping `scheduleLocalSuccessorLive` inside the closure and the diff taken against the bracketed post-state.  Consumes RR7.10's operands and RR7.11's eight declared footprints, and owes the piece RR7.11 deliberately left: the production entry must build each arm's `SyscallLockOperands` from its own decode — the endpoint or notification the capability names, the reply object, and (for `.send` and `.call`) the message, which is built by `resolveExtraCaps` and therefore forces this row to say which state the footprint is resolved at. **This is the row that makes the v1.0.0 claim true**, so it carries the finding: until it lands, "per-object reader-writer fine locks" describes one arm of thirty-five. It also flips the `PerCoreWcrt.lean` sentence asserting the run loop acquires its footprints, which is false while the body does not bracket.  **LANDED v0.34.65**: `syscallDispatchCrossCoreEntry`'s atomic step — extracted verbatim as `syscallDispatchCrossCoreStep` so there was something to wrap — runs inside `syscallDispatchCrossCoreBracketedStep`.  `SeLe4n/Kernel/SyscallLockBracket.lean` holds the mechanism in three pieces: `abiEntryPlan`, the prefix `syscallDispatchFromAbi` performs before it dispatches, named once and tied to what the dispatch runs by `abiEntryPlan_dispatches` — a footprint resolved from a decode the dispatch does not use is a footprint for a different operation; `abiEntryLockOperands`, which resolves the capability exactly as `dispatchSyscallChecked` builds its gate and turns its target into operands, fail-closed on an unresolvable caller, a **multi-level** CSpace resolution (a deeper walk selects the target through interior CNodes no declared footprint holds a lock on, and a `LockSet` capped at `maxLockSetSize` cannot name a path bounded only by the address width), a capability that does not resolve at the required rights, and a sentinel thread target; and `runUnderDeclaredLockSet`, the revalidated acquire / re-resolve / act / unwind with **both** guard conditions — the resolution unchanged *and* the footprint actually held, since `withLockSet` runs its action whether or not the acquisition was granted — unwinding with `unwindAll` so a contended member is withdrawn rather than left queued.  The fallback is definitional (`syscallDispatchCrossCoreBracketedStep_undeclared`), which is what makes landing the bracket safe while twenty-seven arms are undeclared, and a refusal commits nothing but the unwinding and returns `.illegalState` — unreachable today, since the commit is one global read-modify-write, and a dedicated `.lockContention` is worth its ABI cost when that changes.  The `PerCoreWcrt.lean` sentence is flipped to say which half acquires: the syscall seam does, the per-core scheduler entries do not — that is the `schedulerDomain` uncovered-lock-domain registration, closed by a later Track C row — so live WCRT remains the global entry lock's.  A runtime witness in `SmpCrossCoreCallSuite` drives a `.tcbSuspend` decode through the seam and pins that the **committed** arm is taken, that the bracketed step returns the unbracketed step's frame, and that every declared member is released afterwards — without it the row would ship a mechanism nobody had seen engage, since the smoke and trace tiers pass either way | 1 | L |
| RR7.13 | Fine locks, Track C: the export-body gate that keeps it true — a Tier-1 elaborated-environment probe over the `@[export]` state-committing bodies, failing any that commits without a `withLockSet` bracket or a recorded fail-closed `none`, with a self-test that plants a bare-commit body and asserts detection. Derived from the export set rather than a list of the bodies that exist today, so the next seam is covered by construction — the enumeration-for-derivation shape the key conventions warn about.  **LANDED v0.34.66**: `SeLe4n/Testing/ExportCommitDisciplineCensus.lean`, decided by the elaborator (building it *is* the check, as `BootEntryContract` is).  The set is derived by transitive `getUsedConstants` reachability from each `@[export]` to a `kernelStateRef` write, and reconciled against a registry in **both** directions: an unclassified committing seam hides a gap, a stale entry overstates coverage.  A `bracketed` record must be substantiated by reachability to `runUnderDeclaredLockSet` or `Concurrency.withLockSet`; an `unbracketed` one must carry a reason.  **Seven seams commit, two bracket** — the syscall entry and the raw suspend — and the five that do not each name why: three are the scheduler domain, two are the fault delivery, for which `lockSetForSyscall` declares no footprint because a fault is not a syscall.  The witnesses are the plan's self-test: a planted **bare-commit** body must be refused as bracketed and accepted only with a recorded reason, a commit reached through a helper must be seen (so the walk is transitive, not one level), a read-only body must not be, an empty reason must be refused, and the reconciliation is a pure function self-tested on synthetic sets — planting a committing `@[export]` to exercise it in place would emit a real symbol into the kernel's archive.  Verified by mutation: exporting the bare-commit witness fails the build with the unclassified-seam message.  The walk over-approximates (a mentioned constant counts as reached) and says so, which is the fail-closed direction for a census that decides *must be classified* | — | M |
| RR7.14 | Cancellation/timeout error-frame staging, unimplemented at HEAD and owed before the context-restore seam flips.  **LANDED v0.34.67**: both unblocking paths stage, and they stage **different** errors, because they are different facts — `timeoutThread` stages `Architecture.timeoutFrame` (`.ipcTimeout`: the budget expired under a well-formed operation the caller may reissue) and `cancelIpcBlocking`'s four blocked arms stage `Architecture.cancelledIpcFrame` (`.ipcCancelled`, a **new** discriminant at 57: the operation was destroyed, so reissuing may be meaningless and a userspace library cannot write a correct retry against a conflated code).  seL4 answers this by setting the thread `Restart`; this kernel has no restart state, so the crossing has to end in an error the caller can distinguish.  Each is folded into the TCB record its transition was already writing, so neither path commits a second object; `restoreToReadyStaging` is the one field clear both spellings instantiate, so a field added to one and not the other fails to elaborate (`restoreToReadyCancelled_tcb`), and its framing, `invExt`, `ipcInvariant`, `tcb_lookup`, identity and projection results are stated once and instantiated twice.  **Two paths deliberately stage nothing** and are pinned as negatives: the `.ready` arm (the thread was not blocked) and `restoreToReady` itself — the *resume* spelling of the same clear — because `.tcbResume` restarts a thread where it was and overwriting `x0`-`x5` would destroy the window the restart preserves.  **The invariant premise had to be corrected, not worked around**: `objects_change_preserves_schedulerInvariantStructuralRegNodup_smp` demanded register-context stability at *every* thread, while `contextMatchesCurrentOnCore` reads only the **current** thread's — strictly stronger than the conclusion needs, and it refused exactly this write.  `hReg` is now scoped to the current thread and `storeObject_tcb_preserves_…` takes a disjunction (unchanged context **or** current on no core), the second discharged from the `hNotCur` the timeout caller already carries.  The information-flow half needed no new argument: the frame goes into the victim's **own** TCB, the object the high-thread premise already covers, which holds only because `writeReturnFrameToTcb` does not touch `machine`.  Nineteen runtime checks across the two suites, driven against a victim carrying a recognisable stale window so "the frame is right" and "the stale window is gone" are two assertions.  Closes the WS-RA §9 obligation registered against SM10.1 | 1 | M |
| RR7.15 | Boot-path sweep mediums.  **LANDED v0.34.59**: SM10.1 is split out of the release cut into [`SMP_BOOT_PATH_PLAN.md`](SMP_BOOT_PATH_PLAN.md) — WS-BP, **34 sub-tasks across 8 phases `BP1..BP8`**, numbered in execution order, with an acceptance gate whose every box is ticked by an executed run rather than by an artefact existing.  Each finding is scheduled to a named row: bare-metal Lean runtime hosting is `BP2` (five sub-tasks, the shim list *derived* from the cross archive's unresolved symbols rather than guessed), the bootable target is `BP5`, the re-scope is the plan itself, the context switch and user address space are `BP7.1`–`BP7.2`, and the RPi5 `PlatformConfig` with its root task is `BP3`.  **Nothing is renumbered**: WS-BP takes its own prefix, so `SM10.1.1` keeps the meaning three CHANGELOG entries cite and `BP5.3` produces what it packages — the collision the release-closure plan's §1.1 note identified and deferred, resolved the way that note named.  **Landed in one cut with RR7.5**, and the reason belongs here rather than in that row: RR7.5 schedules three obligations *into* the plan this row creates, so the dependency runs backwards through the numbering.  The two IDs are cited in a shipped CHANGELOG entry and are frozen, so the record is the note rather than a renumber — and the plan the two produced numbers its own work in execution order, which is the property that matters downstream | 5 | M |
| RR7.16 | Rust HAL mediums.  **LANDED v0.34.58**: the two implementable findings are implemented — `UartLock` delegates to the verified `TicketLock` (the post-SM2 swap SM1.G.1's comment promised while only core 0 ran), and `tlbi_for_sharing`'s routing became testable by splitting the decision out as `tlbi_variant_for : (SharingDomain, TlbInvalidation) → TlbiVariant`, checked at all eight pairs by six host witnesses.  The two links a host test cannot reach — arm → primitive, primitive → mnemonic — are held by `check_tlbi_broadcast_discipline.py`, derived from the enum and the `asm!` templates rather than enumerated.  The secondary-entry staging finding closed at RR5.15.  The QEMU bring-up finding is closed **by unchecking** the two SM1.H acceptance boxes: the script SKIPs on every run for want of a `[[bin]]` target, so the boxes claimed a hardware behaviour nothing has observed, and restating them as "script authored" would trade a behaviour criterion for an artifact-existence one.  Registered against SM10.1.1 | 4 | M |
| RR7.17 | Syscall return ABI mediums.  **LANDED v0.34.68**: the register's four rows, of which one (SM10.1's two inherited obligations) closed at RR7.5/RR7.15.  (a) `blockingArm_returns_no_frame` was a §10 catalogue line with no artefact — **authored**, with the family the property needs rather than the one-line restatement of the `if` that would satisfy a name check: the characterisation both ways (`syscallReturnOutcome_blocks_iff`), the id-independence §3.5 rests on, the statement that the staged registers are not consulted on that arm — proved by **varying** them, which is the token-preserving mutation — and the composition onto the exported seam (`syscallDispatchFromAbi_blocked_returns_no_frame`), which is where the trap layer reads it.  (b) The Rust `ReturnShape` mirror ended in `_ => ReturnShape::Unit`, so a new value-returning syscall would have read `Unit` there while Lean refused to build until it was classified.  The wildcard is gone (rustc's exhaustiveness now plays Lean's totality), but exhaustiveness is not agreement: two independently maintained total functions can still disagree, so **both sides render the same `id → shape` table against one fixture** (`tests/fixtures/syscall_return_shape.expected`), Lean from `syscallReturnShape` and Rust from the mirror.  Verified by two mutations — a deleting one that fails compilation and a preserving one that moves a variant between shape groups.  (c) The application-IPC-label debt is **lifted out of the review narrative** into the plan's §9 with the aliasing constraint that rules out the naive pass-through (a send capability to a fault endpoint could mint a forged `seL4_Fault_tag`), two candidate designs, and WS-CB as the named owner, cross-registered in the CBS plan and the debt register.  **Two findings closed in passing.**  The `KernelError` count was a literal at nine sites and had gone stale in a trace line one cut after RR7.14 widened it; it is now `kernelErrorCount`, bounded from **both** sides (`toDiscriminant_lt` and `kernelErrorCount_tight`) so it is the least strict upper bound and cannot drift either way.  And a **gate defect**: `test_lib.sh` routes every `rg`/`grep` anchor through the code view, but the overlay linked `.rs` files whole — so 215 Tier-3 anchors over Rust read raw text and "gates read code, prose reads prose" held for Lean only.  The first negative written against a Rust construct was satisfied by the comment explaining what it forbids, which is how it surfaced.  The overlay now strips Rust through `rust_code_view.code` (the view the Python gates already read, so there is one Rust view and not two), `test_code_view_wiring.sh` gained the Rust half of all three directions in both comment forms, and re-running Tier 3 over the corrected view broke **zero** existing anchors | 4 | M |
| RR7.18 | Per-object lock mediums.  **LANDED v0.34.69**: four register rows, two of which the fine-lock rows above already closed (finding 14, the v1.0.0 fine-lock claim, at RR7.12; finding 16's two SM3.B-owned domains at RR7.8/RR7.9, its third — the splice-neighbour queue-ownership domain — being a later Track-C row's, which names this row back).  **Finding 15** was that `lockSetTransitions_within_bound` covered 30 of the tree's `LockSet` declarations — the count was 31 at HEAD, and the tree declares **47**.  The four missing from the conjunction (`mintReplyCap`, `tcbBindNotification`, `tcbUnbindNotification`, `tcbSetAffinity`) are added, and so are the thirteen the finding did not name: every state-resolved `*OnCore` footprint — the ones RR7.12's bracket actually **acquires**, so the bound bounded-wait needs was on the argument-taking bases and not on the sets the seam holds — and the four cancellation footprints, including `lockSet_cancelIpcBlockingOnCore`, which is what the `.tcbSuspend` bracket resolves.  **The mechanism, not the instances**: `SeLe4n/Testing/LockFootprintBoundCensus.lean` derives the footprint set from the elaborated environment (a `def` whose type ends in `LockSet`, named `lockSet_…`) and requires each `<name>_size_le` to have **exactly** the statement built from the definition's own telescope, decided by one `isDefEq`.  That second half is the one that keeps biting: a footprint gains a trailing `Option` with a `:= none` default, the existing bound keeps elaborating because the default fills it in silently, and the live shape is left unbounded under a name that promises otherwise — it happened to `notificationSignal` (SM9.C.8), `endpointReceive` (PR #873 round 8), `endpointSend`/`endpointCall` (RR7.7), and **the census found a fifth**: `lockSet_endpointReply_size_le` was stated at five of its six arguments, so the shape the live `.reply` dispatch resolves — `lockSet_endpointReplyOnCore` reads `target.replyObject`, and a reply always has one — had no bound at all.  `lockSet_endpointCall_size_le` carries a comment telling the next author not to default arguments there; a comment is a convention, this is a mechanism.  Verified by a token-preserving mutation that drops one binder and keeps the name.  **Finding 17** (stale artefact names and counts) is fixed at the source rather than by deleting the cites: `Sm3EInventory.lean` → `SerializabilityInventory.lean` (the old name was also a workstream-ID name the naming rule forbids), "all 25 lockSets" → 35 with the census as the checker, the never-authored `walkAndAcquire_terminates` → the three theorems that realise SM3.C.11.e, the 90-entry inventory figure boxed as that cut's record with `lockSetTheorems_count` (111) as the live one, and the spec's "the migration lands with SM5's per-core scheduler integration" corrected — it did not; the syscall seam brackets since RR7.12 and the three scheduler entries still do not | 4 | M |
| RR7.19 | Fine-lock migration mediums | 3 | M |
| RR7.20 | TLB shootdown mediums | 3 | M |
| RR7.21 | Debt-register mediums | 3 | M |
| RR7.22 | Cross-core IPC mediums | 2 | S |
| RR7.23 | Declassification mediums | 2 | S |
| RR7.24 | Panic-hang remediation mediums | 2 | S |
| RR7.25 | RwLock-deferred mediums | 2 | S |
| RR7.26 | Implement-the-improvement sweep: route the per-core scheduler entries through the HAL context-switch seam.  **LANDED v0.34.58**: all five state-committing per-core entries record the `currentOnCore` their own atomic step committed, through `recordCommittedCurrentThreadHw`; a vacated core clears the mirror rather than leaving it naming a descheduled thread, and `switchToThreadHw` finally has production callers | 1 | S |
| RR7.27 | Implement-the-improvement sweep: the DeviceTree-to-`PlatformConfig` boot bridge — a platform/boot surface unrelated to the row above, so its own task.  **LANDED v0.34.58**: `PlatformConfig.fromDeviceTree` plus the board-versus-binding check (RAM against `rpi5MachineConfig`, MMIO against `RPi5.mmioRegions`) and the production consumer `bootAndInitialiseRPi5FromDtbOrHalt`, which boots through the checked entry or parks the PE.  `DeviceTree.fromDtbFull` has a caller.  The pointer→`ByteArray` read stays SM10.1's, as the finding assigns it | 1 | S |
| RR7.28 | IPC de-threading medium | 1 | S |
| RR7.29 | Reply objects medium | 1 | S |
| RR7.30 | SMP foundations medium | 1 | S |
| RR7.31 | Master plan medium | 1 | S |
| RR7.32 | Doc-sync medium | 1 | S |
| RR7.33 | Unwired proven structures (§7): the four per-core statistics accessors that are declared, wrapped and proven with zero consumers, and `ipcUnwrapCaps`'s dead `senderCspaceRoot`, whose own registered closure target passed without it | 2 | M |
| RR7.34 | Plan-named artefacts that do not exist (§7): `donation_perCore_consistent`, the two unresolvable SM8 theorem names — one of them cited from a **live docstring** — `notification_waiters_nodup`, the SM0-cited Tier-0 gate script, and the four `CLAIM_EVIDENCE_INDEX.md` identifiers.  Per implement-the-improvement each is authored, not struck from the catalogue | 5 | L |
| RR7.35 | Gate coverage the claims assume (§7): the nine `dev_history` cross-references still in production sources plus the gate that would enforce their absence; the three declared `lean_exe` targets no gate compiles; the SMP-M1 surface difference no gate or phase owns; and the documentation-metrics sync, which covers two files while the sync matrix claims the transitive set — eleven i18n READMEs and four GitBook chapters carry `v0.33.101`-era metrics | 4 | M |
| RR7.36 | Boot-core-pinned thread-state classification (§7): `inferThreadState` / `syncThreadStates` / `threadStateConsistent` read `bootCoreId`, so a thread running on a secondary core classifies as `.Inactive`.  **The lift itself is RR5.10**, which needs it before the boot path installs a secondary core's idle TCB; this row verifies the finding closed and sweeps the consumers RR5.10 did not have to touch — the same relation RR7.25 has to RR6 and RR7.28 to RR3, per §2.3.  If RR5 landed it whole, that is what this row records | 1 | S |
| RR7.37 | Test-surface corrections (§7): the D-1 admission-order `decide` fixtures the RwLock gate asks for and the suite lacks; the `r4a_`/`r4c_` test identifiers that encode sub-task codes against the plan's own self-certified naming rule; and the vacuous `trap.rs` SVC test with its stale "pre-FFI stub" prose | 3 | M |
| RR7.38 | Splice-neighbour queue ownership (`UncoveredLockDomain.queueOwnershipProtocol`) — **this is the third of the three SM3.B-owned domains the register's §6 finding 16 names**, the other two having closed at RR7.8 and RR7.9, so RR7.18 records it here rather than claiming it: `queueOwnership_violated_by_tcbSetPriority` states the violation as a `¬`, and the domain had no owner that would close it — RR0.9 pointed it at fine-lock Track B, whose rows close `capTransferReceiverCnode` (RR7.8) and `cdtNodeAllocation` (RR7.9) but never touch splice neighbours.  Either extend the `tcbSetPriority` footprint to declare the queue-owning locks, or hold the endpoint lock across the splice; the `UncoveredLockDomain` entry is deleted only when the domain is actually covered | 1 | M |
| RR7.39 | Fine locks, Track C closure — the scheduler domain (`UncoveredLockDomain.schedulerDomain`; the fine-lock plan's named follow-on SM3.C.9.b). The per-core scheduler entries the RR7.12 bracket does not cover — the timer tick, the `.reschedule` SGI receiver and the secondary bring-up entry — commit run-queue and replenish-queue state under the global entry lock only. Declare their `SchedLockId` footprints from the model footprints that already exist (`timerTickOnCoreLockSet`, `timerTickOnCoreCompleteLockSet`, `chooseThreadOnCoreLockSet`, `switchToThreadOnCoreLockSet`, `wakeThreadLockSet`, `enqueueIdleThreadOnCoreLockSet`, `advanceDomainOnCoreLockSet`), bracket the export bodies through `withLockSet` with RR7.12's revalidate-and-refuse discipline, prove each transition's write set within its footprint, and only then delete the constructor, its violation theorem and the inventory arithmetic, replacing the Tier-3 `run_check`s with `run_negative_check` pins (RR7.8's deletion-last order). Consumes RR7.12 | — | L |
| RR7.40 | Fine locks, Track C closure — the dynamic PIP chain (`dynamicPipChain`). The boost/revert walk's per-member TCB and home-core run-queue write locks are discovered as the walk proceeds, so no pre-state footprint can name them. Route the walk through SM3.C.11's `DynamicChainExtension` inside the RR7.12 bracket — extend the held set hand-over-hand as each member is discovered, in `LockKind` order so the deadlock-freedom argument survives — prove the walk's writes stay within the extended set and that the extension composes with the bracket's revalidation, and only then delete the constructor under the same deletion-last discipline. Consumes RR7.12 | — | L |
| RR7.41 | Fine locks, Track C closure — the interior CNodes of a multi-level CSpace walk (`cspaceWalkInteriorCnodes`). `resolveCapAddress` descends through child CNodes the arguments cannot name, so every CPtr-resolving footprint holds only the root. Make the walk lock-coupling — hand-over-hand read locks down the CSpace, each child acquired before its parent is released, the dynamic-acquisition shape RR7.40 establishes — prove that a concurrent `cspaceDelete` of an interior slot conflicts with a resolution passing through it, and only then delete the constructor under the same deletion-last discipline. Consumes RR7.12 and RR7.40 | — | L |

**Acceptance**: all **65** findings this phase owns — the 46 in the register's
§6 table, the four §4 items in RR7.1–RR7.4, and the 15 §7 rows RR0.11's triage
routed here (RR7.33–RR7.37) — are closed or carry an explicit, registered
deferral with a closure target. A medium may be deferred; it may not be
dropped, and neither the four §4 rows nor the 15 §7 rows may be left open on
the strength of the §6 table alone. **A low severity means the consequence is
small, not that the remedy is a sentence**: every row in RR7.33–RR7.37 needs
code, a proof, a test or a wiring change, which is why the triage did not hand
them to a documentation sweep.


### RR8 — Phase closure and hand-off to SM10

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR8.1 | Walk the RR0..RR7 acceptance gates and record the closing version for each | (1 file) | S |
| RR8.2 | Update `UNFINISHED_SMP_WORK.md`: mark each closed finding with its version, leaving open items visible | `docs/planning/UNFINISHED_SMP_WORK.md` | M |
| RR8.3 | Retire the RR0.3 standing constraint from `CLAUDE.md` and `AGENTS.md` once RR3 has closed — it says two conjuncts remain threaded and `ipcInvariantFull` is not end-to-end checked, which becomes false at RR3.25 and would otherwise misdirect every later contributor | `CLAUDE.md`, `AGENTS.md` | S |
| RR8.4 | Hand-off check **before** the closure entry: confirm SM10's §2 dependencies are genuinely met and its §1 scope statement matches the tree. Ordered first deliberately — each row may land as its own PR, so recording closure first would advertise the workstream complete for an intervening release, and an unmet dependency found afterwards would have to be retracted rather than simply fixed | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | S |
| RR8.5 | WS-RR closure entry in `docs/REGISTERED_DEBT.md`; update the CLAUDE.md phase table — last, on evidence RR8.4 established | (3 files) | S |

## 6. Verification strategy

### 6.1 What each phase proves

- **RR1** — every aarch64 code path compiles *and generates code*, so no
  cfg-gated block or `asm!` site reaches SM10.1 unexercised. **Proved at
  `v0.34.41`**: six defects and three lints, none reachable by any
  pre-existing gate and four of them invisible to `cargo check`.
- **RR2** — every live SMP dispatch arm carries a `_preserves_ipcInvariantFull`
  theorem; both donation paths preserve the SM5.H affinity invariant.
- **RR3** — `ipcInvariantFull` holds end to end: the top-level dispatch
  theorems, with no post-state conjunct threaded as a hypothesis anywhere.
- **RR4** — `faultProgress`: no reachable state returns a thread to its
  faulting instruction without an intervening handler action. This is the
  theorem that makes the livelock unrepresentable rather than merely absent.
- **RR5** — a hardware boot with no production labeling context fails closed;
  every core has an idle thread at boot.
- **RR6** — the deployed Rust locks refine their Lean specs, by trace
  correspondence rather than counter arithmetic.

### 6.2 What each phase validates

Tier 0..3 green after every sub-task, per the PR checklist. RR1 adds an
aarch64 `cargo build` to CI — a real code generation, not a type-check that
stops before the backend. RR4 and RR6 add executable suites
(`tests/FaultHandlingSuite.lean`, the Tier-5 oracle) with golden fixtures.

### 6.3 Gate discipline

Any new acceptance gate this phase adds is registered with `run_gate_check`,
not `run_check`, so a gate that cannot run is reported NOT RUN rather than
PASS — the contract landed at `v0.34.2` and pinned by
`scripts/test_gate_skip_accounting.sh`.

## 7. Risk inventory

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| RR4 fault IPC is larger than XL and slips the phase | HIGH | HIGH | Split at the sub-task boundaries §RR4 names. Partial delivery is **not** safe: RR4.9's no-handler policy is unreachable until RR4.21 wires the abort arms and RR4.23 routes the Rust trap path to them, so until both land aborts still take the old `.error .vmFault` path and return to the faulting instruction. If RR4 slips, the release waits |
| RR3 de-threading blocks on an ordering cycle between invariant modules | MED | HIGH | RR3.2 addresses ordering before any bundle edit; the per-transition establishers already exist |
| RR6.18 composition does not close | MED | MED | RR6.15 lands the trace-shape predicate independently so the composition has something to consume, and RR6.16 carries the known obstacle — the promoting release — with its counterexample, so it is scoped rather than discovered. RR6 stays open and the release waits: deferring the deployed-lock corollary past v1.0.0 would ship the exact gap this phase exists to close |
| RR1 surfaces a large volume of aarch64 compile errors | MED | MED | Expected and desirable — it is cheaper here than at SM10.1; RR1.2 and RR1.3 are sized L for this reason |
| Repointing the FFI pool at `QueuedRwLock` (RR6.10) regresses performance | LOW | MED | The Tier-5 oracle covers both implementations after RR6.3; keep `rw_lock.rs` until measurements land |
| RR6.6's waiters-to-ticket-interval simulation does not admit the FIFO bridge | MED | MED | RR6.5 proves the ticket protocol's own well-formedness first, so the interval is known total and gap-free before anything is related to `waiters`. If the relation still resists, RR6.9's corollary waits and RR6.10's deployment waits with it: the ordering note in §RR6 exists because deploying a lock with no refinement to the spec it is claimed to satisfy is the gap this phase exists to close, not a way around it |
| Two phases edit the trap seam concurrently | MED | MED | §2.3 sequences RR4 and RR5 apart in the same files |
| Medium findings are quietly dropped rather than deferred | MED | LOW | RR7's acceptance gate requires a registered deferral, not silence |

## 8. Acceptance gate

- [ ] Every open workstream has a durable registry entry with a closure target.
- [ ] `SMP_RELEASE_CLOSURE_PLAN.md` §1 scope and estimate match the tree.
- [ ] The SM10 theorem tally includes SM9 and is generated, not hand-summed.
- [ ] Every live SMP dispatch arm carries an `ipcInvariantFull` bundle.
- [ ] Both cross-core donation paths migrate the CBS replenish queue.
- [ ] Fault IPC delivers, resumes and restarts; no path returns to a faulting instruction.
- [ ] The RR3.1 gate reports zero post-state bindings of
      `blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal`
      across the `_preserves_ipcInvariantFull` family. Not a binder-name grep:
      those two conjuncts have no canonical primed name, so a name-based check
      passes without measuring anything.
- [ ] Both top-level dispatch payoff theorems exist.
- [ ] Hardware boot without a production labeling context fails closed.
- [ ] Idle threads are installed **and enqueued** on the production boot path,
      so `idleThreadEnqueuedOnCore` holds of the live boot state rather than
      being assumed by the theorems that consume it.
- [ ] Every kernel seam consults the readiness gate.
- [ ] The deployed RwLock is the one the Lean spec describes.
- [ ] Neither lock refinement theorem assumes its own conclusion.
- [ ] aarch64 `cargo build` **with `--features hw_target`** runs in CI and
      passes (a build, not a `check`:
      `check` never reaches code generation, so it cannot cover the `asm!` sites).
- [ ] Every medium finding is closed or has a registered deferral.
- [ ] Tier 0..3 green at HEAD; Tier 4 honest about what did not run.
- [ ] `UNFINISHED_SMP_WORK.md` updated with closing versions.

## 9. Cross-references

- **Source register**: [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md)
- **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10)
- **Overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
- **Absorbed by RR3**: [`IPC_INVARIANT_DETHREADING_PLAN.md`](../dev_history/planning/IPC_INVARIANT_DETHREADING_PLAN.md)
- **Absorbed by RR6** (both COMPLETE at v0.34.50): [`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md), [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
- **Canonical status**: [`../REGISTERED_DEBT.md`](../REGISTERED_DEBT.md)
- **Out of scope**: [`HARDWARE_PARTITION_ISOLATION_PLAN.md`](HARDWARE_PARTITION_ISOLATION_PLAN.md)

## Appendix A — Verification commands

```bash
source ~/.elan/env

# Per-PR minimum
./scripts/test_smoke.sh
# When theorems or invariants change
./scripts/test_full.sh

# Phase-specific
lake build SeLe4n.Kernel.Architecture.Fault              # RR4
lake build SeLe4n.Kernel.IPC.Invariant.FaultProgress     # RR4
lake build SeLe4n.Kernel.IPC.Invariant.Reachability      # RR3
lake exe fault_handling_suite                            # RR4
./scripts/test_tier5_cross_language.sh                   # RR6
# RR1 — the gate script is the single place the flags live, and it also
# verifies the three .S sources really assembled and lints the cross target.
# It `cd`s into rust/ itself: rustup's directory override selects the pinned
# toolchain (and the cross target) only there, and --manifest-path does not
# change that selection.
./scripts/test_aarch64_cross_build.sh                    # RR1
# The build alone, if you want just that.  `build`, not `check`: check stops
# before code generation, so it never reaches the backend where an inline-asm
# or instruction-encoding error surfaces.
(cd rust && cargo build --target aarch64-unknown-none -p sele4n-hal --features hw_target)

# Gate honesty — a skipped acceptance gate must fail here
SELE4N_REQUIRE_GATES=1 ./scripts/test_tier4_smp_bootcheck.sh

# Version sync
./scripts/check_version_sync.sh
```

---

*WS-RR exists because the audit found SM10's prerequisites unmet, not because
SM0..SM9 were unsound. The phase closes when SM10's §2 dependency list is true
of the tree rather than of the plan that asserts it.*
