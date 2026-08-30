# WS-RR — SMP Release Readiness (pre-SM10 remediation)

> **Status**: IN FLIGHT — **RR0 LANDED at v0.34.26** (all eleven sub-tasks);
> **RR1 LANDED at v0.34.41** (all eleven sub-tasks); RR2..RR8 not started.
> **Parent overview**: [`SMP_MULTICORE_COMPLETION_PLAN.md`](SMP_MULTICORE_COMPLETION_PLAN.md)
> **Source register**: [`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) (171 confirmed findings)
> **Successor**: [`SMP_RELEASE_CLOSURE_PLAN.md`](SMP_RELEASE_CLOSURE_PLAN.md) (SM10) — opens when this phase closes
> **Audited cut**: `v0.34.3`
> **Target releases**: v0.35.0 → v0.99.x (SM10 then cuts v1.0.0)
> **Sub-task count**: 156 across 9 phases (RR0..RR8), each phase numbered in
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
| Low | 99 | RR0.11 triage → **SM10.2**, RR7.27–RR7.31, or the debt register | Triaged at v0.34.26 (register §7.1): 20 closed by the RR0 cut, 9 closed by registration, 18 already owned by a phase reworking the same artefact, **15 needed code and became RR7.27–RR7.31**, 37 are SM10.2's work-list |

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
reworking the same artefact, **15 routed to new rows RR7.27–RR7.31**, and 37
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
- **RR2 before RR3.** The de-threading payoff theorems (RR3.15, RR3.16)
  quantify over dispatch arms that must carry bundles first.
- **RR4 before RR5, and never concurrent.** Both touch the trap and boot
  seams; running them in parallel means two phases editing the same files.
- **RR6 is independent** of everything above; it sits late because nothing
  depends on it, not because it is optional.
- **RR7 is not independent, despite being a sweep.** Several of its rows own
  findings whose primary owner is an earlier phase — RR7.19 the RwLock-deferred
  mediums that RR6 implements, RR7.22 the IPC de-threading medium RR3 closes,
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
| RR1 | aarch64 compile coverage, plus the Rust HAL gate no other phase owns.  **LANDED v0.34.41**; gate hardening through review at v0.34.43 | 12 | M |
| RR2 | Live-path correctness: dispatch-arm bundles + donation queue migration, wired live | 19 | M–L |
| RR3 | `ipcInvariantFull` de-threading closure (D1, D6, D8) | 17 | L–XL |
| RR4 | Fault handling: full fault IPC with reply-based restart | 27 | XL |
| RR5 | Boot-path fail-open closure | 14 | M–L |
| RR6 | Verified lock primitives completion (SM2.C-defer, pre-v1.0.0) | 19 | L |
| RR7 | Medium-severity sweep, plus the §7 rows RR0.11 routes here | 32 | M |
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
| RR0.1 | Add an IPC de-threading workstream row to `docs/WORKSTREAM_HISTORY.md` recording per-slice state (D0/D2/D2′/D3/D4/D5/D7 closed; D1/D6/D8 open) with closure target RR3 | `docs/WORKSTREAM_HISTORY.md` | S |
| RR0.2 | Add it to `SMP_RELEASE_CLOSURE_PLAN.md` §2 Dependencies | (1 file) | T |
| RR0.3 | Add a CLAUDE.md standing-constraint bullet naming the two still-threaded conjuncts, so new code does not assume `ipcInvariantFull` is end-to-end machine-checked; mirror to `AGENTS.md` | `CLAUDE.md`, `AGENTS.md` | S |
| RR0.4 | Rewrite `SMP_RELEASE_CLOSURE_PLAN.md` §1 phase goal against the real SM10.1 scope (§2.2 of the register) | (1 file) | S |
| RR0.5 | Add the missing SM9 term to the §5 theorem tally | (1 file) | T |
| RR0.6 | Replace the hand-summed `wsm_theorem_count` literal with a generated manifest, so the marker theorem cannot certify a stale number | `scripts/`, `SeLe4n/Kernel/Concurrency/` | M |
| RR0.7 | Correct the SM10.6.3 archive list: add the SM9 plan, this plan, and the register; update the file-move count | (1 file) | T |
| RR0.8 | Refresh the SM10.3 sub-task table against the tree — five of six suites and two of three fixtures already exist | (1 file) | S |
| RR0.9 | Register the remaining unregistered debt the debt sweep found, each with an owner and closure target | `docs/WORKSTREAM_HISTORY.md` | M |
| RR0.10 | Fix SM4.C.11's circular closure target (the phase that owns it is marked LANDED); re-home it to a phase that can close it | (2 files) | S |
| RR0.11 | Triage the register's §7 low-severity table by remedy, not by severity: rows fixed by editing prose become SM10.2's documentation work-list (cross-referenced from `SMP_RELEASE_CLOSURE_PLAN.md`); rows needing code, a proof or a wiring change become numbered RR7 rows or registered deferrals with owners. Handing all 99 to a documentation sweep would close the release over unwired proven structures | (2 files) | S |

**Acceptance**: `grep` for each open workstream name returns a hit in
`docs/WORKSTREAM_HISTORY.md`; no plan in `docs/planning/` lacks a status
header; the SM10 tally arithmetic includes every landed phase.

**Met at `v0.34.26`.**  Every plan under `docs/planning/` is cited from
`docs/WORKSTREAM_HISTORY.md` and carries a status header — five did not, and
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

**The first compile found six defects and three lints.**  Two `boot.S`
sites used `and sp, sp, #~0xF`, which does not assemble — `AND (immediate)`
accepts SP as its destination but not as its source — so neither the
primary's nor the secondary's stack-alignment step was valid.  Four `TLBI
*OS` sites are **FEAT_TLBIOS** (ARMv8.4-A) instructions that neither encode
for the baseline target nor execute on **Cortex-A76**, the ARMv8.2-A core in
the RPi5's BCM2712; they now probe `ID_AA64ISAR0_EL1.TLB` and fail closed.
`cargo check` reported all four of those as clean, which is why RR1.5
insisted the gate be a build.  The register records the full inventory
([`UNFINISHED_SMP_WORK.md`](UNFINISHED_SMP_WORK.md) §5.1).


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

**Acceptance**: every arm reachable from `SeLe4n/Kernel/API.lean`'s SMP
dispatch carries a `_preserves_ipcInvariantFull` theorem; the donation paths
migrate the replenish queue; no cancellation theorem rests on an
unproven teardown hypothesis.


### RR3 — `ipcInvariantFull` de-threading closure (D1, D6, D8)

Closes [`IPC_INVARIANT_DETHREADING_PLAN.md`](IPC_INVARIANT_DETHREADING_PLAN.md),
whose D1, D6 and D8 slices are open. Two of the twenty conjuncts are still
assumed as post-state hypotheses on nearly every bundle —
`blockedThreadsPendingMessageConsistent` on 33 of 35 and
`replyCallerLinkageReciprocal` on 31 of 35 — so `ipcInvariantFull` is not
today an end-to-end machine-checked property of the live kernel.

The per-transition establishers for all seven base transitions already exist,
so D1's residue is module ordering rather than missing mathematics. RR3.15 and
RR3.16 depend on RR2: the payoff theorems quantify over dispatch arms that
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
| RR3.15 | `dispatchWithCap_preserves_ipcInvariantFull` (**depends on RR2**) | `SeLe4n/Kernel/API.lean` | L |
| RR3.16 | `syscallDispatch_preserves_ipcInvariantFull` — the D8 payoff — **and** cite both payoff theorems from `docs/CLAIM_EVIDENCE_INDEX.md`, which this phase's acceptance requires and no other row owned: the theorem that changes the claim surface is the one that must update the claim | `SeLe4n/Kernel/API.lean`, `docs/CLAIM_EVIDENCE_INDEX.md` | L |
| RR3.17 | Retire `IPC_INVARIANT_DETHREADING_PLAN.md`: mark closed, record the closure version, move to `docs/dev_history/planning/` | (file move) | S |

**Acceptance**: the RR3.1 gate reports zero post-state bindings of
`blockedThreadsPendingMessageConsistent` and `replyCallerLinkageReciprocal`
across the `_preserves_ipcInvariantFull` family; both payoff theorems exist
and are cited from `docs/CLAIM_EVIDENCE_INDEX.md`.

**A note on measuring this.** The ten conjuncts de-threaded by earlier slices
each had a canonical primed binder (`hQNBC'`, `hPRR'`, …), so "de-threaded"
could be checked by grepping the name to zero — and in the comment-free code
view all ten are indeed zero. The two remaining conjuncts have **no such
canonical name**: they appear under `hInv`, `hRecip`, `hWtpmn` and bare `h`
depending on the bundle. A name-based check would therefore report success
without measuring anything, which is the same failure shape as the tier-4
gates that scored a skip as a pass. RR3.1 exists so the criterion is
measured rather than assumed.


### RR4 — Fault handling: full fault IPC with reply-based restart

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
| RR4.9 | No-handler policy: the thread is suspended fail-closed, never returned to the faulting instruction | `SeLe4n/Kernel/IPC/Operations/Fault.lean` | M 
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
| RR4.22 | `trap.rs`'s four `set_x0`-only exception arms write a full v2 offset-label frame via `error_frame_regs`, retiring the raw-discriminant-in-`x0` convention that leaves `x1` untouched. **Before** the wiring below, not after: once aborts deliver, a resumed thread whose `x1` carries a label under 512 decodes a fault as a successful syscall. The defective arms are in `trap.rs` — `svc_dispatch.rs` already holds the correct helper | `rust/sele4n-hal/src/trap.rs` | S |
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
| RR5.10 | Wire `bootFromPlatformWithIdleThreads` into the production boot path — it is proven correct (`…_all_cores_have_idle`) but has no caller, so the proof does not carry through to runtime — **and** update `bootFromPlatformChecked`'s downstream theorem chain in the same slice. These cannot be separate PRs: the existing theorems unfold the checked function and characterize its result in terms of `bootFromPlatform config`, so switching the base without them either fails to compile or ships a live boot path its own theorems no longer cover. **The switch alone is not the remediation**: `installIdleThread` creates the idle TCB and sets `currentOnCore`, and never touches `runQueueOnCore`, while `idleThreadEnqueuedOnCore`'s first conjunct is run-queue membership — so this slice must also call the per-core enqueue and prove `∀ c, idleThreadEnqueuedOnCore st c` of the live boot state, which is the premise `chooseThreadOnCore_always_succeeds` consumes. Without it a core reaching selection with no runnable user thread still lacks its idle fallback | `SeLe4n/Platform/Boot.lean` | XL |
| RR5.11 | Make the three staged state-committing kernel entries production-reachable, so a linked image carries their `@[export]` symbols | `SeLe4n.lean`, `scripts/staged_module_allowlist.txt` | M |
| RR5.12 | Verify each expected `@[export]` symbol is present in the built archive | `scripts/` | M |
| RR5.13 | Bracket `suspend_thread_inner`, which commits kernel state outside the kernel-entry lock | `SeLe4n/Platform/FFI.lean` | S |
| RR5.14 | Replace the two `debug_assert!` lock/vector tripwires, which vanish from the release image, with checks that survive it | `rust/sele4n-hal/src/` | S |

**Acceptance**: a hardware boot without an explicit production labeling
context fails closed; every seam consults the readiness gate; idle threads
are installed on the production path; the staged-module count falls by three.


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

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR6.1 | Add non-blocking `try_acquire_read` / `try_acquire_write` to the real `RwLock`, removing the oracle's stated reason for modelling instead of driving | `rust/sele4n-hal/src/rw_lock.rs` | M |
| RR6.2 | Rewrite the Tier-5 oracle to drive the real lock through those entry points | `rust/sele4n-hal/src/bin/rw_lock_oracle.rs` | L |
| RR6.3 | Extend the oracle to the queued lock, so both implementations are covered | (same) | M |
| RR6.4 | Operational step model for `QueuedRwLock` plus its refinement to the Lean FIFO spec. `RwLockRefinement.lean` models the **CAS-retry** `rw_lock.rs`, and the `queued_*` theorems in `RwLock.lean` are about the abstract spec's waiter queue — neither is a bridge to the queued Rust algorithm this phase deploys, so without this the next sub-task's corollary has nothing to compose | `SeLe4n/Kernel/Concurrency/Locks/QueuedRwLockRefinement.lean` (new) | XL |
| RR6.5 | Corollary: `QueuedRwLock` refines the Lean FIFO spec end to end, closing the spec-to-implementation gap for the lock the next sub-task deploys — proved before the switch, so no version ships an unrefined core lock | (same) | L |
| RR6.6 | Point `STATIC_RW_LOCK_POOL` and the `ffi_rw_lock_*` entries at `QueuedRwLock`, so the deployed lock is the FIFO one the spec describes — **and** correct the FFI and information-flow docs naming the CAS-retry lock as deployed in the same slice, since landing them apart ships a version whose canonical Lean-side concurrency documentation names the wrong runtime primitive | `rust/sele4n-hal/src/lock_bridge.rs`, `SeLe4n/Kernel/InformationFlow/FineLockFlow.lean` | M |
| RR6.7 | Decide and record the fate of `rw_lock.rs`: retained for compatibility, or retired | (2 files) | S |
| RR6.8 | `TicketLockConcrete` operational step function, mirroring the RwLock refinement's shape | `SeLe4n/Kernel/Concurrency/Locks/TicketLockRefinement.lean` | L |
| RR6.9 | Trace correspondence (`blockBisim` / `ListBlockBisim` analogue) replacing the counter arithmetic in `rust_ticketLock_refines_lean` | (same) | L |
| RR6.10 | Replace the tautological conjunct with a statement that can fail | (same) | M |
| RR6.11 | D-4: prove `opCorresponds`-chain plus an explicit load-then-CAS trace-shape predicate implies `ListBlockBisim`, so the twelve discharge lemmas compose into the main theorem instead of it assuming its own conclusion | `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` | XL |
| RR6.12 | Run the deployed queued lock under Loom: the dev-dependency alone explores nothing, because `queued_rw_lock.rs` imports `core::sync::atomic` directly and Loom only sees its own instrumented atomics. Add the `cfg(loom)` synchronisation aliases so the lock compiles against them, write `loom::model` tests over the bounded interleavings, and invoke them from CI or the nightly — otherwise §8's "loom gate runs" is satisfied by a manifest entry | `rust/sele4n-hal/Cargo.toml`, `rust/sele4n-hal/src/queued_rw_lock.rs`, `.github/workflows/` | L |
| RR6.13 | Add a nightly `miri` job for the queued lock | `.github/workflows/` | M |
| RR6.14 | Raise the FIFO and stress iteration counts to the plan's stated thresholds | `rust/sele4n-hal/src/queued_rw_lock.rs` | S |
| RR6.15 | Prove the D-2.5 writer-bounded-wait statement as specified — the ingredients exist; only a single-state `_weak` corollary landed | `SeLe4n/Kernel/Concurrency/Locks/RwLock.lean` | M |
| RR6.16 | Repoint the R-10 aggregator entry at the theorem that proves writer liveness; keep the safety theorem registered under its accurate name | `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` | S |
| RR6.17 | Plan corrections: the retired-MCS design section, the D-1.9 landed row, the false §3.2.6.1 theorem statement, and the Appendix A commands that name a nonexistent script | `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` | M |
| RR6.18 | Retitle the plan: it is no longer post-v1.0.0; add an SM2.C-defer row to `docs/WORKSTREAM_HISTORY.md` with closure target RR6 — this phase, not the boot-path phase that precedes it | (2 files) | S |
| RR6.19 | Register Track D of `SMP_FINE_LOCK_MIGRATION_PLAN.md` — the commit-model partitioning, which that plan seam-gates to SM10.1 — as a named SM10.1 dependency in `SMP_RELEASE_CLOSURE_PLAN.md` §2 and the debt register, so the one part of the fine-lock work WS-RR cannot land is tracked rather than absorbed silently | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md`, `docs/WORKSTREAM_HISTORY.md` | S |

**Acceptance**: the deployed RwLock is the one the Lean spec describes; the
Tier-5 oracle drives real locks; neither refinement theorem assumes its own
conclusion or contains a tautological conjunct; `loom` and `miri` gates run.

**Note on the two XLs**: RR6.4 (the queued lock's own operational model and
refinement) and RR6.11 (the D-4 bisimulation for the CAS-retry lock) are the
phase's largest items and the likeliest to need splitting. Take the trace-shape
predicate and the composition proof as separate PRs, landing the predicate
first so the composition has something to consume.

RR6.4 and RR6.5 sit **before** RR6.6 deliberately. RR6.6 changes which lock the
kernel deploys, and `RwLockRefinement.lean` models the CAS-retry implementation
— so deploying first would leave several versions shipping a core concurrency
primitive with no refinement to the spec it is claimed to satisfy. The model,
then the corollary, then the switch.

### RR7 — Medium-severity sweep

Every confirmed medium finding, batched so each PR touches one subsystem,
plus the §7 low-severity rows whose remedy is code rather than prose.
**65 findings**: the 45 still open of the register's §6 table — RR7.5's
re-sequencing item closed at v0.34.36 — the four §4 rows RR7.1–RR7.4 that are
remediation work rather than security fixes, the 15 §7 rows RR0.11's triage
routed here (RR7.27–RR7.31), and the one uncovered lock domain the RR0 review
round found with no owner that would close it (RR7.32). Every other
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

| Sub | Description | Findings | Est |
|-----|-------------|----------|-----|
| RR7.1 | Boot MMU corrections: 960 MiB of RAM mapped as Device, and nothing mapped above 4 GiB (§4) | 1 | L |
| RR7.2 | Satisfy the FFI unqualified boot identity-map claim, which the boot tables do not provide above 3 GiB — per the implement-the-improvement rule, extend the tables rather than qualify the claim (§4) | 1 | M |
| RR7.3 | Extend the flagship "syscall entry implies capability held" theorem to the live checked dispatch path; it covers only the legacy path today (§4) | 1 | L |
| RR7.4 | Give the `_atomic_under_lockSet` family operation-specific content: its atomicity half is today a `rfl` instance of a body-agnostic lemma, and five `lockSet_observer_atomic_on` instantiations are missing (§4) | 1 | M |
| RR7.5 | Add SM10's three `contextRestoreSeamLive` prerequisites, absent from its dependencies, sub-tasks and acceptance gate.  This row's two other items are **closed**: §1's false "all substantive SMP work is complete" phase goal (RR0.4, v0.34.26) and the sub-phase re-sequencing (v0.34.36 — SM10 is now numbered SM10.1..SM10.6 in execution order) | 1 | M |
| RR7.6 | Production `native_decide`: six uses are live in Lean at HEAD while §5's release-note template claims zero. Per implement-the-improvement, replace them with proofs rather than weaken the claim | 1 | L |
| RR7.7 | Make the v1.0.0 "per-object reader-writer fine locks" claim **true**, do not reconcile the text to what ships. RR6 refines and deploys the queued lock primitive but performs none of SM3.C.9's exported-body migration, so the claim stays false after it. This row owns Tracks B and C of `SMP_FINE_LOCK_MIGRATION_PLAN.md` — the `capTransferReceiverCnode` footprint closure and the object-domain/dispatch-entry `withLockSet` wrapping of the `@[export]` bodies — and RR6.19 below records what Track D still owes SM10.1. Weakening the capability text instead is the outcome the implement-the-improvement rule forbids | 1 | XL |
| RR7.8 | Cancellation/timeout error-frame staging, unimplemented at HEAD and owed before the context-restore seam flips | 1 | M |
| RR7.9 | Boot-path sweep mediums | 5 | M |
| RR7.10 | Rust HAL mediums | 4 | M |
| RR7.11 | Syscall return ABI mediums | 4 | M |
| RR7.12 | Per-object lock mediums | 4 | M |
| RR7.13 | Fine-lock migration mediums | 3 | M |
| RR7.14 | TLB shootdown mediums | 3 | M |
| RR7.15 | Debt-register mediums | 3 | M |
| RR7.16 | Cross-core IPC mediums | 2 | S |
| RR7.17 | Declassification mediums | 2 | S |
| RR7.18 | Panic-hang remediation mediums | 2 | S |
| RR7.19 | RwLock-deferred mediums | 2 | S |
| RR7.20 | Implement-the-improvement sweep: route the per-core scheduler entries through the HAL context-switch seam | 1 | S |
| RR7.21 | Implement-the-improvement sweep: the DeviceTree-to-`PlatformConfig` boot bridge — a platform/boot surface unrelated to the row above, so its own task | 1 | S |
| RR7.22 | IPC de-threading medium | 1 | S |
| RR7.23 | Reply objects medium | 1 | S |
| RR7.24 | SMP foundations medium | 1 | S |
| RR7.25 | Master plan medium | 1 | S |
| RR7.26 | Doc-sync medium | 1 | S |
| RR7.27 | Unwired proven structures (§7): the four per-core statistics accessors that are declared, wrapped and proven with zero consumers, and `ipcUnwrapCaps`'s dead `senderCspaceRoot`, whose own registered closure target passed without it | 2 | M |
| RR7.28 | Plan-named artefacts that do not exist (§7): `donation_perCore_consistent`, the two unresolvable SM8 theorem names — one of them cited from a **live docstring** — `notification_waiters_nodup`, the SM0-cited Tier-0 gate script, and the four `CLAIM_EVIDENCE_INDEX.md` identifiers.  Per implement-the-improvement each is authored, not struck from the catalogue | 5 | L |
| RR7.29 | Gate coverage the claims assume (§7): the nine `dev_history` cross-references still in production sources plus the gate that would enforce their absence; the three declared `lean_exe` targets no gate compiles; the SMP-M1 surface difference no gate or phase owns; and the documentation-metrics sync, which covers two files while the sync matrix claims the transitive set — eleven i18n READMEs and four GitBook chapters carry `v0.33.101`-era metrics | 4 | M |
| RR7.30 | Boot-core-pinned thread-state classification (§7): `inferThreadState` / `syncThreadStates` / `threadStateConsistent` read `bootCoreId`, so a thread running on a secondary core classifies as `.Inactive` | 1 | M |
| RR7.31 | Test-surface corrections (§7): the D-1 admission-order `decide` fixtures the RwLock gate asks for and the suite lacks; the `r4a_`/`r4c_` test identifiers that encode sub-task codes against the plan's own self-certified naming rule; and the vacuous `trap.rs` SVC test with its stale "pre-FFI stub" prose | 3 | M |
| RR7.32 | Splice-neighbour queue ownership (`UncoveredLockDomain.queueOwnershipProtocol`): `queueOwnership_violated_by_tcbSetPriority` states the violation as a `¬`, and the domain had no owner that would close it — RR0.9 pointed it at RR7.7's fine-lock Track B, which closes `capTransferReceiverCnode` and `cdtNodeAllocation` but never touches splice neighbours.  Either extend the `tcbSetPriority` footprint to declare the queue-owning locks, or hold the endpoint lock across the splice; the `UncoveredLockDomain` entry is deleted only when the domain is actually covered | 1 | M |

**Acceptance**: all **65** findings this phase owns — the 46 in the register's
§6 table, the four §4 items in RR7.1–RR7.4, and the 15 §7 rows RR0.11's triage
routed here (RR7.27–RR7.31) — are closed or carry an explicit, registered
deferral with a closure target. A medium may be deferred; it may not be
dropped, and neither the four §4 rows nor the 15 §7 rows may be left open on
the strength of the §6 table alone. **A low severity means the consequence is
small, not that the remedy is a sentence**: every row in RR7.27–RR7.31 needs
code, a proof, a test or a wiring change, which is why the triage did not hand
them to a documentation sweep.


### RR8 — Phase closure and hand-off to SM10

| Sub | Description | Files | Est |
|-----|-------------|-------|-----|
| RR8.1 | Walk the RR0..RR7 acceptance gates and record the closing version for each | (1 file) | S |
| RR8.2 | Update `UNFINISHED_SMP_WORK.md`: mark each closed finding with its version, leaving open items visible | `docs/planning/UNFINISHED_SMP_WORK.md` | M |
| RR8.3 | Retire the RR0.3 standing constraint from `CLAUDE.md` and `AGENTS.md` once RR3 has closed — it says two conjuncts remain threaded and `ipcInvariantFull` is not end-to-end checked, which becomes false at RR3.16 and would otherwise misdirect every later contributor | `CLAUDE.md`, `AGENTS.md` | S |
| RR8.4 | Hand-off check **before** the closure entry: confirm SM10's §2 dependencies are genuinely met and its §1 scope statement matches the tree. Ordered first deliberately — each row may land as its own PR, so recording closure first would advertise the workstream complete for an intervening release, and an unmet dependency found afterwards would have to be retracted rather than simply fixed | `docs/planning/SMP_RELEASE_CLOSURE_PLAN.md` | S |
| RR8.5 | WS-RR closure entry in `docs/WORKSTREAM_HISTORY.md`; update the CLAUDE.md phase table — last, on evidence RR8.4 established | (3 files) | S |

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
| RR6.11 bisimulation does not close | MED | MED | Land the trace-shape predicate independently so the composition has something to consume; RR6 stays open and the release waits — deferring the deployed-lock corollary past v1.0.0 would ship the exact gap this phase exists to close |
| RR1 surfaces a large volume of aarch64 compile errors | MED | MED | Expected and desirable — it is cheaper here than at SM10.1; RR1.2 and RR1.3 are sized L for this reason |
| Repointing the FFI pool at `QueuedRwLock` (RR6.6) regresses performance | LOW | MED | The Tier-5 oracle covers both implementations after RR6.3; keep `rw_lock.rs` until measurements land |
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
- [ ] Idle threads are installed on the production boot path.
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
- **Absorbed by RR3**: [`IPC_INVARIANT_DETHREADING_PLAN.md`](IPC_INVARIANT_DETHREADING_PLAN.md)
- **Absorbed by RR6**: [`SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`](SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md), [`SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md`](SMP_VERIFIED_LOCK_PRIMITIVES_PLAN.md)
- **Canonical status**: [`../WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md)
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
