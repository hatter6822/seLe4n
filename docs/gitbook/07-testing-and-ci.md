# Testing and CI

Current stage context: the live workstreams and their status are in [`WORKSTREAM_CONTEXT.md`](../agent_guide/WORKSTREAM_CONTEXT.md) and [`REGISTERED_DEBT.md`](../REGISTERED_DEBT.md); each version's test additions are in [`CHANGELOG.md`](../../CHANGELOG.md).  Every QEMU boot (Tier-4 and the archive lane) runs first on rpi5_machine's `raspi5b`, which models the Raspberry Pi 5's BCM2712, then on QEMU's `virt` (WS-RB; [`DEVELOPMENT.md`](../DEVELOPMENT.md) §4 has the commands and [`SELE4N_SPEC.md`](../spec/SELE4N_SPEC.md) §6.2.18a the boot lanes).

Canonical sources: [`TESTING_FRAMEWORK_PLAN.md`](../TESTING_FRAMEWORK_PLAN.md)
owns the tier contract, [`CI_POLICY.md`](../CI_POLICY.md) owns what CI runs and
why it is pinned, and [`DEVELOPMENT.md`](../DEVELOPMENT.md) §4 owns the commands.
What each version changed is in [`CHANGELOG.md`](../../CHANGELOG.md).

## Tier model

- **Tier 0 (hygiene)**
  - marker scan for forbidden placeholders (`axiom|sorry|TODO`) in tracked proof surface,
  - fixture-isolation guard (test-only contracts must not leak into production kernel modules),
  - wrapper-structure regression guard (scalar wrappers must remain structure-based),
  - theorem-body semantic depth check (L-08: Python analyzer flags `sorry` and trivial/single-tactic `preserves` proofs, with regex fallback),
  - CodeQL workflow policy (`check_codeql_workflow_policy.py` + its `--self-test`): the three configurations that each leave the code-scanning merge requirement waiting forever — a missing `init`/`analyze` step, `github/codeql-action/*` references pinning different commits, and an analyze step masked by `continue-on-error` at step or job level — see [`docs/CI_POLICY.md`](../CI_POLICY.md) §8 and §9.1,
  - aarch64 cross-target configuration (`check_aarch64_cross_target.py` + its `--self-test`): the `targets` key in `rust/rust-toolchain.toml`, the `--features hw_target` flag, and the `cargo build`-not-`check` choice in the cross gate — each load-bearing in a way that is silent if lost, since a gate weakened in any of those directions stays green over nothing (WS-RR RR1.8),
  - TLBI broadcast discipline (`check_tlbi_broadcast_discipline.py` + its `--self-test`): the `tlbi` mnemonic may be emitted only from `tlb.rs`; the local, non-broadcast wrappers may be called only from sites registered in `scripts/tlbi_local_allowlist.txt`; and the Lean bindings of the local FFI exports only from registered production modules.  A non-broadcast `tlbi vae1` invalidates just the calling PE, so under SMP another core keeps walking a translation the caller believes it removed (WS-RR RR1.9),
  - optional shell-quality checks.
- **Tier 1 (build/proof compile)**
  - full `lake build` to verify definitions, theorem scripts, and module integration.
- **Tier 2 (trace/behavior)**
  - executable scenario (`lake exe sele4n`) checked against stable fixture fragments,
  - **mandatory determinism validation** (WS-I1/R-02): `scripts/test_tier2_determinism.sh` runs trace twice and diffs output, failing on any divergence,
  - malformed/negative and IF-M1 runtime suites (`lake exe negative_state_suite`, `lake exe information_flow_suite`) run under `scripts/test_tier2_negative.sh`,
  - R8-D (I-M04): frozen/radix correctness suites (`radix_tree_suite`, `frozen_state_suite`, `freeze_proof_suite`, `frozen_ops_suite`) now execute in Tier 2 negative tests (67 scenarios),
  - fixture lines are bracket-prefixed (`[PREFIX-NNN] expected_trace_fragment`; the parser also accepts an optional pipe-delimited `scenario_id | risk_class | fragment` form) for audit traceability (WS-I1/R-03), with the subsystem mapping in `scenario_registry.yaml`,
  - all trace output lines (210 fixture lines at v0.37.33) tagged with scenario IDs across 15+ prefix families (ENT, CAT, SST, LEP, CIC, IMT, IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY, …),
  - 38 inter-transition invariant assertions (WS-I1/R-01, V8-C) check invariant families after every major transition group including post-mutation checks,
  - fixtures include WS-A4 scale scenarios for deep CNode radix, large runnable queues, multi-endpoint IPC, depth-5 service dependencies, and boundary memory addresses.
  - WS-B11 scenario metadata is maintained in `tests/scenarios/scenario_catalog.json` and validated by `scripts/scenario_catalog.py` in smoke/nightly gates.
  - scenario registry (`tests/fixtures/scenario_registry.yaml`) maps all scenario IDs to source functions; validated bidirectionally in Tier 0 hygiene,
  - V8-F: SHA-256 fixture drift detection (all 14 `*.expected.sha256` companions) verified in Tier 2 trace — a checksum pins a fixture against *itself*, forcing every fixture edit to carry a hash refresh in the same commit, and saying nothing about whether the fixture still agrees with the program,
  - v0.35.110: the main trace comparison is **both-directional** — every fixture fragment must occur in the output *and* every output line must be accounted for by some fragment.  The converse used to be computed only inside the failure branch, so an *added* trace line left the fixture silently no longer enumerating the trace; measured free to close (239 fragments, 239 non-empty output lines, zero unaccounted),
  - v0.35.109: the **scenario-traceability manifests'** fragment column is compared against real suite output (`scripts/scenario_catalog.py list-manifests` / `check-fragments`, run per discovered manifest from `scripts/test_tier2_trace.sh`).  Measured at v0.35.109: twelve of fourteen fixtures already had such a comparison and all twelve matched; the two that had none — `robin_hood_smoke.expected` and `two_phase_arch_smoke.expected` — were stale in **19 of 19** fragments.  The swept set is derived (a fixture is a manifest by its row shape, its producer comes from its own `# Suite:` header), so a manifest that declares no producer fails discovery rather than dropping out of the domain,
  - v0.35.111: **presence-for-relation** defects inside the manifest machinery, all fail-open.  The manifest classifier *skipped* a file it could not parse, so one with a valid `# Suite:` header and a single malformed row was swept as golden output with the gate still reporting PASS; a `# Suite:` declaration is now manifest **intent**, and given intent anything short of well-formed is an error — asked at **Tier 0** (`list-manifests`), since well-formedness needs no build.  And a row's fragment was bound to nothing, so `RH-001 | … | [RH-002a …]` passed against real output; `fragment_names_scenario` is the binding, and it refuses a longer id that merely has this one as a prefix,
  - V8-A: end-to-end `syscallEntryChecked` pipeline test (PIP-001..006) covering register decode → checked dispatch → invariant preservation → trace equivalence,
  - V8-B: `cspaceMove` end-to-end test (MOV-001..004) covering decode → move → source/dest verification,
  - V8-G: `ThreadState` consistency check (`threadStateConsistentChecks`) validates TCB `threadState` field matches inferred state from queue membership and IPC blocking state.
- **Tier 3 (invariant surface anchors + type-correctness #check gate)**
  - validates critical theorem/bundle/trace anchors expected for active milestone slices,
  - includes executable-trace anchor checks for milestone-critical lifecycle fragments,
  - is **self-sufficient** (v0.32.104): most checks are `rg` name searches needing
    no build, but a minority elaborate probe files through `lake env lean`, which
    only *reads* `.olean`s and never builds them.  Some of those probes import
    staged modules, which sit outside the default `lake build` target and are
    materialised only by the `SeLe4n.Platform.Staged` anchor, so the gate builds
    that anchor in its preamble rather than relying on Tier 1 having run first
    (a fast no-op replay in the full chain).
- **Tier 4 (nightly staged extension candidates)**
  - `./scripts/test_tier4_nightly_candidates.sh` stages repeat-run determinism + seeded sequence-diversity candidates,
  - `./scripts/test_nightly.sh` uses mode-aware status messaging (default extension-point guidance vs explicit executed signal when `NIGHTLY_ENABLE_EXPERIMENTAL=1`),
  - includes seeded `trace_sequence_probe` sequence-diversity checks in experimental mode,
  - default remains explicit extension-point behavior unless `NIGHTLY_ENABLE_EXPERIMENTAL=1` is set.
- **Tier 5 (cross-language correspondence)** — `scripts/test_tier5_cross_language.sh` (WS-SM SM2.C-defer D-6): Lean-oracle vs Rust lock-primitive correspondence, run from `test_nightly.sh` under `NIGHTLY_ENABLE_EXPERIMENTAL=1`.  **As of v0.34.50 (WS-RR RR6.1–RR6.3) the oracle *drives* the real locks** rather than modelling them: its `Driver` holds a `rw_lock::RwLock` and the deployed `queued_rw_lock::QueuedRwLock` in process memory, runs every generated operation through both, and after each one checks that the two implementations agree, that the queued lock's `[now_serving, next_ticket)` interval matches the abstract waiter queue, that the state word is `encodeRwLock` of the abstract state, and (PR #890 review round 2) that each core's held word reads what the spec says the core holds — a non-holder's release and a holder's re-acquisition are issued to the real ticket lock rather than gated in the driver; and (review round 5) every withdrawal's verdict is held to the spec's, and both oracles print one identity line per state — the writer's core, the sorted reader cores, the ordered queue with modes — read back out of the ticket lock's per-core words on the Rust side, where a flag, a count and a length had let a wrong-waiter promotion pass.  The comparison is an implementation check rather than a Lean↔Lean identity.
- **Concurrency model checking and miri** (WS-RR RR6.20–RR6.22, v0.34.50) — `scripts/test_loom_queued_rw_lock.sh` explores every interleaving of the deployed lock's models under `loom`, with no preemption bound except where stated (nineteen models — five from RR6.20, four withdrawal models from WS-LC LC3.3, two from the WS-LC closure audit at v0.34.56, which found a double-withdrawal stall the four had missed, two from PR #890 review round 2 — a non-holder's unwind against a holder, and `every_pair_of_units_is_safe`, which enumerates every unordered pair of the lock's fourteen single-lifecycle units on two threads, unbounded (two of them the unwind at a held member, from review round 3, two the enqueue-twice-then-acquire shapes from the class closure behind rounds 2 and 3, and from round 5 the write-mode withdrawal and the two RAII guards, the unit list held to the lock's entry points by `build.rs`) — `every_chained_unit_meets_every_unit` from round 5, the three chained lifecycles against every unit under a *stated* preemption bound of 3, since an unbounded exploration of two chained threads does not finish in a per-PR lane — and five from review round 5, which race a served or promoted request's withdrawal against the release that admitted it and tally that both verdicts occur; the plan's "op-sequences of length ≤ 4" sentence is the single-threaded census `per_core_census_to_depth_four` in the host lane, not this enumeration; the lock aliases `core::sync::atomic` under `cfg(loom)` so the instrumented atomics are the ones it uses), run in CI as the `test-loom-concurrency-model` job; `scripts/test_miri_queued_rw_lock.sh` runs the lock's suite under `-Zmiri-strict-provenance`, wired into `test_nightly.sh` behind `NIGHTLY_ENABLE_EXPERIMENTAL=1`.  Both were verified decisive by a *relation-breaking* mutation — removing `await_turn` from `acquire_read`, which leaves every token in place, fails two of the original five loom models; the withdrawal models carry four relation-breaking mutations of their own, recorded in the script — rather than by deleting a symbol.

### The two Rust lanes

The tier model above compiles Lean.  Rust has two lanes of its own, and they
cover disjoint halves of the same crate:

- `scripts/test_rust.sh` — the **host** lane: build, 1 156 unit tests across
  10 binaries (at `v0.34.44`), the conformance suite, `cargo fmt --check`,
  and `cargo clippy --all-targets --all-features -D warnings`.  CI job
  *Rust ABI Tests*.
- `scripts/test_aarch64_cross_build.sh` — the **cross** lane (WS-RR RR1,
  `v0.34.41`): `cargo build` for `aarch64-unknown-none-softfloat` in both
  profiles, a check that `boot.S`, `vectors.S` and `trap.S` really
  assembled, `cargo clippy -D warnings` on the same target, and (since
  `v0.36.2`) a disassembly of the release objects that refuses any FP/SIMD
  register operand (`scripts/check_fp_simd_free_objects.py`) — the kernel
  is FP-free and traps FP/SIMD at EL1 — and (WS-BP BP2.1) a probe link under
  `link.ld` that checks the Lean heap arena and proves the script's three
  `ASSERT`s live (`scripts/check_link_script.py`).  CI job *aarch64 Cross
  Build*.
- `scripts/test_lean_aarch64_archive.sh` — the **Lean cross** lane (WS-BP
  BP1, `v0.36.2`): `libsele4n.a`, the elaborator's closure of `SeLe4n`
  compiled freestanding and soft-float for the same target by
  `scripts/build_lean_aarch64_archive.py`, which refuses a `Lean.*`, staged or
  testing module in the closure, any warning outside the C generator's two
  known shapes, a regenerated stdlib module whose symbols differ from the
  toolchain's own object, an FP/SIMD register operand, and an unresolved symbol
  no provider accounts for, or one attributed to the HAL that the HAL's own
  object code does not define as a function; then the kernel-entry reconciliation over both
  archives (`check_kernel_entry_exports.py --require-cross`); then (BP5.2–BP5.4)
  the Lean kernel linked into `sele4n-kernel`, checked with
  `check_kernel_image.py --lean-kernel` and the FP/SIMD gate, and the boot files
  `kernel8.img` / `config.txt` cut from it by `scripts/build_rpi5_image.sh` with
  the image's size and section map published.  CI job *Lean aarch64 Archive*,
  which uploads the archive and the `rpi5-kernel-image` artifact.

**Neither lane subsumes the other.**  On the host, every
`#[cfg(target_arch = "aarch64")]` block is removed before rustc or clippy
sees it — cfg-false arms are parsed but never type-checked, borrow-checked or
linted — so the host lane cannot see 67 cfg-gated blocks, 57 `asm!`
invocations or any of the four `.S` sources, which is most of the HAL.  The
cross lane, conversely, does not compile the 26 `not(aarch64)` host stubs and
runs no tests: `no_std` bare metal has no test harness.

**The cross lane is a build, not a `cargo check`.**  `check` stops before
code generation, so it never hands an `asm!` template to an assembler.  RR1's
first compile found four `TLBI *OS` sites that `check` reported clean and
that do not encode for the target at all — they are FEAT_TLBIOS (ARMv8.4-A)
instructions, and Cortex-A76 (the RPi5's core) is ARMv8.2-A.

## Entrypoints and intent

- `./scripts/test_fast.sh`
  - fast local confidence gate (Tier 0 + Tier 1).
- `./scripts/test_smoke.sh`
  - semantic smoke path (Tier 0 + Tier 1 + Tier 2).
- `./scripts/test_full.sh`
  - broader local verification (smoke + Tier 3 anchor coverage).
- `./scripts/test_nightly.sh`
  - full + Tier 4 staged-candidate wrapper (explicit opt-in by environment flag).
  - Without `NIGHTLY_ENABLE_EXPERIMENTAL=1` the Tier-4 candidates do not run and
    this exits **0**, which is the mode the PR checklist means. With the flag
    set, a gate that cannot run (no bootable kernel image) reports NOT RUN and
    the command exits **77** — incomplete coverage, not a failure. Add
    `SELE4N_REQUIRE_GATES=1` to turn a skipped gate into a hard failure; that is
    the mode a release must pass.

CI should execute these repository scripts directly to avoid local/CI drift.

Required branch-protection checks and reproducible setup instructions are documented in [`docs/CI_POLICY.md`](../CI_POLICY.md). CI jobs run each tier incrementally (earlier tiers gated by job dependencies) to eliminate redundant re-execution.

No tier tests documentation: gates, tests and anchors check code. Documentation is kept accurate by review (see [`docs/CI_POLICY.md`](../CI_POLICY.md)).

WS-A8 baseline maturity automation is implemented in `.github/workflows/platform_security_baseline.yml`, adding an ARM64 fast-gate CI signal and automated baseline security scanning controls.

## Shared test library behavior

All test entrypoints use `scripts/test_lib.sh` for:

1. common argument handling (`--continue`; disables `set -e` in continue mode per WS-H3/H-12),
2. command execution wrappers (`run_check` — returns 0 on success, 1 on failure;
   `run_gate_check` — the same, plus it understands the reserved skip status),
3. centralized pass/fail, **and skip**, accounting and final report,
4. optional automatic Lean setup helper path if `lake` is missing.

### `run_gate_check` and the reserved skip status

A check that certifies a phase acceptance criterion must go through
**`run_gate_check`**, never `run_check`. A gate whose prerequisite is missing
(no QEMU, no bootable kernel image, no `devmem2`) exits **`SELE4N_SKIP_EXIT`
(77)** rather than 0, and `run_gate_check` records it as **NOT RUN**:
`finalize_report` then names every unexecuted gate and itself exits 77, so the
status survives the process boundary into the parent tier instead of being
scored PASS one level up.

Routing such a gate through `run_check` is the bug this exists to prevent —
`run_check` reads 77 as a non-zero exit and reports FAIL, turning honest
incomplete coverage into a red build, while the older idiom of exiting 0 from a
skip branch turned it into a green one. Neither is true. A skip announcement
must therefore be emitted through `record_skip` or followed by an exit carrying
the skip status; `scripts/test_gate_skip_accounting.sh` (Tier 0) pins both
directions, since a witness that cannot see a fall-through certifies nothing
either.

Set **`SELE4N_REQUIRE_GATES=1`** to promote any skipped gate to a hard failure.
The v1.0.0 release validation must run in that mode — a release may not certify
phases whose gates never executed (see
[`docs/HARDWARE_TESTING.md`](../HARDWARE_TESTING.md) §5–§6).

### Color-coded prefixes

The shared logger now colorizes output when running in an interactive terminal:

- category prefix colors (`[META]`, `[TRACE]`, `[HYGIENE]`, `[BUILD]`, `[INVARIANT]`),
- message-status colors for `RUN`, `PASS`, and `FAIL`,
- automatic fallback to plain text when output is non-interactive or `NO_COLOR` is set.

This keeps CI output clean while making local debugging much easier to scan.

## Why fixture checks matter

Type-checking alone can miss semantic regressions. Tier 2 trace + negative-state checks ensure critical runtime
stories remain visible and intentional, especially for milestone claims tied to executable behavior
(e.g., mint/revoke/delete and IPC handshake flows).

## How the test surface grew

Each tier was added when a class of defect got past the tiers below it, and
the reason is recorded with the cut that added it. Rather than restate that
here — where it would drift from the scripts — read
[`CHANGELOG.md`](../../CHANGELOG.md) at the version a gate appeared, and
`scripts/test_tier*.sh` for what each one checks today. Live figures come from
`python3 scripts/report_current_state.py`.

## Practical failure triage

- **Tier 0 fails:** remove placeholder markers or fix script-level lint/hygiene issues.
- **Tier 1 fails:** resolve first Lean compile/proof failure before chasing downstream errors.
- **Tier 2 fails:** if `test_tier2_trace.sh` fails, inspect missing fixture lines; if `test_tier2_negative.sh` fails, inspect malformed-state or IF-M1 runtime assertions (`negative_state_suite` / `information_flow_suite`) and expected branch behavior.
- **Tier 3 fails (`./scripts/test_tier3_invariant_surface.sh`):** verify theorem/bundle/trace anchor names are still present after refactor, then repair the exact missing anchor in the referenced file.  Note that `run_check` is fail-fast by default, so the first failure hides any that follow — re-run with `--continue` to see the full set before diagnosing.  An `object file '...olean' ... does not exist` error is **not** an anchor regression: it means a probe elaborated a module the tree has not built, which the v0.32.104 preamble build of `SeLe4n.Platform.Staged` is there to prevent; if one reappears, the probe imports something outside both that closure and the default `lake build` target, and needs its own build line placed *above* the probe.
- **Tier 4 fails (`./scripts/test_nightly.sh` / `./scripts/test_tier4_nightly_candidates.sh`):** inspect `tests/artifacts/nightly/` traces + determinism diff and decide whether the drift is semantic regression or an intentional behavior change that needs fixture updates.
