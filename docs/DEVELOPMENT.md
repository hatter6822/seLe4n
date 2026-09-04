# seLe4n Development Guide

The operating manual for working on seLe4n. Everything here is a rule you will
be held to by a gate, a command you will actually run, or a fact about the tree
you need before you write code.

**What this file is not.** It is not a status report. What is in flight is in
[`REGISTERED_DEBT.md`](REGISTERED_DEBT.md); what changed in a given
version is in [`CHANGELOG.md`](../CHANGELOG.md); what new code must assume
about the kernel today is in `CLAUDE.md`'s *Standing constraints and registered
debt*.

---

## 1. The project in one page

seLe4n is a microkernel written in **Lean 4**, improving on the seL4
architecture, with machine-checked proofs and **zero `sorry` and zero `axiom`**
in the production proof surface. Every kernel transition is an executable pure
function. The first hardware target is the **Raspberry Pi 5** (BCM2712,
Cortex-A76, ARMv8.2-A, 4 cores).

The tree has two halves that must both build:

| Half | Language | Where | Builds with |
|------|----------|-------|-------------|
| The kernel model, its transitions and all proofs | Lean 4.28.0 | `SeLe4n/`, `Main.lean`, `tests/` | Lake |
| The hardware abstraction layer, boot assembly, trap seam | Rust + aarch64 asm | `rust/` | Cargo |

They meet at `SeLe4n/Platform/FFI.lean` (`@[extern]` / `@[export]`) and at
`rust/sele4n-hal/src/`. A change on one side of that seam almost always needs a
change on the other.

**The kernel does not boot yet.** SM10.1 owns the bootable image; until it
lands, every runtime seam behind the per-core readiness gate
(`rust/sele4n-hal/src/lean_ready.rs`) is wired and dormant. Do not assume a
Lean seam executes on hardware merely because it is wired.

---

## 2. Set up

```bash
# Toolchain, elan, Lean 4.28.0, and the git hooks. Runs automatically as a
# SessionStart hook; run it by hand on a fresh clone.
./scripts/setup_lean_env.sh                  # includes shellcheck + ripgrep
./scripts/setup_lean_env.sh --skip-test-deps # toolchain only, no test deps
./scripts/setup_lean_env.sh --build          # also run a full build

# Every shell that runs lake needs this first:
source ~/.elan/env
```

### The pre-commit hook is not optional

```bash
./scripts/install_git_hooks.sh          # install (idempotent)
./scripts/install_git_hooks.sh --check  # verify (non-zero if absent)
./scripts/install_git_hooks.sh --force  # overwrite, backing up a diverging hook
```

The hook builds every staged `.lean` module, rejects `sorry` in staged content,
runs the identifier-naming gate against the **git index**, and verifies version
sync when a version-bearing file is staged. **Do not bypass it with
`--no-verify.**

Because the naming gate reads the index rather than the working tree, a Tier 0
run over unstaged edits checks the *previous* content: **stage first, then run
the gate.** The hook is the backstop, not the first line.

### Rust

```bash
rustup target add aarch64-unknown-none   # RR1.1 added this to rust-toolchain.toml
```

`rust/rust-toolchain.toml` pins the toolchain, and rustup's directory override
only applies **inside `rust/`**. Run cargo from there, never with
`--manifest-path` from the repo root — that silently selects the default
toolchain, which does not have the cross target.

---

## 3. Build

```bash
source ~/.elan/env
lake build                    # the default target
lake exe sele4n               # the executable trace harness
lake build <Module.Path>      # ONE module — see the rule below
```

### Module build verification is mandatory

**Before committing any `.lean` file, build that module by name:**

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge     # after editing Bridge.lean
```

`lake build` on the default target is **not sufficient**. It builds only what
is reachable from `Main.lean` and the test executables, so a module not yet
imported by the kernel passes the default target with broken proofs. The
pre-commit hook enforces this; the rule is here because you should not need the
hook to tell you.

`SeLe4n/Platform/Staged.lean` is the build anchor that pulls staged modules
into CI, so a staged module still compiles on every PR even though no linked
image carries it.

---

## 4. Test

Tiers are cumulative. Run the smallest one that covers what you changed, and at
minimum `test_smoke.sh` before any PR.

| Command | Tiers | Covers | Run it when |
|---------|-------|--------|-------------|
| `./scripts/test_fast.sh` | 0–1 | hygiene gates + full build | iterating locally |
| `./scripts/test_smoke.sh` | 0–2 | + trace, determinism, negative state, Rust, docs sync | **minimum before any PR** |
| `./scripts/test_full.sh` | 0–3 | + invariant surface anchors | changing theorems, invariants or doc anchors |
| `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | 0–4 | + nightly candidates, Tier-5 cross-language | before a release cut |

What each tier is for:

| Tier | Script | Question it answers |
|------|--------|---------------------|
| 0 | `test_tier0_hygiene.sh` | Is the tree well-formed? (~39 gates: naming, versions, links, plan structure, staging partition, axioms, TLBI discipline, cross-target config, de-threading) |
| 1 | `test_tier1_build.sh` | Does everything compile, including staged modules? |
| 2 | `test_tier2_trace.sh`, `_determinism.sh`, `_negative.sh` | Does the kernel produce the fixture trace, deterministically, and reject bad states? |
| 3 | `test_tier3_invariant_surface.sh` | Do the named theorems and invariants still exist and still say what the docs claim? |
| 4 | `test_tier4_smp_bootcheck.sh`, `_nightly_candidates.sh` | SMP acceptance — **needs the bootable image**, so it cannot run until SM10.1 |
| 5 | `test_tier5_cross_language.sh` | Do the Rust lock primitives agree with their Lean specs? |

The Tier-5 oracle **drives** both real reader-writer locks — a
`rw_lock::RwLock` and the deployed `queued_rw_lock::QueuedRwLock` — through
every generated operation and checks three relations after each one: that the
two implementations agree, that the queued lock's `[now_serving, next_ticket)`
interval matches the abstract waiter queue, and that the state word is
`encodeRwLock` of the abstract state.  It does not model them; the state it
renders is read back from the lock's own word.  Since v0.34.52 the driver
holds a **real ticket** for every queued waiter and the alphabet carries a
fifth letter, the withdrawal — so the interval check is derived from the
tombstoned invariant (outstanding tickets are the live waiters *plus* the
not-yet-passed tombstones) rather than from the writer bit alone.

### Rust, and the cross target

```bash
./scripts/test_rust.sh                 # host: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel's real target
```

**Run the cross build after any change under `rust/`.** The tier scripts and
`test_rust.sh` compile the *host* target, where every
`#[cfg(target_arch = "aarch64")]` block is removed before rustc or clippy sees
it — so the hardware half of the HAL, which is most of it, is invisible to
them. The cross gate builds `sele4n-hal` for `aarch64-unknown-none` in both
profiles, verifies `boot.S` / `vectors.S` / `trap.S` actually assembled, and
lints the cross target with `-D warnings`. It runs in CI as the
`aarch64 Cross Build` job.

**`cargo check` is not a substitute.** It stops before code generation, so it
never hands an `asm!` template to an assembler. The first real cross build
found six defects and three lints; four of the defects were `check`-clean.

### Concurrency model checking and miri

The deployed reader-writer lock is exercised by two tools the host test lane
cannot substitute for:

```bash
./scripts/test_loom_queued_rw_lock.sh   # exhaustive-interleaving model checking (~35 s)
./scripts/test_miri_queued_rw_lock.sh   # UB / strict-provenance checking
```

`loom` explores the lock's interleavings exhaustively — every schedule of each
two-thread model, with no preemption bound (the first cut capped it at three
preemptions and still called the run exhaustive; PR #890 review) — which is what
catches an ordering bug a stress test only makes *unlikely*.  Setting
`LOOM_MAX_PREEMPTIONS=n` bounds the run for a quick local pass, and that pass is
not the gate.  It
needs the lock compiled against its own instrumented atomics, so
`queued_rw_lock.rs` aliases `core::sync::atomic` under `cfg(loom)` and its
models live in a `#[cfg(loom)] mod loom_model`; a `loom` entry in the manifest
alone explores nothing.  The gate runs in CI as the
`test-loom-concurrency-model` job.

`miri` runs the lock's own suite under `-Zmiri-strict-provenance` and is wired
into `test_nightly.sh` behind `NIGHTLY_ENABLE_EXPERIMENTAL=1`.  The stress and
FIFO iteration counts scale down under `cfg(miri)` (`STRESS_ITER`,
`FIFO_ACQUISITIONS`) so the interpreter finishes, without weakening the
native-speed thresholds.

Both gates were verified decisive by a **relation-breaking** mutation rather
than by deleting a token: removing `await_turn` from `acquire_read` — which
leaves every symbol the gate might grep for in place — fails two of the five
loom models.

### Running one suite

There are 71 `lean_exe` targets. Run one directly:

```bash
lake exe negative_state_suite
lake exe information_flow_suite
lake exe fault_handling_suite
```

Or interpret it without building an executable — useful when a suite hits the
clang bracket-depth limit described in §7:

```bash
lake env lean --run tests/NegativeStateSuite.lean
```

### QEMU and hardware

`scripts/test_qemu*.sh` cover SMP bring-up, IPC, scheduler, timer, SGI
round-trip, TLB shootdown, deadlock and kprintln stress.
`scripts/test_hw_full.sh` and `docs/HARDWARE_TESTING.md` cover the RPi5 path.
Both need artefacts SM10.1 has not produced yet.

---

## 5. Repository layout

```
SeLe4n/PackedString.lean         Packed strings: one Nat per inventory string, kernel-cheap distinctness
SeLe4n/Prelude.lean              Typed identifiers, monad foundations
SeLe4n/Machine.lean              Machine state primitives
SeLe4n/Model/                    Object types, kernel/system state, builder, freeze
SeLe4n/Kernel/Scheduler/         Scheduler transitions, run queues, EDF, PIP, liveness
SeLe4n/Kernel/Capability/        CSpace/capability ops + invariants
SeLe4n/Kernel/IPC/               Endpoint/notification IPC, dual-queue, capability transfer
SeLe4n/Kernel/Lifecycle/         Thread suspend/resume, retype, cleanup
SeLe4n/Kernel/Service/           Service orchestration + policy
SeLe4n/Kernel/Architecture/      ARM64 page tables, exceptions, interrupts, TLB/cache,
                                 register/syscall decode, IPC buffer validation, faults
SeLe4n/Kernel/InformationFlow/   Security labels, projection, non-interference
SeLe4n/Kernel/RobinHood/         Verified Robin Hood hash table
SeLe4n/Kernel/RadixTree/         Verified flat-array CNode radix tree
SeLe4n/Kernel/SchedContext/      CBS budgets, replenishment queue, MCP authority
SeLe4n/Kernel/FrozenOps/         Frozen-state kernel operations (experimental)
SeLe4n/Kernel/Concurrency/       Locks, memory model, SMP assumption inventory
SeLe4n/Kernel/CrossSubsystem.lean  Cross-subsystem invariants, discharge index marker
SeLe4n/Kernel/API.lean           Public kernel interface + syscall wrappers
SeLe4n/Platform/Contract.lean    PlatformBinding typeclass
SeLe4n/Platform/DeviceTree.lean  FDT parsing
SeLe4n/Platform/FFI.lean         Lean <-> Rust HAL bridge (@[extern] / @[export])
SeLe4n/Platform/Boot.lean        Boot sequence (PlatformConfig -> IntermediateState)
SeLe4n/Platform/RPi5/            Raspberry Pi 5 (BCM2712) bindings, boot VSpace
SeLe4n/Platform/Staged.lean      Build anchor pulling staged modules into CI
SeLe4n/Testing/                  Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            ARM64 boot assembly + HAL crates
scripts/                         Every gate, tier script and generator
docs/                            Canonical documentation (see §10)
```

The filesystem is the authoritative file list; this map changes more slowly
than the tree does.

### Two structural rules

**Operations / Invariant split.** Each kernel subsystem has `Operations.lean`
(transitions) and `Invariant.lean` (proofs). Keep them apart. Both may be
re-export hubs over per-concern submodules in a sibling directory of the same
name — import-only files that keep existing `import` statements working.

**Staged vs production.** 67 modules are staged-only, listed in
`scripts/staged_module_allowlist.txt` and gated by
`check_production_staging_partition.sh`. **Production must not import staged.**
CI builds staged modules on every PR through `Platform/Staged.lean`; a linked
kernel image does not carry them.

---

## 6. Rules you will be held to

These are enforced by gates, so violating one fails the build rather than a
review. Each is here because it was violated at least once.

### No `sorry`, no `axiom`

Forbidden in the production proof surface. Tracked exceptions carry a `TPI-D*`
annotation. `check_module_axioms.py` runs map-driven rather than by regex,
because the old regex missed three `@[simp] theorem` declarations.

### Deterministic semantics

Every transition returns explicit success or failure. Never introduce a
non-deterministic branch.

### Typed identifiers

`ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId` and their kin are wrapper
structures, **not** `Nat` aliases. Convert explicitly with `.toNat` / `.ofNat`.

### Internal-first naming

Every identifier — theorem, function, definition, structure, field, test
runner, file name, directory name — describes **what it is**, not which
workstream produced it. Workstream IDs, audit IDs and phase codes (`WS-*`,
`AN3-*`, `RR4.9`, …) must not appear in any identifier or path.

```
BAD   an3b_02_projection_typing
GOOD  ipc_invariant_full_projection_signatures
```

Workstream IDs belong in docstrings, commit messages, CHANGELOG entries and
`CLAUDE.md` prose. Enforced by `check_identifier_naming.py`, which scans every
identifier token and path component over every tracked non-documentation file:
Rust is held at zero, everything else is pinned by an occurrence-count baseline
in `scripts/identifier_naming_baseline.json` — a grandfathered name's count may
fall but never rise.

Documentation paths are exempt by **location**, never by suffix: a `.json`,
`.txt` or `.expected` file outside `docs/` is code to this gate. Within a file
the exemption stops at any literal that supplies a linker-visible name
(`#[export_name]`, an assembly `.global`, a linker-script `PROVIDE`, an `asm!`
template).

### Fixture-backed evidence

`Main.lean`'s output must match `tests/fixtures/main_trace_smoke.expected`.
Update a fixture only with a stated rationale in the PR — see §9.

### Gates read code, prose reads prose

No comment or docstring may decide whether a check passes. Source-scanning
gates match against the **code view** (`scripts/lean_code_view.py --overlay`) —
a comment-free, byte-aligned overlay of the tree — so a docstring can neither
satisfy an anchor nor trip one. This is wired at the helper: `run_check` and
`run_negative_check` route through the view automatically.

When a check's subject genuinely *is* the text — a module docstring must exist,
a contract sentence must be present, a retracted figure must not return — use
`run_prose_check` / `run_prose_negative_check`, which read the real tree.

**Never contort prose to satisfy a scanner.** If a comment cannot say something
plainly, the scanner is reading the wrong text.

### A presence check is not a relation check

Nearly every gate here is a text scanner, and the recurring way one fails is
asserting that a *token is present* when the property it means is a *relation*:
that the flag reaches **this command**, that the guard precedes **this
instruction**, that the artefact came from **this run**, that the reference is
**this occurrence**. Presence is necessary and almost never sufficient, and the
gap is invisible because the token really is there.

**Resolve the text into the structure it stands for before asserting** — expand
the script's variables and check the command, take byte offsets and check the
order, parse the array and check the element, lex the source and check the
scope. The shared views exist for this: `scripts/rust_code_view.py`,
`scripts/lean_code_view.py`, and `rust_code_views` / `top_level_statements` in
`rust/sele4n-hal/build.rs`.

Where a scanner genuinely cannot decide (reachability, aliasing through a
value), say so in its docstring and make it over-approximate, so it fails
**closed**.

**Test a gate by breaking the relation, not by deleting the token.** A mutation
that removes the token is survived by any presence check. Keep the token and
break the relation: leave `hw_target` in the file but build another target;
keep `--release` but put it on a host build; keep the guard but move it after
the `asm!`. The self-test harnesses in `check_aarch64_cross_target.py` and
`check_tlbi_broadcast_discipline.py` **enforce** this — each case declares
whether its mutation is `preserving` or `deleting`, and the harness fails when
a check has no preserving case.

**And sweep the siblings.** A fix applied at one call site and not its
neighbours leaves the class open and reads as closed. Likewise, **an
enumeration standing in for a derivation** cannot see the thing that does not
exist yet: derive the set from what the code does and keep any list as a pin
that fails when the two diverge.

### Implement the improvement

When documentation, a docstring, a comment, a type signature or a design intent
describes something **better** than the code does, the remediation is to make
the description true. It is forbidden to weaken the documentation to match
inferior code.

| You find | You do | Never |
|----------|--------|-------|
| A comment referencing a function `X` that does not exist | implement `X` | remove the reference |
| A docstring describing a complete spec, a truncated implementation | complete the implementation | document the truncation |
| A stub returning `NotImplemented` where the design says it routes | wire the routing | note the stub |
| Two call paths handling one condition asymmetrically | make them symmetric | document the asymmetry |
| An invariant maintained only by convention | enforce it structurally | add a comment about the convention |
| A proven structure nothing consumes | wire it into the consumer | delete the structure |
| A capability claim whose path is non-functional | make the path work | qualify the claim |

The one legitimate exception is documentation describing a **worse** state than
the code — a stale `STATUS: staged` marker on a module since wired into
production. There, the documentation is the inferior artefact.

When the right implementation is genuinely out of scope, **defer the release**
and record the debt with a closure target. Do not ship a documentation-only
patch instead.

### Deferrals are registered, never silent

In-source TODOs that age out with their workstream are forbidden. Every
deferred item is lifted into the *Registered debt index* in
[`REGISTERED_DEBT.md`](REGISTERED_DEBT.md) with an owner and a closure
target, and the source comment cites it by row.
`check_deferral_registration.py` (Tier 0) fails a comment that declares itself
untracked and cites nothing, and fails a citation naming a row that does not
exist.

### Report a vulnerability the moment you find it

If you find a possible CVE-worthy issue — in project code, a dependency, the
toolchain, CI, or as a gap between the model and real seL4 behaviour — stop and
surface it with: summary, file and line, severity plus exploitability, evidence
or reproduction, and suggested remediation. **Do not silently fix it**; it has
to be tracked and disclosed.

---

## 7. Working in Lean here

### Read and edit large files in chunks

Several files exceed 800 lines. Read with explicit offsets rather than whole:

```
Read(path, offset=1,   limit=500)
Read(path, offset=501, limit=500)
```

```bash
./scripts/find_large_lean_files.sh                  # list files over threshold
./scripts/find_large_lean_files.sh --format bullets # regenerate CLAUDE.md's list
./scripts/find_large_lean_files.sh --check          # is CLAUDE.md's list current?
```

For edits, prefer targeted `old_string`/`new_string` replacements over
whole-file writes: a whole-file write of a large file times out and truncates
silently. Read the exact region first so the match includes the real
indentation. Build new large files incrementally, or with a `cat <<'EOF'`
heredoc, which has no size limit.

### The `do`-chain build trap

A suite with hundreds of sequential `expectErr` / `expectOkSt` calls in one
`do`-block compiles to a C `if`-tree deep enough to exceed clang's default
`-fbracket-depth=256`:

```
fatal error: bracket nesting level exceeded maximum of 256
```

The symptom is specific: `lake build <suite>:exe` fails while
`lake env lean --run <suite>.lean` works, because interpretation does not go
through the C backend.

**Mitigation**: keep test helpers under ~150 Lean lines and use the
thin-dispatcher pattern. `tests/NegativeStateSuite.lean`'s `runNegativeChecks`
is the model — a 13-line dispatcher over 8 per-area sub-helpers. C scope depth
resets at each function boundary. Factor up front rather than after the break.

### Keep search and command output bounded

If a command or search might return more than ~100 lines, bound it up front:
`head_limit` on searches, `| tail -80` on builds, or redirect to a file and read
it in slices. `lake build 2>&1 | tail -80` is the usual form.

### Proof hygiene

```bash
python3 scripts/check_proof_depth.py    # flags single-tactic bodies with no structure
python3 scripts/check_module_axioms.py  # axiom sweep, map-driven
```

---

## 8. Versioning: every PR bumps the patch version

There is no "release cut" accumulation and no `Unreleased` heading. Each merged
PR ships its own `vX.Y.Z`, and the docs always reflect the live version.

```bash
./scripts/bump_version.sh 0.34.46     # rewrites every site, then self-verifies
./scripts/check_version_sync.sh       # verify only (Tier 0 + pre-commit)
```

- **Canonical source**: the `version` field in `lakefile.toml`. Every other
  site must equal it.
- **The sites** are listed authoritatively in `scripts/version_locations.sh` —
  36 of them across `lakefile.toml`, the four `sele4n-*` crates, `KERNEL_VERSION`
  in `rust/sele4n-hal/src/boot.rs`, the spec, `CLAUDE.md` + `AGENTS.md`, the
  root README badge and version row, eleven i18n READMEs, three GitBook files
  and `docs/codebase_map.json`.
- **Adding a site**: register it once in `scripts/version_locations.sh`; the
  verifier and the bumper both pick it up.
- **Then add a CHANGELOG entry** — `## v<new-version> — <summary>` at the top
  of [`CHANGELOG.md`](../CHANGELOG.md). The bumper reminds you; it does not do
  it for you.
- **Not version sites**: historical prose (CHANGELOG headers, "LANDED at
  vX.Y.Z" notes), the Lean toolchain version, and audit-document filenames.

There is deliberately **no** force-bump gate, so automated contributors are
never blocked.

---

## 9. Documentation rules

### Canonical ownership

| Layer | Owns |
|-------|------|
| Root `docs/*.md` | policy, spec, ADRs — the canonical text |
| `docs/gitbook/` | mirrors that summarize and link to the canonical text |
| [`CHANGELOG.md`](../CHANGELOG.md) | the per-version narrative, one entry per PR |
| [`REGISTERED_DEBT.md`](REGISTERED_DEBT.md) | workstream status, ownership, the debt register |
| `docs/planning/*.md` | the *schedule* for a phase — its sub-tasks, not its history |

A landed phase's plan carries its sub-task table, not an account of what each
cut changed. That account is the CHANGELOG's, and duplicating it produces two
records that drift.

### When you change behaviour, theorems or workstream status

Update, in the same PR:

1. `README.md` — metrics sync from `docs/codebase_map.json` (`readme_sync`)
2. `docs/spec/SELE4N_SPEC.md`
3. This file, if a command or rule changed
4. The affected GitBook chapter(s) — canonical root docs take priority
5. `docs/CLAIM_EVIDENCE_INDEX.md`, if a claim changed
6. `REGISTERED_DEBT.md`, if workstream status changed
7. `docs/codebase_map.json`, if Lean sources changed

### Sync commands

```bash
./scripts/sync_documentation_metrics.sh          # the whole chain, in order
python3 scripts/generate_codebase_map.py --pretty # regenerate the map
python3 scripts/generate_codebase_map.py --pretty --check  # is it current?
./scripts/sync_readme_from_codebase_map.sh       # README + spec metrics
./scripts/test_docs_sync.sh                      # the gate CI runs
python3 scripts/generate_doc_navigation.py       # GitBook README + SUMMARY
python3 scripts/report_current_state.py          # current metrics, one per line
```

`CLAUDE.md` and `AGENTS.md` must stay **byte-identical below their headers** —
`test_docs_sync.sh` checks it. Edit both in the same PR.

### Fixture updates

A fixture change is a claim that the kernel's observable behaviour changed on
purpose.

```bash
lake exe sele4n > tests/fixtures/main_trace_smoke.expected   # only with a reason
./scripts/test_smoke.sh                                       # then prove it holds
```

State the rationale in the PR body and in the CHANGELOG entry: what transition
changed, why the new trace is correct, and what would have been wrong about
keeping the old one. A fixture updated to make a test pass is a defect.

### Generated artefacts

```bash
python3 scripts/generate_smp_theorem_manifest.py           # regenerate
python3 scripts/generate_smp_theorem_manifest.py --check   # Tier 0 check
```

The SMP theorem total is **measured, not summed**: the manifest registers one
entry per phase and the propositionality census resolves each identifier
against the environment. Never reintroduce a hand-written per-phase figure.

### Website link protection

The project website links to source files, docs, scripts and directories in
this repository. Protected paths are listed in
`scripts/website_link_manifest.txt` and checked by
`scripts/check_website_links.sh` (Tier 0). To rename or remove one:

1. update the website (`hatter6822.github.io`) to the new path **first**;
2. then update `scripts/website_link_manifest.txt`;
3. CI passes only when the manifest and the tree agree.

### Session URL hygiene

A `https://claude.ai/code/session_*` URL must never appear in a commit message,
PR title or body, in-tree documentation, CHANGELOG entry, source comment, test
fixture, or any GitHub comment. Cite the canonical document instead:

```
Refs: docs/planning/SMP_RELEASE_READINESS_PLAN.md sections RR5, RR6
Refs: #761
Refs: 7da2572
```

### Ignore `docs/dev_history/`

It holds milestone closeouts, prior audit reports, completed workstream plans
and legacy GitBook chapters, kept only for traceability. Do not read or
reference it unless explicitly instructed.

---

## 10. Where the documentation is

| Read this | For |
|-----------|-----|
| [`../README.md`](../README.md) | the project at a glance, current metrics |
| [`spec/SELE4N_SPEC.md`](spec/SELE4N_SPEC.md) | the kernel specification |
| [`spec/SEL4_SPEC.md`](spec/SEL4_SPEC.md) | what seL4 does, for comparison |
| [`CLAIM_EVIDENCE_INDEX.md`](CLAIM_EVIDENCE_INDEX.md) | every public claim and the theorem or test backing it |
| [`THREAT_MODEL.md`](THREAT_MODEL.md) | the security model and its boundaries |
| [`HARDWARE_TESTING.md`](HARDWARE_TESTING.md) | the RPi5 bring-up path |
| [`DEPLOYMENT_GUIDE.md`](DEPLOYMENT_GUIDE.md) | building and deploying an image |
| [`CI_POLICY.md`](CI_POLICY.md) | what CI runs and why it is pinned |
| [`INFORMATION_FLOW_ROADMAP.md`](INFORMATION_FLOW_ROADMAP.md) | the non-interference surface |
| `*_ADR.md` | architecture decisions and their alternatives |
| [`planning/`](planning/) | per-phase schedules |
| [`gitbook/`](gitbook/) | the published book; mirrors of the above |

---

## 11. The contribution loop

1. **Find the workstream.** Check
   [`REGISTERED_DEBT.md`](REGISTERED_DEBT.md) for what is in flight and
   the phase plan for the sub-task you are taking. Sub-task numbers are
   execution order: a plan that says `RR5.10` before `RR5.11` means exactly
   that, and a sub-task may only consume a lower-numbered one.
2. **Read the standing constraints.** `CLAUDE.md`'s *Standing constraints and
   registered debt* is current facts about the tree — what a live seam does,
   what is dormant, what new code must not assume. It changes what you may
   write.
3. **Scope one coherent slice.** One PR is one sub-task or less.
4. **Write transitions and their proofs together.** A live kernel transition
   must not land ahead of its own invariant surface. If the two cannot be
   split — the theorems unfold the function the switch replaces — they are one
   PR, not two.
5. **Build the module by name** (§3) and run the right tier (§4).
6. **Bump the version and write the CHANGELOG entry** (§8).
7. **Sync the documentation** (§9).
8. **Stage, then run Tier 0** — the naming and plan gates read the index.
9. **Commit.** The hook runs; do not bypass it.

### PR checklist

Copy into the PR body:

```
- [ ] Workstream ID identified
- [ ] Scope is one coherent slice
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with the implementation
- [ ] Module build verified (hook installed, not bypassed)
- [ ] test_smoke.sh passes (test_full.sh if theorems changed)
- [ ] test_aarch64_cross_build.sh passes (if rust/ changed)
- [ ] Documentation synchronized
- [ ] Patch version bumped, all sites synced, CHANGELOG entry added
- [ ] No website-linked path renamed or removed
- [ ] No claude.ai session URL anywhere in the commit or PR
```

### Definition of done for a milestone-moving change

- The theorem or transition exists, is named for what it does, and is reachable
  from production (or explicitly staged, with the allowlist entry to prove it).
- Tier 0–3 green; Tier 4 honest about what it could not run.
- Every claim the change makes is cited in `CLAIM_EVIDENCE_INDEX.md`.
- Every deferral it creates is a row in the debt register with an owner.
- The CHANGELOG entry says what changed, what it found, and how it was
  verified.

---

## 12. When something fails

| Symptom | Cause | Fix |
|---------|-------|-----|
| `lake: command not found` | elan not on PATH | `source ~/.elan/env` |
| Module passes `lake build` but CI fails | default target does not reach it | `lake build <Module.Path>` by name |
| `bracket nesting level exceeded maximum of 256` | deep `do`-chain in a suite | split into per-area helpers (§7) |
| Tier 0 naming gate passes locally, fails in CI | gate reads the git index | `git add` first, then re-run |
| `check_version_sync.sh` fails | a version site missed | `./scripts/bump_version.sh <version>` |
| `docs/codebase_map.json is stale` | Lean sources changed after the last sync | `python3 scripts/generate_codebase_map.py --pretty` |
| `CLAUDE.md 'Known large files' differs` | a file crossed the 10% tolerance | `./scripts/find_large_lean_files.sh --format bullets`, replace the block in **both** CLAUDE.md and AGENTS.md |
| Cross build fails but `cargo check` was clean | `check` never reaches codegen | that is the point — fix the `asm!` or the encoding |
| A `TLBI *OS` wrapper halts the core | FEAT_TLBIOS is ARMv8.4-A; Cortex-A76 is ARMv8.2-A | use the `*IS` variant; the `*OS` path is fail-closed by design |
| Production module cannot import what it needs | it is on the staged allowlist | promote it deliberately, or restructure — production must not import staged |
| A push to `main` is rejected | branch protection | branch first; never push to the default branch |

Proxy or TLS failures on outbound HTTPS: see `/root/.ccr/README.md` and
`curl -sS "$HTTPS_PROXY/__agentproxy/status"`. Never disable TLS verification
and never unset `HTTPS_PROXY`.

---

## 13. Command reference

```bash
# --- setup -------------------------------------------------------------
./scripts/setup_lean_env.sh [--skip-test-deps] [--build] [--quiet]
./scripts/install_git_hooks.sh [--check|--force]
source ~/.elan/env

# --- build -------------------------------------------------------------
lake build                                   # default target
lake build <Module.Path>                     # one module (required before commit)
lake exe sele4n                              # trace harness
lake env lean --run tests/<Suite>.lean       # interpret a suite

# --- test --------------------------------------------------------------
./scripts/test_fast.sh                       # tiers 0-1
./scripts/test_smoke.sh                      # tiers 0-2   (PR minimum)
./scripts/test_full.sh                       # tiers 0-3
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh   # tiers 0-4
./scripts/test_rust.sh                       # host Rust
./scripts/test_aarch64_cross_build.sh        # cross target (after any rust/ change)
./scripts/test_tier5_cross_language.sh       # Lean <-> Rust lock oracle
SELE4N_REQUIRE_GATES=1 ./scripts/test_tier4_smp_bootcheck.sh   # gate honesty

# --- gates you can run alone -------------------------------------------
./scripts/test_tier0_hygiene.sh
./scripts/check_version_sync.sh
./scripts/check_website_links.sh
python3 scripts/check_workstream_plan.py [--self-test]
python3 scripts/check_deferral_registration.py
python3 scripts/check_identifier_naming.py
python3 scripts/check_module_axioms.py
python3 scripts/check_proof_depth.py
python3 scripts/check_ipc_invariant_dethreading.py
python3 scripts/check_aarch64_cross_target.py
python3 scripts/check_tlbi_broadcast_discipline.py
./scripts/check_production_staging_partition.sh

# --- version and docs --------------------------------------------------
./scripts/bump_version.sh <x.y.z>
./scripts/sync_documentation_metrics.sh
./scripts/test_docs_sync.sh
python3 scripts/generate_codebase_map.py --pretty [--check]
python3 scripts/generate_doc_navigation.py
python3 scripts/generate_smp_theorem_manifest.py [--check]
python3 scripts/report_current_state.py
./scripts/find_large_lean_files.sh [--check|--format bullets]
```

---

## 14. Third-party code

seLe4n is GPLv3+ (see [`../LICENSE`](../LICENSE)). The Rust workspace pulls a
small set of **build-time only** crates (`cc`, `find-msvc-tools`, `shlex`) to
assemble ARM64 boot assembly; **no third-party code is linked into the runtime
kernel binary.** Their upstream MIT notices are reproduced verbatim in
[`../THIRD_PARTY_LICENSES.md`](../THIRD_PARTY_LICENSES.md).

1. Adding a **runtime** dependency (`[dependencies]` of any crate under
   `rust/`) means updating `THIRD_PARTY_LICENSES.md` in the same PR with the
   verbatim upstream copyright lines, and adding the path to
   `scripts/website_link_manifest.txt`.
2. Bumping an external crate means re-checking its `LICENSE-MIT` and
   `Cargo.toml` for authorship changes, and re-checking for a new upstream
   `NOTICE` (Apache-2.0 § 4(d)).
3. Prefer `core::*` and hand-written minimal code over a crate. **A
   microkernel's trusted computing base must stay small.**
