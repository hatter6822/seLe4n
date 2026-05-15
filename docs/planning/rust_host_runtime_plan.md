# WS-RH — Rust Host Runtime Workstream Plan

> **Workstream code-name:** WS-RH ("Rust Host runtime")
> **Audited cut:** `v0.31.3`
> **Target releases:** v0.31.4 .. v0.32.x
> **Plan author branch:** `claude/workspace-ci-harness-3C7fK`
> **Governing engineering rule:** CLAUDE.md "Implement-the-improvement
> rule" — when documentation describes a *better* state than the code,
> the remediation is to implement the description.

## 0. How to read this plan

This document is the canonical decomposition of WS-RH, a workstream
that introduces a host-side Rust runtime crate (`sele4n-host`) to the
existing `rust/` workspace. The host runtime fills a gap in the
testing and conformance story: today the workspace ships four
`no_std` crates (`sele4n-types`, `sele4n-abi`, `sele4n-sys`,
`sele4n-hal`) that build and execute correctly on bare metal but
provide no host-side reference for end-to-end ABI cross-validation or
for driving the verified kernel transitions from a Linux/macOS
developer workstation without QEMU.

WS-RH is decomposed into **eight phases** (RH-H, RH-A .. RH-G). The
first phase (RH-H — Workspace and CI harness) lands the workspace
member, CI integration, and library scaffolding. Subsequent phases
add behaviour:

| Phase | Slice | Notional version |
|---|---|---|
| **RH-H** | Workspace and CI harness | v0.31.4 |
| RH-A | Runtime context type + boot wiring | v0.31.5 |
| RH-B | Register-file fixture + `SyscallRequest` host injection | v0.31.6 |
| RH-C | `KernelError` decode path + host-side trap surface | v0.31.7 |
| RH-D | IPC buffer fixtures + structured trace replay | v0.31.8 |
| RH-E | Capability fixture builder + W^X regression replay | v0.31.9 |
| RH-F | Cross-validation harness — Rust ↔ Lean register layout parity | v0.32.0 |
| RH-G | Documentation, GitBook chapter, closure | v0.32.1 |

This plan focuses on RH-H. Per-phase plans for RH-A..RH-G will be
filed in this directory when WS-RH RH-H closes and the workspace
membership stabilises.

The host runtime is **distinct** from the existing `sele4n-sys`
syscall-wrapper crate: `sele4n-sys` is `no_std`, lives in the
guest/user-mode trusted computing base, and traps via `svc #0` to
the kernel. `sele4n-host` is `std`, lives on the developer
workstation, and never traps — it provides a host-side surface
for fixture construction, structured ABI decoding, and (in later
phases) cross-validation against the verified Lean executable
transitions.

## 1. Executive summary

### 1.1 What this workstream closes

WS-RH closes the host-side conformance gap. Today the `sele4n-abi`
crate carries an `--dev-dependencies` link on `sele4n-sys` to drive
its conformance tests; those tests run register-by-register
encode/decode parity against literal expected layouts hand-copied
from the Lean ABI specification. There is no host-side mechanism to:

1. **Construct** a register-file fixture from a high-level
   declarative description (currently each test hand-builds the
   `SyscallRequest` literal).
2. **Replay** a kernel trace by re-applying the same `SyscallRequest`
   sequence to a host-side state mirror.
3. **Cross-validate** a Rust-encoded register file against the
   Lean-decoded register file by running both encode/decode paths
   over the same input vector and asserting structural equality
   on the decoded representation, not just on the raw register
   words.
4. **Expose** the verified kernel's transition functions to host
   tooling (a future audit batch could drive the kernel from a
   shell-style REPL for exploratory testing).

The host runtime is the natural home for all four capabilities. It
sits at the architectural boundary between the (no_std, register-
abi-encoding) `sele4n-abi` crate and the (host-side, std,
filesystem-using) test scripts. Each later WS-RH phase adds one
of these capabilities; RH-H is the foundation phase that lands the
crate, its workspace membership, its CI harness, and its
scaffolding modules so the later phases have somewhere to land.

### 1.2 Defining outcome — RH-H

RH-H must produce a `sele4n-host` crate that:

1. **Compiles cleanly** on `cargo build --workspace` and
   `cargo build --workspace --release` with the workspace's
   pinned MSRV (Rust 1.82.0).
2. **Passes** `cargo test --workspace` with zero warnings under
   the strict lint profile (`-D warnings`).
3. **Provides** scaffolding modules (`runtime`, `dispatch`,
   `state`, `fixture`) that compile to empty (no-effect) APIs
   with documented invariants. Later WS-RH phases fill these in.
4. **Carries** unit tests for every public API at the scaffold
   level — even no-op stubs must have a test that asserts the
   stub's documented behaviour.
5. **Integrates** into `scripts/test_rust.sh` (the existing Rust
   test gate) and the `Lean Action CI` workflow (the existing
   `test-rust` job).
6. **Maintains** the workspace's structural rules: zero `unsafe`
   code, GPL-3.0-or-later SPDX header on every file, accurate
   doc-comments on every public item, no third-party runtime
   dependencies.

The crate is `std` (not `no_std`) — it is a host-side runtime and
freely uses `std::collections`, `std::io`, etc. The workspace's
`panic = "abort"` profile setting still applies (it is workspace-
wide), but the host crate is allowed to use `Result` for fallible
operations rather than panicking on invalid input.

### 1.3 Release-path positioning

WS-RH is **post-v1.0**. The v1.0 release gate is defined by WS-SM
(SMP multi-core completion) and is closed by the bootable verified
SMP microkernel on Raspberry Pi 5. WS-RH adds developer-side
tooling and does not affect the v1.0 correctness or completeness
claims. It is therefore staged to land **after** v1.0.0, in the
v0.31.4..v0.32.x cuts, on a non-blocking release cadence.

The first phase (RH-H) is, however, suitable to land in the
v0.31.4 cut (i.e., the next non-SMP non-v1.0 cut) because it adds
zero behaviour and zero risk to the kernel proof artefact: it
only adds a new workspace crate that the `no_std` kernel binary
never links against.

## 2. RH-H — Workspace and CI harness

### 2.1 Phase goal

Add the `sele4n-host` crate to the existing `rust/` workspace with
the minimum surface needed for later phases to extend. The phase
delivers:

- A new workspace member `sele4n-host` at `rust/sele4n-host/`.
- A `Cargo.toml` declaring the crate, its dependencies on the
  other workspace members (`sele4n-types`, `sele4n-abi`), its
  `std` opt-in on those dependencies, and its strict lint
  profile.
- A `src/lib.rs` providing the scaffolding modules (`runtime`,
  `dispatch`, `state`, `fixture`) with documented public APIs.
- A `tests/scaffold.rs` integration test covering every public
  scaffolding API.
- Updates to `scripts/test_rust.sh` so the existing Tier-2 Rust
  gate exercises the new crate.
- Updates to the `Lean Action CI` workflow so the existing
  `test-rust` job exercises the new crate.
- Documentation updates: `README.md` (workspace surface),
  `docs/spec/SELE4N_SPEC.md` (host-runtime placement),
  `docs/CLAIM_EVIDENCE_INDEX.md` (new WS-RH claim row),
  `docs/WORKSTREAM_HISTORY.md` (new WS-RH entry),
  `CHANGELOG.md` (new release entry), and the `Active workstream
  context` section in `CLAUDE.md` / `AGENTS.md`.

### 2.2 Mathematical / semantic foundations relevant to RH-H

RH-H delivers no new proof obligations and no new transition
semantics. Its semantic contribution is **interface-level**:

1. **Workspace member partition.** After RH-H, the `rust/`
   workspace has five members partitioned by execution
   environment:

   - `sele4n-types`        : `no_std`, shared types     (env-agnostic).
   - `sele4n-abi`          : `no_std`, ABI encode/decode (env-agnostic).
   - `sele4n-sys`          : `no_std`, guest syscall wrappers (guest-side).
   - `sele4n-hal`          : `no_std`, kernel-side HAL  (kernel-side).
   - `sele4n-host`         : `std`,    host runtime     (host-side, **new**).

   The host-side member is the first `std` member of the workspace.
   The workspace remains `no_std`-compatible for the kernel/guest
   crates; only `sele4n-host` opts into `std`.

2. **Trusted Computing Base (TCB) invariance.** `sele4n-host` is
   not part of the kernel TCB and is not linked into the kernel
   binary. The kernel binary's TCB is identical before and after
   WS-RH lands. This is enforced structurally by the workspace
   partition: the `no_std` crates do not depend on `sele4n-host`,
   and the kernel binary (built via `sele4n-hal`) does not
   transitively reach it.

3. **Lint and unsafety partition.** RH-H continues the workspace
   convention that "exactly one crate (`sele4n-hal`) is allowed to
   contain `unsafe` blocks; every other crate denies `unsafe`
   code crate-wide". The host runtime inherits the
   `#![deny(unsafe_code)]` attribute.

These three properties are stated explicitly in the host crate's
`lib.rs` docstring and asserted at compile time via
`#![deny(unsafe_code)]` and the workspace `Cargo.toml`
membership list.

### 2.3 Sub-task decomposition

RH-H is decomposed into **ten** atomic sub-tasks. Each sub-task is
independently committable and landed in dependency order. The
phase closure gate is: every sub-task lands, the new crate
compiles + tests pass, all documentation is synchronized, and the
website link manifest reflects the new paths.

| Sub-task | Description | File(s) | Gate |
|---|---|---|---|
| RH-H.1 | Add `sele4n-host` to workspace members in `rust/Cargo.toml`. | `rust/Cargo.toml` | `cargo build --workspace` |
| RH-H.2 | Create `rust/sele4n-host/Cargo.toml` with deps on `sele4n-types`/`sele4n-abi` and `std` feature flags. | `rust/sele4n-host/Cargo.toml` | crate compiles |
| RH-H.3 | Create `rust/sele4n-host/src/lib.rs` with SPDX header, crate-level docstring, lint deny lists, module declarations. | `rust/sele4n-host/src/lib.rs` | `cargo build` |
| RH-H.4 | Create `rust/sele4n-host/src/runtime.rs` — `HostRuntime` struct with `new()`, `version()`, and `workspace_version_pinned()` constants. | `rust/sele4n-host/src/runtime.rs` | unit tests pass |
| RH-H.5 | Create `rust/sele4n-host/src/dispatch.rs` — `DispatchOutcome` enum mirroring the `sele4n-hal::svc_dispatch::DispatchError` shape; `decode_outcome` host helper. | `rust/sele4n-host/src/dispatch.rs` | unit tests pass |
| RH-H.6 | Create `rust/sele4n-host/src/state.rs` — `HostState` placeholder + `HostStateError` enum + structural accessors. | `rust/sele4n-host/src/state.rs` | unit tests pass |
| RH-H.7 | Create `rust/sele4n-host/src/fixture.rs` — `FixtureBuilder` placeholder, `FixtureSnapshot` newtype around a register file, deterministic encode helpers. | `rust/sele4n-host/src/fixture.rs` | unit tests pass |
| RH-H.8 | Create `rust/sele4n-host/tests/scaffold.rs` — public-API integration coverage. | `rust/sele4n-host/tests/scaffold.rs` | `cargo test -p sele4n-host` |
| RH-H.9 | Update `scripts/test_rust.sh` to exercise the new crate. Update `.github/workflows/lean_action_ci.yml` so the existing `test-rust` job picks it up automatically (workspace-level test commands already do this — verify and document). | `scripts/test_rust.sh`, `.github/workflows/lean_action_ci.yml` | `./scripts/test_rust.sh` |
| RH-H.10 | Update documentation: `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, `CLAUDE.md` (active workstream block), `AGENTS.md` (mirror), `scripts/website_link_manifest.txt`. | (multiple) | `./scripts/test_docs_sync.sh`, `./scripts/check_website_links.sh` |

### 2.4 Per-sub-task implementation detail

#### RH-H.1 — Workspace member addition

`rust/Cargo.toml` currently lists four members:

```toml
[workspace]
resolver = "2"
members = [
    "sele4n-types",
    "sele4n-abi",
    "sele4n-sys",
    "sele4n-hal",
]
```

RH-H.1 appends `"sele4n-host"` to this list. The list order is
**deferred-dependency-order**: `sele4n-types` first (zero deps),
then `sele4n-abi` (depends on `sele4n-types`), then `sele4n-sys`
(depends on `sele4n-abi`), then `sele4n-hal` (zero deps, kernel-
side). `sele4n-host` joins at the end of the list because it
depends on the env-agnostic crates and conceptually sits at the
top of the host-side dependency stack.

The workspace `panic = "abort"` profile applies to the new crate
automatically (workspace-wide setting).

#### RH-H.2 — Crate Cargo.toml

```toml
[package]
name = "sele4n-host"
description = "Host-side runtime for the seLe4n verified microkernel — std, zero unsafe"
version.workspace = true
edition.workspace = true
license.workspace = true
repository.workspace = true

[features]
default = []

[dependencies]
sele4n-types = { path = "../sele4n-types", features = ["std"] }
sele4n-abi   = { path = "../sele4n-abi",   features = ["std"] }
```

Key choices:

1. **No `default-features = false` on the path deps** because the
   path deps already default to `default = []` (no_std-only with
   an opt-in `std` feature). Enabling `["std"]` directly is the
   correct surface.
2. **No third-party runtime dependencies** for RH-H. Later phases
   may introduce optional dev-dependencies for fixture-format
   parsing (e.g., a TOML parser for declarative fixtures), but
   the foundation phase deliberately keeps the supply chain
   minimal.
3. **No `[[bin]]` target** at this phase — the crate is a library
   only. Later phases may add a thin `[[bin]]` driver for
   exploratory testing, but the foundation phase keeps the
   surface as small as the library API.

#### RH-H.3 — lib.rs crate root

The `lib.rs` carries:

1. SPDX header (`// SPDX-License-Identifier: GPL-3.0-or-later`).
2. Crate-level docstring describing the host-runtime role,
   distinguishing it from `sele4n-sys` (guest-side wrappers).
3. Lint attributes:
   - `#![deny(unsafe_code)]` — zero unsafe in the host runtime.
   - `#![deny(missing_docs)]` — every public item is documented.
   - `#![deny(rust_2018_idioms)]` — idiomatic Rust enforcement.
   - `#![warn(clippy::all)]` is **not** added (the workspace
     does not currently impose clippy denies on the other
     crates; consistency wins).
4. Module declarations for `runtime`, `dispatch`, `state`,
   `fixture`.
5. `pub use` re-exports for the canonical public types of each
   module.

#### RH-H.4 — `runtime` module

`HostRuntime` is the entry-point type for later phases to attach
behaviour to. At the RH-H scaffold level, it carries:

- `new()` — construct a fresh runtime with the workspace-pinned
  version metadata.
- `version()` — returns the workspace-pinned `&'static str`
  version, used by tests to verify that the workspace member is
  reading the correct `Cargo.toml`.
- `workspace_version_pinned()` — `const fn` returning the same
  version, used by tests to verify compile-time consistency.

The version string is sourced from `env!("CARGO_PKG_VERSION")`
which Cargo materialises from the workspace-package version. The
unit test asserts `version() == "0.31.3"` to catch regressions
where the workspace version drifts out of sync with the
lakefile.

#### RH-H.5 — `dispatch` module

The `dispatch` module hosts the host-side mirror of the kernel's
syscall-dispatch outcome shape. At RH-H scaffold level:

- `DispatchOutcome` is an enum with three variants: `Ok(u64)`
  (the success-encoded UInt64 return value from the kernel),
  `KernelError(sele4n_types::KernelError)`, and
  `DispatcherInternal(DispatcherInternalError)`.
- `DispatcherInternalError` is an enum with `InvalidSyscallId`,
  `InvalidArgument`, `AbiMismatch` (mirroring the
  `sele4n-hal::svc_dispatch::DispatchError` shape).
- `decode_outcome(packed: u64) -> DispatchOutcome` — decodes a
  bit-63-flagged UInt64 into the host-side outcome enum,
  matching the contract documented in
  `SeLe4n/Platform/FFI.lean::syscallDispatchFromAbi`.

This module is the host-side equivalent of the `KernelError`
decoding the Rust syscall caller performs after `svc #0`. It
gives later phases a single decoding seam.

#### RH-H.6 — `state` module

`HostState` is a placeholder type for later phases to populate
with a structural mirror of the Lean `SystemState`. At RH-H:

- `HostState::empty()` — constructs an empty state with zero
  threads, zero objects, zero registered services.
- `HostState::is_empty()` — `true` iff no objects/services are
  installed.
- `HostStateError` enum with `Uninitialised`, `BoundedCapacity`,
  `InvalidFixture` variants (mirrors of common error shapes the
  Lean kernel emits).

`HostState` is intentionally a **structural placeholder** at this
phase: no real state-machine semantics yet. Later phases populate
the fields and add the actual transition glue. The placeholder
exists so that the dispatch and fixture modules can refer to it
by type and so that tests can assert "the state surface
compiles" without needing to plumb every field through.

#### RH-H.7 — `fixture` module

`FixtureBuilder` is the entry point for declarative fixture
construction in later phases. At RH-H:

- `FixtureBuilder::new()` — constructs a default builder.
- `FixtureBuilder::with_syscall_id(id)` — sets the syscall id.
- `FixtureBuilder::with_message_info(info)` — sets the message info.
- `FixtureBuilder::build()` — produces a `FixtureSnapshot`.
- `FixtureSnapshot` — a newtype around `[u64; 8]` (the eight-
  register layout the kernel observes on syscall entry per
  `arm64DefaultLayout`).
- `FixtureSnapshot::registers()` — read-only register accessor.

This is a thin facade. The real value comes in RH-B/RH-C/RH-D
when the builder grows IPC-buffer support, capability fixtures,
and W^X regression fixtures. RH-H plumbs the surface so the
later phases don't reshape the crate's public API every cut.

#### RH-H.8 — Integration test surface

`rust/sele4n-host/tests/scaffold.rs` exercises every public API
declared in §RH-H.4..7. The test file uses Rust's standard
`#[test]` harness and produces structured assertions:

- `runtime_version_matches_workspace` — checks `HostRuntime::version()`
  reports the same string as `env!("CARGO_PKG_VERSION")`.
- `runtime_const_version_matches_runtime_version` — checks the
  const-fn and the dynamic accessor agree.
- `dispatch_decode_success` — encodes/decodes a success return.
- `dispatch_decode_kernel_error` — encodes/decodes every
  `KernelError` discriminant (sweeps 0..=52, plus the 255
  sentinel).
- `dispatch_decode_dispatcher_internal` — covers the three
  internal-error variants.
- `state_empty_is_empty` — `HostState::empty().is_empty()` is
  `true`.
- `state_error_variants_distinct` — asserts the three
  `HostStateError` variants are distinct (catches accidental
  variant collapse).
- `fixture_builder_round_trip` — builds a fixture with a
  known syscall id and message info; reads the resulting
  registers; asserts the syscall-id and message-info registers
  carry the expected values per `arm64DefaultLayout`.
- `fixture_snapshot_register_count` — `registers().len() == 8`.

The test count target is **≥ 10 tests** for RH-H. Each test is
named after the property it verifies (CLAUDE.md "Internal-first
naming"); no `RH-H.N` numeric suffix appears in any test
identifier.

#### RH-H.9 — CI integration

`scripts/test_rust.sh` currently runs three steps:

1. `cargo build --all` (host target).
2. `cargo test --all --features std` (workspace unit tests).
3. `cargo test -p sele4n-abi --features std --test conformance`
   (per-crate conformance suite).

RH-H adds a fourth step:

4. `cargo test -p sele4n-host --test scaffold` — runs the
   integration tests added in RH-H.8.

The `--all` of step (2) already discovers the new crate via the
workspace, so RH-H.9 is principally an **explicit-coverage** step
that ensures the new integration test is exercised even if the
workspace-wide test set is filtered (e.g., a future PR adds a
`--workspace --exclude sele4n-host` filter for a CI lane that
needs to isolate host-target tests).

`.github/workflows/lean_action_ci.yml`'s `test-rust` job already
runs `cargo test --workspace` (from the rust dir), so it picks up
the new crate automatically. No workflow-level edits are
required beyond a documentation comment noting that the
workspace coverage now includes the host runtime.

#### RH-H.10 — Documentation synchronisation

The following documents are updated in the same PR as the code:

1. `README.md` — workspace surface section, "Rust workspace
   crates" listing. Adds the `sele4n-host` entry.
2. `docs/spec/SELE4N_SPEC.md` — adds a sub-section under the
   appropriate workspace structure section describing the host
   runtime's role and TCB-non-membership.
3. `docs/CLAIM_EVIDENCE_INDEX.md` — adds a row for WS-RH RH-H
   citing the workspace member, integration test, CI script,
   and CI workflow file.
4. `docs/WORKSTREAM_HISTORY.md` — adds a new WS-RH portfolio
   entry with the RH-H closure detail and the RH-A..RH-G
   forward-look.
5. `CHANGELOG.md` — adds a v0.31.4 entry describing the new
   crate and the CI harness updates.
6. `CLAUDE.md` "Active workstream context" — adds a paragraph
   for WS-RH RH-H closure; older WS-SM SM0 prose stays.
7. `AGENTS.md` — mirrors `CLAUDE.md` (the two files must remain
   byte-identical apart from the header).
8. `scripts/website_link_manifest.txt` — adds the new
   `rust/sele4n-host/` directory, the `Cargo.toml`, the
   `src/lib.rs`, and the four module sources (the integration
   test file is **not** added because tests are not website
   link targets).

### 2.5 Gate / validation

Phase closure requires:

| Gate | Command | Passes when |
|---|---|---|
| Workspace build | `cd rust && cargo build --workspace` | exit 0, zero warnings |
| Workspace tests | `cd rust && cargo test --workspace` | exit 0, every test passes |
| Lean Tier 0 hygiene | `./scripts/test_tier0_hygiene.sh` | exit 0 |
| Lean Tier 1 build  | `./scripts/test_tier1_build.sh`   | exit 0 |
| Lean Tier 2 smoke  | `./scripts/test_smoke.sh`         | exit 0 |
| Website link check | `./scripts/check_website_links.sh` | exit 0 |
| Doc sync | `./scripts/test_docs_sync.sh` | exit 0 |
| Rust ABI gate | `./scripts/test_rust.sh` | exit 0, new integration step passes |

The Lean gates run because RH-H adds the new website link entries
that the Tier 0 hygiene gate verifies; the doc sync gate ensures
the README/spec/claim-index updates stay aligned with the
codebase map.

### 2.6 Risk register

| Risk | Severity | Mitigation |
|---|---|---|
| Workspace member ordering causes a non-deterministic build graph | Low | The workspace's `resolver = "2"` defines a deterministic build order regardless of `members` array ordering. |
| `std` feature on `sele4n-types` / `sele4n-abi` accidentally enables in the kernel's `no_std` build | Low | The kernel build is performed via `sele4n-hal` which does **not** depend on `sele4n-host` and does **not** propagate the `std` feature. Cargo features are additive but path-isolated to consumers. |
| New crate triggers a workspace-wide rebuild on every PR | Negligible | Cargo's incremental cache keys are per-crate; only the host crate rebuilds when its sources change. |
| Documentation drift between WS-RH plan and the README/spec | Low | The `test_docs_sync.sh` gate runs in CI and flags inconsistency; manual sync is performed in the same PR as the code. |
| The host crate accidentally encodes a kernel-internal type that the kernel TCB now depends on (TCB inflation) | Low | The kernel binary is built from `sele4n-hal` (kernel-side), which has zero dependencies on `sele4n-host`. The workspace dependency graph statically enforces TCB non-inflation. |

### 2.7 Commit-message scaffolding

The RH-H landing commit message uses the structured scaffold:

```
rh-h: WS-RH Phase RH-H closure (Rust host runtime workspace + CI harness)

Adds `sele4n-host`, a host-side Rust runtime crate, to the rust/
workspace as the foundation for the WS-RH portfolio. Scaffolds
four modules (runtime, dispatch, state, fixture) with documented
public APIs, an integration test suite covering every public
item, and CI hooks that exercise the new crate on every PR.

Refs: docs/planning/rust_host_runtime_plan.md §2 (RH-H)
```

(The session-URL footer is omitted per CLAUDE.md "Session URL
hygiene".)

## 3. RH-A..RH-G — forward-look (sketch only)

These phases are sketched here for navigational continuity. Each
gets its own plan document when its predecessor closes.

- **RH-A — Runtime context type + boot wiring.** Populate the
  `HostRuntime` placeholder with a boot-sequence mirror that
  accepts a `PlatformConfig`-shaped fixture and produces a
  `HostState` ready for syscall dispatch. Cross-references the
  Lean `bootFromPlatformChecked` path.
- **RH-B — Register-file fixture + `SyscallRequest` host
  injection.** Replace the hand-built `SyscallRequest` literals
  in `sele4n-abi` conformance tests with declarative fixtures
  produced by the host crate's `FixtureBuilder`.
- **RH-C — `KernelError` decode path + host-side trap surface.**
  Provide a host-side facade for the `KernelError → UInt32 →
  UInt64` encoding contract; verify the decoder against the
  Lean kernel's encoder for every discriminant.
- **RH-D — IPC buffer fixtures + structured trace replay.** Add
  IPC-buffer encode/decode parity tests; thread the
  `arm64DefaultLayout`-encoded register sequence through the
  host crate and assert structural equality with the kernel's
  trace fixture.
- **RH-E — Capability fixture builder + W^X regression replay.**
  Extend the `FixtureBuilder` with capability-table builders;
  port the W^X-regression fixtures from
  `tests/WxDefenseSuite.lean` to host-runnable scaffolds.
- **RH-F — Cross-validation harness — Rust ↔ Lean register
  layout parity.** Add a property-test harness that generates
  random `SyscallRequest`s, encodes them with the Rust crate,
  decodes them with the Lean kernel (via `lake exe`), and
  asserts byte-for-byte parity on the encoded register file.
- **RH-G — Documentation, GitBook chapter, closure.** Write
  the GitBook chapter `30-rust-host-runtime.md`, close
  documentation cross-references, and produce the WS-RH
  closure summary.

## 4. Out of scope

The following are explicitly out of scope for WS-RH (any phase):

1. **Linking the host runtime into the kernel binary.** The host
   runtime is host-side only; it must remain `std` and must not
   ever appear in the kernel's `no_std` build graph.
2. **Hardware execution.** The host runtime never traps to the
   kernel. It is a pure encode/decode/cross-validate harness.
3. **Networking, persistence, or anything beyond a local
   in-process test harness.** The supply-chain hygiene rule
   (CLAUDE.md "Third-party attribution") applies: every
   additional runtime dependency must be justified and
   attribution-correct.
4. **Replacing `sele4n-sys`.** The two crates are complementary:
   `sele4n-sys` is the guest-side TCB syscall facade;
   `sele4n-host` is the host-side test harness. They never
   merge.

## 5. Appendix — file index

Every file created or modified by RH-H:

| Path | Status |
|---|---|
| `docs/planning/rust_host_runtime_plan.md` | **new** (this file) |
| `rust/Cargo.toml` | edited (members list) |
| `rust/sele4n-host/Cargo.toml` | **new** |
| `rust/sele4n-host/src/lib.rs` | **new** |
| `rust/sele4n-host/src/runtime.rs` | **new** |
| `rust/sele4n-host/src/dispatch.rs` | **new** |
| `rust/sele4n-host/src/state.rs` | **new** |
| `rust/sele4n-host/src/fixture.rs` | **new** |
| `rust/sele4n-host/tests/scaffold.rs` | **new** |
| `scripts/test_rust.sh` | edited (new step) |
| `.github/workflows/lean_action_ci.yml` | edited (documentation comment) |
| `README.md` | edited (workspace surface) |
| `docs/spec/SELE4N_SPEC.md` | edited (host-runtime placement) |
| `docs/CLAIM_EVIDENCE_INDEX.md` | edited (WS-RH row) |
| `docs/WORKSTREAM_HISTORY.md` | edited (WS-RH entry) |
| `CHANGELOG.md` | edited (v0.31.4 entry) |
| `CLAUDE.md` | edited (active workstream block) |
| `AGENTS.md` | edited (mirror) |
| `scripts/website_link_manifest.txt` | edited (new paths) |
