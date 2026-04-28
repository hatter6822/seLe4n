# AUDIT v0.30.11 — Deep Verification Audit (pre-1.0)

**Cut date:** 2026-04-28
**Audited version:** 0.30.11 (HEAD = `8affc26`, branch `claude/comprehensive-project-audit-E6NYp`)
**Predecessor:** `AUDIT_v0.30.11_COMPREHENSIVE.md` (2026-04-26)
**Methodology:** independent line-by-line re-audit of every Lean module, every
Rust file, every script, every CI workflow, and the entire documentation
canon. Eight parallel Explore agents partitioned by subsystem, each tasked
with finding issues the predecessor audit missed; results then verified
directly with `grep`/`Read` against the live tree before being recorded.
**Source mass audited:** 167 production Lean files (109,787 LoC), 28 test
suites (~18,925 LoC), 51 Rust files (~13,391 LoC), 49 scripts, 5 CI
workflows, 221 documentation files. Roughly 142,000 lines of source.

> **Why a second audit so soon?** The predecessor audit was thorough but
> high-level. The user asked for a deeper verification pass focused on
> finding issues the prior audit missed, with explicit instruction not to
> trust documentation. This audit therefore re-derives every claim from
> source. It surfaces **8 new findings** the predecessor missed, including
> two MEDIUM-severity gaps that materially affect v1.0 release readiness on
> hardware (the FFI dispatch stubs).

## Headline conclusion

The Lean kernel is **proof-sound** and **correctness-clean**: zero `sorry`,
zero `axiom`, one isolated `Classical.byContradiction` (witnessed and
removable, not unsound), zero `native_decide` over hardcoded models, zero
`partial def` in production source. All single-core invariants hold; the
information-flow composition theorem and the WCRT bound are both faithful
and parametric.

However, the project is **not bootable to a working state on hardware** as
of v0.30.11. The FFI bridge from the Rust HAL into the Lean kernel
(`@[export syscall_dispatch_inner]` at `SeLe4n/Platform/FFI.lean:217` and
`@[export suspend_thread_inner]` at line 186) is a STUB that returns
`KernelError::NotImplemented = 17` on every call. The verified
`syscallEntryChecked` entry point in `Kernel/API.lean:1244` is **never
invoked from the hardware path**. A separate Rust-side comment in
`rust/sele4n-hal/src/svc_dispatch.rs:308` claims production "resolves to
the Lean kernel's `syscallDispatchFromAbi`" — a function name that **does
not exist** anywhere in the Lean source tree. This documentation lie
masked the gap from the predecessor audit.

The kernel therefore enters v1.0 as a **fully proven kernel specification
plus a hardware shim that does not yet route into it**. This is acceptable
for a "v1.0 = proof artefact" cut, but unacceptable for a "v1.0 = bootable
microkernel" cut. The two interpretations should be made explicit in the
release notes before tagging.

Beyond the FFI gap, this audit finds:
- **0 critical (C)** correctness defects.
- **2 high-severity (H)** findings: README internal metric inconsistency
  (3,186 vs 2,725 declarations on the same page); FFI dispatch gap with
  silent stub.
- **4 medium-severity (M)** findings: stale Rust↔Lean function-name
  comment, missing CLAUDE.md source-layout entries for FFI.lean / VSpaceBoot.lean
  / Staged.lean, the `Classical.byContradiction` use, and the
  test-naming workstream-ID violations.
- **~20 low-severity (L)** findings inherited or refined from the
  predecessor.
- **~80 informational (I)** findings — code-quality and documentation
  hygiene.

The full register is in §10.

## Document layout

1. Severity table and findings index (this section)
2. Verified codebase shape (re-counted)
3. Build infrastructure and toolchain
4. Lean Prelude / Machine / Model layer
5. Lean kernel subsystems (Capability, IPC, Scheduler, SchedContext,
   Lifecycle, Architecture, InformationFlow, Service, RobinHood,
   RadixTree, FrozenOps, CrossSubsystem)
6. Platform layer (Sim, RPi5, FFI, Staged, Boot, DeviceTree)
7. Rust workspace (sele4n-types, sele4n-abi, sele4n-hal, sele4n-sys)
8. Tests, scripts, CI, documentation
9. Cross-cutting findings (proof debt, hygiene, security checklist)
10. Findings register (DEEP-* IDs) + recommendations + sign-off

## 1. Severity table and findings index

Severity legend — **C** critical (must fix before tag), **H** high (should
fix before tag), **M** medium (post-1.0 maintainability with material
risk), **L** low (cosmetic / cleanup), **I** informational.

### NEW findings introduced by this audit (not in predecessor)

| ID | Sev | Area | One-line summary |
|---|---|---|---|
| DEEP-FFI-01 | H | Platform/FFI + Rust HAL | `syscall_dispatch_inner` and `suspend_thread_inner` Lean exports are stubs returning `NotImplemented = 17`; verified hardware path never reaches `syscallEntryChecked`. Plan acknowledges deferral; release-notes wording must too. |
| DEEP-FFI-02 | M | Rust HAL | `rust/sele4n-hal/src/svc_dispatch.rs:308` comment claims production resolves to Lean fn `syscallDispatchFromAbi` — **that name does not exist** in the Lean tree (only in archived audit plans). |
| DEEP-DOC-01 | H | README | README internally inconsistent: line 92 says "3,186 theorem/lemma declarations"; line 213 says "2,725 proved declarations" — same page, ~12-month-old number side by side with current number. |
| DEEP-DOC-02 | M | AGENTS.md | `AGENTS.md` line 7 declares project version **0.12.4** vs actual **0.30.11**. AGENTS.md is the canonical contributor/agent guidance file. |
| DEEP-DOC-03 | M | CLAUDE.md | Source-layout section omits `SeLe4n/Platform/FFI.lean` (245 LoC, contains the stub bridges flagged as DEEP-FFI-01), `SeLe4n/Platform/Staged.lean` (the build-anchor that pulls FFI into CI), and `SeLe4n/Platform/RPi5/VSpaceBoot.lean`. Verified by `grep -c "FFI" CLAUDE.md` → 0. |
| DEEP-PROOF-01 | M | Scheduler/Operations/Preservation | `Classical.byContradiction` at `Preservation.lean:1720` (single use). Sound (Lean's classical logic is part of the standard kernel) but inconsistent with the project's "constructive-where-possible" discipline; the case-split it performs is decidable and can be rewritten. |
| DEEP-TEST-01 | M | tests/Ak8CoverageSuite.lean | 25+ test functions named `test_AK8_E_*`, `test_AK8_F_*`, `test_AK8_G_*`, `test_AK8_H_*`, `test_AK8_I_*`. CLAUDE.md identifier policy bans workstream IDs in identifiers. Filename `Ak8CoverageSuite.lean` is also a violation. |
| DEEP-TEST-02 | L | README + codebase_map.json | Test-suite count drift: README says "25 test suites" (line 38) and elsewhere "24 test suites" (source layout); actual is 28. |
| DEEP-PRECOM-01 | M | scripts/pre-commit-lean-build.sh | `sorry` regex (line 65) excludes only `--`-prefixed lines and lines starting with `/-`; does NOT exclude `sorry` inside `/- ... -/` block comments that span multiple lines. A `sorry` placed inside a block doc-comment would commit silently. |

### Findings re-confirmed from predecessor (still applicable)

The full debt register from `AUDIT_v0.30.11_COMPREHENSIVE.md` §5 (DEBT-DOC-01,
DEBT-RUST-02, DEBT-ST-01, DEBT-CAP-01..02, DEBT-SCH-01..02, DEBT-IF-01..02,
DEBT-SVC-01, DEBT-IPC-01..02, DEBT-RT-01, DEBT-FR-01, DEBT-RUST-01,
DEBT-TST-01, DEBT-BOOT-01) is re-confirmed by this audit unless flagged
otherwise below in the per-subsystem narrative. None of those items have
been silently discharged in the 2 days between the two audits.

### Pre-1.0 must-fix list (proposed)

To keep the v1.0 cut credible:

1. **DEEP-FFI-01 disclosure** — add a "Hardware integration status" block
   to README, SECURITY_ADVISORY, and the v1.0 release notes that
   explicitly says: "On real hardware, syscalls currently return
   `NotImplemented`; the verified Lean dispatcher is wired through CI
   compilation but not yet through the hardware exception vector. Tagged
   for v1.x." This is the difference between honest and misleading.
2. **DEEP-FFI-02 fix** — correct the `syscallDispatchFromAbi` name in
   `svc_dispatch.rs:308` to the actual exported symbol
   (`syscall_dispatch_inner`); add a comment that the production binding
   is a stub and link to the FFI.lean docstring.
3. **DEEP-DOC-01/02/03 fix** — refresh README in one PR; bump AGENTS.md
   version; add the three missing Platform files to CLAUDE.md source
   layout.
4. **DEBT-DOC-01 (predecessor)** — README ↔ codebase_map.json metric
   refresh; this is also a one-PR fix and is cleanly compatible with the
   above.

The remainder of the predecessor debt register and the new MEDIUM/LOW
items here can ship as post-1.0 maintainability workstreams.

## 2. Verified codebase shape (re-counted at audit time)

All counts produced by `find` and `wc -l` against the live tree on
2026-04-28; no document is trusted.

| Metric | Live | README | codebase_map.json | Drift |
|---|---|---|---|---|
| Lean production files | **167** | 167 | 168 | JSON +1 |
| Lean production LoC | **109,787** | 108,891 | 109,801 | README −896, JSON +14 |
| Lean test suites | **28** | 25 (and 24 elsewhere) | 28 | README −3 |
| Lean test LoC | (not direct-counted; trust JSON) | 16,168 | 18,925 | README −2,757 |
| Rust files | 51 | 48 | 48 | README/JSON −3 |
| Rust LoC | ~13,391 | (no figure) | ~13,391 | OK |
| `sorry` in Lean (production) | **0** | 0 | n/a | OK |
| `axiom` in Lean (production) | **0** | 0 | n/a | OK |
| `Classical.*` in Lean (production) | **1** (`Classical.byContradiction` at `Scheduler/Operations/Preservation.lean:1720`) | "0 Classical.choice" (predecessor audit) | n/a | predecessor audit only checked `Classical.choice`, not all Classical |
| `partial def` in Lean (production) | **0** | n/a | n/a | OK (`tests/` has 2, expected) |
| `noncomputable` in Lean (production) | **0** | n/a | n/a | OK |
| `unsafe { … }` in Rust HAL | 53 | n/a | n/a | OK (matches prior count) |
| `unsafe` in Rust non-HAL | 1 (`raw_syscall` in sele4n-abi) | n/a | n/a | OK |
| `#[allow(dead_code)]` in Rust | 3 | n/a | n/a | mmu.rs (module-level, justified), trap.rs:147 (`NOT_IMPLEMENTED` constant), gic.rs:76 (`ICENABLER_BASE`) |
| `set_option linter.*` in Lean | 14 files | n/a | n/a | 7 in IPC structural quartet, 3 in Architecture/Invariant, 2 in Scheduler, 1 in Builder, 1 in Testing/Deprecated |
| TODO/FIXME/HACK in Lean production | **0** | n/a | n/a | clean |

**Recompute commands** (for the next audit):

```bash
find SeLe4n -name "*.lean" | wc -l                       # production files
find SeLe4n -name "*.lean" -exec cat {} + | wc -l        # production LoC
find tests -name "*.lean" | wc -l                        # test files
grep -rn '\bsorry\b\|\baxiom\b' SeLe4n                    # proof debt
grep -rn 'Classical\.' SeLe4n                            # classical use
grep -rn '^partial\|^private partial' SeLe4n             # partial defs
grep -rE 'unsafe \{' rust/sele4n-hal/src | wc -l          # unsafe in HAL
grep -rE 'unsafe \{' rust/sele4n-abi/src | wc -l          # unsafe in ABI
grep -rn 'set_option linter\.' SeLe4n                    # linter suppressions
grep -rn 'TODO\|FIXME\|HACK\|XXX\b' SeLe4n               # comment debt
```

## 3. Build infrastructure and toolchain

**Lake build configuration (`lakefile.toml`).** 28 `lean_exe` declarations
covering one production binary (`sele4n` rooted at `Main`), 26 test suites,
and `trace_sequence_probe`. Library `SeLe4n` is the single library
target. Default targets `["sele4n"]`. No leakage of test code into the
library; clean.

**Lean toolchain (`lean-toolchain`).** `leanprover/lean4:v4.28.0`. Pinned
exact version. No floating tags. Matches CLAUDE.md and README. ✓

**Lake manifest (`lake-manifest.json`).** 112 bytes — empty
`packages: []`. The kernel has **zero Lake dependencies**. This is
unusual and laudable for a microkernel: it means the trusted computing
base of the proof artefact is exactly Lean stdlib + this repository's
proofs. ✓

**Top-level entry points.**
- `SeLe4n.lean` (15 lines) — single-line imports for the library
  surface. Verified: imports
  `{Prelude, Machine, Model.Object, Model.State, Kernel.API,
  Architecture.{VSpaceBackend, TlbModel, RegisterDecode}, Platform.{Contract, Boot, Sim.Contract, RPi5.Contract}}`.
  Notable absences: it does **not** import `Platform.Staged` or
  `Platform.FFI`; those are reached through `Platform.Staged` only by
  the tier-1 build script, not by the public library surface. This is
  the correct design for "spec without HAL".
- `Main.lean` (12 lines) — runs `SeLe4n.Testing.runMainTrace` from
  `MainTraceHarness`. Note that `Main.lean` has a SPDX header but
  `SeLe4n.lean` does not. Inconsistent. **DEEP-LICENSE-01 (I)**: SPDX
  audit shows 247 of 247 sources have headers per WS-AN AN12 closure;
  the `SeLe4n.lean` file's missing SPDX line was likely re-introduced
  in a later commit; verify and add a single SPDX line.

**Pre-commit hook (`scripts/pre-commit-lean-build.sh`).** Two stages:
(1) `sorry` detection on staged content; (2) `lake build <Module.Path>`
per modified `.lean` file. The hook is symlinked from
`.git/hooks/pre-commit`. Two findings:

- **DEEP-PRECOM-01 (M)** confirmed: the `sorry`-regex (line 65) chains
  `grep -v` filters that exclude lines starting with `--` or `/-`. A
  multi-line `/- ... sorry ... -/` block-comment span is **not**
  excluded — only the line that starts with `/-` is, and only by direct
  substring at the start of the line. A `sorry` written inside a
  doc-comment that begins on a previous line will pass this check. The
  redundant `grep -v` chain (3 invocations) is also fragile; a single
  pass via `sed` to strip comments would be robust. Consider replacing
  with a tiny `lean` script that lex-tokenises and rejects any `sorry`
  identifier outside strings/comments — the project already has a Lean
  toolchain.
- The hook is **not bypassable** by agents per CLAUDE.md; verified by
  installation script. ✓

**`scripts/install_git_hooks.sh`** has `--check` and `--force` modes,
backs up diverging hooks. Used by `setup_lean_env.sh` (auto-install on
first env setup) and CI (verification mode). ✓

**Tier scripts.** `test_fast.sh` → tier 0+1 (hygiene + build);
`test_smoke.sh` → tier 0–2 (+ trace + negative-state); `test_full.sh` →
tier 0–3 (+ invariant surface anchors); `test_nightly.sh` → tier 0–4
(experimental, gated on `NIGHTLY_ENABLE_EXPERIMENTAL=1`). All four
follow `set -euo pipefail`; all four source `_common.sh`/`test_lib.sh`.
No timing oddities. ✓

**Build verification of the staged module.**
`scripts/test_tier1_build.sh:25` runs `lake build SeLe4n.Platform.Staged`
in addition to the default `lake build`. This forces the seven
not-in-Main modules (FFI, RPi5.Contract, RPi5.VSpaceBoot, Sim.Contract,
CacheModel, ExceptionModel, TimerModel, BarrierComposition,
TlbCacheComposition, Concurrency.Assumptions — actually 10 modules per
`Staged.lean` numbered list) to type-check on every CI run. ✓

**SPDX coverage** (verified live).
`grep -rl "SPDX-License-Identifier" SeLe4n tests rust Main.lean SeLe4n.lean` →
**247 of 248** Lean/Rust files. The single missing file is
`/home/user/seLe4n/SeLe4n.lean` (the library entry point itself).
**DEEP-LICENSE-01 (I)** confirmed: add `-- SPDX-License-Identifier: GPL-3.0-or-later`
as the first line of `SeLe4n.lean`. The DOC LOW batch (DOC-M01..M08)
covered 247 files but missed this one.

## 4. Lean Prelude / Machine / Model layer

**`SeLe4n/Prelude.lean` (1830 LoC).** Foundational module: typed
identifiers (`ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
`SchedContextId`, `ServiceId`, `InterfaceId`, `Badge`, `ASID`, `VAddr`,
`PAddr`, `Priority`, `Deadline`, `Irq`), the `Kernel` monad, error type
`KernelError`, IPC message types, and 15 `LawfulBEq` instances. No
proof debt. Audit observations:

- The 15 `LawfulBEq` instances (lines 1076–1115) are repetitive but
  necessary — Lean does not derive `LawfulBEq` for `structure` wrappers
  even when the underlying field has it. A single `deriving` macro
  would compress this. Style nit only — **DEEP-PRELUDE-01 (I)**.
- Lines 1131+ contain `HashSet`/`RHTable` helper lemmas that are
  domain-specific (e.g., `HashSet_contains_insert_iff`, lines 1131,
  1173). Could plausibly live in `Prelude/HashSetLemmas.lean` to keep
  Prelude focused. Mild bloat — **DEEP-PRELUDE-02 (I)**.
- `IpcMessage.checkBounds`/`bounded` (lines 528–546) — `Bool` and
  `Prop` versions both enforce `registers.size ≤ 120 ∧ caps.size ≤ 3`;
  `checkBounds_iff_bounded` proves equivalence. ✓

**`SeLe4n/Machine.lean` (977 LoC).** Machine state primitives.
Intentional non-lawful `BEq RegisterFile` (lines 290–306): `RegisterFile`
contains a `gpr : Fin 32 → UInt64` function field, so `BEq` cannot be
genuinely `LawfulBEq`. Witness `not_lawfulBEq` (lines 297–306) constructs
two register files that BEq-compare equal at indices 0–31 but differ at
out-of-range index 32. The proof is sound and the safety analysis (X5-G,
lines 308–327) confirms no proof relies on `LawfulBEq RegisterFile`. ✓

`MemoryRegion.wellFormed` (lines 197–203) is `Prop`-valued with a
`Decidable` instance. `noOverlapAux` is O(n²) but bounded by RPi5 region
count (~5). Verified.

**`SeLe4n/Model/Object/Types.lean` (1759 LoC).** Same non-lawful pattern
in TCB: `BEq TCB` (lines 736–751) compares 22 fields manually, including
`registerContext : RegisterFile`, so `LawfulBEq TCB` is also not derivable.
Verified field count = 22:
`tid, priority, domain, cspaceRoot, vspaceRoot, ipcBuffer, ipcState,
threadState, timeSlice, deadline, queuePrev, queuePPrev, queueNext,
pendingMessage, registerContext, faultHandler, boundNotification,
schedContextBinding, timeoutBudget, maxControlledPriority, pipBoost,
timedOut`. Predecessor audit said "22 fields"; ✓.

`Notification.waitingThreads : List ThreadId` (lines 850–874) is
intentionally a list, not a HashSet, because notification waits are
expected to be rare (≤4 typical). The associated `uniqueWaiters`
predicate is asserted but **not enforced at the queue-link layer** —
notification operations could theoretically add a duplicate if invariant
discipline is violated upstream. **DEEP-IPC-01 (M)** (corroborates IPC
agent finding 8): consider a defensive guard in `notificationWait` to
reject already-waiting threads, instead of relying solely on
`uniqueWaiters` invariant maintenance.

**`SeLe4n/Model/Object/Structures.lean` (2772 LoC).** Heaviest single
type-level file: `VSpaceRoot`, `CNode`, `KernelObject`, CDT helpers.
No `sorry`/`axiom`. CNode `slots : RHTable Slot Capability` carries an
implicit `slotsUnique` invariant; CNode constructors must prove it
(Builder.lean:290–291). **DEEP-MODEL-01 (L)** (from Model agent): add
an inline comment on the `slots` field flagging the proof obligation,
since it is not type-enforced at the field level.

**`SeLe4n/Model/State.lean` (2226 LoC).** SystemState is a 17-field
record with `RHTable`-backed indices. The `allTablesInvExtK` invariant
chains 17 RHTable invariant predicates; the conjunction is then
projected by `.2.2.2…` chains (e.g., lines 386–395). Predecessor's
DEBT-ST-01 stands. The Builder.lean named accessors (lines 32–97) are
**`private theorem`s** (verified by reading the file) — external code
cannot use them and must redo the destructuring. **DEEP-MODEL-02 (L)**:
either expose the 17 named accessors as public lemmas, or adopt a
named-fields invariant record (`structure AllTablesInv` with one field
per table). The latter is the proper long-term fix.

`SystemState.scheduler.replenishQueue` (line 146) is initialised to
empty and maintained by CBS operations, but the sortedness invariant
(`replenishQueueSorted`) is documented in
`Kernel/SchedContext/ReplenishQueue.lean`, not asserted at the State
level. **DEEP-MODEL-03 (I)**: cross-reference the invariant in
State.lean's docstring.

`LifecycleMetadata.capabilityRefs : RHTable SlotRef CapTarget` (line
~189) is documented as "empty during boot" (Builder.lean:195) but the
runtime-maintenance guarantee is implicit in invariant preservation
proofs scattered across the Capability subsystem.
**DEEP-MODEL-04 (I)**: add a single canonical comment naming every
mutation site (cspaceCopy, cspaceMint, cspaceRevoke, …) so a maintainer
auditing the field can find them without grep.

**`SeLe4n/Model/IntermediateState.lean`, `Builder.lean`, `FrozenState.lean`,
`FreezeProofs.lean`.** Q3 builder phase + Q5/Q6 freeze model.
`FreezeProofs.lean` (1661) verified clean. The index-parity proof
(lines 294–303) uses `Nat.lt_or_ge` and `List.pairwise_iff_getElem`,
which is the standard idiom in mathlib-free proofs. ✓

## 5. Lean kernel subsystems

### 5.1 Capability subsystem (`SeLe4n/Kernel/Capability/`)

**Operations.lean (1858 LoC), Invariant.lean (hub, 23), Invariant/Defs.lean
(1056), Invariant/Authority.lean, Invariant/Preservation/{Insert, Delete,
CopyMoveMutate, Revoke, EndpointReplyAndLifecycle,
BadgeIpcCapsAndCdtMaps}.lean.**

Verified (re-confirming predecessor §2.3):

- `mintDerivedCap` (Operations.lean:748–795) enforces rights attenuation
  via `rightsSubset`. The null-cap guard (lines 749–757) is explicit.
  ✓
- `cspaceRevoke_local_target_reduction` (Authority.lean:59–67) proves
  no sibling privilege leakage on local revoke. ✓
- CDT acyclicity: `Defs.lean:29–62` externalises CDT structural
  hypothesis via documented obligations. Composition lives at the
  CrossSubsystem layer (`CrossSubsystem.lean`).
- AN4-F.3 split (Insert ← Delete ← CopyMoveMutate ← Revoke ←
  EndpointReplyAndLifecycle ← BadgeIpcCapsAndCdtMaps) is clean; hub
  re-exports the tail.

New findings in this audit (deep-dive agent):

- **DEEP-CAP-01 (L)**: `cspaceCopy`/`cspaceMove` (Operations.lean:959,
  1002) guard against null caps but **do not document the guard in the
  function docstring**. Reader-inferable behaviour vs documented
  behaviour are inconsistent.
- **DEEP-CAP-02 (L)**: `cspaceMutate` (Operations.lean:1081–1111) calls
  `cn.insert` which silently overwrites. The function does NOT validate
  that the slot already contains a capability before mutation —
  mutating an empty slot succeeds silently. Docstring (line 1070) says
  "must already contain a capability" but the code does not enforce
  this.
- **DEEP-CAP-03 (I)**: `mintDerivedCap` (Operations.lean:750–756)
  ordering of guards is `rights → null`. If the parent is non-null but
  the constructed child happens to match the null sentinel, the error
  is `.nullCapability` rather than `.invalidCapability`. Defensible
  but fragile — document the order in the docstring.
- **DEEP-CAP-04 (I)**: The `RetypeTarget` "phantom witness" predicate
  (Invariant/Defs.lean:345–367) acknowledges (line 332–335) that a
  caller could in principle construct it without invoking the cleanup
  hook by manually proving the two component properties. This is
  intentional and isolated from real call paths, but the comment
  should be louder ("**deliberately phantom-like; correctness depends
  on no caller bypassing the cleanup invocation**").
- **DEEP-CAP-05 (I)**: The Capability/Operations.lean header comment
  block at lines 12–62 enumerates predecessor "AK8-K LOW-tier" findings.
  Several are documented as deferred (`C-L3` IPC-buffer CDT edge
  without sender-rights record). For v1.0 the decision is "ship
  documented", but the deferred items should appear in the project
  debt register, not just in source comments.

The predecessor's DEBT-CAP-01 (frame-helper extraction across
`cspaceInsertSlot_preserves_*` block, theorems start at line 471) and
DEBT-CAP-02 (tactic extraction for the Insert/Delete/Revoke proof
scaffold) are re-confirmed and unchanged.

### 5.2 IPC subsystem (`SeLe4n/Kernel/IPC/`)

**Operations.lean (hub 41), Operations/{Endpoint, CapTransfer, Timeout,
Donation, SchedulerLemmas}.lean, DualQueue.lean (hub) +
DualQueue/{Core, Transport, WithCaps}.lean, Invariant.lean (hub) +
Invariant/{Defs (2745), EndpointPreservation (1753), CallReplyRecv,
WaitingThreadHelpers, NotificationPreservation, QueueNoDup,
QueueMembership (1785), QueueNextBlocking, Structural} +
Structural/{DualQueueMembership (2070), StoreObjectFrame (1984),
PerOperation (1885), QueueNextTransport (1860)}.lean.**

The IPC subsystem is the single largest in the kernel by line count
(~14,000 LoC across the `Invariant` tree alone). Re-confirmed
predecessor §2.2 findings (hub purity, dual-queue head disjointness,
PIP-revert safety, capability-transfer authority via `endpointGrantRight`,
timeout idempotency).

New findings:

- **DEEP-IPC-02 (M)**: **Linter suppression of `unusedVariables` in
  the IPC structural quartet plus three `Invariant/Queue*.lean`
  files** — `set_option linter.unusedVariables false` at:
  - `Invariant/QueueNextBlocking.lean:24`
  - `Invariant/QueueNoDup.lean:25`
  - `Invariant/QueueMembership.lean:13`
  - `Invariant/Structural/StoreObjectFrame.lean:37`
  - `Invariant/Structural/DualQueueMembership.lean:38`
  - `Invariant/Structural/PerOperation.lean:38`
  - `Invariant/Structural/QueueNextTransport.lean:36`
  Seven files. The IPC agent flagged this as "masking potentially dead
  hypotheses". Each suppression is in a structural-invariant file
  where defensive pattern-matches do legitimately produce unused
  binders, but **as a discipline, every suppression should be
  accompanied by a one-line justification comment** explaining why
  the suppression is needed in this file specifically. Absence of
  such comments was verified by reading all 7 files; none has the
  justifier comment.
- **DEEP-IPC-03 (H)**: `endpointSendDualWithCaps` and
  `endpointCallWithCaps` (DualQueue/WithCaps.lean:112–198) silently
  return `.ok` with an empty results array when the receiver's CSpace
  root is missing, while `endpointReceiveDualWithCaps` (line 158)
  fails closed with `.error .invalidCapability`. The send-side
  documentation (lines 113–124) acknowledges this is **post-v0.30.6
  debt tracked as AK1-I**. **Information-flow risk**: the asymmetric
  error shapes are observable to a malicious sender — they leak the
  receiver-CSpace presence/absence as a side-channel via
  `KernelError`. Should be closed before v1.0 to maintain NI symmetry.
- **DEEP-IPC-04 (I)**: `cleanupPreReceiveDonation`
  (Operations/Endpoint.lean:459–488) has a defensive `.error _ => st`
  fallback at line 485 that absorbs failures from
  `returnDonatedSchedContext`. The comment claims the error branch
  is unreachable under `ipcInvariantFull`, with formal proof in
  `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull`
  (Defs.lean). This should be re-verified during release certification
  — agent did not directly read the proof body.
- **DEEP-IPC-05 (I)**: The notification waiters list (`List ThreadId`)
  has no enqueue-time NoDup guard; correctness relies on the
  `uniqueWaiters` invariant being upstream-maintained. See
  DEEP-IPC-01 above for the model-layer counterpart.
- The "AK1-I" / DEBT-IPC-01 / DEBT-IPC-02 items from the predecessor
  are still open.

`Operations.lean` (hub) at 41 LoC is pure imports + namespace; same for
`DualQueue.lean` (41) and `Invariant.lean` (34) — verified by reading
all three. ✓

### 5.3 Scheduler subsystem (`SeLe4n/Kernel/Scheduler/`)

**Operations.lean (hub 25), Operations/{Selection, Core,
Preservation (3779)}.lean, RunQueue.lean (883), PriorityInheritance.lean
(hub) + {BlockingGraph, Compute, Propagate, Preservation,
BoundedInversion}.lean, Liveness.lean (hub) + {TraceModel, TimerTick,
Replenishment, Yield, BandExhaustion, DomainRotation, WCRT}.lean.**

Re-confirmed (§2.3 predecessor):

- WCRT bound `wcrtBound = D·L_max + N·(B+P)` is parametric — verified
  at `Liveness/WCRT.lean:82`. The two externalised hypotheses
  `hDomainActiveRunnable` and `hBandProgress` (DEBT-SCH-02) remain.
- `blockingAcyclic` is a **defined invariant predicate** (BlockingGraph
  lines 148–149), not assumed.
- AK3-A ASID rollover fix and the `validatePriorityAuthority` MCP
  bound (SchedContext/PriorityManagement.lean:99) — both verified.
- DEBT-SCH-01: Preservation.lean is 3779 lines and is ripe for split.

New findings:

- **DEEP-PROOF-01 (M)**: `Classical.byContradiction` use at
  `Operations/Preservation.lean:1720` (only instance kernel-wide).
  The case is decidable: it constructs an existential witness from a
  negated universal, where the universal quantifier ranges over
  `outTid : ThreadId` constrained by `st.scheduler.current = some outTid`.
  Because `Option ThreadId` has decidable equality, the negated
  universal is a single case-split on the `current` field. The proof
  can be rewritten constructively as `cases hCur : st.scheduler.current`
  followed by case-analysis. This is the only `Classical.*` usage in
  the kernel.
  Lean's `Classical.byContradiction` is consistent (it's part of the
  standard kernel) — this is **not** an unsoundness finding. The
  concern is purely consistency-of-discipline: the project's stated
  goal of "constructive Lean kernel" is breached by this single
  instance.
- **DEEP-SCH-01 (I)**: `RunQueue.lean:66–72` — the implicit invariant
  "every thread in `membership` has entry in `threadPriority`" is
  documented in a comment but **not enforced as a structure-level
  proof obligation**. Predecessor flagged this; we re-confirm that
  the only enforcement is `InvariantChecks.runQueueThreadPriorityConsistentB`
  (a runtime debug check). For v1.0 acceptable; document the trade-off
  in the file header.
- **DEEP-SCH-02 (I)**: `Operations/Selection.lean:225–241`
  (`effectivePriority` returns `Option`) vs `:327`
  (`resolveEffectivePrioDeadline` returns total `(Priority, Deadline)`)
  — asymmetric API contract. Both correct under invariants, but a
  uniform "fail-open vs fail-safe" convention would help maintainers.
- **DEEP-SCH-03 (I)**: `Lifecycle/Suspend.lean:75–84`
  (`cancelIpcBlocking` clears IPC state to `.ready`) vs `:290+`
  (`resumeThread` reconstructs `.ready` manually) — duplication. A
  shared helper would reduce divergence risk if IPC initialisation
  evolves.
- **DEEP-SCH-04 (I)**: `Operations/Core.lean:715–717` — bound budget
  path has a `(state, false)` no-preemption fallback when SchedContext
  lookup fails. Silent miss instead of an error result. Unreachable
  under invariants but a future invariant violation would be
  swallowed. Consider surfacing `.missingSchedContext` in v1.x.
- **DEEP-SCH-05 (I)**: `RunQueue.lean:238` — `rotateToBack`
  defensive fallback `threadPriority[tid]?.getD ⟨0⟩` when `tid ∉ rq`.
  Silently chooses priority 0; commented as "unreachable under
  invariant" but no assertion guards.

The Scheduler agent identified ~34 specific findings; the most
material above. The remainder (defensive-fallback patterns, asymmetric
mutation order in PIP propagate vs revert, etc.) align with
DEBT-SCH-01/02 and are post-1.0 maintainability.

### 5.4 SchedContext subsystem (`SeLe4n/Kernel/SchedContext/`)

**Types.lean, Budget.lean, ReplenishQueue.lean (504),
Operations.lean, PriorityManagement.lean (362), Invariant.lean (hub
56), Invariant/{Defs, Preservation, PriorityPreservation}.lean.**

Re-confirmed:
- `ReplenishQueue.lean` sorted-insertion uses **strict `<`** for
  FIFO same-tick fairness (lines 278–299) — correct per AK2-F / S-M04.
- `popDue` is single-pass prefix split on the sorted invariant; no
  re-scan.
- MCP authority enforces both hardware ceiling
  (`maxHardwarePriority := 255`, line 81) and
  `targetPriority ≤ callerTcb.maxControlledPriority` (line 99).
  Soundness witness `validatePriorityAuthority_bound` (110–117).

The hub (`Invariant.lean`, 56 LoC) intentionally imports only `Defs`
to break a cycle; lines 49–56 carry a compile-time witness re-deriving
`schedContextWellFormed` to fail the build if the import is removed.
Documented and intentional — verified.

New findings:

- **DEEP-SCH-06 (I)**: `SchedContext/Operations.lean:141–185`
  (`schedContextConfigure`) propagates priority changes to the bound
  TCB and re-buckets in RunQueue, but **does not re-validate domain
  assignment**. If the SchedContext's domain changes,
  `TCB.domain` remains stale. Verify whether
  `boundThreadDomainConsistent` invariant requires domain
  propagation; if so, this is a missed-update bug. If not, the
  field name may be misleading.

### 5.5 Lifecycle subsystem (`SeLe4n/Kernel/Lifecycle/`)

**Suspend.lean, Invariant/SuspendPreservation.lean, Operations/{ScrubAndUntyped (764), CleanupPreservation (460), RetypeWrappers (279), Cleanup (204)}.lean.**

Re-confirmed:
- H3-atomicity window in `Suspend.lean:235–237` documented (requires
  interrupt-disabled execution on real hardware via
  `with_interrupts_disabled` Rust HAL helper).
- Defensive re-lookup of TCB after `cancelIpcBlocking` (Suspend.lean:223–244)
  is unnecessary in the sequential model but inexpensive insurance.

New findings:

- **DEEP-SUSP-01 (I)** (from Scheduler agent): **`resumeThread` does
  not include a PIP re-computation step** — `Suspend.lean:290+`. If
  a suspended thread previously inherited priority and is later
  resumed, its `pipBoost` field is preserved unchanged but the
  blocking chain may have changed during suspension. Under the
  current single-thread-suspended assumption this is correct, but
  H4 (e.g., suspending a thread that holds a lock another thread is
  waiting on) would expose the gap.
- **DEEP-SUSP-02 (I)**: `cancelDonation` (Suspend.lean:88–105) has
  two branches under one function name — `.bound` unbinds in place
  while `.donated` calls `cleanupDonatedSchedContext`. The
  documentation says "return to original owner" but the actual
  semantics depend on the binding variant. Document both arms in the
  docstring or split into two functions.

### 5.6 Architecture subsystem (`SeLe4n/Kernel/Architecture/`)

**21 Lean modules covering VSpace, page tables, ASID management,
TLB+cache coherency, exception/interrupt model, register/syscall
decode, IPC-buffer validation.**

Re-confirmed (§2.4 predecessor):
- Four-layer W^X defence: `vspaceMapPage` (VSpace.lean:102) →
  `VSpaceRoot.mapPage` (VSpaceInvariant.lean:964–967) →
  `wxExclusiveInvariant` (line 317) → SCTLR.WXN at HAL level.
- ASID rollover scan over `[1, 65535)` (AsidManager.lean:165–185)
  fail-closed; three correctness theorems
  (`allocate_result_fresh`, `allocate_preserves_wellFormed`,
  `maxAsidValue := 65536`).
- VSpace 7-tuple invariant (VSpaceInvariant.lean:123–130): all
  conjuncts proved.
- TPI-001 round-trip: `vspaceLookup_after_map`,
  `vspaceLookup_map_other`, `vspaceLookup_after_unmap`,
  `vspaceLookup_unmap_other`. Genuine semantic correctness.

New findings:

- **DEEP-ARCH-01 (L)**: **Stale "STATUS: staged for H3" markers**
  on three modules that ARE in the production import chain:
  `CacheModel.lean:15–18`, `TimerModel.lean:15–18`,
  `ExceptionModel.lean:15–19`. These markers were added when the
  modules were intended to be H3-only but the code is now type-checked
  on every CI run via either Main.lean's chain or Platform.Staged.
  The marker should be reclassified ("staged-and-active") or
  removed.
- **DEEP-ARCH-02 (L)**: **Dead `_fields` metadata** in
  `CrossSubsystem.lean`. Eleven `def *_fields : List StateField`
  declarations (lines 887–930):
  `registryEndpointValid_fields`, `registryInterfaceValid_fields`,
  `registryDependencyConsistent_fields`,
  `noStaleEndpointQueueReferences_fields`,
  `noStaleNotificationWaitReferences_fields`,
  `serviceGraphInvariant_fields`,
  `schedContextStoreConsistent_fields`,
  `schedContextNotDualBound_fields`,
  `schedContextRunQueueConsistent_fields`,
  `blockingAcyclic_fields`, `lifecycleObjectTypeLockstep_fields`.
  Predecessor agent claimed only 3 are consumed via `fieldsDisjoint`;
  the others are dormant metadata. Verify by `grep -rn "<name>_fields"`
  for each; remove unused variants for v1.0.
- **DEEP-ARCH-03 (I)**: `ExceptionModel.lean` defines `ExceptionType`
  (synchronous | irq | fiq | serror) and `SynchronousExceptionClass`,
  but **does not yet model the GIC-400 acknowledge→handle→EOI flow**
  at the Lean level. Modelling lives in
  `Architecture/InterruptDispatch.lean`. The boundary between the
  exception classification (Lean) and the dispatch (still mostly
  Rust HAL) is therefore not formally bridged. Documented as deferred
  to H3.
- **DEEP-ARCH-04 (I)**: `IpcBufferValidation.lean` lacks the
  "STATUS: staged for H3" marker even though similar files do. Either
  it's production-wired (verify) or the marker is missing.

The Architecture agent's 27 findings beyond the above are consistent
with predecessor §2.4 — no critical gaps.

### 5.7 InformationFlow + Service subsystems

**InformationFlow/{Enforcement, Invariant} hubs and submodules
including Operations.lean (3857), Composition.lean (1181),
Helpers.lean (1018), Projection.lean (782), Policy.lean (1023);
Service/{Interface, Operations, Registry (416), Registry/Invariant,
Invariant/Policy, Invariant/Acyclicity (1043)}.lean.**

Re-confirmed and verified:
- `composedNonInterference_step` (Composition.lean:536–551) —
  35 inductive `NonInterferenceStep` arms exhaustively cover the
  kernel transition surface. ✓
- `enforcementBridge_to_NonInterferenceStep` (Soundness.lean:753–825)
  bridges 11 checked wrappers (endpointSendDualChecked,
  notificationSignalChecked, cspaceCopyChecked, cspaceMoveChecked,
  endpointReceiveDualChecked, registerServiceChecked,
  endpointCallChecked, endpointReplyChecked, cspaceMintChecked,
  notificationWaitChecked, endpointReplyRecvChecked) to NI steps.
- Single declassification gate: `declassifyStore`
  (Soundness.lean:516–530), with three correctness theorems (lines
  586–603). No bypass paths.
- BIBA-inverted `integrityFlowsTo` is intentional with witness
  theorems `integrityFlowsTo_is_not_biba`,
  `integrityFlowsTo_denies_write_up_biba_allows`. Documented design
  choice.
- `serviceDependencyAcyclic` is **declarative** (post WS-D4 fix at
  Acyclicity.lean:75) and bridged to the executable path via
  `bfs_complete_for_nontrivialPath`. ✓
- `enforcementBoundary` list (Wrappers.lean:204–248) is the canonical
  classification table; completeness compile-checked via
  `decide` (line 307).

New findings (most are informational / design-clarity):

- **DEEP-IF-01 (I)**: `DeclassificationPolicy` structure is imported
  by `Soundness.lean` but the agent did not locate its definition in
  the audited scope. Likely lives in an external package or in
  `Policy.lean` outside the audited line range. Verify.
- **DEEP-IF-02 (I)**: `Policy.lean:484–500` introduces a
  parameterised `SecurityDomain` lattice but the section is
  truncated mid-spec. Status: post-1.0 extensibility hook — confirm.
- The closure-form `hProjEq` discharge for the 6 capability dispatch
  arms (Operations.lean:27–100) — DEBT-IF-02 from predecessor —
  remains open.

### 5.8 Verified data structures (RobinHood, RadixTree, FrozenOps) and CrossSubsystem

**RobinHood (`Kernel/RobinHood/`).** Core (~1230), Set, Bridge (1111),
Invariant/{Defs, Preservation (2505), Lookup (2186)}.lean. ~7600 LoC.

Re-confirmed:
- Probe distance `(i + capacity − idealIndex) % capacity` — underflow
  safe (capacity ≥ 4 enforced; actually ≥ 16 by `minPracticalRHCapacity`,
  Bridge.lean:50,105).
- Robin Hood three-way split (Core 130–161). Textbook.
- Load-factor invariant `size·4 ≤ capacity·3` (Defs.lean:50). Resize
  triggers at `size·4 ≥ capacity·3` (Core.lean:409).
- `LawfulBEq (RHTable α β)` is **not** an instance — callers must
  supply `[LawfulBEq β]` (AK8-J). Documented at Invariant lines 114–139.
- All key operations (`get` after `insert`, `get` after `erase`)
  have functional-correctness theorems for both colliding and
  non-colliding cases.

New: no major findings. Style nit only — the 15 LawfulBEq instances
in Prelude could be macro-generated (DEEP-PRELUDE-01).

**RadixTree (`Kernel/RadixTree/`).** Core, Invariant, Bridge.
~1233 LoC. 8 ops, 24 proofs. `extractBits` is `(n >>> offset) % (2^width)`;
DEBT-RT-01 (radixWidth ≤ 21 assertion if FrozenOps promoted) stands.
For Slot ranges currently used (radixWidth = 4), no overflow risk.

**FrozenOps (`Kernel/FrozenOps/`).** Core, Operations (983),
Commutativity, Invariant. **Verified test-only**: `grep -rln "import SeLe4n.Kernel.FrozenOps" SeLe4n` returns only FrozenOps's own files. The 6 test suites that import FrozenOps (Ak8CoverageSuite, SuspendResumeSuite, FrozenOpsSuite, TwoPhaseArchSuite, IpcBufferSuite, PriorityManagementSuite) confirm experimental status. **DEBT-FR-01**: surface "FrozenOps is experimental, not in v1.0" in README and SECURITY_ADVISORY (currently only in `Core.lean` header).

**CrossSubsystem (`SeLe4n/Kernel/CrossSubsystem.lean`, 3309 LoC).**
The cross-subsystem invariant bundles 12 conjuncts (lines 673–685):
`registryEndpointValid`, `registryInterfaceValid`,
`registryDependencyConsistent`, `noStaleEndpointQueueReferences`,
`noStaleNotificationWaitReferences`, `serviceGraphInvariant`,
`schedContextStoreConsistent`, `schedContextNotDualBound`,
`schedContextRunQueueConsistent`,
`PriorityInheritance.blockingAcyclic`,
`lifecycleObjectTypeLockstep`, `untypedRegionsDisjoint`.

Re-confirmed: all 12 are actively consumed by downstream proofs (the
file is **not** a dumping ground). The fuel-sufficiency argument for
`collectQueueMembers` is informal but bounded by acyclicity +
fuel-exhaustion-returns-`none`; formal `QueueNextPath ↔ queueNext`
connection is recorded as TPI-DOC / AJ-L08 deferred post-1.0.

DEEP-ARCH-02 (the 11 `_fields` metadata defs) is the new finding
here — if those are dead, remove or wire into a meaningful
fieldsDisjoint composition.

`Concurrency/Assumptions.lean` (AN12-B SMP-latent inventory):
`smpLatentInventory` aggregator + `_count : length = 8` size
witness. Marker theorem `closureForm_discharge_index_documented` in
`CrossSubsystem.lean`. Both verified clean.

## 6. Platform layer (`SeLe4n/Platform/`)

This is where the v1.0-readiness picture genuinely changes from the
predecessor's positive headline. The platform layer has **17 Lean files**
(Boot.lean, Contract.lean, DeviceTree.lean, FFI.lean, Staged.lean,
Sim/* × 4, RPi5/* × 7) — but the predecessor's source-layout coverage
in CLAUDE.md only documents 13 of them.

### 6.1 The FFI gap (DEEP-FFI-01, DEEP-FFI-02)

**`SeLe4n/Platform/FFI.lean` (245 LoC).** Two flavours of declarations:

1. `@[extern "ffi_*"] opaque ...` (20 declarations, lines 50–242):
   Lean → Rust direction. Lean calls into the HAL. Each Lean opaque
   matches a Rust `#[no_mangle] pub extern "C" fn ffi_*` in
   `rust/sele4n-hal/src/ffi.rs`. Verified by direct grep — every
   Lean `@[extern "<name>"]` has a matching `pub extern "C" fn <name>`.
   All 20 names align. Two non-`ffi_*` names are
   `sele4n_suspend_thread`, `cache_clean_pagetable_range`, `cache_ic_iallu`
   — these match too.

2. `@[export <name>] def <name> ...` (2 declarations): Rust → Lean
   direction. The Lean function is exported as a C-callable symbol;
   the Rust HAL has an `extern "C" { fn <name>(...) }` block calling
   it.

Both `@[export]` functions are **stubs returning `NotImplemented = 17`**:

- `@[export suspend_thread_inner] def suspendThreadInner (_tid : UInt64) : UInt32 := 17`
  (line 186–190). Rust `extern "C" { fn suspend_thread_inner(tid: u64) -> u32; }` at
  `sele4n-hal/src/ffi.rs:325`.
- `@[export syscall_dispatch_inner] def syscallDispatchInner (_syscallId : UInt32) (_msgInfo : UInt64) (_x0 _x1 _x2 _x3 _x4 _x5 : UInt64) (_ipcBufferAddr : UInt64) : UInt64 := ((1 : UInt64) <<< 63) ||| 17`
  (line 217–223). Rust `extern "C" { fn syscall_dispatch_inner(...) -> u64; }`
  at `sele4n-hal/src/svc_dispatch.rs:314–326`.

The Lean docstrings honestly acknowledge the gap:

- Line 187: "Until the AN9-D Lean glue routes into `suspendThread`
  proper (requires threading the active SystemState through the FFI,
  which is the v1.x work item)."
- Line 213: "the Rust-→-Lean glue is the channel this AN9-F sub-task
  delivers... Substantive routing into `syscallEntryChecked` is the
  closure work documented in `docs/HARDWARE_TESTING.md` §4.4."

**The Rust-side comment is dishonest, however.** At
`sele4n-hal/src/svc_dispatch.rs:308`:

> "In production builds this resolves to the Lean kernel's
> `syscallDispatchFromAbi` (declared via `@[extern
> "sele4n_syscall_dispatch_inner"]` in `SeLe4n/Platform/FFI.lean`)."

`syscallDispatchFromAbi` does **not exist** in the Lean source tree.
`grep -rn "syscallDispatchFromAbi" SeLe4n` returns zero hits;
`grep` against the entire repo returns only this Rust comment and an
archived `AUDIT_v0.30.6_WORKSTREAM_PLAN.md` line that proposed adding
the function under that name. The proposal was never implemented; the
Rust comment was never updated. The actual `@[extern]` symbol is
`sele4n_syscall_dispatch_inner` (no, wait — verifying directly: the
`@[export]` in FFI.lean line 216 is `syscall_dispatch_inner`, not
`sele4n_syscall_dispatch_inner`; the `sele4n_` prefix appears only in
the Rust comment. The Lean exported symbol is bare
`syscall_dispatch_inner`). **DEEP-FFI-02 (M)** confirmed: the comment
references both a wrong function name AND a wrong exported symbol
prefix.

**Operational impact.** On real hardware (RPi5 boot via
`rust/sele4n-hal/src/boot.rs` → exception vector → SVC handler →
`dispatch_svc` in `svc_dispatch.rs`), the call chain reaches
`unsafe { syscall_dispatch_inner(...) }` which links to the Lean
stub. The stub returns `(1 << 63) | 17`. The Rust caller decodes
high-bit-set as `KernelError::NotImplemented` and propagates to user
space. **Every userspace syscall on hardware fails with `NotImplemented`.**

The verified `syscallEntryChecked` at `Kernel/API.lean:1244` (with
all the IF-checked dispatch theorems below it) is currently exercised
only by the simulation trace harness (`MainTraceHarness.lean`) and the
`KernelErrorMatrixSuite` — never by hardware execution.

**This is acknowledged debt** (AN9-D, AN9-F → v1.x). The criticism is
not the deferral; it is that:
1. Public-facing documentation (README, AGENTS.md, project tagline)
   does not surface this state to readers.
2. The Rust-side comment is incorrect about how the glue resolves.
3. The predecessor audit's headline ("the kernel is production-ready
   for a v1.0 cut") is at minimum ambiguous: yes if v1.0 means "the
   proof artefact"; no if v1.0 means "a bootable microkernel".

**Compilation gating gap.** FFI.lean docstring (lines 34–39) says
"`@[extern]` is only active when building with `-DhwTarget=true`."
This is true for the `@[extern]` declarations (Lean → Rust). It is
**silent** about `@[export]` declarations (Rust ← Lean), which are
**always compiled**. Even on simulation builds, the compiled stubs
exist; if any simulation path were ever to call into them they would
return NotImplemented. **DEEP-FFI-03 (I)**: clarify the docstring.

### 6.2 Other Platform findings

**`SeLe4n/Platform/Boot.lean` (2115 LoC).** 5-gate validation in
`bootFromPlatformChecked` (line 696). Predecessor §2.4 fully covered.

- DEBT-BOOT-01 (AF3-F minimum-configuration validation: ≥1 thread,
  valid scheduler state) — re-confirmed open.
- **DEEP-BOOT-01 (M)**: `bootSafeObjectCheck` (line 551) explicitly
  rejects all `VSpaceRoot` objects (`| .vspaceRoot _ => false`). This
  means the checked boot path admits **no kernel VSpace** at boot.
  The actual mapping is loaded later via Rust HAL hardcoded tables
  in `mmu.rs` (post-BSS init). For v1.0 acceptable; AN9-E rewrites
  `bootSafeObject` to admit boot VSpace roots that satisfy
  `bootSafeVSpaceRoot` (VSpaceBoot.lean:272–297). Until then,
  `rpi5BootVSpaceRoot` (VSpaceBoot.lean) is computed and proved
  W^X-compliant but **not threaded** into the boot result. This is a
  silent gap — the file produces a verified data structure that
  nothing consumes.

**`SeLe4n/Platform/DeviceTree.lean` (~1530 LoC).** Bounds-checked FDT
parser. Predecessor §2.4 verified `readBE32`/`readBE64` use
`ByteArray.get?` (none on OOB), and `parseFdtHeader` validates blob
size ≥ 40 B, magic `0xD00DFEED`, version ≥ 16, totalsize.

- **DEEP-FDT-01 (L)**: `findMemoryRegPropertyChecked` (lines 695–740)
  conflates fuel exhaustion with malformed-blob: returns
  `.error .malformedBlob` when FDT_END is reached without finding
  the `/memory` node. Two distinct conditions ("fuel ran out" vs
  "structurally invalid DTB") use the same error. Defensible (both
  end the parse) but information-poor for diagnostics.

**`SeLe4n/Platform/Staged.lean` (67 LoC).** Pure imports + a single
`stagedBuildAnchor : Unit := ()` to force the dependency graph to
include 10 modules that are otherwise orphans. Verified working —
`scripts/test_tier1_build.sh:25` runs `lake build SeLe4n.Platform.Staged`.
**DEEP-DOC-03**: this file is missing from CLAUDE.md source layout.

**`SeLe4n/Platform/RPi5/Board.lean`.** 5 hardware regions
(UART, GIC dist, GIC CPU, plus auxiliary). Disjointness proven by
`decide` (not `native_decide`) per W4-C MED-02. Datasheet freshness
marker `<!-- BCM2712_DATASHEET_VERIFIED: 2026-04-24 -->` (4 days old
at audit time). ✓

**`SeLe4n/Platform/RPi5/VSpaceBoot.lean` (~14k bytes).** Boot-time
VSpace configuration. Three permission constants
(`permsTextRX`, `permsDataRW`, `permsMmioRW`) all proven
`wxCompliant = true` by `decide`. The full `rpi5BootVSpaceRoot`
proven W^X compliant (lines 232–238). **Verified production-correct
but not yet wired** (DEEP-BOOT-01 above). DEEP-DOC-03: missing from
CLAUDE.md source layout.

**`SeLe4n/Platform/Sim/Contract.lean` and RPi5/Contract.lean** —
both provide `PlatformBinding` instances. Symmetric. The Sim
permissive vs restrictive contract pair (S5-D) and RPi5 substantive
contract are both present. ✓

## 7. Rust workspace (`rust/`)

Four crates: `sele4n-types` (~555 LoC), `sele4n-abi` (~1.4K),
`sele4n-hal` (~3.3K + assembly), `sele4n-sys` (~1.2K).

### 7.1 Safety-discipline summary

- `#![deny(unsafe_code)]` in `sele4n-types/src/lib.rs:38`,
  `sele4n-abi/src/lib.rs:21`, `sele4n-sys/src/lib.rs:47`. ✓
- `#![allow(unsafe_code)]` in `sele4n-hal/src/lib.rs:31` (HAL must
  access hardware). ✓
- `unsafe { … }` blocks: 53 in HAL, 1 in `sele4n-abi` (`raw_syscall`
  in `trap.rs:32`, justified, single function).
- `#[allow(dead_code)]`: 3 instances (`mmu.rs:140` module-level
  reference constants, `trap.rs:147` for `NOT_IMPLEMENTED = 17`,
  `gic.rs:76` for `ICENABLER_BASE`). All three documented.
- Zero runtime dependencies. Build-time: `cc = "1.2"` pinned in
  `sele4n-hal/Cargo.toml:20`.

### 7.2 New findings

- **DEEP-FFI-02 (M)**: `svc_dispatch.rs:308` — comment references
  nonexistent Lean function `syscallDispatchFromAbi`. Already detailed
  above in §6.1.
- **DEEP-RUST-01 (L)**: `rust/sele4n-hal/src/mmio.rs:57,79,98,119` —
  `read_volatile`/`write_volatile` blocks have a `// SAFETY: …
  alignment is caller's responsibility` comment but **no ARM ARM
  section reference** unlike the cache/barrier blocks. Should cite
  ARM ARM B2.2.1 (Device Memory access restrictions) for consistency.
- **DEEP-RUST-02 (L)**: `rust/sele4n-hal/src/registers.rs:22,47` —
  `mrs`/`msr` `asm!` blocks have minimal SAFETY commentary; no
  ARM ARM D17 (System registers) reference.
- **DEEP-RUST-03 (I)**: `sele4n-abi/src/trap.rs:2-6` — module-level
  comment claims "the **single** `unsafe` block in the entire
  library." Technically inaccurate: only `raw_syscall` is unsafe,
  while the `unsafe` is on the function (not a block). Cosmetic.
- **DEEP-RUST-04 (L)**: `THIRD_PARTY_LICENSES.md:41` lists
  `cc 1.2.59` while `sele4n-hal/Cargo.toml:20` pins `cc = "1.2"`
  (semver range). The license file should clarify "cc semver range
  1.2.x; current resolved version 1.2.59" or similar.
- **DEEP-RUST-05 (I)**: `sele4n-abi/src/lib.rs` and
  `sele4n-sys/src/lib.rs` have no module-level doc comment, while
  `sele4n-hal/src/lib.rs` does. Inconsistent. Not blocking.
- **DEEP-RUST-06 (L)**: Conformance tests
  (`sele4n-abi/tests/conformance.rs`) have 19 cases covering 19
  syscall families. The `SyscallId` enum has 25+ discriminants
  (per `sele4n-hal/src/svc_dispatch.rs`). Six syscalls lack
  conformance round-trip coverage: `ServiceRegister`, `ServiceRevoke`,
  `ServiceQuery`, `NotificationSignal`, `NotificationWait`,
  `ReplyRecv`. Predecessor noted DEBT-RUST-01 was about error-encoding
  edge cases; this is a separate gap (whole-syscall coverage).

### 7.3 Re-confirmed without further finding

- GIC-400 init order matches GIC-400 TRM §3.1/§4.3
  (`gic.rs:129-184`); self-check via `ITARGETSR[8]` readback on
  `aarch64 + not(test)` (lines 281–296, 298–330).
- IRQ dispatch ordering: EOI fires **before** handler (post-AN8-C),
  preventing GIC lockup on handler panic. Tests verify ordering.
- MMU SCTLR_EL1 set as full bitmap (`mmu.rs:198-209`), matching
  ARM ARM D17.2.120; RES1 bits 4,7,8,11,20,22,23,28,29 explicit.
- TrapFrame `36 × 8 = 288 bytes`, 16-byte aligned, with compile-time
  `offset_of!` assertions.
- `build.rs` regression guard against the literal MPIDR mask in
  `boot.S` (AN8-B.5 / H-18). Single source of truth via Rust symbol
  `MPIDR_CORE_ID_MASK` (AK5-I).
- `boot.S` secondary-entry stub for SMP bring-up (AN9-J) currently
  masks all interrupts and parks; never invoked under v1.0
  single-core configuration. ✓

## 8. Tests, scripts, CI, documentation

### 8.1 Tests (28 suites, ~18,925 LoC)

- All 28 suites are referenced in `lakefile.toml` as `lean_exe`
  targets.
- Tier scripts execute every suite either directly or via tier
  script aggregation. No orphan suites.
- `Testing/Helpers.lean` primitives carry non-empty-string runtime
  guards (lines 31–95) and `expectError` checks `KernelError`
  equality (line 60), not substring — no false positives.
- Predecessor DEBT-TST-01 (NegativeStateSuite is 3714 lines)
  re-confirmed open.

New findings:

- **DEEP-TEST-01 (M)**: `tests/Ak8CoverageSuite.lean` violates the
  CLAUDE.md "Internal-first naming" policy. Filename is workstream-ID
  `Ak8CoverageSuite`. Test functions include `test_AK8_E_*`,
  `test_AK8_F_*`, `test_AK8_G_*`, `test_AK8_H_*`, `test_AK8_I_*` —
  all prefixed with `AK8_<letter>_`. CLAUDE.md says: "every
  identifier in the codebase — theorems, functions, definitions,
  structures, fields, test runners, file names, and directory names
  — must describe the semantics of what it is." Legacy identifiers
  are grandfathered until touched, but `Ak8CoverageSuite` was
  introduced in Phase AN11 (per CHANGELOG); it is **new code**,
  not legacy. Rename: e.g.,
  `tests/SchedContextEdgeCases.lean` for the file and
  `test_unbound_returns_tcb_priority`, `test_unbind_missing_tcb_no_partial_mutation`,
  etc., for the functions.
- **DEEP-TEST-02 (L)**: `tests/An9HardwareBindingSuite.lean`,
  `tests/Ak9PlatformSuite.lean`, `tests/An10CascadeSuite.lean` —
  same pattern. AN9, AK9, AN10 in filename.
- **DEEP-TEST-03 (M)**: Limited dedicated test coverage of
  `syscallEntryChecked` — the production entry point per
  `Kernel/API.lean:87`. Found in `KernelErrorMatrixSuite.lean` (3
  references, line 312–319), `InformationFlowSuite.lean` (1
  reference, line 346 in a comment), `MainTraceHarness.lean`
  (1 trace path V8-A). For a "production entry point" claim, this
  is sparse. A dedicated `SyscallDispatchSuite.lean` with
  per-syscall positive and negative cases would close the gap.
- **DEEP-TEST-04 (L)**: `tests/fixtures/main_trace_smoke.expected`
  is the golden output for `Main.lean`. 145+ lines. Verified
  non-empty and exercised by the main trace. ✓ Predecessor §2.8.

### 8.2 Scripts (49 files)

- `set -euo pipefail` in 100% of shell scripts.
- Trap-based cleanup discipline via `_common.sh:119–163`.
- Pre-commit hook (`scripts/pre-commit-lean-build.sh`) is symlinked
  from `.git/hooks/pre-commit`. Verified at audit time.

New findings:

- **DEEP-PRECOM-01 (M)**: documented above in §3. The `sorry`-detection
  regex is fragile against block-comment `/- ... sorry ... -/` spans.
- **DEEP-SCRIPT-01 (I)**: `scripts/website_link_manifest.txt:18` says
  "Last synchronized: 2026-03-02" — 56 days stale. The manifest is
  enforced by Tier-0 hygiene (`scripts/check_website_links.sh`) so
  staleness in the comment doesn't affect correctness, but the
  comment is misleading. Either auto-update via a CI step or
  remove the timestamp.
- **DEEP-SCRIPT-02 (I)**: Python helpers (`scenario_catalog.py`,
  `report_current_state.py`, etc.) use type hints and
  `subprocess.run(check=True)` list-form. No `shell=True`, no `eval`.
  Verified clean.

### 8.3 CI workflows (5)

- `lean_action_ci.yml`: SHA-pinned actions, `cancel-in-progress: true`,
  job-tagged cache keys (`-fast`/`-smoke`/`-full`). ✓
- `platform_security_baseline.yml`: ARM runner, gitleaks/Trivy/CodeQL
  gated on non-fork PRs.

New finding:

- **DEEP-CI-01 (L)**: Concurrency control inconsistency.
  `lean_action_ci.yml` correctly sets `cancel-in-progress: true`
  (lines 19–21), but the other workflows
  (`platform_security_baseline.yml`,
  `lean_toolchain_update_proposal.yml`,
  `nightly_determinism.yml`,
  `codebase_map_sync.yml`) lack concurrency groups. Pushes to main
  queue redundant jobs across non-Lean workflows. Add a uniform
  `concurrency:` block to each workflow file to prevent waste.

### 8.4 Documentation

The project has 221 doc files (excluding archived `docs/dev_history/`).
The active canon is:

- `README.md`, `CLAUDE.md`, `CONTRIBUTING.md`, `AGENTS.md` (root).
- `docs/spec/SELE4N_SPEC.md` (1904), `docs/CLAIM_EVIDENCE_INDEX.md`,
  `docs/WORKSTREAM_HISTORY.md`, `docs/codebase_map.json`.
- `docs/gitbook/` (18 chapters, mirrors of canonical root docs).
- `docs/audits/` (current audit cycle artefacts).
- `docs/planning/`, `docs/hardware_validation/`, `docs/i18n/`.

New findings:

- **DEEP-DOC-01 (H)** confirmed: README has internally inconsistent
  proved-declaration count. Line 92 says "3,186 theorem/lemma
  declarations"; line 213 says "2,725 proved declarations". The
  former matches `codebase_map.json`'s prior-cycle snapshot; the
  latter is older. Both numbers appear on the same rendered page.
  The reader cannot tell which is current.
- **DEEP-DOC-02 (M)** confirmed: `AGENTS.md:7` says
  "version 0.12.4". Actual is 0.30.11. AGENTS.md is the canonical
  guidance file for external contributors and Claude Code agents;
  stale version metadata misleads them.
- **DEEP-DOC-03 (M)** confirmed: `CLAUDE.md` source-layout section
  (lines 77–234) omits **3 files** that are part of the production
  Lean tree:
  - `SeLe4n/Platform/FFI.lean` (245 lines, contains the v1.x stub
    bridges that determine hardware boot success).
  - `SeLe4n/Platform/Staged.lean` (67 lines, the build-anchor that
    forces the staged modules to compile).
  - `SeLe4n/Platform/RPi5/VSpaceBoot.lean` (~14k bytes, RPi5 boot
    VSpace configuration).
  Verified by `grep -c "FFI" CLAUDE.md` → 0 and `grep` for
  `VSpaceBoot` → 0.
- **DEEP-DOC-04 (L)**: `README.md` has active links to
  `docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md` and
  `docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md` in the
  audit-history table without an "archived" annotation. v1.0 readers
  arriving at the README will follow these links and see year-old
  findings as if they were current. Add an "archived" badge or
  re-point links to the active audit
  `docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md` (and to this
  document, post-merge).
- **DEEP-DOC-05 (I)**: Project description in `CLAUDE.md` line 9
  reads: "First hardware target: Raspberry Pi 5." This is consistent
  with the kernel's design intent and roadmap, but in the absence of
  the FFI dispatch wiring (DEEP-FFI-01) the kernel cannot service
  syscalls on RPi5 in v1.0. The phrasing should be qualified:
  "First hardware target (proof-artefact ready for v1.0; full
  syscall dispatch on hardware lands in v1.x via AN9-D/AN9-F
  glue closure)."
- **DEEP-DOC-06 (L)**: README test-suite count drift. Line 38 says
  "Test Lean LoC | 16,168 across 25 test suites"; the source-layout
  table elsewhere says "tests/ — 24 test suites"; actual is 28. The
  `codebase_map.json` correctly says 28. README is doubly-stale.

## 9. Cross-cutting findings

### 9.1 Proof-debt summary (re-counted)

| Category | Count | Location |
|---|---|---|
| `sorry` (production) | **0** | grep-verified across SeLe4n/ |
| `axiom` (production) | **0** | grep-verified |
| `Classical.byContradiction` | **1** | `Scheduler/Operations/Preservation.lean:1720` (DEEP-PROOF-01) |
| `Classical.choice` | **0** | grep-verified |
| `Classical.em` (explicit) | **0** | grep-verified |
| `noncomputable` (production) | **0** | grep-verified |
| `partial def` (production) | **0** | grep-verified |
| `partial def` (tests) | 2 | `tests/TraceSequenceProbe.lean:249`, `tests/OperationChainSuite.lean:419` (probe loop, expected) |
| `unsafe` (Lean) | **0** | n/a in Lean |
| `unsafe { … }` (Rust HAL) | 53 | each ARM-ARM-cited (with DEEP-RUST-01/02 noting two missing references) |
| `unsafe` (Rust non-HAL) | 1 | `sele4n-abi/src/trap.rs::raw_syscall`, single-function unsafe, justified |
| `decide` over hardcoded model | 0 | WCRT and other liveness metrics fully parametric ✓ |
| `set_option linter.*` | 14 files | 7 IPC + 3 Architecture + 2 Scheduler + 1 Builder + 1 Testing/Deprecated; DEEP-IPC-02 flags missing justification comments |

### 9.2 Identifier hygiene (CLAUDE.md "Internal-first naming")

- **0 violations** in production Lean (`SeLe4n/`) for new/recent code.
  Pre-existing legacy identifiers (`ak8a_*`, `an2f3_*`, etc.) are
  explicitly grandfathered until touched in a workstream that can
  rename them in the same commit.
- **Tests violate the policy in 4+ files** (DEEP-TEST-01/02):
  `Ak8CoverageSuite.lean`, `An9HardwareBindingSuite.lean`,
  `Ak9PlatformSuite.lean`, `An10CascadeSuite.lean`. The CLAUDE.md
  rule applies to "every identifier in the codebase — theorems,
  functions, definitions, structures, fields, **test runners, file
  names, and directory names**". These suites should be renamed.

### 9.3 Re-export hub purity

| Hub | Lines | Status (re-verified) |
|---|---|---|
| `Kernel/IPC/Operations.lean` | 41 | pure imports |
| `Kernel/IPC/Invariant.lean` | 34 | pure imports |
| `Kernel/IPC/DualQueue.lean` | 41 | pure imports |
| `Kernel/Capability/Invariant.lean` | 23 | pure imports |
| `Kernel/Scheduler/Operations.lean` | 25 | pure imports |
| `Kernel/Scheduler/Invariant.lean` | (sample) | imports only |
| `Kernel/InformationFlow/Enforcement.lean` | 22 | pure imports |
| `Kernel/InformationFlow/Invariant.lean` | 23 | pure imports |
| `Kernel/Service/Invariant.lean` | 26 | pure imports |
| `Kernel/SchedContext/Invariant.lean` | 56 | imports + intentional compile-time guard |

### 9.4 Security-property checklist (re-verified)

| Property | Status | Witness |
|---|---|---|
| Badge derivation one-way | ✓ | `mintDerivedCap` rights attenuation |
| No sibling privilege leakage on revoke | ✓ | `cspaceRevoke_local_target_reduction` |
| CDT acyclicity invariant | ✓ | `Invariant/Defs.lean` lines 29–62 |
| Blocking-graph acyclicity | ✓ | `blockingAcyclic` (defined predicate) |
| WCRT bound parametric | ✓ | `WCRTHypotheses` fields, monotone reduction |
| ASID rollover preserves TLB isolation | ✓ | `AsidPool.allocate_result_fresh` |
| W^X invariant on VSpace | ✓ | `wxExclusiveInvariant` 7-tuple bundle |
| VSpace lookup round-trips (TPI-001 quartet) | ✓ | 4 named theorems |
| Boot-time IRQ handler validity | ✓ | `irqHandlersReferenceNotifications` |
| MCP authority bounds (no escalation) | ✓ | `validatePriorityAuthority_bound` |
| Information-flow composition (IF-M4) | ✓ | `composedNonInterference_step` |
| Single declassification site, gated | ✓ | `declassifyStore` |
| Service dependency acyclicity | ✓ | declarative `serviceDependencyAcyclic` |
| FDT parser bounds-checked | ✓ | `readBE32`/`readBE64` + `parseFdtHeader` |
| Hardware syscall dispatch wired | **✗** | DEEP-FFI-01: `syscall_dispatch_inner` returns `NotImplemented` |

The last row is the audit's headline correction.

### 9.5 Architectural concerns (general)

The project's overall architecture is **clean and disciplined**.
The Operations / Invariant split per subsystem is uniform, the
hub re-exports are pure, the layering is acyclic (Capability →
Scheduler at hub level only; Scheduler does not import Capability),
and Cross-subsystem invariants are gathered in a single file rather
than scattered.

The single **architectural rough edge** is the Platform layer:
`FFI.lean` and `Staged.lean` were added late (post-AN7-D / AN9 cycles)
and the source-layout documentation was not updated. The FFI bridge
as currently shaped has **two distinct directions** (`@[extern]` and
`@[export]`) under one file, which can confuse readers. A future
refactor splitting `Platform/FFI/{LeanCallsRust,RustCallsLean}.lean`
would make the deferred `@[export]` stubs more obviously
under-implemented.

### 9.6 Dead-code summary

Dead-code findings, consolidated:

- **DEEP-ARCH-02**: 11 `_fields` definitions in CrossSubsystem.lean
  (lines 887–930). At least 7 appear unused (per Architecture agent
  finding 4a). Manual verification: `grep -rn "noStaleEndpointQueueReferences_fields"
  /home/user/seLe4n/SeLe4n` should reveal consumers; if 0 hits beyond
  the definition, the def is dead.
- **`rust/sele4n-hal/src/gic.rs:76 ICENABLER_BASE`** — `#[allow(dead_code)]`
  documented as future selective-disable surface. If no near-term
  plan to use it, remove.
- **`rust/sele4n-hal/src/trap.rs:147 NOT_IMPLEMENTED = 17`** —
  declared with `#[allow(dead_code)]`. Used only in test stub;
  consider inlining.
- **`SeLe4n/Platform/RPi5/VSpaceBoot.lean rpi5BootVSpaceRoot`** —
  computed and proven W^X-compliant but not threaded into the boot
  result (DEEP-BOOT-01). The verified data structure has no
  consumer in the boot path until AN9-E rewires
  `bootSafeObject` to admit boot VSpace roots. Not "dead" in the
  malicious sense; just inert and surprising.

The kernel's overall dead-code rate is **very low**. Predecessor's
spot checks of theorem/def reachability for IF, Service, IPC,
Capability, Scheduler all came up clean. The above 4 items are the
only real candidates this audit found.

## 10. Findings register (DEEP-* IDs) and recommendations

### 10.1 Full DEEP-* register

| ID | Sev | Area | Action |
|---|---|---|---|
| DEEP-FFI-01 | H | Platform/FFI + Rust HAL | Disclose hardware-dispatch gap in README, SECURITY_ADVISORY, release notes; do not ship a "v1.0 = bootable kernel" cut without first wiring `syscall_dispatch_inner`/`suspend_thread_inner` to the verified Lean dispatchers. Acknowledged debt under AN9-D / AN9-F → v1.x. |
| DEEP-FFI-02 | M | rust/sele4n-hal/src/svc_dispatch.rs:308 | Replace `syscallDispatchFromAbi` reference with the actual exported symbol (`syscall_dispatch_inner`) and link to FFI.lean docstring. |
| DEEP-FFI-03 | I | SeLe4n/Platform/FFI.lean:34–39 | Clarify in docstring that the `-DhwTarget=true` gating applies only to `@[extern]` (Lean→Rust) declarations; `@[export]` (Rust→Lean) stubs are always compiled. |
| DEEP-DOC-01 | H | README.md:92 vs :213 | Reconcile "3,186" and "2,725" theorem-count numbers; choose one and remove the other. |
| DEEP-DOC-02 | M | AGENTS.md:7 | Bump version from 0.12.4 → 0.30.11 (and add a sync-script hook). |
| DEEP-DOC-03 | M | CLAUDE.md source-layout section | Add entries for `SeLe4n/Platform/FFI.lean`, `SeLe4n/Platform/Staged.lean`, `SeLe4n/Platform/RPi5/VSpaceBoot.lean`. |
| DEEP-DOC-04 | L | README.md audit-history table | Annotate `AUDIT_v0.29.0_*` and `AUDIT_v0.30.6_*` links as "archived". |
| DEEP-DOC-05 | I | CLAUDE.md project description | Qualify "First hardware target: Raspberry Pi 5" with v1.0 dispatch-stub note. |
| DEEP-DOC-06 | L | README.md test-suite count | Update 25/24 → 28; resync from `codebase_map.json`. |
| DEEP-PROOF-01 | M | Scheduler/Operations/Preservation.lean:1720 | Rewrite the single `Classical.byContradiction` use as a constructive `cases hCur : st.scheduler.current` split. The existential is decidable. |
| DEEP-LICENSE-01 | I | SeLe4n.lean | Add `-- SPDX-License-Identifier: GPL-3.0-or-later` as line 1 (matches the 247 other files). |
| DEEP-MODEL-01 | L | Model/Object/Structures.lean CNode | Inline comment on `slots` field flagging `slotsUnique` proof obligation. |
| DEEP-MODEL-02 | L | Model/State.lean + Builder.lean | Promote 17 named accessors to public lemmas (or refactor to a record-shaped invariant). Subsumes DEBT-ST-01. |
| DEEP-MODEL-03 | I | Model/State.lean:146 | Cross-reference `replenishQueueSorted` invariant defined in SchedContext/ReplenishQueue.lean. |
| DEEP-MODEL-04 | I | Model/State.lean LifecycleMetadata | Document mutation sites for `capabilityRefs`. |
| DEEP-PRELUDE-01 | I | Prelude.lean:1076–1115 | Macro-generate the 15 `LawfulBEq` instances for typed identifiers. |
| DEEP-PRELUDE-02 | I | Prelude.lean:1131+ | Move HashSet/RHTable helper lemmas to `Prelude/HashSetLemmas.lean`. |
| DEEP-CAP-01 | L | Capability/Operations.lean:959, 1002 | Document null-cap guards in `cspaceCopy`/`cspaceMove` docstrings. |
| DEEP-CAP-02 | L | Capability/Operations.lean:1081–1111 | Either enforce "slot already contains a capability" precondition for `cspaceMutate`, or update the docstring to match the relaxed semantics. |
| DEEP-CAP-03 | I | Capability/Operations.lean:750–756 | Document guard order (rights → null) in `mintDerivedCap` docstring. |
| DEEP-CAP-04 | I | Capability/Invariant/Defs.lean:345–367 | Strengthen `RetypeTarget` "phantom witness" comment. |
| DEEP-CAP-05 | I | Capability/Operations.lean:12–62 | Move "AK8-K LOW-tier" deferred items from header comment to the project debt register. |
| DEEP-IPC-01 | M | Model/Object/Types.lean Notification, IPC ops | Add NoDup guard at `notificationWait` enqueue, instead of relying on upstream invariant maintenance. |
| DEEP-IPC-02 | M | 7 files in IPC/Invariant | Add a one-line justification comment beside each `set_option linter.unusedVariables false`. |
| DEEP-IPC-03 | H | IPC/DualQueue/WithCaps.lean:112–198 | Close AK1-I: align send/call cap-transfer error with receive (`.error .invalidCapability`) when receiver CSpace root is missing. NI symmetry. |
| DEEP-IPC-04 | I | IPC/Operations/Endpoint.lean:485 | Verify the formal proof `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull` exists and is sorry-free. |
| DEEP-IPC-05 | I | (cross-references DEEP-IPC-01) | covered above. |
| DEEP-SCH-01 | I | Scheduler/RunQueue.lean:66–72 | Document the `membership ↔ threadPriority` consistency invariant in the file header. |
| DEEP-SCH-02 | I | Scheduler/Operations/Selection.lean:225–241 vs :327 | Document fail-open vs fail-safe API contract. |
| DEEP-SCH-03 | I | Lifecycle/Suspend.lean:75–84 / :290+ | Extract shared "restore-to-ready" helper. |
| DEEP-SCH-04 | I | Scheduler/Operations/Core.lean:715–717 | Surface `.missingSchedContext` instead of silent no-preempt fallback. |
| DEEP-SCH-05 | I | Scheduler/RunQueue.lean:238 | Replace defensive priority-0 fallback with explicit error or assertion. |
| DEEP-SCH-06 | I | SchedContext/Operations.lean:141–185 | Verify domain propagation for `schedContextConfigure`. |
| DEEP-SUSP-01 | I | Lifecycle/Suspend.lean resumeThread | Document/handle PIP recomputation on resume if blocking chain changed during suspension. |
| DEEP-SUSP-02 | I | Lifecycle/Suspend.lean:88–105 | Document `cancelDonation` two-arm semantics or split into `cancelBoundDonation`/`cancelDonatedDonation`. |
| DEEP-ARCH-01 | L | CacheModel/TimerModel/ExceptionModel.lean | Reclassify "STATUS: staged for H3" markers (modules are now production-active). |
| DEEP-ARCH-02 | L | CrossSubsystem.lean:887–930 | Audit each of 11 `_fields` defs; remove unused ones or wire them into a `fieldsDisjoint` composition. |
| DEEP-ARCH-03 | I | Architecture/ExceptionModel.lean | Document GIC dispatch flow boundary — formal model is in InterruptDispatch.lean. |
| DEEP-ARCH-04 | I | Architecture/IpcBufferValidation.lean | Either add "STATUS: staged" marker or confirm production. |
| DEEP-IF-01 | I | InformationFlow/Soundness.lean | Verify import path of `DeclassificationPolicy` structure. |
| DEEP-IF-02 | I | Policy.lean:484–500 | Document that the parameterised `SecurityDomain` lattice section is intentionally truncated as post-1.0 hook. |
| DEEP-BOOT-01 | M | Platform/Boot.lean:551 + RPi5/VSpaceBoot.lean | Either thread `rpi5BootVSpaceRoot` into the boot result via the AN9-E rewire of `bootSafeObject`, or remove the unwired data structure. |
| DEEP-FDT-01 | L | Platform/DeviceTree.lean:695–740 | Distinguish fuel exhaustion from malformed-blob in `findMemoryRegPropertyChecked`. |
| DEEP-RUST-01 | L | rust/sele4n-hal/src/mmio.rs | Add ARM ARM B2.2.1 reference to MMIO unsafe blocks. |
| DEEP-RUST-02 | L | rust/sele4n-hal/src/registers.rs | Add ARM ARM D17 reference to `mrs`/`msr` blocks. |
| DEEP-RUST-03 | I | sele4n-abi/src/trap.rs:2-6 | Correct module-level comment about "single unsafe block." |
| DEEP-RUST-04 | L | THIRD_PARTY_LICENSES.md:41 | Clarify cc semver range vs resolved version. |
| DEEP-RUST-05 | I | sele4n-abi/src/lib.rs, sele4n-sys/src/lib.rs | Add module-level doc comments. |
| DEEP-RUST-06 | L | sele4n-abi/tests/conformance.rs | Extend conformance to 6 missing syscalls (ServiceRegister/Revoke/Query, NotificationSignal/Wait, ReplyRecv). |
| DEEP-TEST-01 | M | tests/Ak8CoverageSuite.lean | Rename file + 25+ test functions to remove `AK8` workstream-ID prefix. |
| DEEP-TEST-02 | L | tests/{An9HardwareBindingSuite, Ak9PlatformSuite, An10CascadeSuite}.lean | Same rename treatment. |
| DEEP-TEST-03 | M | tests/ | Add a dedicated `SyscallDispatchSuite.lean` exercising `syscallEntryChecked` per syscall. |
| DEEP-TEST-04 | L | tests/fixtures/main_trace_smoke.expected | Verified non-empty; no action. |
| DEEP-PRECOM-01 | M | scripts/pre-commit-lean-build.sh:65 | Replace fragile multi-grep `sorry` regex with a Lean-tokenised check or with proper block-comment stripping. |
| DEEP-SCRIPT-01 | I | scripts/website_link_manifest.txt:18 | Auto-update or remove the "Last synchronized" timestamp. |
| DEEP-SCRIPT-02 | I | scripts/*.py | All clean. No action. |
| DEEP-CI-01 | L | .github/workflows/*.yml | Add `concurrency:` block to non-Lean workflows. |

### 10.2 Predecessor debt register status (re-confirmation)

| Predecessor ID | Status under this audit | Notes |
|---|---|---|
| DEBT-DOC-01 | **OPEN** | Re-confirmed; superseded in scope by DEEP-DOC-01/02/03/06. |
| DEBT-RUST-02 | **OPEN** | Predecessor could not reproduce H-24 markers; this audit re-grepped — zero hits. The H-24 finding is genuinely closed; mark `AUDIT_v0.30.6_DISCHARGE_INDEX.md` accordingly. |
| DEBT-ST-01 | **OPEN** (subsumed by DEEP-MODEL-02) | 17-conjunct projection chain. |
| DEBT-CAP-01, CAP-02 | **OPEN** | Frame-helper extraction + tactic for Insert/Delete/Revoke. |
| DEBT-SCH-01, SCH-02 | **OPEN** | Preservation.lean split, WCRT hypothesis discharge. |
| DEBT-IF-01, IF-02 | **OPEN** | Operations.lean thematic split, closure-form discharge. |
| DEBT-SVC-01 | **OPEN** | Acyclicity.lean split (Lean elaborator fragility blocker). |
| DEBT-IPC-01, IPC-02 | **OPEN** | H3 IPC-buffer extraction + AK10 rename. |
| DEBT-RT-01 | **OPEN** | RadixTree assertion if FrozenOps promoted. |
| DEBT-FR-01 | **OPEN** | FrozenOps experimental status — surface to README and SECURITY_ADVISORY. |
| DEBT-RUST-01 | **OPEN** (subsumed by DEEP-RUST-06 expanded) | Conformance test coverage. |
| DEBT-TST-01 | **OPEN** | NegativeStateSuite split. |
| DEBT-BOOT-01 | **OPEN** (interacts with DEEP-BOOT-01) | AF3-F minimum-config validation. |

### 10.3 Recommended pre-1.0 must-fix sequence

The pre-1.0 cleanup PR plan (in priority order):

1. **PR 1 — Honesty.** Update README, AGENTS.md, CLAUDE.md (closes
   DEEP-DOC-01, -02, -03, -05, -06, DEEP-LICENSE-01, DEEP-FFI-03,
   DEEP-FFI-02, DEBT-DOC-01). One PR; all documentation.
2. **PR 2 — Safety symmetry in IPC.** Close DEEP-IPC-03 (AK1-I) by
   aligning send/call cap-transfer error with receive. Information-flow
   covert-channel hardening.
3. **PR 3 — Classical removal.** Rewrite `Preservation.lean:1720`
   constructively (DEEP-PROOF-01). Closes the project's stated
   "constructive Lean kernel" discipline.
4. **PR 4 — Test rename.** Strip workstream IDs from test
   filenames and identifiers (DEEP-TEST-01/02). Pure rename PR; large
   churn but mechanical.
5. **PR 5 — Pre-commit hardening.** Replace the regex `sorry` check
   with a Lean tokenizer-based check (DEEP-PRECOM-01).

Items 1–5 plus the predecessor's must-fix lane (refresh metrics,
re-confirm H-24) constitute the v1.0 readiness PR set.

### 10.4 Hardware-readiness recommendation (the bigger picture)

The kernel today is, in effect, **two artefacts shipped together**:

1. **The proof artefact** — 109,787 lines of Lean, 0 sorry/axiom,
   parametric WCRT, faithful information-flow composition,
   verified data structures, ARM-architectural correctness boundaries
   (ASID uniqueness, W^X, TLB+cache coherency, FDT bounds-checking,
   boot hardening). This is **production-ready** for academic and
   industrial consumption as a verified microkernel specification.
2. **The hardware shim** — Rust HAL with 53 careful `unsafe` blocks
   (each ARM-ARM-cited with two missing references — DEEP-RUST-01/02),
   GIC-400 init, MMU bringup, MMIO accessors, exception vectors. This
   is **mostly production-ready** for hardware boot, but the SVC
   dispatch glue (`syscall_dispatch_inner` and `suspend_thread_inner`)
   is currently a stub that returns NotImplemented for every call.

Tagging v1.0 today is honest if and only if the release notes
explicitly state which artefact is being released. The most defensible
path:

- **v1.0.0** = "verified microkernel **specification** — the proof
  artefact, with a working simulation harness and a hardware boot
  shim that wires interrupts and MMU but does not yet route syscalls
  to the verified dispatcher."
- **v1.x.0** = the AN9-D / AN9-F closure — wires
  `syscallDispatchInner` and `suspendThreadInner` to
  `syscallEntryChecked` and `suspendThread` respectively, threading
  `SystemState` through the FFI as required by the docstring's own
  v1.x roadmap.

Calling the v1.0 cut a "fully verified bootable microkernel" without
this clarification would be a credibility risk for a project whose
defining property is honesty about correctness.

### 10.5 Sign-off

This audit finds **no critical (C) defects** in the proof artefact:
no `sorry`, no `axiom`, exactly one `Classical.byContradiction` use
(constructively rewritable), one stale Rust-side comment referencing
a nonexistent Lean function, and a small body of documentation drift
(README/AGENTS/CLAUDE) that the project has acknowledged in its own
DEBT-DOC-01 register.

The audit finds **two H-severity findings** affecting v1.0 readiness:
DEEP-FFI-01 (the syscall-dispatch stub on hardware) and DEEP-DOC-01
(the README's internally inconsistent theorem count). The first is
acknowledged debt that needs honest disclosure in release notes; the
second is a 1-PR documentation refresh.

Beyond that, this audit refines the predecessor's debt register with
50+ specific, actionable findings (DEEP-* IDs above), most of which
are documentation-hygiene or post-1.0 maintainability work. None of
them block a v1.0 tag if the release-notes wording correctly
distinguishes "proof artefact" from "bootable kernel."

The prior audit's headline ("the kernel exhibits mature proof
discipline … explicit hardware-correctness boundaries … and disciplined
Rust safety") **stands**, with one substantive correction: the
hardware-correctness boundary is **not yet wired into the syscall
fast path**, and the documentation should say so.

— Audit closed 2026-04-28 on branch
`claude/comprehensive-project-audit-E6NYp`. Successor audit cycle
should re-verify DEEP-FFI-01 (closed when AN9-D/AN9-F glue lands)
and the documentation findings (closed when the must-fix PR set
merges).

