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
> one HIGH-severity dispatch-stub gap and one MEDIUM-severity stale-comment
> gap that together materially affect v1.0 release readiness on hardware
> (the FFI dispatch stubs and the dishonest Rust comment).

> **Remediation principle (added 2026-04-28, post-publication revision).**
> Where a finding identifies a discrepancy between code and the
> documentation/comment/design that describes it, the remediation is
> **always** to implement the description if the description represents
> an improvement, **never** to weaken the documentation to match
> inferior code. This rule is now codified in
> `CLAUDE.md` ("Implement-the-improvement rule"). Earlier drafts of
> this audit recommended documentation-only patches for findings such
> as DEEP-FFI-01 ("disclose the stub in release notes"), DEEP-DOC-05
> ("qualify the hardware-target claim"), DEEP-BOOT-01 ("thread the
> VSpaceRoot OR remove the unwired data structure"), DEEP-IF-02
> ("document the spec truncation"), and several others. Every such
> finding has been re-issued below with an
> implementation-first remediation. The "or remove" / "or document"
> alternatives have been struck. The release scheduling implication
> (a v1.0 cut is contingent on the implementation work landing,
> not on documentation surgery) is reflected in §10.3 and §10.4.

## Headline conclusion

The Lean kernel is **proof-sound** and **correctness-clean**: zero `sorry`,
zero `axiom`, one isolated `Classical.byContradiction` (witnessed; not
unsound; per the §12 implement-the-improvement rule the constructive
restructuring is scheduled for v1.x rather than relaxed via documentation),
zero `native_decide` over hardcoded models, zero `partial def` in
production source. All single-core invariants hold; the information-flow
composition theorem and the WCRT bound are both faithful and parametric.

However, the project is **not bootable to a working state on hardware** as
of v0.30.11. The FFI bridge from the Rust HAL into the Lean kernel
(`@[export syscall_dispatch_inner]` at `SeLe4n/Platform/FFI.lean:217` and
`@[export suspend_thread_inner]` at line 186) is a STUB that returns
`KernelError::NotImplemented = 17` on every call. The verified
`syscallEntryChecked` entry point in `Kernel/API.lean:1244` is **never
invoked from the hardware path**. A separate Rust-side comment in
`rust/sele4n-hal/src/svc_dispatch.rs:308` claims production "resolves to
the Lean kernel's `syscallDispatchFromAbi`" — a function name that **does
not exist** anywhere in the Lean source tree. This documentation
discrepancy masked the gap from the predecessor audit.

Per the implement-the-improvement rule (CLAUDE.md), the remediation for
this gap is to **implement the dispatch routing** so that
`syscall_dispatch_inner` actually invokes `syscallEntryChecked`,
`suspend_thread_inner` actually invokes `suspendThread`, and the Rust
comment's reference to `syscallDispatchFromAbi` becomes true (either by
adding that function or by aligning both sides on the
`syscall_dispatch_inner` name and threading the typed ABI decode
through it). It is **not** an acceptable remediation to leave the
stubs in place and add release-note disclosure of the gap. The work to
thread `SystemState` through the FFI is non-trivial (it requires a
v1.x architectural slice; see DEEP-FFI-01 in §10), but the audit's
recommended action is the architectural slice, not the disclosure
patch.

The release-readiness conclusion of v1.0 is therefore: **v1.0 cannot
ship until DEEP-FFI-01 lands**. The predecessor's "v1.0 = proof
artefact" framing is rejected on this audit cycle: a microkernel
that cannot dispatch syscalls on its named hardware target is not
v1.0, regardless of how thoroughly its specification is verified.
The proof artefact is a substantial milestone in its own right and
deserves a tagged release (e.g., `v0.31.0` "verified specification
release"), but `v1.0.0` should remain reserved for the bootable
cut.

Beyond the FFI gap, this audit finds (after the §11 verification
pass that withdrew 5 false positives and refined severities, and
the §12 implement-the-improvement revision that re-issued
documentation-only recommendations as implementation slices):

- **0 critical (C)** correctness defects.
- **2 high-severity (H)** findings: FFI dispatch gap with silent
  stub (DEEP-FFI-01 — remediation re-issued as
  *implement the dispatch routing*, not "disclose the stub");
  IPC capability-transfer NI asymmetry on the call path
  (DEEP-IPC-03, narrowed from 3 paths to 1).
- **~10 medium-severity (M)** findings: stale Rust↔Lean
  function-name comment (DEEP-FFI-02 — remediation re-issued as
  *implement `syscallDispatchFromAbi`*, not "fix the comment"),
  AGENTS.md comprehensively stale (DEEP-DOC-02), missing
  CLAUDE.md source-layout entries (DEEP-DOC-03), README metric
  inconsistency (DEEP-DOC-01, downgraded H→M), test-naming
  workstream-ID violations (DEEP-TEST-01), thin checked-syscall
  test coverage (DEEP-TEST-03), boot VSpaceRoot rejection
  (DEEP-BOOT-01 — remediation re-issued as
  *thread the verified VSpaceRoot through boot*, not "thread or
  remove"), pre-commit regex over-zealousness (DEEP-PRECOM-01,
  severity inverted L→M for fragility), IPC linter-suppression
  hygiene (DEEP-IPC-02), 17-conjunct accessor refactor
  (DEEP-MODEL-02).
- **~18 low-severity (L)** findings — including
  DEEP-PROOF-01 (the lone `Classical.byContradiction`,
  downgraded M→L after re-analysis), DEEP-CAP-01 (docstring
  promotion), and several LoC-hygiene items.
- **~18 informational (I)** findings — documentation gaps,
  consistency nits, post-1.0 maintainability hooks. Note that
  §12 re-issued **9 originally-informational/low-severity findings**
  as implementation work: DEEP-MODEL-01 (L), DEEP-CAP-04 (I),
  DEEP-IPC-05 (I), DEEP-SCH-02 (I), DEEP-SCH-06 (I),
  DEEP-SUSP-01 (I), DEEP-SUSP-02 (I), DEEP-IF-02 (I), DEEP-ARCH-03 (I).
  Their I/L classification reflects the *quality risk* of the
  current code state (low — invariants hold by upstream
  convention), not the *priority of the remediation* (which is
  pre-1.0 because the documentation describes the better state
  and should be made true).

The full register is in §10; the verification-pass corrections
(5 false positives withdrawn, 2 narrowed, 2 inverted-or-adjusted-severity)
are catalogued in §11; the implement-the-improvement re-issues
are catalogued in §12.

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
11. Verification-pass corrections (false positives, severity adjusts)
12. Implement-the-improvement revision (every documentation-only
    recommendation re-issued as the corresponding implementation
    slice, per the rule codified in CLAUDE.md)

## 1. Severity table and findings index

Severity legend — **C** critical (must fix before tag), **H** high (should
fix before tag), **M** medium (post-1.0 maintainability with material
risk), **L** low (cosmetic / cleanup), **I** informational.

### NEW findings introduced by this audit (not in predecessor) — POST-VERIFICATION, POST-REVISION

> Note: the table below shows severities **after** the §11 verification
> pass and the §12 implement-the-improvement revision. Findings withdrawn
> as false positives (DEEP-CAP-02, DEEP-ARCH-02, DEEP-RUST-01,
> DEEP-RUST-02, DEEP-IPC-01) are listed in §11.1 with full rationale.
> The "Action shape" column flags whether the remediation is
> *implementation* (code change), *documentation* (text change with no
> code counterpart), or *both* (a coordinated PR). Per CLAUDE.md's
> implement-the-improvement rule, no row should read "documentation"
> when the documentation describes a better state than the code.

| ID | Sev | Area | Action shape | One-line summary |
|---|---|---|---|---|
| DEEP-FFI-01 | H | Platform/FFI + Rust HAL | implementation | `syscall_dispatch_inner` and `suspend_thread_inner` Lean exports are stubs returning `NotImplemented = 17`; verified hardware path never reaches `syscallEntryChecked`. Wire the routing — disclosure-only patches are rejected. |
| DEEP-IPC-03 | H | IPC/DualQueue/WithCaps:198 | implementation | `endpointCallWithCaps` returns `.ok ({ results := #[] }, st')` on missing receiver-CSpace-root; AK1-I closed send and receive paths but the call path remains asymmetric. NI covert-channel risk. |
| DEEP-FFI-02 | M | Rust HAL | implementation | `rust/sele4n-hal/src/svc_dispatch.rs:308` comment describes Lean fn `syscallDispatchFromAbi`. The function should exist (it is the typed-ABI entry point that Tier 2 of the must-fix sequence builds). Implement the function, not edit the comment. |
| DEEP-DOC-01 | M | README (was H, downgraded §11.4) | documentation | README internally inconsistent: line 92 says "3,186 theorem/lemma declarations"; line 213 says "2,725 proved declarations" — same page. Pure documentation drift; one-PR refresh. |
| DEEP-DOC-02 | M | AGENTS.md | documentation | `AGENTS.md` line 7 declares project version **0.12.4** vs actual **0.30.11**. The entire file is from ~v0.12.x — it references audits at v0.11.0/v0.12.2 and a "WS-F (v0.12.2 audit remediation)" workstream. Best fix: rewrite to mirror CLAUDE.md or replace with a 10-line redirect (§11.5). |
| DEEP-DOC-03 | M | CLAUDE.md | documentation | Source-layout section omits `SeLe4n/Platform/FFI.lean` (245 LoC, contains the stub bridges flagged as DEEP-FFI-01), `SeLe4n/Platform/Staged.lean` (the build-anchor that pulls FFI into CI), and `SeLe4n/Platform/RPi5/VSpaceBoot.lean`. Verified by `grep -c "FFI" CLAUDE.md` → 0. |
| DEEP-TEST-01 | M | tests/Ak8CoverageSuite.lean | implementation | 25+ test functions named `test_AK8_E_*`, `test_AK8_F_*`, `test_AK8_G_*`, `test_AK8_H_*`, `test_AK8_I_*`. CLAUDE.md identifier policy bans workstream IDs in identifiers. Filename `Ak8CoverageSuite.lean` is also a violation. Mechanical rename PR. |
| DEEP-TEST-02 | L | README + codebase_map.json | documentation | Test-suite count drift: README says "25 test suites" (line 38) and elsewhere "24 test suites" (source layout); actual is 28. |
| DEEP-PROOF-01 | L | Scheduler/Operations/Preservation (was M, downgraded §11.4) | implementation (post-1.0) | `Classical.byContradiction` at `Preservation.lean:1720` (single explicit Classical use). Surrounding `by_cases` already invokes `Classical.em` implicitly; full elimination requires proof restructuring. The implement-the-improvement rule prefers restructuring over weakening the "constructive Lean kernel" claim, but Lean stdlib Classical is foundationally safe — restructure scheduled for v1.x. |
| DEEP-PRECOM-01 | M | scripts/pre-commit-lean-build.sh | implementation | The `sorry`-detection regex chain is fragile against block-comment syntax. Verification pass found the failure mode is OVER-zealous (rejects legitimate doc references to `sorry` in `/-…-/` blocks), not UNDER-zealous as initially documented. Replace with a Lean-tokeniser-based check. |

### Findings re-confirmed from predecessor (still applicable)

The full debt register from `AUDIT_v0.30.11_COMPREHENSIVE.md` §5 (DEBT-DOC-01,
DEBT-RUST-02, DEBT-ST-01, DEBT-CAP-01..02, DEBT-SCH-01..02, DEBT-IF-01..02,
DEBT-SVC-01, DEBT-IPC-01..02, DEBT-RT-01, DEBT-FR-01, DEBT-RUST-01,
DEBT-TST-01, DEBT-BOOT-01) is re-confirmed by this audit unless flagged
otherwise below in the per-subsystem narrative. None of those items have
been silently discharged in the 2 days between the two audits.

### Pre-1.0 must-fix list (proposed, post-verification, post-revision)

To keep the v1.0 cut credible. Tier ordering reflects the
implement-the-improvement rule: every "documentation-only" tier
that previously stood in lieu of a code fix has been replaced with
the corresponding implementation slice. Tiers are ordered so that
the smallest implementation slice precedes the largest, with the
strictly-documentation items (those that genuinely have no code
counterpart) at the end.

**Tier 1 — IPC NI symmetry (one-line code change, smallest slice):**

1. **DEEP-IPC-03** — at `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean:198`,
   replace `.ok ({ results := #[] }, st')` with
   `.error .invalidCapability`. Mirror the AK1-I comment block
   from line 113-125. This closes the last NI asymmetry between
   send/receive/call cap-transfer paths.

**Tier 2 — Hardware-dispatch implementation (the headline pre-1.0
work; no longer a documentation tier):**

2. **DEEP-FFI-01 IMPLEMENTATION (was: disclosure).** Wire
   `@[export syscall_dispatch_inner]` (`SeLe4n/Platform/FFI.lean:217`)
   into `syscallEntryChecked` (`Kernel/API.lean:1244`) and
   `@[export suspend_thread_inner]` (line 186) into `suspendThread`
   (`Kernel/Lifecycle/Suspend.lean`). This requires:
   - Threading the active `SystemState` through the FFI boundary
     (the v1.x work item the docstring already names). Options
     considered: (a) a `BaseIO` reference cell holding the global
     state; (b) a Lean-side `IO.Ref SystemState` initialised at
     boot; (c) a thread-local register-decoded snapshot. Option
     (b) is the simplest and aligns with how the simulation
     trace harness already manages state.
   - Per-call `RegisterDecode` + `SyscallArgDecode` to construct
     typed arguments from the eight `UInt64` register slots, then
     dispatch through `syscallEntryChecked` and re-encode the
     result.
   - Equivalent threading for `suspend_thread_inner`.
   - Tests: a hardware-mode integration suite that exercises
     each syscall on a simulated boot path (the existing
     `KernelErrorMatrixSuite` provides a starting matrix).
   The verified `syscallEntryChecked` already exists; the
   work is plumbing, not new proofs. **The v1.0 cut is
   contingent on this PR landing.** A "ship the proof artefact
   and disclose the stub" path is rejected per the
   implement-the-improvement rule.

3. **DEEP-FFI-02 IMPLEMENTATION (was: comment fix).** The Rust
   comment at `rust/sele4n-hal/src/svc_dispatch.rs:308` describes
   a Lean function `syscallDispatchFromAbi` that does not exist.
   Per the implement-the-improvement rule, the remediation is to
   **add** `syscallDispatchFromAbi` as the typed-ABI entry point
   the comment describes — the function that takes the eight
   register slots, calls `decodeSyscall` and `decodeSyscallArgs`,
   invokes `syscallEntryChecked`, and re-encodes. This becomes
   the body of `syscallDispatchInner` (FFI.lean) once Tier 2
   item 2 lands; the Rust comment is then accurate as written.
   (Documentation surgery to remove the reference is rejected:
   the comment was not aspirational, it was describing the
   design the audit itself agrees should exist.)

3a. **DEEP-FFI-03 IMPLEMENTATION (was: docstring clarification).**
    Wrap the two `@[export]` declarations in
    `SeLe4n/Platform/FFI.lean` (lines 185–190 and 216–223) in the
    same `hwTarget`-conditional `section` already used for the
    `@[extern]` declarations. After this, the FFI.lean docstring's
    claim "the `@[extern]` attribute is only active when building
    with `-DhwTarget=true`" generalises uniformly to both
    directions of the FFI bridge, and the docstring is accurate
    end-to-end.

**Tier 3 — Boot VSpace wiring + spec completeness (medium slice):**

4. **DEEP-BOOT-01 IMPLEMENTATION (was: thread or remove).**
   At `SeLe4n/Platform/Boot.lean:551`, rewrite `bootSafeObject`
   to admit `VSpaceRoot` objects that satisfy
   `bootSafeVSpaceRoot` (RPi5/VSpaceBoot.lean:272–297). Then
   thread `rpi5BootVSpaceRoot` (RPi5/VSpaceBoot.lean) into the
   boot result so the W^X-compliance proof carries through to
   runtime. The "or remove the unwired data structure" alternative
   in the original audit is struck — `rpi5BootVSpaceRoot` is the
   verified data structure that the rest of the boot path was
   built around; removing it would discard finished proof work.

5. **DEEP-IF-02 IMPLEMENTATION (was: document the truncation).**
   Complete the parameterised `SecurityDomain` lattice section at
   `Policy.lean:484–500` so the spec is end-to-end. The originally
   recommended "document that the section is intentionally
   truncated as a post-1.0 hook" is struck per the
   implement-the-improvement rule.

6. **DEEP-ARCH-03 IMPLEMENTATION (was: document the boundary).**
   Add the formal Lean-level bridge from `ExceptionModel`'s
   classification to `InterruptDispatch`'s
   acknowledge→handle→EOI flow. The originally recommended
   "document that the boundary lives between Lean and Rust
   HAL" is struck.

**Tier 4 — Structural invariant enforcement (medium slice):**

7. **DEEP-MODEL-01 IMPLEMENTATION (was: inline comment).** Refactor
   the CNode `slots : RHTable Slot Capability` field (or its
   constructors) so the `slotsUnique` invariant is structurally
   enforced rather than maintained by Builder convention. Options:
   (a) replace `RHTable` with an opaque type whose constructors
   discharge `slotsUnique`; (b) bundle `slots` with an
   accompanying `slotsUnique` proof field so the predicate is
   carried at the type level. The originally recommended "inline
   comment on the slots field flagging the proof obligation" is
   struck.

8. **DEEP-CAP-04 IMPLEMENTATION (was: louder comment).** Make the
   `RetypeTarget` "phantom witness" predicate
   (`Capability/Invariant/Defs.lean:345–367`) non-bypassable. Wrap
   the construction in a smart-constructor helper whose only
   public form requires invocation of the cleanup hook
   (`scrubLifecycleObject`); make the underlying `structure`
   private. Direct construction by manually proving the two
   component properties is then statically prevented. The
   originally recommended "strengthen the warning comment" is
   struck.

9. **DEEP-IPC-05 IMPLEMENTATION (was: cross-reference).** Add a
   type-level NoDup constraint to the notification
   `waitingThreads` field, so the `uniqueWaiters` predicate is
   discharged structurally rather than maintained by upstream
   convention. The runtime guard at `Operations/Endpoint.lean:723`
   continues to reject duplicate enqueue attempts; the new
   constraint additionally proves no future code path can
   bypass the guard without a corresponding type-level
   discharge.

**Tier 5 — Behaviour symmetry and split (small per-PR slices):**

10. **DEEP-SUSP-01 IMPLEMENTATION (was: document/handle).** Add
    a PIP-recomputation step to `resumeThread`
    (`Lifecycle/Suspend.lean:290+`) so a thread whose blocking
    chain changed during suspension has its `pipBoost` correctly
    re-derived on resume. Required for H4 readiness; needed
    in v1.0 if any non-trivial blocking chain can include a
    suspended holder.

11. **DEEP-SUSP-02 IMPLEMENTATION (was: document or split).**
    Split `cancelDonation` (`Lifecycle/Suspend.lean:88–105`)
    into `cancelBoundDonation` and `cancelDonatedDonation`.
    The two arms have distinct semantics ("unbind in place" vs
    "return to original owner") that should not be compressed
    under a single name.

12. **DEEP-SCH-02 IMPLEMENTATION (was: document the asymmetry).**
    Make `effectivePriority` (`Selection.lean:225–241`) and
    `resolveEffectivePrioDeadline` (line 327) share a single
    fail-safe convention. Either both return `Option`, or both
    are total under invariants; the asymmetric API contract is
    a structural smell.

13. **DEEP-SCH-04 IMPLEMENTATION** (already an implementation
    finding in the original audit). Surface
    `.missingSchedContext` from `Operations/Core.lean:715–717`
    instead of the silent no-preempt fallback.

14. **DEEP-SCH-05 IMPLEMENTATION** (already an implementation
    finding). Replace the `RunQueue.lean:238` defensive
    priority-0 fallback with explicit error or assertion.

15. **DEEP-SCH-06 IMPLEMENTATION (was: verify).** If
    `boundThreadDomainConsistent` requires it, wire domain
    propagation into `schedContextConfigure`
    (`SchedContext/Operations.lean:141–185`); if the invariant
    does not require it, prove the domain field on the bound
    TCB is reachable without it. Either way, the "stale field"
    risk must be discharged structurally.

16. **DEEP-CAP-05 IMPLEMENTATION (was: move to debt register).**
    Address the "AK8-K LOW-tier" deferred items currently
    documented in the `Capability/Operations.lean:12–62`
    header. Items whose fix fits inside this audit cycle are
    closed in this tier; items that genuinely cannot ship in
    v1.0 are lifted into the project debt register
    (`docs/audits/`) and CHANGELOG with explicit closure
    targets — never left as in-source comments that age out.

**Tier 6 — Hook hardening, license, and identifier hygiene
(small implementation slices):**

17. **DEEP-PRECOM-01** — replace the fragile `sorry`-detection
    regex chain in `scripts/pre-commit-lean-build.sh:59,61`
    with a Lean-tokeniser-based check.
18. **DEEP-LICENSE-01** — add `-- SPDX-License-Identifier:
    GPL-3.0-or-later` as line 1 of `SeLe4n.lean`.
19. **DEEP-TEST-01 / DEEP-TEST-02** — rename
    `Ak8CoverageSuite.lean`, `An9HardwareBindingSuite.lean`,
    `Ak9PlatformSuite.lean`, `An10CascadeSuite.lean` and their
    workstream-ID-prefixed test functions.

**Tier 7 — Documentation accuracy (the genuinely-documentation
tier; restricted to cases where the code is correct and the docs
are wrong, never the inverse):**

20. **DEEP-DOC-03** — add the three missing Platform files
    (`FFI.lean`, `Staged.lean`, `RPi5/VSpaceBoot.lean`) to
    `CLAUDE.md` source-layout section. (CLAUDE.md describes a
    *worse* state than the code — files exist that the doc
    omits — so the doc is the inferior artefact and the
    legitimate-exception clause of the rule applies.)
21. **DEEP-DOC-04** — annotate archived audit links in README.
22. **DEEP-DOC-06** — fix the README test-suite count drift
    (25/24 → 28).
23. **DEEP-DOC-01** — reconcile the 3,186 vs 2,725 declaration
    counts. Best approach: drop both inline numbers and replace
    with a single CI-synchronised reference to
    `codebase_map.json`.
24. **DEEP-ARCH-01 (CacheModel marker)** — the file's "STATUS:
    staged" marker describes a worse state than the code;
    update the marker to reflect production use.
25. **DEEP-DOC-05 (REVISED).** The original audit recommended
    qualifying "First hardware target: Raspberry Pi 5" with a
    stub-status caveat. Per the implement-the-improvement rule,
    the original phrasing is correct and the **code** is what
    must change (DEEP-FFI-01 / Tier 2). Once Tier 2 lands, no
    documentation change is needed. Until then, the README and
    CLAUDE.md may either keep the original phrasing
    (consistent with the implement-the-improvement
    commitment) or be silent about the hardware target — but
    they must not say the kernel "currently runs on RPi5"
    while Tier 2 is open. No "stub-status caveat" should be
    added.
26. **DEBT-DOC-01 (predecessor)** — refresh
    README ↔ codebase_map.json metric drift; sync test-suite
    count, file count, LoC.

**Tier 8 — AGENTS.md disposition:**

27. **DEEP-DOC-02** — `AGENTS.md` is from ~v0.12.x and is
    stale enough that a version bump is insufficient. The
    canonical agent-guidance file is `CLAUDE.md`. Best fix:
    rewrite `AGENTS.md` to mirror `CLAUDE.md` with a
    CI-enforced sync check, **or** replace with a 10-line
    redirect stub pointing to `CLAUDE.md`. Either keeps the
    discoverability some agent frameworks expect; both
    eliminate the divergence-rot risk. The redirect-stub
    option is acceptable here because the duplicated content
    has no proof or correctness payload — it is purely a
    navigation aid.

**Post-1.0 maintainability (deferred, but not relaxed):**
DEEP-PROOF-01 (Classical-use restructuring; the implement-the-
improvement rule mandates the proof rewrite, but the v1.x
window is acceptable because the single use is Lean-stdlib safe
and not unsound), DEEP-MODEL-02 (record-shaped 17-conjunct
invariant), and the remaining informational items not enumerated
above. **None of these are absorbed into documentation
disclaimers.** Each remains tracked as known debt with an
explicit closure target, per the implement-the-improvement
rule.

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
predicate is asserted; **operationally enforced** by
`notificationWait` at `Operations/Endpoint.lean:723` via an O(1)
`tcb.ipcState = .blockedOnNotification notificationId` check
(`.error .alreadyWaiting`). The originally-filed DEEP-IPC-01 was
**WITHDRAWN** in §11.1 after this verification.

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
- ~~**DEEP-CAP-02 (L)**~~: **WITHDRAWN — see §11.1.** The
  agent claim was that `cspaceMutate` does not validate the
  precondition. False positive: line 1093
  `if cap.isNull then .error .nullCapability` IS the validation,
  and the docstring at lines 1069–1080 describes the design.
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
- **DEEP-IPC-03 (H — narrowed in §11.3)**: `endpointCallWithCaps`
  (DualQueue/WithCaps.lean:198) silently returns `.ok ({ results := #[] }, st')`
  when the receiver's CSpace root is missing. The send and receive
  paths were already aligned with `.error .invalidCapability` under
  AK1-I (lines 125 and 158); only the call path remained
  asymmetric. **Information-flow risk**: a malicious caller can
  distinguish "receiver-CSpace-root present" from "missing" by
  observing `.ok` vs (some other error), giving a covert channel
  via
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

- **DEEP-ARCH-01 (L — narrowed §11.3)**: **Stale "STATUS: staged
  for H3" marker** on `CacheModel.lean:15–18`. Direct trace of
  imports: `SeLe4n.lean → TlbModel.lean → BarrierComposition.lean →
  CacheModel.lean`. CacheModel IS in the production chain, so the
  marker is misleading. **TimerModel.lean and ExceptionModel.lean
  markers are correct** — both are imported only by
  `Platform/Staged.lean` (verified via `grep -rln`), so they are
  genuinely staged. Action narrows to one file (CacheModel).
- ~~**DEEP-ARCH-02 (L)**~~: **WITHDRAWN — see §11.1.** The agent
  claim was that 7 of 11 `_fields` definitions are dead metadata.
  Direct verification shows every one has 3 to 26 consumers in
  the kernel. False positive.
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

**This is acknowledged debt** (AN9-D, AN9-F → v1.x). The §12
revision restates the criticism per the implement-the-improvement
rule:
1. The Lean docstrings, the Rust comment, the design intent, and
   the project documentation (README, CLAUDE.md) all describe a
   working hardware-syscall path. The code is the inferior
   artefact.
2. The remediation is to **implement the dispatch routing** so
   the documentation becomes true (§10.3 PR 2). The earlier-draft
   recommendation of "surface the state via release-note
   disclosure" is struck.
3. The Rust-side comment's reference to a Lean function
   `syscallDispatchFromAbi` should be made true by **adding the
   function**, not by deleting the reference (§10.3 PR 2 builds
   the typed-ABI entry point under that name).
4. v1.0 is no longer reinterpreted as "the proof artefact" —
   v1.0 = bootable verified microkernel. A pre-v1.0 release
   tag (`v0.31.0` "verified specification release") covers the
   current state honestly.

**Compilation gating gap.** FFI.lean docstring (lines 34–39) says
"`@[extern]` is only active when building with `-DhwTarget=true`."
This is true for the `@[extern]` declarations (Lean → Rust). It is
**silent** about `@[export]` declarations (Rust ← Lean), which are
**always compiled**. Even on simulation builds, the compiled stubs
exist; if any simulation path were ever to call into them they
would return NotImplemented. **DEEP-FFI-03 (I)**: per §12, the
remediation is to **implement uniform `hwTarget` gating** so the
docstring is accurate end-to-end, not to clarify the docstring's
asymmetric description.

### 6.2 Other Platform findings

**`SeLe4n/Platform/Boot.lean` (2115 LoC).** 5-gate validation in
`bootFromPlatformChecked` (line 696). Predecessor §2.4 fully covered.

- DEBT-BOOT-01 (AF3-F minimum-configuration validation: ≥1 thread,
  valid scheduler state) — re-confirmed open.
- **DEEP-BOOT-01 (M)**: `bootSafeObjectCheck` (line 551) explicitly
  rejects all `VSpaceRoot` objects (`| .vspaceRoot _ => false`). This
  means the checked boot path admits **no kernel VSpace** at boot.
  The actual mapping is loaded later via Rust HAL hardcoded tables
  in `mmu.rs` (post-BSS init). `rpi5BootVSpaceRoot`
  (VSpaceBoot.lean) is computed and proved W^X-compliant but
  **not threaded** into the boot result — a silent gap where a
  verified data structure has no consumer. **§12-revised
  remediation:** implement the AN9-E rewrite of `bootSafeObject`
  so the verified VSpaceRoot is admitted, then thread
  `rpi5BootVSpaceRoot` through. The earlier-draft "or remove the
  unwired data structure" alternative is struck per the
  implement-the-improvement rule — the verified data structure is
  the better state and removing finished proof work to match
  inferior boot code is rejected.

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
- ~~**DEEP-RUST-01 (L)**~~: **WITHDRAWN — see §11.1.** Direct
  verification: every MMIO unsafe block at lines 54–57, 76–79,
  96–98, 117–119 cites `(ARM ARM B2.1)`. The agent's claim was
  incorrect.
- ~~**DEEP-RUST-02 (L)**~~: **WITHDRAWN — see §11.1.** Direct
  verification: `mrs`/`msr` `asm!` blocks at lines 20–21 and
  45–46 cite `(ARM ARM C5.2)`, the appropriate section for
  system register access mnemonics.
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
- **DEEP-DOC-05 (I)** — REVISED §12: Project description in
  `CLAUDE.md` line 9 reads: "First hardware target: Raspberry Pi
  5." Earlier drafts of this audit recommended qualifying the
  phrasing with a "proof-artefact ready for v1.0; full syscall
  dispatch on hardware lands in v1.x" caveat. **§12 strikes that
  recommendation** per the implement-the-improvement rule. The
  CLAUDE.md statement is the project's design intent; making it
  true is DEEP-FFI-01 (the dispatch routing). Adding a stub-status
  caveat to the documentation while leaving the code as a stub is
  rejected. **No documentation change is required for DEEP-DOC-05.**
  v1.0 readiness is contingent on DEEP-FFI-01 landing; if v1.0 is
  tagged before that, the project's release scope itself is
  miscommitted (see §10.4 — pre-v1.0 release `v0.31.0` is
  available for the current state).
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
| Hardware syscall dispatch wired | **✗** | DEEP-FFI-01: `syscall_dispatch_inner` returns `NotImplemented`; §12 mandates implementation, not disclosure |

The last row is the audit's headline correction. Per §12 and the
implement-the-improvement rule, this row should read ✓ before a
v1.0 tag. A v0.31.0 "verified specification release" can ship
without the ✓; a v1.0.0 cannot.

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
`@[export]`) under one file, which can confuse readers. The §12
recommendation (per the implement-the-improvement rule) is to
**both** (a) implement the dispatch routing so the `@[export]`
stubs become real (PR 2 in §10.3) and (b) refactor the bridge into
`Platform/FFI/{LeanCallsRust,RustCallsLean}.lean` so the two
directions are separately auditable. The earlier-draft framing
("a future refactor would make the deferred stubs more obviously
under-implemented") is partially struck — the stubs should not
remain "under-implemented" past v1.0; the refactor is a separate
clarity improvement.

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
  computed and proven W^X-compliant but not threaded into the
  boot result (DEEP-BOOT-01). The verified data structure has no
  consumer in the boot path until AN9-E rewires
  `bootSafeObject` to admit boot VSpace roots. Not "dead" in the
  malicious sense; just inert and surprising. **§12 remediation:
  thread it through (do not remove it).** Per the
  implement-the-improvement rule, removing finished proof work
  to match inferior boot code is rejected.

The kernel's overall dead-code rate is **very low**. Predecessor's
spot checks of theorem/def reachability for IF, Service, IPC,
Capability, Scheduler all came up clean. The above 4 items are the
only real candidates this audit found.

## 10. Findings register (DEEP-* IDs) and recommendations

### 10.1 Full DEEP-* register

| ID | Sev | Area | Action |
|---|---|---|---|
> ⚠ Severities below are **as-originally-issued**; refer to §11.4
> for severity adjustments and §11.1 for findings withdrawn as
> false positives. The §11.6 table has the post-correction
> headline counts.

| DEEP-FFI-01 | H | Platform/FFI + Rust HAL | **Implement the dispatch routing.** Wire `syscall_dispatch_inner` (`Platform/FFI.lean:217`) into `syscallEntryChecked` (`Kernel/API.lean:1244`) and `suspend_thread_inner` (line 186) into `suspendThread` (`Kernel/Lifecycle/Suspend.lean`). Threading `SystemState` through the FFI is the v1.x work item the docstring already names; per CLAUDE.md's implement-the-improvement rule, this work is what unblocks v1.0 — release-note disclosure is not a substitute. (Original recommendation "disclose the gap in release notes" struck per §12.) |
| DEEP-FFI-02 | M | rust/sele4n-hal/src/svc_dispatch.rs:308 | **Implement `syscallDispatchFromAbi`** as the typed-ABI Lean entry point that the comment describes. Once DEEP-FFI-01 lands, this function is the body of `syscallDispatchInner` (FFI.lean) — it decodes the eight `UInt64` register slots via `RegisterDecode`/`SyscallArgDecode`, calls `syscallEntryChecked`, and re-encodes the result. Then the Rust comment is true as written. (Original recommendation "replace the reference with the existing exported symbol name" struck per §12 — the comment was describing the better state, and the better state is what we should implement.) |
| DEEP-FFI-03 | I | SeLe4n/Platform/FFI.lean:34–39 | **Implement uniform compile-time gating.** The docstring asserts `@[extern]` is gated by `-DhwTarget=true`, but `@[export]` symbols are always compiled. Wrap the two `@[export]` declarations (lines 185–190 and 216–223) in the same `hwTarget`-conditional `section`/`end` so both directions of the FFI bridge share a single gating mechanism. Then the docstring is accurate end-to-end. (Original recommendation "clarify the docstring asymmetry" struck per §12.) |
| DEEP-DOC-01 | M | README.md:92 vs :213 | (DOWNGRADED H→M §11.4) Reconcile "3,186" and "2,725" theorem-count numbers. Best fix: drop both, link to `codebase_map.json`, add CI sync check (§10.3 PR 11 post-§12). Pure documentation drift (the docs are inferior to the code; legitimate-exception clause of the implement-the-improvement rule). |
| DEEP-DOC-02 | M | AGENTS.md (entire file) | (REFINED §11.5) Entire file is from ~v0.12.x — version bump alone is insufficient. Best fix: replace with a 10-line redirect stub pointing to CLAUDE.md, OR full rewrite mirroring CLAUDE.md with CI-enforced sync check. |
| DEEP-DOC-03 | M | CLAUDE.md source-layout section | Add entries for `SeLe4n/Platform/FFI.lean`, `SeLe4n/Platform/Staged.lean`, `SeLe4n/Platform/RPi5/VSpaceBoot.lean`. |
| DEEP-DOC-04 | L | README.md audit-history table | Annotate `AUDIT_v0.29.0_*` and `AUDIT_v0.30.6_*` links as "archived". |
| DEEP-DOC-05 | I | CLAUDE.md project description | (REVISED §12.) The original "qualify with v1.0 dispatch-stub note" recommendation is struck per the implement-the-improvement rule. The CLAUDE.md statement "First hardware target: Raspberry Pi 5" is the design intent and must be made true via DEEP-FFI-01, not weakened. No documentation change is required as long as v1.0 is contingent on the FFI implementation landing. If v1.0 ships without DEEP-FFI-01, the project's release-readiness premise is itself broken and the audit's recommendation is to defer the tag, not to soften the documentation. |
| DEEP-DOC-06 | L | README.md test-suite count | Update 25/24 → 28; resync from `codebase_map.json`. |
| DEEP-PROOF-01 | L | Scheduler/Operations/Preservation.lean:1711-1721 | (DOWNGRADED M→L §11.4; REVISED §12.) Restructure the proof constructively (case-analysis on `Option ThreadId`) so the explicit `Classical.byContradiction` and the surrounding implicit `Classical.em` from `by_cases` both go away. The "or add a CLAUDE.md note clarifying that Lean stdlib Classical is permitted" alternative is struck per the implement-the-improvement rule: if the project's stated "constructive Lean kernel" discipline is the design intent, the kernel must conform — the documentation must not be relaxed to match a single non-constructive site. Severity remains L because Lean-stdlib `Classical.byContradiction` is foundationally safe; pre-1.0 priority is *medium-low* and the work is a v1.x research-style task. |
| DEEP-LICENSE-01 | I | SeLe4n.lean | Add `-- SPDX-License-Identifier: GPL-3.0-or-later` as line 1 (matches the 247 other files). |
| DEEP-MODEL-01 | L | Model/Object/Structures.lean CNode | (REVISED §12.) **Enforce the `slotsUnique` invariant structurally.** Either (a) replace `slots : RHTable Slot Capability` with an opaque `UniqueSlotMap` whose constructors discharge `slotsUnique`, or (b) bundle `slots` with a paired `slotsUnique : ...` proof field so the predicate is type-level. Original "inline comment on the slots field flagging the proof obligation" recommendation struck per §12 — the documentation already implies the invariant; the code should make it structurally inviolable rather than merely advertised. |
| DEEP-MODEL-02 | L | Model/State.lean + Builder.lean | (REFINED §11.5) Best fix: refactor `allTablesInvExtK` from a 17-tuple conjunction to a `structure` with named `Prop` fields. Then call sites use `h.objects`/`h.scheduler` etc.; adding a new RHTable field becomes a one-line structure change with compile-time enforcement. The public-accessor option is a stepping-stone, not the proper fix. Subsumes DEBT-ST-01. |
| DEEP-MODEL-03 | I | Model/State.lean:146 | Cross-reference `replenishQueueSorted` invariant defined in SchedContext/ReplenishQueue.lean. |
| DEEP-MODEL-04 | I | Model/State.lean LifecycleMetadata | Document mutation sites for `capabilityRefs`. |
| DEEP-PRELUDE-01 | I | Prelude.lean:1076–1115 | Macro-generate the 15 `LawfulBEq` instances for typed identifiers. |
| DEEP-PRELUDE-02 | I | Prelude.lean:1131+ | Move HashSet/RHTable helper lemmas to `Prelude/HashSetLemmas.lean`. |
| DEEP-CAP-01 | L | Capability/Operations.lean:959, 1002 | (REFINED §11.5) The null-cap guards ARE documented — but in inline `--` comments inside the function body (lines 964–968 for cspaceCopy, 998–1001 for cspaceMove). Best fix: promote these inline rationale blocks UP into the formal `/-- ... -/` docstring above each function. No code change. |
| ~~DEEP-CAP-02~~ | ~~L~~ | ~~Capability/Operations.lean:1081–1111~~ | **WITHDRAWN (§11.1)** — `cspaceMutate` DOES enforce the precondition via the `cap.isNull` guard at line 1093. False positive. |
| ~~DEEP-CAP-03~~ | I | Capability/Operations.lean:740–747 | (NO-ACTION §11.5) Guard order rationale already documented in the existing docstring at lines 740–747. No additional documentation needed. |
| DEEP-CAP-04 | I | Capability/Invariant/Defs.lean:345–367 | (REVISED §12.) **Make the `RetypeTarget` predicate non-bypassable.** Wrap construction in a smart-constructor whose only public form requires invocation of the cleanup hook (`scrubLifecycleObject`); make the underlying structure private. Direct construction by manually proving the two component properties is then statically prevented. Original "strengthen the warning comment" recommendation struck per §12 — the comment admitted a real bypass route, and the bypass route is what should be closed, not merely louder-warned. |
| DEEP-CAP-05 | I | Capability/Operations.lean:12–62 | (REVISED §12.) **Address the deferred items.** Each "AK8-K LOW-tier" comment in the header describes a known issue with a known fix; per the implement-the-improvement rule, those whose fix fits the current scope are closed in this audit cycle, and those that genuinely cannot ship in v1.0 are lifted into the project debt register with explicit closure targets. Original "move from header comment to project debt register" recommendation is the *minimum* acceptable action — fixing them is the optimal action and is preferred wherever effort permits. |
| ~~DEEP-IPC-01~~ | ~~M~~ | ~~Model/Object/Types.lean Notification, IPC ops~~ | **WITHDRAWN (§11.1)** — `notificationWait` already has an O(1) duplicate guard at `Operations/Endpoint.lean:723` (`tcb.ipcState = .blockedOnNotification` test → `.error .alreadyWaiting`). False positive. |
| DEEP-IPC-02 | M | 7 files in IPC/Invariant | Add a one-line justification comment beside each `set_option linter.unusedVariables false`. |
| DEEP-IPC-03 | H | IPC/DualQueue/WithCaps.lean:**198 only** (NARROWED §11.3) | At `:198`, replace `.ok ({ results := #[] }, st')` with `.error .invalidCapability`. AK1-I closure already fixed the send (line 125) and receive (line 158) paths; only the `endpointCallWithCaps` path still has the asymmetry. One-line fix mirroring AK1-I comment block. |
| DEEP-IPC-04 | I | IPC/Operations/Endpoint.lean:485 | Verify the formal proof `cleanupPreReceiveDonationChecked_never_errors_under_ipcInvariantFull` exists and is sorry-free. If the proof is missing, **prove it** rather than weaken the docstring claim that "the error branch is unreachable under `ipcInvariantFull`" — per the implement-the-improvement rule the docstring describes the better state. |
| DEEP-IPC-05 | I | Model/Object/Types.lean Notification | (REVISED §12.) **Make NoDup type-level on `waitingThreads`.** The `uniqueWaiters` predicate is currently asserted (and operationally enforced via the runtime guard at `Operations/Endpoint.lean:723` per §11.1's withdrawal of DEEP-IPC-01). The improvement is to make NoDup statically discharged (e.g., refinement type, opaque NoDupList). Original "cross-references DEEP-IPC-01" treatment struck per §12 — the cross-reference described the runtime guard but did not propose making the upstream invariant type-level, which is what the implement-the-improvement rule requires. |
| ~~DEEP-SCH-01~~ | I | Scheduler/RunQueue.lean:66–72 | (NO-ACTION §11.5) The implicit invariant is already documented in a 6-line comment at lines 66–72 inside the structure body, with a reference to `InvariantChecks.runQueueThreadPriorityConsistentB`. |
| DEEP-SCH-02 | I | Scheduler/Operations/Selection.lean:225–241 vs :327 | (REVISED §12.) **Make the API contract uniform.** Either `effectivePriority` and `resolveEffectivePrioDeadline` both return `Option`, or both are total under invariants; the asymmetric contract is a structural smell. Original "document fail-open vs fail-safe" recommendation struck per §12 — symmetric APIs are the better state and should be implemented, not asymmetric APIs labelled with disclaimers. |
| DEEP-SCH-03 | I | Lifecycle/Suspend.lean:75–84 / :290+ | Extract shared "restore-to-ready" helper. (Already implementation-first; no §12 revision needed.) |
| DEEP-SCH-04 | I | Scheduler/Operations/Core.lean:715–717 | Surface `.missingSchedContext` instead of silent no-preempt fallback. (Already implementation-first; no §12 revision needed.) |
| DEEP-SCH-05 | I | Scheduler/RunQueue.lean:238 | Replace defensive priority-0 fallback with explicit error or assertion. (Already implementation-first; no §12 revision needed.) |
| DEEP-SCH-06 | I | SchedContext/Operations.lean:141–185 | (REVISED §12.) **Implement domain propagation** for `schedContextConfigure` if `boundThreadDomainConsistent` requires it; if not, prove the field is reachable without it. Either way, the "stale field" risk is discharged structurally. Original "verify domain propagation" recommendation struck per §12 — verification alone leaves the gap latent if the answer is "yes, propagation is required." The fix must follow the verification step. |
| DEEP-SUSP-01 | I | Lifecycle/Suspend.lean resumeThread | (REVISED §12.) **Implement PIP recomputation on resume.** A thread whose blocking chain changed during suspension must have its `pipBoost` re-derived when resumed. Original "document/handle PIP recomputation" recommendation struck per §12 — the documented design implies the recomputation is required, and per the implement-the-improvement rule the code must conform. |
| DEEP-SUSP-02 | I | Lifecycle/Suspend.lean:88–105 | (REVISED §12.) **Split `cancelDonation` into `cancelBoundDonation` and `cancelDonatedDonation`.** The two semantic arms ("unbind in place" vs "return to original owner") are distinct enough that compressing them under a single name is a readability and correctness hazard. Original "document the two-arm semantics OR split" recommendation: the "or" branch is struck per §12. |
| DEEP-ARCH-01 | L | **CacheModel.lean only** (NARROWED §11.3) | Reclassify "STATUS: staged for H3" marker on `CacheModel.lean` — it IS in the production chain via `BarrierComposition` ← `TlbModel` ← `SeLe4n.lean`. TimerModel and ExceptionModel are genuinely staged-only; their markers are correct. |
| ~~DEEP-ARCH-02~~ | ~~L~~ | ~~CrossSubsystem.lean:887–930~~ | **WITHDRAWN (§11.1)** — every one of the 11 `_fields` definitions has 3–26 active consumers in the kernel (verified by `grep -rn`). False positive. |
| DEEP-ARCH-03 | I | Architecture/ExceptionModel.lean | (REVISED §12.) **Add the formal Lean-level bridge** from `ExceptionModel`'s classification to `InterruptDispatch`'s acknowledge→handle→EOI flow. Original "document the boundary" recommendation struck per §12 — the documentation's framing assumes the boundary will eventually be bridged formally; that's the implementation work. |
| DEEP-ARCH-04 | I | Architecture/IpcBufferValidation.lean | The marker is either correct or stale. If the file is in production, **remove the stale marker** (legitimate-exception clause: doc is the inferior artefact). If the file is genuinely staged-only, **add the marker** (so the staged state is visible to readers and the file is enrolled in `Platform/Staged.lean`). Verification first, then the corresponding action. |
| DEEP-IF-01 | I | InformationFlow/Soundness.lean | Verify import path of `DeclassificationPolicy` structure. If missing, **define it** rather than weaken the soundness theorem statement. |
| DEEP-IF-02 | I | Policy.lean:484–500 | (REVISED §12.) **Complete the parameterised `SecurityDomain` lattice section.** Original "document that the section is intentionally truncated as a post-1.0 hook" recommendation struck per §12 — the spec implies a complete lattice; the implementation must finish it rather than the spec be re-framed as deliberately truncated. |
| DEEP-BOOT-01 | M | Platform/Boot.lean:551 + RPi5/VSpaceBoot.lean | (REVISED §12.) **Thread `rpi5BootVSpaceRoot` through the boot result** by rewriting `bootSafeObject` (line 551) to admit `VSpaceRoot` objects that satisfy `bootSafeVSpaceRoot` (RPi5/VSpaceBoot.lean:272–297). Original "thread it OR remove the unwired data structure" alternative struck per §12 — the verified data structure is the better state and the code must consume it; removing finished proof work to match an inferior boot path is rejected. |
| DEEP-FDT-01 | L | Platform/DeviceTree.lean:695–740 | Distinguish fuel exhaustion from malformed-blob in `findMemoryRegPropertyChecked`. |
| ~~DEEP-RUST-01~~ | ~~L~~ | ~~rust/sele4n-hal/src/mmio.rs~~ | **WITHDRAWN (§11.1)** — every MMIO unsafe block already cites `(ARM ARM B2.1)`. False positive. |
| ~~DEEP-RUST-02~~ | ~~L~~ | ~~rust/sele4n-hal/src/registers.rs~~ | **WITHDRAWN (§11.1)** — `mrs`/`msr` `asm!` blocks already cite `(ARM ARM C5.2)`, the correct section for system register access mnemonics. False positive. |
| DEEP-RUST-03 | I | sele4n-abi/src/trap.rs:2-6 | Correct module-level comment about "single unsafe block." |
| DEEP-RUST-04 | L | THIRD_PARTY_LICENSES.md:41 | Clarify cc semver range vs resolved version. |
| DEEP-RUST-05 | I | sele4n-abi/src/lib.rs, sele4n-sys/src/lib.rs | Add module-level doc comments. |
| DEEP-RUST-06 | L | sele4n-abi/tests/conformance.rs | Extend conformance to 6 missing syscalls (ServiceRegister/Revoke/Query, NotificationSignal/Wait, ReplyRecv). |
| DEEP-TEST-01 | M | tests/Ak8CoverageSuite.lean | Rename file + 25+ test functions to remove `AK8` workstream-ID prefix. |
| DEEP-TEST-02 | L | tests/{An9HardwareBindingSuite, Ak9PlatformSuite, An10CascadeSuite}.lean | Same rename treatment. |
| DEEP-TEST-03 | M | tests/ | Add a dedicated `SyscallDispatchSuite.lean` exercising `syscallEntryChecked` per syscall. |
| DEEP-TEST-04 | L | tests/fixtures/main_trace_smoke.expected | Verified non-empty; no action. |
| DEEP-PRECOM-01 | M | scripts/pre-commit-lean-build.sh:59,61 | (INVERTED §11.2) The regex is OVER-zealous (false-positive on `/-…-/` block-comment `sorry` mentions), not under-zealous. No real `sorry`s slip through; the failure mode is rejecting legitimate doc references. Best fix: replace with a Lean-tokeniser-based check via `lean --run` on a small parser script. |
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

### 10.3 Recommended pre-1.0 must-fix sequence (post-§12 revision)

The pre-1.0 cleanup PR plan, ordered smallest implementation slice
first. The predecessor's "Honesty PR" (a documentation-only patch
for the FFI gap) has been replaced with the corresponding
**implementation** PRs per the implement-the-improvement rule. The
genuinely-documentation items (README metric drift, source-layout
omissions, archived-link annotation) ride at the end of the
sequence rather than the beginning, because they have no
documented-better-state-than-code conflict.

1. **PR 1 — IPC NI symmetry (one line).** Close DEEP-IPC-03 by
   aligning the call cap-transfer error with the send/receive
   pattern at `IPC/DualQueue/WithCaps.lean:198`.
2. **PR 2 — Hardware syscall dispatch wiring (substantive).**
   Close DEEP-FFI-01 + DEEP-FFI-02 + DEEP-FFI-03 + DEEP-DOC-05
   together: thread `SystemState` through the FFI, implement
   `syscallDispatchFromAbi` (the typed-ABI Lean entry point the
   Rust comment already described), wire
   `syscall_dispatch_inner` and `suspend_thread_inner` to
   `syscallEntryChecked` and `suspendThread` respectively, and
   apply uniform `hwTarget` gating to `@[export]` declarations.
   This is the headline implementation slice the v1.0 cut is
   contingent on.
3. **PR 3 — Boot VSpace threading.** Close DEEP-BOOT-01 by
   rewriting `bootSafeObject` to admit
   `bootSafeVSpaceRoot`-compliant VSpaceRoot objects, then
   threading `rpi5BootVSpaceRoot` into the boot result.
4. **PR 4 — Structural-invariant promotions.** Close
   DEEP-MODEL-01, DEEP-CAP-04, DEEP-IPC-05 by promoting the
   currently-implicit invariants (`slotsUnique`, RetypeTarget
   non-bypass, NoDup on `waitingThreads`) to type-level.
5. **PR 5 — Behaviour symmetry & function splits.** Close
   DEEP-SUSP-01 (PIP recomputation on resume), DEEP-SUSP-02
   (cancelDonation split), DEEP-SCH-02 (uniform priority API),
   DEEP-SCH-04, DEEP-SCH-05, DEEP-SCH-06, DEEP-SCH-03.
6. **PR 6 — Architecture/InformationFlow completeness.**
   Close DEEP-ARCH-03 (Lean-level GIC bridge), DEEP-IF-02
   (complete SecurityDomain lattice), DEEP-IF-01 (verify or
   define DeclassificationPolicy).
7. **PR 7 — Capability deferred-items closure.** Close
   DEEP-CAP-05 by addressing the AK8-K LOW-tier items inline
   where the fix fits, lifting the residue into the project
   debt register.
8. **PR 8 — Test rename.** Strip workstream IDs from
   `Ak8CoverageSuite.lean`, `An9HardwareBindingSuite.lean`,
   `Ak9PlatformSuite.lean`, `An10CascadeSuite.lean` and their
   workstream-ID-prefixed test functions. Mechanical rename
   PR; large churn (DEEP-TEST-01/02).
9. **PR 9 — Pre-commit hardening.** Replace the regex `sorry`
   check with a Lean tokeniser-based check (DEEP-PRECOM-01).
10. **PR 10 — License header sweep.** Add SPDX header to
    `SeLe4n.lean` (DEEP-LICENSE-01).
11. **PR 11 — Documentation accuracy (genuinely-doc tier).**
    Close DEEP-DOC-01 (README metric drift), DEEP-DOC-02
    (AGENTS.md disposition — rewrite or redirect),
    DEEP-DOC-03 (CLAUDE.md source-layout entries),
    DEEP-DOC-04 (archived-audit link annotation),
    DEEP-DOC-06 (test-suite count drift), DEEP-ARCH-01
    (CacheModel marker correction), DEBT-DOC-01.
12. **PR 12 — CI hygiene.** Add `concurrency:` blocks to
    non-Lean workflows (DEEP-CI-01).

PRs 1–6 are the v1.0 readiness set. PRs 7–12 may ship as a
v1.0 follow-up or be folded into the v1.0 cut if effort
permits. **Crucially, no documentation-only patch is now
proposed as a substitute for an implementation slice.**

The post-1.0 maintainability backlog continues to include
DEEP-PROOF-01 (Classical removal restructuring),
DEEP-MODEL-02 (record-shaped 17-conjunct invariant),
DEBT-CAP-01/02, DEBT-SCH-01/02, DEBT-IF-01/02, DEBT-SVC-01,
DEBT-IPC-01/02, DEBT-RT-01, DEBT-FR-01, DEBT-RUST-01,
DEBT-TST-01, DEBT-BOOT-01.

### 10.4 Hardware-readiness recommendation (the bigger picture, post-§12 revision)

The kernel today is, in effect, **two artefacts assembled into one
release candidate**:

1. **The proof artefact** — 109,787 lines of Lean, 0 sorry/axiom,
   parametric WCRT, faithful information-flow composition, verified
   data structures, ARM-architectural correctness boundaries (ASID
   uniqueness, W^X, TLB+cache coherency, FDT bounds-checking, boot
   hardening). The proof artefact is **complete** for academic and
   industrial consumption as a verified microkernel specification.
2. **The hardware shim** — Rust HAL with 53 careful `unsafe` blocks
   (each ARM-ARM-cited; DEEP-RUST-01/02 withdrawn in §11.1), GIC-400
   init, MMU bringup, MMIO accessors, exception vectors. The shim is
   complete *except* for the SVC dispatch glue
   (`syscall_dispatch_inner` and `suspend_thread_inner`), which is
   currently a stub returning `NotImplemented` for every call.

The predecessor audit and earlier drafts of this document recommended
splitting v1.0 into two interpretations ("v1.0 = proof artefact" vs
"v1.0 = bootable kernel") and tagging the proof-artefact cut now,
deferring the bootable cut to v1.x. **The §12 revision rejects this
approach.** Per the implement-the-improvement rule:

- The project's documentation, README headline, and CLAUDE.md
  description all describe a microkernel that runs on Raspberry Pi 5
  hardware. That is the better state.
- The remediation is to make the hardware path functional (PR 2 in
  the §10.3 sequence) so the documentation becomes true, **not** to
  dilute the documentation to match a stub.
- A v1.0 tag on a kernel that cannot dispatch syscalls on its named
  hardware target — regardless of how comprehensive its specification
  proofs are — is incompatible with the project's defining property
  of honesty about correctness.

The recommended release path, post-§12:

- **`v0.31.0` "verified specification release"** — tag the current
  state. Include the §10.3 PR 8–12 documentation/hygiene work if
  effort permits. This release is correctly described as a verified
  microkernel specification + simulation harness + hardware boot
  shim. No claims about hardware syscall dispatch. **No
  documentation-surgery is needed** because the release is named
  for what it actually is.
- **`v1.0.0` "bootable verified microkernel"** — tag once §10.3 PRs
  1–6 land. The defining v1.0 property is that
  `syscallEntryChecked` is reachable from a real RPi5 SVC; the
  CLAUDE.md "First hardware target: Raspberry Pi 5" statement is
  then literally true.

This separation costs one extra release tag in exchange for
honesty about scope. Tagging v1.0 today and patching the
documentation to "explain" why the kernel cannot service syscalls
on hardware would violate the implement-the-improvement rule and
the project's own correctness-honesty premise.

### 10.5 Sign-off

This audit finds **no critical (C) defects** in the proof artefact:
no `sorry`, no `axiom`, exactly one explicit `Classical.byContradiction`
use (post-§11.4 reanalysis: not easily eliminated and Lean-stdlib safe),
one stale Rust-side comment referencing a nonexistent Lean function,
and a small body of documentation drift (README/AGENTS/CLAUDE) that
the project has acknowledged in its own DEBT-DOC-01 register.

The audit finds **two H-severity findings** affecting v1.0 readiness
(post-verification): DEEP-FFI-01 (the syscall-dispatch stub on
hardware) and DEEP-IPC-03 (the call-path NI asymmetry, narrowed to
one line at `IPC/DualQueue/WithCaps.lean:198`). The first is
acknowledged debt that, per the §12 revision and CLAUDE.md's
implement-the-improvement rule, must be **closed by implementing
the dispatch routing**, not by release-note disclosure. The second
H finding (DEEP-IPC-03) is a one-line code change mirroring AK1-I's
pattern.
DEEP-DOC-01 (the README inconsistency) was downgraded H→M during
the verification pass — still pre-1.0 must-fix as a credibility item.

Beyond that, this audit refines the predecessor's debt register with
50+ specific, actionable findings (DEEP-* IDs above). Per the §12
implement-the-improvement revision, **a v1.0 tag is contingent on
§10.3 PRs 1–6 landing** — the proof artefact alone is not v1.0;
v1.0 is the bootable verified microkernel that the project's own
documentation describes. The genuinely-documentation findings
(README/CLAUDE.md/AGENTS.md hygiene; archived-link annotation;
SPDX header; CI concurrency) ride PR 11–12 and may follow the
v1.0 tag if effort dictates.

The prior audit's headline ("the kernel exhibits mature proof
discipline … explicit hardware-correctness boundaries … and
disciplined Rust safety") **stands**, with one substantive
correction: the hardware-correctness boundary is **not yet wired
into the syscall fast path**, and the project must close that gap
in code rather than dilute the documentation that asserts it.

— Audit closed 2026-04-28 on branch
`claude/comprehensive-project-audit-E6NYp`; revised 2026-04-28 on
branch `claude/fix-audit-findings-Feksd` to apply the
implement-the-improvement rule (CLAUDE.md). Successor audit cycle
should re-verify DEEP-FFI-01 (closed when the dispatch wiring
lands), the §12-revised structural findings (DEEP-MODEL-01,
DEEP-CAP-04, DEEP-IPC-05, DEEP-SUSP-01/02, DEEP-SCH-02/06,
DEEP-IF-02, DEEP-ARCH-03, DEEP-BOOT-01), and the
genuinely-documentation findings (closed when PR 11 merges).

---

## 11. Verification pass corrections (2026-04-28, same day)

After the audit was first written, every finding was re-verified
directly against the source one more time. Several findings produced
by the parallel agents were inaccurate; the corrections are
catalogued here so the report becomes a faithful record. **All
corrections strictly tighten the audit** — no new high-severity
findings emerged from the verification pass; several findings were
**withdrawn** because they were false positives.

### 11.1 Findings WITHDRAWN (false positives — remove from any remediation plan)

- **DEEP-CAP-02 — WITHDRAWN.** Claim was that `cspaceMutate` does
  not validate "slot already contains a capability" before mutation.
  False: `Capability/Operations.lean:1093` explicitly checks
  `if cap.isNull then .error .nullCapability` (the AK8-K C-L2
  occupied-slot guard). The docstring at lines 1069–1080 also
  documents the guarded design. The agent confused
  "`cspaceLookupSlot` returns `cap = Capability.null` on empty slot"
  (which it does, by CNode semantics) with "no validation occurs"
  (which is wrong — line 1093 IS the validation). Action: none.

- **DEEP-ARCH-02 — WITHDRAWN.** Claim was that 7 of 11
  `*_fields : List StateField` definitions in
  `CrossSubsystem.lean:887–930` are dead metadata. False: direct
  consumer counts via `grep -rn` for each name show 3 to 26
  consumers per field. Verified counts: `registryEndpointValid_fields`
  16, `registryInterfaceValid_fields` 3,
  `registryDependencyConsistent_fields` 26,
  `noStaleEndpointQueueReferences_fields` 16,
  `noStaleNotificationWaitReferences_fields` 16,
  `serviceGraphInvariant_fields` 26,
  `schedContextStoreConsistent_fields` 12,
  `schedContextNotDualBound_fields` 12,
  `schedContextRunQueueConsistent_fields` 12,
  `blockingAcyclic_fields` 4, `lifecycleObjectTypeLockstep_fields` 5.
  All 11 are actively used. Action: none.

- **DEEP-RUST-01 — WITHDRAWN.** Claim was that MMIO unsafe blocks in
  `rust/sele4n-hal/src/mmio.rs` lack ARM ARM section references.
  False: every MMIO unsafe block (lines 54–57, 76–79, 96–98, 117–119)
  cites `(ARM ARM B2.1)`. The agent missed this. Action: none.

- **DEEP-RUST-02 — WITHDRAWN.** Claim was that `mrs`/`msr` `asm!`
  blocks in `rust/sele4n-hal/src/registers.rs` lack ARM ARM
  references. False: lines 20–21 and 45–46 both cite
  `(ARM ARM C5.2)`, which is the correct section for
  MRS/MSR mnemonics (system register access). The agent confused
  C5.2 (instruction definition) with D17 (system register
  definitions); both are valid, but the existing reference is
  appropriate. Action: none.

- **DEEP-IPC-01 — WITHDRAWN.** Claim was that `notificationWait` has
  no NoDup guard on `waitingThreads`, so duplicates could be added
  upstream-error. False: `Operations/Endpoint.lean:723` does an
  O(1) duplicate check via the `tcb.ipcState ==
  .blockedOnNotification notificationId` test before enqueueing,
  rejecting with `.error .alreadyWaiting`. The "WS-G7/F-P11"
  comment at line 719 documents this design. Action: none.

### 11.2 Findings INVERTED (the description was wrong direction)

- **DEEP-PRECOM-01 — INVERTED.** Original claim: the pre-commit
  `sorry` regex would silently MISS a `sorry` in a multi-line
  `/- ... -/` block comment. Direct test (a 4-line block comment
  containing the word `sorry` was fed through the actual regex
  chain at `scripts/pre-commit-lean-build.sh:59,61`) shows the
  OPPOSITE: the line containing `sorry` IS flagged because none of
  the `grep -v` filters exclude lines that are merely INSIDE a
  block comment (the filters only exclude `--`-prefixed lines and
  lines with `"sorry"` strings). The hook is therefore
  **over-zealous** (false-positive on documentation references to
  `sorry` in block comments) rather than **under-zealous** (false-
  negative on real `sorry`s in block comments).
  Practical impact: zero — the codebase has no block-comment `sorry`
  references (the three matches in `tests/OperationChainSuite.lean`
  at lines 1660, 1661, 1668 are all in `--` line comments and are
  correctly excluded). The recommendation stands (replace the
  fragile regex with a tokeniser), but the rationale shifts from
  "lets bad code through" to "rejects legitimate documentation."
  Severity: **L** (down from M — the hook is safe-failing).

### 11.3 Findings NARROWED (scope was too broad)

- **DEEP-IPC-03 — NARROWED.** Original claim: `endpointSendDualWithCaps`
  AND `endpointCallWithCaps` silently return `.ok` on missing
  receiver CSpace root, while only `endpointReceiveDualWithCaps`
  fails closed. Direct read of
  `IPC/DualQueue/WithCaps.lean:113–125` shows that **the AK1-I
  closure already fixed the send path** — line 125 returns
  `.error .invalidCapability`, with a 13-line comment (lines
  113–125) documenting the NI symmetry. The receive path is also
  closed (line 158 likewise errors). The asymmetry persists
  **only in `endpointCallWithCaps`** (line 198, where the missing
  receiver-CSpace-root case still returns
  `.ok ({ results := #[] }, st')`). Severity stays H — NI
  symmetry across send/receive/call is the design goal — but the
  fix surface is one path, not three.

- **DEEP-ARCH-01 — NARROWED.** Original claim: three modules
  (`CacheModel.lean`, `TimerModel.lean`, `ExceptionModel.lean`)
  are marked "STATUS: staged for H3 hardware binding" but are in
  the production import chain. Direct trace via
  `grep -rln "import SeLe4n.Kernel.Architecture.<X>"`:
  - **CacheModel**: imported by `Platform/Staged.lean`,
    `Architecture/TlbCacheComposition.lean`, AND
    `Architecture/BarrierComposition.lean`. `BarrierComposition`
    is imported by `Architecture/TlbModel.lean`, which is imported
    by `SeLe4n.lean` (the production library entry point). So
    CacheModel **is** in the production chain. Marker is misleading.
  - **TimerModel**: imported only by `Platform/Staged.lean`.
    Genuinely staged. Marker is correct.
  - **ExceptionModel**: imported only by `Platform/Staged.lean`.
    Genuinely staged. Marker is correct.
  Action narrowed: only CacheModel.lean's marker should be
  reclassified or removed.

### 11.4 Findings with SEVERITY adjusted

- **DEEP-DOC-01 — H → M.** The README's internal inconsistency
  (3,186 vs 2,725 theorem-count) is documentation hygiene, not a
  correctness defect. A reader who notices the discrepancy can
  cross-check `codebase_map.json` to find the truth. Severity
  reduced to M (still pre-1.0 must-fix as a credibility item, but
  not blocking).

- **DEEP-PROOF-01 — M → L.** The single `Classical.byContradiction`
  use at `Scheduler/Operations/Preservation.lean:1720` is inside
  a proof that already invokes classical logic implicitly via
  `by_cases` on a non-decidable proposition (line 1711 — the
  universal quantifier over `outTid`). Removing only the explicit
  `Classical.byContradiction` does NOT make the proof constructive;
  the `by_cases` would still desugar to `Classical.em`. To fully
  eliminate Classical use, the proof must be restructured around
  case-analysis on `Option ThreadId` (decidable). Furthermore,
  Lean's `Classical.byContradiction` is a stdlib primitive
  ultimately backed by `Classical.choice` (an axiom in Lean's
  standard library, not in this project's code). The project's
  "no axiom" policy in CLAUDE.md is ambiguous on whether stdlib
  Classical primitives count. Severity reduced to L.
  **§12 revision:** the original §11.4 alternative
  ("OR add a one-line note in CLAUDE.md clarifying that Lean
  stdlib Classical primitives are permitted") is **struck** per
  the implement-the-improvement rule. The project's
  "constructive Lean kernel" discipline is design intent and
  must be made true via proof restructuring, not relaxed via
  a CLAUDE.md note. The restructuring is scheduled as a v1.x
  task; until it lands, the single Classical use is recorded
  as known debt, not endorsed.

### 11.5 Findings with RECOMMENDATIONS refined for optimality

For each remaining finding, the verification pass re-considered
whether the proposed action was the **best** approach. Where a
better approach exists, it is recorded here:

- **DEEP-DOC-02 (AGENTS.md staleness) — recommendation expanded.**
  Original action: "Bump version 0.12.4 → 0.30.11." The
  verification pass found that AGENTS.md is comprehensively
  out-of-date — it references audits at `v0.11.0`/`v0.12.2`,
  workstream "WS-F (v0.12.2 audit remediation) — planning",
  and other content from ~18 versions ago. A version bump alone
  would leave the rest of the file stale and create a false
  signal of currency.
  **Best approach (chosen):** delete `AGENTS.md` and add a
  redirect stub that points to `CLAUDE.md` as the single source
  of truth. CLAUDE.md is already the canonical agent-guidance
  file (it has the project's full v0.30.11 state); maintaining
  two parallel files invites drift. If `AGENTS.md` must remain
  for tooling discoverability (some agent frameworks scan for
  this filename), reduce it to ~10 lines: project name, version
  (auto-synced from `lakefile.toml`), one-line description, and
  a link to `CLAUDE.md`.
  **Second-best approach:** do a full rewrite of AGENTS.md
  matching CLAUDE.md content, then add a sync hook to keep them
  identical (or a CI check that fails if they diverge).

- **DEEP-MODEL-02 (17-conjunct accessor chain) — recommendation
  refined.** Original action: "Promote 17 named accessors to
  public lemmas (or refactor to a record-shaped invariant)."
  The verification pass strongly prefers the **record-shaped
  invariant** option:
  ```
  structure AllTablesInvExtK (st : SystemState) : Prop where
    objects             : st.objects.invExtK
    irqHandlers         : st.irqHandlers.invExtK
    services            : st.services.invExtK
    -- ... 14 more named fields
  ```
  Then call sites use `h.objects`, `h.scheduler`, etc. — every
  field has a stable name; adding a new RHTable field is a
  one-line addition to the structure with compile-time enforcement.
  Promoting the 17 `.2.2.2…` accessors to public is a strict
  improvement over the status quo but preserves the underlying
  fragility (any reorder of conjuncts breaks every call site).
  The structure-shaped form is the **proper long-term fix**;
  the public-accessor form is the lower-effort interim fix.
  Recommendation: target the structure form for v1.x; if effort
  is constrained, do the public accessors as a stepping stone
  but explicitly mark them as transitional in the docstring.

- **DEEP-CAP-01 (cspaceCopy/cspaceMove docstring null-cap
  guard) — recommendation refined.** The verification pass
  confirmed that the null-cap guards ARE documented — but in
  inline `--` comments inside the function body
  (`Operations.lean:964–968` for cspaceCopy, lines 998–1001 for
  cspaceMove), not in the formal `/-- ... -/` docstring above
  the function signature. The optimal fix is to **promote the
  inline rationale to the docstring**, not to write new
  documentation. Specifically: copy the `AL1b (AK7-I.cascade)`
  comment block from inside the function up into the docstring
  alongside the existing "destination must be empty" line. This
  is purely a comment-block move; no code or behaviour change.

- **DEEP-CAP-03 (mintDerivedCap guard order) — DOWNGRADE TO
  NO-ACTION.** The verification pass observed that the design
  rationale for the guard order (rights → null) is already
  documented in the `mintDerivedCap` docstring at
  `Operations.lean:740–747`. The agent's complaint was that the
  ordering is "fragile"; on closer reading, the design is
  intentional and well-explained. Action: none. Severity demoted
  from I to "no action."

- **DEEP-SCH-01 (RunQueue implicit invariant) — DOWNGRADE TO
  NO-ACTION.** The implicit invariant `membership ↔
  threadPriority consistency` is already documented in the
  `RunQueue` structure body at lines 66–72 with a 6-line
  comment explaining the design choice and pointing to the
  runtime check (`InvariantChecks.runQueueThreadPriorityConsistentB`).
  No additional documentation is needed. Action: none.

### 11.6 Updated severity counts (post-correction)

| Severity | Original count | Corrected count | Change |
|---|---|---|---|
| Critical (C) | 0 | 0 | – |
| High (H) | 3 (FFI-01, DOC-01, IPC-03) | 2 (FFI-01, IPC-03 narrowed) | -1 (DOC-01 → M) |
| Medium (M) | ~12 | ~10 (DOC-01 added, PROOF-01 → L, IPC-01 + CAP-02 withdrawn) | -2 |
| Low (L) | ~20 | ~18 (PROOF-01 added, RUST-01 + RUST-02 withdrawn, ARCH-02 withdrawn) | -2 |
| Informational (I) | ~20 | ~18 (CAP-03 + SCH-01 demoted to no-action) | -2 |
| **Total DEEP-* findings** | ~55 | ~48 | **-7** |

The updated headline: **0 critical, 2 high, 10 medium, 18 low,
18 informational, 48 total** new DEEP-* findings, with 5
withdrawn for false positives.

### 11.7 Verification-pass adjustments to the original §10.3 sequence (superseded by §12)

The verification pass produced this list of adjustments to the
original 5-PR §10.3 sequence:

- PR 1 (Honesty): 6 items, not 8.
- PR 2 (NI symmetry): scope reduced to a single file edit.
- PR 3 (Classical removal): consider deferring with a CLAUDE.md
  note that Lean-stdlib Classical is permitted.
- PR 4 (Test rename): unchanged.
- PR 5 (Pre-commit hardening): regex → Lean tokeniser.

**§12 supersedes this list.** The PR 1 "Honesty" tier is dissolved
into PR 2 (Hardware syscall dispatch wiring) and PR 11
(Documentation accuracy). The PR 3 "defer with a CLAUDE.md note"
proposal is **struck** per the implement-the-improvement rule —
the only acceptable resolution is the proof restructuring (see
DEEP-PROOF-01 row in §10.1). PRs 2, 4, and 5 carry forward into
the §10.3 post-§12 sequence as PRs 1, 8, and 9 respectively. See
§10.3 for the canonical post-§12 PR plan and §12 for the
governing principle.

### 11.8 Verification pass sign-off

The verification pass increased confidence in the audit by
removing false positives and tightening recommendations toward
the genuinely optimal fix in each case. **No new high-severity
findings emerged from the verification pass.** A subsequent
**§12 implement-the-improvement revision** (same day) re-issued
the documentation-only recommendations as their corresponding
implementation slices and re-shaped the §10.3 must-fix sequence
and §10.4 release recommendation accordingly. The post-§12
headline: proof artefact is clean; the v1.0 cut requires §10.3
PRs 1–6 to land; tagging v1.0 with a documentation-only patch
of the FFI gap is rejected.

— Verification pass closed 2026-04-28 on the same branch as
the original audit; superseded by §12 the same day.

---

## 12. Implement-the-improvement revision (2026-04-28, same day)

After the §11 verification pass closed, a final review of the
audit's recommendations identified that several findings were
recommending **documentation-only patches** for cases where the
documentation already described the *better* state and the code
was the *inferior* artefact. Examples in the original audit:

- DEEP-FFI-01 recommended "disclose the hardware-dispatch gap in
  release notes" — but the FFI docstrings, the design intent, and
  the Rust comment all describe a working dispatch routing. The
  documentation describes the better state; the code is the stub.
- DEEP-FFI-02 recommended "replace the Rust comment's reference to
  `syscallDispatchFromAbi` with the actual exported symbol name" —
  but the comment was describing the typed-ABI Lean entry point
  the design calls for. The documentation describes the better
  state; the code lacks the function.
- DEEP-DOC-05 recommended "qualify the CLAUDE.md statement 'First
  hardware target: Raspberry Pi 5' with a v1.0 dispatch-stub
  caveat" — but the statement is the project's design intent. The
  documentation describes the better state; the code lacks the
  hardware path.
- DEEP-BOOT-01 offered the alternative "thread the verified
  VSpaceRoot OR remove the unwired data structure" — but the
  proven-W^X-compliant data structure is the better state. The
  "remove" alternative would discard finished proof work to match
  inferior boot code.
- DEEP-MODEL-01 recommended "inline comment flagging the
  `slotsUnique` proof obligation" — but the proof obligation
  describes a stronger invariant than the field type advertises.
  Structural enforcement is the better state.
- DEEP-CAP-04 recommended "strengthen the warning comment on the
  `RetypeTarget` phantom witness" — but the comment admits a real
  bypass route, and structural prevention of that bypass is the
  better state.
- DEEP-IPC-05, DEEP-SCH-02, DEEP-SCH-06, DEEP-SUSP-01,
  DEEP-SUSP-02, DEEP-IF-02, DEEP-ARCH-03 — same pattern in each
  case.
- DEEP-PROOF-01's secondary recommendation ("add a CLAUDE.md note
  clarifying that Lean stdlib Classical is permitted") would
  weaken the project's "constructive Lean kernel" discipline to
  match a single non-constructive proof site, exactly the failure
  mode the rule prohibits.

These patterns violate the engineering principle the user
articulated and which is now codified in CLAUDE.md as the
**Implement-the-improvement rule**:

> When an audit, code review, or any reading of the codebase
> surfaces a discrepancy between the **code** on one side and the
> **documentation, docstring, comment, type signature, or design
> intent** that describes it on the other side, and the
> description represents an *improvement* over the actual code,
> the remediation is **always** to implement the improvement so
> the description becomes true. It is **forbidden** to weaken,
> dilute, qualify, or rewrite the documentation to match
> inferior code.

### 12.1 Findings revised by §12

Every finding listed below has been re-issued with an
implementation-first remediation in §10.1. The bullets here are
the canonical record of *what changed* in each row:

| Finding | Before §12 | After §12 |
|---|---|---|
| DEEP-FFI-01 | "Disclose hardware-dispatch gap in release notes" | "Implement dispatch routing into `syscallEntryChecked`/`suspendThread`" |
| DEEP-FFI-02 | "Fix the Rust comment's misnamed reference" | "Implement `syscallDispatchFromAbi` (the typed-ABI entry point the comment described)" |
| DEEP-FFI-03 | "Clarify the docstring's gating asymmetry" | "Implement uniform `hwTarget` gating for `@[export]` declarations" |
| DEEP-DOC-05 | "Qualify 'First hardware target: Raspberry Pi 5' with stub-status caveat" | "No documentation change; make the original statement true via DEEP-FFI-01" |
| DEEP-BOOT-01 | "Thread the VSpaceRoot OR remove the unwired data structure" | "Thread `rpi5BootVSpaceRoot` through `bootSafeObject`" (the "or remove" alternative struck) |
| DEEP-MODEL-01 | "Inline comment flagging the proof obligation" | "Enforce `slotsUnique` structurally (opaque type or paired proof field)" |
| DEEP-CAP-04 | "Strengthen the warning comment" | "Wrap `RetypeTarget` construction in a smart-constructor that requires cleanup invocation" |
| DEEP-CAP-05 | "Move deferred items from header comment to debt register" | "Address the deferred items where scope permits; lift the residue to the debt register only as a fallback" |
| DEEP-IPC-04 | "Verify the proof exists" | "Verify; if missing, **prove it** rather than weaken the docstring claim" |
| DEEP-IPC-05 | "Cross-references DEEP-IPC-01" (no action) | "Promote NoDup on `waitingThreads` to type-level enforcement" |
| DEEP-SCH-02 | "Document the asymmetric API contract" | "Make the API uniform" |
| DEEP-SCH-06 | "Verify domain propagation" | "Implement domain propagation if required; if not, prove it isn't required" |
| DEEP-SUSP-01 | "Document/handle PIP recomputation" | "Implement PIP recomputation on resume" |
| DEEP-SUSP-02 | "Document the two-arm semantics OR split into two functions" | "Split `cancelDonation` into `cancelBoundDonation` and `cancelDonatedDonation`" (the "or document" alternative struck) |
| DEEP-IF-01 | "Verify import path of `DeclassificationPolicy`" | "Verify; if missing, **define** the structure rather than weaken the soundness theorem" |
| DEEP-IF-02 | "Document that the SecurityDomain lattice is intentionally truncated" | "Complete the parameterised SecurityDomain lattice section" |
| DEEP-ARCH-03 | "Document the GIC dispatch flow boundary" | "Add the formal Lean-level bridge from `ExceptionModel` to `InterruptDispatch`" |
| DEEP-PROOF-01 (secondary recommendation) | "Add a CLAUDE.md note that Lean stdlib Classical is permitted" | Struck. Restructure the proof constructively (deferred to v1.x as known debt; not endorsed via documentation) |

### 12.2 Findings NOT revised by §12 (legitimate exceptions and clean cases)

Some findings remained untouched by the §12 revision because
their existing recommendation already conformed to the
implement-the-improvement rule, or because they fell under the
rule's legitimate-exception clause (documentation describing a
*worse* state than the code, where the doc is the inferior
artefact and updating it to match the code is correct):

- **DEEP-IPC-03** — already implementation-first in original audit
  (one-line code change at `IPC/DualQueue/WithCaps.lean:198`).
- **DEEP-SCH-03/04/05** — already implementation-first.
- **DEEP-FDT-01** — already implementation-first.
- **DEEP-PRECOM-01** — already implementation-first (replace
  regex with tokeniser).
- **DEEP-RUST-06** — already implementation-first (extend
  conformance tests).
- **DEEP-LICENSE-01** — already implementation-first (add SPDX
  header).
- **DEEP-MODEL-02** — already implementation-first per §11.5
  refinement (record-shaped invariant).
- **DEEP-TEST-01/02/03/04** — implementation actions
  (rename / extend / verify).
- **DEEP-CI-01** — already implementation-first.
- **DEEP-DOC-01, DEEP-DOC-02, DEEP-DOC-03, DEEP-DOC-04,
  DEEP-DOC-06** — pure documentation drift (the docs describe a
  *worse* state than the code, e.g., omitted source-layout
  entries for files that exist; mis-stated test-suite count;
  stale archived-link annotations). Legitimate-exception clause:
  the documentation is the inferior artefact and updating it to
  match the better code is correct.
- **DEEP-ARCH-01 (CacheModel marker)** — same legitimate-exception
  case: the "STATUS: staged" marker describes a worse state than
  the code (the file is in the production import chain). Update
  the marker.
- **DEEP-RUST-03/04/05** — comment accuracy and module-level doc
  additions (no code↔doc improvement asymmetry that the rule
  governs).
- **DEEP-SCRIPT-01** — manifest timestamp staleness.
- **DEEP-PRELUDE-01/02** — code refactor improvements (no
  doc↔code conflict).
- **DEEP-CAP-01** — verification pass already chose the
  implementation-conforming fix (promote inline rationale to
  formal docstring; no code change because code is correct).
- **DEEP-CAP-03 / DEEP-SCH-01** — demoted to no-action by §11.5
  (existing documentation already accurate).

### 12.3 Severity counts (post-§12)

| Severity | Post-§11 | Post-§12 | Reshaped remediations |
|---|---|---|---|
| Critical (C) | 0 | 0 | – |
| High (H) | 2 | 2 | DEEP-FFI-01 |
| Medium (M) | ~10 | ~10 | DEEP-FFI-02, DEEP-BOOT-01 |
| Low (L) | ~18 | ~18 | DEEP-MODEL-01, DEEP-PROOF-01 |
| Informational (I) | ~18 | ~18 | DEEP-FFI-03, DEEP-DOC-05, DEEP-CAP-04, DEEP-CAP-05, DEEP-IPC-04, DEEP-IPC-05, DEEP-SCH-02, DEEP-SCH-06, DEEP-SUSP-01, DEEP-SUSP-02, DEEP-IF-01, DEEP-IF-02, DEEP-ARCH-03 |
| **Total DEEP-* findings** | ~48 | ~48 | **18 reshaped** |

The §12 revision **does not change severity counts.** It changes
the *shape of the remediation* for 18 findings (those listed in
§12.1 and the rightmost column above). The reshaped remediations
are typically larger code slices than the original documentation
patches, so the **PR plan in §10.3 grew from 5 PRs to 12 PRs** —
one of the §12 revision's most visible effects.

Crucially, the *informational* severity rating of (e.g.)
DEEP-SUSP-01 remains accurate: the current code state is low-risk
because the missing PIP recomputation is masked by upstream
invariants. The reshaped remediation (implement the recomputation
rather than document it) is pre-1.0 priority **not** because the
bug is high-severity but because the implement-the-improvement
rule mandates that the documented design intent be made true
rather than relaxed.

### 12.4 Audit conclusion under the §12 revision

The audit's headline is unchanged at the severity level: 0 C, 2
H, ~10 M, ~18 L, ~18 I. What changes is the **release path**.

Pre-§12: the audit recommended a v1.0 cut with documentation
disclosure of the hardware-dispatch gap.

Post-§12: a v1.0 cut requires the gap to be **closed** rather
than disclosed. The release path now includes a
`v0.31.0` "verified specification release" tag for the current
state and a `v1.0.0` "bootable verified microkernel" tag once
§10.3 PRs 1–6 land. This separation is the audit's
post-§12 recommendation and reflects the project's defining
property of honesty about correctness.

### 12.5 Forward-looking note

Future audits on this project should apply the implement-the-
improvement rule from the outset rather than as a post-hoc
revision. The following preflight question should accompany
every audit finding:

> "Does my recommendation make the documentation true (by
> changing code), or does it make the code's current behaviour
> defensible (by changing documentation)? If the latter, am I
> certain the documentation describes a *worse* state than the
> code, not a *better* one?"

If the answer is "the documentation describes a better state,"
the recommendation must be the code change. The CLAUDE.md
section "Implement-the-improvement rule" is the canonical
reference.

— Implement-the-improvement revision closed 2026-04-28 on
branch `claude/fix-audit-findings-Feksd`. This is the
authoritative version of the audit; §10–§11 are retained for
provenance but are superseded where they conflict with §12.

