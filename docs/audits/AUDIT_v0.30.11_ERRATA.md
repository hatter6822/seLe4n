# AUDIT v0.30.11 — Errata

This file records audit-text corrections discovered during WS-RC
remediation planning and execution. Per the audit lifecycle (see
`docs/audits/README.md`), errata files accumulate during a
workstream's life and ship with the workstream's archived bundle.

## E-1 — DEEP-ARCH-01 verification rationale incorrect

**Source:** `AUDIT_v0.30.11_DEEP_VERIFICATION.md` §11.3 (DEEP-ARCH-01
narrowing).

**Original claim.** "CacheModel: imported by `Platform/Staged.lean`,
`Architecture/TlbCacheComposition.lean`, AND
`Architecture/BarrierComposition.lean`. `BarrierComposition` is
imported by `Architecture/TlbModel.lean`, which is imported by
`SeLe4n.lean` (the production library entry point). So CacheModel
**is** in the production chain. Marker is misleading."

**Verification.** Direct source inspection at v0.30.11 HEAD:

```
$ grep "^import" SeLe4n/Kernel/Architecture/BarrierComposition.lean
(returns no lines — file has zero imports)
```

`BarrierComposition.lean` has **no imports**. The audit's claimed
import chain `BarrierComposition → CacheModel` does not exist.

A full transitive-closure trace from `SeLe4n.lean` (the production
library entry point) reaches **144 modules** (see Appendix A of
`AUDIT_v0.30.11_WORKSTREAM_PLAN.md`). The set does **not** include:
- `SeLe4n.Kernel.Architecture.CacheModel`
- `SeLe4n.Kernel.Architecture.TimerModel`
- `SeLe4n.Kernel.Architecture.ExceptionModel`
- `SeLe4n.Kernel.Architecture.TlbCacheComposition`

These four modules are reachable **only** via `Platform/Staged.lean`
(the staging anchor). All three "STATUS: staged" markers
(CacheModel, TimerModel, ExceptionModel) are therefore correct.

**Disposition.** DEEP-ARCH-01 is **withdrawn as an active finding**.
The structural enforcement of the production/staged partition
(eliminating the auditor-error class that produced this finding)
lands in WS-RC R12.B as a CI gate that machine-checks the
partition at every build.

**Cross-references.**
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §2.2 (errata recording)
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` Appendix A (full trace)
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §16.3 (R12.B gate design)

## E-2 — DEEP-ARCH-02 consumer count incorrect

**Source:** `AUDIT_v0.30.11_DEEP_VERIFICATION.md` §11.1 (DEEP-ARCH-02
withdrawal verification).

**Original claim.** "Direct verification: every one of the 11
`_fields` definitions has 3 to 26 active consumers in the kernel.
False positive."

**Verification.** Direct re-grep at WS-RC R0 prep time:

| Definition | In-file consumers | Out-of-file consumers |
|---|---|---|
| `registryEndpointValid_fields` | 4 | 0 |
| `registryInterfaceValid_fields` | 3 | 0 |
| `registryDependencyConsistent_fields` | 5 | 0 |
| `noStaleEndpointQueueReferences_fields` | 5 | 0 |
| `noStaleNotificationWaitReferences_fields` | 5 | 0 |
| `serviceGraphInvariant_fields` | 5 | 0 |
| `schedContextStoreConsistent_fields` | 4 | 0 |
| `schedContextNotDualBound_fields` | 4 | 0 |
| `schedContextRunQueueConsistent_fields` | 4 | 0 |
| `blockingAcyclic_fields` | 3 | 0 |
| `lifecycleObjectTypeLockstep_fields` | 3 | 0 |

The deep audit's cited 3-26 consumer counts were for the underlying
predicate names (e.g., `registryEndpointValid` — 16 consumers
across the kernel), **not** for the `_fields` metadata defs. The
metadata defs are file-local helpers used only via `fieldsDisjoint`
calls within `CrossSubsystem.lean`.

**Disposition.** DEEP-ARCH-02 is **still withdrawn as a finding**
(the defs are not dead code — they have in-file consumers), but
the rationale is corrected. The R12.D CI gate's design is updated
to count total hits (in-file + out-of-file ≥ 2, where 1 is the
def itself), not out-of-file consumers only.

**Cross-references.**
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §2.1 (false-positive table)
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §16.5 (R12.D gate design)

## E-3 — DEEP-RUST-01/02 partial verification

**Source:** `AUDIT_v0.30.11_DEEP_VERIFICATION.md` §11.1 (DEEP-RUST-01,
DEEP-RUST-02 withdrawal verifications).

**Original claim.** Both findings withdrawn on grounds that "every
MMIO unsafe block cites (ARM ARM B2.1)" and "mrs/msr asm! blocks
cite (ARM ARM C5.2)".

**Verification.** Direct gate-prototype run at WS-RC R0 prep time:
the audit's verification was correct **only for the MMIO and asm!
subset**. The HAL contains 53 unsafe blocks total; 20 of them are
**not** MMIO/asm! (e.g., `unsafe impl Sync` for `UnsafeCell`
wrappers, `unsafe fn` boundary helpers with single-threaded
preconditions). These 20 blocks correctly use `// SAFETY:` comments
per the Rust idiom but do not cite ARM ARM sections.

**Disposition.** Both DEEP-RUST-01 and DEEP-RUST-02 remain
**withdrawn as findings** for the hardware-access (MMIO, asm!)
subset. The R12.C CI gate's design is refined to a **two-tier
rule**:
- Tier 1 (universal): every unsafe block/fn/impl needs a `// SAFETY:`
  comment within 5 preceding lines.
- Tier 2 (hardware-access subset): blocks containing
  `read_volatile`, `write_volatile`, or `asm!` additionally need
  an `(ARM ARM <section>)` citation within 5 preceding lines.

The deep audit's verification covered only Tier 2.

**Cross-references.**
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §2.1 (false-positive table)
- `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §16.4 (R12.C gate design)

## E-4 — Plan internal corrections (non-audit)

The following corrections to `AUDIT_v0.30.11_WORKSTREAM_PLAN.md`
were applied during WS-RC R0 prep based on direct verification
against the v0.30.11 HEAD source tree:

| Plan section | Original claim | Corrected fact |
|---|---|---|
| R3.3 | `PlatformConfig` lives in `Platform/Contract.lean` | Lives in `Platform/Boot.lean:81`. `Contract.lean` defines the `PlatformBinding` typeclass. |
| R3.1 | `bootSafeObject` returns `Bool` at line 551 | Two functions: `bootSafeObjectCheck : Bool` at line 534 (line 551 is the VSpaceRoot arm) and `bootSafeObject : Prop` at line 1456. Both must be updated. |
| R3.1 | `bootSafeVSpaceRoot` returns `Bool` | Returns `Prop` at `RPi5/VSpaceBoot.lean:273`. The Bool variant requires `decide`. |
| R4.B | `RetypeTarget` fields are `obj : KernelObject`, `h : afterScrub obj` | Actual fields: `id : ObjId`, `cleanupHookDischarged : ...` (parameterized by `st : SystemState`). |
| R4.B | Add `mkRetypeTarget` smart constructor | Structure already has the smart-constructor shape; the improvement is to **strengthen the predicate** via an opaque `ScrubToken` (per refined R4.B). |
| R2.B.1 | `syscallDispatchFromAbi` decodes args itself | `syscallEntryChecked` already decodes via `decodeSyscallArgsFromState`; the FFI shim should populate the TCB's register context, not re-decode. |

Each correction is reflected in the corresponding plan phase's
implementation walkthrough.

## Errata closure

This file is closed at WS-RC closure (along with the workstream
plan, baseline, discharge index, and deferred files). New errata
discovered after WS-RC opens should append to this file as E-N+1.
