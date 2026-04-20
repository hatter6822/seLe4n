# Audit v0.29.0 — Errata and Clarifications

**Parent audit:** [`AUDIT_v0.29.0_COMPREHENSIVE.md`](AUDIT_v0.29.0_COMPREHENSIVE.md)
**Plan:** [`AUDIT_v0.29.0_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md) (archived in `docs/dev_history/audits/` after WS-AK closure)
**Workstream:** WS-AK Phase AK10 (Closure)
**Status:** Closed under v0.30.6 (AK10-D).

This document records errata and clarifications surfaced during the WS-AK
workstream implementation pass (AK1..AK10). None of the entries below invalidate
the audit's core findings; each is an informational correction of audit-text
wording, scope description, or arithmetic.

---

## E-1 — S-H03 verification clarification

**Audit text (excerpted from finding S-H03):**

> "`schedContextBind` must re-enqueue the bound thread at
> `effectiveRunQueuePriority tcb` rather than `resolveInsertPriority`."

**Status:** **No errata — audit finding stands.**

**Clarification:** Initial verification of the AK2-A fix (v0.29.2) confused
two distinct helpers:

- `resolveInsertPriority` is the correct production re-enqueue entry point
  for `schedContextBind` and `schedContextConfigure`. It delegates to
  `effectiveRunQueuePriority tcb` under the PIP-propagation invariant.
- `effectiveRunQueuePriority tcb` is the correct semantic quantity at the
  four production re-enqueue sites (`handleYield`, `timerTick`,
  `timerTickBudget` unbound, `switchDomain`).

The AK2-A implementation correctly uses `resolveInsertPriority` at bind/
configure and `effectiveRunQueuePriority` at the four scheduler sites;
under the post-AK2-A propagation invariant these agree. Audit text
correctly identifies the behavioural requirement; no correction needed.

---

## E-2 — R-HAL-M12 dead-code removal (supersedes AK5-K's "defensive fall-through")

**Audit text (excerpted from finding R-HAL-M12):**

> "SError handlers return via ERET after `handle_serror` despite the
> handler being `-> !`."
>
> *Remediation:* make signature `-> !` and `b .` after `bl` in asm.

**Status:** **Finding RESOLVED. Dead-code removal landed in AK10.**

**Clarification:** AK5-K initially took half the remediation: it
changed `handle_serror`'s signature from `-> ()` to `-> !`, but left
the now-unreachable `restore_context` macro call after `bl
handle_serror` in place and annotated it as a "defensive fall-through".

AK10 completes the remediation per the audit's original guidance. Both
`__el0_serror_entry` and `__el1_serror_entry` in
`rust/sele4n-hal/src/trap.S` now branch to `b .` (branch-to-self
infinite loop) after `bl handle_serror`. This:

1. Deletes genuinely dead code from the kernel image (the optimizer
   already dropped the unreachable `restore_context` under `-> !`,
   but the source now matches reality).
2. Provides a stronger defensive posture than the prior
   `restore_context` fall-through: if the `-> !` divergence contract
   were ever relaxed by a future refactor, the core halts in place
   rather than attempting an `ERET` with an SError-corrupted context.

`handle_serror` itself is unchanged — it still declares `-> !` and
contains `loop { cpu::wfe() }`. The `b .` after the `bl` is only
reachable in pathological paths; normal operation terminates inside
`handle_serror` under WFE.

---

## E-3 — A-H01 layering extends to three layers

**Audit text (excerpted from finding A-H01):**

> "`fromPagePermissions` must refuse W+X. Currently emits descriptors
> with `AP[0]=W` and `XN=0`."

**Status:** **Finding stands. Scope extends to THREE layers, not one.**

**Clarification:** The audit §7.5 locates the W^X gap at
`fromPagePermissions` only. The AK3-B remediation discovered that the
defense must be threaded through three independent layers:

1. `ARMv8VSpace.mapPage` wrapper in
   `SeLe4n/Kernel/Architecture/VSpaceARMv8.lean` — refuses W+X at the
   backend boundary.
2. `VSpaceRoot.mapPage` in `SeLe4n/Kernel/Architecture/VSpace.lean` —
   refuses W+X at the model layer.
3. `fromPagePermissions` in `PageTable.lean` — refuses W+X at the
   descriptor-encode layer.

AK5-C completes a fourth layer at hardware level (`SCTLR.WXN = 1`). The
composition theorem `wxInvariant_fourLayer_defense` documents all four
gates. The audit finding is correct in substance; its scope was
understated.

---

## E-4 — R-HAL-H02 partial: DSB/ISB present, TLB flush + D-cache clean missing

**Audit text (excerpted from finding R-HAL-H02):**

> "MMU enable lacks the ARM ARM D8.11 ordering (`tlbi vmalle1` → D-cache
> clean → MMU enable)."

**Status:** **Finding stands. Scope clarification: DSB ISH + ISB already
present; what was missing is `tlbi vmalle1` and D-cache clean of the PT
pages.**

**Clarification:** Prior to AK5-D, `enable_mmu` issued DSB ISH + ISB
correctly but omitted the two prerequisites mandated by the ARM ARM:

1. `tlbi vmalle1` — flushes stale TLB entries that may have been
   populated under non-zero SCTLR_EL1 state during boot.
2. D-cache clean over the boot L1 table — ensures the table walker
   observes the programmed descriptors after the Point-of-Coherency
   clean.

AK5-D now emits the full `tlbi vmalle1` → `dc cvac (BOOT_L1_TABLE)` →
TCR/MAIR/TTBR program → DSB ISH + ISB → SCTLR write → ISB sequence.
See `cache::clean_pagetable_range` helper.

---

## E-5 — NI-H02 structure: per-op preservation exists; composition is what was missing

**Audit text (excerpted from finding NI-H02):**

> "The projection-preservation obligation on `dispatchCapabilityOnly` is
> implicit; callers of `syscallDispatchHigh` must supply `hArmProj`."

**Status:** **Finding stands. Scope clarification: every per-op
`*_preserves_projection` theorem exists. What was missing is the
composition theorem that discharges `hArmProj` internally.**

**Clarification:** The 11 cap-only dispatch arms (`.cspaceDelete`,
`.lifecycleRetype`, `.vspaceMap`, `.vspaceUnmap`, `.serviceRevoke`,
`.serviceQuery`, `.schedContextConfigure/Bind/Unbind`, `.tcbSuspend/
Resume`) each have a per-op `_preserves_projection` theorem. Prior to
AK6-F, the aggregation over all 11 arms was an implicit caller
obligation at `syscallDispatchHigh`. AK6-F introduces
`dispatchCapabilityOnly_preserves_projection` in
`SeLe4n/Kernel/API.lean` composing the 11 per-op witnesses into a
single projection-preservation conclusion; callers no longer need to
supply a per-arm witness. The audit finding correctly identifies the
structural gap; its scope was non-obvious from the text.

---

## E-6 — Finding-count arithmetic: 202, not 201

**Audit text (excerpted from §2 summary):**

> "2 CRITICAL + 23 HIGH + 68 MEDIUM + 108 LOW = 201 findings."

**Status:** **Informational. Correct totals: 2 + 23 + 76 + 101 = 202
findings.**

**Clarification:** Enumerating IDs across subsystem notes yields the
following:

| Severity | Sum | Breakdown by subsystem |
|----------|-----|-------------------------|
| CRITICAL | 2   | A-C01, R-ABI-C01 |
| HIGH     | 23  | I-H01, I-H02, S-H01..H04, A-H01..H03, R-HAL-H01..H05, F-H01..H02, NI-H01..H02, SC-H01, P-H01..H02, R-ABI-H01..H02 |
| MEDIUM   | 76  | F: 11, S: 8, I: 7, C: 7, A: 10, NI: 2, SC: 4, DS: 4, P: 7, R-HAL: 12, R-ABI: 4 |
| LOW      | 101 | F: 15, S: 6, I: 6, C: 10, A: 9, NI: 4, SC: 3, DS: 11, P: 13, R-HAL: 16, R-ABI: 8 |
| **TOTAL**| **202** | |

The plan's §13 Phase AK10 addresses every enumerated ID. The §2
summary's 68/108 subtotals aggregate against sub-subsystem categories
whose boundaries differ from the per-finding subtotal used here; no
finding was added or removed. This is recorded for historical
traceability only.

---

## Closure

All errata above are informational. The WS-AK workstream implementation
(v0.29.1..v0.30.6) honours the intent of the audit's 202 findings;
where audit-text wording understated or overstated a finding's scope,
the implementation tracked to the substantive requirement and the
errata entry records the terminology delta.
