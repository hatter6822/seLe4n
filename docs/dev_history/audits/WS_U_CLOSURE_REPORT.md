# WS-U Closure Report — v0.20.7 Audit Remediation

**Workstream**: WS-U (v0.20.7 Comprehensive Audit Remediation)
**Version range**: v0.21.0–v0.21.7
**Created**: 2026-03-25
**Status**: PORTFOLIO COMPLETE

---

## 1. Executive Summary

WS-U addressed all actionable findings from four v0.20.7 comprehensive audits:
- `AUDIT_COMPREHENSIVE_v0.20.7_FULL_CODEBASE.md` (5 HIGH, 26 MEDIUM, 33 LOW)
- `AUDIT_COMPREHENSIVE_v0.20.7_KERNEL_IMPLEMENTATION.md` (2 HIGH, 22 MEDIUM, 60+ LOW)
- `AUDIT_COMPREHENSIVE_v0.20.7_PRE_RELEASE.md` (13 HIGH, 37 MEDIUM, 43 LOW)
- `audit_findings_provided_by_me.md` (user-reported findings)

After cross-referencing and deduplication: **14 HIGH**, **39 MEDIUM**, **28 LOW**
confirmed findings. **12 erroneous findings** were identified and excluded.

**8 phases**, **97+ sub-tasks** across versions v0.21.0–v0.21.7. All 14 HIGH,
all 39 MEDIUM, and all 28 selected LOW findings resolved. Zero sorry/axiom
across the entire production proof surface.

**No CVE-worthy vulnerabilities were discovered** in any audit.

---

## 2. Phase Summary

| Phase | Version | Scope | Sub-tasks | Status |
|-------|---------|-------|-----------|--------|
| U1 | v0.21.0 | Correctness Fixes | 13 | COMPLETE |
| U2 | v0.21.1 | Safety Boundary Hardening | 14 | COMPLETE |
| U3 | v0.21.2 | Rust ABI Hardening | 10 | COMPLETE |
| U4 | v0.21.3 | Proof Chain & Invariant Composition | 3 groups | COMPLETE |
| U5 | v0.21.4 | API & Dispatch Integrity | 14 | COMPLETE |
| U6 | v0.21.5 | Architecture & Platform Fidelity | 12 | COMPLETE |
| U7 | v0.21.6 | Dead Code & Proof Hygiene | 12 | COMPLETE |
| U8 | v0.21.7 | Documentation & Closure | 8 | COMPLETE |
| **Total** | | | **~97** | |

---

## 3. Erroneous Finding Registry

12 findings were reported by one or more audits but determined to be incorrect
after verification against the actual codebase. They were excluded from
remediation. See Section 2 of `AUDIT_v0.20.7_WORKSTREAM_PLAN.md` for full
details and verification evidence.

Key erroneous findings:
- `readBE32` bounds-check already present (M-08, AR-12)
- GIC base addresses within declared device region (AR-07)
- Duplicate frame lemmas are distinct properties (M-11)
- GIC CPU interface size correct per ARM spec (User)
- CSpace cross-CNode operations work correctly (User)
- `handleYield` semantics match seL4 (S-05)
- Simulation boot contracts trivially True by design (P-04)

---

## 4. HIGH Finding Resolution (14/14)

| ID | Subsystem | Resolution | Phase |
|----|-----------|------------|-------|
| U-H01 | FrozenOps | `frozenQueuePopHead` clears `queuePPrev`; re-enqueue enabled | U1 |
| U-H02 | Lifecycle | Watermark alignment re-verified after advance | U1 |
| U-H03 | Lifecycle | Compile-time `revokeBeforeDelete` enforcement | U1 |
| U-H04 | API | Lifecycle dispatch routed through cleanup/scrub pipeline | U1 |
| U-H05 | Architecture | Access restriction + TLB flush documentation | U2 |
| U-H06 | Architecture | VAddr bounds-checked against 2^48 | U2 |
| U-H07 | Architecture | Platform-specific PA width validation | U2 |
| U-H08 | Architecture | ASID bounds-checked against `maxASID` | U2 |
| U-H09 | InfoFlow | `hProjection` hypotheses discharged for 4 IPC ops | U4 |
| U-H10 | InfoFlow | `NonInterferenceStep` completeness enforcement | U2 |
| U-H11 | Rust | Clobber registers declared in inline asm | U3 |
| U-H12 | RobinHood | `BEq RHTable` made symmetric with reverse fold | U7 |
| U-H13 | IPC | Sender CSpace root fallback returns error | U1 |
| U-H14 | Capability | Retype right mismatch fixed (`.retype` consistent) | U1 |

---

## 5. MEDIUM Finding Resolution (39/39)

All 39 MEDIUM findings resolved across phases U1–U7. Key categories:

- **API dispatch integrity** (U-M01 through U-M07): Checked vs unchecked
  dispatch equivalence proved, enforcement wrappers added.
- **Architecture hardening** (U-M08 through U-M15): MMIO abstraction
  boundary, runtime contract strengthening, boot validation, GIC
  register access ops.
- **Information flow** (U-M22 through U-M24): BIBA direction documented,
  service registry NI gap documented, covert channels documented.
- **Design documentation** (U-M25 through U-M35): Badge-0, message
  handling, notification overwrite, slot 0, GrantReply, CDT tracking,
  hash collision assumptions — all documented.

---

## 6. LOW Finding Resolution (28/28)

All 28 selected LOW findings resolved across phases U5–U8. Key categories:

- **Dead code removal** (U7): KMap module, dead types/functions, trivial
  tautology theorems, superseded invariant bundles.
- **TCB reduction** (U7): 5 `native_decide` → `decide` migrations.
- **Platform documentation** (U8): IRQ/INTID range, notification overflow,
  scheduler starvation, hash collision assumptions.
- **Code deduplication** (U8): `simSubstantiveMemoryMap` unified with
  compile-time consistency theorem.

---

## 7. Items Deferred to WS-V (Hardware Binding)

The following items were identified during WS-U but are deferred to the
hardware binding workstream (WS-V):

1. **Notification 64-bit word width enforcement** (U-L24 documentation):
   Model uses unbounded Nat. Platform boundary must mask to 2^64 - 1.
2. **Extended GIC SPIs** (U-L18/L19): BCM2712 may expose INTIDs > 223
   on future revisions. `gicSpiCount` must be validated against datasheet.
3. **SGI handling** (U-L18): SGIs (INTIDs 0–15) should not be wired to
   device drivers. Kernel IRQ dispatch must filter SGIs appropriately.
4. **TLB flush hardware integration** (U-H05): Model has flush operations;
   hardware binding must implement ARM64 TLBI instructions.
5. **MCS scheduling extensions**: Starvation prevention delegated to
   user-level policy (documented in U-L26).
6. **`notificationSignal` syscall wiring**: Mentioned in docstrings but
   intentionally deferred from `SyscallId` enum (per erroneous finding
   registry).

---

## 8. Validation Evidence

- `test_full.sh`: PASS (all tiers 0–3)
- `NIGHTLY_ENABLE_EXPERIMENTAL=1 test_nightly.sh`: PASS (tier 4 determinism)
- `rg -w sorry SeLe4n/ Main.lean`: zero matches
- `rg -w axiom SeLe4n/ Main.lean`: zero matches (excluding `Lean.axiomVal`)
- `lake build`: 168 modules, zero errors, zero warnings

---

## 9. Metrics Snapshot (v0.21.7)

| Metric | Value |
|--------|-------|
| **Production LoC** | 64,229 across 100 files |
| **Test LoC** | 8,316 across 10 test suites |
| **Proved declarations** | 1,878 theorem/lemma declarations |
| **Module count** | 110 |
| **Declaration count** | 3,421 |
| **Zero sorry/axiom** | Confirmed |

---

## 10. Conclusion

WS-U is the largest remediation workstream in seLe4n's history, addressing
findings from four independent comprehensive audits. All 14 HIGH, 39 MEDIUM,
and 28 LOW findings have been resolved. 12 erroneous findings were identified
and documented. The codebase is now ready for the next milestone: Raspberry Pi 5
hardware binding (WS-V).
