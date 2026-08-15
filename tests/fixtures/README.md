# Test fixtures

This directory holds **golden output** files used by the kernel test
suite to detect unintended behavioural changes in the trace-emitting
test executables.  Each `.expected` file has a paired `.sha256` companion
that the Tier 2 trace gate (`scripts/test_tier2_trace.sh`) verifies on
every CI run; the gate refuses to compare a fixture whose hash does not
match its companion, forcing every fixture edit to be paired with an
explicit hash refresh in the same commit.

## Files

| Fixture | Hash | Used by |
| --- | --- | --- |
| `main_trace_smoke.expected` | `main_trace_smoke.expected.sha256` | `scripts/test_tier2_trace.sh` (compares `lake exe sele4n` output) |
| `robin_hood_smoke.expected` | `robin_hood_smoke.expected.sha256` | `tests/RobinHoodSuite.lean` |
| `two_phase_arch_smoke.expected` | `two_phase_arch_smoke.expected.sha256` | `tests/TwoPhaseArchSuite.lean` |
| `smp_4core_scheduler.expected` | `smp_4core_scheduler.expected.sha256` | `tests/SmpSchedulerSuite.lean` (WS-SM SM5.K.4 — the deterministic 4-thread/4-core per-core scheduler trace + the multi-step cross-core wake→SGI→handler round-trip, verified byte-for-byte against the live `chooseThreadOnCore` / `determineTargetCore` / `wakeThread` / `switchToThreadOnCore` / `handleRescheduleSgiOnCore` decisions) |
| `smp_ipc_4core.expected` | `smp_ipc_4core.expected.sha256` | `tests/SmpIpcSuite.lean` (WS-SM SM6.F.4 — the deterministic 4-thread/4-core cross-core IPC trace: both client/server call→SGI→handler-dispatch→reply→SGI→handler-dispatch round trips plus the cross-core send/receive rendezvous, verified byte-for-byte against the live `endpointReceiveDualOnCore` / `endpointCallOnCore` / `endpointReplyOnCore` / `endpointSendDual` / `handleRescheduleSgiOnCore` decisions) |
| `smp_tlb_shootdown.expected` | `smp_tlb_shootdown.expected.sha256` | `tests/SmpTlbShootdownSuite.lean` (WS-SM SM7.E.6 — the deterministic 4-core TLB shootdown trace: a live map + translation-walk fill on core 1, a cross-core unmap from core 0 posting a covering round, and the deferred catch-up draining every target, plus the four-core concurrent-unmap storm and the cross-cluster domain identity, verified byte-for-byte against the live `vspaceMapPageCheckedWithShootdownFromStatePerCore` / `vspaceUnmapPageWithShootdownPerCore` / `shootdownCatchUpPerCore` / `handleTlbShootdownReqOnCorePerCore` decisions.  Each line reports per-core observables — cached entries, pending descriptors, ack flags, and the pending-aware invariant verdict — so any change in the shootdown semantics diverges the fixture) |
| `smp_declassification_audit.expected` | `smp_declassification_audit.expected.sha256` | `tests/SmpInformationFlowSuite.lean` (WS-SM SM8.C.7 — the deterministic declassification-audit trace: a run of authorized downgrades through the live `.declassify` transition and the mounted trail, reporting each recorded entry's core, domains, target and basis, the per-core partition of the log, and the three fail-closed refusals — unconfigured policy, idle core, absent target) |
| `smp_fine_lock_contention.expected` | `smp_fine_lock_contention.expected.sha256` | `tests/SmpInformationFlowSuite.lean` (WS-SM SM8.D.6 — the deterministic lock-contention trace: the per-object lock erased from every core's projection, a real contended execution with its delay, wait depth and channel code, the blocked reader's temporal figures, both integrity directions, and the two bracketed live syscall entries) |
| `smp_information_flow.expected` | `smp_information_flow.expected.sha256` | `tests/SmpInformationFlowSuite.lean` (WS-SM SM8.E.2 — the phase-level information-flow trace: what an observer at `(core, label)` sees of the four-thread/four-core fixture, per-core independence, CNode slot redaction across three clearances, a live high-object signal and its low-object negative control, the cross-core write sets, and the sizes of the enforcement boundary, the non-interference coverage and the accepted covert-channel inventory) |

The Tier 2 trace gate (`scripts/test_tier2_trace.sh`) walks every
`*.expected.sha256` file in this directory and runs `sha256sum -c` on
the full set in a single invocation, so a missing or stale hash for any
fixture fails CI with a uniform remediation message.

## Regeneration workflow (when a fixture changes intentionally)

1. Run the affected suite locally and confirm the new output is what you
   intend.  For the main trace fixture:

   ```bash
   source ~/.elan/env
   lake exe sele4n > tests/fixtures/main_trace_smoke.expected
   ```

   For the secondary suites:

   ```bash
   lake exe robin_hood_suite      # writes to robin_hood_smoke.expected
   lake exe two_phase_arch_suite  # writes to two_phase_arch_smoke.expected
   ```

   For the SMP 4-core scheduler trace fixture (WS-SM SM5.K.4), extract only
   the `[smp-4core]` trace lines the aggregate suite emits.  The brackets
   MUST be escaped — unescaped, `[smp-4core]` is a regex character class
   that also matches the suite's `---` section headers and would corrupt
   the regenerated fixture:

   ```bash
   lake exe smp_scheduler_suite | grep '^\[smp-4core\]' \
     > tests/fixtures/smp_4core_scheduler.expected
   ```

   For the SMP 4-core cross-core IPC trace fixture (WS-SM SM6.F.4), the
   same escaping rule applies to its `[smp-ipc-4core]` tag:

   ```bash
   lake exe smp_ipc_suite | grep '^\[smp-ipc-4core\]' \
     > tests/fixtures/smp_ipc_4core.expected
   ```

   For the SMP TLB shootdown trace fixture (WS-SM SM7.E.6), the same
   escaping rule applies to its `[smp-tlb-shootdown]` tag:

   ```bash
   lake exe smp_tlb_shootdown_suite | grep '^\[smp-tlb-shootdown\]' \
     > tests/fixtures/smp_tlb_shootdown.expected
   ```

   The information-flow suite emits **three** fixtures, one per tag, and
   the same escaping rule applies to each (WS-SM SM8.C.7 / SM8.D.6 /
   SM8.E.2):

   ```bash
   lake exe smp_information_flow_suite | grep '^\[smp-declassification\]' \
     > tests/fixtures/smp_declassification_audit.expected
   lake exe smp_information_flow_suite | grep '^\[smp-fine-lock\]' \
     > tests/fixtures/smp_fine_lock_contention.expected
   lake exe smp_information_flow_suite | grep '^\[smp-information-flow\]' \
     > tests/fixtures/smp_information_flow.expected
   ```

2. Recompute the SHA-256 companion in the format `sha256sum` writes by
   default (`<hash>  <basename>`):

   ```bash
   cd tests/fixtures
   sha256sum main_trace_smoke.expected      > main_trace_smoke.expected.sha256
   sha256sum robin_hood_smoke.expected      > robin_hood_smoke.expected.sha256
   sha256sum two_phase_arch_smoke.expected  > two_phase_arch_smoke.expected.sha256
   sha256sum smp_4core_scheduler.expected   > smp_4core_scheduler.expected.sha256
   sha256sum smp_ipc_4core.expected         > smp_ipc_4core.expected.sha256
   sha256sum smp_tlb_shootdown.expected     > smp_tlb_shootdown.expected.sha256
   sha256sum smp_declassification_audit.expected \
     > smp_declassification_audit.expected.sha256
   sha256sum smp_fine_lock_contention.expected \
     > smp_fine_lock_contention.expected.sha256
   sha256sum smp_information_flow.expected  > smp_information_flow.expected.sha256
   ```

3. Verify both files agree:

   ```bash
   cd tests/fixtures
   sha256sum -c main_trace_smoke.expected.sha256 \
                robin_hood_smoke.expected.sha256 \
                two_phase_arch_smoke.expected.sha256
   ```

4. Commit BOTH the `.expected` and the `.expected.sha256` files in a
   single commit.  Include in the commit message:

   * a one-sentence description of the behavioural change that drove the
     fixture update,
   * a cross-reference to the workstream / audit ID responsible
     (e.g. `WS-AN AN11-C`).

## Design rationale

The hash companion exists because golden-output files are easy to commit
without realising the diff:  a tab-vs-space change, a re-ordered field,
or an `IO.println` reorder will silently shift the trace.  Pairing each
fixture with a hash forces the author to acknowledge the change exists
and lets reviewers spot it without scrolling through hundreds of trace
lines.

The hash format matches `sha256sum`'s default output (`<hash>  <name>`)
so that `sha256sum -c <companion>` works without flags or a custom
parser.  The trace gate runs `sha256sum -c` in the same invocation for
every companion in this directory, producing a uniform remediation
message regardless of which fixture drifted.
