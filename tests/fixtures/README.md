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

2. Recompute the SHA-256 companion in the format `sha256sum` writes by
   default (`<hash>  <basename>`):

   ```bash
   cd tests/fixtures
   sha256sum main_trace_smoke.expected      > main_trace_smoke.expected.sha256
   sha256sum robin_hood_smoke.expected      > robin_hood_smoke.expected.sha256
   sha256sum two_phase_arch_smoke.expected  > two_phase_arch_smoke.expected.sha256
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
