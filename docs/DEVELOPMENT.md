# seLe4n Development Guide

## 1. Purpose

This guide describes the expected engineering workflow for seLe4n contributors.

The project currently sits at **post-M3 seed / pre-M3.5** and the main goal is to expand IPC in a
controlled way while preserving existing theorem surfaces.

Primary goals for day-to-day work:

- keep executable semantics readable and testable,
- preserve milestone theorem entrypoints,
- land changes in narrowly scoped slices with clear acceptance evidence.

---

## 2. Current baseline and stability contract

The following behavior is considered stable and must not regress:

1. M1 scheduler invariant bundle (`schedulerInvariantBundle`) and associated preservation
   theorems.
2. M2 CSpace transition APIs (`lookup`, `insert`, `mint`, `delete`, `revoke`) and capability
   bundle preservation entrypoints.
3. M3 endpoint seed APIs (`endpointSend`, `endpointReceive`) and IPC invariant bundle entrypoints.
4. Runnable executable trace in `Main.lean` that already demonstrates scheduler + CSpace + IPC seed
   behavior.

If your change intentionally modifies one of these contracts, call it out explicitly in docs and PR
notes.

---

## 3. Active development target: M3.5 IPC handshake + scheduler interaction

### 3.1 Target outcomes for this slice

Contributors should align new work to these outcomes:

1. Refine endpoint protocol state so waiting directions are explicit.
2. Introduce minimal blocking/wakeup effects in endpoint transitions.
3. Add scheduler-facing coherence predicates for IPC-blocked threads.
4. Prove preservation theorems for new/changed transitions.
5. Keep proofs compositional with M1/M2/M3 bundles.
6. Extend executable trace with one concrete waiting-to-delivery scenario.

### 3.2 Non-goals for this slice

Do **not** include the following in M3.5 PRs unless explicitly approved:

- full reply-cap protocol,
- priority policy redesign,
- architecture/MMU concerns,
- full object retype lifecycle semantics.

---

## 4. Recommended implementation sequence (for M3.5)

Follow this order unless a dependency forces a small adjustment.

1. **State-model refinement first**
   - Introduce only the endpoint/thread state needed for one deterministic handshake story.
   - Keep field naming and ownership explicit.

2. **Transition updates second**
   - Update/add endpoint transitions with explicit success/error branches.
   - Keep transition code easy to unfold in proofs.

3. **Scheduler contract predicates third**
   - Define targeted predicates describing blocked-vs-runnable coherence.
   - Keep predicates local and avoid over-generalized abstractions.

4. **Invariant bundle composition fourth**
   - Add named IPC+scheduler coherence components.
   - Integrate into a composed bundle layered over existing `m3IpcSeedInvariantBundle` structure.

5. **Helper lemmas fifth**
   - Add lookup/update helper lemmas close to transitions.
   - Prefer small lemmas with direct transition relevance.

6. **Preservation theorems sixth**
   - Prove local invariants first, then composed-bundle preservation.
   - Keep theorem naming in `<transition>_preserves_<invariant>` form.

7. **Executable demonstration last**
   - Extend `Main.lean` with one concrete M3.5 scenario.
   - Ensure prior demonstration sequence still runs as a prefix.

---

## 5. Proof engineering standards

1. Prefer explicit and stable theorem statements over clever tactics.
2. Keep conjunction-heavy invariants factored into named components.
3. Avoid global `simp` side effects; use local simp blocks.
4. Structure proofs in layers:
   - unfold transition,
   - split result cases,
   - apply local store/lookup lemmas,
   - discharge invariant components.
5. Keep helper lemmas near the transitions they support.
6. Do not introduce `axiom` or `sorry` in core modules.

---

## 6. Documentation responsibilities

Any PR that changes transitions, invariants, or milestone boundaries must update docs in the same
commit range:

1. `docs/SEL4_SPEC.md`: status, next slice outcomes, acceptance criteria.
2. `docs/DEVELOPMENT.md`: implementation sequence, workflow expectations, PR checklist.
3. `README.md`: stage summary and contributor verification loop.

If docs are intentionally deferred, state why and when they will be updated.

---

## 7. Contributor validation loop (required)

Run this minimum set before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

Keep these direct checks in your local loop when debugging specific failures:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
```

If any command cannot run due to environment constraints, report the constraint and its impact.

Default ownership for test and CI gate maintenance is shared by contributors touching
`Main.lean`, `SeLe4n/Kernel/API.lean`, `scripts/test_*.sh`, and fixture files under `tests/fixtures/`.

For fresh environments, run `./scripts/setup_lean_env.sh` once. Test scripts auto-source
`$HOME/.elan/env` when available so `lake` can be found in non-interactive shells.

---


## 7.1 Pull request CI enforcement (required)

Pull request CI now enforces the same required tiers used locally by calling repository scripts
from `.github/workflows/lean_action_ci.yml`:

- `tier_fast` job runs `./scripts/test_fast.sh`.
- `tier_smoke` job runs `./scripts/test_smoke.sh`.

Do not inline bespoke test commands in CI when updating gates; keep CI and local behavior aligned
by extending script entrypoints under `scripts/` first.

---

## 8. PR checklist (required)

Copy this checklist into the PR description:

- [ ] Scope is one coherent milestone slice.
- [ ] Transition APIs use explicit success/error branching.
- [ ] New invariant components are named and documented.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed.
- [ ] `lake exe sele4n` executed.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed.
- [ ] Docs updated in the same commit range.
- [ ] CI required-tier workflow jobs still call repository script entrypoints.
- [ ] Remaining proof debt is identified.

---


## 8.1 Fixture-backed smoke regression workflow (Tier 2)

Tier 2 is now active and required in `./scripts/test_smoke.sh`.

- Expected trace fragments live in `tests/fixtures/main_trace_smoke.expected`.
- `scripts/test_tier2_trace.sh` runs `lake exe sele4n` and enforces substring matching for every
  non-empty fixture line.
- On mismatch, failures are tagged with `[TRACE]` and list every missing expectation.

Intentional behavior change workflow:

1. Run `lake exe sele4n` and verify the new executable behavior is expected.
2. Update only stable semantic lines in `tests/fixtures/main_trace_smoke.expected`.
3. Re-run `./scripts/test_tier2_trace.sh` and `./scripts/test_smoke.sh`.
4. Explain fixture changes in the PR description.

## 9. Review heuristics for maintainers

Reviewers should verify:

1. Transition semantics are understandable without deep tactic archaeology.
2. Endpoint/scheduler coupling is minimal and justified.
3. Helper lemmas are scoped to transition behavior.
4. Invariant bundle growth remains incremental and compositional.
5. Executable trace evidence matches the claims in docs.
6. Milestone status and next-slice plan are internally consistent across docs.

---

## 10. Anti-patterns to avoid

- Bundling model redesign, protocol redesign, and major proof rewrites in one PR.
- Adding non-essential architecture detail during IPC-slice work.
- Hiding transition semantics behind abstractions that block straightforward unfolding.
- Claiming slice completion without theorem and executable evidence.
- Leaving milestone docs stale after API or theorem-surface changes.
