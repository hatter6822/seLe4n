# seLe4n Development Guide

## 1. Purpose

This guide defines the expected engineering workflow for seLe4n contributors.

Current project stage: **post-M3 seed / pre-M3.5 handshake completion**.

Primary contributor goals:

- keep executable semantics readable and testable,
- preserve milestone theorem entrypoints,
- land changes in narrow, reviewable slices,
- keep docs synchronized with implementation stage and next-slice planning.

---

## 2. Stage contract and baseline stability

The following behavior is stable and must not regress unless intentionally redesigned and documented.

1. M1 scheduler invariant bundle (`schedulerInvariantBundle`) and preservation theorem entrypoints.
2. M2 CSpace transition APIs (`lookup`, `insert`, `mint`, `delete`, `revoke`) and capability bundle
   preservation entrypoints.
3. M3 endpoint seed APIs (`endpointSend`, `endpointReceive`) and IPC invariant bundle entrypoints.
4. Runnable executable trace in `Main.lean` demonstrating scheduler + CSpace + IPC seed behavior.
5. Tier 0/1/2 required gates and Tier 3 full-suite invariant/doc-surface checks.

If a change intentionally adjusts one of these contracts, call it out in docs + PR notes.

---

## 3. Active development target (current slice): M3.5 IPC handshake + scheduler interaction

### 3.1 Current-slice target outcomes

Contributors should align M3.5 work to all outcomes below:

1. Refine endpoint protocol state so waiting directions are explicit.
2. Introduce minimal blocking/wakeup effects in endpoint transitions.
3. Add scheduler-facing coherence predicates for IPC-blocked threads.
4. Extend IPC invariant bundle with endpoint/scheduler coherence components.
5. Prove preservation theorem entrypoints for new/changed transitions.
6. Extend executable trace with one waiting-to-delivery scenario.

### 3.2 Current-slice non-goals

Do **not** include the following in M3.5 PRs unless explicitly approved:

- full reply-cap protocol,
- priority scheduling policy redesign,
- architecture/MMU concerns,
- object lifecycle/retype semantics (belongs to M4).

### 3.3 M3.5 recommended implementation sequence

Use this order unless a concrete dependency forces adjustment.

1. **State-model refinement first**
   - add only endpoint/thread fields needed for one deterministic handshake story,
   - keep state ownership clear.

2. **Transition updates second**
   - add/update endpoint transitions with explicit success/error branches,
   - preserve straightforward unfoldability for proofs.

3. **Scheduler contract predicates third**
   - define targeted blocked-vs-runnable coherence predicates,
   - avoid over-generalized abstraction.

4. **Invariant bundle composition fourth**
   - add named IPC+scheduler coherence components,
   - layer over `m3IpcSeedInvariantBundle`.

5. **Helper lemmas fifth**
   - add local store/lookup lemmas near transitions,
   - prefer small lemmas that discharge concrete proof obligations.

6. **Preservation theorems sixth**
   - prove local invariants first, composed bundles second,
   - use `<transition>_preserves_<invariant>` naming.

7. **Executable demonstration last**
   - extend `Main.lean` with a concrete M3.5 story,
   - preserve prior demonstration sequence as a prefix.

---

## 4. Next slice preparation (planned): M4 object lifecycle / retype safety

Contributors do not need to implement M4 in M3.5 PRs, but should avoid design choices that block it.

### 4.1 M4 target outcomes (planning baseline)

1. Executable lifecycle/retype transition surface.
2. Object identity and aliasing invariants.
3. Capability-object lifecycle coherence invariants.
4. Preservation theorem entrypoints for lifecycle transitions.
5. Executable + fixture evidence for lifecycle behavior.

### 4.2 Pre-M4 design guardrails

While working on M3.5:

- keep transition APIs typed and explicit,
- avoid embedding lifecycle assumptions into IPC-only predicates,
- preserve compositional bundle structure so M4 can layer cleanly.

---

## 5. Proof engineering standards

1. Prefer explicit theorem statements over brittle tactic cleverness.
2. Keep conjunction-heavy invariants factored into named components.
3. Avoid global `simp` side effects; use local simp blocks.
4. Structure proofs in layers:
   - unfold transition,
   - split result cases,
   - apply local helper lemmas,
   - discharge invariant components.
5. Keep helper lemmas near transitions they support.
6. Do not introduce `axiom` or `sorry` in core modules.

---

## 6. Documentation responsibilities

Any PR changing transitions, invariants, or milestone boundaries must update docs in the same
commit range:

1. `docs/SEL4_SPEC.md`: current + next slice definitions, outcomes, acceptance criteria.
2. `docs/DEVELOPMENT.md`: implementation sequence, workflow expectations, PR checklist.
3. `README.md`: stage snapshot and contributor verification loop.
4. `docs/TESTING_FRAMEWORK_PLAN.md` and/or `tests/scenarios/README.md` when testing workflow
   expectations change.

If docs are deferred, state why and when they will be updated.

---

## 7. Contributor validation loop (required)

Run this minimum set before opening a PR:

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
```

Direct checks for local debugging:

```bash
lake build
lake exe sele4n
rg -n "axiom|sorry|TODO" SeLe4n Main.lean
./scripts/test_full.sh
```

If any command cannot run due to environment limits, report the constraint and impact.

Default shared ownership of test/CI gates applies to contributors touching:

- `Main.lean`,
- `SeLe4n/Kernel/API.lean`,
- `scripts/test_*.sh`,
- `tests/fixtures/*`.

Pull-request CI enforces required gates through `.github/workflows/lean_action_ci.yml` by running
`./scripts/test_fast.sh` and `./scripts/test_smoke.sh` as separate required jobs.

For fresh environments, run `./scripts/setup_lean_env.sh` once. Test scripts auto-source
`$HOME/.elan/env` when available.

---

## 8. PR checklist (required)

Copy this checklist into PR descriptions:

- [ ] Scope is one coherent milestone slice.
- [ ] Transition APIs use explicit success/error branching.
- [ ] New invariant components are named and documented.
- [ ] Preservation theorem entrypoints compile.
- [ ] `lake build` executed.
- [ ] `lake exe sele4n` executed.
- [ ] Hygiene scan (`axiom|sorry|TODO`) executed.
- [ ] Docs updated in the same commit range.
- [ ] Remaining proof debt identified.
- [ ] Current-slice and next-slice docs are synchronized.

### 8.1 Fixture-backed smoke regression workflow (Tier 2)

Tier 2 is active and required in `./scripts/test_smoke.sh`.

- Expected trace fragments live in `tests/fixtures/main_trace_smoke.expected`.
- `scripts/test_tier2_trace.sh` runs `lake exe sele4n` and enforces substring matching for each
  non-empty fixture line.
- On mismatch, failures are tagged with `[TRACE]` and list each missing expectation.

Intentional behavior change workflow:

1. Run `lake exe sele4n` and verify new behavior is expected.
2. Update only stable semantic lines in fixture.
3. Re-run `./scripts/test_tier2_trace.sh` and `./scripts/test_smoke.sh`.
4. Explain fixture updates in PR description.

---

## 9. Review heuristics for maintainers

Reviewers should verify:

1. Transition semantics are understandable without tactic archaeology.
2. Endpoint/scheduler coupling is minimal and justified.
3. Helper lemmas are scoped to transition behavior.
4. Invariant bundle growth remains incremental and compositional.
5. Executable trace evidence matches milestone claims.
6. Current-slice and next-slice planning text is consistent across docs.

---

## 10. Anti-patterns to avoid

- Bundling model redesign, protocol redesign, and major proof rewrites in one PR.
- Adding non-essential architecture detail during IPC-slice work.
- Hiding transition semantics behind abstractions that block direct unfolding.
- Claiming slice completion without theorem + executable evidence.
- Leaving milestone docs stale after API or theorem-surface changes.
