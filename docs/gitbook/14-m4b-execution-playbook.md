# M4-B Execution Playbook

This chapter records how M4-B was executed and captures handoff guidance so contributors can reuse
a proven delivery pattern for M5.

## 1. Scope of this playbook

M4-B was a composition-hardening slice. Completion required integrated semantics, invariant
hardening, theorem expansion, executable evidence, and test/doc synchronization.

Use this with:

- `docs/spec/SELE4N_SPEC.md` for normative scope,
- `docs/DEVELOPMENT.md` for proof and workflow standards,
- `docs/TESTING_FRAMEWORK_PLAN.md` for tiered validation contracts.

## 2. Workstream summary (completed)

### Workstream A — transition composition semantics ✅

Goal: deterministic lifecycle + revoke/delete behavior with explicit errors.

### Workstream B — invariant hardening ✅

Goal: stale-reference exclusion components tied to lifecycle/capability assumptions.

### Workstream C — preservation theorem expansion ✅

Goal: local then composed proofs including failure paths.

### Workstream D — executable + fixture evidence ✅

Goal: observable composed behavior guarded by fixture anchors.

### Workstream E — testing and CI growth ✅

Goal: Tier 3 theorem anchors and stable full-suite behavior.

## 3. What made execution effective

1. semantics landed before fixture growth,
2. local proofs landed before composed theorems,
3. failure paths were treated as required proof surfaces,
4. docs were closed out in the same phase as tests.

## 4. Reusable PR template (for future slices)

Each milestone-moving PR should include:

1. workstream(s) advanced,
2. target outcome(s) moved,
3. evidence commands and results,
4. explicit deferrals,
5. next-slice unlock statement.

## 5. M5 kickoff playbook (new)

To start M5 cleanly, run this sequence:

1. **M5-K1: service graph definitions**
   - add minimal service state model and dependency representation.
2. **M5-K2: transition helpers**
   - add deterministic start/stop/restart helpers with explicit failures.
3. **M5-K3: policy predicates**
   - add policy-oriented authority constraints as narrow components.
4. **M5-K4: local proofs**
   - prove each transition preserves relevant components.
5. **M5-K5: composed proofs**
   - prove service + lifecycle + capability bundle preservation.
6. **M5-K6: traces/tests/docs**
   - expose scenarios in `Main.lean`, update fixtures/Tier 3, sync docs.

## 6. Common pitfalls to avoid

1. proof-first without stable semantics,
2. monolithic invariants that block reuse,
3. fixture updates without semantic intent notes,
4. M5 policy logic coupled too tightly to one service story,
5. documentation updates deferred to "later".

## 7. Exit checklist for maintainers

Before declaring a slice complete:

- transition and failure behavior are deterministic and explicit,
- local + composed theorem surfaces compile,
- executable evidence covers success and failure stories,
- Tier 3 anchors include new theorem surfaces,
- docs and roadmap state delivered outcomes plus deferrals.
