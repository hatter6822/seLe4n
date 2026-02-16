# seLe4n

A Lean 4 formalization project for building an executable and machine-checked model of key
[seL4 microkernel](https://sel4.systems) semantics.

## Project status snapshot

seLe4n is currently in **M4-B lifecycle-capability composition hardening (active slice kickoff)** after
completing M4-A lifecycle/retype foundations.

### Milestone board

- ✅ **Bootstrap complete**: executable kernel monad, core object/state model, transition scaffolding.
- ✅ **M1 complete**: scheduler integrity invariants and preservation entrypoints.
- ✅ **M2 complete**: capability + CSpace operations, attenuation/lifecycle rules, composed invariants.
- ✅ **M3 complete**: endpoint IPC seed (`endpointSend`/`endpointReceive`) plus preservation theorem surface.
- ✅ **M3.5 complete**: typed waiting/handshake behavior, scheduler coherence contract predicates,
  composed IPC+scheduler invariant bundle, local-first preservation theorem layering, executable
  waiting-to-delivery trace evidence.
- ✅ **M4-A current slice complete**: object lifecycle/retype foundations now include local lifecycle
  preservation entrypoints and composed scheduler/capability/IPC + lifecycle bundle theorem entrypoints.
- 🚧 **M4-B current slice active**: lifecycle + revocation composition hardening, stale-reference
  exclusion, and expanded executable/testing coverage.

## Documentation hub (GitBook-ready)

Project documentation has been reorganized into a GitBook-compatible structure at:

- `docs/gitbook/README.md` (book introduction + navigation)
- `docs/gitbook/SUMMARY.md` (book table of contents)
- `docs/gitbook/02-microkernel-and-sel4-primer.md` (microkernel + seL4 concepts)
- `docs/gitbook/10-path-to-real-hardware-mobile-first.md` (mobile-first hardware roadmap)
- `docs/gitbook/13-future-slices-and-delivery-plan.md` (post-M4 planning and delivery path)

Core references remain:

- `docs/SEL4_SPEC.md` — normative milestone spec, current/next slice targets, acceptance criteria.
- `docs/DEVELOPMENT.md` — contributor workflow, proof standards, implementation sequence.
- `docs/TESTING_FRAMEWORK_PLAN.md` — active test tiers and CI contract.
- `docs/PROJECT_AUDIT.md` — audit snapshot and recommendations.

Deep technical chapters for implementation work:

- `docs/gitbook/11-codebase-reference.md` — file-by-file architecture map, transition semantics,
  proof organization, runtime trace contract, and debugging playbooks.
- `docs/gitbook/12-proof-and-invariant-map.md` — theorem surface map and invariant composition index.
- `docs/gitbook/07-testing-and-ci.md` — exact tier responsibilities, triage flow, and script logging
  behavior (including color-coded prefixes in interactive terminals).

## Completed slice outcomes (M4-A)

1. Introduce typed lifecycle transition surface (deterministic retype branch now implemented).
2. Define object identity and aliasing invariants for newly created/retyped objects.
3. Establish capability-reference coherence invariants over lifecycle updates.
4. Add preservation theorem entrypoints for each lifecycle transition.
5. Extend executable evidence (`Main.lean`) and Tier 2 trace fixtures for lifecycle behavior.

Progress note (steps 1-6): lifecycle metadata now explicitly tracks object-store type identity and slot-to-target
capability references (including store-time synchronization when a CNode is updated), `lifecycleRetypeObject`
retains deterministic success/error branching, lifecycle invariants remain narrowly layered, theorem entrypoints
cover local and composed lifecycle preservation, and executable/fixture evidence now includes the lifecycle
unauthorized branch, illegal-state branch, and success-path object-kind confirmation.

## Current slice target outcomes (M4-B)

1. Compose lifecycle transitions with revoke/delete authority paths.
2. Strengthen invariants for stale-reference exclusion and authority monotonicity across retype chains.
3. Add composed preservation theorems spanning lifecycle + capability bundles.
4. Expand scenario coverage to include lifecycle rollback/error branches.
5. Deepen Tier 3 checks for lifecycle-specific theorem/bundle surfaces.

Next-slice (M5 preview) direction: service-graph semantics, policy-oriented authority constraints,
and architecture-binding interfaces that preserve reusable core proofs while M4-B lands.


## Current slice execution plan (M4-B)

To move M4-B toward closeout, work should progress in this order:

1. compose lifecycle transitions with revoke/delete semantics,
2. formalize stale-reference exclusion invariant components,
3. prove local then composed preservation including failure paths,
4. extend executable scenarios + fixture anchors,
5. add Tier 3 anchors for new theorem/bundle surfaces,
6. close out docs with explicit M5 deferrals.

## Next-slice readiness goals (M5 preview)

M5 kickoff goals are now documented around three readiness tracks:

1. service-graph semantics for restart/isolation stories,
2. policy-oriented authority decomposition over existing bundles,
3. architecture-binding interface assumptions without rewriting core proofs.

See `docs/gitbook/14-m4b-execution-playbook.md` for detailed workstream guidance and exit checklists.

## Codebase reasoning quick map

For developers trying to understand where logic lives today:

1. **Foundations**
   - `SeLe4n/Prelude.lean` (core IDs + kernel monad)
   - `SeLe4n/Machine.lean` (machine state + primitive updates)

2. **Object/state model**
   - `SeLe4n/Model/Object.lean` (typed objects, capabilities, TCB/endpoint/CNode)
   - `SeLe4n/Model/State.lean` (global system state, typed lookups, store/update helpers)

3. **Kernel semantics + proofs**
   - scheduler: `SeLe4n/Kernel/Scheduler/*.lean`
   - capability/CSpace: `SeLe4n/Kernel/Capability/*.lean`
   - IPC + handshake/scheduler coherence: `SeLe4n/Kernel/IPC/*.lean`

4. **Integration surface**
   - `SeLe4n/Kernel/API.lean` (barrel)
   - `Main.lean` (executable scenario trace)

If you need deeper module-level rationale, use `docs/gitbook/11-codebase-reference.md` and
`docs/gitbook/12-proof-and-invariant-map.md`.

## Quick start

### 1) Install Lean tooling

```bash
./scripts/setup_lean_env.sh
```

### 2) Build and run

```bash
lake build
lake exe sele4n
```

## Validation commands

```bash
./scripts/test_fast.sh
./scripts/test_smoke.sh
./scripts/test_full.sh
./scripts/test_nightly.sh
```

Note: test script logs use color-coded category/status prefixes when run in a TTY, and
automatically fall back to plain output in non-interactive environments (such as most CI logs).

## Repository layout

- `SeLe4n.lean` — library export root.
- `SeLe4n/Prelude.lean` — shared IDs, aliases, kernel monad definitions.
- `SeLe4n/Machine.lean` — abstract machine state and primitive updates.
- `SeLe4n/Model/Object.lean` — kernel object types (`TCB`, `Endpoint`, `CNode`, `Capability`).
- `SeLe4n/Model/State.lean` — global system state and typed lookup helpers.
- `SeLe4n/Kernel/API.lean` — compatibility barrel that re-exports the kernel surface.
- `SeLe4n/Kernel/Scheduler/*.lean` — scheduler operations, invariants, and preservation theorems.
- `SeLe4n/Kernel/Capability/*.lean` — capability operations, invariants, composition with IPC layer.
- `SeLe4n/Kernel/IPC/*.lean` — endpoint transitions and IPC invariants.
- `Main.lean` — runnable integration trace.
- `docs/gitbook/*` — in-depth project handbook for GitBook.

## License

This project is licensed under the MIT License. See [`LICENSE`](./LICENSE).
