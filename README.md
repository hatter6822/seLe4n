# seLe4n

A Lean 4 formalization project for building an executable and machine-checked model of key
[seL4 microkernel](https://sel4.systems) semantics.

## Project status snapshot

seLe4n is currently in **M4 kickoff (object lifecycle/retype safety)** after completing M3.5 IPC
handshake + scheduler coherence.

### Milestone board

- ✅ **Bootstrap complete**: executable kernel monad, core object/state model, transition scaffolding.
- ✅ **M1 complete**: scheduler integrity invariants and preservation entrypoints.
- ✅ **M2 complete**: capability + CSpace operations, attenuation/lifecycle rules, composed invariants.
- ✅ **M3 complete**: endpoint IPC seed (`endpointSend`/`endpointReceive`) plus preservation theorem surface.
- ✅ **M3.5 complete**: typed waiting/handshake behavior, scheduler coherence contract predicates,
  composed IPC+scheduler invariant bundle, local-first preservation theorem layering, executable
  waiting-to-delivery trace evidence.
- 🚧 **M4 current slice in progress**: object lifecycle/retype foundations and capability-object
  coupling safety.
- 📍 **M4 next slice planned**: lifecycle + revocation composition, richer invariants, and expanded
  executable scenarios.

## Documentation hub (GitBook-ready)

Project documentation has been reorganized into a GitBook-compatible structure at:

- `docs/gitbook/README.md` (book introduction + navigation)
- `docs/gitbook/SUMMARY.md` (book table of contents)
- `docs/gitbook/02-microkernel-and-sel4-primer.md` (microkernel + seL4 concepts)
- `docs/gitbook/10-path-to-real-hardware-mobile-first.md` (mobile-first hardware roadmap)

Core references remain:

- `docs/SEL4_SPEC.md` — normative milestone spec, current/next slice targets, acceptance criteria.
- `docs/DEVELOPMENT.md` — contributor workflow, proof standards, implementation sequence.
- `docs/TESTING_FRAMEWORK_PLAN.md` — active test tiers and CI contract.
- `docs/PROJECT_AUDIT.md` — audit snapshot and recommendations.

## Current slice target outcomes (M4-A)

1. Introduce typed lifecycle transition surface (at minimum one deterministic retype/create path).
2. Define object identity and aliasing invariants for newly created/retyped objects.
3. Establish capability-reference coherence invariants over lifecycle updates.
4. Add preservation theorem entrypoints for each lifecycle transition.
5. Extend executable evidence (`Main.lean`) and Tier 2 trace fixtures for lifecycle behavior.

## Next slice target outcomes (M4-B)

1. Compose lifecycle transitions with revoke/delete authority paths.
2. Strengthen invariants for stale-reference exclusion and authority monotonicity across retype chains.
3. Add composed preservation theorems spanning lifecycle + capability bundles.
4. Expand scenario coverage to include lifecycle rollback/error branches.
5. Deepen Tier 3 checks for lifecycle-specific theorem/bundle surfaces.


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
