# CLAUDE.md — seLe4n project guidance

## What this project is

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics. It produces
machine-checked proofs of invariant preservation over executable transition
semantics. Lean 4.27.0 toolchain, Lake build system, version 0.11.5.

## Build and run

```bash
# Environment setup (runs automatically via SessionStart hook)
./scripts/setup_lean_env.sh --build

# Manual build
source ~/.elan/env && lake build

# Run executable trace harness
lake exe sele4n
```

## Validation commands (tiered)

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # Tier 0-2: + trace + negative-state
./scripts/test_full.sh      # Tier 0-3: + invariant/doc anchors
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Tier 0-4
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

## Source layout

```
SeLe4n/Prelude.lean              Typed identifiers, monad foundations
SeLe4n/Machine.lean              Machine state primitives
SeLe4n/Model/Object.lean         Kernel objects and data structures
SeLe4n/Model/State.lean          Kernel/system state representation
SeLe4n/Kernel/Scheduler/*        Scheduler transitions + invariants
SeLe4n/Kernel/Capability/*       CSpace/capability ops + invariants
SeLe4n/Kernel/IPC/*              Endpoint/notification IPC + invariants
SeLe4n/Kernel/Lifecycle/*        Lifecycle/retype transitions + invariants
SeLe4n/Kernel/Service/*          Service orchestration + policy
SeLe4n/Kernel/Architecture/*     Architecture assumptions + VSpace
SeLe4n/Kernel/InformationFlow/*  Security labels, projection, non-interference
SeLe4n/Kernel/API.lean           Public kernel interface
SeLe4n/Testing/*                 Test harness, state builder, fixtures
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
```

## Key conventions

- **Invariant/Operations split**: each kernel subsystem has `Operations.lean`
  (transitions) and `Invariant.lean` (proofs). Keep this separation.
- **No axiom/sorry**: forbidden in production proof surface. Tracked exceptions
  must carry a `TPI-D*` annotation.
- **Deterministic semantics**: all transitions return explicit success/failure.
  Never introduce non-deterministic branches.
- **Fixture-backed evidence**: `Main.lean` output must match
  `tests/fixtures/main_trace_smoke.expected`. Update fixture only with rationale.
- **Typed identifiers**: `ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, etc.
  are wrapper structures, not `Nat` aliases. Use explicit `.toNat`/`.ofNat`.

## Documentation rules

When changing behavior, theorems, or workstream status, update in the same PR:
1. `README.md`
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. Affected GitBook chapter(s) — canonical root docs take priority over GitBook
5. `docs/CLAIM_EVIDENCE_INDEX.md` if claims change

Canonical ownership: root `docs/` files own policy/spec text. GitBook chapters
under `docs/gitbook/` are mirrors that summarize and link to canonical sources.

## Active workstream context

- **Active portfolio**: WS-D (v0.11.0 audit remediation)
- **Completed**: WS-D1 (test validity), WS-D2 (info-flow), WS-D3 (proof gaps),
  WS-D4 (kernel hardening)
- **Planned**: WS-D5 (test infrastructure), WS-D6 (CI/docs polish)
- **Planning backbone**: `docs/audits/AUDIT_v0.11.0_WORKSTREAM_PLAN.md`

## PR checklist

- [ ] Workstream ID identified
- [ ] Scope is one coherent slice
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with implementation
- [ ] `test_smoke.sh` passes (minimum); `test_full.sh` for theorem changes
- [ ] Documentation synchronized
