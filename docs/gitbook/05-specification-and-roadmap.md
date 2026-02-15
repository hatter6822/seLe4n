# Specification and Roadmap

This handbook chapter complements `docs/SEL4_SPEC.md`.

## Current slice: M4-A

M4-A focuses on introducing lifecycle/retype semantics with clear theorem and executable surfaces:

1. lifecycle transition API,
2. identity/aliasing invariants,
3. capability-object coherence invariants,
4. preservation theorem entrypoints,
5. executable + fixture evidence.

## Next slice: M4-B

M4-B hardens lifecycle semantics through capability-lifecycle composition:

1. lifecycle + revoke/delete interaction stories,
2. stale-reference exclusion invariants,
3. cross-bundle preservation,
4. explicit failure-path theorem coverage,
5. expanded scenario/Tier 3 checks.

## Longer-term direction

After M4-A/M4-B, likely focus areas include:

- richer object lifecycle families,
- policy and authority decomposition hardening,
- architecture binding strategy,
- and pre-deployment constraints for hardware execution paths.
