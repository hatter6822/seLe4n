# Project Usage and Value

## 1. What seLe4n provides today

### A production kernel with proofs

seLe4n is not a research prototype — it is a kernel being built for production
deployment on Raspberry Pi 5. Every transition is an executable function, and
every invariant is machine-checked.

### Concrete artifacts

- **103,131 lines** of production Lean code across 142 files.
- **3,037 theorem/lemma declarations** with zero sorry/axiom.
- **4-tier CI** with hygiene, build, trace, and invariant surface gates.
- **Negative-state test suite** with corruption testing and per-mutation invariant checks.
- **Executable trace harness** with fixture-backed evidence.

## 2. Practical use cases

### A) Build a verified kernel

The primary use case: a microkernel where the implementation *is* the specification,
with machine-checked proofs that security invariants are preserved across every
transition.

### B) Evaluate authority and policy design

Encode policy assumptions as predicates. Verify composition against lifecycle,
capability, and information-flow behavior. Catch violations at type-check time.

### C) Formal-methods engineering practice

The milestone progression (Bootstrap → M7 → WS-B..Q) provides a practical path
from state modeling through composed theorem surfaces to production kernel.

### D) Architecture and security review

Reviews reference concrete transition definitions, invariant theorems, and
executable trace evidence — not prose-only claims.

### E) Hardware-bound assurance

Architecture-neutral proofs and adapter contracts provide the foundation for
platform-specific binding without invalidating core verification.

## 3. Team adoption paths

| Team | Entry point | Value |
|------|-------------|-------|
| **Kernel developers** | Codebase reference (Ch. 11), [`DEVELOPMENT.md`](../DEVELOPMENT.md) | Understand semantics, contribute transitions and proofs |
| **Verification engineers** | Proof map (Ch. 12), invariant suites | Extend invariants, strengthen proof coverage |
| **Security teams** | Threat model (Ch. 28), information-flow modules | Validate policy enforcement, stress failure paths |
| **Platform teams** | Hardware path (Ch. 10), architecture modules | Plan Raspberry Pi 5 binding, track semantic drift |

## 4. Key links

- Specification: [Specification & Roadmap](05-specification-and-roadmap.md)
- Completed workstream: [WS-S Pre-Benchmark Strengthening](../dev_history/audits/AUDIT_v0.18.7_WORKSTREAM_PLAN.md)
- Hardware path: [Path to Real Hardware (Raspberry Pi 5)](10-path-to-real-hardware-mobile-first.md)
- Workstream history: [`docs/WORKSTREAM_HISTORY.md`](../WORKSTREAM_HISTORY.md)
