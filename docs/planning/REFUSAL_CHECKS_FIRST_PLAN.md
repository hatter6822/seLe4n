# WS-CK — Checks first: no state held across a write

> **Workstream**: WS-CK (every refusal on a committing entry checked before
> the first write, so no caller holds the state across a writing call).
> **Status**: **PLANNED** — registered at `v0.37.58` by WS-SX SX29, under the
> owner's ruling D51 (2026-11-26) in
> [`SEL4_ABI_FIDELITY_PLAN.md`](SEL4_ABI_FIDELITY_PLAN.md). It opens after
> WS-SX closes at `v0.38.0`, and after WS-PK: WS-PK runs first, and D29 is
> kept (the owner's ruling, 2026-11-26).
> **Prefix**: `CK`. `ck<digit>` matches no identifier in the tree (measured at
> `v0.37.58` over `SeLe4n/`, `tests/`, `rust/` and `scripts/`, `Cargo.lock`
> excluded), so the identifier-naming gate can enforce the family.
> **Rows**: CK1–CK3, numbered in the order they are implemented, one PR each.
> Each row consumes only lower-numbered rows. No two rows run in parallel.

## 1. The problem

A Lean function that keeps a value live across a call that would write it in
place makes the value shared, so the callee copies it. When the value is the
`SystemState`, the copy includes the object store's 131,072-slot table, about
1 MB, on every such call. WS-SX SX28 traced the reply-receive general path's
three 1 MB cells to this; SX29.1 (D51) derived the whole set from the Lean IR
the C emitter prints, over the closure of the 12 committing exports: 1,548
holds, 327 (caller, callee) pairs, over 147 source functions.

seL4's C has no such copies: it decodes and checks before it writes, and where
it commits partial work it reports what it committed. The fix follows seL4:
each refusal moves before the first write, as a read-only check on the entry
state, and the write that follows does not refuse.

## 2. Scope

SX29 takes the holds of ReplyRecv's legs and SX32 and SX33 ReplyRecv's own (class
b, D52, D53); SX34 lands the gate, with a pinned list of the holds this
workstream removes, which may only shrink. WS-CK takes the rest, by class
(D51):

| Class | What holds the state | Functions |
|---|---|---|
| (a) | a refusal-carrying wrapper whose callee reports its entry state on a refusal after a write | 19 |
| (c) | an invocation that refuses after a write, where seL4 decodes first (`handleInvocation`, `decodeInvocation`) | 17 |
| (d) | a specification body that refuses after a write and reports its entry state, an exit seL4's C does not have | 35 |
| (e) | the pre-state read after a write, no refusal involved | 50 |
| (f) | a field of the state held across a write | 10 |

Class (g), the boot (4 functions), runs once and is **out of scope**.

The counts include the functions on the reply-receive path that SX29 to SX33 take;
SX34's pinned list is the exact remainder when this workstream opens.

## 3. Rules

- **Checks first, unconditional.** Each fast form keeps an equality to its
  specification with no invariant assumption. Where a refusal is unreachable
  under the invariants, the refusal still moves before the write; it is not
  deleted on an invariant argument inside this workstream.
- **The dual queue never holds a half-unlinked state.** A refusal after a pop
  is not reported with the popped state; its check moves before the pop.
- **The flow gate runs before anything observable**, and the non-interference
  proofs are restated, not dropped. The lock sets stay; nothing allocates.
- **No steering.** No dead stores, no `@[export]` used to shape the IR, and no
  compiled branch that can never run. A read moved before a write may be
  floated back by the compiler; that is measured by SX34's gate, not assumed.

## 4. Rows

| Row | Change | Proofs | Gates and fixtures | Estimate |
|---|---|---|---|---|
| CK1 | Classes (d) and (a): each specification body's refusals after a write moved before its first write; each wrapper over it then carries its callee's state. | Each body's and wrapper's unconditional equality to its specification; the invariant and non-interference proofs restated where a refusal now reports a different state. | SX34's pinned list shrinks by every (d) and (a) entry; Tier 3 anchors; every heap reading 0 | 5–7 |
| CK2 | Class (c): the invocation dispatch decodes and checks before it performs, as seL4's `decodeInvocation` does (`dispatchInvocationByR` and the configure, service, overflow, priority, resume, copy and finalise sites). | Each decode/perform split's equality to its specification. | SX34's pinned list shrinks by every (c) entry; Tier 3 anchors | 3–5 |
| CK3 | Classes (e) and (f): each read of the pre-state, or of a field of it, moved before the write it follows. | Each moved read's equality. | SX34's pinned list empty; the gate then refuses any hold | 3–4 |

About 11–16 sessions. **Closure**: CK3, when SX34's pinned list is empty.

## 5. Risks

- LCNF let-floating can move a hoisted read back after a write; the gate
  measures the IR, so the row is not done until the gate agrees.
- The closure applications the IR does not name (1,336 in 305 declarations at
  SX29.1) are refused by the gate until resolved; resolving them may surface
  holds the measurement did not count.
