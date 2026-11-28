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
> **Rows**: CK1–CK4, numbered in the order they are implemented, one PR each.
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

SX29 takes the holds of ReplyRecv's legs and SX32 to SX34 ReplyRecv's own (class
b, D52, D53); SX39 lands the gate, with a pinned list of the holds this
workstream removes, which may only shrink. WS-CK takes the rest, by class
(D51), after CK1 puts `objects.invExt` in the object table's type:

| Class | What holds the state | Functions |
|---|---|---|
| (a) | a refusal-carrying wrapper whose callee reports its entry state on a refusal after a write | 19 |
| (c) | an invocation that refuses after a write, where seL4 decodes first (`handleInvocation`, `decodeInvocation`) | 17 |
| (d) | a specification body that refuses after a write and reports its entry state, an exit seL4's C does not have | 35 |
| (e) | the pre-state read after a write, no refusal involved | 50 |
| (f) | a field of the state held across a write | 10 |

Class (g), the boot (4 functions), runs once and is **out of scope**.

The counts include the functions on the reply-receive path that SX29 to SX34 take;
SX39's pinned list is the exact remainder when this workstream opens.

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
  floated back by the compiler; that is measured by SX39's gate, not assumed.

## 4. Rows

| Row | Change | Proofs | Gates and fixtures | Estimate |
|---|---|---|---|---|
| CK1 | The object table carries `objects.invExt` by construction (the owner's ruling, 2026-11-26): the table's type holds the proof, every insert and erase returns it, and the store reads it from the type instead of taking `hObjInv`. Each checks-first form then gets its unconditional equality to its specification with no in-place guard, since a read across a store at another key no longer needs a hypothesis the code cannot test. The general path's defensive arms that run only off `invExt` are retired, as unreachable by type (WS-SX D60 lists them: the reply-receive composite's post-leg pop `.error` arm and its reply-leg `.error` arm). A refused reply-receive's receive is then decided before the context return (WS-SX D60's option (c)), its frames across `receiveReturnSchedContext` no longer under a hypothesis. WS-SX's `dispatchReplyRecvAfterReply` then reads the receive capability after the reply in every answering case, seL4's order outright: its entry-order branch (the receive capability resolved on the state handed in) goes, since `dispatchReplyRecvAfterReply_eq_sel4Order` no longer needs `objects.invExt` as a hypothesis (WS-SX D63). | The table's operations' and every store's lemmas restated over the carried proof; each checks-first form's unconditional equality without its in-place guard; `dispatchReplyRecvAfterReply` restated as the reply step, then the receive capability's read on the state it left, with its entry-order branch gone; the reply-receive composite's equality with the two arms gone and the receive's admission read first. | Every `@[csimp]` unconditional with no in-place guard on a checks-first form; Tier 3 anchors; every heap reading 0 | 4–6 (not measured; measured at the row's start) |
| CK2 | Classes (d) and (a): each specification body's refusals after a write moved before its first write; each wrapper over it then carries its callee's state. This includes the reply transfer shared by the `.reply` arm and the reply-receive signal arm (`endpointReplyCrossCoreDispatch`, through `replyTransferOnCoreChecked`): its recorded-server and target sentinels (`.invalidArgument 0`) and its pop's refusals (`applyReplyDonationOnCore`: the holder's sentinel, `returnDonatedSchedContextResolved`, `keepDonatedSchedContextResolved`, `popUnheldReplyHead`) run after the reply leg's writes and report the entry state, off the invariant only (WS-SX D60). The admission design is the reply-receive one (`replyRecvPopAdmits`, WS-SX SX33): the two sentinels read on the entry state, and the pop's commit test (`replyRecvPopAdmitsCore` at the answered reply object) read before `endpointReplyOnCore`, with a commit lemma of its own for `applyReplyDonationOnCore`, which is keyed by the holder and deschedules. The refusal-carrying forms of the reply-receive's pop and post-receive donation (`replyRecvPopDonation`, `replyRecvPostReceiveDonation`, down to their stores) are WS-SX SX34's (D61), for the reply-receive path only; this row reuses them where the same operations run elsewhere and does not redo them. The capability-transfer loop's class (d) hold (`ipcUnwrapCapsLoop`'s `.error` fallback, which keeps the loop's entry state live across `ipcTransferSingleCap`) is WS-SX SX35.1's (D64): the loop is shared, so its install checked first serves every receive that transfers capabilities, and this row does not redo it. | Each body's and wrapper's unconditional equality to its specification; the invariant and non-interference proofs restated where a refusal now reports a different state. | SX39's pinned list shrinks by every (d) and (a) entry; Tier 3 anchors; every heap reading 0 | 5–7 |
| CK3 | Class (c): the invocation dispatch decodes and checks before it performs, as seL4's `decodeInvocation` does (`dispatchInvocationByR` and the configure, service, overflow, priority, resume, copy and finalise sites). | Each decode/perform split's equality to its specification. | SX39's pinned list shrinks by every (c) entry; Tier 3 anchors | 3–5 |
| CK4 | Classes (e) and (f): each read of the pre-state, or of a field of it, moved before the write it follows. | Each moved read's equality. | SX39's pinned list empty; the gate then refuses any hold | 3–4 |

About 15–22 sessions. **Closure**: CK4, when SX39's pinned list is empty.

## 5. Risks

- LCNF let-floating can move a hoisted read back after a write; the gate
  measures the IR, so the row is not done until the gate agrees.
- The closure applications the IR does not name (1,336 in 305 declarations at
  SX29.1) are refused by the gate until resolved; resolving them may surface
  holds the measurement did not count.
