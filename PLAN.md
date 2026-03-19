# Plan: Close Remaining 6 Sorry Items in Lookup.lean

## Current State
- File: `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean` (1148 lines)
- Builds cleanly with 6 sorry items (zero errors)
- All sorry items are in functional correctness proofs for Robin Hood hashing

## Dependency Graph

```
insertLoop_output_source (sorry #1, line 1017)
    └── used by: get_after_insert_ne

get_after_insert_ne (sorry #2, line 1048)
    └── depends on: insertLoop_output_source + new helpers

backshiftLoop_preserves_entry_presence (sorry #3, line 1128)
    └── used by: erase_preserves_ne_entry

erase_removes_key (sorry #4, line 315)
    └── used by: get_after_erase_eq (already proved!)

erase_preserves_ne_entry (sorry #5, line 1139)
    └── depends on: backshiftLoop_preserves_entry_presence
    └── used by: get_after_erase_ne

get_after_erase_ne (sorry #6, line 1146)
    └── depends on: erase_preserves_ne_entry + erase_removes_key
```

## Execution Order (leaf-first)

### Step 1: `insertLoop_output_source` sorry at line 1017

**What we have:** In the Robin Hood swap case, IH returns:
- Left: `(e.key == eOld.key) = true ∧ e.value = eOld.value`
- We need: `∃ q, hq, slots[q] = some e`

**Why this is simple:** `e` has `e.key == eOld.key` and `e.value = eOld.value`.
But `e` is NOT literally `eOld` — it's an entry with the same key/value but
possibly different `dist`. We can't prove `e = eOld`.

However: the goal asks for `((e.key == kIns) = true ∧ e.value = vIns) ∨ (∃ q hq, slots[q] = some e)`.

We're in the left branch of `rcases` where `hKeyE : (e.key == eOld.key) = true`
and `hValE : e.value = eOld.value`. We need EITHER the left disjunct OR the right.

The right disjunct needs `slots[q] = some e` for original slots. But `e` might
have a different `.dist` than `eOld`, so `slots[idx%cap] = some eOld` doesn't
give `slots[idx%cap] = some e` directly.

**Key insight**: Actually, the IH was called with `eOld.key` and `eOld.value`
as the insertion key/value. So the left branch of IH means `e.key == eOld.key`
and `e.value = eOld.value`. This entry came from the recursive insertLoop
that inserts `eOld` into the shifted slots. The entry `e` either IS the
newly-inserted copy of eOld (with `e.key == eOld.key`, `e.value = eOld.value`)
or from the set array.

We need to show this entry was in the ORIGINAL `slots`. Since
`e.key == eOld.key` and `eOld` was at `slots[idx%cap]`, we know
`eOld` has the same key. But `e` might not be literally `eOld`.

**Wait** — re-read the goal more carefully. The goal is:
```
((e.key == kIns) = true ∧ e.value = vIns) ∨
(∃ q, ∃ hq : q < capacity, slots[q]'(hLen ▸ hq) = some e)
```

We're in the left branch: `e.key == eOld.key = true` and `e.value = eOld.value`.
We know `eOld.key ≠ kIns` (from `hKey : ¬(eOld.key == kIns)`... wait, actually
`hKey` says `¬(eOld.key == kIns)`, let me re-check).

Looking at line 997-999: `if hKey : eOld.key == kIns then ... else ...`
So in the else branch: `hKey : ¬(eOld.key == kIns) = true`, which means
`eOld.key ≠ kIns`.

Since `e.key == eOld.key` and `eOld.key ≠ kIns`, we can't use the left
disjunct (which needs `e.key == kIns`). We must use the right disjunct.

But `e` came from the recursive IH with `e.key == eOld.key` and `e.value = eOld.value`.
The entry `e` in the output has these fields but might have a different `dist`.
We need `slots[q] = some e` for the ORIGINAL slots — meaning the exact same
structure `e` must exist somewhere in the original array.

**This is the real problem**: `e` has `dist` possibly different from `eOld.dist`
(the recursive insertLoop may have placed it with a new dist). So `e ≠ eOld`
in general, and `e` doesn't exist in the original slots.

**Resolution**: We need to strengthen the IH or change the approach.

Actually, wait. The IH was about `insertLoop` with `eOld.key, eOld.value` into
the set array. The IH's left branch says the output entry has
`key == eOld.key` and `value = eOld.value`. This means the entry was
PLACED BY the recursive insertLoop (it's the newly-inserted copy).

So this entry has `key == eOld.key` (which == some key from original slots
at idx%cap). We need to get it into the original slots disjunct. But it's
NOT in the original slots — it's a freshly created entry by insertLoop.

**The fix**: We can't prove the right disjunct. Instead, we should try to
prove that `(e.key == kIns) = true` IS possible. But we showed `eOld.key ≠ kIns`...

Hmm. Let me reconsider. The entry `e` has `e.key == eOld.key` where
`eOld.key ≠ kIns`. So `e.key ≠ kIns` by transitivity. And `e` is not
literally in the original slots. **This case is actually impossible!**

Think about it: `insertLoop` with `eOld.key, eOld.value` into an array
that has `⟨kIns, vIns, d⟩` at `idx%cap` and the original entries elsewhere.
Every entry in the output either:
1. Has key == eOld.key and value = eOld.value (the inserted copy), OR
2. Existed in the set array.

If it's case 1, the entry was freshly created by insertLoop. Its dist field
is whatever insertLoop assigned. But this entry's key/value match `eOld`,
which was at `slots[idx%cap]` in the original array. So `eOld` IS in the
original slots. But `e` (with possibly different dist) is NOT.

**The actual fix**: The theorem statement should track key/value pairs rather
than exact entries. OR, we observe that `e` (from insertLoop output) with
`e.key == eOld.key` and `e.value = eOld.value` means `e` "corresponds to"
`eOld` in the original. We can witness `eOld` at `idx%cap`:
`slots[idx%cap] = some eOld`, and the goal's right disjunct needs
`slots[q] = some e` (exact structural equality).

Since `e` may have different dist, we can't satisfy this. **The theorem
needs to be restated**, or we need to handle this case differently.

**Alternative approach**: Instead of using `insertLoop_output_source` directly,
use a weaker version: every entry in the output has key/value that
matches either (kIns, vIns) or some original entry. This is what the
theorem SHOULD say but the existential `slots[q] = some e` is too strong
when `e` has a modified dist.

**ACTUAL FIX for the sorry**: Looking again at the IH result type — the
IH was called with `(slots.set (idx%cap) (some ⟨kIns, vIns, d⟩) hIdx)` as
the input slots. So the IH's right disjunct says:
`∃ q hq, (slots.set ...)[q] = some e`.

Not `slots[q] = some e`. The set array. The left branch of rcases says
`(e.key == eOld.key) = true ∧ e.value = eOld.value`.

We need the OUTER goal: `((e.key == kIns) = true ∧ e.value = vIns) ∨ (∃ q hq, slots[q] = some e)`.

In the left branch: `e.key == eOld.key` and `e.value = eOld.value`.
Since `eOld.key ≠ kIns`, we can't use the left disjunct. For the right, we need
exact `slots[q] = some e`. Since `e` might differ from `eOld` only in `.dist`,
and `slots[idx%cap] = some eOld`, this only works if `e = eOld`.

**Key question**: Can `e` differ from `eOld` in the `.dist` field?

The IH inserts `(eOld.key, eOld.value)` at displacement `eOld.dist + 1`.
If this entry gets placed without further displacement, the result entry
has `dist = eOld.dist + 1` (or some other value). But the IH's left result
says the entry has `key == eOld.key` and `value = eOld.value`. This entry
was freshly created by insertLoop and WILL have a dist field that differs
from what was in the original `slots`.

**So the theorem as stated has a gap in the Robin Hood case.**

**The correct fix**: Change `insertLoop_output_source` to track key/value
pairs instead of exact entries. The right disjunct should be:
```
∃ q hq, ∃ eOrig, slots[q] = some eOrig ∧ eOrig.key = e.key ∧ eOrig.value = e.value
```
instead of `slots[q] = some e`.

This is a small but essential change to the theorem statement.

### Step 1 (revised): Fix `insertLoop_output_source` statement and prove

**Action**: Change the right disjunct from `slots[q] = some e` to
`∃ eOrig, slots[q] = some eOrig ∧ eOrig.key = e.key ∧ eOrig.value = e.value`.

Then the sorry at line 1017 becomes: we have `e.key == eOld.key` and
`e.value = eOld.value`, and `slots[idx%cap] = some eOld`, so we witness
`eOrig := eOld` at `q := idx%cap`.

**Lines changed**: ~5 lines in the theorem statement + ~5 lines fixing the
existing proof cases + ~5 lines for the sorry case.

### Step 2: `erase_removes_key` (line 315)

**What we have:**
- `hFL`: `findLoop_none_implies_absent` applied to `findLoop` on original table
- We need to case-split on whether `findLoop` returns `none` or `some idx`

**Strategy**: Unfold `RHTable.erase`, match on `findLoop` result:
- `none` case: `erase` returns `t` unchanged. Key already absent by `hFL`.
- `some idx` case: Table slots are `backshiftLoop(slots.set(idx%cap, none))`.
  1. `findLoop_some_has_key` gives us `slots[idx%cap] = some eFound` with `eFound.key == k`
  2. After `set(idx%cap, none)`: key `k` is absent (was at idx%cap by noDupKeys,
     now that slot is none, and findLoop_none_implies_absent says no other slot has it)
  3. `backshiftLoop_preserves_key_absence` carries absence through backshift

**Concrete sub-steps**:
- a) Prove key absent from `slots.set(idx%cap, none)`: ~15 lines
- b) Apply `backshiftLoop_preserves_key_absence`: ~5 lines
- c) Stitch together under the match: ~10 lines

Total: ~30 lines. Straightforward composition of existing helpers.

### Step 3: `backshiftLoop_preserves_entry_presence` (line 1128)

**What we have**: Entry `e` at position `p` in `slots` (with `p ≠ gapIdx%cap`
since gap is `none` but `slots[p] = some e`). Prove after backshift, some
entry with same key/value exists.

**Strategy**: By induction on fuel.
- Fuel = 0: backshiftLoop returns slots unchanged. Entry still there. Trivial.
- Fuel > 0: Match on `slots[(gapIdx+1)%cap]`:
  - `none`: backshiftLoop returns slots. Trivial.
  - `some nextE` with `nextE.dist == 0`: returns slots. Trivial.
  - `some nextE` with `nextE.dist ≠ 0`: Backshift happens.
    The double-set array moves `nextE` (with decremented dist) to `gapIdx%cap`
    and clears `(gapIdx+1)%cap`.

    Case split on `p`:
    - `p = (gapIdx+1)%cap`: Entry `e` was at the position being cleared.
      But `e = nextE` (same slot). After the double-set, `nextE` is now at
      `gapIdx%cap` with `key = nextE.key = e.key` and `value = nextE.value = e.value`.
      The gap for the recursive call is at `(gapIdx+1)%cap`. So the moved
      entry at `gapIdx%cap` is NOT the gap — it survives the recursive call.
      Apply IH.
    - `p ≠ (gapIdx+1)%cap`: Entry `e` is untouched by the double-set
      (neither at gapIdx%cap since that was none, nor at (gapIdx+1)%cap).
      So `e` is still in the double-set array. Apply IH.

**The IH concern**: The IH has a precondition `hGapNone` requiring the new
gap position to be none. After the double-set, position `(gapIdx+1)%cap`
IS none (we set it to none). So this precondition is satisfied.

**Sub-steps**:
- a) Induction on fuel, handle base + none + dist=0 cases: ~15 lines
- b) For the shift case, construct the double-set array properties: ~10 lines
- c) Case split p = (gapIdx+1)%cap vs p ≠ (gapIdx+1)%cap: ~25 lines each
- d) Apply IH in each case: ~10 lines each

Total: ~70 lines. This is the longest single proof.

### Step 4: `erase_preserves_ne_entry` (line 1139)

**What we have**: Entry `e` at position `p` with `e.key == k'` and `k' ≠ k`.
Prove after `erase k`, some entry with same key `k'` and same value exists.

**Strategy**: Unfold `erase`, match on `findLoop`:
- `none`: `erase` returns `t`. Entry trivially preserved.
- `some idx`: Two-phase — set `idx%cap` to none, then backshiftLoop.
  1. `p ≠ idx%cap` (since `e.key == k'` and `k' ≠ k`, but slot at `idx%cap`
     has key `== k` by `findLoop_some_has_key`, and `noDupKeys` gives `p ≠ idx%cap`
     unless same key).
  2. After `set(idx%cap, none)`: `e` still at position `p` (since `p ≠ idx%cap`).
  3. Gap at `idx%cap` is none.
  4. Apply `backshiftLoop_preserves_entry_presence` to get the result.

Total: ~30 lines. Composition of existing helpers + step 3 result.

### Step 5: `get_after_insert_ne` (line 1048)

**Strategy**: Case split on `t.get? k'`:
- **`none` case**: `t.get? k' = none` means key `k'` absent from all slots.
  After insert, still absent by `insertLoop_absent_ne_key` (+ `resize_preserves_key_absence`
  if resize happened). Then `getLoop_none_of_absent` gives `none`.

- **`some val` case**: `getLoop_some_implies_entry` gives us a slot `p` with
  `slots[p] = some e` where `e.key == k'` and `e.value = val`.
  After insert, this entry still exists (via `insertLoop_output_source` revised —
  it has same key/value in the output). And the output satisfies invExt.
  Apply `getLoop_finds_present` on the output table.

**Sub-steps**:
- a) Unfold `get?` and `insert`, handle resize vs no-resize: ~10 lines
- b) None case: ~15 lines (insertLoop_absent_ne_key + resize + getLoop_none_of_absent)
- c) Some case: ~25 lines (getLoop_some_implies_entry + insertLoop_output_source +
     getLoop_finds_present on output)

But wait — the "some case" needs that the entry's key/value pair survives
in the output AND that we can locate it. We need `insertLoop_output_source`
(revised) to know the entry exists, but we also need its position in the
output to apply `getLoop_finds_present`. The revised `insertLoop_output_source`
tells us key/value match but not the exact position properties (dist etc.)
needed for `getLoop_finds_present`.

**Alternative for some case**: Instead of tracking the entry through insert,
use the fact that `(t.insert k v).invExt` holds and there exists an entry
with `key == k'` in the output (from `insertLoop_output_source` revised).
Then `getLoop_finds_present` can be applied using the output table's own
distCorrect, PCD, noDupKeys.

This works! We need:
1. `insertLoop_output_source` (revised) → entry with `key == k'` exists in output
2. Output satisfies invExt
3. `getLoop_finds_present` on output table

For the value: we need `e'.value = val` where `e'` is in the output.
The revised `insertLoop_output_source` gives two cases:
- `e'.key == kIns ∧ e'.value = vIns`: but `e'.key == k'` and `k' ≠ k = kIns`, contradiction.
- `∃ eOrig in original, eOrig.key = e'.key ∧ eOrig.value = e'.value`: so `e'.value = eOrig.value`.

We know `eOrig` has `key == k'` and `eOrig.value = e.value = val` (from getLoop_some_implies_entry).
So `e'.value = val`. Then `getLoop_finds_present` gives `some val`.

This approach is viable but needs a helper to bridge from
`insertLoop_output_source` to the insertNoResize/insert level. Could be
~40 lines.

**Actually, a simpler approach**: We already have `insertLoop_absent_ne_key`
(key absent stays absent) and `insertLoop_output_source` (every output entry
came from input or is the new key). The composition:

For the none case: straightforward.
For the some case: We need a new helper `insertLoop_preserves_ne_entry`
that says: if `slots[p] = some e` with `e.key ≠ kIns`, then
`∃ q, output[q] = some e'` with `e'.key = e.key ∧ e'.value = e.value`.

This helper can be proved by induction on fuel with similar structure to
`insertLoop_absent_ne_key`. ~50 lines.

Total for step 5: ~50-line helper + ~30-line main proof = ~80 lines.

### Step 6: `get_after_erase_ne` (line 1146)

**Strategy**: Same pattern as step 5 but for erase.

Case split on `t.get? k'`:
- **none case**: key `k'` absent → after erase, still absent
  (erase only removes entries or moves them, doesn't create new keys;
  use `backshiftLoop_preserves_key_absence` + `erase` structure).
  Actually simpler: `erase_removes_key` handles key `k` specifically.
  For `k' ≠ k`: use that `backshiftLoop_output_has_input_key_value`
  (every output entry came from input). If `k'` absent from input,
  absent from output. Apply `getLoop_none_of_absent`.

- **some val case**: `getLoop_some_implies_entry` gives slot with `key == k'`.
  `erase_preserves_ne_entry` (step 4) gives slot in erased table with
  same key/value. Apply `getLoop_finds_present` with erased table's invExt.

**Sub-steps**:
- a) None case: ~15 lines
- b) Some case: ~20 lines (erase_preserves_ne_entry + getLoop_finds_present)

Total: ~35 lines.

## Implementation Order

| Step | Sorry | Lines | Dependencies |
|------|-------|-------|--------------|
| 1 | `insertLoop_output_source` (fix stmt + prove) | ~20 | None |
| 2 | `erase_removes_key` | ~30 | None |
| 3 | `backshiftLoop_preserves_entry_presence` | ~70 | None |
| 4 | `erase_preserves_ne_entry` | ~30 | Step 3 |
| 5 | `get_after_insert_ne` | ~80 | Step 1 |
| 6 | `get_after_erase_ne` | ~35 | Steps 2, 3, 4 |

Steps 1, 2, 3 are independent and can be done first (in any order).
Steps 4, 5, 6 depend on earlier steps.

## Risk Mitigation

- **Dependent array motives**: Use `getElem_idx_eq` (already proved) to
  bridge between `slots[i]'proof1` and `slots[i]'proof2` when index matches.
- **Nested match in erase**: Use `unfold RHTable.erase; simp only []; split`
  to case-split on findLoop result. Each branch is then straightforward.
- **IH preconditions**: For `backshiftLoop_preserves_entry_presence`, the
  key precondition `hGapNone` is satisfied because the double-set clears
  `(gapIdx+1)%cap`. Explicitly construct this proof term.
- **Keep each Edit ≤ 80 lines**: Break larger proofs into helper lemmas
  if needed.
