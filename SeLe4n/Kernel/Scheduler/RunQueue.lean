-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.RobinHood.Set
import SeLe4n.Kernel.Scheduler.LinkedQueue
namespace SeLe4n.Kernel
open SeLe4n
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.LinkedQueue

/-- WS-ZA ZA4.5: one thread's entry in a core's run queue — its priority,
whether it is queued, and its four links (codes, `LinkedQueue.code`): `prev` and
`next` in the core's queue of every runnable thread, `bucketPrev` and
`bucketNext` in the queue of its priority.  An entry outlives the thread's stay
in the queue (`queued := false`), so a thread that leaves and comes back
rewrites its entry in place and the table never gains or loses a key on the
scheduling path. -/
structure RunQueueLink where
  prio : Priority := ⟨0⟩
  queued : Bool := false
  prev : Nat := 0
  next : Nat := 0
  bucketPrev : Nat := 0
  bucketNext : Nat := 0
deriving Inhabited, DecidableEq

/-- WS-ZA ZA4.5: the codes of a priority bucket's first and last threads. -/
structure BucketEnds where
  head : Nat := 0
  tail : Nat := 0
deriving Inhabited, DecidableEq

namespace RunQueue

/-- The entry of a thread with none: unqueued, no links.  A named constant, so
the compiled lookup answers one shared object rather than building it. -/
def RunQueueLink.none : RunQueueLink := {}

/-- A thread's entry, the empty entry for a thread with none. -/
@[inline] def linkOf (links : RHTable ThreadId RunQueueLink) (t : ThreadId) : RunQueueLink :=
  (links.get? t).getD RunQueueLink.none

/-- A priority's bucket ends, `0`/`0` for a priority with none. -/
@[inline] def endsOf (buckets : RHTable Priority BucketEnds) (p : Priority) : BucketEnds :=
  (buckets.get? p).getD {}

/-- Rewrite a thread's entry. -/
@[inline] def setLink (links : RHTable ThreadId RunQueueLink) (t : ThreadId)
    (f : RunQueueLink → RunQueueLink) : RHTable ThreadId RunQueueLink :=
  links.insert t (f (linkOf links t))

/-- Rewrite a priority's bucket ends. -/
@[inline] def setEnds (buckets : RHTable Priority BucketEnds) (p : Priority)
    (f : BucketEnds → BucketEnds) : RHTable Priority BucketEnds :=
  buckets.insert p (f (endsOf buckets p))

theorem linkOf_setLink {links : RHTable ThreadId RunQueueLink} (h : links.invExt)
    (t : ThreadId) (f : RunQueueLink → RunQueueLink) (x : ThreadId) :
    linkOf (setLink links t f) x = if x = t then f (linkOf links t) else linkOf links x := by
  unfold linkOf setLink
  rw [RHTable_getElem?_insert _ _ _ h]
  by_cases hx : x = t
  · subst hx; simp; rfl
  · have : (t == x) = false := by simp; exact Ne.symm hx
    simp [this, hx]

theorem endsOf_setEnds {buckets : RHTable Priority BucketEnds} (h : buckets.invExt)
    (p : Priority) (f : BucketEnds → BucketEnds) (q : Priority) :
    endsOf (setEnds buckets p f) q = if q = p then f (endsOf buckets p) else endsOf buckets q := by
  unfold endsOf setEnds
  rw [RHTable_getElem?_insert _ _ _ h]
  by_cases hq : q = p
  · subst hq; simp; rfl
  · have : (p == q) = false := by simp; exact Ne.symm hq
    simp [this, hq]

theorem setLink_invExtK {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (f : RunQueueLink → RunQueueLink) : (setLink links t f).invExtK :=
  RHTable_insert_preserves_invExtK _ _ _ h

theorem setEnds_invExtK {buckets : RHTable Priority BucketEnds} (h : buckets.invExtK)
    (p : Priority) (f : BucketEnds → BucketEnds) : (setEnds buckets p f).invExtK :=
  RHTable_insert_preserves_invExtK _ _ _ h

/-- WS-ZA ZA4.5: the compiled `setLink`.  A present entry is rewritten where it
stands (`RHTable.modify`, which hands `f` the entry exclusively, so `f`'s
record update reuses it); only a thread's first entry inserts a key. -/
@[inline] def setLinkImpl (links : RHTable ThreadId RunQueueLink) (t : ThreadId)
    (f : RunQueueLink → RunQueueLink) : RHTable ThreadId RunQueueLink :=
  if links.contains t then links.modify t f else links.insert t (f RunQueueLink.none)

@[csimp] theorem setLink_eq_impl : @setLink = @setLinkImpl := by
  funext links t f
  unfold setLink setLinkImpl linkOf
  cases h : links.get? t with
  | none => simp [RHTable.contains, h]
  | some v => simp [RHTable.contains, h, RHTable.modify_of_get? h]

/-- WS-ZA ZA4.5: the compiled `setEnds`, as `setLinkImpl`. -/
@[inline] def setEndsImpl (buckets : RHTable Priority BucketEnds) (p : Priority)
    (f : BucketEnds → BucketEnds) : RHTable Priority BucketEnds :=
  if buckets.contains p then buckets.modify p f else buckets.insert p (f {})

@[csimp] theorem setEnds_eq_impl : @setEnds = @setEndsImpl := by
  funext buckets p f
  unfold setEnds setEndsImpl endsOf
  cases h : buckets.get? p with
  | none => simp [RHTable.contains, h]
  | some v => simp [RHTable.contains, h, RHTable.modify_of_get? h]

/-- The forward links of a links table. -/
@[inline] def nextOf (links : RHTable ThreadId RunQueueLink) (t : ThreadId) : Nat :=
  (linkOf links t).next

/-- The highest priority among `l`'s threads as a code (`p + 1`, `0` for none). -/
def maxPrioCode (lk : ThreadId → RunQueueLink) (l : List ThreadId) : Nat :=
  l.foldr (fun t m => max ((lk t).prio.val + 1) m) 0

/-- WS-ZA ZA4.5: the highest priority code along the queue links, read one entry
at a time from code `c` for at most `n` steps, joined with `acc` — the scan
`remove` runs when the last thread at the highest priority leaves, with no list
built (`maxPrioCodeWalk_eq`). -/
def maxPrioCodeWalk (links : RHTable ThreadId RunQueueLink) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | n + 1, c + 1, acc =>
      let lk := linkOf links ⟨c⟩
      maxPrioCodeWalk links n lk.next (max (lk.prio.val + 1) acc)

theorem maxPrioCodeWalk_eq (links : RHTable ThreadId RunQueueLink) (n c acc : Nat) :
    maxPrioCodeWalk links n c acc =
      max acc (maxPrioCode (linkOf links) (LinkedQueue.walk (nextOf links) n c)) := by
  induction n generalizing c acc with
  | zero => simp [maxPrioCodeWalk, LinkedQueue.walk, maxPrioCode]
  | succ n ih =>
    cases c with
    | zero => simp [maxPrioCodeWalk, LinkedQueue.walk, maxPrioCode]
    | succ c =>
      simp only [maxPrioCodeWalk, LinkedQueue.walk, ih]
      simp only [maxPrioCode, List.foldr_cons, nextOf]
      omega

/-- `maxPrioCodeWalk` over any read of the entries (the threads' own links,
once they live in the TCBs). -/
def maxPrioCodeWalkBy (lk : ThreadId → RunQueueLink) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | n + 1, c + 1, acc =>
      maxPrioCodeWalkBy lk n (lk ⟨c⟩).next (max ((lk ⟨c⟩).prio.val + 1) acc)

theorem maxPrioCodeWalkBy_eq (lk : ThreadId → RunQueueLink) (n c acc : Nat) :
    maxPrioCodeWalkBy lk n c acc =
      max acc (maxPrioCode lk (LinkedQueue.walk (fun t => (lk t).next) n c)) := by
  induction n generalizing c acc with
  | zero => simp [maxPrioCodeWalkBy, LinkedQueue.walk, maxPrioCode]
  | succ n ih =>
    cases c with
    | zero => simp [maxPrioCodeWalkBy, LinkedQueue.walk, maxPrioCode]
    | succ c =>
      simp only [maxPrioCodeWalkBy, LinkedQueue.walk, ih]
      simp only [maxPrioCode, List.foldr_cons]
      omega

/-- WS-ZA ZA4.5: what a run queue's tables and words describe.  `l` is the
queue of every runnable thread, in the order they joined it; each priority's
bucket is the queue of `l`'s threads at that priority, in the same order; a
thread is marked queued exactly when it is in `l`; `size` counts `l` and
`maxCode` is its highest priority. -/
structure Layout (links : RHTable ThreadId RunQueueLink) (buckets : RHTable Priority BucketEnds)
    (head tail size maxCode : Nat) (l : List ThreadId) : Prop where
  queue : IsQueue (fun t => (linkOf links t).next) (fun t => (linkOf links t).prev) head tail l
  nodup : l.Nodup
  length : l.length = size
  queued : ∀ t, (linkOf links t).queued = true ↔ t ∈ l
  bucket : ∀ p, IsQueue (fun t => (linkOf links t).bucketNext)
    (fun t => (linkOf links t).bucketPrev) (endsOf buckets p).head (endsOf buckets p).tail
    (l.filter (fun t => (linkOf links t).prio == p))
  maxCode : maxCode = maxPrioCode (linkOf links) l

/-- The layout's list is the one the forward links read from the head. -/
theorem Layout.walk_eq {links buckets head tail size maxCode l}
    (h : Layout links buckets head tail size maxCode l) : walk (nextOf links) size head = l :=
  h.queue.walk_eq (by rw [h.length]; exact Nat.le_refl _)

theorem Layout.self {links buckets head tail size maxCode l}
    (h : Layout links buckets head tail size maxCode l) :
    Layout links buckets head tail size maxCode (walk (nextOf links) size head) := by
  rw [h.walk_eq]; exact h

end RunQueue

/-- S-06 / WS-ZA ZA4.5: a core's run queue — the threads ready to run there,
kept as doubly linked lists whose links live in a per-thread entry table
(`links`) and whose ends live in the queue (`head`, `tail`) and in a
per-priority table (`buckets`).  Enqueue, dequeue and rotation rewrite a
handful of entries and words in place; the list of queued threads
(`toList`), a priority's bucket (`atPriority`) and every other view are read
off the links, and `layout` is the proof that they describe one queue. -/
structure RunQueue where
  links : RHTable ThreadId RunQueueLink
  buckets : RHTable Priority BucketEnds
  head : Nat
  tail : Nat
  size : Nat
  maxCode : Nat
  links_invExtK : links.invExtK
  buckets_invExtK : buckets.invExtK
  layout : RunQueue.Layout links buckets head tail size maxCode
    (LinkedQueue.walk (RunQueue.nextOf links) size head)

namespace RunQueue

theorem layout_empty_tables :
    Layout (RHTable.empty 16 (by omega)) (RHTable.empty 16 (by omega)) 0 0 0 0 [] := by
  have hl : ∀ t, linkOf (RHTable.empty 16 (by omega) : RHTable ThreadId RunQueueLink) t = {} := by
    intro t; unfold linkOf; rw [RHTable_get?_empty]; rfl
  have he : ∀ p, endsOf (RHTable.empty 16 (by omega) : RHTable Priority BucketEnds) p = {} := by
    intro p; unfold endsOf; rw [RHTable_get?_empty]; rfl
  refine ⟨isQueue_nil _ _, List.nodup_nil, rfl, fun t => ?_, fun p => ?_, rfl⟩
  · rw [hl]; simp
  · rw [he]; exact isQueue_nil _ _

@[inline] def empty : RunQueue where
  links := RHTable.empty 16 (by omega)
  buckets := RHTable.empty 16 (by omega)
  head := 0; tail := 0; size := 0; maxCode := 0
  links_invExtK := RHTable.empty_invExtK 16 (by omega)
  buckets_invExtK := RHTable.empty_invExtK 16 (by omega)
  layout := layout_empty_tables.self

instance : Inhabited RunQueue where default := empty
instance : EmptyCollection RunQueue where emptyCollection := empty

/-- The queued threads, in the order they joined the queue. -/
def toList (rq : RunQueue) : List ThreadId := walk (nextOf rq.links) rq.size rq.head

theorem layout_toList (rq : RunQueue) :
    Layout rq.links rq.buckets rq.head rq.tail rq.size rq.maxCode rq.toList := rq.layout

instance : Repr RunQueue where reprPrec rq _ := repr rq.toList

/-- O(1) membership: the thread's entry is marked queued. -/
@[inline] def contains (rq : RunQueue) (tid : ThreadId) : Bool := (linkOf rq.links tid).queued

instance : Membership ThreadId RunQueue where
  mem rq tid := rq.contains tid = true
instance (tid : ThreadId) (rq : RunQueue) : Decidable (tid ∈ rq) :=
  inferInstanceAs (Decidable (rq.contains tid = true))

/-- The priority a queued thread is queued at; `none` for a thread not queued. -/
@[inline] def priorityOf (rq : RunQueue) (tid : ThreadId) : Option Priority :=
  if rq.contains tid then some (linkOf rq.links tid).prio else none

/-- The threads queued at `prio`, in queue order. -/
def atPriority (rq : RunQueue) (prio : Priority) : List ThreadId :=
  walk (fun t => (linkOf rq.links t).bucketNext) rq.size (endsOf rq.buckets prio).head

/-- The highest priority with a queued thread. -/
@[inline] def maxPriority (rq : RunQueue) : Option Priority :=
  if rq.maxCode = 0 then none else some ⟨rq.maxCode - 1⟩

/-- WS-G4/F-P07: the threads at the highest queued priority, `[]` when empty. -/
@[inline] def maxPriorityBucket (rq : RunQueue) : List ThreadId :=
  match rq.maxPriority with
  | none => []
  | some prio => rq.atPriority prio

theorem mem_toList_iff_mem (rq : RunQueue) (tid : ThreadId) : tid ∈ rq.toList ↔ tid ∈ rq :=
  (rq.layout.queued tid).symm

theorem toList_nodup (rq : RunQueue) : rq.toList.Nodup := rq.layout.nodup

theorem atPriority_eq (rq : RunQueue) (prio : Priority) :
    rq.atPriority prio = rq.toList.filter (fun t => (linkOf rq.links t).prio == prio) :=
  (rq.layout.bucket prio).walk_eq
    (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq rq.layout.length))

theorem code_eq_iff (x : ThreadId) (c : Nat) : code x = c ↔ c ≠ 0 ∧ x = decode c := by
  constructor
  · rintro rfl; exact ⟨code_ne_zero x, (decode_code x).symm⟩
  · rintro ⟨hc, rfl⟩; cases c with
    | zero => exact absurd rfl hc
    | succ k => simp [code, decode]

/-- A nonzero `lastCode` decodes to a member. -/
theorem decode_lastCode_mem {l : List ThreadId} (h : lastCode 0 l ≠ 0) :
    decode (lastCode 0 l) ∈ l := by
  rcases lastCode_cases 0 l with h0 | ⟨z, hz, hc⟩
  · exact absurd h0 h
  · rw [hc, decode_code]; exact hz

theorem maxPrioCode_congr {lk lk' : ThreadId → RunQueueLink} {l : List ThreadId}
    (h : ∀ x ∈ l, (lk' x).prio = (lk x).prio) : maxPrioCode lk' l = maxPrioCode lk l := by
  induction l with
  | nil => rfl
  | cons y r ih =>
    simp only [maxPrioCode, List.foldr_cons] at ih ⊢
    rw [h y (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem maxPrioCode_append_single (lk : ThreadId → RunQueueLink) (l : List ThreadId)
    (y : ThreadId) : maxPrioCode lk (l ++ [y]) = max (maxPrioCode lk l) ((lk y).prio.val + 1) := by
  unfold maxPrioCode
  induction l with
  | nil => simp
  | cons z r ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

/-- A guarded rewrite of the entry coded `c` (none when `c = 0`). -/
theorem linkOf_setLink_code {links : RHTable ThreadId RunQueueLink} (h : links.invExt)
    (c : Nat) (g : RunQueueLink → RunQueueLink) (x : ThreadId) :
    linkOf (if c = 0 then links else setLink links (decode c) g) x =
      if code x = c then g (linkOf links x) else linkOf links x := by
  by_cases hc : c = 0
  · subst hc; simp [code_ne_zero]
  · rw [if_neg hc, linkOf_setLink h]
    by_cases hx : x = decode c
    · subst hx
      have : code (decode c) = c := (code_eq_iff _ _).mpr ⟨hc, rfl⟩
      simp [this]
    · have : code x ≠ c := fun e => hx ((code_eq_iff _ _).mp e).2
      simp [hx, this]

/-- Rewrite the entry a link code names; nothing for the code `0`. -/
@[inline] def setLinkAt (links : RHTable ThreadId RunQueueLink) (c : Nat)
    (g : RunQueueLink → RunQueueLink) : RHTable ThreadId RunQueueLink :=
  if c = 0 then links else setLink links (decode c) g

theorem setLinkAt_invExtK {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (c : Nat) (g : RunQueueLink → RunQueueLink) : (setLinkAt links c g).invExtK := by
  unfold setLinkAt; split
  · exact h
  · exact setLink_invExtK h _ _

theorem linkOf_setLinkAt {links : RHTable ThreadId RunQueueLink} (h : links.invExt)
    (c : Nat) (g : RunQueueLink → RunQueueLink) (x : ThreadId) :
    linkOf (setLinkAt links c g) x = if code x = c then g (linkOf links x) else linkOf links x :=
  linkOf_setLink_code h c g x

/-- The links after `t` joins at priority `p`, behind the queue's last thread
(code `tail`) and behind its bucket's last (code `btail`). -/
def appendLinks (links : RHTable ThreadId RunQueueLink) (t : ThreadId) (p : Priority)
    (tail btail : Nat) : RHTable ThreadId RunQueueLink :=
  let l1 := setLink links t
    (fun x => { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 })
  let l2 := setLinkAt l1 tail (fun x => { x with next := code t })
  setLinkAt l2 btail (fun x => { x with bucketNext := code t })

/-- WS-ZA ZA4.5: the compiled `appendLinks`.  The joining thread's entry is
rewritten in every field; branching on its priority first lets the rewrite
reuse the entry's cell (a field-by-field rebuild of an entry it never reads
would be a fresh one), and the common case, a thread rejoining at the priority
it left with, keeps that field. -/
@[inline] def appendLinksImpl (links : RHTable ThreadId RunQueueLink) (t : ThreadId) (p : Priority)
    (tail btail : Nat) : RHTable ThreadId RunQueueLink :=
  let l1 := setLink links t (fun x =>
    if x.prio = p then
      { x with queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 }
    else
      { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 })
  let l2 := setLinkAt l1 tail (fun x => { x with next := code t })
  setLinkAt l2 btail (fun x => { x with bucketNext := code t })

@[csimp] theorem appendLinks_eq_impl : @appendLinks = @appendLinksImpl := by
  funext links t p tail btail
  have hf : (fun x : RunQueueLink =>
      if x.prio = p then
        { x with queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 }
      else
        { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 }) =
      (fun x => { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 }) := by
    funext x
    split
    · next h => cases x; simp only at h; subst h; rfl
    · rfl
  unfold appendLinksImpl
  rw [hf]
  rfl

theorem appendLinks_invExtK {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (p : Priority) (tail btail : Nat) :
    (appendLinks links t p tail btail).invExtK := by
  unfold appendLinks
  exact setLinkAt_invExtK (setLinkAt_invExtK (setLink_invExtK h _ _) _ _) _ _

theorem linkOf_appendLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (p : Priority) (tail btail : Nat)
    (ht : code t ≠ tail) (hb : code t ≠ btail) (x : ThreadId) :
    linkOf (appendLinks links t p tail btail) x =
      if x = t then
        { linkOf links t with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 }
      else { linkOf links x with
        next := if code x = tail then code t else (linkOf links x).next
        bucketNext := if code x = btail then code t else (linkOf links x).bucketNext } := by
  unfold appendLinks
  dsimp only
  have h1 := setLink_invExtK h t
    (fun x => { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 })
  have h2 := setLinkAt_invExtK h1 tail (fun x => { x with next := code t })
  rw [linkOf_setLinkAt h2.1, linkOf_setLinkAt h1.1, linkOf_setLink h.1]
  by_cases hx : x = t
  · subst hx; simp [ht, hb]
  · simp only [hx, ↓reduceIte]
    by_cases e1 : code x = tail <;> by_cases e2 : code x = btail
    · simp only [if_pos e1, if_pos e2]
    · simp only [if_pos e1, if_neg e2]
    · simp only [if_neg e1, if_pos e2]
    · simp only [if_neg e1, if_neg e2]

theorem prio_appendLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (p : Priority) (tail btail : Nat) (x : ThreadId) :
    (linkOf (appendLinks links t p tail btail) x).prio =
      if x = t then p else (linkOf links x).prio := by
  have h1 := setLink_invExtK h t
    (fun x => { x with prio := p, queued := true, prev := tail, next := 0, bucketPrev := btail, bucketNext := 0 })
  have h2 := setLinkAt_invExtK h1 tail (fun x => { x with next := code t })
  unfold appendLinks
  dsimp only
  rw [linkOf_setLinkAt h2.1, linkOf_setLinkAt h1.1, linkOf_setLink h.1]
  by_cases hx : x = t
  · subst hx; simp only [↓reduceIte]; split <;> split <;> rfl
  · simp only [if_neg hx]; split <;> split <;> rfl

/-- The bucket ends after `t` joins behind the bucket's last thread (code `btail`). -/
@[inline] def appendEnds (t : ThreadId) (btail : Nat) (e : BucketEnds) : BucketEnds :=
  { head := if btail = 0 then code t else e.head, tail := code t }

/-- WS-ZA ZA4.5: the compiled `appendEnds`, branching on the old tail so the
rewrite reuses the ends' cell. -/
@[inline] def appendEndsImpl (t : ThreadId) (btail : Nat) (e : BucketEnds) : BucketEnds :=
  let h := if btail = 0 then code t else e.head
  if e.tail = code t then { e with head := h } else { e with head := h, tail := code t }

@[csimp] theorem appendEnds_eq_impl : @appendEnds = @appendEndsImpl := by
  funext t btail e
  cases e with
  | mk hd tl =>
    unfold appendEnds appendEndsImpl
    by_cases h : tl = code t <;> simp [h]

theorem nodup_filter {l : List ThreadId} (f : ThreadId → Bool) (h : l.Nodup) :
    (l.filter f).Nodup := List.Nodup.sublist List.filter_sublist h

/-- A nonzero end code of a queue names one of its members. -/
theorem code_ne_end {l : List ThreadId} {e : Nat} (he : e = lastCode 0 l) {t : ThreadId}
    (ht : t ∉ l) : code t ≠ e := by
  intro hc
  have hne : lastCode 0 l ≠ 0 := by rw [← he, ← hc]; exact code_ne_zero t
  have hm := decode_lastCode_mem hne
  rw [← he, ← hc, decode_code] at hm
  exact ht hm

/-- Appending a thread not in the queue at priority `p`. -/
theorem layout_append {links buckets head tail size maxCode l}
    (hL : Layout links buckets head tail size maxCode l) (hK : links.invExtK)
    (hKb : buckets.invExtK) (t : ThreadId) (p : Priority) (ht : t ∉ l) :
    Layout (appendLinks links t p tail (endsOf buckets p).tail)
      (setEnds buckets p (appendEnds t (endsOf buckets p).tail))
      (if tail = 0 then code t else head) (code t) (size + 1) (max maxCode (p.val + 1))
      (l ++ [t]) := by
  obtain ⟨btail, hbt⟩ : ∃ b, b = (endsOf buckets p).tail := ⟨_, rfl⟩
  rw [← hbt]
  have hBq := hL.bucket p
  rw [← hbt] at hBq
  have hT : tail = lastCode 0 l := hL.queue.2.1
  have hB : btail = lastCode 0 (l.filter (fun x => (linkOf links x).prio == p)) := hBq.2.1
  have ht' : code t ≠ tail := code_ne_end hT ht
  have hb' : code t ≠ btail := code_ne_end hB (fun hm => ht (List.mem_filter.mp hm).1)
  have hlk := linkOf_appendLinks hK t p tail btail ht' hb'
  have hne : ∀ x ∈ l, x ≠ t := fun x hx e => ht (e ▸ hx)
  have hprio : ∀ x ∈ l, (linkOf (appendLinks links t p tail btail) x).prio = (linkOf links x).prio := by
    intro x hx; rw [hlk, if_neg (hne x hx)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isQueue_append hL.queue hL.nodup (fun x hx => ?_) ?_ (fun x hx => ?_) ?_
    · rw [hlk, if_neg (hne x hx)]
    · rw [hlk, if_pos rfl]
    · rw [hlk, if_neg (hne x hx)]
    · rw [hlk, if_pos rfl]
  · exact List.nodup_append.mpr ⟨hL.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun a ha b hb e => by simp at hb; subst hb; exact ht (e ▸ ha)⟩
  · simp [hL.length]
  · intro x
    by_cases hx : x = t
    · subst hx; rw [hlk, if_pos rfl]; simp
    · rw [hlk, if_neg hx, hL.queued x]; simp [hx]
  · intro q
    rw [List.filter_append, List.filter_congr (q := fun x => (linkOf links x).prio == q)
      (fun x hx => by rw [hprio x hx])]
    rw [endsOf_setEnds hKb.1]
    by_cases hq : q = p
    · subst hq
      simp only [appendEnds]
      have hft : [t].filter (fun x => (linkOf (appendLinks links t q tail btail) x).prio == q) = [t] := by
        simp [hlk]
      rw [hft]
      refine isQueue_append hBq (nodup_filter _ hL.nodup) (fun x hx => ?_) ?_ (fun x hx => ?_) ?_
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
      · rw [hlk, if_pos rfl]
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
      · rw [hlk, if_pos rfl]
    · simp only [if_neg hq]
      have hft : [t].filter (fun x => (linkOf (appendLinks links t p tail btail) x).prio == q) = [] := by
        simp [hlk]; exact Ne.symm hq
      rw [hft, List.append_nil]
      refine (isQueue_congr (fun x hx => ?_) (fun x hx => ?_)).mpr (hL.bucket q)
      · have hxl := (List.mem_filter.mp hx).1
        rw [hlk, if_neg (hne x hxl)]
        simp only
        rw [if_neg]
        intro hc
        have hxp : x ∈ l.filter (fun x => (linkOf links x).prio == p) := by
          have hm := decode_lastCode_mem (l := l.filter (fun x => (linkOf links x).prio == p))
            (by rw [← hB, ← hc]; exact code_ne_zero x)
          rw [← hB, ← hc, decode_code] at hm; exact hm
        have h1 := (List.mem_filter.mp hx).2
        have h2 := (List.mem_filter.mp hxp).2
        simp at h1 h2; exact hq (h1.symm.trans h2)
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
  · rw [maxPrioCode_append_single, maxPrioCode_congr hprio, ← hL.maxCode, hlk, if_pos rfl]

theorem maxPrioCode_append (lk : ThreadId → RunQueueLink) (A B : List ThreadId) :
    maxPrioCode lk (A ++ B) = max (maxPrioCode lk A) (maxPrioCode lk B) := by
  unfold maxPrioCode
  induction A with
  | nil => simp
  | cons z r ih => simp only [List.cons_append, List.foldr_cons, ih]; omega

theorem maxPrioCode_cons (lk : ThreadId → RunQueueLink) (z : ThreadId) (r : List ThreadId) :
    maxPrioCode lk (z :: r) = max ((lk z).prio.val + 1) (maxPrioCode lk r) := rfl

/-- WS-ZA ZA6.9: the links after `t` joins at priority `p` **ahead of** the
queue's first thread (code `head`) and its bucket's first (code `bhead`), seL4's
`tcbSchedEnqueue` (the head of the band; `appendLinks` is `tcbSchedAppend`). -/
def prependLinks (links : RHTable ThreadId RunQueueLink) (t : ThreadId) (p : Priority)
    (head bhead : Nat) : RHTable ThreadId RunQueueLink :=
  let l1 := setLink links t
    (fun x => { x with prio := p, queued := true, prev := 0, next := head, bucketPrev := 0, bucketNext := bhead })
  let l2 := setLinkAt l1 head (fun x => { x with prev := code t })
  setLinkAt l2 bhead (fun x => { x with bucketPrev := code t })

theorem prependLinks_invExtK {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (p : Priority) (head bhead : Nat) :
    (prependLinks links t p head bhead).invExtK := by
  unfold prependLinks
  exact setLinkAt_invExtK (setLinkAt_invExtK (setLink_invExtK h _ _) _ _) _ _

theorem linkOf_prependLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (p : Priority) (head bhead : Nat)
    (ht : code t ≠ head) (hb : code t ≠ bhead) (x : ThreadId) :
    linkOf (prependLinks links t p head bhead) x =
      if x = t then
        { linkOf links t with prio := p, queued := true, prev := 0, next := head, bucketPrev := 0, bucketNext := bhead }
      else { linkOf links x with
        prev := if code x = head then code t else (linkOf links x).prev
        bucketPrev := if code x = bhead then code t else (linkOf links x).bucketPrev } := by
  unfold prependLinks
  dsimp only
  have h1 := setLink_invExtK h t
    (fun x => { x with prio := p, queued := true, prev := 0, next := head, bucketPrev := 0, bucketNext := bhead })
  have h2 := setLinkAt_invExtK h1 head (fun x => { x with prev := code t })
  rw [linkOf_setLinkAt h2.1, linkOf_setLinkAt h1.1, linkOf_setLink h.1]
  by_cases hx : x = t
  · subst hx; simp [ht, hb]
  · simp only [hx, ↓reduceIte]
    by_cases e1 : code x = head <;> by_cases e2 : code x = bhead
    · simp only [if_pos e1, if_pos e2]
    · simp only [if_pos e1, if_neg e2]
    · simp only [if_neg e1, if_pos e2]
    · simp only [if_neg e1, if_neg e2]

/-- The bucket ends after `t` joins ahead of the bucket's first thread (code
`bhead`). -/
@[inline] def prependEnds (t : ThreadId) (bhead : Nat) (e : BucketEnds) : BucketEnds :=
  { head := code t, tail := if bhead = 0 then code t else e.tail }

/-- A nonzero head code of a queue names one of its members. -/
theorem code_ne_head {l : List ThreadId} {e : Nat} (he : e = lastCode 0 l.reverse) {t : ThreadId}
    (ht : t ∉ l) : code t ≠ e := code_ne_end he (fun h => ht (List.mem_reverse.mp h))

/-- **Prepending a thread not in the queue at priority `p`** (WS-ZA ZA6.9): the
queue of `t :: l`, `t` first in its bucket. -/
theorem layout_prepend {links buckets head tail size maxCode l}
    (hL : Layout links buckets head tail size maxCode l) (hK : links.invExtK)
    (hKb : buckets.invExtK) (t : ThreadId) (p : Priority) (ht : t ∉ l) :
    Layout (prependLinks links t p head (endsOf buckets p).head)
      (setEnds buckets p (prependEnds t (endsOf buckets p).head))
      (code t) (if head = 0 then code t else tail) (size + 1) (max maxCode (p.val + 1))
      (t :: l) := by
  obtain ⟨bhead, hbh⟩ : ∃ b, b = (endsOf buckets p).head := ⟨_, rfl⟩
  rw [← hbh]
  have hBq := hL.bucket p
  rw [← hbh] at hBq
  have hH : head = lastCode 0 l.reverse := hL.queue.1
  have hB : bhead = lastCode 0 (l.filter (fun x => (linkOf links x).prio == p)).reverse := hBq.1
  have ht' : code t ≠ head := code_ne_head hH ht
  have hb' : code t ≠ bhead := code_ne_head hB (fun hm => ht (List.mem_filter.mp hm).1)
  have hlk := linkOf_prependLinks hK t p head bhead ht' hb'
  have hne : ∀ x ∈ l, x ≠ t := fun x hx e => ht (e ▸ hx)
  have hprio : ∀ x ∈ l, (linkOf (prependLinks links t p head bhead) x).prio = (linkOf links x).prio := by
    intro x hx; rw [hlk, if_neg (hne x hx)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isQueue_cons hL.queue hL.nodup (fun x hx => ?_) ?_ (fun x hx => ?_) ?_
    · rw [hlk, if_neg (hne x hx)]
    · rw [hlk, if_pos rfl]
    · rw [hlk, if_neg (hne x hx)]
    · rw [hlk, if_pos rfl]
  · exact List.nodup_cons.mpr ⟨ht, hL.nodup⟩
  · simp [hL.length]
  · intro x
    by_cases hx : x = t
    · subst hx; rw [hlk, if_pos rfl]; simp
    · rw [hlk, if_neg hx, hL.queued x]; simp [hx]
  · intro q
    rw [endsOf_setEnds hKb.1]
    by_cases hq : q = p
    · subst hq
      simp only [prependEnds]
      have hft : (t :: l).filter (fun x => (linkOf (prependLinks links t q head bhead) x).prio == q) =
          t :: l.filter (fun x => (linkOf links x).prio == q) := by
        rw [List.filter_cons, if_pos (by rw [hlk, if_pos rfl]; simp),
          List.filter_congr (q := fun x => (linkOf links x).prio == q) (fun x hx => by rw [hprio x hx])]
      rw [hft]
      refine isQueue_cons hBq (nodup_filter _ hL.nodup) (fun x hx => ?_) ?_ (fun x hx => ?_) ?_
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
      · rw [hlk, if_pos rfl]
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
      · rw [hlk, if_pos rfl]
    · simp only [if_neg hq]
      have hft : (t :: l).filter (fun x => (linkOf (prependLinks links t p head bhead) x).prio == q) =
          l.filter (fun x => (linkOf links x).prio == q) := by
        rw [List.filter_cons, if_neg (by rw [hlk, if_pos rfl]; simpa using Ne.symm hq),
          List.filter_congr (q := fun x => (linkOf links x).prio == q) (fun x hx => by rw [hprio x hx])]
      rw [hft]
      refine (isQueue_congr (fun x hx => ?_) (fun x hx => ?_)).mpr (hL.bucket q)
      · rw [hlk, if_neg (hne x (List.mem_filter.mp hx).1)]
      · have hxl := (List.mem_filter.mp hx).1
        rw [hlk, if_neg (hne x hxl)]
        simp only
        rw [if_neg]
        intro hc
        have hxp : x ∈ l.filter (fun x => (linkOf links x).prio == p) := by
          have hm := decode_lastCode_mem (l := (l.filter (fun x => (linkOf links x).prio == p)).reverse)
            (by rw [← hB, ← hc]; exact code_ne_zero x)
          rw [← hB, ← hc, decode_code] at hm; exact List.mem_reverse.mp hm
        have h1 := (List.mem_filter.mp hx).2
        have h2 := (List.mem_filter.mp hxp).2
        simp at h1 h2; exact hq (h1.symm.trans h2)
  · rw [maxPrioCode_cons, maxPrioCode_congr hprio, ← hL.maxCode, hlk, if_pos rfl]
    simp only; omega

theorem le_maxPrioCode {lk : ThreadId → RunQueueLink} {l : List ThreadId} {z : ThreadId}
    (hz : z ∈ l) : (lk z).prio.val + 1 ≤ maxPrioCode lk l := by
  induction l with
  | nil => simp at hz
  | cons y r ih =>
    rw [maxPrioCode_cons]
    rcases List.mem_cons.mp hz with rfl | h
    · omega
    · have := ih h; omega

/-- The links after the queued thread `t` leaves, its four links being `pv`,
`nx` (the queue) and `bpv`, `bnx` (its bucket): each neighbour takes over the
link `t` held towards the other, and `t`'s entry is marked not queued.  The
links are passed as words, not as `t`'s entry, so no reference to the entry is
held while it is rewritten. -/
def unlinkLinks (links : RHTable ThreadId RunQueueLink) (t : ThreadId)
    (pv nx bpv bnx : Nat) : RHTable ThreadId RunQueueLink :=
  let l1 := setLinkAt links pv (fun y => { y with next := nx })
  let l2 := setLinkAt l1 nx (fun y => { y with prev := pv })
  let l3 := setLinkAt l2 bpv (fun y => { y with bucketNext := bnx })
  let l4 := setLinkAt l3 bnx (fun y => { y with bucketPrev := bpv })
  setLink l4 t (fun y => { y with queued := false })

theorem unlinkLinks_invExtK {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (pv nx bpv bnx : Nat) : (unlinkLinks links t pv nx bpv bnx).invExtK := by
  unfold unlinkLinks
  exact setLink_invExtK (setLinkAt_invExtK (setLinkAt_invExtK (setLinkAt_invExtK
    (setLinkAt_invExtK h _ _) _ _) _ _) _ _) _ _

theorem linkOf_unlinkLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (pv nx bpv bnx : Nat)
    (h1 : code t ≠ pv) (h2 : code t ≠ nx) (h3 : code t ≠ bpv) (h4 : code t ≠ bnx) (y : ThreadId) :
    linkOf (unlinkLinks links t pv nx bpv bnx) y =
      if y = t then { linkOf links t with queued := false }
      else { linkOf links y with
        next := if code y = pv then nx else (linkOf links y).next
        prev := if code y = nx then pv else (linkOf links y).prev
        bucketNext := if code y = bpv then bnx else (linkOf links y).bucketNext
        bucketPrev := if code y = bnx then bpv else (linkOf links y).bucketPrev } := by
  have k1 := setLinkAt_invExtK h pv (fun y => { y with next := nx })
  have k2 := setLinkAt_invExtK k1 nx (fun y => { y with prev := pv })
  have k3 := setLinkAt_invExtK k2 bpv (fun y => { y with bucketNext := bnx })
  have k4 := setLinkAt_invExtK k3 bnx (fun y => { y with bucketPrev := bpv })
  unfold unlinkLinks
  dsimp only
  simp only [linkOf_setLink k4.1, linkOf_setLinkAt k3.1, linkOf_setLinkAt k2.1,
    linkOf_setLinkAt k1.1, linkOf_setLinkAt h.1]
  by_cases hy : y = t
  · subst hy; simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  · simp only [if_neg hy]
    by_cases e1 : code y = pv <;> by_cases e2 : code y = nx <;> by_cases e3 : code y = bpv <;>
      by_cases e4 : code y = bnx
    all_goals (first | simp only [if_pos e1] | simp only [if_neg e1])
    all_goals (first | simp only [if_pos e2] | simp only [if_neg e2])
    all_goals (first | simp only [if_pos e3] | simp only [if_neg e3])
    all_goals (first | simp only [if_pos e4] | simp only [if_neg e4])

/-- The bucket ends after the thread whose bucket links are `bpv`/`bnx` leaves. -/
@[inline] def unlinkEnds (bpv bnx : Nat) (e : BucketEnds) : BucketEnds :=
  { head := if bpv = 0 then bnx else e.head, tail := if bnx = 0 then bpv else e.tail }

/-- WS-ZA ZA4.5: the compiled `unlinkEnds`, branching on the old tail so the
rewrite reuses the ends' cell. -/
@[inline] def unlinkEndsImpl (bpv bnx : Nat) (e : BucketEnds) : BucketEnds :=
  let h := if bpv = 0 then bnx else e.head
  let tl := if bnx = 0 then bpv else e.tail
  if e.tail = tl then { e with head := h } else { e with head := h, tail := tl }

@[csimp] theorem unlinkEnds_eq_impl : @unlinkEnds = @unlinkEndsImpl := by
  funext bpv bnx e
  cases e with
  | mk hd tl =>
    unfold unlinkEnds unlinkEndsImpl
    by_cases h2 : bnx = 0 <;> by_cases h3 : tl = bpv <;> simp [h2, h3]

/-- The links a member holds are its neighbours' codes. -/
theorem IsQueue.mid {nx pv : ThreadId → Nat} {head tail : Nat} {A B : List ThreadId}
    {x : ThreadId} (hq : IsQueue nx pv head tail (A ++ x :: B)) :
    pv x = lastCode 0 A ∧ nx x = lastCode 0 B.reverse := by
  refine ⟨linked_mid hq.2.2.1, ?_⟩
  have hNr : Linked nx 0 (B.reverse ++ x :: A.reverse) := by
    simpa [List.reverse_append] using hq.2.2.2
  exact linked_mid hNr

theorem filter_mid {A B : List ThreadId} {t : ThreadId} {f : ThreadId → Bool} (hf : f t = true) :
    (A ++ t :: B).filter f = A.filter f ++ t :: B.filter f := by
  simp [List.filter_append, hf]

theorem filter_mid_neg {A B : List ThreadId} {t : ThreadId} {f : ThreadId → Bool}
    (hf : f t = false) : (A ++ t :: B).filter f = (A ++ B).filter f := by
  simp [List.filter_append, hf]

/-- Unlinking the member `t` of `A ++ t :: B`; the new maximum `M` is any word
equal to the remaining threads' highest priority. -/
theorem layout_unlink {links buckets head tail size maxCode} {A B : List ThreadId} {t : ThreadId}
    (hL : Layout links buckets head tail size maxCode (A ++ t :: B)) (hK : links.invExtK)
    (hKb : buckets.invExtK) (M : Nat)
    (hM : M = maxPrioCode (linkOf links) (A ++ B)) :
    let x := linkOf links t
    Layout (unlinkLinks links t x.prev x.next x.bucketPrev x.bucketNext)
      (setEnds buckets x.prio (unlinkEnds x.bucketPrev x.bucketNext))
      (if x.prev = 0 then x.next else head) (if x.next = 0 then x.prev else tail)
      (size - 1) M (A ++ B) := by
  intro x
  have hnd := hL.nodup
  obtain ⟨hndA, hndtB, hAtB⟩ := List.nodup_append.mp hnd
  obtain ⟨htB, hndB⟩ := List.nodup_cons.mp hndtB
  have htA : t ∉ A := fun h => hAtB t h t (List.mem_cons_self ..) rfl
  have hne : ∀ z ∈ A ++ B, z ≠ t := by
    intro z hz e; subst e
    rcases List.mem_append.mp hz with h | h
    · exact htA h
    · exact htB h
  let fp := fun z => (linkOf links z).prio == x.prio
  have hfp : fp t = true := by simp [fp, x]
  have hBq := hL.bucket x.prio
  rw [filter_mid hfp] at hBq
  obtain ⟨hpv, hnx⟩ := IsQueue.mid hL.queue
  obtain ⟨hbpv, hbnx⟩ := IsQueue.mid hBq
  have c1 : code t ≠ x.prev := by rw [show x.prev = _ from hpv]; exact code_ne_end rfl htA
  have c2 : code t ≠ x.next := by
    rw [show x.next = _ from hnx]; exact code_ne_end rfl (by simpa using htB)
  have c3 : code t ≠ x.bucketPrev := by
    rw [show x.bucketPrev = _ from hbpv]
    exact code_ne_end rfl (fun h => htA (List.mem_filter.mp h).1)
  have c4 : code t ≠ x.bucketNext := by
    rw [show x.bucketNext = _ from hbnx]
    exact code_ne_end rfl (fun h => htB (List.mem_filter.mp (List.mem_reverse.mp h)).1)
  have hlk := linkOf_unlinkLinks hK t x.prev x.next x.bucketPrev x.bucketNext c1 c2 c3 c4
  have hprio : ∀ z ∈ A ++ B,
      (linkOf (unlinkLinks links t x.prev x.next x.bucketPrev x.bucketNext) z).prio =
        (linkOf links z).prio := by
    intro z hz; rw [hlk, if_neg (hne z hz)]
  -- a member coded by a nonzero `lastCode` of a sublist lies in it
  have hmemCode : ∀ (L : List ThreadId) (z : ThreadId), code z = lastCode 0 L → z ∈ L := by
    intro L z hc
    have hm := decode_lastCode_mem (l := L) (by rw [← hc]; exact code_ne_zero z)
    rwa [← hc, decode_code] at hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isQueue_unlink hL.queue hnd (fun z hz => ?_) (fun z hz => ?_)
    · rw [hlk, if_neg (hne z hz)]
    · rw [hlk, if_neg (hne z hz)]
  · exact List.nodup_append.mpr ⟨hndA, hndB, fun a ha b hb => hAtB a ha b (List.mem_cons_of_mem _ hb)⟩
  · have := hL.length; simp at this ⊢; omega
  · intro z
    by_cases hz : z = t
    · subst hz; rw [hlk, if_pos rfl]; simp [htA, htB]
    · rw [hlk, if_neg hz, hL.queued z]; simp [hz]
  · intro q
    rw [List.filter_congr (fun z hz => by rw [hprio z hz]), endsOf_setEnds hKb.1]
    by_cases hq : q = x.prio
    · subst hq
      rw [if_pos rfl, List.filter_append]
      refine isQueue_unlink hBq (by rw [← filter_mid hfp]; exact nodup_filter _ hnd)
        (fun z hz => ?_) (fun z hz => ?_)
      · have hz' : z ∈ A ++ B := by
          rcases List.mem_append.mp hz with h | h
          · exact List.mem_append_left _ (List.mem_filter.mp h).1
          · exact List.mem_append_right _ (List.mem_filter.mp h).1
        rw [hlk, if_neg (hne z hz')]
      · have hz' : z ∈ A ++ B := by
          rcases List.mem_append.mp hz with h | h
          · exact List.mem_append_left _ (List.mem_filter.mp h).1
          · exact List.mem_append_right _ (List.mem_filter.mp h).1
        rw [hlk, if_neg (hne z hz')]
    · rw [if_neg hq]
      have hft : (fun z => (linkOf links z).prio == q) t = false := by simp [x] at hq ⊢; exact Ne.symm hq
      rw [← filter_mid_neg hft]
      refine (isQueue_congr (fun z hz => ?_) (fun z hz => ?_)).mpr (hL.bucket q)
      all_goals
        obtain ⟨hzl, hzq⟩ := List.mem_filter.mp hz
        have hzt : z ≠ t := by
          intro e
          have hft' : ((linkOf links t).prio == q) = false := hft
          rw [e, hft'] at hzq; exact absurd hzq (by simp)
        have hzq' : (linkOf links z).prio = q := by simpa using hzq
        rw [hlk, if_neg hzt]
        simp only
        rw [if_neg]
        intro hc
      · rw [hbpv] at hc
        have hm := List.mem_filter.mp (hmemCode _ z hc)
        have : (linkOf links z).prio = x.prio := by simpa [fp] using hm.2
        exact hq (hzq'.symm.trans this)
      · rw [hbnx] at hc
        have hm := List.mem_filter.mp (List.mem_reverse.mp (hmemCode _ z hc))
        have : (linkOf links z).prio = x.prio := by simpa [fp] using hm.2
        exact hq (hzq'.symm.trans this)
  · rw [hM]; exact (maxPrioCode_congr hprio).symm

theorem Layout.with_maxCode {links buckets head tail size M M' l}
    (h : Layout links buckets head tail size M l) (e : M = M') :
    Layout links buckets head tail size M' l := e ▸ h

/-- Enqueue `tid` at priority `prio` behind every queued thread; a thread
already queued is left where it is. -/
def insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if hc : rq.contains tid then rq
  else
    let btail := (endsOf rq.buckets prio).tail
    { links := appendLinks rq.links tid prio rq.tail btail
      buckets := setEnds rq.buckets prio (appendEnds tid btail)
      head := if rq.tail = 0 then code tid else rq.head
      tail := code tid
      size := rq.size + 1
      maxCode := max rq.maxCode (prio.val + 1)
      links_invExtK := appendLinks_invExtK rq.links_invExtK _ _ _ _
      buckets_invExtK := setEnds_invExtK rq.buckets_invExtK _ _
      layout := (layout_append rq.layout rq.links_invExtK rq.buckets_invExtK tid prio
        (fun h => hc ((rq.layout.queued tid).mpr h))).self }

theorem toList_insert_not_mem (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (h : ¬(tid ∈ rq)) : (rq.insert tid prio).toList = rq.toList ++ [tid] := by
  unfold insert
  rw [dif_neg (show ¬(rq.contains tid = true) from h)]
  exact (layout_append rq.layout rq.links_invExtK rq.buckets_invExtK tid prio
    (fun h' => h ((rq.layout.queued tid).mpr h'))).walk_eq

theorem contains_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    (rq.insert tid prio).contains x = (rq.contains x || x == tid) := by
  unfold insert
  by_cases hc : rq.contains tid
  · rw [dif_pos hc]
    by_cases hx : x = tid
    · subst hx; simp [hc]
    · simp [hx]
  · rw [dif_neg hc]
    unfold contains
    rw [linkOf_appendLinks rq.links_invExtK]
    · by_cases hx : x = tid
      · subst hx; simp
      · simp [hx]
    · exact code_ne_end rq.layout.queue.2.1 (fun h => hc ((rq.layout.queued tid).mpr h))
    · exact code_ne_end (rq.layout.bucket prio).2.1
        (fun h => hc ((rq.layout.queued tid).mpr (List.mem_filter.mp h).1))

/-- WS-ZA ZA6.9: enqueue `tid` at priority `prio` **ahead of** every queued
thread, first in its bucket (seL4's `tcbSchedEnqueue`; `insert` is
`tcbSchedAppend`); a thread already queued is left where it is. -/
def insertHead (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if hc : rq.contains tid then rq
  else
    let bhead := (endsOf rq.buckets prio).head
    { links := prependLinks rq.links tid prio rq.head bhead
      buckets := setEnds rq.buckets prio (prependEnds tid bhead)
      head := code tid
      tail := if rq.head = 0 then code tid else rq.tail
      size := rq.size + 1
      maxCode := max rq.maxCode (prio.val + 1)
      links_invExtK := prependLinks_invExtK rq.links_invExtK _ _ _ _
      buckets_invExtK := setEnds_invExtK rq.buckets_invExtK _ _
      layout := (layout_prepend rq.layout rq.links_invExtK rq.buckets_invExtK tid prio
        (fun h => hc ((rq.layout.queued tid).mpr h))).self }

theorem toList_insertHead_not_mem (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (h : ¬(tid ∈ rq)) : (rq.insertHead tid prio).toList = tid :: rq.toList := by
  unfold insertHead
  rw [dif_neg (show ¬(rq.contains tid = true) from h)]
  exact (layout_prepend rq.layout rq.links_invExtK rq.buckets_invExtK tid prio
    (fun h' => h ((rq.layout.queued tid).mpr h'))).walk_eq

theorem insertHead_of_mem (rq : RunQueue) (tid : ThreadId) (prio : Priority) (h : tid ∈ rq) :
    rq.insertHead tid prio = rq := by
  unfold insertHead; rw [dif_pos (show rq.contains tid = true from h)]

theorem contains_insertHead (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    (rq.insertHead tid prio).contains x = (rq.contains x || x == tid) := by
  unfold insertHead
  by_cases hc : rq.contains tid
  · rw [dif_pos hc]
    by_cases hx : x = tid
    · subst hx; simp [hc]
    · simp [hx]
  · rw [dif_neg hc]
    unfold contains
    rw [linkOf_prependLinks rq.links_invExtK]
    · by_cases hx : x = tid
      · subst hx; simp
      · simp [hx]
    · exact code_ne_head rq.layout.queue.1 (fun h => hc ((rq.layout.queued tid).mpr h))
    · exact code_ne_head (rq.layout.bucket prio).1
        (fun h => hc ((rq.layout.queued tid).mpr (List.mem_filter.mp h).1))

theorem links_insertHead_of_not_contains {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false)
    (p : Priority) :
    (rq.insertHead t p).links = prependLinks rq.links t p rq.head (endsOf rq.buckets p).head := by
  unfold insertHead; rw [dif_neg (by rw [h]; decide)]

theorem maxPrioCode_mid (lk : ThreadId → RunQueueLink) (A B : List ThreadId) (t : ThreadId) :
    maxPrioCode lk (A ++ t :: B) = max (maxPrioCode lk (A ++ B)) ((lk t).prio.val + 1) := by
  rw [maxPrioCode_append, maxPrioCode_cons, maxPrioCode_append]; omega

/-- When the leaving thread `t` shares its bucket, or was not at the highest
priority, the highest priority is unchanged by its leaving. -/
theorem maxCode_unlink_keep {links buckets head tail size maxCode} {A B : List ThreadId}
    {t : ThreadId} (hL : Layout links buckets head tail size maxCode (A ++ t :: B))
    (hn : ¬((linkOf links t).bucketPrev = 0 ∧ (linkOf links t).bucketNext = 0 ∧
      maxCode = (linkOf links t).prio.val + 1)) :
    maxCode = maxPrioCode (linkOf links) (A ++ B) := by
  have hmax := hL.maxCode
  rw [maxPrioCode_mid] at hmax
  let fp := fun z => (linkOf links z).prio == (linkOf links t).prio
  have hBq := hL.bucket (linkOf links t).prio
  rw [filter_mid (f := fp) (by simp [fp])] at hBq
  obtain ⟨hbpv, hbnx⟩ := IsQueue.mid hBq
  have hmemCode : ∀ (L : List ThreadId) (z : ThreadId), code z = lastCode 0 L → z ∈ L := by
    intro L z hc
    have hm := decode_lastCode_mem (l := L) (by rw [← hc]; exact code_ne_zero z)
    rwa [← hc, decode_code] at hm
  by_cases hb : (linkOf links t).bucketPrev = 0 ∧ (linkOf links t).bucketNext = 0
  · have hm : maxCode ≠ (linkOf links t).prio.val + 1 := fun e => hn ⟨hb.1, hb.2, e⟩
    omega
  · -- some other thread of the bucket remains
    have : ∃ z ∈ A ++ B, (linkOf links z).prio = (linkOf links t).prio := by
      by_cases h1 : (linkOf links t).bucketPrev = 0
      · have h2 : (linkOf links t).bucketNext ≠ 0 := fun e => hb ⟨h1, e⟩
        have hm := decode_lastCode_mem (hbnx ▸ h2)
        rw [← hbnx] at hm
        obtain ⟨hz, hzp⟩ := List.mem_filter.mp (List.mem_reverse.mp hm)
        exact ⟨_, List.mem_append_right _ hz, by simpa [fp] using hzp⟩
      · have hm := decode_lastCode_mem (hbpv ▸ h1)
        rw [← hbpv] at hm
        obtain ⟨hz, hzp⟩ := List.mem_filter.mp hm
        exact ⟨_, List.mem_append_left _ hz, by simpa [fp] using hzp⟩
    obtain ⟨z, hz, hzp⟩ := this
    have := le_maxPrioCode (lk := linkOf links) hz
    rw [hzp] at this
    omega

/-- The members around a queued thread. -/
theorem split_of_contains (rq : RunQueue) {tid : ThreadId} (hc : rq.contains tid = true) :
    ∃ A B, rq.toList = A ++ tid :: B :=
  List.append_of_mem ((rq.layout.queued tid).mp hc)

/-- Dequeue `tid`; a thread not queued leaves the queue unchanged.  Its four
links are read before any entry is written, so its entry is held by no other
reference when it is marked not queued.  The highest priority is recomputed
(`maxPrioCode` over the remaining threads) only when `tid` was alone at the
highest priority. -/
def remove (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  if hc : rq.contains tid then
    let x := linkOf rq.links tid
    let pv := x.prev
    let nx := x.next
    let bpv := x.bucketPrev
    let bnx := x.bucketNext
    let p := x.prio
    let links' := unlinkLinks rq.links tid pv nx bpv bnx
    let head' := if pv = 0 then nx else rq.head
    { links := links'
      buckets := setEnds rq.buckets p (unlinkEnds bpv bnx)
      head := head'
      tail := if nx = 0 then pv else rq.tail
      size := rq.size - 1
      maxCode := if bpv = 0 ∧ bnx = 0 ∧ rq.maxCode = p.val + 1
        then maxPrioCodeWalk links' (rq.size - 1) head' 0
        else rq.maxCode
      links_invExtK := unlinkLinks_invExtK rq.links_invExtK _ _ _ _ _
      buckets_invExtK := setEnds_invExtK rq.buckets_invExtK _ _
      layout := by
        obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
        have hL := rq.layout
        rw [show walk (nextOf rq.links) rq.size rq.head = rq.toList from rfl, hAB] at hL
        have h0 := layout_unlink hL rq.links_invExtK rq.buckets_invExtK _ rfl
        apply Layout.self
        refine h0.with_maxCode ?_
        split
        · next hm =>
          rw [maxPrioCodeWalk_eq, Nat.zero_max, h0.walk_eq]; exact h0.maxCode
        · next hm => exact (maxCode_unlink_keep hL hm).symm }
  else rq

theorem filter_ne_mid {A B : List ThreadId} {t : ThreadId} (h : (A ++ t :: B).Nodup) :
    (A ++ t :: B).filter (fun x => decide (x ≠ t)) = A ++ B := by
  obtain ⟨_, hndtB, hAtB⟩ := List.nodup_append.mp h
  have htA : t ∉ A := fun hm => hAtB t hm t (List.mem_cons_self ..) rfl
  have htB : t ∉ B := (List.nodup_cons.mp hndtB).1
  rw [List.filter_append, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_eq_self.mpr (fun x hx => by simp; exact fun e => htA (e ▸ hx)),
    List.filter_eq_self.mpr (fun x hx => by simp; exact fun e => htB (e ▸ hx))]

/-- Dequeue removes exactly `tid`, keeping every other thread in its place. -/
theorem toList_remove (rq : RunQueue) (tid : ThreadId) :
    (rq.remove tid).toList = rq.toList.filter (fun x => decide (x ≠ tid)) := by
  unfold remove
  by_cases hc : rq.contains tid
  · rw [dif_pos hc]
    obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
    have hL := rq.layout
    rw [show walk (nextOf rq.links) rq.size rq.head = rq.toList from rfl, hAB] at hL
    rw [hAB, filter_ne_mid (hAB ▸ rq.toList_nodup)]
    exact (layout_unlink hL rq.links_invExtK rq.buckets_invExtK _ rfl).walk_eq
  · rw [dif_neg hc]
    refine (List.filter_eq_self.mpr fun x hx => ?_).symm
    simp only [ne_eq, decide_eq_true_eq]
    intro e; subst e; exact hc ((rq.mem_toList_iff_mem x).mp hx)

theorem contains_remove (rq : RunQueue) (tid x : ThreadId) :
    (rq.remove tid).contains x = (rq.contains x && !(x == tid)) := by
  have h1 := (rq.remove tid).mem_toList_iff_mem x
  have h2 := rq.mem_toList_iff_mem x
  rw [toList_remove, List.mem_filter] at h1
  by_cases hx : x = tid
  · subst hx
    have : (rq.remove x).contains x = false := by
      cases h : (rq.remove x).contains x
      · rfl
      · exact absurd (h1.mpr h) (by simp)
    simp [this]
  · have : (rq.remove tid).contains x = rq.contains x := by
      cases h : rq.contains x <;> cases h' : (rq.remove tid).contains x
      · rfl
      · exact absurd (h2.mp (h1.mpr h').1) (by simp [Membership.mem, h])
      · exact absurd (h1.mp ⟨h2.mpr h, by simp [hx]⟩) (by simp [Membership.mem, h'])
      · rfl
    simp [this, hx]

theorem Layout.with_size {links buckets head tail size size' M l}
    (h : Layout links buckets head tail size M l) (e : size = size') :
    Layout links buckets head tail size' M l := e ▸ h

/-- Move the queued `tid` behind every other queued thread, in the queue and in
its bucket; a thread not queued leaves the queue unchanged.  The set of queued
threads and their priorities do not change, so neither does the size or the
highest priority. -/
def rotateToBack (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  if hc : rq.contains tid then
    let x := linkOf rq.links tid
    let pv := x.prev
    let nx := x.next
    let bpv := x.bucketPrev
    let bnx := x.bucketNext
    let p := x.prio
    let links1 := unlinkLinks rq.links tid pv nx bpv bnx
    let buckets1 := setEnds rq.buckets p (unlinkEnds bpv bnx)
    let head1 := if pv = 0 then nx else rq.head
    let tail1 := if nx = 0 then pv else rq.tail
    let btail := (endsOf buckets1 p).tail
    { links := appendLinks links1 tid p tail1 btail
      buckets := setEnds buckets1 p (appendEnds tid btail)
      head := if tail1 = 0 then code tid else head1
      tail := code tid
      size := rq.size
      maxCode := rq.maxCode
      links_invExtK := appendLinks_invExtK (unlinkLinks_invExtK rq.links_invExtK _ _ _ _ _) _ _ _ _
      buckets_invExtK := setEnds_invExtK (setEnds_invExtK rq.buckets_invExtK _ _) _ _
      layout := by
        obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
        have hL := rq.layout
        rw [show walk (nextOf rq.links) rq.size rq.head = rq.toList from rfl, hAB] at hL
        have h0 := layout_unlink hL rq.links_invExtK rq.buckets_invExtK _ rfl
        have htAB : tid ∉ A ++ B := by
          obtain ⟨_, hndtB, hAtB⟩ := List.nodup_append.mp hL.nodup
          intro h
          rcases List.mem_append.mp h with h | h
          · exact hAtB tid h tid (List.mem_cons_self ..) rfl
          · exact (List.nodup_cons.mp hndtB).1 h
        have h1 := layout_append h0 (unlinkLinks_invExtK rq.links_invExtK _ _ _ _ _)
          (setEnds_invExtK rq.buckets_invExtK _ _) tid (linkOf rq.links tid).prio htAB
        apply Layout.self
        refine (h1.with_size ?_).with_maxCode ?_
        · have := hL.length; simp at this; omega
        · have := hL.maxCode; rw [maxPrioCode_mid] at this; rw [this] }
  else rq

-- ============================================================================
-- In-place forms of enqueue, dequeue and rotation
-- ============================================================================

/-! The compiled forms of `insert`, `remove` and `rotateToBack` (WS-ZA ZA4.5).
Each tests membership first and returns the queue untouched when there is
nothing to do; otherwise it hands the queue to a helper whose first act is to
take the record apart, so the record's cell is free when the result is built
and the result is written into it.  A record built from fresh field values in
the same function as the membership test is a new allocation: the test keeps
the old record alive past the point where its cell could be handed on.  Each
helper's queue layout is the one the specification proves, read off its
result (`insertImpl_eq`, `removeImpl_eq`, `rotateToBackImpl_eq`). -/

/-- `insert` for a thread not yet queued, written into `rq`'s cell. -/
@[noinline] def insertFresh (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (hc : ¬rq.contains tid) : RunQueue :=
  match rq, hc with
  | ⟨links, buckets, head, tail, size, maxCode, hl, hb, lay⟩, hc =>
    let btail := (endsOf buckets prio).tail
    { links := appendLinks links tid prio tail btail
      buckets := setEnds buckets prio (appendEnds tid btail)
      head := if tail = 0 then code tid else head
      tail := code tid
      size := size + 1
      maxCode := max maxCode (prio.val + 1)
      links_invExtK := appendLinks_invExtK hl _ _ _ _
      buckets_invExtK := setEnds_invExtK hb _ _
      layout := (layout_append lay hl hb tid prio
        (fun h => hc ((lay.queued tid).mpr h))).self }

def insertImpl (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if hc : rq.contains tid then rq else rq.insertFresh tid prio hc

@[csimp] theorem insertImpl_eq : @insert = @insertImpl := by
  funext rq tid prio; cases rq; simp only [insertImpl, insertFresh, insert, contains]

/-- `remove` for a queued thread, written into `rq`'s cell. -/
@[noinline] def removeQueued (rq : RunQueue) (tid : ThreadId) (hc : rq.contains tid) :
    RunQueue :=
  match rq, hc with
  | ⟨links, buckets, head, tail, size, maxCode, hl, hb, lay⟩, hc =>
    let x := linkOf links tid
    let pv := x.prev
    let nx := x.next
    let bpv := x.bucketPrev
    let bnx := x.bucketNext
    let p := x.prio
    let links' := unlinkLinks links tid pv nx bpv bnx
    let head' := if pv = 0 then nx else head
    { links := links'
      buckets := setEnds buckets p (unlinkEnds bpv bnx)
      head := head'
      tail := if nx = 0 then pv else tail
      size := size - 1
      maxCode := if bpv = 0 ∧ bnx = 0 ∧ maxCode = p.val + 1
        then maxPrioCodeWalk links' (size - 1) head' 0
        else maxCode
      links_invExtK := unlinkLinks_invExtK hl _ _ _ _ _
      buckets_invExtK := setEnds_invExtK hb _ _
      layout := by
        let q : RunQueue := ⟨links, buckets, head, tail, size, maxCode, hl, hb, lay⟩
        have h := (remove q tid).layout
        unfold remove at h
        rw [dif_pos (show q.contains tid = true from hc)] at h
        exact h }

def removeImpl (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  if hc : rq.contains tid then rq.removeQueued tid hc else rq

@[csimp] theorem removeImpl_eq : @remove = @removeImpl := by
  funext rq tid; cases rq; simp only [removeImpl, removeQueued, remove, contains]

/-- `rotateToBack` for a queued thread, written into `rq`'s cell. -/
@[noinline] def rotateQueued (rq : RunQueue) (tid : ThreadId) (hc : rq.contains tid) :
    RunQueue :=
  match rq, hc with
  | ⟨links, buckets, head, tail, size, maxCode, hl, hb, lay⟩, hc =>
    let x := linkOf links tid
    let pv := x.prev
    let nx := x.next
    let bpv := x.bucketPrev
    let bnx := x.bucketNext
    let p := x.prio
    let links1 := unlinkLinks links tid pv nx bpv bnx
    let buckets1 := setEnds buckets p (unlinkEnds bpv bnx)
    let head1 := if pv = 0 then nx else head
    let tail1 := if nx = 0 then pv else tail
    let btail := (endsOf buckets1 p).tail
    { links := appendLinks links1 tid p tail1 btail
      buckets := setEnds buckets1 p (appendEnds tid btail)
      head := if tail1 = 0 then code tid else head1
      tail := code tid
      size := size
      maxCode := maxCode
      links_invExtK := appendLinks_invExtK (unlinkLinks_invExtK hl _ _ _ _ _) _ _ _ _
      buckets_invExtK := setEnds_invExtK (setEnds_invExtK hb _ _) _ _
      layout := by
        let q : RunQueue := ⟨links, buckets, head, tail, size, maxCode, hl, hb, lay⟩
        have h := (rotateToBack q tid).layout
        unfold rotateToBack at h
        rw [dif_pos (show q.contains tid = true from hc)] at h
        exact h }

def rotateToBackImpl (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  if hc : rq.contains tid then rq.rotateQueued tid hc else rq

@[csimp] theorem rotateToBackImpl_eq : @rotateToBack = @rotateToBackImpl := by
  funext rq tid; cases rq; simp only [rotateToBackImpl, rotateQueued, rotateToBack, contains]

-- ============================================================================
-- Views: membership, order, priorities, buckets
-- ============================================================================

@[simp] theorem mem_iff_contains {rq : RunQueue} {tid : ThreadId} :
    tid ∈ rq ↔ rq.contains tid = true := Iff.rfl

theorem contains_false_of_not_mem {rq : RunQueue} {tid : ThreadId}
    (h : ¬(tid ∈ rq)) : rq.contains tid = false := by
  cases hc : rq.contains tid <;> simp_all

@[simp] theorem toList_empty : (empty : RunQueue).toList = [] := by
  unfold toList; simp [empty]

theorem not_mem_empty (tid : ThreadId) : ¬(tid ∈ (empty : RunQueue)) := by
  rw [← mem_toList_iff_mem, toList_empty]; simp

theorem not_mem_toList_of_not_mem (rq : RunQueue) (tid : ThreadId)
    (h : ¬(tid ∈ rq)) : tid ∉ rq.toList := fun h' => h ((rq.mem_toList_iff_mem tid).mp h')

theorem membership_implies_flat (rq : RunQueue) (tid : ThreadId)
    (h : tid ∈ rq) : tid ∈ rq.toList := (rq.mem_toList_iff_mem tid).mpr h

theorem mem_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    x ∈ rq.insert tid prio ↔ x ∈ rq ∨ x = tid := by
  simp only [mem_iff_contains, contains_insert, Bool.or_eq_true, beq_iff_eq]

theorem mem_remove (rq : RunQueue) (tid : ThreadId) (x : ThreadId) :
    x ∈ rq.remove tid ↔ x ∈ rq ∧ x ≠ tid := by
  simp only [mem_iff_contains, contains_remove, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]

/-- Re-key `tid` at priority `prio` when the queue holds it (remove, then insert
at the new bucket's tail); a queue that does not hold `tid` is left as is. -/
def rekey (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if rq.contains tid then (rq.remove tid).insert tid prio else rq

/-- A re-key moves no thread into or out of the queue. -/
@[simp] theorem contains_rekey (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    (rq.rekey tid prio).contains x = rq.contains x := by
  unfold rekey
  split
  · rename_i h
    rw [contains_insert, contains_remove]
    by_cases hx : x = tid
    · subst hx; rw [h, beq_self_eq_true]; rfl
    · rw [beq_false_of_ne hx]; cases rq.contains x <;> rfl
  · rfl

theorem mem_rekey (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    x ∈ rq.rekey tid prio ↔ x ∈ rq := by
  simp only [mem_iff_contains, contains_rekey]

theorem rekey_of_contains {rq : RunQueue} {tid : ThreadId} (prio : Priority)
    (h : rq.contains tid = true) : rq.rekey tid prio = (rq.remove tid).insert tid prio := by
  unfold rekey; rw [if_pos h]

theorem not_mem_remove_self (rq : RunQueue) (tid : ThreadId) : ¬(tid ∈ rq.remove tid) := by
  rw [mem_remove]; exact fun ⟨_, hne⟩ => hne rfl

theorem remove_of_not_mem (rq : RunQueue) (tid : ThreadId) (h : tid ∉ rq) : rq.remove tid = rq := by
  unfold remove; rw [dif_neg (show ¬(rq.contains tid = true) from h)]

theorem insert_of_mem (rq : RunQueue) (tid : ThreadId) (prio : Priority) (h : tid ∈ rq) :
    rq.insert tid prio = rq := by
  unfold insert; rw [dif_pos (show rq.contains tid = true from h)]

theorem toList_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) :
    (rq.insert tid prio).toList = if tid ∈ rq then rq.toList else rq.toList ++ [tid] := by
  by_cases h : tid ∈ rq
  · rw [if_pos h, insert_of_mem rq tid prio h]
  · rw [if_neg h]; exact toList_insert_not_mem rq tid prio h

theorem rotateToBack_of_not_mem (rq : RunQueue) (tid : ThreadId) (h : tid ∉ rq) :
    rq.rotateToBack tid = rq := by
  unfold rotateToBack; rw [dif_neg (show ¬(rq.contains tid = true) from h)]

theorem toList_rotateToBack (rq : RunQueue) (tid : ThreadId) :
    (rq.rotateToBack tid).toList =
      if tid ∈ rq then rq.toList.filter (fun x => decide (x ≠ tid)) ++ [tid] else rq.toList := by
  by_cases hc : tid ∈ rq
  · rw [if_pos hc]
    unfold rotateToBack
    rw [dif_pos (show rq.contains tid = true from hc)]
    obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
    have hL := rq.layout
    rw [show walk (nextOf rq.links) rq.size rq.head = rq.toList from rfl, hAB] at hL
    have h0 := layout_unlink hL rq.links_invExtK rq.buckets_invExtK _ rfl
    have htAB : tid ∉ A ++ B := by
      obtain ⟨_, hndtB, hAtB⟩ := List.nodup_append.mp hL.nodup
      intro h
      rcases List.mem_append.mp h with h | h
      · exact hAtB tid h tid (List.mem_cons_self ..) rfl
      · exact (List.nodup_cons.mp hndtB).1 h
    have h1 := layout_append h0 (unlinkLinks_invExtK rq.links_invExtK _ _ _ _ _)
      (setEnds_invExtK rq.buckets_invExtK _ _) tid (linkOf rq.links tid).prio htAB
    rw [hAB, filter_ne_mid (hAB ▸ rq.toList_nodup)]
    have hs : rq.size = rq.size - 1 + 1 := by have := hL.length; simp at this; omega
    have hw := h1.walk_eq
    rw [← hs] at hw
    exact hw
  · rw [if_neg hc, rotateToBack_of_not_mem rq tid hc]

theorem contains_rotateToBack (rq : RunQueue) (tid t : ThreadId) :
    (rq.rotateToBack tid).contains t = rq.contains t := by
  have h1 := (rq.rotateToBack tid).mem_toList_iff_mem t
  have h2 := rq.mem_toList_iff_mem t
  have key : t ∈ (rq.rotateToBack tid).toList ↔ t ∈ rq.toList := by
    rw [toList_rotateToBack]
    split
    · next hc =>
      simp only [List.mem_append, List.mem_filter, List.mem_singleton, ne_eq, decide_eq_true_eq]
      constructor
      · rintro (⟨h, _⟩ | rfl)
        · exact h
        · exact (rq.mem_toList_iff_mem _).mpr hc
      · intro h; by_cases e : t = tid
        · exact Or.inr e
        · exact Or.inl ⟨h, e⟩
    · exact Iff.rfl
  cases e1 : (rq.rotateToBack tid).contains t <;> cases e2 : rq.contains t <;> try rfl
  · exact absurd (h1.mp (key.mpr (h2.mpr e2))) (by simp [Membership.mem, e1])
  · exact absurd (h2.mp (key.mp (h1.mpr e1))) (by simp [Membership.mem, e2])

theorem mem_rotateToBack (rq : RunQueue) (tid x : ThreadId) :
    x ∈ rq.rotateToBack tid ↔ x ∈ rq := by
  simp only [mem_iff_contains, contains_rotateToBack]

theorem prio_setLinkAt {links : RHTable ThreadId RunQueueLink} (h : links.invExt) (c : Nat)
    {g : RunQueueLink → RunQueueLink} (hg : ∀ y, (g y).prio = y.prio) (x : ThreadId) :
    (linkOf (setLinkAt links c g) x).prio = (linkOf links x).prio := by
  rw [linkOf_setLinkAt h]; split
  · exact hg _
  · rfl

theorem prio_unlinkLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (pv nx bpv bnx : Nat) (x : ThreadId) :
    (linkOf (unlinkLinks links t pv nx bpv bnx) x).prio = (linkOf links x).prio := by
  have k1 := setLinkAt_invExtK h pv (fun y => { y with next := nx })
  have k2 := setLinkAt_invExtK k1 nx (fun y => { y with prev := pv })
  have k3 := setLinkAt_invExtK k2 bpv (fun y => { y with bucketNext := bnx })
  have k4 := setLinkAt_invExtK k3 bnx (fun y => { y with bucketPrev := bpv })
  unfold unlinkLinks
  dsimp only
  rw [linkOf_setLink k4.1]
  have : ∀ y, (linkOf (setLinkAt (setLinkAt (setLinkAt (setLinkAt links pv
      (fun y => { y with next := nx })) nx (fun y => { y with prev := pv }))
      bpv (fun y => { y with bucketNext := bnx })) bnx (fun y => { y with bucketPrev := bpv })) y).prio
      = (linkOf links y).prio := by
    intro y
    rw [prio_setLinkAt (g := fun y => { y with bucketPrev := bpv }) k3.1 _ (fun _ => rfl),
      prio_setLinkAt (g := fun y => { y with bucketNext := bnx }) k2.1 _ (fun _ => rfl),
      prio_setLinkAt (g := fun y => { y with prev := pv }) k1.1 _ (fun _ => rfl),
      prio_setLinkAt (g := fun y => { y with next := nx }) h.1 _ (fun _ => rfl)]
  split
  · next e => subst e; exact this _
  · exact this _

theorem queued_unlinkLinks {links : RHTable ThreadId RunQueueLink} (h : links.invExtK)
    (t : ThreadId) (pv nx bpv bnx : Nat) (x : ThreadId) :
    (linkOf (unlinkLinks links t pv nx bpv bnx) x).queued =
      (if x = t then false else (linkOf links x).queued) := by
  have k1 := setLinkAt_invExtK h pv (fun y => { y with next := nx })
  have k2 := setLinkAt_invExtK k1 nx (fun y => { y with prev := pv })
  have k3 := setLinkAt_invExtK k2 bpv (fun y => { y with bucketNext := bnx })
  have k4 := setLinkAt_invExtK k3 bnx (fun y => { y with bucketPrev := bpv })
  have hq : ∀ {L : RHTable ThreadId RunQueueLink} (hL : L.invExt) (c : Nat)
      {g : RunQueueLink → RunQueueLink} (hg : ∀ y, (g y).queued = y.queued) (y : ThreadId),
      (linkOf (setLinkAt L c g) y).queued = (linkOf L y).queued := by
    intro L hL c g hg y; rw [linkOf_setLinkAt hL]; split
    · exact hg _
    · rfl
  unfold unlinkLinks
  dsimp only
  rw [linkOf_setLink k4.1]
  split
  · rfl
  · rw [hq (g := fun y => { y with bucketPrev := bpv }) k3.1 _ (fun _ => rfl),
      hq (g := fun y => { y with bucketNext := bnx }) k2.1 _ (fun _ => rfl),
      hq (g := fun y => { y with prev := pv }) k1.1 _ (fun _ => rfl),
      hq (g := fun y => { y with next := nx }) h.1 _ (fun _ => rfl)]

theorem priorityOf_remove (rq : RunQueue) (tid x : ThreadId) :
    (rq.remove tid).priorityOf x = if x = tid then none else rq.priorityOf x := by
  by_cases hc : rq.contains tid
  · unfold priorityOf
    rw [contains_remove]
    by_cases hx : x = tid
    · simp [hx]
    · simp only [hx, ↓reduceIte, Bool.and_true,
        show (x == tid) = false from by simp [hx], Bool.not_false]
      unfold remove
      rw [dif_pos hc]
      simp only [prio_unlinkLinks rq.links_invExtK]
  · rw [remove_of_not_mem rq tid hc]
    by_cases hx : x = tid
    · subst hx; simp [priorityOf, show rq.contains x = false from by simpa using hc]
    · simp [hx]

theorem priorityOf_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    (rq.insert tid prio).priorityOf x =
      if rq.contains tid then rq.priorityOf x
      else if x = tid then some prio else rq.priorityOf x := by
  by_cases hc : rq.contains tid
  · rw [if_pos hc, insert_of_mem rq tid prio hc]
  · rw [if_neg hc]
    unfold priorityOf
    rw [contains_insert]
    unfold insert
    rw [dif_neg hc]
    simp only [prio_appendLinks rq.links_invExtK]
    by_cases hx : x = tid
    · simp [hx]
    · simp [hx]

theorem priorityOf_rotateToBack (rq : RunQueue) (tid x : ThreadId) :
    (rq.rotateToBack tid).priorityOf x = rq.priorityOf x := by
  by_cases hc : rq.contains tid
  · unfold priorityOf
    rw [contains_rotateToBack]
    unfold rotateToBack
    rw [dif_pos hc]
    simp only [prio_appendLinks (unlinkLinks_invExtK rq.links_invExtK _ _ _ _ _),
      prio_unlinkLinks rq.links_invExtK]
    by_cases hx : x = tid
    · subst hx; simp
    · simp [hx]
  · rw [rotateToBack_of_not_mem rq tid hc]

theorem priorityOf_none_of_not_mem (rq : RunQueue) (tid : ThreadId) (h : tid ∉ rq) :
    rq.priorityOf tid = none := by
  simp [priorityOf, show rq.contains tid = false from by simpa using h]

theorem priorityOf_isSome_iff (rq : RunQueue) (tid : ThreadId) :
    (rq.priorityOf tid).isSome = true ↔ tid ∈ rq := by
  unfold priorityOf; split <;> simp_all

@[simp] theorem priorityOf_empty (tid : ThreadId) : (empty : RunQueue).priorityOf tid = none :=
  priorityOf_none_of_not_mem _ _ (not_mem_empty tid)

theorem maxPrioCode_attained (lk : ThreadId → RunQueueLink) :
    ∀ (l : List ThreadId), l ≠ [] → ∃ z ∈ l, maxPrioCode lk l = (lk z).prio.val + 1
  | [], h => absurd rfl h
  | y :: r, _ => by
    rw [maxPrioCode_cons]
    by_cases hr : r = []
    · subst hr; exact ⟨y, by simp, by simp [maxPrioCode]⟩
    · obtain ⟨z, hz, e⟩ := maxPrioCode_attained lk r hr
      by_cases hle : (lk y).prio.val + 1 ≥ maxPrioCode lk r
      · exact ⟨y, List.mem_cons_self .., by omega⟩
      · exact ⟨z, List.mem_cons_of_mem _ hz, by omega⟩

theorem maxPrioCode_eq_zero_iff (lk : ThreadId → RunQueueLink) (l : List ThreadId) :
    maxPrioCode lk l = 0 ↔ l = [] := by
  cases l with
  | nil => simp [maxPrioCode]
  | cons y r => simp only [maxPrioCode_cons, reduceCtorEq, iff_false]; omega

theorem atPriority_eq_filter (rq : RunQueue) (prio : Priority) :
    rq.atPriority prio = rq.toList.filter (fun t => rq.priorityOf t == some prio) := by
  rw [atPriority_eq]
  refine List.filter_congr (fun t ht => ?_)
  have hc : rq.contains t = true := (rq.mem_toList_iff_mem t).mp ht
  simp [priorityOf, hc]

theorem mem_atPriority (rq : RunQueue) (prio : Priority) (t : ThreadId) :
    t ∈ rq.atPriority prio ↔ t ∈ rq ∧ rq.priorityOf t = some prio := by
  rw [atPriority_eq_filter, List.mem_filter, mem_toList_iff_mem]; simp

theorem maxPriority_eq_none_iff (rq : RunQueue) : rq.maxPriority = none ↔ rq.toList = [] := by
  have hM : rq.maxCode = maxPrioCode (linkOf rq.links) rq.toList := rq.layout.maxCode
  have hz := maxPrioCode_eq_zero_iff (linkOf rq.links) rq.toList
  unfold maxPriority
  split
  · next h => simp only [true_iff]; exact hz.mp (hM ▸ h)
  · next h => simp only [reduceCtorEq, false_iff]; intro e; exact h (hM ▸ hz.mpr e)

/-- The highest priority is a queued thread's priority, and no queued thread's
priority exceeds it. -/
theorem maxPriority_spec (rq : RunQueue) (prio : Priority) (h : rq.maxPriority = some prio) :
    (∃ t, t ∈ rq ∧ rq.priorityOf t = some prio) ∧
      ∀ t q, rq.priorityOf t = some q → q.val ≤ prio.val := by
  unfold maxPriority at h
  split at h
  · cases h
  · next hne =>
    cases h
    have hM : rq.maxCode = maxPrioCode (linkOf rq.links) rq.toList := rq.layout.maxCode
    have hl : rq.toList ≠ [] := fun e => hne (by rw [hM, e]; rfl)
    obtain ⟨z, hz, e⟩ := maxPrioCode_attained (linkOf rq.links) _ hl
    have hcz : rq.contains z = true := (rq.mem_toList_iff_mem z).mp hz
    refine ⟨⟨z, hcz, ?_⟩, fun t q ht => ?_⟩
    · simp only [priorityOf, hcz, ↓reduceIte, Option.some.injEq]
      cases hp : (linkOf rq.links z).prio; simp only [Priority.mk.injEq]
      rw [hp] at e; simp at e; omega
    · unfold priorityOf at ht
      split at ht
      · next hct =>
        cases ht
        have := le_maxPrioCode (lk := linkOf rq.links) ((rq.mem_toList_iff_mem t).mpr hct)
        simp only; omega
      · cases ht

theorem toList_filter_insert_neg' (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.insert tid prio).toList.filter p = rq.toList.filter p := by
  rw [toList_insert]; split
  · rfl
  · rw [List.filter_append]; simp [hp]

theorem toList_filter_insert_neg (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (p : ThreadId → Bool) (hp : p tid = false) (_hNotMem : ¬(tid ∈ rq)) :
    (rq.insert tid prio).toList.filter p = rq.toList.filter p :=
  toList_filter_insert_neg' rq tid prio p hp

theorem toList_filter_remove_neg (rq : RunQueue) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.remove tid).toList.filter p = rq.toList.filter p := by
  rw [toList_remove, List.filter_filter]
  refine List.filter_congr (fun x _ => ?_)
  by_cases hx : x = tid
  · subst hx; simp [hp]
  · simp [hx]

/-- A re-key leaves the queue's order on every thread the filter drops `tid`
from unchanged. -/
theorem toList_filter_rekey_neg (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.rekey tid prio).toList.filter p = rq.toList.filter p := by
  unfold rekey; split
  · rw [toList_filter_insert_neg' _ tid _ _ hp, toList_filter_remove_neg _ tid _ hp]
  · rfl

theorem toList_filter_rotateToBack_neg (rq : RunQueue) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.rotateToBack tid).toList.filter p = rq.toList.filter p := by
  rw [toList_rotateToBack]; split
  · rw [List.filter_append, List.filter_filter]
    simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
      List.append_nil]
    refine List.filter_congr (fun x _ => ?_)
    by_cases hx : x = tid
    · subst hx; simp [hp]
    · simp [hx]
  · rfl

theorem not_mem_remove_toList (rq : RunQueue) (tid : ThreadId) :
    tid ∉ (rq.remove tid).toList := by
  rw [toList_remove]; simp

theorem remove_preserves_toList_nodup (rq : RunQueue) (tid : ThreadId)
    (_ : rq.toList.Nodup) : (rq.remove tid).toList.Nodup := (rq.remove tid).toList_nodup

theorem insert_preserves_toList_nodup (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (_ : rq.toList.Nodup) : (rq.insert tid prio).toList.Nodup := (rq.insert tid prio).toList_nodup

theorem toList_rotateToBack_nodup (rq : RunQueue) (tid : ThreadId)
    (_ : rq.toList.Nodup) (_ : tid ∈ rq) : (rq.rotateToBack tid).toList.Nodup :=
  (rq.rotateToBack tid).toList_nodup

theorem remove_toList_of_not_mem (rq : RunQueue) (tid : ThreadId) (h : tid ∉ rq) :
    (rq.remove tid).toList = rq.toList := by rw [remove_of_not_mem rq tid h]

theorem rotateToBack_mem_iff (rq : RunQueue) (tid t : ThreadId) :
    t ∈ rq.rotateToBack tid ↔ t ∈ rq := mem_rotateToBack rq tid t

/-- WS-H6: a thread in the max-priority bucket is a member of the run queue. -/
theorem maxPriorityBucket_subset (rq : RunQueue) (t : ThreadId)
    (ht : t ∈ rq.maxPriorityBucket) : t ∈ rq := by
  unfold maxPriorityBucket at ht
  split at ht
  · simp at ht
  · exact ((mem_atPriority _ _ _).mp ht).1

theorem maxPriorityBucket_priorityOf (rq : RunQueue) (t : ThreadId)
    (ht : t ∈ rq.maxPriorityBucket) :
    ∃ prio, rq.maxPriority = some prio ∧ rq.priorityOf t = some prio := by
  unfold maxPriorityBucket at ht
  split at ht
  · simp at ht
  · next prio hp => exact ⟨prio, hp, ((mem_atPriority _ _ _).mp ht).2⟩

theorem mem_maxPriorityBucket_of_priorityOf (rq : RunQueue) (t : ThreadId) (prio : Priority)
    (hMem : t ∈ rq) (hTP : rq.priorityOf t = some prio) (hMP : rq.maxPriority = some prio) :
    t ∈ rq.maxPriorityBucket := by
  unfold maxPriorityBucket; rw [hMP]
  exact (mem_atPriority _ _ _).mpr ⟨hMem, hTP⟩

/-- Every bucket member is queued at that bucket's priority, and every queued
thread is in the bucket of its priority.  The structure carries it (`layout`),
so it holds of every run queue (`wellFormed_holds`). -/
def wellFormed (rq : RunQueue) : Prop :=
  (∀ prio tid, tid ∈ rq.atPriority prio → rq.contains tid = true ∧ rq.priorityOf tid = some prio) ∧
  (∀ tid, rq.contains tid = true → ∃ prio, rq.priorityOf tid = some prio ∧ tid ∈ rq.atPriority prio)

theorem wellFormed_holds (rq : RunQueue) : rq.wellFormed := by
  refine ⟨fun prio tid h => (mem_atPriority _ _ _).mp h, fun tid hc => ?_⟩
  refine ⟨(linkOf rq.links tid).prio, by simp [priorityOf, hc], (mem_atPriority _ _ _).mpr
    ⟨hc, by simp [priorityOf, hc]⟩⟩

/-- V7-J: a run queue holding `entries`, built with `insert`. -/
def ofList (entries : List (ThreadId × Priority)) : RunQueue :=
  entries.foldl (fun rq (tid, prio) => rq.insert tid prio) empty

theorem empty_wellFormed : (empty : RunQueue).wellFormed := wellFormed_holds _

theorem insert_preserves_wellFormed (rq : RunQueue) (_ : rq.wellFormed)
    (tid : ThreadId) (prio : Priority) : (rq.insert tid prio).wellFormed := wellFormed_holds _

theorem remove_preserves_wellFormed (rq : RunQueue) (_ : rq.wellFormed) (tid : ThreadId) :
    (rq.remove tid).wellFormed := wellFormed_holds _

theorem rotateToBack_preserves_wellFormed (rq : RunQueue) (_ : rq.wellFormed) (tid : ThreadId) :
    (rq.rotateToBack tid).wellFormed := wellFormed_holds _

theorem ofList_wellFormed (entries : List (ThreadId × Priority)) : (ofList entries).wellFormed :=
  wellFormed_holds _

-- ============================================================================
-- Tables for the frozen snapshot (built once, at freeze)
-- ============================================================================

/-- The threads of queue order `l` with their priorities `prio` as a table.
The frozen snapshot builds it from the threads' run-queue links
(`freezeScheduler`); `threadPriorityTable` is the same table read off the
abstract queue. -/
def threadPriorityTableOf (l : List ThreadId) (prio : ThreadId → Priority) :
    RHTable ThreadId Priority :=
  l.foldl (fun t tid => t.insert tid (prio tid)) (RHTable.empty 16 (by omega))

/-- The threads of queue order `l` as a table. -/
def membershipTableOf (l : List ThreadId) : RHTable ThreadId Unit :=
  l.foldl (fun t tid => t.insert tid ()) (RHTable.empty 16 (by omega))

/-- Each priority's bucket of queue order `l` as a table. -/
def byPriorityTableOf (l : List ThreadId) (prio : ThreadId → Priority) :
    RHTable Priority (List ThreadId) :=
  l.foldl (fun t tid =>
    let p := prio tid
    t.insert p ((t.get? p).getD [] ++ [tid])) (RHTable.empty 16 (by omega))

/-- A fold reads its step only at the list's members. -/
theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ b, f b a = g b a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: r, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a (List.mem_cons_self ..) b]
    exact foldl_congr_mem f g r _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem threadPriorityTableOf_congr {l : List ThreadId} {prio prio' : ThreadId → Priority}
    (h : ∀ t ∈ l, prio t = prio' t) :
    threadPriorityTableOf l prio = threadPriorityTableOf l prio' :=
  foldl_congr_mem _ _ l _ (fun t ht _ => by rw [h t ht])

theorem byPriorityTableOf_congr {l : List ThreadId} {prio prio' : ThreadId → Priority}
    (h : ∀ t ∈ l, prio t = prio' t) :
    byPriorityTableOf l prio = byPriorityTableOf l prio' :=
  foldl_congr_mem _ _ l _ (fun t ht _ => by simp only [h t ht])

/-- The queued threads' priorities as a table, for the frozen snapshot. -/
def threadPriorityTable (rq : RunQueue) : RHTable ThreadId Priority :=
  threadPriorityTableOf rq.toList (fun tid => (linkOf rq.links tid).prio)

/-- The queued threads as a table, for the frozen snapshot. -/
def membershipTable (rq : RunQueue) : RHTable ThreadId Unit :=
  membershipTableOf rq.toList

/-- Each priority's bucket as a table, for the frozen snapshot. -/
def byPriorityTable (rq : RunQueue) : RHTable Priority (List ThreadId) :=
  byPriorityTableOf rq.toList (fun tid => (linkOf rq.links tid).prio)

theorem foldl_insert_invExtK {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (f : RHTable α β → ThreadId → α × β) :
    ∀ (l : List ThreadId) (acc : RHTable α β), acc.invExtK →
      (l.foldl (fun t tid => t.insert (f t tid).1 (f t tid).2) acc).invExtK
  | [], _, h => h
  | _ :: r, _, h => foldl_insert_invExtK f r _ (RHTable_insert_preserves_invExtK _ _ _ h)

theorem threadPriorityTable_invExtK (rq : RunQueue) : rq.threadPriorityTable.invExtK :=
  show (threadPriorityTableOf _ _).invExtK from foldl_insert_invExtK (fun _ tid => (tid, (linkOf rq.links tid).prio)) _ _
    (RHTable.empty_invExtK 16 (by omega))

theorem membershipTable_invExtK (rq : RunQueue) : rq.membershipTable.invExtK :=
  foldl_insert_invExtK (fun _ tid => (tid, ())) _ _ (RHTable.empty_invExtK 16 (by omega))

theorem byPriorityTable_invExtK (rq : RunQueue) : rq.byPriorityTable.invExtK :=
  foldl_insert_invExtK (fun t tid => ((linkOf rq.links tid).prio,
    (t.get? (linkOf rq.links tid).prio).getD [] ++ [tid])) _ _ (RHTable.empty_invExtK 16 (by omega))

theorem foldl_insert_get_key {β : Type} (g : ThreadId → β) (x : ThreadId) :
    ∀ (l : List ThreadId) (acc : RHTable ThreadId β), acc.invExtK →
      (l.foldl (fun t tid => t.insert tid (g tid)) acc).get? x =
        if x ∈ l then some (g x) else acc.get? x
  | [], _, _ => by simp
  | y :: r, acc, h => by
    rw [List.foldl_cons, foldl_insert_get_key g x r _ (RHTable_insert_preserves_invExtK _ _ _ h),
      RHTable_getElem?_insert _ _ _ h.1]
    by_cases hx : x ∈ r
    · simp [hx]
    · by_cases e : y = x
      · subst e; simp [hx]
      · simp [hx, e, Ne.symm e]

theorem threadPriorityTable_get? (rq : RunQueue) (tid : ThreadId) :
    rq.threadPriorityTable.get? tid = rq.priorityOf tid := by
  unfold threadPriorityTable threadPriorityTableOf
  rw [foldl_insert_get_key (fun tid => (linkOf rq.links tid).prio) tid _ _
    (RHTable.empty_invExtK 16 (by omega)), RHTable_get?_empty]
  unfold priorityOf
  by_cases h : rq.contains tid
  · simp [h, (rq.mem_toList_iff_mem tid).mpr h]
  · simp [h, show tid ∉ rq.toList from fun h' => h ((rq.mem_toList_iff_mem tid).mp h')]

theorem membershipTable_get? (rq : RunQueue) (tid : ThreadId) :
    rq.membershipTable.get? tid = if rq.contains tid then some () else none := by
  unfold membershipTable membershipTableOf
  rw [foldl_insert_get_key (fun _ => ()) tid _ _ (RHTable.empty_invExtK 16 (by omega)),
    RHTable_get?_empty]
  by_cases h : rq.contains tid
  · simp [h, (rq.mem_toList_iff_mem tid).mpr h]
  · simp [h, show tid ∉ rq.toList from fun h' => h ((rq.mem_toList_iff_mem tid).mp h')]

theorem byPriorityTable_get? (rq : RunQueue) (p : Priority) :
    rq.byPriorityTable.get? p = if rq.atPriority p = [] then none else some (rq.atPriority p) := by
  have key : ∀ (l : List ThreadId) (acc : RHTable Priority (List ThreadId)), acc.invExtK →
      (l.foldl (fun t tid =>
        let q := (linkOf rq.links tid).prio
        t.insert q ((t.get? q).getD [] ++ [tid])) acc).get? p =
      if l.filter (fun t => (linkOf rq.links t).prio == p) = [] then acc.get? p
      else some ((acc.get? p).getD [] ++ l.filter (fun t => (linkOf rq.links t).prio == p)) := by
    intro l
    induction l with
    | nil => intro acc _; simp
    | cons y r ih =>
      intro acc h
      rw [List.foldl_cons, ih _ (RHTable_insert_preserves_invExtK _ _ _ h)]
      rw [RHTable_getElem?_insert _ _ _ h.1]
      by_cases e : (linkOf rq.links y).prio = p
      · subst e; simp
      · have e' : ((linkOf rq.links y).prio == p) = false := by simp [e]
        simp only [e', List.filter_cons, Bool.false_eq_true, ↓reduceIte]
  unfold byPriorityTable byPriorityTableOf
  rw [key _ _ (RHTable.empty_invExtK 16 (by omega)), RHTable_get?_empty, atPriority_eq]
  split <;> simp

-- ============================================================================
-- What a core keeps once the links live in the threads
-- ============================================================================

/-- WS-ZA ZA4.5: the entry the queue holds for `t`, read as the threads hold
it: a queued thread's entry, and the empty entry for any other.  A thread
that leaves keeps its old entry in `links` (`queued := false`); its TCB keeps
its old links too, but answers no core's queue, so this is what the two have
in common. -/
def queuedLink (rq : RunQueue) (t : ThreadId) : RunQueueLink :=
  if (linkOf rq.links t).queued then linkOf rq.links t else RunQueueLink.none

theorem queuedLink_queued (rq : RunQueue) (t : ThreadId) :
    (rq.queuedLink t).queued = rq.contains t := by
  unfold queuedLink contains
  split
  · rfl
  · next h => simp only [Bool.not_eq_true] at h; rw [h]; rfl

theorem queuedLink_of_contains {rq : RunQueue} {t : ThreadId} (h : rq.contains t = true) :
    rq.queuedLink t = linkOf rq.links t := by
  unfold queuedLink; exact if_pos h

theorem queuedLink_of_not_contains {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false) :
    rq.queuedLink t = RunQueueLink.none := by
  unfold queuedLink; rw [if_neg]; exact fun e => by unfold contains at h; rw [e] at h; cases h

/-- A thread not on the queue is neither its last thread nor any bucket's. -/
theorem code_ne_tail {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false) :
    code t ≠ rq.tail :=
  code_ne_end rq.layout_toList.queue.2.1
    (fun hm => by rw [(rq.mem_toList_iff_mem t).mp hm] at h; cases h)

theorem code_ne_bucket_tail {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false)
    (p : Priority) : code t ≠ (endsOf rq.buckets p).tail :=
  code_ne_end (rq.layout_toList.bucket p).2.1
    (fun hm => by rw [(rq.mem_toList_iff_mem t).mp (List.mem_filter.mp hm).1] at h; cases h)

/-- The thread a queue's nonzero tail code names is on the queue. -/
theorem contains_of_code_eq_tail {rq : RunQueue} {x : ThreadId} (h : code x = rq.tail) :
    rq.contains x = true := by
  have he := rq.layout_toList.queue.2.1
  have hm := decode_lastCode_mem (l := rq.toList) (by rw [← he, ← h]; exact code_ne_zero x)
  rw [← he, ← h, decode_code] at hm
  exact (rq.mem_toList_iff_mem x).mp hm

theorem contains_of_code_eq_bucket_tail {rq : RunQueue} {x : ThreadId} {p : Priority}
    (h : code x = (endsOf rq.buckets p).tail) : rq.contains x = true := by
  have he := (rq.layout_toList.bucket p).2.1
  have hm := decode_lastCode_mem (by rw [← he, ← h]; exact code_ne_zero x)
  rw [← he, ← h, decode_code] at hm
  exact (rq.mem_toList_iff_mem x).mp (List.mem_filter.mp hm).1

/-- The thread a queue's nonzero head code names is on the queue (WS-ZA ZA6.9). -/
theorem contains_of_code_eq_head {rq : RunQueue} {x : ThreadId} (h : code x = rq.head) :
    rq.contains x = true := by
  have he := rq.layout_toList.queue.1
  have hm := decode_lastCode_mem (l := rq.toList.reverse) (by rw [← he, ← h]; exact code_ne_zero x)
  rw [← he, ← h, decode_code] at hm
  exact (rq.mem_toList_iff_mem x).mp (List.mem_reverse.mp hm)

theorem contains_of_code_eq_bucket_head {rq : RunQueue} {x : ThreadId} {p : Priority}
    (h : code x = (endsOf rq.buckets p).head) : rq.contains x = true := by
  have he := (rq.layout_toList.bucket p).1
  have hm := decode_lastCode_mem (by rw [← he, ← h]; exact code_ne_zero x)
  rw [← he, ← h, decode_code] at hm
  exact (rq.mem_toList_iff_mem x).mp (List.mem_filter.mp (List.mem_reverse.mp hm)).1

/-- A thread not on the queue is neither its first thread nor any bucket's. -/
theorem code_ne_queue_head {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false) :
    code t ≠ rq.head :=
  code_ne_head rq.layout_toList.queue.1
    (fun hm => by rw [(rq.mem_toList_iff_mem t).mp hm] at h; cases h)

theorem code_ne_bucket_head {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false)
    (p : Priority) : code t ≠ (endsOf rq.buckets p).head :=
  code_ne_head (rq.layout_toList.bucket p).1
    (fun hm => by rw [(rq.mem_toList_iff_mem t).mp (List.mem_filter.mp hm).1] at h; cases h)

/-- A read of a queue's entries that agrees with the queue on every queued
thread walks the queue's list and finds its highest priority. -/
theorem walk_of_agree (rq : RunQueue) {lk : ThreadId → RunQueueLink}
    (h : ∀ x, lk x = rq.queuedLink x) :
    walk (fun t => (lk t).next) rq.size rq.head = rq.toList := by
  have hL := rq.layout_toList
  have hmem : ∀ x ∈ rq.toList, lk x = linkOf rq.links x := fun x hx => by
    rw [h x]; exact queuedLink_of_contains ((rq.mem_toList_iff_mem x).mp hx)
  have hq := (isQueue_congr (nx' := fun t => (lk t).next) (pv' := fun t => (lk t).prev)
    (fun x hx => by dsimp only; rw [hmem x hx]) (fun x hx => by dsimp only; rw [hmem x hx])).mpr
    hL.queue
  exact hq.walk_eq (Nat.le_of_eq hL.length)

theorem maxPrioCode_of_agree (rq : RunQueue) {lk : ThreadId → RunQueueLink}
    (h : ∀ x, lk x = rq.queuedLink x) :
    maxPrioCode lk rq.toList = rq.maxCode := by
  rw [rq.layout_toList.maxCode]
  refine maxPrioCode_congr (fun x hx => ?_)
  rw [h x, queuedLink_of_contains ((rq.mem_toList_iff_mem x).mp hx)]

/-- A queued thread's links name neither itself nor any thread off the queue. -/
theorem own_links (rq : RunQueue) {t : ThreadId} (hc : rq.contains t = true) :
    let x := linkOf rq.links t
    (code t ≠ x.prev ∧ code t ≠ x.next ∧ code t ≠ x.bucketPrev ∧ code t ≠ x.bucketNext) ∧
    ∀ y : ThreadId, (code y = x.prev ∨ code y = x.next ∨ code y = x.bucketPrev ∨
      code y = x.bucketNext) → rq.contains y = true := by
  intro x
  obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
  have hL := rq.layout_toList
  rw [hAB] at hL
  have hnd := hL.nodup
  obtain ⟨_, hndtB, hAtB⟩ := List.nodup_append.mp hnd
  obtain ⟨htB, _⟩ := List.nodup_cons.mp hndtB
  have htA : t ∉ A := fun h => hAtB t h t (List.mem_cons_self ..) rfl
  let fp := fun z => (linkOf rq.links z).prio == x.prio
  have hfp : fp t = true := by simp [fp, x]
  have hBq := hL.bucket x.prio
  rw [filter_mid hfp] at hBq
  obtain ⟨hpv, hnx⟩ := IsQueue.mid hL.queue
  obtain ⟨hbpv, hbnx⟩ := IsQueue.mid hBq
  have hmemCode : ∀ (L : List ThreadId) (z : ThreadId), code z = lastCode 0 L → z ∈ L := by
    intro L z hc
    have hm := decode_lastCode_mem (l := L) (by rw [← hc]; exact code_ne_zero z)
    rwa [← hc, decode_code] at hm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun y hy => ?_⟩
  · rw [show x.prev = _ from hpv]; exact code_ne_end rfl htA
  · rw [show x.next = _ from hnx]; exact code_ne_end rfl (by simpa using htB)
  · rw [show x.bucketPrev = _ from hbpv]
    exact code_ne_end rfl (fun h => htA (List.mem_filter.mp h).1)
  · rw [show x.bucketNext = _ from hbnx]
    exact code_ne_end rfl (fun h => htB (List.mem_filter.mp (List.mem_reverse.mp h)).1)
  · apply (rq.mem_toList_iff_mem y).mp
    rw [hAB]
    rcases hy with hy | hy | hy | hy
    · exact List.mem_append_left _ (hmemCode _ y (hy.trans hpv))
    · exact List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_reverse.mp (hmemCode _ y (hy.trans hnx))))
    · exact List.mem_append_left _ (List.mem_filter.mp (hmemCode _ y (hy.trans hbpv))).1
    · exact List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_filter.mp (List.mem_reverse.mp (hmemCode _ y (hy.trans hbnx)))).1)

/-- The fields of a queue once its member `t` is dequeued, read off `t`'s entry. -/
theorem remove_fields (rq : RunQueue) {t : ThreadId} (hc : rq.contains t = true) :
    let x := linkOf rq.links t
    let head' := if x.prev = 0 then x.next else rq.head
    (rq.remove t).links = unlinkLinks rq.links t x.prev x.next x.bucketPrev x.bucketNext ∧
    (rq.remove t).buckets = setEnds rq.buckets x.prio (unlinkEnds x.bucketPrev x.bucketNext) ∧
    (rq.remove t).head = head' ∧
    (rq.remove t).tail = (if x.next = 0 then x.prev else rq.tail) ∧
    (rq.remove t).size = rq.size - 1 ∧
    (rq.remove t).maxCode =
      (if x.bucketPrev = 0 ∧ x.bucketNext = 0 ∧ rq.maxCode = x.prio.val + 1 then
        maxPrioCodeWalk (unlinkLinks rq.links t x.prev x.next x.bucketPrev x.bucketNext)
          (rq.size - 1) head' 0
      else rq.maxCode) := by
  unfold remove; rw [dif_pos hc]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two queues with the same tables and words are the same queue. -/
theorem ext_fields {a b : RunQueue} (h1 : a.links = b.links) (h2 : a.buckets = b.buckets)
    (h3 : a.head = b.head) (h4 : a.tail = b.tail) (h5 : a.size = b.size)
    (h6 : a.maxCode = b.maxCode) : a = b := by
  cases a; cases b; simp only at h1 h2 h3 h4 h5 h6; subst h1 h2 h3 h4 h5 h6; rfl

/-- Moving a queued thread to the back is dequeueing it and enqueueing it again
at the priority it was queued at. -/
theorem rotateToBack_eq_remove_insert (rq : RunQueue) {t : ThreadId} (hc : rq.contains t = true) :
    rq.rotateToBack t = (rq.remove t).insert t (linkOf rq.links t).prio := by
  obtain ⟨hLk, hBk, hHd, hTl, hSz, hMx⟩ := rq.remove_fields hc
  have hnc : (rq.remove t).contains t = false := by
    have := contains_remove rq t t; simp at this; exact this
  obtain ⟨A, B, hAB⟩ := rq.split_of_contains hc
  have hL := rq.layout_toList
  rw [hAB] at hL
  have hlen := hL.length
  have hrl : (rq.remove t).toList = A ++ B := by
    rw [toList_remove, hAB, filter_ne_mid (hAB ▸ rq.toList_nodup)]
  have hmaxR : (rq.remove t).maxCode = maxPrioCode (linkOf rq.links) (A ++ B) := by
    rw [(rq.remove t).layout_toList.maxCode, hrl, hLk]
    exact maxPrioCode_congr (fun x _ => prio_unlinkLinks rq.links_invExtK t _ _ _ _ x)
  have hmax : rq.maxCode = max (rq.remove t).maxCode ((linkOf rq.links t).prio.val + 1) := by
    rw [hL.maxCode, maxPrioCode_mid, hmaxR]
  unfold rotateToBack insert
  rw [dif_pos hc, dif_neg (by rw [hnc]; decide)]
  apply ext_fields
  · simp only [hLk, hTl, hBk]
  · simp only [hBk]
  · simp only [hHd, hTl]
  · rfl
  · simp only [hSz]; simp at hlen; omega
  · exact hmax

theorem links_insert_of_not_contains {rq : RunQueue} {t : ThreadId} (h : rq.contains t = false)
    (p : Priority) :
    (rq.insert t p).links = appendLinks rq.links t p rq.tail (endsOf rq.buckets p).tail := by
  unfold insert; rw [dif_neg (by rw [h]; decide)]

end RunQueue

/-- WS-ZA ZA4.5: a core's run queue as the core holds it once each thread's
links live in its TCB (as seL4's `tcbSchedNext`/`tcbSchedPrev`): the ends of
the queue of runnable threads, the ends of each priority's bucket, the count
and the highest queued priority.  `RunQueue.ends` reads them off a queue. -/
structure RunQueueEnds where
  buckets : RHTable Priority BucketEnds
  head : Nat
  tail : Nat
  size : Nat
  maxCode : Nat

namespace RunQueue

/-- The ends a run queue keeps: every field but the links and the proofs. -/
def ends (rq : RunQueue) : RunQueueEnds := ⟨rq.buckets, rq.head, rq.tail, rq.size, rq.maxCode⟩

end RunQueue

namespace RunQueueEnds

/-- The ends of an empty queue, as one constant built once at initialisation
(`RunQueue.empty` is inlined, so a slot filled with it would build a fresh
record on every call). -/
@[noinline] def empty : RunQueueEnds := RunQueue.empty.ends

instance : Inhabited RunQueueEnds where default := empty

instance : Repr RunQueueEnds where
  reprPrec e _ := repr (e.head, e.tail, e.size, e.maxCode)

end RunQueueEnds
end SeLe4n.Kernel
