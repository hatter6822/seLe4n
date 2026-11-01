/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.Scheduler.RunQueueThreadLinks

/-!
# Run-queue stages of a step that may link threads

WS-ZA ZA6.10.  The run-queue stage families (`RunQueueStage`,
`RunQueueWindowStage`, `RunQueueDispatchStage`, `RunQueueEntryStage`) carry the
`live` frame with no slot linked: every step but seL4's yieldTo invocation
links no thread.  The invocation links its caller, so its stages carry the
frame over the slots `L` it may link (`RunQueueLinkStageOn L`).  This file
states the four families over `L`, how a stage that links nothing joins them
(`.on`), and how they compose.
-/

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A link stage over `L` that links nothing off `L'` ⊇ `L`. -/
theorem RunQueueLinkStageOn.mono {L L' : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (hL : ∀ k, L k → L' k) (h : RunQueueLinkStageOn L st st') : RunQueueLinkStageOn L' st st' :=
  ⟨h.links, h.tables, h.release, h.refills, h.yield, fun hI hR => (h.live hI hR).mono hL⟩

/-- A link stage that links nothing is one over any `L`. -/
theorem RunQueueLinkStage.on {st st' : SystemState} (L : SeLe4n.ObjId → Prop)
    (h : RunQueueLinkStage st st') : RunQueueLinkStageOn L st st' :=
  h.mono fun _ e => e.elim

theorem RunQueueLinkStageOn.trans {L : SeLe4n.ObjId → Prop} {st st' st'' : SystemState}
    (h1 : RunQueueLinkStageOn L st st') (h2 : RunQueueLinkStageOn L st' st'') :
    RunQueueLinkStageOn L st st'' :=
  ⟨fun h r => (h1.links h r).elim h2.links,
    fun h r t => let ⟨h', r'⟩ := h1.links h r; h2.tables h' r' (h1.tables h r t),
    fun h r q => let ⟨h', r'⟩ := h1.links h r; h2.release h' r' (h1.release h r q),
    fun S h r q s => let ⟨h', r'⟩ := h1.links h r
      h2.refills S h' r' (h1.release h r q) (h1.refills S h r q s),
    fun h r y => let ⟨h', r'⟩ := h1.links h r; h2.yield h' r' (h1.yield h r y),
    fun h r => let ⟨h', r'⟩ := h1.links h r; (h2.live h' r').trans (h1.live h r)⟩

/-- **A stage over `L`**: `RunQueueStage` with the link half over `L`. -/
def RunQueueStageOn (L : SeLe4n.ObjId → Prop) (st st' : SystemState) : Prop :=
  RunQueueLinkStageOn L st st' ∧
  (∀ e, st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e) ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- **A step inside a scheduling point, over `L`.** -/
def RunQueueWindowStageOn (L : SeLe4n.ObjId → Prop) (p : SchedPoint) (st st' : SystemState) :
    Prop :=
  RunQueueLinkStageOn L st st' ∧
  (st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept (some p) → st'.currentDequeuedUniqueExcept (some p))

/-- **A dispatch on core `c`, over `L`.** -/
def RunQueueDispatchStageOn (L : SeLe4n.ObjId → Prop) (c : CoreId) (st st' : SystemState) :
    Prop :=
  RunQueueLinkStageOn L st st' ∧
  (∀ e e', (∀ p, e = some p → p.core ≠ c → e' = some p) →
    st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUniqueExcept e → st'.currentDequeuedUniqueExcept e') ∧
  (st.objects.invExt → st.runQueueRefined → StateMono st st')

/-- **A whole kernel entry, over `L`.** -/
def RunQueueEntryStageOn (L : SeLe4n.ObjId → Prop) (st st' : SystemState) : Prop :=
  RunQueueLinkStageOn L st st' ∧
  (st.objects.invExt → st.runQueueRefined → st'.runQueueRefined →
    st.currentDequeuedUnique → st'.currentDequeuedUnique)

/-! ### Stages that link nothing join the families over `L` -/

theorem RunQueueStage.on {st st' : SystemState} (L : SeLe4n.ObjId → Prop)
    (h : RunQueueStage st st') : RunQueueStageOn L st st' := ⟨h.1.on L, h.2⟩

theorem RunQueueWindowStage.on {p : SchedPoint} {st st' : SystemState} (L : SeLe4n.ObjId → Prop)
    (h : RunQueueWindowStage p st st') : RunQueueWindowStageOn L p st st' := ⟨h.1.on L, h.2⟩

theorem RunQueueDispatchStage.on {c : CoreId} {st st' : SystemState} (L : SeLe4n.ObjId → Prop)
    (h : RunQueueDispatchStage c st st') : RunQueueDispatchStageOn L c st st' := ⟨h.1.on L, h.2⟩

theorem RunQueueEntryStage.on {st st' : SystemState} (L : SeLe4n.ObjId → Prop)
    (h : RunQueueEntryStage st st') : RunQueueEntryStageOn L st st' := ⟨h.1.on L, h.2⟩

/-! ### Composition over `L` -/

theorem RunQueueStageOn.trans {L : SeLe4n.ObjId → Prop} {st st' st'' : SystemState}
    (h1 : RunQueueStageOn L st st') (h2 : RunQueueStageOn L st' st'') :
    RunQueueStageOn L st st'' :=
  ⟨h1.1.trans h2.1, fun e h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    h2.2.1 e h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1.links h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

theorem RunQueueStageOn.window {L : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (h : RunQueueStageOn L st st') (p : SchedPoint) : RunQueueWindowStageOn L p st st' :=
  ⟨h.1, h.2.1 (some p)⟩

theorem RunQueueStageOn.entry {L : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (h : RunQueueStageOn L st st') : RunQueueEntryStageOn L st st' :=
  ⟨h.1, h.2.1 none⟩

theorem RunQueueWindowStageOn.trans {L : SeLe4n.ObjId → Prop} {p : SchedPoint}
    {st st' st'' : SystemState} (h1 : RunQueueWindowStageOn L p st st')
    (h2 : RunQueueWindowStageOn L p st' st'') : RunQueueWindowStageOn L p st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    h2.2 h' r' r'' (h1.2 h r r' d)⟩

/-- **A scheduling point over `L`**: steps inside core `p.core`'s point, then
the dispatch that closes it. -/
theorem RunQueueWindowStageOn.dispatch {L : SeLe4n.ObjId → Prop} {p : SchedPoint}
    {st st' st'' : SystemState} (h1 : RunQueueWindowStageOn L p st st')
    (h2 : RunQueueDispatchStageOn L p.core st' st'') : RunQueueEntryStageOn L st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    h2.2.1 (some p) none (fun _ he hne => absurd (by cases he; rfl) hne) h' r' r''
      (h1.2 h r r' (d.except _))⟩

/-- A stage over `L` before a dispatch over `L` is part of it. -/
theorem RunQueueStageOn.dispatch {L : SeLe4n.ObjId → Prop} {c : CoreId}
    {st st' st'' : SystemState} (h1 : RunQueueStageOn L st st')
    (h2 : RunQueueDispatchStageOn L c st' st'') : RunQueueDispatchStageOn L c st st'' :=
  ⟨h1.1.trans h2.1, fun e e' he h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    h2.2.1 e e' he h' r' r'' (h1.2.1 e h r r' d),
    fun h r => let ⟨h', r'⟩ := h1.1.links h r; (h1.2.2 h r).trans (h2.2.2 h' r')⟩

theorem RunQueueEntryStageOn.trans {L : SeLe4n.ObjId → Prop} {st st' st'' : SystemState}
    (h1 : RunQueueEntryStageOn L st st') (h2 : RunQueueEntryStageOn L st' st'') :
    RunQueueEntryStageOn L st st'' :=
  ⟨h1.1.trans h2.1, fun h r r'' d =>
    let ⟨h', r'⟩ := h1.1.links h r
    h2.2 h' r' r'' (h1.2 h r r' d)⟩

theorem RunQueueEntryStageOn.mono {L L' : SeLe4n.ObjId → Prop} {st st' : SystemState}
    (hL : ∀ k, L k → L' k) (h : RunQueueEntryStageOn L st st') : RunQueueEntryStageOn L' st st' :=
  ⟨h.1.mono hL, h.2⟩

end SeLe4n.Model.SystemState
