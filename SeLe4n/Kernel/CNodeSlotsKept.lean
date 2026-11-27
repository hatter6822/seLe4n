-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API

/-!
# A step that keeps every capability a CNode holds

seL4's `SysReplyRecv` replies first and then looks the receive capability up
(`handleRecv`), on the state the reply left.  The reply writes CNodes only by
its capability transfer, which installs into a slot it found empty and may set
an untyped source's free index.  So a slot that held a capability still holds
it, and a resolution that reached a capability still reaches it.

`CNodeSlotsKept st st'` is that frame: every object keeps its kind, and every
CNode keeps its radix and every slot it fills, with a capability naming the
same target; one naming no untyped object is kept whole, one naming an untyped
object up to its free index.  Over it, a walk that stopped at an occupied slot
stops there again (`resolveAddressBits_of_cnodeSlotsKept`), a resolution
resolves to a capability naming the same target
(`syscallResolveCap_target_of_cnodeSlotsKept`), to the same capability when it
names no untyped object (`syscallResolveCap_of_cnodeSlotsKept`), and the type
verdict, which reads the target alone, is kept
(`syscallTargetAccepted_of_cnodeSlotsKept`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A capability naming an untyped object at `st`: the one kind of capability a
capability transfer rewrites in place (`untypedSourceSetFull`). -/
def capNamesUntyped (st : SystemState) (c : Capability) : Prop :=
  ∃ oid, c.target = .object oid ∧ (st.getUntyped? oid).isSome

/-- **Every CNode kept with every capability it holds**: each object keeps its
kind, and each CNode its radix and each slot it fills, with a capability naming
the same target, the very capability when it names no untyped object. -/
structure CNodeSlotsKept (st st' : SystemState) : Prop where
  kind : ∀ id : SeLe4n.ObjId, (st'.objects[id]?).map KernelObject.objectType =
    (st.objects[id]?).map KernelObject.objectType
  cnode : ∀ (id : SeLe4n.ObjId) (cn : CNode), st.getCNode? id = some cn → ∃ cn', st'.getCNode? id = some cn' ∧
    cn'.radixWidth = cn.radixWidth ∧
    ∀ s c, cn.lookup s = some c → ∃ c', cn'.lookup s = some c' ∧ c'.target = c.target ∧
      (¬ capNamesUntyped st c → c' = c)

namespace CNodeSlotsKept

variable {st st' st'' : SystemState}

theorem refl (st : SystemState) : CNodeSlotsKept st st :=
  ⟨fun _ => rfl, fun _ cn h => ⟨cn, h, rfl, fun _ c hL => ⟨c, hL, rfl, fun _ => rfl⟩⟩⟩

theorem of_objects_eq (h : st'.objects = st.objects) : CNodeSlotsKept st st' := by
  refine ⟨fun id => by rw [h], fun id cn hC => ⟨cn, ?_, rfl, fun _ c hL => ⟨c, hL, rfl, fun _ => rfl⟩⟩⟩
  rw [SystemState.getCNode?_eq_some_iff] at hC ⊢
  rw [h]; exact hC

/-- A kept kind keeps whether an id holds a CNode. -/
theorem getCNode?_isSome (h : CNodeSlotsKept st st') (id : SeLe4n.ObjId) :
    (st'.getCNode? id).isSome = (st.getCNode? id).isSome := by
  have hK := h.kind id
  unfold SystemState.getCNode?
  cases h1 : st.objects[id]? with
  | none => rw [h1] at hK; cases h2 : st'.objects[id]? <;> simp_all
  | some o =>
    rw [h1] at hK
    cases h2 : st'.objects[id]? with
    | none => rw [h2] at hK; cases hK
    | some o' =>
      rw [h2] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      cases o <;> cases o' <;> simp_all [KernelObject.objectType]

/-- A kept kind keeps whether an id holds an untyped object. -/
theorem getUntyped?_isSome (h : CNodeSlotsKept st st') (id : SeLe4n.ObjId) :
    (st'.getUntyped? id).isSome = (st.getUntyped? id).isSome := by
  have hK := h.kind id
  unfold SystemState.getUntyped?
  cases h1 : st.objects[id]? with
  | none => rw [h1] at hK; cases h2 : st'.objects[id]? <;> simp_all
  | some o =>
    rw [h1] at hK
    cases h2 : st'.objects[id]? with
    | none => rw [h2] at hK; cases hK
    | some o' =>
      rw [h2] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      cases o <;> cases o' <;> simp_all [KernelObject.objectType]

theorem capNamesUntyped_iff (h : CNodeSlotsKept st st') (c : Capability) :
    capNamesUntyped st' c ↔ capNamesUntyped st c := by
  unfold capNamesUntyped
  constructor
  · rintro ⟨oid, hT, hU⟩; exact ⟨oid, hT, (h.getUntyped?_isSome oid) ▸ hU⟩
  · rintro ⟨oid, hT, hU⟩; exact ⟨oid, hT, (h.getUntyped?_isSome oid).symm ▸ hU⟩

theorem trans (h₁ : CNodeSlotsKept st st') (h₂ : CNodeSlotsKept st' st'') :
    CNodeSlotsKept st st'' := by
  refine ⟨fun id => (h₂.kind id).trans (h₁.kind id), fun id cn hC => ?_⟩
  obtain ⟨cn', hC', hR', hL'⟩ := h₁.cnode id cn hC
  obtain ⟨cn'', hC'', hR'', hL''⟩ := h₂.cnode id cn' hC'
  refine ⟨cn'', hC'', hR''.trans hR', fun s c hL => ?_⟩
  obtain ⟨c', hc', hT', hE'⟩ := hL' s c hL
  obtain ⟨c'', hc'', hT'', hE''⟩ := hL'' s c' hc'
  refine ⟨c'', hc'', hT''.trans hT', fun hU => ?_⟩
  have e' := hE' hU
  subst e'
  exact hE'' fun hU' => hU ((h₁.capNamesUntyped_iff c').mp hU')

/-- **A kind-preserving write keeps every CNode**: it writes no CNode at all. -/
theorem of_kindPreservingWriteAt (h : ∀ oid, kindPreservingWriteAt st st' oid) :
    CNodeSlotsKept st st' := by
  refine ⟨fun id => ?_, fun id cn hC => ⟨cn, ?_, rfl, fun _ c hL => ⟨c, hL, rfl, fun _ => rfl⟩⟩⟩
  · rcases h id with e | ⟨pre, post, hp, hq, ht, -⟩
    · rw [e]
    · rw [hp, hq]; simp only [Option.map_some, ht]
  · rw [SystemState.getCNode?_eq_some_iff] at hC ⊢
    rcases h id with e | ⟨pre, post, hp, hq, ht, hn, -⟩
    · rw [e]; exact hC
    · rw [hC] at hp; cases hp
      exact absurd (ht.trans rfl) hn

/-- A kind-preserving write, its ghosts aside. -/
theorem of_kindPreservingWrite (h : kindPreservingWrite st st') : CNodeSlotsKept st st' :=
  of_kindPreservingWriteAt h.objectsAt

end CNodeSlotsKept

/-- A capability naming a CNode names no untyped object. -/
theorem not_capNamesUntyped_of_isCNodeCap {st : SystemState} {c : Capability}
    (h : isCNodeCap st c = true) : ¬ capNamesUntyped st c := by
  rintro ⟨oid, hT, hU⟩
  unfold isCNodeCap at h
  rw [hT] at h
  simp only at h
  unfold SystemState.getCNode? at h
  unfold SystemState.getUntyped? at hU
  cases ho : st.objects[oid]? with
  | none => rw [ho] at h; cases h
  | some o => rw [ho] at h hU; cases o <;> simp_all

theorem isCNodeCap_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    (c : Capability) : isCNodeCap st' c = isCNodeCap st c := by
  unfold isCNodeCap
  cases c.target <;> simp [h.getCNode?_isSome]

/-- **A walk that stopped at an occupied slot stops there again**: over a step
that keeps every CNode, a resolution whose slot holds a capability passes the
same guards and radices, descends through the same CNode capabilities and stops
at the same slot with the same bits left (the slot it stops at holds a
capability naming the same target, so not a CNode one). -/
theorem resolveAddressBits_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    (cptr : SeLe4n.CPtr) :
    ∀ (nBits : Nat) (nodeCap : Capability) (ref : SlotRef) (rem : Nat) (c : Capability),
      resolveAddressBits nodeCap cptr nBits st = .ok (ref, rem) →
      SystemState.lookupSlotCap st ref = some c →
      resolveAddressBits nodeCap cptr nBits st' = .ok (ref, rem) := by
  intro nBits
  induction nBits using Nat.strongRecOn with
  | _ n ih =>
    intro nodeCap ref rem c hR hLk
    rw [resolveAddressBits] at hR ⊢
    cases hT : nodeCap.target with
    | object id =>
      rw [hT] at hR
      dsimp only at hR ⊢
      cases hC : st.getCNode? id with
      | none => rw [hC] at hR; cases hR
      | some cn =>
        obtain ⟨cn', hC', hRw, hKeep⟩ := h.cnode id cn hC
        rw [hC] at hR
        rw [hC']
        dsimp only at hR ⊢
        simp -iota only [hRw]
        split at hR
        · cases hR
        · next hG =>
          rw [if_neg hG]
          split at hR
          · cases hR
          · next hD =>
            rw [dif_neg hD]
            split at hR
            · next hE => rw [dif_pos hE]; exact hR
            · next hE =>
              rw [dif_neg hE]
              revert hR
              cases hS : cn.lookup (SeLe4n.Slot.ofNat (cptr.slotBits
                  (n - (nodeCap.cnodeGuardSize.toNat + cn.radixWidth)) cn.radixWidth)) with
              | some cap =>
                intro hR
                dsimp only at hR
                obtain ⟨c', hc', hT', hE'⟩ := hKeep _ cap hS
                rw [hc']
                dsimp only
                have hI' : isCNodeCap st' c' = isCNodeCap st cap := by
                  rw [isCNodeCap_of_cnodeSlotsKept h c']
                  unfold isCNodeCap
                  rw [hT']
                rw [hI']
                by_cases hI : isCNodeCap st cap = true
                · rw [if_pos hI] at hR ⊢
                  rw [hE' (not_capNamesUntyped_of_isCNodeCap hI)]
                  exact ih _ (by omega) cap ref rem c hR hLk
                · rw [if_neg hI] at hR ⊢; exact hR
              | none =>
                intro hR
                dsimp only at hR
                cases hR
                unfold SystemState.lookupSlotCap SystemState.lookupCNode at hLk
                rw [(SystemState.getCNode?_eq_some_iff st id cn).mp hC] at hLk
                dsimp only at hLk
                rw [hS] at hLk; cases hLk
    | _ => rw [hT] at hR; cases hR

/-- A slot holding a capability holds one naming the same target again, the
very capability when it names no untyped object. -/
theorem lookupSlotCap_target_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    {ref : SlotRef} {c : Capability} (hC : SystemState.lookupSlotCap st ref = some c) :
    ∃ c', SystemState.lookupSlotCap st' ref = some c' ∧ c'.target = c.target ∧
      (¬ capNamesUntyped st c → c' = c) := by
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at hC ⊢
  cases hO : st.objects[ref.cnode]? with
  | none => rw [hO] at hC; cases hC
  | some o =>
    rw [hO] at hC
    cases o with
    | cnode cn =>
      dsimp only at hC
      obtain ⟨cn', hC', -, hKeep⟩ :=
        h.cnode ref.cnode cn ((SystemState.getCNode?_eq_some_iff st _ cn).mpr hO)
      rw [(SystemState.getCNode?_eq_some_iff st' _ cn').mp hC']
      exact hKeep _ c hC
    | _ => cases hC

/-- The reserved-object refusal reads a capability's target alone. -/
theorem capTargetsReservedKernelObject_congr_target {c c' : Capability}
    (h : c'.target = c.target) :
    capTargetsReservedKernelObject c' = capTargetsReservedKernelObject c := by
  unfold capTargetsReservedKernelObject
  rw [h]

/-- **A resolution resolves again, to a capability naming the same target**,
over a step that keeps every CNode: the walk stops at the same slot
(`resolveAddressBits_of_cnodeSlotsKept`), the slot holds a capability naming
the same target, so not a reserved one, and the very capability when it names
no untyped object. -/
theorem syscallResolveCap_target_of_cnodeSlotsKept {st st' : SystemState}
    (h : CNodeSlotsKept st st') (gate : SyscallGate) {cap : Capability}
    (hR : syscallResolveCap gate st = .ok (cap, st)) :
    ∃ cap', syscallResolveCap gate st' = .ok (cap', st') ∧ cap'.target = cap.target ∧
      (¬ capNamesUntyped st cap → cap' = cap) := by
  unfold syscallResolveCap at hR ⊢
  cases hL : gate.lookupSlot st with
  | error f => rw [hL] at hR; cases hR
  | ok ref =>
    rw [hL] at hR
    dsimp only at hR
    cases hC : SystemState.lookupSlotCap st ref with
    | none => rw [hC] at hR; cases hR
    | some c =>
      rw [hC] at hR
      dsimp only at hR
      by_cases hRes : capTargetsReservedKernelObject c = true
      · rw [if_pos hRes] at hR; cases hR
      · rw [if_neg hRes] at hR
        cases hR
        have hL' : gate.lookupSlot st' = .ok ref := by
          unfold SyscallGate.lookupSlot at hL ⊢
          cases hRoot : gate.cspaceRootCap with
          | none => rw [hRoot] at hL; cases hL
          | some root =>
            rw [hRoot] at hL
            dsimp only at hL ⊢
            unfold lookupSlotFrom at hL ⊢
            cases hW : resolveAddressBits root gate.capAddr 64 st with
            | error f => rw [hW] at hL; cases hL
            | ok p =>
              obtain ⟨ref', rem⟩ := p
              rw [hW] at hL
              dsimp only at hL
              cases hL
              rw [resolveAddressBits_of_cnodeSlotsKept h gate.capAddr 64 root _ rem cap hW hC]
        rw [hL']
        dsimp only
        obtain ⟨c', hc', hT', hE'⟩ := lookupSlotCap_target_of_cnodeSlotsKept h hC
        rw [hc']
        dsimp only
        rw [capTargetsReservedKernelObject_congr_target hT', if_neg hRes]
        exact ⟨c', rfl, hT', hE'⟩

/-- **A resolution of a capability naming no untyped object resolves to it
again** over a step that keeps every CNode. -/
theorem syscallResolveCap_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    (gate : SyscallGate) {cap : Capability} (hR : syscallResolveCap gate st = .ok (cap, st))
    (hU : ¬ capNamesUntyped st cap) : syscallResolveCap gate st' = .ok (cap, st') := by
  obtain ⟨c', hc', -, hE⟩ := syscallResolveCap_target_of_cnodeSlotsKept h gate hR
  rw [hc', hE hU]

/-- A kept kind keeps the kind an id holds, read in place. -/
theorem objectKindIs_of_cnodeSlotsKept {st st' : SystemState} (h : CNodeSlotsKept st st')
    (id : SeLe4n.ObjId) (kind : KernelObjectType) :
    objectKindIs st' id kind = objectKindIs st id kind := by
  have hK := h.kind id
  unfold objectKindIs
  rw [SystemState.getObject?_eq_getElem, SystemState.getObject?_eq_getElem]
  cases h1 : st.objects[id]? with
  | none =>
    rw [h1] at hK
    cases h2 : st'.objects[id]? with
    | none => rfl
    | some o' => rw [h2] at hK; cases hK
  | some o =>
    rw [h1] at hK
    cases h2 : st'.objects[id]? with
    | none => rw [h2] at hK; cases hK
    | some o' =>
      rw [h2] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      dsimp only
      rw [hK]

/-- The type verdict reads a capability's target alone. -/
theorem syscallTargetAccepted_congr_target (sid : SyscallId) (st : SystemState)
    {c c' : Capability} (h : c'.target = c.target) :
    syscallTargetAccepted sid st c' = syscallTargetAccepted sid st c := by
  unfold syscallTargetAccepted
  rw [h]

/-- **The type verdict is kept**: the target type each syscall accepts reads
the kind of the object a capability names, which a step that keeps every CNode
keeps. -/
theorem syscallTargetAccepted_of_cnodeSlotsKept {st st' : SystemState}
    (h : CNodeSlotsKept st st') (sid : SyscallId) (cap : Capability) :
    syscallTargetAccepted sid st' cap = syscallTargetAccepted sid st cap := by
  unfold syscallTargetAccepted
  cases cap.target with
  | object id =>
    dsimp only
    cases syscallObjectKind? sid with
    | none => rfl
    | some kind => exact objectKindIs_of_cnodeSlotsKept h id kind
  | _ => rfl

/-- A capability a reply-receive accepts names an endpoint, so no untyped
object: a capability transfer never rewrites it. -/
theorem not_capNamesUntyped_of_replyRecvAccepted {st : SystemState} {cap : Capability}
    (h : syscallTargetAccepted .replyRecv st cap = true) : ¬ capNamesUntyped st cap := by
  rintro ⟨oid, hT, hU⟩
  unfold syscallTargetAccepted at h
  rw [hT] at h
  dsimp only [syscallObjectKind?] at h
  unfold objectKindIs at h
  unfold SystemState.getUntyped? at hU
  rw [SystemState.getObject?_eq_getElem] at h
  cases ho : st.objects[oid]? with
  | none => rw [ho] at hU; cases hU
  | some o =>
    rw [ho] at h hU
    dsimp only at h
    cases o with
    | untyped _ => cases h
    | _ => cases hU

end SeLe4n.Kernel
