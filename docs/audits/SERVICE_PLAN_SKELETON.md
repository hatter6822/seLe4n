# seLe4n Verified Service Interface Layer  
## Complete Workstream Planning Document

---

# 0. Executive Summary

This document defines the design and implementation plan for introducing a:

> **Verified Service Interface Layer** into the seLe4n microkernel

This is **not** a traditional service subsystem.

Instead, it is a:

> **Capability-indexed, formally verified interface enforcement layer**

This preserves microkernel principles while enabling:

- type-safe IPC
- proof-carrying service registration
- deterministic execution
- composable system-wide verification

---

# 1. Design Principles (Non-Negotiable)

## 1.1 Mechanism ≠ Policy

### Kernel MAY:
- enforce capability safety  
- enforce interface typing  
- enforce lifecycle correctness  

### Kernel MUST NOT:
- perform naming  
- implement discovery  
- orchestrate services  
- manage dependencies  

---

## 1.2 Authority = Capability

- No global service registry  
- No string-based lookup  
- No ambient authority  

All access must be capability-mediated.

---

## 1.3 Determinism

All kernel-visible behavior must be:

- total  
- deterministic  
- side-effect explicit  

---

## 1.4 Proof-Carrying Registration

Each service must provide:

- interface correctness proof  
- invariant preservation guarantee  

---

## 1.5 Minimal TCB Expansion

The service layer must:

- remain small  
- be compositional  
- avoid global coupling  

---

# 2. Architecture

## 2.1 Layered System

User Space:

- Service Managers (policy, replaceable)
- Verified Service Graphs (Lean)
- Application Services

Verified Interface Layer (Kernel):

- Interface typing
- Capability enforcement
- Deterministic dispatch

# Microkernel

## Scheduling
---

## 2.2 Core Abstraction

A service is:


(ServiceId, InterfaceSpec, Capability)


Not:
- a name  
- a global object  
- a managed runtime entity  

---

# 3. Formal Model

## 3.1 Interface Specification


InterfaceSpec:
Req : Type
Resp : Type
inv : Resp → Prop


---

## 3.2 Service Descriptor


ServiceDesc:
sid : ServiceId
iface : InterfaceSpec
endpoint : Capability


---

## 3.3 Verified Service


VerifiedService:
desc : ServiceDesc
impl : Req → KernelM Resp
proof : ∀ req, response satisfies invariant


---

## 3.4 Kernel State


KernelState:
services : List ServiceDesc
caps : List Capability


---

## 3.5 Global Invariant

For all services:


endpoint ∈ caps


---

# 4. Kernel API (Minimal Surface)

## Required Operations

- `registerService`
- `lookupServiceByCap`
- `revokeService`

---

## Design Constraint

> If more than ~5–7 primitives are required, policy has leaked into the kernel.

---

# 5. Implementation Workstream

---

## Phase 1 — Core Types & State

**Goal:** Define minimal formal model

Tasks:
- Define core structures  
- Define kernel state  
- Define invariants  

Deliverable:
- Compiling Lean module  

---

## Phase 2 — Verified Services

**Goal:** Introduce proof-carrying services

Tasks:
- Define `VerifiedService`  
- Require proofs at registration  

Deliverable:
- Only valid services can be registered  

---

## Phase 3 — Kernel API

**Goal:** Implement minimal mechanism

Tasks:
- registration  
- lookup  
- revocation  

Deliverable:
- small, auditable kernel API  

---

## Phase 4 — Proof Completion

**Goal:** Close invariants

Prove:
- registration preserves invariants  
- revocation preserves invariants  
- lookup soundness  

Deliverable:
- stable formal core  

---

## Phase 5 — Typed Invocation (Next Step)

Introduce:

```lean
structure TypedCap where
  cap   : Capability
  iface : InterfaceSpec
```

Goal:

- enforce type-safe IPC

## Phase 6 — Determinism

Prove:

- same input + same state → same output

## Phase 7 — Move Policy to User Space

Move OUT of kernel:

  - naming

  - discovery

  - dependency graphs

  - orchestration

## Phase 8 — Optimization & Refinement

- Lean → Rust/C extraction

- prove refinement correctness

- eliminate runtime overhead

## 6. Lean Kernel Skeleton (Proof-Complete Minimal Core)


```
namespace seLe4n

abbrev ServiceId := Nat
abbrev CapId     := Nat
abbrev ThreadId  := Nat

structure Capability where
  id    : CapId
  owner : ThreadId
  deriving DecidableEq

structure InterfaceSpec where
  Req  : Type
  Resp : Type
  inv  : Resp → Prop

structure ServiceDesc where
  sid      : ServiceId
  iface    : InterfaceSpec
  endpoint : Capability

structure KernelState where
  services : List ServiceDesc
  caps     : List Capability

abbrev KernelM := StateM KernelState

def validCap (s : KernelState) (c : Capability) : Prop :=
  c ∈ s.caps

def validService (s : KernelState) (sd : ServiceDesc) : Prop :=
  validCap s sd.endpoint

def KernelInvariant (s : KernelState) : Prop :=
  ∀ sd ∈ s.services, validService s sd

structure VerifiedService where
  desc  : ServiceDesc
  impl  : desc.iface.Req → KernelM desc.iface.Resp
  proof :
    ∀ req st,
      let (resp, _) := (impl req).run st
      desc.iface.inv resp

def registerService (vs : VerifiedService) : KernelM Unit := do
  let st ← get
  set { st with services := vs.desc :: st.services }

def lookupServiceByCap (c : Capability) : KernelM (Option ServiceDesc) := do
  let st ← get
  pure <| st.services.find? (fun sd => sd.endpoint = c)

def revokeService (c : Capability) : KernelM Unit := do
  let st ← get
  let newServices := st.services.filter (fun sd => sd.endpoint ≠ c)
  set { st with services := newServices }

lemma mem_cons {α} (x y : α) (xs : List α) :
  x ∈ y :: xs → x = y ∨ x ∈ xs := by
  intro h
  cases h with
  | head => exact Or.inl rfl
  | tail h' => exact Or.inr h'

lemma mem_filter {α} (p : α → Bool) (x : α) (xs : List α) :
  x ∈ xs.filter p → x ∈ xs := by
  intro h
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp at h
    cases h with
    | inl h1 =>
        cases h1
        exact List.mem_cons_self _ _
    | inr h2 =>
        exact List.mem_cons_of_mem _ (ih h2)

theorem register_preserves_invariant
  (vs : VerifiedService)
  (s : KernelState)
  (h : KernelInvariant s)
  (hcap : validCap s vs.desc.endpoint)
  : KernelInvariant (registerService vs |>.run' s) :=
by
  intro sd hmem
  simp [registerService] at hmem ⊢
  have hsplit := mem_cons sd vs.desc s.services hmem
  cases hsplit with
  | inl h_eq =>
      subst h_eq
      exact hcap
  | inr h_old =>
      exact h sd h_old

theorem revoke_preserves_invariant
  (c : Capability)
  (s : KernelState)
  (h : KernelInvariant s)
  : KernelInvariant (revokeService c |>.run' s) :=
by
  intro sd hmem
  simp [revokeService] at hmem ⊢
  have h_old := mem_filter (fun sd => sd.endpoint ≠ c) sd s.services hmem
  exact h sd h_old

end seLe4n

```

# 7. Risks & Mitigations

Kernel Bloat

Mitigation:

  - strict API size control

Policy Leakage

Mitigation:

  - capability-only access

Proof Complexity

Mitigation:

  - compositional invariants

Performance Regression

Mitigation:

  - staged refinement

# 8. Success Criteria

Technical

- small kernel

- deterministic behavior

- type-safe IPC

Architectural

- no policy in kernel

- replaceable services

Formal

- invariant preservation

- composable proofs

# 9. Final Principle

The kernel enforces constraints — it does not decide behavior.
