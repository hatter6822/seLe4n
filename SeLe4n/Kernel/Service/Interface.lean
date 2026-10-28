-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object

/-! # Service Interface Types — seLe4n Extension

Defines the capability-indexed interface enforcement layer for the service
subsystem. This replaces the lifecycle-focused orchestration model with a
registry of concrete interface specifications and capability-mediated service
registrations.

**InterfaceSpec** defines what a service provides: method count, message size
bounds, and whether grant rights are required.

**ServiceRegistration** binds a service identity to an interface specification
and the endpoint capability through which the service is accessible.

See the WS-Q master plan §3.3 for the architectural rationale. -/

namespace SeLe4n.Model

/-- Concrete interface specification for service registration.
No universe polymorphism — all fields are concrete types.

- `ifaceId`: unique identifier for this interface type
- `methodCount`: number of methods the interface exposes
- `maxMessageSize`: maximum IPC message register count for requests
- `maxResponseSize`: maximum IPC message register count for responses
- `requiresGrant`: whether invoking this interface requires Grant right -/
structure InterfaceSpec where
  ifaceId         : SeLe4n.InterfaceId
  methodCount     : Nat
  maxMessageSize  : Nat
  maxResponseSize : Nat
  requiresGrant   : Bool
  deriving Repr, DecidableEq

namespace InterfaceSpec

instance : BEq InterfaceSpec := ⟨fun a b => a == b⟩

instance : Inhabited InterfaceSpec where
  default := {
    ifaceId := SeLe4n.InterfaceId.sentinel
    methodCount := 0
    maxMessageSize := 0
    maxResponseSize := 0
    requiresGrant := false
  }

end InterfaceSpec

/-- Capability-mediated service registration binding a service to an
interface specification and the endpoint through which it is accessible.

- `iface`: the interface specification this service implements
- `endpointCap`: the capability for the service's endpoint object

A service's identity is its endpoint's (`ServiceRegistration.sid`, derived
from `endpointCap`): one registration per endpoint, so no registration can name
an identity its endpoint does not have. -/
structure ServiceRegistration where
  iface       : InterfaceSpec
  endpointCap : Capability
  deriving Repr, DecidableEq

namespace ServiceRegistration

/-- **WS-ZA ZA5.6: a service's identity is its endpoint's id**, derived from
the capability the registration keeps, so it has one owner.  A capability that
names no object gives the sentinel; `registerService` refuses such a target, so
no registry entry has it. -/
@[inline] def sid (reg : ServiceRegistration) : ServiceId :=
  match reg.endpointCap.target with
  | .object e => ServiceId.ofNat e.toNat
  | _ => ServiceId.sentinel

/-- The identity of a registration whose capability names the object `e`. -/
theorem sid_of_target {reg : ServiceRegistration} {e : SeLe4n.ObjId}
    (h : reg.endpointCap.target = .object e) : reg.sid = ServiceId.ofNat e.toNat := by
  unfold sid; rw [h]

instance : Inhabited ServiceRegistration where
  default := {
    iface := default
    endpointCap := { target := .object ⟨0⟩, rights := .empty }
  }

end ServiceRegistration

namespace EndpointService

/-- **WS-ZA ZA5.8: the service record a registration writes on its endpoint**:
the flag set, and the registration's words — its interface, and the capability
it keeps less the target, which is the endpoint. -/
@[inline] def ofRegistration (reg : ServiceRegistration) : EndpointService :=
  { registered := true, interfaceId := reg.iface.ifaceId,
    methodCount := reg.iface.methodCount, maxMessageSize := reg.iface.maxMessageSize,
    maxResponseSize := reg.iface.maxResponseSize, requiresGrant := reg.iface.requiresGrant,
    capRights := reg.endpointCap.rights, capBadgeWord := reg.endpointCap.badgeWord,
    capBadged := reg.endpointCap.badged, capMapAsid := reg.endpointCap.mapAsid,
    capMapVaddr := reg.endpointCap.mapVaddr, capMapEpoch := reg.endpointCap.mapEpoch,
    capMapped := reg.endpointCap.mapped, capFreeIndex := reg.endpointCap.freeIndex }

/-- **The registration a service record holds on the endpoint `e`**: its words,
the kept capability naming `e`. -/
@[inline] def registrationAt (sv : EndpointService) (e : SeLe4n.ObjId) : ServiceRegistration :=
  { iface := { ifaceId := sv.interfaceId, methodCount := sv.methodCount,
               maxMessageSize := sv.maxMessageSize, maxResponseSize := sv.maxResponseSize,
               requiresGrant := sv.requiresGrant },
    endpointCap := { target := .object e, rights := sv.capRights,
                     badgeWord := sv.capBadgeWord, badged := sv.capBadged,
                     mapAsid := sv.capMapAsid, mapVaddr := sv.capMapVaddr,
                     mapEpoch := sv.capMapEpoch, mapped := sv.capMapped,
                     freeIndex := sv.capFreeIndex } }

@[simp] theorem ofRegistration_registered (reg : ServiceRegistration) :
    (ofRegistration reg).registered = true := rfl

/-- The registration a record holds names its endpoint. -/
@[simp] theorem registrationAt_target (sv : EndpointService) (e : SeLe4n.ObjId) :
    (sv.registrationAt e).endpointCap.target = .object e := rfl

/-- The registration a record holds is under its endpoint's id. -/
@[simp] theorem registrationAt_sid (sv : EndpointService) (e : SeLe4n.ObjId) :
    (sv.registrationAt e).sid = ServiceId.ofNat e.toNat := rfl

/-- **A registration is the one its endpoint's record holds**: the record keeps
every word but the target, and the target is the endpoint. -/
theorem registrationAt_ofRegistration {reg : ServiceRegistration} {e : SeLe4n.ObjId}
    (h : reg.endpointCap.target = .object e) : (ofRegistration reg).registrationAt e = reg := by
  obtain ⟨⟨_, _, _, _, _⟩, ⟨t, _, _, _, _, _, _, _, _⟩⟩ := reg
  simp only at h; subst h; rfl

end EndpointService

end SeLe4n.Model
