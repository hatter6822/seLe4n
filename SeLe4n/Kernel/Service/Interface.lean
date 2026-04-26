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

- `sid`: the service identity in the service graph
- `iface`: the interface specification this service implements
- `endpointCap`: the capability for the service's endpoint object -/
structure ServiceRegistration where
  sid         : ServiceId
  iface       : InterfaceSpec
  endpointCap : Capability
  deriving Repr, DecidableEq

namespace ServiceRegistration

instance : Inhabited ServiceRegistration where
  default := {
    sid := ServiceId.sentinel
    iface := default
    endpointCap := { target := .object ⟨0⟩, rights := .empty }
  }

end ServiceRegistration

end SeLe4n.Model
