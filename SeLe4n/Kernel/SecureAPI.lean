import SeLe4n.Kernel.InformationFlow.Enforcement
import SeLe4n.Kernel.Architecture.VSpace

namespace SeLe4n.Kernel

open SeLe4n.Model

private def tcbExists (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.objects tid.toObjId with
  | some (.tcb _) => true
  | _ => false

/-- Detect duplicate ASID roots in the discovered object index window. -/
def asidRootUnique (st : SystemState) (asid : SeLe4n.ASID) : Bool :=
  decide (((st.objectIndex.filter (fun oid =>
    match st.objects oid with
    | some (.vspaceRoot root) => root.asid = asid
    | _ => false)).length) ≤ 1)

/-- L-09/WS-E6: Secure API wrapper for endpoint send.
Rejects reserved IDs, missing sender TCBs, and applies information-flow checks. -/
def endpointSendSecure
    (ctx : LabelingContext)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    if endpointId.isReserved || sender.isReserved then
      .error .invalidCapability
    else if ¬ tcbExists st sender then
      .error .objectNotFound
    else
      endpointSendChecked ctx endpointId sender st

/-- L-09/WS-E6: Secure API wrapper for endpoint receive registration.
Rejects reserved IDs and missing receiver TCBs. -/
def endpointAwaitReceiveSecure
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    if endpointId.isReserved || receiver.isReserved then
      .error .invalidCapability
    else if ¬ tcbExists st receiver then
      .error .objectNotFound
    else
      endpointAwaitReceive endpointId receiver st

/-- L-09/WS-E6: Secure API wrapper for notification wait.
Rejects reserved IDs and missing waiter TCBs. -/
def notificationWaitSecure
    (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) : Kernel (Option SeLe4n.Badge) :=
  fun st =>
    if notificationId.isReserved || waiter.isReserved then
      .error .invalidCapability
    else if ¬ tcbExists st waiter then
      .error .objectNotFound
    else
      notificationWait notificationId waiter st

/-- L-09/WS-E6: Secure API wrapper for capability mint.
Rejects sentinel CNode identifiers and applies information-flow checks. -/
def cspaceMintSecure
    (ctx : LabelingContext)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    if src.cnode.isReserved || dst.cnode.isReserved then
      .error .invalidCapability
    else
      cspaceMintChecked ctx src dst rights badge st

/-- L-09/WS-E6: Secure API wrapper for service restart.
Rejects sentinel service identifiers and applies information-flow checks. -/
def serviceRestartSecure
    (ctx : LabelingContext)
    (orchestrator sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    if orchestrator.isReserved || sid.isReserved then
      .error .invalidCapability
    else
      serviceRestartChecked ctx orchestrator sid policyAllowsStop policyAllowsStart st

/-- L-09/WS-E6: Strict VSpace map wrapper that rejects ambiguous ASID bindings. -/
def vspaceMapPageSecure
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) : Kernel Unit :=
  fun st =>
    if asidRootUnique st asid then
      SeLe4n.Kernel.Architecture.vspaceMapPage asid vaddr paddr st
    else
      .error .illegalState

/-- L-09/WS-E6: Strict VSpace unmap wrapper that rejects ambiguous ASID bindings. -/
def vspaceUnmapPageSecure
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    if asidRootUnique st asid then
      SeLe4n.Kernel.Architecture.vspaceUnmapPage asid vaddr st
    else
      .error .illegalState

/-- L-09/WS-E6: Strict VSpace lookup wrapper that rejects ambiguous ASID bindings. -/
def vspaceLookupSecure
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) : Kernel SeLe4n.PAddr :=
  fun st =>
    if asidRootUnique st asid then
      SeLe4n.Kernel.Architecture.vspaceLookup asid vaddr st
    else
      .error .illegalState

end SeLe4n.Kernel
