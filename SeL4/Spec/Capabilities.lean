import SeL4.Model.KernelState

namespace SeL4
namespace Spec
open Model

/-- Capability safety policy (starter skeleton). -/
def CapabilitySafe (s : KernelState) : Prop :=
  ∀ cnodeId cnode,
    s.cnodes cnodeId = some cnode →
      ∀ slot,
        match cnode.slots slot with
        | .nullCap => True
        | .threadCap tid => (s.threads tid).isSome
        | .endpointCap eid _ => (s.endpoints eid).isSome
        | .notificationCap _ => True
        | .cnodeCap cid => (s.cnodes cid).isSome

end Spec
end SeL4
