A few things I have noticed. 


Key actionable items: 

  - make AccessRightSet.mk private, ensure isWord64 enforcement at hardware boundary, prefer edgeWellFounded over BFS-based acyclic for CDT security checks.
  - CDT acyclicity proof burden on callers (Medium), verify processRevokeNode_lenient is dead code, ensure API always dispatches to CDT-based revocation.
  - unproven size field and recomputeMaxPriority (Medium), document lack of starvation freedom guarantee (seL4-faithful), consider using List.get with proof for domain switch index.
  - missing formal commutativity proofs between builder and frozen operations. RadixTree slot aliasing is safe given documented preconditions. 
  - Virtual address not bounds-checked in VSpace map operations — unbounded VAddr can exceed 2^48, creating a model-reality gap on ARM64
  - ASID not bounds-checked against maxASID at decode boundary — same model-reality gap
  - physicalAddressBound mismatch with RPi5's 44-bit PA width, wrong error code in decodeVSpaceMapArgs, and GIC CPU interface size discrepancy. 
  - API dispatch for lifecycle retype uses lifecycleRetypeDirect, bypassing both cleanup (dangling scheduler/IPC references) and memory scrubbing (cross-domain information leakage). The safe wrapper lifecycleRetypeWithCleanup exists but is never called from the dispatch path. 
  - notificationSignalChecked not wired into syscall dispatch (Medium), NI for compound IPC relies on undischarged projection hypotheses.
  - Missing notificationSignal, replyRecv, nbSend, nbRecv syscall variants — fundamental seL4 operations unreachable from user-space
  - CSpace mint/copy/move constrained to same CNode (cross-CNode transfers impossible), retype right mismatch between gate check (.retype) and authority check (.write), missing registryInterfaceValid preservation proof. The call dispatch uses inline flow check instead of a proven checked wrapper.
  - CSpace root fallback to ObjId in cap transfer could use bogus CNode root if invariants violated — should return error instead
  - GrantReply right defined but has no operational effect in IPC — strictly more restrictive than seL4 (not exploitable)
  - Cap transfer uses fixed slot 0 for CDT tracking — imprecise but over-revokes rather than under-revokes
