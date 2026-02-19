import SeLe4n.Kernel.InformationFlow.Projection
import SeLe4n.Kernel.IPC.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A successful endpoint send preserves low-equivalence for observers that cannot
see the sender thread and cannot observe the endpoint object itself. -/
theorem endpointSend_preserves_lowEquivalent
    (ctx : LabelingContext)
    (observer : IfObserver)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent ctx observer s₁ s₂)
    (_hSenderHigh : threadObservable ctx observer sender = false)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
    (hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂')) :
    lowEquivalent ctx observer s₁' s₂' := by
  rcases endpointSend_ok_as_storeObject s₁ s₁' endpointId sender hStep₁ with ⟨ep₁, hStore₁⟩
  rcases endpointSend_ok_as_storeObject s₂ s₂' endpointId sender hStep₂ with ⟨ep₂, hStore₂⟩
  have hObjLow : projectObjects ctx observer s₁ = projectObjects ctx observer s₂ := by
    exact congrArg ObservableState.objects hLow
  have hRunLow : projectRunnable ctx observer s₁ = projectRunnable ctx observer s₂ := by
    exact congrArg ObservableState.runnable hLow
  have hCurLow : projectCurrent ctx observer s₁ = projectCurrent ctx observer s₂ := by
    exact congrArg ObservableState.current hLow
  have hSvcLow : projectServiceStatus ctx observer s₁ = projectServiceStatus ctx observer s₂ := by
    exact congrArg ObservableState.services hLow
  have hObj' : projectObjects ctx observer s₁' = projectObjects ctx observer s₂' := by
    funext oid
    by_cases hObs : objectObservable ctx observer oid
    · by_cases hEq : oid = endpointId
      · subst hEq
        simp [projectObjects, hEndpointHigh]
      · have hObj₁ : s₁'.objects oid = s₁.objects oid :=
          storeObject_objects_ne s₁ s₁' endpointId oid (.endpoint ep₁) hEq hStore₁
        have hObj₂ : s₂'.objects oid = s₂.objects oid :=
          storeObject_objects_ne s₂ s₂' endpointId oid (.endpoint ep₂) hEq hStore₂
        have hObjBase : s₁.objects oid = s₂.objects oid := by
          have hBase := congrFun hObjLow oid
          simpa [projectObjects, hObs] using hBase
        simpa [projectObjects, hObs, hObj₁, hObj₂] using hObjBase
    · simp [projectObjects, hObs]
  have hRun' : projectRunnable ctx observer s₁' = projectRunnable ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' endpointId (.endpoint ep₁) hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' endpointId (.endpoint ep₂) hStore₂
    simpa [projectRunnable, hSched₁, hSched₂] using hRunLow
  have hCur' : projectCurrent ctx observer s₁' = projectCurrent ctx observer s₂' := by
    have hSched₁ := storeObject_scheduler_eq s₁ s₁' endpointId (.endpoint ep₁) hStore₁
    have hSched₂ := storeObject_scheduler_eq s₂ s₂' endpointId (.endpoint ep₂) hStore₂
    simpa [projectCurrent, hSched₁, hSched₂] using hCurLow
  have hSvc' : projectServiceStatus ctx observer s₁' = projectServiceStatus ctx observer s₂' := by
    unfold storeObject at hStore₁ hStore₂
    cases hStore₁
    cases hStore₂
    simpa [projectServiceStatus] using hSvcLow
  unfold lowEquivalent
  simp [projectState, hObj', hRun', hCur', hSvc']

end SeLe4n.Kernel
