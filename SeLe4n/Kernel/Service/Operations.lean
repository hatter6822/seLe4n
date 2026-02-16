import SeLe4n.Model.State

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- External policy gate used by M5 orchestration helpers. -/
abbrev ServicePolicy := ServiceGraphEntry → Bool

/-- Deterministic service update helper in kernel-monad form. -/
def storeServiceEntry (sid : ServiceId) (entry : ServiceGraphEntry) : Kernel Unit :=
  fun st => .ok ((), storeServiceState sid entry st)

/-- Start a stopped service when policy allows and dependencies are running.

Deterministic check ordering:
1. service lookup (`objectNotFound`),
2. service must be `stopped` (`illegalState`),
3. policy predicate must allow start (`policyDenied`),
4. dependencies must be running (`dependencyViolation`),
5. status changes to `running` on success. -/
def serviceStart
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    match lookupService st sid with
    | none => .error .objectNotFound
    | some svc =>
        if svc.status = .stopped then
          if policyAllowsStart svc then
            if dependenciesSatisfied st sid then
              storeServiceEntry sid { svc with status := .running } st
            else
              .error .dependencyViolation
          else
            .error .policyDenied
        else
          .error .illegalState

/-- Stop a running service when policy allows.

Deterministic check ordering:
1. service lookup (`objectNotFound`),
2. service must be `running` (`illegalState`),
3. policy predicate must allow stop (`policyDenied`),
4. status changes to `stopped` on success. -/
def serviceStop
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy) : Kernel Unit :=
  fun st =>
    match lookupService st sid with
    | none => .error .objectNotFound
    | some svc =>
        if svc.status = .running then
          if policyAllowsStop svc then
            storeServiceEntry sid { svc with status := .stopped } st
          else
            .error .policyDenied
        else
          .error .illegalState

/-- Restart composes deterministic `stop` then `start` transition ordering.

Failure ordering:
1. any `serviceStop` failure is returned directly,
2. if stop succeeds then `serviceStart` runs over the post-stop state,
3. any start failure is returned directly,
4. success requires both stages to succeed. -/
def serviceRestart
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy) : Kernel Unit :=
  fun st =>
    match serviceStop sid policyAllowsStop st with
    | .error e => .error e
    | .ok (_, stStopped) => serviceStart sid policyAllowsStart stStopped

theorem serviceStart_error_policyDenied
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hStopped : svc.status = .stopped)
    (hPolicy : policyAllowsStart svc = false) :
    serviceStart sid policyAllowsStart st = .error .policyDenied := by
  unfold serviceStart
  simp [hSvc, hStopped, hPolicy]

theorem serviceStart_error_dependencyViolation
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStart : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hStopped : svc.status = .stopped)
    (hPolicy : policyAllowsStart svc = true)
    (hDeps : dependenciesSatisfied st sid = false) :
    serviceStart sid policyAllowsStart st = .error .dependencyViolation := by
  unfold serviceStart
  simp [hSvc, hStopped, hPolicy, hDeps]

theorem serviceStop_error_policyDenied
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hRunning : svc.status = .running)
    (hPolicy : policyAllowsStop svc = false) :
    serviceStop sid policyAllowsStop st = .error .policyDenied := by
  unfold serviceStop
  simp [hSvc, hRunning, hPolicy]

theorem serviceStop_error_illegalState
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (svc : ServiceGraphEntry)
    (hSvc : lookupService st sid = some svc)
    (hNotRunning : svc.status ≠ .running) :
    serviceStop sid policyAllowsStop st = .error .illegalState := by
  unfold serviceStop
  simp [hSvc, hNotRunning]

theorem serviceRestart_error_of_stop_error
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (e : KernelError)
    (hStop : serviceStop sid policyAllowsStop st = .error e) :
    serviceRestart sid policyAllowsStop policyAllowsStart st = .error e := by
  unfold serviceRestart
  simp [hStop]

theorem serviceRestart_error_of_start_error
    (st : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (stStopped : SystemState)
    (e : KernelError)
    (hStop : serviceStop sid policyAllowsStop st = .ok ((), stStopped))
    (hStart : serviceStart sid policyAllowsStart stStopped = .error e) :
    serviceRestart sid policyAllowsStop policyAllowsStart st = .error e := by
  unfold serviceRestart
  simp [hStop, hStart]

theorem serviceRestart_ok_implies_staged_steps
    (st st' : SystemState)
    (sid : ServiceId)
    (policyAllowsStop : ServicePolicy)
    (policyAllowsStart : ServicePolicy)
    (hStep : serviceRestart sid policyAllowsStop policyAllowsStart st = .ok ((), st')) :
    ∃ stStopped,
      serviceStop sid policyAllowsStop st = .ok ((), stStopped) ∧
      serviceStart sid policyAllowsStart stStopped = .ok ((), st') := by
  unfold serviceRestart at hStep
  cases hStop : serviceStop sid policyAllowsStop st with
  | error e => simp [hStop] at hStep
  | ok pair =>
      rcases pair with ⟨u, stStopped⟩
      cases u
      refine ⟨stStopped, ?_, ?_⟩
      · rfl
      · simpa [hStop] using hStep

end SeLe4n.Kernel
