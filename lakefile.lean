import Lake
open Lake DSL

package "seLe4n" where
  version := v!"0.12.15"

lean_lib «SeLe4n» where
  -- Kernel source library

@[default_target]
lean_exe "sele4n" where
  root := `Main

lean_exe "trace_sequence_probe" where
  root := `tests.TraceSequenceProbe

lean_exe "negative_state_suite" where
  root := `tests.NegativeStateSuite

lean_exe "information_flow_suite" where
  root := `tests.InformationFlowSuite
