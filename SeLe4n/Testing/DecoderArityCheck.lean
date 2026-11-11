-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.DecoderArity

/-!
# The decoder-arity check, run over the kernel

`#assert_decoder_arities` is an elaborator command, so the module that runs it
imports `Lean`; it lives here, outside `SeLe4n.lean`'s import closure, so the
elaborator never reaches the kernel's archive.  Tier 1 builds it
(`scripts/test_tier1_build.sh`), and a failed check fails that build.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-! **The truncation table is the decodes' word counts** (`truncationMinimum`):
each syscall with a nonzero minimum is listed with the decode its dispatch
reads its arguments through, and the check reads that decode's body, failing
the build unless its first action is the truncation check at the syscall's
minimum and the words it reads are exactly `0, …, minimum - 1`
(`DecoderArity`).  The pairing is pinned against the checked dispatch
(`dispatchWithCapChecked`): each listed syscall's arm calls exactly its listed
decode, and no other syscall's arm calls one.  The signal, the receives and the declassifications have
minimum 0, as seL4 checks no length for an IPC or a signal. -/
#assert_decoder_arities truncationMinimum requireMessageLength requireMsgReg
    SyscallDecodeResult.msgRegs SyscallDecodeResult.syscallId dispatchWithCapChecked [
  (.cspaceMint, decodeCSpaceMintArgs), (.cspaceCopy, decodeCSpaceCopyArgs),
  (.cspaceMove, decodeCSpaceMoveArgs), (.cspaceDelete, decodeCSpaceDeleteArgs),
  (.cspaceRevoke, decodeCSpaceDeleteArgs), (.mintReplyCap, decodeCSpaceCopyArgs),
  (.untypedRetype, decodeUntypedRetypeArgs), (.vspaceMap, decodeVSpaceMapArgs),
  (.vspaceUnmap, decodeVSpaceUnmapArgs),
  (.vspaceUnifyInstruction, decodeVSpaceUnifyInstructionArgs),
  (.serviceRegister, decodeServiceRegisterArgs),
  (.schedContextConfigure, decodeSchedContextConfigureArgs),
  (.schedContextBind, decodeSchedContextBindArgs),
  (.tcbBindNotification, decodeTcbBindNotificationArgs),
  (.irqControlGet, decodeIrqControlGetArgs),
  (.irqHandlerSetNotification, decodeIrqHandlerSetNotificationArgs),
  (.tcbSetPriority, decodeSetPriorityArgs), (.tcbSetMCPriority, decodeSetMCPriorityArgs),
  (.tcbSetIPCBuffer, decodeSetIPCBufferArgs), (.tcbSetAffinity, decodeSetAffinityArgs),
  (.tcbSetFaultHandler, decodeSetFaultHandlerArgs), (.tcbSetSpace, decodeSetSpaceArgs),
  (.pageTableMap, decodePageTableMapArgs), (.auditRead, decodeAuditReadArgs),
  (.auditDrain, decodeAuditDrainArgs)]

end SeLe4n.Kernel
