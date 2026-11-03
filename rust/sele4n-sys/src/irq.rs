// SPDX-License-Identifier: GPL-3.0-or-later
//! Interrupt-handler operations — the acknowledge.
//!
//! Lean: `Architecture.irqHandlerAck` (`SeLe4n/Kernel/Architecture/InterruptMask.lean`)
//! behind the `.irqHandlerAck` arm of `API.lean`, WS-ZA ZA6.32.  The kernel
//! delivers a device interrupt to the notification its handler is bound to and
//! masks the line at the interrupt controller until the handler acknowledges it,
//! as seL4's `handleInterrupt` does.

use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Acknowledge the interrupt line an interrupt-handler capability names —
/// seL4's `seL4_IRQHandler_Ack`.
///
/// Unmasks the line at the interrupt controller, so its next assertion is
/// delivered to the handler's notification again.  Requires the `Write` right
/// on the handler capability; no message registers are sent.  A capability to
/// anything other than an interrupt handler is refused (`InvalidCapability`).
#[inline]
pub fn irq_handler_ack(handler_cap: CPtr) -> KernelResult<()> {
    invoke_syscall(SyscallRequest {
        cap_addr: handler_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::IrqHandlerAck,
    })?;
    Ok(())
}
