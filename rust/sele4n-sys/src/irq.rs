// SPDX-License-Identifier: GPL-3.0-or-later
//! Interrupt-control and interrupt-handler operations — seL4's `IRQControl` and
//! `IRQHandler` invocations.
//!
//! Lean: `irqControlGet`, `irqHandlerSetNotification` and `irqHandlerClear`
//! (`SeLe4n/Kernel/Capability/IrqControl.lean`) and `Architecture.irqHandlerAck`
//! (`SeLe4n/Kernel/Architecture/InterruptMask.lean`), behind the `.irqControlGet`,
//! `.irqHandlerSetNotification`, `.irqHandlerClear` and `.irqHandlerAck` arms of
//! `API.lean`, WS-ZA ZA6.32.  The kernel
//! delivers a device interrupt to the notification its handler is bound to and
//! masks the line at the interrupt controller until the handler acknowledges it,
//! as seL4's `handleInterrupt` does.

use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest};
use sele4n_types::{CPtr, KernelResult, Slot, SyscallId};

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

/// Issue the handler capability of interrupt line `line` — seL4's
/// `seL4_IRQControl_Get`.
///
/// Invoked on the interrupt-control capability (`Write` right).  The handler
/// capability is installed at slot `dst_slot` of the CNode `dst_cnode` names
/// (a CNode capability with the `Write` right), as a derivation child of the
/// interrupt-control capability, and the line is enabled.  A line that is no
/// device line of the board is refused (`InvalidIrq`), as is one a handler
/// already holds (`RevocationRequired`) and an occupied slot
/// (`TargetSlotOccupied`).
#[inline]
pub fn irq_control_get(
    control_cap: CPtr,
    line: u64,
    dst_cnode: CPtr,
    dst_slot: Slot,
) -> KernelResult<()> {
    invoke_syscall(SyscallRequest {
        cap_addr: control_cap,
        msg_info: MessageInfo::new_const(3, 0, 0),
        msg_regs: [line, dst_cnode.into(), dst_slot.into(), 0],
        syscall_id: SyscallId::IrqControlGet,
    })?;
    Ok(())
}

/// Bind the notification `notification_cap` names to the line a handler
/// capability names — seL4's `seL4_IRQHandler_SetNotification`.
///
/// Requires the `Write` right on the handler capability; the notification
/// capability must carry the `Write` (send) right.  A copy of it replaces the
/// one bound before, so the line's next delivery signals it with its badge.
#[inline]
pub fn irq_handler_set_notification(handler_cap: CPtr, notification_cap: CPtr) -> KernelResult<()> {
    invoke_syscall(SyscallRequest {
        cap_addr: handler_cap,
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [notification_cap.into(), 0, 0, 0],
        syscall_id: SyscallId::IrqHandlerSetNotification,
    })?;
    Ok(())
}

/// Unbind the notification of the line a handler capability names — seL4's
/// `seL4_IRQHandler_Clear`.  No message registers are sent.
#[inline]
pub fn irq_handler_clear(handler_cap: CPtr) -> KernelResult<()> {
    invoke_syscall(SyscallRequest {
        cap_addr: handler_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::IrqHandlerClear,
    })?;
    Ok(())
}
