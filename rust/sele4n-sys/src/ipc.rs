//! IPC operations — endpoint send/receive/call/reply, notification signal/wait.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `apiEndpointSend`, `apiEndpointReceive`,
//! `apiEndpointCall`, `apiEndpointReply`.

use sele4n_types::{CPtr, Badge, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};

/// Maximum number of inline message registers (seL4_MsgMaxLength).
pub const MAX_MSG_REGS: usize = 120;

/// Maximum number of extra capability addresses per message (seL4_MsgMaxExtraCaps).
pub const MAX_EXTRA_CAPS: usize = 3;

/// An IPC message with up to 4 inline registers and a label.
///
/// On ARM64, only 4 inline message registers are available (x2–x5).
/// For messages longer than 4 registers, an IPC buffer mechanism is needed
/// (not yet modeled in the abstract kernel).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpcMessage {
    /// Inline message registers (up to 4 on ARM64).
    pub regs: [u64; 4],
    /// Number of valid registers (0..=4).
    pub length: u8,
    /// User-defined label.
    pub label: u64,
}

impl IpcMessage {
    /// Create an empty message with the given label.
    pub const fn new(label: u64) -> Self {
        Self { regs: [0; 4], length: 0, label }
    }

    /// Push a register value. Returns error if all 4 inline slots are full.
    pub fn push(&mut self, val: u64) -> Result<(), sele4n_types::KernelError> {
        if self.length >= 4 {
            return Err(sele4n_types::KernelError::IpcMessageTooLarge);
        }
        self.regs[self.length as usize] = val;
        self.length += 1;
        Ok(())
    }
}

/// Send a message to an endpoint.
///
/// Lean: `apiEndpointSend` (API.lean) — requires `.write` right.
#[must_use]
pub fn endpoint_send(dest: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo {
        length: msg.length,
        extra_caps: 0,
        label: msg.label,
    };
    invoke_syscall(SyscallRequest {
        cap_addr: dest,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Send,
    })
}

/// Receive a message from an endpoint. Blocks until a message arrives.
///
/// Lean: `apiEndpointReceive` (API.lean) — requires `.read` right.
///
/// Returns the received badge and response registers.
#[must_use]
pub fn endpoint_receive(src: CPtr) -> KernelResult<(Badge, SyscallResponse)> {
    let msg_info = MessageInfo { length: 0, extra_caps: 0, label: 0 };
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: src,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
    })?;
    Ok((resp.badge, resp))
}

/// Call an endpoint (send + blocking receive in one syscall).
///
/// Lean: `apiEndpointCall` (API.lean) — requires `.write` right.
#[must_use]
pub fn endpoint_call(dest: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo {
        length: msg.length,
        extra_caps: 0,
        label: msg.label,
    };
    invoke_syscall(SyscallRequest {
        cap_addr: dest,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Call,
    })
}

/// Reply to a caller (one-shot reply capability).
///
/// Lean: `apiEndpointReply` (API.lean) — requires `.write` right.
#[must_use]
pub fn endpoint_reply(reply_cap: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo {
        length: msg.length,
        extra_caps: 0,
        label: msg.label,
    };
    invoke_syscall(SyscallRequest {
        cap_addr: reply_cap,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Reply,
    })
}

/// Signal a notification object (badge OR accumulation).
///
/// Lean: This is an IPC send to a notification object. The kernel accumulates
/// badges via bitwise OR (`Badge.bor`).
#[must_use]
pub fn notification_signal(ntfn: CPtr, badge: Badge) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo { length: 0, extra_caps: 0, label: 0 };
    invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [badge.0, 0, 0, 0],
        syscall_id: SyscallId::Send,
    })
}

/// Wait on a notification object. Blocks until signaled.
///
/// Returns the accumulated badge value.
#[must_use]
pub fn notification_wait(ntfn: CPtr) -> KernelResult<Badge> {
    let msg_info = MessageInfo { length: 0, extra_caps: 0, label: 0 };
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
    })?;
    Ok(resp.badge)
}
