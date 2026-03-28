//! IPC operations — 7 syscall wrappers covering endpoint and notification ops.
//!
//! - `endpoint_send` / `endpoint_receive` / `endpoint_call` / `endpoint_reply`
//! - `notification_signal` / `notification_wait`
//! - `endpoint_reply_recv` (compound: reply + blocking receive)
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `dispatchSyscall` → `dispatchWithCap`.

use sele4n_types::{Badge, CPtr, KernelResult, SyscallId, ThreadId};
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

impl Default for IpcMessage {
    fn default() -> Self { Self::new(0) }
}

impl IpcMessage {
    /// Create an empty message with the given label.
    pub const fn new(label: u64) -> Self {
        Self { regs: [0; 4], length: 0, label }
    }

    /// Push a register value. Returns `IpcMessageTooLarge` if all 4 inline
    /// ARM64 slots (x2–x5) are full.
    #[inline]
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
#[inline]
pub fn endpoint_send(dest: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new(msg.length, 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
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
#[inline]
pub fn endpoint_receive(src: CPtr) -> KernelResult<(Badge, SyscallResponse)> {
    // V1-D: new_const() is compile-time validated — infallible for valid constants.
    let msg_info = MessageInfo::new_const(0, 0, 0);
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: src,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
    })?;
    Ok((resp.badge(), resp))
}

/// Call an endpoint (send + blocking receive in one syscall).
///
/// Lean: `apiEndpointCall` (API.lean) — requires `.write` right.
#[inline]
pub fn endpoint_call(dest: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new(msg.length, 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
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
#[inline]
pub fn endpoint_reply(reply_cap: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new(msg.length, 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    invoke_syscall(SyscallRequest {
        cap_addr: reply_cap,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Reply,
    })
}

/// Signal a notification object (badge OR accumulation).
///
/// The badge value is passed via message register 0 (x2). The kernel's
/// `decodeNotificationSignalArgs` reads MR\[0\] and accumulates it into the
/// notification object's badge word via bitwise OR (`Badge.bor`).
///
/// Lean: `notificationSignal` (API.lean) dispatches to
/// `decodeNotificationSignalArgs` (SyscallArgDecode.lean:869-872) which
/// reads `badge := Badge.ofNatMasked (requireMsgReg msgRegs 0).val`.
///
/// Note: seLe4n's badge-via-MR\[0\] design deliberately differs from seL4's
/// capability-embedded badge. This allows callers to specify the badge
/// value per-signal rather than relying on capability badge alone.
#[inline]
pub fn notification_signal(ntfn: CPtr, badge: Badge) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new_const(1, 0, 0);
    invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [badge.into(), 0, 0, 0],
        syscall_id: SyscallId::NotificationSignal,
    })
}

/// Wait on a notification object. Blocks until signaled.
///
/// Returns the accumulated badge value from the notification object.
/// Lean: `notificationWait` (API.lean) — returns accumulated badge.
#[inline]
pub fn notification_wait(ntfn: CPtr) -> KernelResult<Badge> {
    let msg_info = MessageInfo::new_const(0, 0, 0);
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::NotificationWait,
    })?;
    Ok(resp.badge())
}

/// Atomically reply to a caller and then block waiting for a new message.
///
/// Replies to `reply_target` with the message payload, then blocks waiting
/// for a new message on the endpoint identified by `recv_cap`. This is the
/// standard server-loop primitive.
///
/// Lean: `endpointReplyRecv` (API.lean:566-576) — `decodeReplyRecvArgs`
/// (SyscallArgDecode.lean:881-884) reads MR\[0\] as `replyTarget : ThreadId`.
/// Message registers carry both the reply target ID (MR\[0\]) and the reply
/// data (MR\[1..3\]).
///
/// Returns the received badge and response registers from the new message.
#[inline]
pub fn endpoint_reply_recv(
    recv_cap: CPtr,
    reply_target: ThreadId,
    msg: &IpcMessage,
) -> KernelResult<(Badge, SyscallResponse)> {
    let msg_info = MessageInfo::new(msg.length, 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: recv_cap,
        msg_info,
        msg_regs: [reply_target.into(), msg.regs[1], msg.regs[2], msg.regs[3]],
        syscall_id: SyscallId::ReplyRecv,
    })?;
    Ok((resp.badge(), resp))
}
