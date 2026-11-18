// SPDX-License-Identifier: GPL-3.0-or-later
//! IPC operations — 8 syscall wrappers.
//!
//! - `endpoint_send` / `endpoint_receive` / `endpoint_receive_with_reply`
//! - `endpoint_call` / `endpoint_reply`
//! - `notification_signal` / `notification_wait`
//! - `endpoint_reply_recv` (compound: reply + blocking receive)
//!
//! A receive's reply capability rides the reply register (x6, seL4-MCS
//! `replyRegister`, [`SyscallRequest::reply_cap`]), never a message word: the
//! message registers carry the message whole.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — `dispatchSyscallChecked` → `dispatchWithCapChecked`.

use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{Badge, CPtr, KernelResult, SyscallId};

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
    /// AF6-E: Private — number of valid registers (0..=4).
    /// Use `length()` to read, `new_with_length()` or `push()` to set.
    length: u8,
    /// User-defined label.
    pub label: u64,
}

impl Default for IpcMessage {
    fn default() -> Self {
        Self::empty(0)
    }
}

impl IpcMessage {
    /// Create an empty message with the given label.
    pub const fn empty(label: u64) -> Self {
        Self {
            regs: [0; 4],
            length: 0,
            label,
        }
    }

    /// Create an empty message with the given label.
    /// Alias for [`empty`] — preserves backward compatibility.
    pub const fn new(label: u64) -> Self {
        Self::empty(label)
    }

    /// AF6-E: Create a new IPC message with validated length.
    ///
    /// Returns `None` if `length > 4` (exceeds ARM64 inline register capacity).
    pub const fn new_with_length(regs: [u64; 4], length: u8, label: u64) -> Option<Self> {
        if length > 4 {
            return None;
        }
        Some(Self {
            regs,
            length,
            label,
        })
    }

    /// Returns the number of valid registers (0..=4).
    pub const fn length(&self) -> u8 {
        self.length
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
    let msg_info = MessageInfo::new(msg.length(), 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    invoke_syscall(SyscallRequest {
        cap_addr: dest,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Send,
        reply_cap: CPtr::NULL,
    })
}

/// Receive a message from an endpoint. Blocks until a message arrives.
///
/// Lean: `apiEndpointReceive` (API.lean) — requires `.read` right.
///
/// Returns the received badge and response registers.  WS-RA: these are
/// **real** — the badge from `x0`, the delivered inline message registers
/// from `x2`-`x5` with their count in the returned `MessageInfo` — staged
/// by the kernel's `.receive` arm (`stageDeliveredMessage`).  Before the
/// flip the kernel wrote no register back and this function returned the
/// caller's own values.
#[inline]
pub fn endpoint_receive(src: CPtr) -> KernelResult<(Badge, SyscallResponse)> {
    // V1-D: new_const() is compile-time validated — infallible for valid constants.
    // Plain receive: no reply object supplied, so the syscall is seL4's `Wait`
    // (`handleRecv` with `canReply` false), which reads no reply register; on
    // an endpoint the kernel selects the receive (`receiveOperation`).  A `Recv`
    // would look its reply capability up at x6 and fault on the null one.  Use
    // `endpoint_receive_with_reply` to accept Call IPC.
    let msg_info = MessageInfo::new_const(0, 0, 0);
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: src,
        msg_info,
        msg_regs: [0; 4],
        // The operation whose syscall is `Wait` (`SyscallId::syscall`).
        syscall_id: SyscallId::NotificationWait,
        reply_cap: CPtr::NULL,
    })?;
    Ok((resp.badge(), resp))
}

/// WS-SM SM6.D (faithful seL4-MCS): receive a message from an endpoint, supplying
/// a Reply object capability so a rendezvousing `Call` caller can be answered.
///
/// x6 = the server-supplied reply capability pointer (seL4-MCS
/// `replyRegister`; the syscall is `Recv`, which looks it up).  When a
/// queued `Call` rendezvouses, the kernel links it to this reply object
/// (`reply.caller`), so the server's subsequent `endpoint_reply` /
/// `endpoint_reply_recv` resolves authority through the reply object.  A `Send`
/// source ignores the reply cap.  This is the Call-capable analogue of
/// [`endpoint_receive`] (which omits the reply object and therefore cannot accept
/// Call IPC under the reply-object ABI).
///
/// Lean: the `.receive` dispatch arm (`resolveRecvReplyId` + `linkReceivedCaller`).
#[inline]
pub fn endpoint_receive_with_reply(
    recv_cap: CPtr,
    reply_cap: CPtr,
) -> KernelResult<(Badge, SyscallResponse)> {
    let msg_info = MessageInfo::new_const(0, 0, 0);
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: recv_cap,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::Receive,
        reply_cap,
    })?;
    Ok((resp.badge(), resp))
}

/// Call an endpoint (send + blocking receive in one syscall).
///
/// Lean: `apiEndpointCall` (API.lean) — requires `.write` right.
///
/// PR #866 round-3 review: returns `(Badge, SyscallResponse)` like its
/// `.message`-shaped siblings `endpoint_receive` / `endpoint_reply_recv`
/// — a call's reply-delivered frame carries the badge in `x0` exactly as
/// a receive's does (the kernel stages `.call`'s frame through the reply
/// path, plan §3.5), and the bare `SyscallResponse` return left the
/// shape-to-signature contract unenforceable for one of its three
/// members.
#[inline]
pub fn endpoint_call(dest: CPtr, msg: &IpcMessage) -> KernelResult<(Badge, SyscallResponse)> {
    let msg_info = MessageInfo::new(msg.length(), 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: dest,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Call,
        reply_cap: CPtr::NULL,
    })?;
    Ok((resp.badge(), resp))
}

/// Reply to a caller (one-shot reply capability).
///
/// Lean: `apiEndpointReply` (API.lean) — requires `.write` right.
#[inline]
pub fn endpoint_reply(reply_cap: CPtr, msg: &IpcMessage) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new(msg.length(), 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    invoke_syscall(SyscallRequest {
        cap_addr: reply_cap,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::Reply,
        reply_cap: CPtr::NULL,
    })
}

/// Signal a notification object (badge OR accumulation), as seL4's
/// `seL4_Signal`.
///
/// The badge ORed into the notification's word is the one **minted into the
/// capability** `ntfn` names (`cspace_mint`), and zero for an unbadged
/// capability — seL4's `sendSignal(ntfn, capNtfnBadge(cap))`.  The caller
/// cannot choose it: the kernel reads no message register, so a holder of a
/// notification capability can never set badge bits its capability was not
/// minted with (another client's, or an interrupt handler's).  The call sends
/// an empty message; the kernel checks no length, as seL4's does not.
///
/// Lean: the `.notificationSignal` arm of `dispatchWithCapChecked`
/// (API.lean), which ORs in `Capability.signalBadge`;
/// `dispatchWithCapChecked_notificationSignal_badge_of_cap` proves no word of the
/// decoded message reaches it.  Requires the **write** right.
#[inline]
pub fn notification_signal(ntfn: CPtr) -> KernelResult<SyscallResponse> {
    let msg_info = MessageInfo::new_const(0, 0, 0);
    invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::NotificationSignal,
        reply_cap: CPtr::NULL,
    })
}

/// Wait on a notification object. Blocks until signaled.
///
/// Returns the accumulated badge value from the notification object —
/// **really** (WS-RA closed SM9.C.0): the kernel's `.notificationWait`
/// arm stages the consumed badge into `x0` (`returnFrameOfBadge`), and
/// `badge()` reads `x0`.  Before the flip this doc claimed a badge the
/// ABI never delivered — the kernel wrote no register back, and the old
/// `badge()` read `x1`, handing back the caller's own msgInfo word.
/// Lean: `notificationWait` (API.lean).
#[inline]
pub fn notification_wait(ntfn: CPtr) -> KernelResult<Badge> {
    let msg_info = MessageInfo::new_const(0, 0, 0);
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: ntfn,
        msg_info,
        msg_regs: [0; 4],
        syscall_id: SyscallId::NotificationWait,
        reply_cap: CPtr::NULL,
    })?;
    Ok(resp.badge())
}

/// Atomically reply to a caller and then block waiting for a new message.
///
/// Replies to the previous caller (the reply object's recorded `caller`, named
/// by `reply_cap`) with the message payload, then blocks waiting for a new
/// message on the endpoint identified by `recv_cap` — re-linking the same reply
/// object to the next caller. This is the standard server-loop primitive.
///
/// Lean: the `.replyRecv` arm in `API.lean` (`resolveReplyRecvReply`): seL4-MCS
/// `SysReplyRecv` names the reply capability in the reply register (x6,
/// `replyRegister`), so the message registers carry the reply whole, MR\[0\]
/// on, and the kernel delivers it as a send delivers its message.  A reply
/// capability with no caller skips the reply and receives.
///
/// Returns the received badge and response registers from the new message.
#[inline]
pub fn endpoint_reply_recv(
    recv_cap: CPtr,
    reply_cap: CPtr,
    msg: &IpcMessage,
) -> KernelResult<(Badge, SyscallResponse)> {
    let msg_info = MessageInfo::new(msg.length(), 0, msg.label)
        .map_err(|_| sele4n_types::KernelError::InvalidMessageInfo)?;
    let resp = invoke_syscall(SyscallRequest {
        cap_addr: recv_cap,
        msg_info,
        msg_regs: msg.regs,
        syscall_id: SyscallId::ReplyRecv,
        reply_cap,
    })?;
    Ok((resp.badge(), resp))
}
