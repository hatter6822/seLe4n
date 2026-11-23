// SPDX-License-Identifier: GPL-3.0-or-later
//! Declassification — authorize and audit a cross-domain information downgrade.
//!
//! Lean: `SeLe4n/Kernel/InformationFlow/Declassification.lean` —
//! `declassifyObjectFromCore`, reached through `API.dispatchWithCapChecked`'s
//! `.declassify` arm.  Added in WS-SM SM8.C.9.
//!
//! Both calls are invocations of the **audit-trail capability** (WS-SX SX6.7),
//! so no message label selects an operation on an endpoint or a notification:
//! the object released into is the message's extra capability 0
//! (`caps_or_badges[0]` of the caller's IPC buffer), as seL4 passes an
//! argument capability.

use sele4n_abi::{invoke_syscall, IpcBuffer, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{CPtr, KernelResult, SyscallId};

/// Authorize and record a declassification into the object named by
/// `target_cap`, invoked on `audit_cap`.
///
/// # What it does
///
/// The kernel checks that the flow from the *calling thread's* security domain
/// into the *target object's* domain is one the base lattice denies and the
/// configured declassification policy permits, and — if so — appends one
/// attributed entry to the kernel's declassification audit trail.
///
/// # What it does not do
///
/// It moves no data.  Lean: `authorizeDeclassificationOnCore_frame` — the only
/// field the transition writes is `SystemState.declassificationAuditLog`.  This
/// is the MLS "trusted downgrader" primitive: the kernel is the arbiter of
/// which downgrades its policy permits and the durable trail is the evidence;
/// the transfer itself is whatever the caller does next.
///
/// # Arguments
///
/// The audit-trail capability (invoked, with its **write** right: recording a
/// downgrade appends to the trail) and the target's capability, written to
/// `buf.caps_or_badges[0]` as extra capability 0.  Neither security domain is
/// a parameter: the source is read off the subject the executing core is
/// running and the destination off the target object, so a caller cannot
/// record a downgrade between two domains it has nothing to do with.  The
/// target capability needs the **write** right too (the flow direction is
/// subject → object).
///
/// # Errors
///
/// * `InvalidCapability` (number 0) — `audit_cap` is not the audit-trail
///   capability.
/// * `IllegalAuthority` — `audit_cap` or `target_cap` does not carry `write`.
/// * `TruncatedMessage` — no extra capability was named.
/// * `InvalidCapability` (number 1) — `target_cap` names an empty slot or no
///   object.
/// * `IllegalState` — the executing core is running no thread, so there is no
///   subject to attribute the downgrade to.
/// * `ObjectNotFound` — the capability names an object that is not in the
///   store, so there is no domain to resolve the destination from.
/// * `FlowDenied` — the base policy *already* permits this flow, so it is not a
///   declassification; use the ordinary operation.
/// * `DeclassificationDenied` — the declassification policy does not authorize
///   this domain pair.  Also what an unconfigured deployment gets on every
///   call: the policy defaults to deny-all.
/// * `AuditLogCapacityExceeded` — the audit trail is full.  The downgrade was
///   **refused rather than performed unrecorded**; drain the trail.
#[inline]
pub fn declassify(
    audit_cap: CPtr,
    target_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    buf.caps_or_badges[0] = target_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: audit_cap,
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::Declassify,
        reply_cap: CPtr::NULL,
    })
}

/// Signal a notification whose badge may cross a boundary the base lattice
/// denies — the **data-carrying** declassification.
///
/// # What it does
///
/// Everything the ordinary `notification_signal` does: the badge — the one
/// minted into `notification_cap`, zero for an unbadged capability, never a
/// caller-chosen word — is ORed into the notification, a waiting thread (or the notification's bound TCB) is
/// woken on its own home core, and the badge is delivered to it.  Lean:
/// `declassifiedSignal_delivers_badge` — the object store the transition
/// commits is the ordinary signal's, so this is a real delivery rather than the
/// simulated transfer `declassify` performs.
///
/// # What makes it a declassification
///
/// One gated hop.  The kernel authorizes the **signaller into the
/// notification** against the base lattice first and the configured
/// declassification policy second, and appends one attributed audit entry when
/// that hop turned out to be a downgrade.  A hop the base lattice already
/// permits is an ordinary flow and records nothing, so a deployment with no
/// declassification policy configured gets exactly `notification_signal`'s
/// behaviour and an audit trail that cannot grow (Lean:
/// `declassifiedSignal_default_policy_eq_signal`).
///
/// The onward delivery to the thread that receives the badge needs no gate of
/// its own: a thread waits on, or is bound to, a notification only at the
/// notification's own label (the two-way wait and bind gates, and the boot's
/// label check), so that flow is the identity flow (Lean:
/// `declassifiedSignalReceiver_flow_ordinary_of_coherent`).
///
/// # Arguments
///
/// The audit-trail capability (invoked, with its **write** right) and the
/// notification capability, written to `buf.caps_or_badges[0]` as extra
/// capability 0.  The badge is the notification capability's own (Lean:
/// `Capability.signalBadge`,
/// `dispatchWithCapChecked_declassifySignal_badge_of_cap`): what crosses the
/// label boundary is the identity the capability was minted with, so a
/// declassifying signal can no more forge another sender's badge bits than an
/// ordinary one.  No security domain is a parameter, for the reason `declassify` takes none: the source is read off
/// the subject the executing core is running, and the destination off the
/// notification.  Requires the **write** right — the
/// same authority the ordinary signal requires, which the declassification
/// gates sit on top of rather than replace.
///
/// # Errors
///
/// * `InvalidCapability` (number 0) — `audit_cap` is not the audit-trail
///   capability.
/// * `IllegalAuthority` — `audit_cap` or `notification_cap` does not carry
///   `write`.
/// * `TruncatedMessage` — no extra capability was named.
/// * `InvalidCapability` (number 1) — `notification_cap` names an empty slot
///   or anything but a notification.
/// * `IllegalState` — the executing core is running no thread, so there is no
///   subject to attribute the downgrade to.
/// * `DeclassificationDenied` — the signaller's hop into the notification is
///   authorized by neither policy.  Also what an unconfigured deployment gets
///   whenever the base lattice denies that hop.  The onward delivery to the
///   receiver is never refused: only a thread of the notification's own label
///   can wait on it or be bound to it.
/// * `AuditLogCapacityExceeded` — the audit trail cannot hold this delivery's
///   record.  The badge was **not delivered**: a downgrade the kernel cannot
///   record is refused rather than performed unaudited (Lean:
///   `declassifiedSignal_never_unaudited`).
#[inline]
pub fn declassify_signal(
    audit_cap: CPtr,
    notification_cap: CPtr,
    buf: &mut IpcBuffer,
) -> KernelResult<SyscallResponse> {
    buf.caps_or_badges[0] = notification_cap.raw();
    invoke_syscall(SyscallRequest {
        cap_addr: audit_cap,
        // No message register is read: the badge is the notification
        // capability's.  One extra capability, the notification.
        msg_info: MessageInfo::new_const(0, 1, 0),
        msg_regs: [0; 4],
        syscall_id: SyscallId::DeclassifySignal,
        reply_cap: CPtr::NULL,
    })
}
