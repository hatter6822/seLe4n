// SPDX-License-Identifier: GPL-3.0-or-later
//! Declassification — authorize and audit a cross-domain information downgrade.
//!
//! Lean: `SeLe4n/Kernel/InformationFlow/Declassification.lean` —
//! `declassifyObjectFromCore`, reached through `API.dispatchWithCapChecked`'s
//! `.declassify` arm.  Added in WS-SM SM8.C.9.

use sele4n_abi::{invoke_syscall, MessageInfo, SyscallRequest, SyscallResponse};
use sele4n_types::{Badge, CPtr, KernelResult, SyscallId};

/// Authorize and record a declassification into the object named by
/// `target_cap`.
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
/// Only the capability.  Neither security domain is a parameter: the source is
/// read off the subject the executing core is running and the destination off
/// the target object, so a caller cannot record a downgrade between two domains
/// it has nothing to do with.  Requires the **write** right (the flow direction
/// is subject → object).
///
/// # Errors
///
/// * `IllegalAuthority` / `InvalidCapability` — the capability does not carry
///   `write`, or does not name an object.
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
pub fn declassify(target_cap: CPtr) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: target_cap,
        msg_info: MessageInfo::new_const(0, 0, 0),
        msg_regs: [0, 0, 0, 0],
        syscall_id: SyscallId::Declassify,
    })
}

/// Signal a notification whose badge may cross a boundary the base lattice
/// denies — the **data-carrying** declassification.
///
/// # What it does
///
/// Everything the ordinary `notification_signal` does: the badge is written
/// into the notification, a waiting thread (or the notification's bound TCB) is
/// woken on its own home core, and the badge is delivered to it.  Lean:
/// `declassifiedSignal_delivers_badge` — the object store the transition
/// commits is the ordinary signal's, so this is a real delivery rather than the
/// simulated transfer `declassify` performs.
///
/// # What makes it a declassification
///
/// Two gated hops, not one.  The kernel authorizes the **signaller into the
/// notification** and the **notification onward into the resolved receiver**,
/// each against the base lattice first and the configured declassification
/// policy second, and appends one attributed audit entry per hop that turned
/// out to be a downgrade.  A hop the base lattice already permits is an
/// ordinary flow and records nothing, so a deployment with no declassification
/// policy configured gets exactly `notification_signal`'s behaviour and an
/// audit trail that cannot grow (Lean:
/// `declassifiedSignal_default_policy_eq_signal`).
///
/// Gating the second hop is not optional decoration.  A signaller authorized
/// into the notification but not onward to the thread that will receive the
/// badge is **refused**, with its own discriminant — because a receiver being
/// inside the delivery's effect footprint says where the badge lands, not that
/// sending it there is permitted (Lean: `footprint_does_not_authorize`).
///
/// # Arguments
///
/// The notification capability and the badge.  No security domain is a
/// parameter, for the reason `declassify` takes none: the source is read off
/// the subject the executing core is running, and the two destinations off the
/// notification and its resolved receiver.  Requires the **write** right — the
/// same authority the ordinary signal requires, which the declassification
/// gates sit on top of rather than replace.
///
/// # Errors
///
/// * `IllegalAuthority` / `InvalidCapability` — the capability does not carry
///   `write`, or does not name an object.
/// * `IllegalState` — the executing core is running no thread, so there is no
///   subject to attribute the downgrade to.
/// * `DeclassificationDenied` — the **first** hop (signaller → notification)
///   is authorized by neither policy.  Also what an unconfigured deployment
///   gets whenever the base lattice denies that hop.
/// * `DeclassificationDeniedAtReceiver` — the **second** hop (notification →
///   resolved receiver) is authorized by neither policy.  A distinct
///   discriminant on purpose: an unauthorized caller and an authorized caller
///   aimed at an unauthorized sink call for opposite responses.
/// * `AuditLogCapacityExceeded` — the audit trail cannot hold this delivery's
///   records.  The badge was **not delivered**: a downgrade the kernel cannot
///   record is refused rather than performed unaudited (Lean:
///   `declassifiedSignal_never_unaudited`).
#[inline]
pub fn declassify_signal(notification_cap: CPtr, badge: Badge) -> KernelResult<SyscallResponse> {
    invoke_syscall(SyscallRequest {
        cap_addr: notification_cap,
        // The ordinary signal's frame exactly (`decodeNotificationSignalArgs`
        // reads MR[0]), because the declassifying variant reuses that decoder.
        msg_info: MessageInfo::new_const(1, 0, 0),
        msg_regs: [badge.into(), 0, 0, 0],
        syscall_id: SyscallId::DeclassifySignal,
    })
}
