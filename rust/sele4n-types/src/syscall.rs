// SPDX-License-Identifier: GPL-3.0-or-later
//! Syscall identifier enumeration — 1:1 mapping from `SeLe4n.Model.SyscallId`.
//!
//! Lean source: `SeLe4n/Model/Object/Types.lean` lines 601–710.

use crate::rights::AccessRight;

/// Syscall identifier. 45 variants matching the Lean `SyscallId` inductive.
///
/// The `toNat` encoding from Lean is reflected in the `#[repr(u64)]` discriminants.
/// Numbers 8, the retired in-place `lifecycleRetype`, 34, the retired
/// `tcbSetFaultHandler`, and 37, the retired untyped reset, are reserved: no
/// variant carries them and they are never reassigned (see
/// [`SyscallId::RETIRED`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u64)]
pub enum SyscallId {
    // IPC
    Send = 0,
    Receive = 1,
    Call = 2,
    Reply = 3,
    // CSpace
    CSpaceMint = 4,
    CSpaceCopy = 5,
    CSpaceMove = 6,
    CSpaceDelete = 7,
    // 8: retired (WS-ZA ZA5.4 part 14, the in-place retype); reserved.
    // VSpace
    VSpaceMap = 9,
    VSpaceUnmap = 10,
    // Service (WS-Q1-D)
    ServiceRegister = 11,
    ServiceRevoke = 12,
    ServiceQuery = 13,
    // Notification (V2-A)
    NotificationSignal = 14,
    NotificationWait = 15,
    // Compound IPC (V2-C)
    ReplyRecv = 16,
    // SchedContext (WS-Z Z5-J)
    SchedContextConfigure = 17,
    SchedContextBind = 18,
    SchedContextUnbind = 19,
    // Thread lifecycle (WS-AB D1)
    TcbSuspend = 20,
    TcbResume = 21,
    // Priority management (WS-AB D2)
    TcbSetPriority = 22,
    TcbSetMCPriority = 23,
    // IPC buffer configuration (WS-AB D3)
    TcbSetIPCBuffer = 24,
    // CPU-affinity configuration (WS-SM SM5.H.4)
    TcbSetAffinity = 25,
    // Notification binding (WS-SM SM6.B)
    TcbBindNotification = 26,
    TcbUnbindNotification = 27,
    // Reply-cap mint (WS-SM SM6.D / PR #822 Phase H): derive a `.replyCap` from an
    // `.object` cap to a retyped Reply object.
    MintReplyCap = 28,
    // Instruction/data unification of one mapped page (WS-SM SM7.D): seLe4n's
    // equivalent of seL4's `Page_Unify_Instruction`.  Publishes freshly written
    // code — an instruction fetch reads at the Point of Unification, so stores
    // that are still only in the data cache must be cleaned there first.
    VSpaceUnifyInstruction = 29,
    // Declassification (WS-SM SM8.C.9): authorize and audit a cross-domain
    // downgrade.  The one syscall whose authority is a *policy* rather than a
    // capability alone — the base lattice must deny the flow and the configured
    // declassification policy must permit it — and whose entire state effect is
    // one entry appended to the kernel's declassification audit trail.
    Declassify = 30,
    // Audit-trail access (WS-SM SM9.A.6).  Two syscalls rather than one with a
    // mode operand, so authority stays per-operation: `required_right` is keyed
    // on the `SyscallId`, and a monitoring deployment can therefore hand out a
    // read-only audit capability that provably cannot drain.
    //
    // Both are gated first on the capability *targeting* the audit trail
    // (`CapTarget::AuditTrail` in the Lean model), not merely on carrying the
    // right: `syscallLookupCap` never constrains a capability's target, so a
    // rights-only gate would be reachable by any thread holding any readable
    // capability.
    AuditRead = 31,
    AuditDrain = 32,
    // Data-carrying declassification (WS-SM SM9.C.8): signal a notification
    // whose badge may cross a boundary the base lattice denies.
    //
    // Unlike `Declassify`, which authorizes a downgrade and records it without
    // moving any user data, this one performs the real delivery — the badge
    // lands where an ordinary `NotificationSignal` would put it — and gates
    // **two** hops: the signaller into the notification, and the notification
    // onward into the *resolved receiver*.  An authorized signaller aimed at a
    // sink the policy never authorized is refused at the second, with its own
    // discriminant (`DeclassificationDeniedAtReceiver`), because a monitor
    // reading a bare "denied" cannot tell an unauthorized caller from an
    // authorized caller aimed at an unauthorized sink.
    DeclassifySignal = 33,
    // 34: retired (WS-SX SX6.5, `tcbSetFaultHandler`: seL4-MCS installs the
    // fault endpoint in `TCB_SetSpace`, extra capability 0); reserved.
    /// WS-RR RR8.16 (`v0.35.190`): revoke every capability derived from the one
    /// in the named slot — seL4's `seL4_CNode_Revoke`.
    ///
    /// The source slot itself **survives**: revocation destroys a capability's
    /// derivations, not the capability, which is what distinguishes it from
    /// `CSpaceDelete`.  It takes the
    /// delete's argument layout (one message register naming the slot), since
    /// both name one slot of the invoked CNode.
    CspaceRevoke = 35,
    /// WS-BP BP7.1 (`v0.36.5`): carve a frame out of an untyped the caller
    /// holds — seL4's `seL4_Untyped_Retype` at the frame type.
    ///
    /// Invoked on the **untyped** capability (`Retype` right).  `x2` is the
    /// object type (only the frame tag, 8, is carved), `x3` the object id the
    /// frame takes, `x4` the address of a writable capability to the
    /// destination CNode and `x5` the empty slot the new frame capability goes
    /// to.  The frame is the page at the untyped's watermark, a device untyped
    /// yields a device frame, and a RAM page is zeroed before the capability
    /// exists.  The only way a frame — and so mappable memory — comes to exist.
    UntypedRetype = 36,
    // 37: retired (WS-SX SX7.1, the untyped reset); reserved.
    /// WS-BP BP7.1 (`v0.36.11`): set a suspended thread's CSpace and VSpace
    /// roots — seL4's `TCB_SetSpace`.
    ///
    /// Invoked on the **target TCB** capability (`Write` right).  x2 = the
    /// address, in the caller's CSpace, of a capability to the new CSpace root
    /// (a CNode, held with `Grant` and `Write`); x3 = the address of a
    /// capability to the new VSpace root (held with `Write`).  Refused unless
    /// the target is suspended.
    TcbSetSpace = 38,
    /// WS-BP BP7.1 (`v0.36.12`): install an intermediate page table — seL4's
    /// `seL4_ARM_PageTable_Map`.
    ///
    /// Invoked on the **page-table** capability (`Write` right).  x2 = the
    /// address, in the caller's CSpace, of a capability to the address space
    /// (held with `Write`); x3 = a virtual address whose walk the table serves.
    /// The table is installed at the shallowest level that walk is missing.
    PageTableMap = 39,
    /// WS-BP BP7.1 (`v0.36.12`): take an intermediate page table out of the
    /// address space it is installed in — seL4's `seL4_ARM_PageTable_Unmap`.
    /// Invoked on the page-table capability (`Write` right), with no message
    /// registers; refused while anything still translates through the table.
    PageTableUnmap = 40,
    /// WS-ZA ZA4.3: give up the rest of the caller's allotment — seL4's
    /// `seL4_Yield` under MCS.  A thread bound to a scheduling context forfeits
    /// its remaining budget until the next refill; an unbound thread ends its
    /// time slice and goes behind the threads of its priority.  Invokes no
    /// capability: x0 and the message registers are ignored.
    Yield = 41,
    /// WS-ZA ZA6.9: read and reset a scheduling context's consumed time —
    /// seL4's `seL4_SchedContext_Consumed`.  Invoked on the scheduling-context
    /// capability (`Write` right), with no message registers; the consumed time
    /// returns in the first message register (x2) with a one-register
    /// `MessageInfo` in x1.
    SchedContextConsumed = 42,
    /// WS-ZA ZA6.29: yield to the thread bound to a scheduling context —
    /// seL4's `seL4_SchedContext_YieldTo`.  Invoked on the scheduling-context
    /// capability (`Write` right), with no message registers; the consumed time
    /// returns in the first message register (x2) with a one-register
    /// `MessageInfo` in x1, written when the call returns or, when the caller
    /// yielded its core to the target, when the caller next runs.
    SchedContextYieldTo = 43,
    /// WS-ZA ZA6.32: acknowledge an interrupt line — seL4's
    /// `seL4_IRQHandler_Ack`.  Invoked on the interrupt-handler capability
    /// (`Write` right), with no message registers: the line the capability
    /// names, masked since the kernel delivered it, is unmasked at the
    /// interrupt controller.  Returns no value.
    IrqHandlerAck = 44,
    /// WS-ZA ZA6.32: issue an interrupt-handler capability — seL4's
    /// `seL4_IRQControl_Get`.  Invoked on the interrupt-control capability
    /// (`Write` right): x2 the line, x3 the address of the CNode the handler
    /// capability is issued into, x4 the slot in it.  Refused for a line that
    /// is no device line of the board or that a handler already holds.
    /// Returns no value.
    IrqControlGet = 45,
    /// WS-ZA ZA6.32: bind a notification to an interrupt line — seL4's
    /// `seL4_IRQHandler_SetNotification`.  Invoked on the interrupt-handler
    /// capability (`Write` right): x2 the address of a notification capability
    /// carrying the send right, copied into the line's node slot in place of
    /// the one there.  Returns no value.
    IrqHandlerSetNotification = 46,
    /// WS-ZA ZA6.32: unbind an interrupt line's notification — seL4's
    /// `seL4_IRQHandler_Clear`.  Invoked on the interrupt-handler capability
    /// (`Write` right), with no message registers.  Returns no value.
    IrqHandlerClear = 47,
}

impl SyscallId {
    /// Total number of modeled syscalls (variants).
    pub const COUNT: usize = 45;

    /// One past the largest syscall number: every number below it is a
    /// variant's or a retired one.
    pub const ENCODING_BOUND: u64 = 48;

    /// Retired syscall numbers, reserved and never reassigned.  `8` was the
    /// in-place `lifecycleRetype`; since WS-ZA ZA5.4 part 14 every object is
    /// carved from an untyped by `UntypedRetype` (36), as in seL4.  `34` was
    /// `tcbSetFaultHandler`; since WS-SX SX6.5 the fault endpoint is
    /// `TcbSetSpace`'s (38) extra capability 0, as in seL4-MCS.  `37` was
    /// the untyped reset; seL4 resets inside `Untyped_Retype`, as the carve
    /// does (WS-SX SX7.1).
    pub const RETIRED: [u64; 3] = [8, 34, 37];

    /// Convert from a raw `u64` value. Returns `None` for out-of-range.
    /// Lean: `SyscallId.ofNat?`
    pub const fn from_u64(v: u64) -> Option<Self> {
        match v {
            0 => Some(Self::Send),
            1 => Some(Self::Receive),
            2 => Some(Self::Call),
            3 => Some(Self::Reply),
            4 => Some(Self::CSpaceMint),
            5 => Some(Self::CSpaceCopy),
            6 => Some(Self::CSpaceMove),
            7 => Some(Self::CSpaceDelete),
            9 => Some(Self::VSpaceMap),
            10 => Some(Self::VSpaceUnmap),
            11 => Some(Self::ServiceRegister),
            12 => Some(Self::ServiceRevoke),
            13 => Some(Self::ServiceQuery),
            14 => Some(Self::NotificationSignal),
            15 => Some(Self::NotificationWait),
            16 => Some(Self::ReplyRecv),
            17 => Some(Self::SchedContextConfigure),
            18 => Some(Self::SchedContextBind),
            19 => Some(Self::SchedContextUnbind),
            20 => Some(Self::TcbSuspend),
            21 => Some(Self::TcbResume),
            22 => Some(Self::TcbSetPriority),
            23 => Some(Self::TcbSetMCPriority),
            24 => Some(Self::TcbSetIPCBuffer),
            25 => Some(Self::TcbSetAffinity),
            26 => Some(Self::TcbBindNotification),
            27 => Some(Self::TcbUnbindNotification),
            28 => Some(Self::MintReplyCap),
            29 => Some(Self::VSpaceUnifyInstruction),
            30 => Some(Self::Declassify),
            31 => Some(Self::AuditRead),
            32 => Some(Self::AuditDrain),
            33 => Some(Self::DeclassifySignal),
            35 => Some(Self::CspaceRevoke),
            36 => Some(Self::UntypedRetype),
            38 => Some(Self::TcbSetSpace),
            39 => Some(Self::PageTableMap),
            40 => Some(Self::PageTableUnmap),
            41 => Some(Self::Yield),
            42 => Some(Self::SchedContextConsumed),
            43 => Some(Self::SchedContextYieldTo),
            44 => Some(Self::IrqHandlerAck),
            45 => Some(Self::IrqControlGet),
            46 => Some(Self::IrqHandlerSetNotification),
            47 => Some(Self::IrqHandlerClear),
            _ => None,
        }
    }

    /// Convert to raw `u64`. Lean: `SyscallId.toNat`.
    #[inline]
    pub const fn to_u64(self) -> u64 {
        self as u64
    }

    /// **The invocation label that selects this operation** on a capability
    /// of the type it takes (seL4's `invocation_label`, aarch64 with MCS and
    /// SMP; the model-only operations after seL4's last, 56).  `None` for the
    /// operations the capability's type selects (the IPC operations) and the
    /// yield.  Lean: `SyscallId.label?`.
    pub const fn label(self) -> Option<u64> {
        match self {
            Self::UntypedRetype => Some(1),
            Self::TcbSetPriority => Some(6),
            Self::TcbSetMCPriority => Some(7),
            Self::TcbSetIPCBuffer => Some(10),
            Self::TcbSetSpace => Some(11),
            Self::TcbSuspend => Some(12),
            Self::TcbResume => Some(13),
            Self::TcbBindNotification => Some(14),
            Self::TcbUnbindNotification => Some(15),
            Self::CspaceRevoke => Some(18),
            Self::CSpaceDelete => Some(19),
            Self::CSpaceCopy => Some(21),
            Self::CSpaceMint => Some(22),
            Self::CSpaceMove => Some(23),
            Self::IrqControlGet => Some(26),
            Self::IrqHandlerAck => Some(27),
            Self::IrqHandlerSetNotification => Some(28),
            Self::IrqHandlerClear => Some(29),
            Self::SchedContextConfigure => Some(33),
            Self::SchedContextBind => Some(34),
            Self::SchedContextUnbind => Some(35),
            Self::SchedContextConsumed => Some(37),
            Self::SchedContextYieldTo => Some(38),
            Self::VSpaceUnifyInstruction => Some(42),
            Self::PageTableMap => Some(44),
            Self::PageTableUnmap => Some(45),
            Self::VSpaceMap => Some(46),
            Self::VSpaceUnmap => Some(47),
            Self::ServiceRegister => Some(57),
            Self::ServiceRevoke => Some(58),
            Self::ServiceQuery => Some(59),
            Self::MintReplyCap => Some(60),
            Self::Declassify => Some(61),
            Self::AuditRead => Some(62),
            Self::AuditDrain => Some(63),
            Self::DeclassifySignal => Some(64),
            Self::TcbSetAffinity => Some(66),
            Self::Send
            | Self::Receive
            | Self::Call
            | Self::Reply
            | Self::NotificationSignal
            | Self::NotificationWait
            | Self::ReplyRecv
            | Self::Yield => None,
        }
    }

    /// **The syscall a wrapper issues for this operation**: an invocation is
    /// a `Call` (its result and its error come back, as libsel4's invocation
    /// stubs issue it); a send, a signal and a reply through a reply
    /// capability are a `Send`; a wait is a `Wait`, a receive a `Recv`.
    pub const fn syscall(self) -> Syscall {
        match self {
            Self::Send | Self::Reply | Self::NotificationSignal => Syscall::Send,
            Self::Receive => Syscall::Recv,
            Self::NotificationWait => Syscall::Wait,
            Self::ReplyRecv => Syscall::ReplyRecv,
            Self::Yield => Syscall::Yield,
            _ => Syscall::Call,
        }
    }

    /// Required access right for this syscall.
    ///
    /// Matches the `SyscallGate.requiredRight` usage in `SeLe4n/Kernel/API.lean`.
    pub const fn required_right(self) -> AccessRight {
        match self {
            Self::Send | Self::Call | Self::Reply => AccessRight::Write,
            Self::Receive => AccessRight::Read,
            Self::CSpaceMint | Self::CSpaceCopy | Self::CSpaceMove => AccessRight::Grant,
            Self::CSpaceDelete => AccessRight::Write,
            // WS-RR RR8.16: revocation writes the CNodes holding the derived
            // capabilities, so it is a write on the invoked CNode exactly as the
            // delete is.  Not `Grant`: grant authorises *creating* a derivation
            // (mint/copy/move), and destroying one is not that authority.
            Self::CspaceRevoke => AccessRight::Write,
            // WS-BP BP7.1: a carve is a retype of the untyped's memory.
            Self::UntypedRetype => AccessRight::Retype,
            // WS-BP BP7.1: setting a thread's roots configures the thread.
            Self::TcbSetSpace => AccessRight::Write,
            // WS-BP BP7.1: installing or removing a table changes the table.
            Self::PageTableMap | Self::PageTableUnmap => AccessRight::Write,
            Self::VSpaceMap | Self::VSpaceUnmap => AccessRight::Write,
            Self::ServiceRegister | Self::ServiceRevoke => AccessRight::Write,
            Self::ServiceQuery => AccessRight::Read,
            Self::NotificationSignal => AccessRight::Write,
            Self::NotificationWait => AccessRight::Read,
            Self::ReplyRecv => AccessRight::Read,
            Self::SchedContextConfigure | Self::SchedContextBind | Self::SchedContextUnbind => {
                AccessRight::Write
            }
            Self::TcbSuspend | Self::TcbResume => AccessRight::Write,
            Self::TcbSetPriority | Self::TcbSetMCPriority => AccessRight::Write,
            Self::TcbSetIPCBuffer => AccessRight::Write,
            Self::TcbSetAffinity => AccessRight::Write,
            Self::TcbBindNotification | Self::TcbUnbindNotification => AccessRight::Write,
            // PR #822 Phase H: deriving a reply cap requires grant authority on the
            // source object cap (matches the cspaceMint/Copy/Move family).
            Self::MintReplyCap => AccessRight::Grant,
            // WS-SM SM7.D: least-privilege reading of seL4's frame-cap authority —
            // the operation publishes the caller's own stores, so the subject
            // that needs it could by construction write the page.
            Self::VSpaceUnifyInstruction => AccessRight::Write,
            // WS-SM SM8.C.9: declassifying releases the caller's information
            // *into* the target object's domain, so the flow direction is
            // subject -> object and the authority is the write right.
            Self::Declassify => AccessRight::Write,
            // WS-SM SM9.A.10: the reader needs the read right and the drain the
            // write right, on an audit capability.  The split is what lets a
            // deployment mint a reader that cannot remove evidence.
            Self::AuditRead => AccessRight::Read,
            Self::AuditDrain => AccessRight::Write,
            // WS-SM SM9.C.8: the data-carrying declassification signals a
            // notification, so its authority is the same write right the
            // ordinary signal requires.  The declassification is an
            // *additional* gate on top of that authority, never a substitute:
            // a read-only notification cap cannot signal, and so cannot
            // declassify through a signal either, whatever the policy says.
            Self::DeclassifySignal => AccessRight::Write,
            // WS-ZA ZA4.3: yield invokes no capability, so no right is ever
            // checked for it (the kernel dispatches it before the capability
            // gate).  `Read` is the value the Lean `syscallRequiredRight` gives.
            Self::Yield => AccessRight::Read,
            // WS-ZA ZA6.9: the Consumed invocation resets the context's consumed
            // time, so it carries the write right Bind and Unbind carry.
            Self::SchedContextConsumed => AccessRight::Write,
            // WS-ZA ZA6.29: the yieldTo invocation resets the context's consumed
            // time and requeues its thread, so it carries the same write right.
            Self::SchedContextYieldTo => AccessRight::Write,
            // WS-ZA ZA6.32: the acknowledge writes the line's mask, the right
            // seL4's IRQHandler invocations need on the handler capability.
            Self::IrqHandlerAck => AccessRight::Write,
            // WS-ZA ZA6.32: the issue, bind and unbind write kernel state; the
            // Lean `syscallRequiredRight` gives each the write right.
            Self::IrqControlGet | Self::IrqHandlerSetNotification | Self::IrqHandlerClear => {
                AccessRight::Write
            }
        }
    }
}

/// **seL4's system calls** (`syscall.xml`, `api-mcs`): the number the trap
/// carries, negated, in `x7`.  An operation is not a syscall: an invocation is
/// a `Call` (or `Send`) on a capability with the operation's label in the
/// message-info word, and the kernel selects the operation from the syscall,
/// the invoked capability's type and the label (WS-SX SX7).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Syscall {
    /// `seL4_SysCall`, -1.
    Call,
    /// `seL4_SysReplyRecv`, -2.
    ReplyRecv,
    /// `seL4_SysNBSendRecv`, -3.
    NBSendRecv,
    /// `seL4_SysNBSendWait`, -4.
    NBSendWait,
    /// `seL4_SysSend`, -5.
    Send,
    /// `seL4_SysNBSend`, -6.
    NBSend,
    /// `seL4_SysRecv`, -7.
    Recv,
    /// `seL4_SysNBRecv`, -8.
    NBRecv,
    /// `seL4_SysWait`, -9.
    Wait,
    /// `seL4_SysNBWait`, -10.
    NBWait,
    /// `seL4_SysYield`, -11.
    Yield,
}

impl Syscall {
    /// Every syscall, in seL4's numbering order.
    pub const ALL: [Syscall; 11] = [
        Self::Call,
        Self::ReplyRecv,
        Self::NBSendRecv,
        Self::NBSendWait,
        Self::Send,
        Self::NBSend,
        Self::Recv,
        Self::NBRecv,
        Self::Wait,
        Self::NBWait,
        Self::Yield,
    ];

    /// The syscall's number, the negation of the word in `x7` (1 to 11).
    /// Lean: `Syscall.number`.
    pub const fn number(self) -> u32 {
        match self {
            Self::Call => 1,
            Self::ReplyRecv => 2,
            Self::NBSendRecv => 3,
            Self::NBSendWait => 4,
            Self::Send => 5,
            Self::NBSend => 6,
            Self::Recv => 7,
            Self::NBRecv => 8,
            Self::Wait => 9,
            Self::NBWait => 10,
            Self::Yield => 11,
        }
    }

    /// The word the trap carries in `x7`: the number negated, two's
    /// complement.  Lean: `Syscall.word`.
    pub const fn word(self) -> u64 {
        0u64.wrapping_sub(self.number() as u64)
    }

    /// The syscall a number names.  Lean: `Syscall.ofNumber?`.
    pub const fn from_number(n: u32) -> Option<Self> {
        match n {
            1 => Some(Self::Call),
            2 => Some(Self::ReplyRecv),
            3 => Some(Self::NBSendRecv),
            4 => Some(Self::NBSendWait),
            5 => Some(Self::Send),
            6 => Some(Self::NBSend),
            7 => Some(Self::Recv),
            8 => Some(Self::NBRecv),
            9 => Some(Self::Wait),
            10 => Some(Self::NBWait),
            11 => Some(Self::Yield),
            _ => None,
        }
    }

    /// The syscall an `x7` word names: its negation, when that fits 32 bits.
    /// Lean: `Syscall.ofWord?`.
    pub const fn from_word(w: u64) -> Option<Self> {
        let n = w.wrapping_neg();
        if n < (1u64 << 32) {
            Self::from_number(n as u32)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_u64_roundtrip() {
        let mut variants = 0;
        for i in 0..SyscallId::ENCODING_BOUND {
            if SyscallId::RETIRED.contains(&i) {
                assert!(SyscallId::from_u64(i).is_none());
                continue;
            }
            let sid = SyscallId::from_u64(i).unwrap();
            assert_eq!(sid.to_u64(), i);
            variants += 1;
        }
        assert_eq!(variants, SyscallId::COUNT);
    }

    #[test]
    fn from_u64_out_of_range() {
        assert!(SyscallId::from_u64(SyscallId::ENCODING_BOUND).is_none());
        assert!(SyscallId::from_u64(255).is_none());
    }

    #[test]
    fn retired_lifecycle_retype_number_is_reserved() {
        assert_eq!(SyscallId::RETIRED, [8, 34, 37]);
        assert!(SyscallId::from_u64(8).is_none());
    }

    #[test]
    fn injective() {
        // All variants produce distinct values
        let mut seen = [false; SyscallId::ENCODING_BOUND as usize];
        for i in 0..SyscallId::ENCODING_BOUND {
            let Some(sid) = SyscallId::from_u64(i) else {
                continue;
            };
            let idx = sid.to_u64() as usize;
            assert!(!seen[idx]);
            seen[idx] = true;
        }
    }

    #[test]
    fn required_right_ipc() {
        assert_eq!(SyscallId::Send.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::Receive.required_right(), AccessRight::Read);
        assert_eq!(SyscallId::Call.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::Reply.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_cspace() {
        assert_eq!(SyscallId::CSpaceMint.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceCopy.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceMove.required_right(), AccessRight::Grant);
        assert_eq!(SyscallId::CSpaceDelete.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_vspace() {
        assert_eq!(SyscallId::VSpaceMap.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::VSpaceUnmap.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_service() {
        assert_eq!(
            SyscallId::ServiceRegister.required_right(),
            AccessRight::Write
        );
        assert_eq!(
            SyscallId::ServiceRevoke.required_right(),
            AccessRight::Write
        );
        // ServiceQuery requires Read (not Write) — Lean API.lean:318
        assert_eq!(SyscallId::ServiceQuery.required_right(), AccessRight::Read);
    }

    #[test]
    fn required_right_notification() {
        assert_eq!(
            SyscallId::NotificationSignal.required_right(),
            AccessRight::Write
        );
        assert_eq!(
            SyscallId::NotificationWait.required_right(),
            AccessRight::Read
        );
    }

    #[test]
    fn required_right_reply_recv() {
        assert_eq!(SyscallId::ReplyRecv.required_right(), AccessRight::Read);
    }

    #[test]
    fn required_right_sched_context() {
        // Z5-J: All SchedContext operations require Write (API.lean:381-383)
        assert_eq!(
            SyscallId::SchedContextConfigure.required_right(),
            AccessRight::Write
        );
        assert_eq!(
            SyscallId::SchedContextBind.required_right(),
            AccessRight::Write
        );
        assert_eq!(
            SyscallId::SchedContextUnbind.required_right(),
            AccessRight::Write
        );
    }

    #[test]
    fn sched_context_discriminants() {
        assert_eq!(SyscallId::SchedContextConfigure.to_u64(), 17);
        assert_eq!(SyscallId::SchedContextBind.to_u64(), 18);
        assert_eq!(SyscallId::SchedContextUnbind.to_u64(), 19);
    }

    #[test]
    fn tcb_lifecycle_discriminants() {
        assert_eq!(SyscallId::TcbSuspend.to_u64(), 20);
        assert_eq!(SyscallId::TcbResume.to_u64(), 21);
    }

    #[test]
    fn tcb_priority_discriminants() {
        assert_eq!(SyscallId::TcbSetPriority.to_u64(), 22);
        assert_eq!(SyscallId::TcbSetMCPriority.to_u64(), 23);
    }

    #[test]
    fn tcb_ipc_buffer_discriminant() {
        assert_eq!(SyscallId::TcbSetIPCBuffer.to_u64(), 24);
    }

    #[test]
    fn tcb_affinity_discriminant() {
        // WS-SM SM5.H.4: CPU-affinity configuration
        assert_eq!(SyscallId::TcbSetAffinity.to_u64(), 25);
    }

    #[test]
    fn retired_tcb_set_fault_handler_number_is_reserved() {
        // WS-SX SX6.5: the fault endpoint is TcbSetSpace's extra capability 0.
        assert!(SyscallId::RETIRED.contains(&34));
        assert!(SyscallId::from_u64(34).is_none());
    }

    #[test]
    fn cspace_revoke_discriminant() {
        // WS-RR RR8.16 (`v0.35.190`): `seL4_CNode_Revoke`, appended so every
        // earlier discriminant is unchanged.
        assert_eq!(SyscallId::CspaceRevoke.to_u64(), 35);
        assert_eq!(SyscallId::from_u64(35), Some(SyscallId::CspaceRevoke));
        assert_eq!(SyscallId::CspaceRevoke.required_right(), AccessRight::Write);
    }

    #[test]
    fn untyped_retype_discriminant() {
        // WS-BP BP7.1 (`v0.36.5`): `seL4_Untyped_Retype`, appended so every
        // earlier discriminant is unchanged.
        assert_eq!(SyscallId::UntypedRetype.to_u64(), 36);
        assert_eq!(SyscallId::from_u64(36), Some(SyscallId::UntypedRetype));
        assert_eq!(
            SyscallId::UntypedRetype.required_right(),
            AccessRight::Retype
        );
    }

    #[test]
    fn retired_reset_discriminant() {
        // WS-SX SX7.1: 37, the untyped reset, is retired (seL4 resets inside
        // Untyped_Retype); every other discriminant is unchanged.
        assert_eq!(SyscallId::from_u64(37), None);
        assert_eq!(SyscallId::from_u64(38), Some(SyscallId::TcbSetSpace));
        assert_eq!(SyscallId::from_u64(39), Some(SyscallId::PageTableMap));
        assert_eq!(SyscallId::from_u64(40), Some(SyscallId::PageTableUnmap));
        // WS-ZA ZA4.3: the yield, appended the same way.
        assert_eq!(SyscallId::from_u64(41), Some(SyscallId::Yield));
        // WS-ZA ZA6.9: the Consumed invocation, appended the same way.
        assert_eq!(
            SyscallId::from_u64(42),
            Some(SyscallId::SchedContextConsumed)
        );
        // WS-ZA ZA6.29: the yieldTo invocation, appended the same way.
        assert_eq!(
            SyscallId::from_u64(43),
            Some(SyscallId::SchedContextYieldTo)
        );
        // WS-ZA ZA6.32: the interrupt acknowledge, appended the same way.
        assert_eq!(SyscallId::from_u64(44), Some(SyscallId::IrqHandlerAck));
        assert_eq!(
            SyscallId::IrqHandlerAck.required_right(),
            AccessRight::Write
        );
        // WS-ZA ZA6.32: the handler issue, bind and unbind, appended the same way.
        assert_eq!(SyscallId::from_u64(45), Some(SyscallId::IrqControlGet));
        assert_eq!(
            SyscallId::from_u64(46),
            Some(SyscallId::IrqHandlerSetNotification)
        );
        assert_eq!(SyscallId::from_u64(47), Some(SyscallId::IrqHandlerClear));
        for sid in [
            SyscallId::IrqControlGet,
            SyscallId::IrqHandlerSetNotification,
            SyscallId::IrqHandlerClear,
        ] {
            assert_eq!(sid.required_right(), AccessRight::Write);
        }
        assert_eq!(SyscallId::from_u64(48), None);
        assert_eq!(SyscallId::COUNT, 45);
        assert_eq!(SyscallId::ENCODING_BOUND, 48);
    }

    #[test]
    fn required_right_tcb_lifecycle() {
        // D1: Suspend/Resume require Write (API.lean:387-388)
        assert_eq!(SyscallId::TcbSuspend.required_right(), AccessRight::Write);
        assert_eq!(SyscallId::TcbResume.required_right(), AccessRight::Write);
    }

    #[test]
    fn required_right_tcb_priority() {
        // D2: Priority management requires Write (API.lean:389-390)
        assert_eq!(
            SyscallId::TcbSetPriority.required_right(),
            AccessRight::Write
        );
        assert_eq!(
            SyscallId::TcbSetMCPriority.required_right(),
            AccessRight::Write
        );
    }

    #[test]
    fn required_right_tcb_ipc_buffer() {
        // D3: IPC buffer configuration requires Write (API.lean:391)
        assert_eq!(
            SyscallId::TcbSetIPCBuffer.required_right(),
            AccessRight::Write
        );
    }

    #[test]
    fn required_right_tcb_affinity() {
        // WS-SM SM5.H.4: CPU-affinity configuration requires Write
        assert_eq!(
            SyscallId::TcbSetAffinity.required_right(),
            AccessRight::Write
        );
    }
}
