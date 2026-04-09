//! Trap frame structure and exception handler dispatch.
//!
//! The assembly entry points (vectors.S / trap.S) save the full CPU context
//! into a `TrapFrame` on the kernel stack, then call into these Rust handlers.
//! On return, the assembly restores context and executes ERET.

/// Saved CPU context during an exception.
///
/// Layout must match the assembly save/restore macros in `trap.S`:
/// - GPRs x0-x30 at offsets 0..248
/// - SP_EL0 at offset 248
/// - ELR_EL1 at offset 256
/// - SPSR_EL1 at offset 264
///
/// Total size: 34 × 8 = 272 bytes.
#[repr(C)]
pub struct TrapFrame {
    /// General-purpose registers x0-x30 (31 registers).
    pub gprs: [u64; 31],
    /// User-mode stack pointer (SP_EL0).
    pub sp_el0: u64,
    /// Exception Link Register — return address.
    pub elr_el1: u64,
    /// Saved Program Status Register — saved PSTATE.
    pub spsr_el1: u64,
}

/// Size of TrapFrame in bytes (for assembly offset calculations).
pub const TRAP_FRAME_SIZE: usize = core::mem::size_of::<TrapFrame>();

// Compile-time assertion that TrapFrame is exactly 272 bytes.
const _: () = assert!(TRAP_FRAME_SIZE == 272);

impl TrapFrame {
    /// ABI register accessors matching the seLe4n syscall convention:
    /// x0 = capability pointer, x1 = message info, x2-x5 = message registers,
    /// x7 = syscall number.
    /// x0 — capability pointer / first argument.
    #[inline(always)]
    pub fn x0(&self) -> u64 {
        self.gprs[0]
    }

    /// x1 — message info / second argument.
    #[inline(always)]
    pub fn x1(&self) -> u64 {
        self.gprs[1]
    }

    /// x2 — message register 0.
    #[inline(always)]
    pub fn x2(&self) -> u64 {
        self.gprs[2]
    }

    /// x3 — message register 1.
    #[inline(always)]
    pub fn x3(&self) -> u64 {
        self.gprs[3]
    }

    /// x4 — message register 2.
    #[inline(always)]
    pub fn x4(&self) -> u64 {
        self.gprs[4]
    }

    /// x5 — message register 3.
    #[inline(always)]
    pub fn x5(&self) -> u64 {
        self.gprs[5]
    }

    /// x7 — syscall number.
    #[inline(always)]
    pub fn x7(&self) -> u64 {
        self.gprs[7]
    }

    /// Set x0 (return value / error code).
    #[inline(always)]
    pub fn set_x0(&mut self, val: u64) {
        self.gprs[0] = val;
    }

    /// Set x1 (return message info).
    #[inline(always)]
    pub fn set_x1(&mut self, val: u64) {
        self.gprs[1] = val;
    }
}

/// ESR_EL1 Exception Class (EC) field values.
/// ARM ARM D17.2.40: ESR_EL1 bits [31:26].
mod ec {
    /// SVC instruction execution in AArch64 state.
    pub const SVC_AARCH64: u64 = 0x15;
    /// Instruction Abort from a lower Exception level.
    pub const IABT_LOWER: u64 = 0x20;
    /// Instruction Abort from the current Exception level.
    pub const IABT_CURRENT: u64 = 0x21;
    /// PC alignment fault.
    pub const PC_ALIGN: u64 = 0x22;
    /// Data Abort from a lower Exception level.
    pub const DABT_LOWER: u64 = 0x24;
    /// Data Abort from the current Exception level.
    pub const DABT_CURRENT: u64 = 0x25;
    /// SP alignment fault.
    pub const SP_ALIGN: u64 = 0x26;
}

/// Read ESR_EL1 to get the Exception Syndrome Register.
#[inline(always)]
fn read_esr_el1() -> u64 {
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: Reading ESR_EL1 at EL1 is always safe; it's a read-only
        // register that captures the syndrome of the most recent exception.
        // (ARM ARM D17.2.40)
        let val: u64;
        unsafe {
            core::arch::asm!("mrs {}, esr_el1", out(reg) val, options(nomem, nostack, preserves_flags));
        }
        val
    }
    #[cfg(not(target_arch = "aarch64"))]
    0
}

/// Extract the Exception Class from ESR_EL1.
#[inline(always)]
fn esr_ec(esr: u64) -> u64 {
    (esr >> 26) & 0x3F
}

/// Synchronous exception handler — called from assembly after context save.
///
/// Routes to the appropriate handler based on the ESR_EL1 Exception Class:
/// - SVC (0x15): Syscall dispatch (reads x0-x5, x7 from TrapFrame)
/// - Data/Instruction Abort: VM fault handling (placeholder)
/// - Other: Unhandled exception (prints diagnostic and halts)
#[no_mangle]
pub extern "C" fn handle_synchronous_exception(frame: &mut TrapFrame) {
    let esr = read_esr_el1();
    let exception_class = esr_ec(esr);

    match exception_class {
        ec::SVC_AARCH64 => {
            // Syscall: extract the immediate from ESR (bits [15:0]) or use x7
            // The seLe4n ABI uses x7 for syscall number, matching the Lean
            // model's `arm64DefaultLayout.syscallNumReg = ⟨7⟩`.
            //
            // AG7 will wire this to the Lean kernel FFI. For now, return
            // an error indicating the kernel is not yet ready.
            let _syscall_id = frame.x7();
            // Return error code 0 (no error) in x0 as a no-op placeholder.
            // AG7-A will replace this with actual Lean FFI dispatch.
            frame.set_x0(0);
        }
        ec::DABT_LOWER | ec::DABT_CURRENT => {
            // Data abort — set VM fault error in x0
            // KernelError.vmFault = 44 (from Lean error.rs mapping)
            frame.set_x0(44);
        }
        ec::IABT_LOWER | ec::IABT_CURRENT => {
            // Instruction abort — set VM fault error in x0
            frame.set_x0(44);
        }
        ec::PC_ALIGN | ec::SP_ALIGN => {
            // Alignment fault — set userException error
            // KernelError.userException = 43
            frame.set_x0(43);
        }
        _ => {
            // Unknown exception class — print diagnostic and set error
            crate::kprintln!("FATAL: unhandled exception EC=0x{:02x} ESR=0x{:016x}", exception_class, esr);
            frame.set_x0(43); // userException
        }
    }
}

/// IRQ handler — called from assembly after context save.
///
/// Stub implementation for AG4. AG5 will wire this to the GIC-400
/// acknowledge → dispatch → EOI sequence.
#[no_mangle]
pub extern "C" fn handle_irq(_frame: &mut TrapFrame) {
    // AG5-C will implement: GIC acknowledge → handler dispatch → GIC EOI
    crate::kprintln!("IRQ received (stub handler)");
}

/// SError handler — called from assembly on system error exceptions.
///
/// SErrors are typically unrecoverable hardware errors. Log and halt.
#[no_mangle]
pub extern "C" fn handle_serror(_frame: &mut TrapFrame) {
    crate::kprintln!("FATAL: SError exception");
    loop {
        crate::cpu::wfe();
    }
}
