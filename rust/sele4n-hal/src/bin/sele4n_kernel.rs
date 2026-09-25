//! The seLe4n kernel image (WS-BP BP5.1).
//!
//! This is the one final binary crate in the tree, so it is where the
//! kernel's image-wide decisions live: the entry point, the linker script
//! and the panic handler.  It contains almost no code, deliberately, because
//! everything the image runs is the HAL library's (and, once BP5.2 links it,
//! the Lean kernel's):
//!
//! * **The entry is `_start`** in `boot.S`, selected by `ENTRY(_start)` in
//!   `link.ld`.  `_start` masks FP/SIMD, zeroes `.bss` and the stacks, sets
//!   the boot stack and branches to [`sele4n_hal::boot::rust_boot_main`];
//!   this crate has no `main` (`no_main`) because nothing but the firmware
//!   ever calls into the image.
//! * **The layout is `link.ld`'s**, passed to the link by the HAL's build
//!   script (`-T link.ld`, emitted for this binary alone and only on a
//!   bare-metal target), so the section boundaries the boot map's W^X
//!   permissions are built from, the Lean heap arena and the kernel's
//!   reserved extent are the ones `scripts/check_link_script.py` proves live.
//! * **A panic halts the whole system.**  The HAL defines no
//!   `#[panic_handler]` — a library cannot — and several of its fail-closed
//!   paths reach one through an `assert!` or a bounds check, so what a panic
//!   does is decided here.  It does what every boot-fatal refusal in the HAL
//!   already does: [`sele4n_hal::gic::halt_all`], which parks every other PE
//!   with an SGI and then this one with its interrupts masked.  Halting only
//!   this PE would leave the others running on state the panicking core may
//!   have left half-written — the shape `shootdown.rs` records for its round
//!   generation wrap.  No diagnostic is printed: the UART writer takes a lock
//!   the panicking core may already hold, and a best-effort message that can
//!   deadlock is not best-effort.
//!
//! On a hosted target this file is a program that refuses to run: the HAL's
//! host lanes build every target (`cargo clippy --all-targets
//! --all-features`), and a `no_std` / `no_main` binary is not a thing a
//! hosted target can link.  `required-features = ["kernel_image"]` keeps it
//! out of every ordinary build.
//!
//! Until BP5.2 links `libsele4n.a` this image is built **without**
//! `hw_target`, so it boots the Rust half only —
//! `SecondaryReleasePermit::no_lean_kernel` licenses the secondaries'
//! release and no Lean code is present to install kernel state.

#![cfg_attr(target_os = "none", no_std)]
#![cfg_attr(target_os = "none", no_main)]
#![deny(unsafe_code)]

// The binary's own code is the panic handler; linking the HAL is what puts
// `rust_boot_main`, the vectors and the assembly entry in the image.
use sele4n_hal as _;

#[cfg(target_os = "none")]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    sele4n_hal::gic::halt_all()
}

#[cfg(not(target_os = "none"))]
fn main() {
    eprintln!(
        "sele4n-kernel is the bare-metal kernel image; build it for \
         aarch64-unknown-none-softfloat (scripts/test_aarch64_cross_build.sh)"
    );
    std::process::exit(1);
}
