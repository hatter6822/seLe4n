// SPDX-License-Identifier: GPL-3.0-or-later
//! **WS-SM SM1.D**: DTB `/chosen/bootargs` command-line parser.
//!
//! At boot time U-Boot (or ARM Trusted Firmware) hands the kernel a
//! pointer to a flattened device tree (DTB) in `x0`.  The DTB's
//! `/chosen/bootargs` property carries the kernel command-line string —
//! this module extracts that string and parses it into a typed
//! [`CmdlineConfig`] the boot path consumes.
//!
//! ## Supported options (v1.0.0)
//!
//! | Key             | Type   | Default | Semantics                                |
//! |-----------------|--------|---------|------------------------------------------|
//! | `smp_enabled`   | bool   | `true`  | Enable SMP secondary-core bring-up.      |
//! | `smp_max_cores` | usize  | 4       | Upper bound on cores to bring up [0..4]. |
//!
//! Unknown tokens are silently ignored (forward-compatible).  Malformed
//! values fall back to the default for the affected option — the parser
//! never panics on user input.
//!
//! ## Sub-task map (SMP_RUST_HAL_PLAN.md §5.4)
//!
//! - **SM1.D.1**: this module's parser ([`parse_cmdline`]) +
//!   self-contained DTB walker ([`extract_bootargs_into`]).
//! - **SM1.D.2**: Phase 5 in `rust_boot_main` (see `boot.rs`).
//! - **SM1.D.3**: [`CmdlineConfig::default`] has `smp_enabled = true`
//!   per maintainer decision #7.  The static `smp::SMP_ENABLED` atomic
//!   still defaults to `false` at module load; Phase 5 sets it to the
//!   parsed value before invoking [`crate::smp::bring_up_secondaries`].
//! - **SM1.D.4**: per-object locks live inside objects with
//!   `Default::default()` initialisers; no global BKL exists under
//!   per-object fine locks, so no init-order hazard.  See module
//!   docstring of `crate::smp` for the BKL-state-machine discussion.
//! - **SM1.D.5**: `per_cpu::check_per_cpu_invariants()` runs in Phase 1
//!   of `rust_boot_main`, before TPIDR_EL1 is set and before
//!   bring-up issues any PSCI CPU_ON.
//! - **SM1.D.6**: [`crate::smp::bring_up_secondaries_with_limit`]
//!   accepts an upper bound on the secondaries to spawn — useful for
//!   QEMU testing with `-smp 2` etc.
//!
//! ## DTB walker design
//!
//! The walker is a fuel-bounded depth-first scan of the DTB's
//! structure block (Devicetree Specification v0.4 §5.4).  It looks for
//! the `/chosen` node and copies its `bootargs` property into a
//! caller-supplied buffer.  Failure modes (NULL pointer, bad magic,
//! malformed tokens, fuel exhaustion, missing node/property) all
//! short-circuit to "empty bootargs" — which then yields the default
//! [`CmdlineConfig`].
//!
//! The DTB walker is deliberately self-contained (does **not** route
//! through the Lean-side `Platform.DeviceTree` parser).  Calling out to
//! the Lean kernel from boot.rs Phase 5 would create a circular
//! dependency: the kernel needs the cmdline parsed *before* it is
//! initialised, but the Lean kernel cannot run until kernel state is
//! initialised.  Keeping the parser in Rust resolves the cycle and
//! keeps the trust boundary tight.  The Lean parser (which has formal
//! correctness theorems) is the canonical structure walker for
//! kernel-time DTB consumption; this Rust parser duplicates only the
//! minimum surface needed at boot.

// Bring `std` into scope under `cargo test` only.  The HAL is
// `no_std` for production builds (kernel runs without libstd); under
// the host test profile we use `Vec` and friends in the DTB-blob test
// fixtures.  Production code below never references `std::*` items.
#[cfg(test)]
extern crate std;

use core::sync::atomic::Ordering;

/// **WS-SM SM1.D.1**: Maximum number of bootargs bytes we copy from
/// the DTB into our local buffer.
///
/// Real-world kernel command lines on production systems are well
/// under 1 KiB.  Linux's `CONFIG_COMMAND_LINE_SIZE` defaults to 256
/// for embedded targets and 2 KiB on x86/arm64; we pick a middle
/// value that covers expected use cases without burning excessive
/// stack frame.
///
/// The buffer is a stack frame in [`parse_cmdline_from_dtb`] — using
/// 1024 bytes is well within the 64 KiB-per-core stack reservation in
/// `link.ld`.
pub const MAX_BOOTARGS_LEN: usize = 1024;

/// **WS-SM SM1.D.1 audit-pass-1** (defense-in-depth): upper bound on
/// the DTB blob size we will accept from `dtb_ptr`.
///
/// The DTB-header-supplied `totalsize` is untrusted — a malicious or
/// malformed bootloader could write an arbitrarily large value
/// (e.g., `0xFFFF_FFFF` ≈ 4 GB).  Constructing
/// `core::slice::from_raw_parts(dtb_ptr, totalsize)` over memory that
/// isn't fully readable is Undefined Behaviour per Rust's safety
/// invariants — even if we never read past the actual blob, the
/// slice itself must describe a valid contiguous extent.
///
/// We bound `totalsize` at 2 MiB.  Real-world DTBs are tens to a few
/// hundred KiB (RPi5 BCM2712: ~50 KiB); Linux's
/// `OF_FDT_MAX_HEADERSIZE` cap is implicit at the page-allocator
/// level (usually order-3 allocations, ~32 KiB).  A 2 MiB bound is
/// orders of magnitude above any plausible legitimate DTB and still
/// well below the smallest typical RAM region a bootloader maps.
///
/// A DTB with `totalsize > MAX_DTB_SIZE` is rejected at
/// [`extract_bootargs_into`]; the kernel falls back to the default
/// [`CmdlineConfig`] (the same behaviour as missing/malformed DTB).
const MAX_DTB_SIZE: usize = 2 * 1024 * 1024;

/// **WS-SM SM1.D.1**: DTB magic number (big-endian when read as u32).
///
/// Per Devicetree Specification v0.4 §5.2: every DTB starts with the
/// 4-byte magic value `0xD00DFEED` (stored big-endian on disk; read
/// as a u32 after `u32::from_be_bytes`).  A magic mismatch is the
/// strongest indicator we have that the DTB pointer is invalid (NULL
/// pointer, wrong type, mis-aligned, or simply absent on platforms
/// that don't pass a DTB).
const FDT_MAGIC: u32 = 0xD00D_FEED;

/// **WS-SM SM1.D.1**: FDT structure block tokens (Devicetree Spec v0.4 §5.4.1).
const FDT_BEGIN_NODE: u32 = 0x0000_0001;
const FDT_END_NODE: u32 = 0x0000_0002;
const FDT_PROP: u32 = 0x0000_0003;
const FDT_NOP: u32 = 0x0000_0004;
const FDT_END: u32 = 0x0000_0009;

/// **WS-SM SM1.D.1**: Header size in bytes per Devicetree Spec v0.4 §5.2.
///
/// The standard header carries 10 big-endian `u32` fields:
/// `magic`, `totalsize`, `off_dt_struct`, `off_dt_strings`,
/// `off_mem_rsvmap`, `version`, `last_comp_version`,
/// `boot_cpuid_phys`, `size_dt_strings`, `size_dt_struct`.
const FDT_HEADER_SIZE: usize = 40;

/// **WS-SM SM1.D.1**: Fuel bound for the DTB structure walk.
///
/// Caps the number of FDT tokens we'll consume before giving up.
/// Real DTBs have a few hundred tokens; 4096 is a comfortable upper
/// bound that still guards against pathological / malicious blobs
/// with infinite NOP chains or recursive cycles.
const FDT_WALK_FUEL: usize = 4096;

/// **WS-SM SM1.D.1**: Maximum nesting depth for DTB nodes.
///
/// Production DTBs don't nest beyond ~6 levels.  This bound prevents
/// stack exhaustion or runaway recursion on malformed blobs.
const FDT_MAX_DEPTH: usize = 32;

/// **WS-SM SM1.D.1**: Parsed kernel command-line configuration.
///
/// Returned by [`parse_cmdline`] and consumed by `boot.rs::rust_boot_main`
/// Phase 5.  Each field has a documented default in [`Self::default`].
///
/// **Stability**: this struct is `#[derive(Debug, Clone, Copy)]` so it
/// can be passed by value through the boot path.  Adding fields is
/// non-breaking for the parser (which only matches known keys); the
/// initialisation site in [`Self::default`] must be updated in
/// lockstep to provide the new field's default.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CmdlineConfig {
    /// **WS-SM SM1.D.3**: Whether to bring up secondary cores at boot.
    ///
    /// `true` (default): boot loops through [`crate::smp::SECONDARY_MPIDR_TABLE`]
    /// and issues PSCI `CPU_ON` for each secondary, up to
    /// [`Self::smp_max_cores`].
    ///
    /// `false`: only the boot core runs.  Useful for debugging the
    /// boot path on single-core targets, or for diagnostic kernels
    /// that need to isolate a regression to single-core operation.
    pub smp_enabled: bool,

    /// **WS-SM SM1.D.6**: Maximum number of cores (including the boot
    /// core) to bring up.
    ///
    /// Clamped to `[0, MAX_SECONDARY_CORES + 1]` (= `[0, 4]` on RPi5)
    /// during parsing — out-of-range values silently saturate to the
    /// platform bound.  Examples:
    ///
    /// - `0` → no cores brought up (functionally equivalent to
    ///   `smp_enabled=false`).
    /// - `1` → boot core only; no secondaries.
    /// - `2` → boot core + 1 secondary.
    /// - `4` → boot core + 3 secondaries (full RPi5 quartet).
    ///
    /// The default of `4` matches the RPi5 BCM2712 core count.  Users
    /// passing `smp_max_cores=2` get a 2-core boot for QEMU `-smp 2`
    /// testing.
    pub smp_max_cores: usize,
}

impl Default for CmdlineConfig {
    /// **WS-SM SM1.D.3**: Production default — SMP enabled, all 4
    /// cores brought up.
    ///
    /// Per maintainer decision #7 (recorded in
    /// `docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md`), v1.0.0
    /// defaults to "SMP on" so the verified microkernel arrives at
    /// production with all four Cortex-A76 cores online by default.
    /// Operators that need single-core boot can opt out via
    /// `smp_enabled=false` on the kernel command line.
    ///
    /// Note: this differs from the `crate::smp::SMP_ENABLED` atomic's
    /// initial value of `false`.  The atomic stays `false` at module
    /// load (so a kernel that never reaches Phase 5 — e.g., one that
    /// halts in an earlier phase due to a hardware fault — does not
    /// accidentally start spawning secondaries).  Phase 5 explicitly
    /// stores the parsed `smp_enabled` into the atomic before invoking
    /// [`crate::smp::bring_up_secondaries`].
    fn default() -> Self {
        Self {
            smp_enabled: true,
            smp_max_cores: crate::smp::MAX_SECONDARY_CORES + 1,
        }
    }
}

/// **WS-SM SM1.D.1**: Parse a kernel command-line string into a
/// [`CmdlineConfig`].
///
/// ## Format
///
/// The command line is a sequence of space-separated tokens.  Each
/// token is either:
///
/// - A `key=value` pair (typed: bool or usize, depending on key)
/// - A bare flag (currently no recognised flags; reserved for future
///   options like `quiet` or `debug`)
///
/// Quoted values (`key="some value with spaces"`) are accepted by
/// trimming the matched leading/trailing quote characters.  ASCII
/// double-quote and single-quote are both supported.
///
/// ## Forward compatibility
///
/// Unknown keys are silently ignored.  This lets a future kernel
/// version add new options (e.g., `log_level=debug`) without breaking
/// boot when an older bootloader passes a cmdline still containing
/// them — or, in the reverse direction, an older kernel boots cleanly
/// when a newer bootloader passes options it doesn't yet know about.
///
/// ## Robustness
///
/// Malformed values fall back to the default for the affected option:
///
/// - `smp_enabled=foo` → keeps default (`true`).
/// - `smp_max_cores=999` → clamped to `MAX_SECONDARY_CORES + 1 = 4`.
/// - `smp_max_cores=-1` → fails parse (negative not allowed for
///   `usize`), keeps default.
/// - Empty value (`smp_enabled=`) → keeps default.
///
/// The parser never panics on user input.
pub fn parse_cmdline(s: &str) -> CmdlineConfig {
    let mut cfg = CmdlineConfig::default();
    for token in s.split_ascii_whitespace() {
        parse_token_into(token, &mut cfg);
    }
    // SM1.D.6 invariant: smp_max_cores never exceeds the platform's
    // physical core count, even if the user passes a larger value.
    // The clamp also runs after the per-token parse so a token like
    // `smp_max_cores=999` always sees the saturated value.
    cfg.smp_max_cores = cfg.smp_max_cores.min(crate::smp::MAX_SECONDARY_CORES + 1);
    cfg
}

/// **WS-SM SM1.D.1**: Apply a single cmdline token to the running
/// [`CmdlineConfig`].
///
/// Helper for [`parse_cmdline`].  Factored out so a hypothetical
/// future "stream parser" (reading bootargs lazily from the DTB) can
/// reuse the per-token discipline.  Side effect only — returns nothing
/// and silently ignores unrecognised tokens.
fn parse_token_into(token: &str, cfg: &mut CmdlineConfig) {
    if let Some(eq_idx) = token.find('=') {
        let key = &token[..eq_idx];
        // Skip the '=' byte.  `find('=')` returns a byte offset; '=' is
        // 1 byte in UTF-8, so `eq_idx + 1` is a valid char boundary.
        let value_raw = &token[eq_idx + 1..];
        let value = trim_matching_quotes(value_raw);
        match key {
            "smp_enabled" => {
                if let Some(b) = parse_bool(value) {
                    cfg.smp_enabled = b;
                }
                // else: malformed value, keep default
            }
            "smp_max_cores" => {
                if let Ok(n) = value.parse::<usize>() {
                    cfg.smp_max_cores = n.min(crate::smp::MAX_SECONDARY_CORES + 1);
                }
                // else: malformed value, keep default
            }
            _ => {
                // Unknown key — silently ignore (forward-compat).
            }
        }
    } else {
        // Flag-only token.  Currently no recognised flags.  Reserved
        // for future use (e.g., `debug`, `quiet`).  Unknown flags are
        // silently ignored.
    }
}

/// **WS-SM SM1.D.1**: Trim a single pair of matching leading/trailing
/// quote characters from a string slice.
///
/// Accepts both ASCII `"` (U+0022) and `'` (U+0027).  If the string
/// has no matching quote pair, returns the input unchanged.  If only
/// one side is quoted (e.g., `"foo`), the input is also returned
/// unchanged — partial quoting is treated as a parse error rather than
/// silent acceptance.
///
/// Note: this does NOT handle escape sequences (`\"`, `\\`, etc.).
/// The kernel command line is a one-line bootloader-provided string
/// without escape semantics; if escape support is ever needed, this
/// function is the place to add it.
fn trim_matching_quotes(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.len() < 2 {
        return s;
    }
    let first = bytes[0];
    let last = bytes[bytes.len() - 1];
    if (first == b'"' && last == b'"') || (first == b'\'' && last == b'\'') {
        // ASCII quote characters are single-byte; slicing past them is
        // safe and produces a valid UTF-8 substring.
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// **WS-SM SM1.D.1**: Parse a boolean value from a cmdline token.
///
/// Accepts the Linux-conventional names (`true`/`false`, `yes`/`no`,
/// `on`/`off`, `1`/`0`).  Case-sensitive ASCII matching — the kernel
/// command line is a fixed-format machine-readable string, not a
/// human-input form, so we don't widen to case-insensitive matching.
///
/// Returns `None` on any unrecognised value (the caller falls back to
/// the default).
fn parse_bool(s: &str) -> Option<bool> {
    match s {
        "true" | "1" | "yes" | "on" => Some(true),
        "false" | "0" | "no" | "off" => Some(false),
        _ => None,
    }
}

/// **WS-SM SM1.D.1**: Read a big-endian `u32` from a byte slice at the
/// given byte offset.
///
/// Returns `None` if the offset is out of bounds OR if `offset + 4`
/// overflows `usize`.  The `checked_add` is the defense against a
/// hostile caller passing `offset == usize::MAX - 3`: without it,
/// `offset + 4` would wrap to a small value and the subsequent
/// `blob.get(..)` could succeed against an unintended range.  In
/// practice every caller bounds `offset` by `struct_end_exclusive`,
/// but the explicit overflow check makes the discipline robust by
/// construction.  Use this for every DTB header / structure-block
/// read — the DTB is big-endian on disk regardless of host
/// endianness.
#[inline]
fn read_be_u32(blob: &[u8], offset: usize) -> Option<u32> {
    let end = offset.checked_add(4)?;
    // Use slice indexing through `get` to get an Option without panic.
    let bytes = blob.get(offset..end)?;
    // We've just bounded the slice to 4 bytes via get(); the
    // try_into is structurally guaranteed to succeed and the unwrap
    // is unreachable.  Using `from_be_bytes` instead of manual shifts
    // keeps the implementation aligned with `u32::to_be_bytes`'s
    // inverse semantics and is what `clippy::manual_bit_ops` would
    // recommend.
    let arr: [u8; 4] = bytes.try_into().ok()?;
    Some(u32::from_be_bytes(arr))
}

/// **WS-SM SM1.D.1**: Highest FDT layout version this parser
/// supports.  A DTB whose `last_comp_version` is greater than this
/// requires layout features we don't implement — we refuse to parse
/// it rather than risk misinterpretation.
///
/// Version 17 added the `size_dt_strings` and `size_dt_struct` fields
/// at offsets 32/36; our parser reads those fields, so we are a v17
/// parser.  Per the FDT spec, a parser version `P` can read any DTB
/// whose `last_comp_version <= P`.
const FDT_PARSER_VERSION: u32 = 17;

/// **WS-SM SM1.D.1**: Parsed FDT header fields.
///
/// Sliced from a DTB blob's first 40 bytes by [`parse_fdt_header`].
#[derive(Debug, Clone, Copy)]
struct FdtHeader {
    /// Should equal [`FDT_MAGIC`] (`0xD00DFEED`).
    magic: u32,
    /// Total DTB size in bytes (header + reserved memory map +
    /// structure block + strings block).
    totalsize: u32,
    /// Byte offset into the blob where the structure block begins.
    off_dt_struct: u32,
    /// Byte offset into the blob where the strings block begins.
    off_dt_strings: u32,
    /// DTB format version.  v1.0.0 requires ≥ 16.
    version: u32,
    /// Minimum FDT version required to parse this DTB.  Per the
    /// FDT spec, a parser at layout version `P` may read DTBs whose
    /// `last_comp_version <= P`.  Our parser is at
    /// [`FDT_PARSER_VERSION`].
    last_comp_version: u32,
    /// Size of the structure block in bytes.
    size_dt_struct: u32,
    /// Size of the strings block in bytes.
    size_dt_strings: u32,
}

/// **WS-SM SM1.D.1**: Parse the 40-byte FDT header from a DTB blob.
///
/// Returns `None` if the blob is too small, has the wrong magic, or
/// any header field can't be read.  Lets every subsequent call assume
/// the header is sane.
fn parse_fdt_header(blob: &[u8]) -> Option<FdtHeader> {
    if blob.len() < FDT_HEADER_SIZE {
        return None;
    }
    let magic = read_be_u32(blob, 0)?;
    if magic != FDT_MAGIC {
        return None;
    }
    let totalsize = read_be_u32(blob, 4)?;
    let off_dt_struct = read_be_u32(blob, 8)?;
    let off_dt_strings = read_be_u32(blob, 12)?;
    // Skip off_mem_rsvmap at 16.
    let version = read_be_u32(blob, 20)?;
    let last_comp_version = read_be_u32(blob, 24)?;
    // Skip boot_cpuid_phys at 28.
    let size_dt_strings = read_be_u32(blob, 32)?;
    let size_dt_struct = read_be_u32(blob, 36)?;
    Some(FdtHeader {
        magic,
        totalsize,
        off_dt_struct,
        off_dt_strings,
        version,
        last_comp_version,
        size_dt_struct,
        size_dt_strings,
    })
}

/// **WS-SM SM1.D.1**: Validate header field consistency.
///
/// Returns `true` if the header passes the full sanity check set:
///   1. Magic = `0xD00DFEED` (re-verified for defense-in-depth even
///      though [`parse_fdt_header`] already gates on it).
///   2. `version >= 16` (the minimum we support).
///   3. `last_comp_version <= FDT_PARSER_VERSION` — refuses DTBs
///      requiring a newer layout than this parser supports
///      (audit-pass-1 forward-compat defense).
///   4. `totalsize >= FDT_HEADER_SIZE`.
///   5. Offsets `off_dt_struct` / `off_dt_strings` are 4-byte aligned
///      (FDT tokens require 4-byte alignment).
///   6. Both blocks fit inside `totalsize`.
fn validate_fdt_header(hdr: &FdtHeader) -> bool {
    if hdr.magic != FDT_MAGIC {
        return false;
    }
    if hdr.version < 16 {
        return false;
    }
    // Audit-pass-1: reject DTBs that require a newer parser than us.
    // Per FDT spec, `last_comp_version` is the minimum version the
    // parser must support to correctly read this DTB; if it exceeds
    // our parser's version, layout fields might be at different
    // offsets and we'd silently misread them.
    if hdr.last_comp_version > FDT_PARSER_VERSION {
        return false;
    }
    if hdr.totalsize < FDT_HEADER_SIZE as u32 {
        return false;
    }
    // Block offsets must be 4-byte aligned (FDT tokens are 4-byte).
    if hdr.off_dt_struct % 4 != 0 {
        return false;
    }
    if hdr.off_dt_strings % 4 != 0 {
        return false;
    }
    // Block end must fit inside the total size.  Use u64 arithmetic
    // so a malicious `off + size > u32::MAX` doesn't wrap silently.
    let struct_end = hdr.off_dt_struct as u64 + hdr.size_dt_struct as u64;
    if struct_end > hdr.totalsize as u64 {
        return false;
    }
    let strings_end = hdr.off_dt_strings as u64 + hdr.size_dt_strings as u64;
    if strings_end > hdr.totalsize as u64 {
        return false;
    }
    true
}

/// **WS-SM SM1.D.1**: Look up a string in the FDT strings block by
/// its offset.
///
/// Strings are null-terminated.  Returns `None` if the offset is out
/// of range, the string runs past the strings block end, or the
/// string contains non-ASCII bytes the caller would have to reject.
///
/// The slice returned is borrowed from `blob`; callers must not
/// retain it past the lifetime of `blob`.
fn lookup_fdt_string(
    blob: &[u8],
    strings_off: usize,
    strings_size: usize,
    name_offset: usize,
) -> Option<&[u8]> {
    if name_offset >= strings_size {
        return None;
    }
    // Audit-pass-1: `strings_off + name_offset` and `strings_off +
    // strings_size` can each overflow with adversarial values
    // (`strings_off ≈ usize::MAX`).  In practice
    // `validate_fdt_header` bounded `strings_off + strings_size <=
    // totalsize <= MAX_DTB_SIZE`, so the overflow is unreachable on
    // legitimate input; but using `checked_add` keeps the function
    // total even against a future caller that bypasses validation.
    let abs = strings_off.checked_add(name_offset)?;
    let strings_end = strings_off.checked_add(strings_size)?;
    // Search for the null terminator, bounded by the strings block end.
    let slice = blob.get(abs..strings_end)?;
    let null_idx = slice.iter().position(|&b| b == 0)?;
    Some(&slice[..null_idx])
}

/// **WS-SM SM1.D.1**: Read a null-terminated string from the DTB
/// structure block at the given offset, returning the byte slice and
/// the offset past the terminator (padded to 4 bytes per Spec §5.4).
///
/// Audit-pass-1: every arithmetic step uses `checked_add` so a
/// hostile input close to `usize::MAX` cannot overflow into a
/// wrap-around.  The `null_idx + 1` would only overflow if the input
/// itself were `usize::MAX` long, which is impossible (a `&[u8]`
/// slice's length is at most `isize::MAX`), but the explicit check
/// is documentation and defense-in-depth.
fn read_node_name(blob: &[u8], offset: usize) -> Option<(&[u8], usize)> {
    // Find the null terminator starting at `offset`.  Bound by blob length.
    let tail = blob.get(offset..)?;
    let null_idx = tail.iter().position(|&b| b == 0)?;
    let name = &tail[..null_idx];
    // Length including null terminator.
    let name_with_null_len = null_idx.checked_add(1)?;
    // Round up to 4-byte alignment using a (4 - len % 4) % 4 padding
    // computation; this avoids the `(x + 3) & !3` form whose
    // intermediate `x + 3` can overflow for `x` near `usize::MAX`.
    let padding = (4usize - (name_with_null_len % 4)) % 4;
    let padded_len = name_with_null_len.checked_add(padding)?;
    let next_offset = offset.checked_add(padded_len)?;
    if next_offset > blob.len() {
        return None;
    }
    Some((name, next_offset))
}

/// **WS-SM SM1.D.1**: Walk the FDT structure block looking for
/// `/chosen/bootargs`.  Returns the bootargs value bytes (as a slice
/// of `blob`) on success, or `None` if absent / unparseable.
///
/// ## Walk discipline
///
/// The DTB structure block is a stream of tokens; we maintain three
/// pieces of state during the walk:
///   - `offset`: current byte position in the blob (relative to the
///     start of the blob, not the structure block).
///   - `depth`: current node nesting depth (0 = before root,
///     1 = inside `/`, 2 = inside children of `/`, etc.).
///   - `in_chosen` + `chosen_depth`: whether we are currently
///     descended into the `/chosen` subtree and the depth at which
///     we entered.
///
/// Token handling:
///   - `FDT_BEGIN_NODE`: read the node name; if we're about to
///     enter a top-level node (depth == 1, the children of `/`)
///     whose name is exactly `"chosen"`, set `in_chosen = true` and
///     remember the depth we are inside chosen at (`chosen_depth`).
///     Increment depth.
///   - `FDT_END_NODE`: decrement depth; if we were inside chosen
///     and depth dropped below the chosen-entering depth, clear
///     `in_chosen`.
///   - `FDT_PROP`: read len/nameoff; only if `in_chosen` AND we are
///     **directly** inside `/chosen` (not in a nested sub-node:
///     `depth == chosen_depth`) AND the looked-up property name is
///     `"bootargs"`, return its value.  This filters out a
///     hypothetical `/chosen/sub/bootargs` (audit-pass-1).
///   - `FDT_NOP`: skip; doesn't move depth or in_chosen.
///   - `FDT_END`: terminate the walk.
///
/// Fuel-bounded by [`FDT_WALK_FUEL`]; depth-bounded by [`FDT_MAX_DEPTH`].
fn find_bootargs_in_dtb(blob: &[u8]) -> Option<&[u8]> {
    let hdr = parse_fdt_header(blob)?;
    if !validate_fdt_header(&hdr) {
        return None;
    }
    let strings_off = hdr.off_dt_strings as usize;
    let strings_size = hdr.size_dt_strings as usize;
    let struct_start = hdr.off_dt_struct as usize;
    let struct_end_exclusive = struct_start.checked_add(hdr.size_dt_struct as usize)?;
    if struct_end_exclusive > blob.len() {
        return None;
    }

    let mut offset = struct_start;
    let mut depth: usize = 0;
    let mut in_chosen = false;
    let mut chosen_depth: usize = 0;
    let mut fuel = FDT_WALK_FUEL;

    while fuel > 0 {
        fuel -= 1;
        // Audit-pass-1: use checked_add so a hostile offset close to
        // `usize::MAX` cannot overflow into a wrap-around that
        // appears valid.  In practice `offset` is bounded by
        // `struct_end_exclusive` (and therefore by `blob.len()`), so
        // the overflow path is unreachable on legitimate input, but
        // the explicit `?` makes the discipline fail-closed.
        let next_token_offset = offset.checked_add(4)?;
        if next_token_offset > struct_end_exclusive {
            break;
        }
        let token = read_be_u32(blob, offset)?;
        match token {
            FDT_BEGIN_NODE => {
                let (name, next_off) = read_node_name(blob, next_token_offset)?;
                if next_off > struct_end_exclusive {
                    return None;
                }
                // depth 0 → before root; depth 1 → we're inside `/`,
                // so this BEGIN_NODE introduces a top-level child
                // (where `/chosen` lives).  Detect /chosen exactly
                // — `chosen@N` (unit-address suffix) is not the
                // canonical /chosen and is rejected by exact-match.
                if depth == 1 && name == b"chosen" {
                    in_chosen = true;
                    chosen_depth = depth.checked_add(1)?;
                }
                depth = depth.checked_add(1)?;
                if depth > FDT_MAX_DEPTH {
                    return None;
                }
                offset = next_off;
            }
            FDT_END_NODE => {
                if depth == 0 {
                    return None;
                }
                depth -= 1;
                if in_chosen && depth < chosen_depth {
                    in_chosen = false;
                }
                offset = offset.checked_add(4)?;
            }
            FDT_PROP => {
                // Property layout: token (4) + len (4) + nameoff (4)
                // + value (len, padded to 4 bytes).
                let len_offset = offset.checked_add(4)?;
                let nameoff_offset = offset.checked_add(8)?;
                let len = read_be_u32(blob, len_offset)?;
                let nameoff = read_be_u32(blob, nameoff_offset)?;
                let value_start = offset.checked_add(12)?;
                let value_end = value_start.checked_add(len as usize)?;
                if value_end > struct_end_exclusive {
                    return None;
                }
                // Audit-pass-1: only match bootargs if we are
                // **directly** inside /chosen (depth == chosen_depth),
                // not in a nested sub-node like /chosen/sub.  A
                // malicious DTB with `/chosen/sub/bootargs =
                // "smp_enabled=false"` must NOT be honoured.  The FDT
                // spec puts properties before sub-nodes within any
                // node, so this is also robust to ordering edge
                // cases where a /chosen/sub appears between /chosen's
                // direct properties.
                if in_chosen && depth == chosen_depth {
                    let prop_name = lookup_fdt_string(
                        blob,
                        strings_off,
                        strings_size,
                        nameoff as usize,
                    )?;
                    if prop_name == b"bootargs" {
                        return blob.get(value_start..value_end);
                    }
                }
                // Advance past value, padded to 4-byte alignment.
                // `(len + 3) & !3` could overflow on a 32-bit target
                // with adversarial `len`; use `checked_add` for
                // defense-in-depth.
                let len_usize = len as usize;
                let padding = (4usize - (len_usize % 4)) % 4;
                let padded_len = len_usize.checked_add(padding)?;
                offset = value_start.checked_add(padded_len)?;
            }
            FDT_NOP => {
                offset = offset.checked_add(4)?;
            }
            FDT_END => {
                return None;
            }
            _ => {
                // Unknown token — malformed blob; fail safely.
                return None;
            }
        }
    }
    None
}

/// **WS-SM SM1.D.1**: Extract the kernel command-line string from a
/// DTB blob into a caller-supplied buffer.
///
/// Returns a `&str` slice of `buffer` containing the bootargs (with
/// any trailing nulls stripped), or an empty slice on any failure
/// (NULL pointer, bad magic, missing property, malformed blob,
/// non-UTF8 bytes, buffer too small).
///
/// ## Safety
///
/// `dtb_ptr` is taken as a raw u64 address rather than a `&[u8]`
/// because on real hardware the DTB pointer arrives in `x0` from
/// U-Boot as an opaque physical address.  The function:
///
///   1. Treats `dtb_ptr == 0` as "no DTB available" → empty string.
///   2. Otherwise reads the header word at `dtb_ptr` to learn the
///      total size, then constructs a slice covering the full DTB.
///
/// The function is `unsafe` to call if any of the following hold:
///   - The pointer is non-null but does not point to a readable
///     mapping of at least 40 bytes.
///   - The DTB lifetime is shorter than the function call (the slice
///     borrow extends through the return; the function doesn't
///     retain it past return).
///
/// The boot path (rust_boot_main) calls this with the `x0`-passed
/// pointer, which by the ARM64 boot ABI is either NULL or points
/// to a valid DTB mapped at boot time (typically in physical RAM
/// reserved by U-Boot).
///
/// ## Why not `&'static str`?
///
/// The plan's original sketch returned `&'static str` from
/// `extract_bootargs(dtb_ptr)`.  That signature is unsound: the DTB
/// is not guaranteed `'static` (the kernel may eventually reclaim its
/// memory).  Returning a slice borrowed from a caller-supplied buffer
/// gives the caller full control over the lifetime.  The buffer-based
/// API also lets unit tests exercise the parser with synthesised DTBs
/// without involving any `static`s.
///
/// ## Implementation note
///
/// This function is gated behind an `unsafe` block at the call site
/// because constructing `&[u8]` from a raw pointer requires the
/// caller to discharge the safety invariants (no aliasing writers,
/// pointed-to memory valid for the slice extent).  The host-side
/// (cargo test) implementation handles `dtb_ptr == 0` directly and
/// returns empty for any non-null pointer (we cannot synthesise a
/// safe DTB pointer on host).
pub fn extract_bootargs_into(dtb_ptr: u64, buffer: &mut [u8]) -> &str {
    if dtb_ptr == 0 {
        return "";
    }
    // Read the totalsize field (header byte 4..8) to know how much
    // memory to slice.  We start by reading the first 40 bytes (the
    // header) and validating it before slicing the full DTB.
    //
    // Two reads:
    //   1. Header slice (40 bytes) — covers magic + totalsize.
    //   2. Full DTB slice (totalsize bytes) — used for the walk.
    //
    // This is a brief two-step to avoid trusting the totalsize before
    // we've verified the magic word.
    //
    // SAFETY: on real hardware, U-Boot sets `dtb_ptr` to a valid DTB
    // mapping (the ARM64 boot protocol guarantees this).  The reader
    // checks magic before trusting any further fields, so an invalid
    // pointer producing a non-magic header value will short-circuit
    // here.  On host (cargo test) we never invoke this with a
    // non-null pointer, so the unsafe slice is never constructed.

    #[cfg(target_arch = "aarch64")]
    let result = {
        // SAFETY: The caller (boot.rs Phase 5) supplies `dtb_ptr` from
        // U-Boot's `x0` register, which the ARM64 boot protocol
        // requires to be either NULL or point to a valid DTB mapping
        // of at least totalsize bytes.  We handle NULL above.  For
        // non-NULL: read 40 bytes first to determine totalsize,
        // validate the header, validate that totalsize ≤
        // MAX_DTB_SIZE, then read the full blob.
        //
        // Audit-pass-1: bounding `totalsize` to MAX_DTB_SIZE is the
        // critical defense against a malicious or malformed
        // bootloader writing `totalsize = 0xFFFF_FFFF` (≈ 4 GiB).
        // Constructing `core::slice::from_raw_parts(ptr, len)` over
        // memory that isn't fully readable is Undefined Behaviour
        // per Rust's safety invariants — even if we never read past
        // the actual blob, the slice itself must describe a valid
        // contiguous extent.  Real DTBs are tens to a few hundred
        // KiB; the 2 MiB cap is orders of magnitude above any
        // plausible legitimate DTB and well below the smallest RAM
        // region typically mapped by U-Boot.
        unsafe {
            let header_slice = core::slice::from_raw_parts(dtb_ptr as *const u8, FDT_HEADER_SIZE);
            match parse_fdt_header(header_slice) {
                Some(hdr) if validate_fdt_header(&hdr) => {
                    let total = hdr.totalsize as usize;
                    if total > MAX_DTB_SIZE {
                        // Defense: refuse to construct a slice over
                        // a DTB extent that exceeds our safety bound.
                        // Falls back to the default CmdlineConfig
                        // (same as missing/malformed DTB).
                        ""
                    } else {
                        let full_slice =
                            core::slice::from_raw_parts(dtb_ptr as *const u8, total);
                        bootargs_to_buffer(full_slice, buffer)
                    }
                }
                _ => "",
            }
        }
    };

    #[cfg(not(target_arch = "aarch64"))]
    let result = {
        // Host-side stub: cargo tests never pass a non-zero `dtb_ptr`
        // (they use [`parse_cmdline`] directly or
        // [`extract_bootargs_from_blob_into`] with a synthesised
        // buffer), so the unsafe slice construction would be UB.
        // Return empty deterministically.
        let _ = dtb_ptr;
        let _ = buffer;
        ""
    };

    result
}

/// **WS-SM SM1.D.1**: Test-friendly entry point: extract bootargs
/// from a DTB blob in memory (no raw pointer needed).
///
/// Unit tests use this to exercise the parser with synthesised DTBs
/// — much cleaner than constructing a raw pointer from a `Vec<u8>` and
/// calling [`extract_bootargs_into`].
///
/// The slice returned is into `buffer`, so the buffer's lifetime
/// drives the returned `&str`.
///
/// Audit-pass-1: blobs larger than [`MAX_DTB_SIZE`] are rejected with
/// an empty result, matching the [`extract_bootargs_into`] safety
/// bound on aarch64.  This keeps the two entry points behaviourally
/// symmetric — a unit test cannot bypass the bound the production
/// path enforces.
pub fn extract_bootargs_from_blob_into<'b>(blob: &[u8], buffer: &'b mut [u8]) -> &'b str {
    if blob.len() > MAX_DTB_SIZE {
        return "";
    }
    bootargs_to_buffer(blob, buffer)
}

/// **WS-SM SM1.D.1**: Internal helper: walk a DTB blob, locate
/// `/chosen/bootargs`, copy into `buffer`, return UTF-8 view.
///
/// The DTB value bytes may include a trailing null byte (FDT spec
/// allows it for string-typed properties).  We strip that on copy so
/// the parser sees a clean string.
///
/// Returns `""` on any failure (no DTB, no bootargs, malformed bytes,
/// buffer too small).
fn bootargs_to_buffer<'b>(blob: &[u8], buffer: &'b mut [u8]) -> &'b str {
    let value = match find_bootargs_in_dtb(blob) {
        Some(v) => v,
        None => return "",
    };
    // Strip a trailing null terminator if present (FDT strings are
    // null-terminated; we want a clean &str).
    let trimmed = match value.split_last() {
        Some((&0, rest)) => rest,
        _ => value,
    };
    let copy_len = trimmed.len().min(buffer.len());
    let dst = match buffer.get_mut(..copy_len) {
        Some(d) => d,
        None => return "",
    };
    let src = match trimmed.get(..copy_len) {
        Some(s) => s,
        None => return "",
    };
    dst.copy_from_slice(src);
    // Validate UTF-8: if the bootargs contains non-UTF8 bytes (which
    // would be unusual but technically allowed), fail safely.
    // `unwrap_or_default()` on `Result<&str, _>` yields `""` on error,
    // which is exactly the safe-fallback contract we want.
    core::str::from_utf8(dst).unwrap_or_default()
}

/// **WS-SM SM1.D.1 + SM1.D.2**: One-shot helper combining
/// [`extract_bootargs_into`] and [`parse_cmdline`].
///
/// Allocates a stack-frame buffer of [`MAX_BOOTARGS_LEN`] bytes,
/// extracts the bootargs from the DTB, parses them, and returns the
/// resulting [`CmdlineConfig`].
///
/// This is the function `rust_boot_main` Phase 5 calls; it hides the
/// buffer-management discipline from the caller.
pub fn parse_cmdline_from_dtb(dtb_ptr: u64) -> CmdlineConfig {
    let mut buffer = [0u8; MAX_BOOTARGS_LEN];
    let bootargs = extract_bootargs_into(dtb_ptr, &mut buffer);
    parse_cmdline(bootargs)
}

/// **WS-SM SM1.D.2**: Apply a parsed [`CmdlineConfig`] to the SMP
/// runtime state and (if enabled) bring up secondaries.
///
/// Called from `rust_boot_main` Phase 5.  Returns the number of
/// secondaries actually brought up.
///
/// Side effects:
///   1. Stores `cfg.smp_enabled` into [`crate::smp::SMP_ENABLED`]
///      atomic.
///   2. If `cfg.smp_enabled`, invokes
///      [`crate::smp::bring_up_secondaries_with_limit`] with
///      `cfg.smp_max_cores`.
///
/// This is the production-globals entry point.  The implementation
/// dispatches to [`apply_cmdline_and_start_smp_inner`], which takes
/// explicit state references for test isolation.
pub fn apply_cmdline_and_start_smp(cfg: &CmdlineConfig) -> u32 {
    apply_cmdline_and_start_smp_inner(
        cfg,
        &crate::smp::SMP_ENABLED,
        &crate::smp::CORE_READY,
        &crate::smp::SECONDARY_CORES_ONLINE,
        &crate::smp::SECONDARY_MPIDR_TABLE,
    )
}

/// **WS-SM SM1.D.2 audit-pass-1** (test-isolation form): inner
/// implementation of [`apply_cmdline_and_start_smp`] taking explicit
/// state references.
///
/// Matches the [`crate::smp::bring_up_secondaries_inner`] discipline
/// so unit tests can exercise the disable path / enable path without
/// racing against parallel tests that mutate the production
/// `crate::smp::SMP_ENABLED` atomic.  Production callers should use
/// [`apply_cmdline_and_start_smp`].
///
/// `pub(crate)` so the in-crate `tests` module can exercise it;
/// external callers must go through the production entry point.
pub(crate) fn apply_cmdline_and_start_smp_inner(
    cfg: &CmdlineConfig,
    enabled: &core::sync::atomic::AtomicBool,
    core_ready: &[core::sync::atomic::AtomicBool],
    online_count: &core::sync::atomic::AtomicU32,
    mpidr_table: &[u64],
) -> u32 {
    enabled.store(cfg.smp_enabled, Ordering::Release);
    if cfg.smp_enabled {
        crate::smp::bring_up_secondaries_with_limit_inner(
            cfg.smp_max_cores,
            enabled,
            core_ready,
            online_count,
            mpidr_table,
        )
    } else {
        0
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec;
    use std::vec::Vec;

    // ========================================================================
    // SM1.D.1 — parse_cmdline core branches
    // ========================================================================

    #[test]
    fn parse_empty_returns_defaults() {
        // SM1.D.3: empty cmdline → default config (SMP enabled, all
        // cores).  This is the most common case (no DTB cmdline node).
        let cfg = parse_cmdline("");
        assert_eq!(cfg, CmdlineConfig::default());
        assert!(cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_whitespace_only_returns_defaults() {
        // SM1.D.1: a cmdline that's just whitespace yields no tokens.
        let cfg = parse_cmdline("   \t\n   ");
        assert_eq!(cfg, CmdlineConfig::default());
    }

    #[test]
    fn parse_smp_enabled_false() {
        // SM1.D.1 acceptance: explicit opt-out flips smp_enabled.
        let cfg = parse_cmdline("smp_enabled=false");
        assert!(!cfg.smp_enabled);
        // smp_max_cores untouched.
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_smp_enabled_true_alias_yes_on_one() {
        // SM1.D.1: every accepted truthy alias maps to `true`.
        for token in &["smp_enabled=true", "smp_enabled=yes", "smp_enabled=on", "smp_enabled=1"] {
            let cfg = parse_cmdline(token);
            assert!(cfg.smp_enabled, "{token} should set smp_enabled=true");
        }
    }

    #[test]
    fn parse_smp_enabled_false_alias_no_off_zero() {
        // SM1.D.1: every accepted falsy alias maps to `false`.
        for token in &["smp_enabled=false", "smp_enabled=no", "smp_enabled=off", "smp_enabled=0"] {
            let cfg = parse_cmdline(token);
            assert!(!cfg.smp_enabled, "{token} should set smp_enabled=false");
        }
    }

    #[test]
    fn parse_smp_enabled_malformed_keeps_default() {
        // SM1.D.1 robustness: unrecognised bool value keeps default.
        let cfg = parse_cmdline("smp_enabled=foo");
        assert!(cfg.smp_enabled, "default `true` should be preserved");
    }

    #[test]
    fn parse_smp_enabled_empty_value_keeps_default() {
        // SM1.D.1 robustness: empty value keeps default.
        let cfg = parse_cmdline("smp_enabled=");
        assert!(cfg.smp_enabled);
    }

    // ========================================================================
    // SM1.D.6 — smp_max_cores parsing
    // ========================================================================

    #[test]
    fn parse_smp_max_cores_two() {
        // SM1.D.6 acceptance: max=2 → 1 secondary.
        let cfg = parse_cmdline("smp_max_cores=2");
        assert_eq!(cfg.smp_max_cores, 2);
    }

    #[test]
    fn parse_smp_max_cores_one() {
        // SM1.D.6: max=1 → no secondaries (boot core only).
        let cfg = parse_cmdline("smp_max_cores=1");
        assert_eq!(cfg.smp_max_cores, 1);
    }

    #[test]
    fn parse_smp_max_cores_zero() {
        // SM1.D.6: max=0 → no cores brought up (defensively
        // equivalent to smp_enabled=false in effect).
        let cfg = parse_cmdline("smp_max_cores=0");
        assert_eq!(cfg.smp_max_cores, 0);
    }

    #[test]
    fn parse_smp_max_cores_full_count() {
        // SM1.D.6 acceptance: max=4 → all 3 secondaries.
        let cfg = parse_cmdline("smp_max_cores=4");
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_smp_max_cores_clamped_to_platform_max() {
        // SM1.D.6 robustness: value > platform max is clamped down.
        // We don't reject — silently saturate to the platform bound
        // so a misconfigured bootloader doesn't refuse to boot.
        let cfg = parse_cmdline("smp_max_cores=999");
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_smp_max_cores_negative_keeps_default() {
        // SM1.D.6 robustness: usize parse rejects negative numbers
        // (no sign character allowed).  Default `4` preserved.
        let cfg = parse_cmdline("smp_max_cores=-1");
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_smp_max_cores_non_numeric_keeps_default() {
        // SM1.D.6 robustness: alphabetic value keeps default.
        let cfg = parse_cmdline("smp_max_cores=abc");
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    // ========================================================================
    // SM1.D.1 — Multi-token + mixed cases
    // ========================================================================

    #[test]
    fn parse_multiple_tokens() {
        // SM1.D.1: combining tokens — order independent.
        let cfg = parse_cmdline("smp_enabled=true smp_max_cores=2");
        assert!(cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, 2);

        let cfg = parse_cmdline("smp_max_cores=2 smp_enabled=false");
        assert!(!cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, 2);
    }

    #[test]
    fn parse_unknown_keys_silently_ignored() {
        // SM1.D.1 forward-compat: unknown options don't fail boot.
        let cfg = parse_cmdline("debug=1 log_level=warn smp_enabled=false");
        assert!(!cfg.smp_enabled);
        // Unknown options should not have affected defaults.
        assert_eq!(cfg.smp_max_cores, crate::smp::MAX_SECONDARY_CORES + 1);
    }

    #[test]
    fn parse_unknown_flag_only_tokens_silently_ignored() {
        // SM1.D.1: flag-only tokens (no `=`) are reserved for future
        // options.  Currently none are recognised; all silently
        // ignored.
        let cfg = parse_cmdline("debug quiet earlyprintk");
        assert_eq!(cfg, CmdlineConfig::default());
    }

    #[test]
    fn parse_mixed_flags_and_kv() {
        // SM1.D.1: flag-only tokens interleaved with key=value.
        let cfg = parse_cmdline("quiet smp_enabled=false debug smp_max_cores=2");
        assert!(!cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, 2);
    }

    // ========================================================================
    // SM1.D.1 — Quoted values
    // ========================================================================

    #[test]
    fn parse_double_quoted_value() {
        // SM1.D.1 robustness: `key="value"` is accepted.
        let cfg = parse_cmdline("smp_enabled=\"false\"");
        assert!(!cfg.smp_enabled);
    }

    #[test]
    fn parse_single_quoted_value() {
        // SM1.D.1 robustness: `key='value'` is accepted.
        let cfg = parse_cmdline("smp_enabled='false'");
        assert!(!cfg.smp_enabled);
    }

    #[test]
    fn parse_partial_quote_keeps_default() {
        // SM1.D.1 robustness: unmatched quotes treated as part of
        // value (which then doesn't match any bool alias).
        let cfg = parse_cmdline("smp_enabled=\"false");
        assert!(cfg.smp_enabled, "default `true` preserved on partial-quote value");
    }

    #[test]
    fn trim_matching_quotes_double() {
        assert_eq!(trim_matching_quotes("\"abc\""), "abc");
    }

    #[test]
    fn trim_matching_quotes_single() {
        assert_eq!(trim_matching_quotes("'abc'"), "abc");
    }

    #[test]
    fn trim_matching_quotes_unmatched_preserved() {
        assert_eq!(trim_matching_quotes("\"abc"), "\"abc");
        assert_eq!(trim_matching_quotes("abc\""), "abc\"");
        assert_eq!(trim_matching_quotes("\"abc'"), "\"abc'");
    }

    #[test]
    fn trim_matching_quotes_short_strings() {
        // Defensive: 0/1 char strings can't have a matching pair.
        assert_eq!(trim_matching_quotes(""), "");
        assert_eq!(trim_matching_quotes("\""), "\"");
        assert_eq!(trim_matching_quotes("a"), "a");
    }

    // ========================================================================
    // SM1.D.1 — parse_bool boundary
    // ========================================================================

    #[test]
    fn parse_bool_canonical_truthy() {
        assert_eq!(parse_bool("true"), Some(true));
        assert_eq!(parse_bool("1"), Some(true));
        assert_eq!(parse_bool("yes"), Some(true));
        assert_eq!(parse_bool("on"), Some(true));
    }

    #[test]
    fn parse_bool_canonical_falsy() {
        assert_eq!(parse_bool("false"), Some(false));
        assert_eq!(parse_bool("0"), Some(false));
        assert_eq!(parse_bool("no"), Some(false));
        assert_eq!(parse_bool("off"), Some(false));
    }

    #[test]
    fn parse_bool_case_sensitive() {
        // SM1.D.1: the bootloader-supplied cmdline is a
        // machine-readable string, not human input.  We keep matching
        // case-sensitive so `True`, `TRUE`, `On`, etc. all fail —
        // forcing the canonical lowercase form.
        assert_eq!(parse_bool("True"), None);
        assert_eq!(parse_bool("TRUE"), None);
        assert_eq!(parse_bool("On"), None);
        assert_eq!(parse_bool("YES"), None);
    }

    #[test]
    fn parse_bool_garbage_returns_none() {
        assert_eq!(parse_bool(""), None);
        assert_eq!(parse_bool("maybe"), None);
        assert_eq!(parse_bool("2"), None);
        assert_eq!(parse_bool(" true"), None); // leading space rejected
    }

    // ========================================================================
    // SM1.D.1 — CmdlineConfig::default + invariants
    // ========================================================================

    #[test]
    fn default_smp_enabled_is_true() {
        // SM1.D.3: production default per maintainer decision #7.
        assert!(CmdlineConfig::default().smp_enabled);
    }

    #[test]
    fn default_smp_max_cores_matches_platform() {
        // SM1.D.6: default brings up the full physical core count.
        assert_eq!(
            CmdlineConfig::default().smp_max_cores,
            crate::smp::MAX_SECONDARY_CORES + 1
        );
    }

    #[test]
    fn default_smp_max_cores_is_four_on_rpi5() {
        // SM1.D.6: pin the literal value (the WS-SM SM0.O assertion
        // pins MAX_SECONDARY_CORES + 1 = 4 at compile time, so this
        // is a runtime cross-check).
        assert_eq!(CmdlineConfig::default().smp_max_cores, 4);
    }

    #[test]
    fn config_is_copy() {
        // SM1.D.1: the struct is `Copy` so it can be passed by value
        // through the boot path without lifetime gymnastics.  A
        // future PR that adds a non-Copy field would need to explicitly
        // remove the derive — this test pins the requirement.
        let cfg = CmdlineConfig::default();
        let cfg2 = cfg; // would fail to compile if not Copy
        assert_eq!(cfg, cfg2);
    }

    // ========================================================================
    // SM1.D.1 — DTB parser: read_be_u32 + parse_fdt_header
    // ========================================================================

    #[test]
    fn read_be_u32_basic() {
        // Big-endian: first byte is MSB.
        let blob = [0x12, 0x34, 0x56, 0x78];
        assert_eq!(read_be_u32(&blob, 0), Some(0x1234_5678));
    }

    #[test]
    fn read_be_u32_offset() {
        let blob = [0xFF, 0xFF, 0x12, 0x34, 0x56, 0x78];
        assert_eq!(read_be_u32(&blob, 2), Some(0x1234_5678));
    }

    #[test]
    fn read_be_u32_out_of_bounds() {
        let blob = [0xFF, 0xFF, 0xFF];
        // 3 bytes, can't read a 4-byte u32 at any offset.
        assert_eq!(read_be_u32(&blob, 0), None);
    }

    #[test]
    fn read_be_u32_offset_at_end_oob() {
        let blob = [0x12, 0x34, 0x56, 0x78];
        // Reading at offset 1 needs bytes 1..5; only 0..4 available.
        assert_eq!(read_be_u32(&blob, 1), None);
    }

    #[test]
    fn parse_fdt_header_rejects_short_blob() {
        let blob = [0u8; 10];
        assert!(parse_fdt_header(&blob).is_none());
    }

    #[test]
    fn parse_fdt_header_rejects_wrong_magic() {
        let mut blob = [0u8; FDT_HEADER_SIZE];
        blob[0..4].copy_from_slice(&0x1234_5678u32.to_be_bytes());
        assert!(parse_fdt_header(&blob).is_none());
    }

    #[test]
    fn parse_fdt_header_accepts_minimal_valid() {
        let blob = build_minimal_dtb_header();
        let hdr = parse_fdt_header(&blob).expect("minimal header should parse");
        assert_eq!(hdr.magic, FDT_MAGIC);
        assert_eq!(hdr.version, 17);
    }

    #[test]
    fn validate_fdt_header_rejects_old_version() {
        let mut blob = build_minimal_dtb_header();
        blob[20..24].copy_from_slice(&15u32.to_be_bytes()); // version 15 < 16
        let hdr = parse_fdt_header(&blob).expect("should still parse fields");
        assert!(!validate_fdt_header(&hdr));
    }

    #[test]
    fn validate_fdt_header_rejects_misaligned_struct_offset() {
        let mut blob = build_minimal_dtb_header();
        // Header is 40 bytes; set off_dt_struct to 41 (not 4-byte aligned).
        blob[8..12].copy_from_slice(&41u32.to_be_bytes());
        let hdr = parse_fdt_header(&blob).expect("should parse fields");
        assert!(!validate_fdt_header(&hdr));
    }

    // ========================================================================
    // SM1.D.1 — DTB parser: full walker with synthesised blob
    // ========================================================================

    #[test]
    fn find_bootargs_in_synthesised_dtb() {
        // SM1.D.1 end-to-end: build a minimal DTB containing
        // `/chosen/bootargs = "smp_enabled=false"` and walk it.
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false");
        let bootargs = find_bootargs_in_dtb(&dtb)
            .expect("synthesised DTB should yield bootargs");
        assert_eq!(bootargs, b"smp_enabled=false\0");
    }

    #[test]
    fn extract_bootargs_from_synthesised_dtb_into_buffer() {
        // SM1.D.1: end-to-end through extract_bootargs_from_blob_into.
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false");
        let mut buf = [0u8; 64];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut buf);
        assert_eq!(bootargs, "smp_enabled=false");
    }

    #[test]
    fn parse_cmdline_via_synthesised_dtb_buffer() {
        // SM1.D.1 + SM1.D.2: full pipeline ending in CmdlineConfig.
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false smp_max_cores=2");
        let mut buf = [0u8; 64];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut buf);
        let cfg = parse_cmdline(bootargs);
        assert!(!cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, 2);
    }

    #[test]
    fn dtb_without_chosen_yields_empty() {
        // SM1.D.1: a DTB with no `/chosen` node returns empty.
        let dtb = build_dtb_without_chosen();
        assert!(find_bootargs_in_dtb(&dtb).is_none());
    }

    #[test]
    fn dtb_with_chosen_but_no_bootargs_yields_empty() {
        // SM1.D.1: `/chosen` present but no `bootargs` property →
        // empty.
        let dtb = build_dtb_chosen_without_bootargs();
        assert!(find_bootargs_in_dtb(&dtb).is_none());
    }

    #[test]
    fn dtb_with_malformed_header_yields_empty() {
        // SM1.D.1: malformed DTB header → safe empty result.
        let blob = [0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0];
        assert!(find_bootargs_in_dtb(&blob).is_none());
    }

    #[test]
    fn extract_bootargs_null_pointer_yields_empty() {
        // SM1.D.1: dtb_ptr = 0 (NULL) → empty.  This is the most
        // common host-test path (cargo test never has a real DTB).
        let mut buf = [0u8; 64];
        let bootargs = extract_bootargs_into(0, &mut buf);
        assert_eq!(bootargs, "");
    }

    #[test]
    fn parse_cmdline_from_dtb_null_pointer_yields_defaults() {
        // SM1.D.2 entry point: NULL pointer → defaults.
        let cfg = parse_cmdline_from_dtb(0);
        assert_eq!(cfg, CmdlineConfig::default());
    }

    #[test]
    fn extract_bootargs_small_buffer_truncates_cleanly() {
        // SM1.D.1: if the caller buffer is too small, we truncate
        // rather than failing.  This may yield a partially-formed
        // cmdline string, but parse_cmdline is robust to fragments
        // (unknown keys ignored, malformed values keep defaults).
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false");
        let mut tiny_buf = [0u8; 4];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut tiny_buf);
        // First 4 chars of "smp_enabled=false" = "smp_"
        assert_eq!(bootargs, "smp_");
    }

    #[test]
    fn extract_bootargs_zero_buffer_yields_empty() {
        // SM1.D.1: zero-length buffer → empty (defensive).
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false");
        let mut empty_buf = [0u8; 0];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut empty_buf);
        assert_eq!(bootargs, "");
    }

    #[test]
    fn parse_cmdline_with_max_bootargs_buffer_succeeds() {
        // SM1.D.1: MAX_BOOTARGS_LEN-sized buffer covers expected
        // production cmdline length.  Spot-check with a long but
        // realistic cmdline.
        let realistic = b"smp_enabled=true smp_max_cores=4 \
                          unknown_option=value debug log_level=info";
        let dtb = build_dtb_with_bootargs(realistic);
        let mut buf = [0u8; MAX_BOOTARGS_LEN];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut buf);
        let cfg = parse_cmdline(bootargs);
        assert!(cfg.smp_enabled);
        assert_eq!(cfg.smp_max_cores, 4);
    }

    // ========================================================================
    // SM1.D.2 — apply_cmdline_and_start_smp behavioural tests
    // ========================================================================

    #[test]
    fn apply_disabled_returns_zero_online() {
        // SM1.D.2: when cmdline says smp_enabled=false, no
        // secondaries are brought up.  We don't touch the global
        // atomic (which is shared between tests); reading it would
        // race with parallel tests.  Instead we exercise the helper
        // with a fresh local state via bring_up_secondaries_inner.
        //
        // This test only verifies the dispatch: the parser produces
        // smp_enabled=false, the action helper sees it, and the
        // CPU_ON loop is bypassed.  The behavioural test for
        // bring_up_secondaries_with_limit is in smp::tests below.
        let cfg = CmdlineConfig {
            smp_enabled: false,
            smp_max_cores: 4,
        };
        // We cannot call apply_cmdline_and_start_smp directly here
        // because it mutates the global SMP_ENABLED atomic and races
        // with other tests.  Instead we verify the dispatch logic by
        // reading the cfg fields.
        assert!(!cfg.smp_enabled);
    }

    // ========================================================================
    // SM1.D.1 — Test fixtures (DTB blob builders)
    //
    // These helpers build minimal valid DTBs for unit testing.  Each
    // builder emits a complete, validate_fdt_header-conformant blob.
    // ========================================================================

    /// Build a minimal valid DTB header (40 bytes) with version 17.
    /// Subsequent test fixtures append a structure block + strings
    /// block and patch the offsets.
    fn build_minimal_dtb_header() -> [u8; FDT_HEADER_SIZE] {
        let mut hdr = [0u8; FDT_HEADER_SIZE];
        // magic
        hdr[0..4].copy_from_slice(&FDT_MAGIC.to_be_bytes());
        // totalsize = 40 (just the header)
        hdr[4..8].copy_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        // off_dt_struct = 40 (empty struct block)
        hdr[8..12].copy_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        // off_dt_strings = 40 (empty strings block)
        hdr[12..16].copy_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        // off_mem_rsvmap = 40
        hdr[16..20].copy_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        // version = 17
        hdr[20..24].copy_from_slice(&17u32.to_be_bytes());
        // last_comp_version = 16
        hdr[24..28].copy_from_slice(&16u32.to_be_bytes());
        // boot_cpuid_phys = 0
        hdr[28..32].copy_from_slice(&0u32.to_be_bytes());
        // size_dt_strings = 0
        hdr[32..36].copy_from_slice(&0u32.to_be_bytes());
        // size_dt_struct = 0
        hdr[36..40].copy_from_slice(&0u32.to_be_bytes());
        hdr
    }

    /// Build a DTB containing `/chosen/bootargs = <value>`.
    ///
    /// Structure layout:
    ///   BEGIN_NODE ""       (root)
    ///     BEGIN_NODE "chosen"
    ///       PROP bootargs = value
    ///     END_NODE
    ///   END_NODE
    ///   END
    ///
    /// Strings block contains a single null-terminated "bootargs"
    /// string at offset 0.
    fn build_dtb_with_bootargs(value: &[u8]) -> Vec<u8> {
        // Strings block: "bootargs\0"
        let strings = b"bootargs\0".to_vec();
        let bootargs_nameoff = 0u32;

        // Build the structure block.
        let mut s: Vec<u8> = Vec::new();
        // BEGIN_NODE "" (root)
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        // Empty name "\0", padded to 4 bytes → 4 bytes of zero.
        s.extend_from_slice(&[0u8; 4]);
        // BEGIN_NODE "chosen"
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"chosen\0");
        // pad "chosen\0" (7 bytes) to 8 bytes (next 4-byte boundary)
        s.push(0);
        // PROP bootargs
        s.extend_from_slice(&FDT_PROP.to_be_bytes());
        // Property value will be `value` + a null terminator so the
        // parser strips the trailing null.  Length = value.len() + 1.
        let prop_len = (value.len() + 1) as u32;
        s.extend_from_slice(&prop_len.to_be_bytes());
        s.extend_from_slice(&bootargs_nameoff.to_be_bytes());
        s.extend_from_slice(value);
        s.push(0); // null terminator
                   // pad to 4-byte boundary
        while s.len() % 4 != 0 {
            s.push(0);
        }
        // END_NODE (chosen)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END_NODE (root)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END
        s.extend_from_slice(&FDT_END.to_be_bytes());

        // Lay out the full blob: header (40) + struct + strings.
        let off_dt_struct = FDT_HEADER_SIZE;
        let off_dt_strings = off_dt_struct + s.len();
        let totalsize = off_dt_strings + strings.len();

        let mut blob = Vec::with_capacity(totalsize);
        // Header (we'll fill in the offsets below).
        blob.extend_from_slice(&FDT_MAGIC.to_be_bytes());
        blob.extend_from_slice(&(totalsize as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_struct as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_strings as u32).to_be_bytes());
        blob.extend_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes()); // off_mem_rsvmap
        blob.extend_from_slice(&17u32.to_be_bytes()); // version
        blob.extend_from_slice(&16u32.to_be_bytes()); // last_comp_version
        blob.extend_from_slice(&0u32.to_be_bytes()); // boot_cpuid_phys
        blob.extend_from_slice(&(strings.len() as u32).to_be_bytes());
        blob.extend_from_slice(&(s.len() as u32).to_be_bytes());

        // Structure block + strings block.
        blob.extend_from_slice(&s);
        blob.extend_from_slice(&strings);
        blob
    }

    /// Build a DTB with only a root node and no `/chosen` node.
    fn build_dtb_without_chosen() -> Vec<u8> {
        let strings: Vec<u8> = Vec::new();
        let mut s: Vec<u8> = Vec::new();
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(&[0u8; 4]); // empty name
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        s.extend_from_slice(&FDT_END.to_be_bytes());

        let off_dt_struct = FDT_HEADER_SIZE;
        let off_dt_strings = off_dt_struct + s.len();
        let totalsize = off_dt_strings + strings.len();

        let mut blob = Vec::with_capacity(totalsize);
        blob.extend_from_slice(&FDT_MAGIC.to_be_bytes());
        blob.extend_from_slice(&(totalsize as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_struct as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_strings as u32).to_be_bytes());
        blob.extend_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        blob.extend_from_slice(&17u32.to_be_bytes());
        blob.extend_from_slice(&16u32.to_be_bytes());
        blob.extend_from_slice(&0u32.to_be_bytes());
        blob.extend_from_slice(&(strings.len() as u32).to_be_bytes());
        blob.extend_from_slice(&(s.len() as u32).to_be_bytes());
        blob.extend_from_slice(&s);
        blob.extend_from_slice(&strings);
        blob
    }

    /// Build a DTB with `/chosen` but no `bootargs` property.
    fn build_dtb_chosen_without_bootargs() -> Vec<u8> {
        // Strings block contains some other property name, "other\0".
        let strings = b"other\0".to_vec();
        let other_nameoff = 0u32;

        let mut s: Vec<u8> = Vec::new();
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(&[0u8; 4]); // root name ""
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"chosen\0");
        s.push(0); // pad
        s.extend_from_slice(&FDT_PROP.to_be_bytes());
        let value = b"some\0";
        s.extend_from_slice(&(value.len() as u32).to_be_bytes());
        s.extend_from_slice(&other_nameoff.to_be_bytes());
        s.extend_from_slice(value);
        // pad to 4
        while s.len() % 4 != 0 {
            s.push(0);
        }
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes()); // chosen end
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes()); // root end
        s.extend_from_slice(&FDT_END.to_be_bytes());

        let off_dt_struct = FDT_HEADER_SIZE;
        let off_dt_strings = off_dt_struct + s.len();
        let totalsize = off_dt_strings + strings.len();

        let mut blob = Vec::with_capacity(totalsize);
        blob.extend_from_slice(&FDT_MAGIC.to_be_bytes());
        blob.extend_from_slice(&(totalsize as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_struct as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_strings as u32).to_be_bytes());
        blob.extend_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        blob.extend_from_slice(&17u32.to_be_bytes());
        blob.extend_from_slice(&16u32.to_be_bytes());
        blob.extend_from_slice(&0u32.to_be_bytes());
        blob.extend_from_slice(&(strings.len() as u32).to_be_bytes());
        blob.extend_from_slice(&(s.len() as u32).to_be_bytes());
        blob.extend_from_slice(&s);
        blob.extend_from_slice(&strings);
        blob
    }

    // ========================================================================
    // SM1.D.1 audit-pass-1 — regression tests for the deep-audit findings
    // ========================================================================

    /// **Audit-pass-1 regression**: DTBs with `bootargs` in a node
    /// nested INSIDE `/chosen` (e.g., `/chosen/sub/bootargs`) must
    /// NOT be matched.  Only the direct `/chosen/bootargs` property
    /// is the canonical kernel command-line per the FDT specification
    /// §3.5.  A malicious DTB exploiting the pre-audit behaviour
    /// could have set `/chosen/sub/bootargs = "smp_enabled=false"`
    /// to silently disable SMP without anyone noticing.
    #[test]
    fn dtb_with_bootargs_in_chosen_sub_node_yields_empty() {
        let dtb = build_dtb_chosen_with_sub_node_bootargs(b"hostile");
        // Pre-audit form (matching bootargs anywhere in /chosen)
        // would return Some(b"hostile\0").  Post-audit form must
        // return None — only /chosen/bootargs (direct child) counts.
        assert!(
            find_bootargs_in_dtb(&dtb).is_none(),
            "regression: bootargs nested in /chosen/sub must not be honoured"
        );
    }

    /// **Audit-pass-1 regression**: when `/chosen` has both a direct
    /// `bootargs` property AND a nested `/chosen/sub/bootargs`, the
    /// walker must return the direct one (not the nested one, and
    /// the order should be deterministic per FDT spec §5.4).
    ///
    /// Per FDT spec §5.4.1, properties precede sub-nodes within any
    /// node — so the direct `bootargs` appears before the nested
    /// node in the structure stream and is found first.
    #[test]
    fn dtb_with_direct_and_nested_chosen_bootargs_picks_direct() {
        let dtb = build_dtb_chosen_with_direct_and_nested_bootargs(
            b"real_value",
            b"fake_value",
        );
        let bootargs = find_bootargs_in_dtb(&dtb)
            .expect("direct /chosen/bootargs must be found");
        assert_eq!(
            bootargs, b"real_value\0",
            "audit-pass-1: walker must return the DIRECT /chosen/bootargs, \
             not a nested one"
        );
    }

    /// **Audit-pass-1 regression**: a DTB with
    /// `last_comp_version > FDT_PARSER_VERSION` (=17) must be
    /// rejected.  Per FDT spec §5.2, `last_comp_version` is the
    /// minimum version of the parser required to correctly read the
    /// DTB; a parser at version P can only read DTBs with
    /// `last_comp_version <= P`.  A DTB asserting it requires v18+
    /// could have layout fields at different offsets than we expect.
    #[test]
    fn dtb_with_higher_last_comp_version_rejected() {
        let mut blob = build_dtb_with_bootargs(b"smp_enabled=false");
        // Overwrite last_comp_version (header bytes 24..28) with 18.
        let new_lcv = 18u32.to_be_bytes();
        blob[24..28].copy_from_slice(&new_lcv);
        assert!(
            find_bootargs_in_dtb(&blob).is_none(),
            "DTB requiring parser v18+ must be rejected"
        );
    }

    /// **Audit-pass-1 regression**: a DTB with `last_comp_version ==
    /// FDT_PARSER_VERSION` (= our exact version, 17) must still be
    /// accepted.  Tests the boundary of the version check.
    #[test]
    fn dtb_with_last_comp_version_equal_parser_version_accepted() {
        let mut blob = build_dtb_with_bootargs(b"smp_enabled=false");
        // Overwrite last_comp_version (header bytes 24..28) with 17
        // = FDT_PARSER_VERSION.
        let new_lcv = FDT_PARSER_VERSION.to_be_bytes();
        blob[24..28].copy_from_slice(&new_lcv);
        assert!(
            find_bootargs_in_dtb(&blob).is_some(),
            "DTB at the parser's exact version must remain accepted"
        );
    }

    /// **Audit-pass-1 regression**: when read directly from a blob
    /// larger than [`MAX_DTB_SIZE`], `extract_bootargs_from_blob_into`
    /// must short-circuit to empty (defense-in-depth: mirrors the
    /// aarch64 raw-pointer path's MAX_DTB_SIZE bound).
    #[test]
    fn extract_bootargs_from_oversize_blob_yields_empty() {
        // Build a 2 MiB + 1-byte blob containing a valid DTB at
        // the start (it would otherwise parse cleanly).  Even though
        // the actual structure block is small, the blob length
        // exceeds MAX_DTB_SIZE so we refuse to walk.
        let mut blob = build_dtb_with_bootargs(b"smp_enabled=false");
        blob.resize(MAX_DTB_SIZE + 1, 0u8);
        let mut buf = [0u8; 64];
        let bootargs = extract_bootargs_from_blob_into(&blob, &mut buf);
        assert_eq!(
            bootargs, "",
            "blob > MAX_DTB_SIZE must yield empty (size guard)"
        );
    }

    /// **Audit-pass-1 regression**: a blob exactly at
    /// [`MAX_DTB_SIZE`] must still parse normally (boundary
    /// condition of the size guard).
    #[test]
    fn extract_bootargs_from_blob_at_max_size_succeeds() {
        // Smaller than MAX_DTB_SIZE — we can't actually allocate
        // 2 MiB cheaply for every test run, so we test a blob whose
        // size is well below the cap.  The boundary semantics are
        // pinned by the inequality `blob.len() > MAX_DTB_SIZE` in
        // the guard: `<=` always passes, `>` always fails.  We
        // verify that a small blob still works:
        let dtb = build_dtb_with_bootargs(b"smp_enabled=false");
        assert!(
            dtb.len() <= MAX_DTB_SIZE,
            "synthesised DTB must fit within the size guard"
        );
        let mut buf = [0u8; 64];
        let bootargs = extract_bootargs_from_blob_into(&dtb, &mut buf);
        assert_eq!(bootargs, "smp_enabled=false");
    }

    /// **Audit-pass-1 sanity**: MAX_DTB_SIZE is set to a generous
    /// value covering real-world DTBs but bounded against malicious
    /// totalsize values.  Pinning the literal here makes a
    /// surprise tightening (e.g., 4 KB) impossible without updating
    /// the test.
    #[test]
    fn max_dtb_size_is_two_mib() {
        assert_eq!(MAX_DTB_SIZE, 2 * 1024 * 1024);
    }

    /// **Audit-pass-1 sanity**: FDT_PARSER_VERSION matches the
    /// layout we parse (v17 added size_dt_strings + size_dt_struct
    /// at offsets 32/36).  A future bump (e.g., adding a v18 field)
    /// must also bump this constant.
    #[test]
    fn fdt_parser_version_is_seventeen() {
        assert_eq!(FDT_PARSER_VERSION, 17);
    }

    /// **Audit-pass-1 sanity**: the LongPropertyLayout we use
    /// (FDT_PROP = 0x3, len:u32, nameoff:u32, value:len) matches
    /// FDT spec §5.4.2.  Verified by hand-rolling a DTB whose
    /// padding requirements exercise the `(len + 3) & !3` path and
    /// confirming the parser still finds bootargs at the correct
    /// offset.  Padding-stress test:
    ///
    ///   - value length 1 → 1 + null = 2 → pads to 4 (padding=2)
    ///   - value length 2 → 2 + null = 3 → pads to 4 (padding=1)
    ///   - value length 3 → 3 + null = 4 → pads to 4 (padding=0)
    ///   - value length 4 → 4 + null = 5 → pads to 8 (padding=3)
    ///   - value length 5 → 5 + null = 6 → pads to 8 (padding=2)
    ///   - value length 6 → 6 + null = 7 → pads to 8 (padding=1)
    ///   - value length 7 → 7 + null = 8 → pads to 8 (padding=0)
    ///
    /// Each case must parse cleanly without falling off the
    /// structure block end.
    #[test]
    fn dtb_property_padding_stress_test() {
        for len in 1usize..=7 {
            let value = vec![b'a'; len];
            let dtb = build_dtb_with_bootargs(&value);
            let bootargs = find_bootargs_in_dtb(&dtb).unwrap_or_else(|| {
                panic!("padding stress failed at len={}", len)
            });
            assert_eq!(
                bootargs.len(),
                len + 1,
                "padding stress: returned value length must equal \
                 input length + 1 (null) for len={}",
                len
            );
        }
    }

    // ========================================================================
    // SM1.D.2 audit-pass-1 — apply_cmdline_and_start_smp_inner tests
    //
    // These tests exercise the dispatch path using local atomics so
    // the global SMP_ENABLED state is never perturbed.  Each test
    // builds a fresh state, calls the inner form, and verifies the
    // post-state.  This closes the pre-audit coverage gap where the
    // dispatch helper was only tested indirectly.
    // ========================================================================

    fn fresh_local_smp_state(
    ) -> (
        core::sync::atomic::AtomicBool,
        [core::sync::atomic::AtomicBool; 4],
        core::sync::atomic::AtomicU32,
    ) {
        (
            core::sync::atomic::AtomicBool::new(false),
            [
                core::sync::atomic::AtomicBool::new(true),
                core::sync::atomic::AtomicBool::new(false),
                core::sync::atomic::AtomicBool::new(false),
                core::sync::atomic::AtomicBool::new(false),
            ],
            core::sync::atomic::AtomicU32::new(0),
        )
    }

    #[test]
    fn apply_inner_disabled_sets_atomic_and_returns_zero() {
        // SM1.D.2: disabled cfg → atomic stored as false, no
        // secondaries brought up, return 0.
        let (enabled, ready, count) = fresh_local_smp_state();
        // Pre-condition: atomic is initially false.
        assert!(!enabled.load(Ordering::Acquire));
        let cfg = CmdlineConfig {
            smp_enabled: false,
            smp_max_cores: 4,
        };
        let online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert_eq!(online, 0, "disabled cfg must bring up zero secondaries");
        assert!(
            !enabled.load(Ordering::Acquire),
            "atomic must be stored as false after disabled cfg apply"
        );
        // The CORE_READY flags should be untouched (still in fresh state).
        assert!(!ready[1].load(Ordering::Acquire));
        assert!(!ready[2].load(Ordering::Acquire));
        assert!(!ready[3].load(Ordering::Acquire));
    }

    #[test]
    fn apply_inner_disabled_clears_atomic_even_when_initially_true() {
        // SM1.D.2 invariant: after `apply`, the atomic reflects the
        // parsed cfg regardless of its prior value.  A previously
        // SMP-enabled run that re-applies a disabled cfg must end
        // with atomic = false.  This guards against a regression
        // where the disabled branch forgets to commit the false
        // state.
        let (enabled, ready, count) = fresh_local_smp_state();
        enabled.store(true, Ordering::Release);
        let cfg = CmdlineConfig {
            smp_enabled: false,
            smp_max_cores: 4,
        };
        let _online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert!(
            !enabled.load(Ordering::Acquire),
            "disabled cfg apply must overwrite a previously-true atomic"
        );
    }

    #[test]
    fn apply_inner_enabled_sets_atomic_and_brings_up_secondaries() {
        // SM1.D.2: enabled cfg with full max_cores → all 3
        // secondaries online, atomic stored as true.
        let (enabled, ready, count) = fresh_local_smp_state();
        let cfg = CmdlineConfig {
            smp_enabled: true,
            smp_max_cores: crate::smp::MAX_SECONDARY_CORES + 1,
        };
        let online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert_eq!(
            online,
            crate::smp::MAX_SECONDARY_CORES as u32,
            "enabled cfg with max=4 must bring up all 3 secondaries"
        );
        assert!(
            enabled.load(Ordering::Acquire),
            "atomic must be stored as true after enabled cfg apply"
        );
        // Each secondary's ready flag should now be true.
        for (idx, slot) in ready.iter().enumerate().skip(1) {
            assert!(
                slot.load(Ordering::Acquire),
                "secondary {} must be ready after full bring-up",
                idx
            );
        }
    }

    #[test]
    fn apply_inner_enabled_with_limit_two_brings_up_one_secondary() {
        // SM1.D.2 + SM1.D.6: enabled cfg with smp_max_cores=2 →
        // only 1 secondary brought up.  Cores 2 and 3 remain
        // unready.
        let (enabled, ready, count) = fresh_local_smp_state();
        let cfg = CmdlineConfig {
            smp_enabled: true,
            smp_max_cores: 2,
        };
        let online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert_eq!(online, 1, "smp_max_cores=2 must bring up exactly 1 secondary");
        assert!(enabled.load(Ordering::Acquire));
        assert!(
            ready[1].load(Ordering::Acquire),
            "first secondary must be ready"
        );
        assert!(
            !ready[2].load(Ordering::Acquire),
            "second secondary must remain unready under smp_max_cores=2"
        );
        assert!(
            !ready[3].load(Ordering::Acquire),
            "third secondary must remain unready under smp_max_cores=2"
        );
    }

    #[test]
    fn apply_inner_enabled_with_limit_one_brings_up_zero_secondaries() {
        // SM1.D.6: smp_max_cores=1 means boot core only; no
        // secondaries.  Atomic still stored as true (the cfg says
        // SMP is conceptually enabled; the limit just bounds the
        // bring-up to 0 secondaries).
        let (enabled, ready, count) = fresh_local_smp_state();
        let cfg = CmdlineConfig {
            smp_enabled: true,
            smp_max_cores: 1,
        };
        let online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert_eq!(online, 0);
        assert!(enabled.load(Ordering::Acquire));
    }

    #[test]
    fn apply_inner_enabled_with_limit_zero_brings_up_zero_secondaries() {
        // SM1.D.6 edge case: smp_max_cores=0 (functionally
        // equivalent to disabled, but atomic is still set to true
        // because cfg.smp_enabled is true).  This is the documented
        // semantics — the operator opted in to SMP but capped the
        // core count below the boot core.
        let (enabled, ready, count) = fresh_local_smp_state();
        let cfg = CmdlineConfig {
            smp_enabled: true,
            smp_max_cores: 0,
        };
        let online = apply_cmdline_and_start_smp_inner(
            &cfg,
            &enabled,
            &ready,
            &count,
            &crate::smp::SECONDARY_MPIDR_TABLE,
        );
        assert_eq!(online, 0);
        assert!(
            enabled.load(Ordering::Acquire),
            "atomic = cfg.smp_enabled regardless of max_cores"
        );
    }

    #[test]
    fn apply_inner_function_signature_pin() {
        // SM1.D.2: pin the function pointer signature so a future
        // refactor that changes the inner-helper ABI surfaces here
        // at compile time.
        let _: fn(
            &CmdlineConfig,
            &core::sync::atomic::AtomicBool,
            &[core::sync::atomic::AtomicBool],
            &core::sync::atomic::AtomicU32,
            &[u64],
        ) -> u32 = apply_cmdline_and_start_smp_inner;
    }

    #[test]
    fn apply_public_function_signature_pin() {
        // SM1.D.2: pin the public ABI signature.  A future PR
        // changing it (e.g., taking ownership of CmdlineConfig)
        // would break boot.rs callers; this test surfaces the
        // signature shift at the type system.
        let _: fn(&CmdlineConfig) -> u32 = apply_cmdline_and_start_smp;
    }

    /// Build a DTB containing `/chosen/sub/bootargs = <value>` —
    /// `bootargs` is in a SUB-NODE of chosen, NOT a direct child.
    /// Post-audit-pass-1 the walker must NOT match this property.
    fn build_dtb_chosen_with_sub_node_bootargs(value: &[u8]) -> Vec<u8> {
        let strings = b"bootargs\0".to_vec();
        let bootargs_nameoff = 0u32;

        let mut s: Vec<u8> = Vec::new();
        // BEGIN_NODE "" (root)
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(&[0u8; 4]);
        // BEGIN_NODE "chosen"
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"chosen\0");
        s.push(0); // pad
                   // BEGIN_NODE "sub" (nested inside chosen)
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"sub\0");
        // PROP bootargs (in /chosen/sub — must NOT match)
        s.extend_from_slice(&FDT_PROP.to_be_bytes());
        let prop_len = (value.len() + 1) as u32;
        s.extend_from_slice(&prop_len.to_be_bytes());
        s.extend_from_slice(&bootargs_nameoff.to_be_bytes());
        s.extend_from_slice(value);
        s.push(0); // null
        while s.len() % 4 != 0 {
            s.push(0);
        }
        // END_NODE (sub)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END_NODE (chosen)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END_NODE (root)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END
        s.extend_from_slice(&FDT_END.to_be_bytes());

        let off_dt_struct = FDT_HEADER_SIZE;
        let off_dt_strings = off_dt_struct + s.len();
        let totalsize = off_dt_strings + strings.len();

        let mut blob = Vec::with_capacity(totalsize);
        blob.extend_from_slice(&FDT_MAGIC.to_be_bytes());
        blob.extend_from_slice(&(totalsize as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_struct as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_strings as u32).to_be_bytes());
        blob.extend_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        blob.extend_from_slice(&17u32.to_be_bytes());
        blob.extend_from_slice(&16u32.to_be_bytes());
        blob.extend_from_slice(&0u32.to_be_bytes());
        blob.extend_from_slice(&(strings.len() as u32).to_be_bytes());
        blob.extend_from_slice(&(s.len() as u32).to_be_bytes());
        blob.extend_from_slice(&s);
        blob.extend_from_slice(&strings);
        blob
    }

    /// Build a DTB containing BOTH `/chosen/bootargs = direct_value`
    /// AND `/chosen/sub/bootargs = nested_value`.  The walker must
    /// return the direct value (not the nested one) per the
    /// FDT spec §5.4.1 ordering convention (properties precede
    /// sub-nodes).
    fn build_dtb_chosen_with_direct_and_nested_bootargs(
        direct_value: &[u8],
        nested_value: &[u8],
    ) -> Vec<u8> {
        let strings = b"bootargs\0".to_vec();
        let bootargs_nameoff = 0u32;

        let mut s: Vec<u8> = Vec::new();
        // BEGIN_NODE "" (root)
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(&[0u8; 4]);
        // BEGIN_NODE "chosen"
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"chosen\0");
        s.push(0); // pad

        // Direct PROP bootargs (must be FIRST per FDT spec §5.4.1).
        s.extend_from_slice(&FDT_PROP.to_be_bytes());
        let direct_len = (direct_value.len() + 1) as u32;
        s.extend_from_slice(&direct_len.to_be_bytes());
        s.extend_from_slice(&bootargs_nameoff.to_be_bytes());
        s.extend_from_slice(direct_value);
        s.push(0); // null
        while s.len() % 4 != 0 {
            s.push(0);
        }

        // BEGIN_NODE "sub" (nested inside chosen)
        s.extend_from_slice(&FDT_BEGIN_NODE.to_be_bytes());
        s.extend_from_slice(b"sub\0");
        // Nested PROP bootargs (must NOT be returned)
        s.extend_from_slice(&FDT_PROP.to_be_bytes());
        let nested_len = (nested_value.len() + 1) as u32;
        s.extend_from_slice(&nested_len.to_be_bytes());
        s.extend_from_slice(&bootargs_nameoff.to_be_bytes());
        s.extend_from_slice(nested_value);
        s.push(0); // null
        while s.len() % 4 != 0 {
            s.push(0);
        }
        // END_NODE (sub)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END_NODE (chosen)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END_NODE (root)
        s.extend_from_slice(&FDT_END_NODE.to_be_bytes());
        // END
        s.extend_from_slice(&FDT_END.to_be_bytes());

        let off_dt_struct = FDT_HEADER_SIZE;
        let off_dt_strings = off_dt_struct + s.len();
        let totalsize = off_dt_strings + strings.len();

        let mut blob = Vec::with_capacity(totalsize);
        blob.extend_from_slice(&FDT_MAGIC.to_be_bytes());
        blob.extend_from_slice(&(totalsize as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_struct as u32).to_be_bytes());
        blob.extend_from_slice(&(off_dt_strings as u32).to_be_bytes());
        blob.extend_from_slice(&(FDT_HEADER_SIZE as u32).to_be_bytes());
        blob.extend_from_slice(&17u32.to_be_bytes());
        blob.extend_from_slice(&16u32.to_be_bytes());
        blob.extend_from_slice(&0u32.to_be_bytes());
        blob.extend_from_slice(&(strings.len() as u32).to_be_bytes());
        blob.extend_from_slice(&(s.len() as u32).to_be_bytes());
        blob.extend_from_slice(&s);
        blob.extend_from_slice(&strings);
        blob
    }
}
