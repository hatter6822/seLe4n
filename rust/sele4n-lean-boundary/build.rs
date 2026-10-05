// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

//! Resolve and link the compiled host Lean archives and the Lean toolchain's
//! runtime, and compile the C shim over the toolchain's own `lean.h`.
//!
//! Two inputs, each overridable by an environment variable
//! (`scripts/test_lean_boundary_layout.sh` sets both):
//!
//! * `SELE4N_LAKE_LIB_DIR` — Lake's library directory, holding
//!   `libseLe4n_SeLe4n.a` (`lake build SeLe4n:static`) and
//!   `libseLe4n_SeLe4nBoundaryProbes.a` (`lake build
//!   SeLe4nBoundaryProbes:static`); default `../../.lake/build/lib`.
//! * `SELE4N_LEAN_LIBDIR` — the toolchain's `lean --print-libdir`, holding
//!   the runtime (`libleanshared.so` on Linux, `libleanshared.dylib` on
//!   macOS — the host the test runs on, `CARGO_CFG_TARGET_OS`), with `lean.h`
//!   two directories up under `include/lean/`; default: ask `lean` on `PATH`.
//!
//! When every input is present the crate is built with
//! `cfg(sele4n_lean_host_archive)` and the test links.  When one is missing
//! the crate still compiles — so `cargo build`, `cargo clippy` and `cargo fmt`
//! over the workspace need no Lean toolchain — but its one test fails,
//! naming what is missing: the test is never skipped silently.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

const PROBES_ARCHIVE: &str = "libseLe4n_SeLe4nBoundaryProbes.a";
const KERNEL_ARCHIVE: &str = "libseLe4n_SeLe4n.a";

/// The toolchain's runtime library, named as the host platform names it.
fn runtime_shared(target_os: &str) -> &'static str {
    match target_os {
        "macos" => "libleanshared.dylib",
        _ => "libleanshared.so",
    }
}

fn lake_lib_dir(manifest_dir: &Path) -> PathBuf {
    match env::var_os("SELE4N_LAKE_LIB_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => manifest_dir.join("../../.lake/build/lib"),
    }
}

fn lean_libdir() -> Option<PathBuf> {
    if let Some(dir) = env::var_os("SELE4N_LEAN_LIBDIR") {
        return Some(PathBuf::from(dir));
    }
    let out = Command::new("lean").arg("--print-libdir").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let dir = String::from_utf8(out.stdout).ok()?;
    Some(PathBuf::from(dir.trim()))
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(sele4n_lean_host_archive)");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=shim.c");
    println!("cargo:rerun-if-env-changed=SELE4N_LAKE_LIB_DIR");
    println!("cargo:rerun-if-env-changed=SELE4N_LEAN_LIBDIR");

    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let target_os = env::var("CARGO_CFG_TARGET_OS").expect("CARGO_CFG_TARGET_OS");
    let lake_lib = lake_lib_dir(&manifest_dir);
    let mut missing = Vec::new();
    for archive in [PROBES_ARCHIVE, KERNEL_ARCHIVE] {
        let path = lake_lib.join(archive);
        println!("cargo:rerun-if-changed={}", path.display());
        if !path.is_file() {
            missing.push(path.display().to_string());
        }
    }
    let Some(libdir) = lean_libdir() else {
        println!(
            "cargo:warning=sele4n-lean-boundary: no Lean toolchain found (`lean --print-libdir` \
             failed and SELE4N_LEAN_LIBDIR is unset); the boundary layout test will fail"
        );
        return;
    };
    let runtime = libdir.join(runtime_shared(&target_os));
    if !runtime.is_file() {
        missing.push(runtime.display().to_string());
    }
    let include = libdir.join("../../include");
    if !include.join("lean/lean.h").is_file() {
        missing.push(include.join("lean/lean.h").display().to_string());
    }
    if !missing.is_empty() {
        for path in &missing {
            println!("cargo:warning=sele4n-lean-boundary: missing {path}");
        }
        println!(
            "cargo:warning=sele4n-lean-boundary: the boundary layout test will fail; run \
             scripts/test_lean_boundary_layout.sh, which builds the archives first"
        );
        return;
    }

    cc::Build::new()
        .file("shim.c")
        .include(&include)
        .warnings(true)
        .extra_warnings(true)
        .flag("-Werror")
        .compile("sele4n_lean_boundary_shim");

    println!("cargo:rustc-link-search=native={}", lake_lib.display());
    println!("cargo:rustc-link-lib=static=seLe4n_SeLe4nBoundaryProbes");
    println!("cargo:rustc-link-lib=static=seLe4n_SeLe4n");
    println!("cargo:rustc-link-search=native={}", libdir.display());
    // `libgcc_s` ahead of `libleanshared` in the link, so it precedes it in
    // the binary's `DT_NEEDED` order: `libleanshared.so` exports the
    // toolchain's bundled libunwind (`_Unwind_RaiseException`, `_Unwind_GetIP`,
    // …), and were it searched first Rust's panics — which unwind through
    // `libgcc_s`'s implementation of the same ABI — would bind to it and
    // abort (`failed to initiate panic`) or fault in the backtrace printer,
    // turning a failed assertion into a crash with its message lost.  Rust's
    // own `-lgcc_s` comes after the crate's native libraries, which is too
    // late; naming it here puts it first.  Linux only: macOS unwinds through
    // the system `libunwind` in `libSystem`, and has no `libgcc_s`.
    if target_os == "linux" {
        println!("cargo:rustc-link-lib=dylib=gcc_s");
    }
    println!("cargo:rustc-link-lib=dylib=leanshared");
    // The test binary finds the runtime where the toolchain keeps it.
    println!("cargo:rustc-link-arg-tests=-Wl,-rpath,{}", libdir.display());
    println!("cargo:rustc-cfg=sele4n_lean_host_archive");
}
