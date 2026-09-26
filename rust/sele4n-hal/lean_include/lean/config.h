/*
 * seLe4n  - A Lean Microkernel
 * Copyright (C) 2026  Adam Hall
 * This program comes with ABSOLUTELY NO WARRANTY.
 * This is free software, and you are welcome to redistribute it
 * under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
 *
 * The bare-metal Lean runtime configuration (WS-BP BP1.2).
 *
 * `lean.h` includes `<lean/config.h>`, and the toolchain's copy selects
 * mimalloc (`LEAN_MIMALLOC`), whose inline allocation paths call `mi_*`
 * functions that need an operating system's virtual-memory primitives.  The
 * image has none, so every C file of the kernel archive is compiled with this
 * directory ahead of the toolchain's include path and gets the runtime's
 * small allocator instead: `lean.h` then calls `lean_alloc_small` /
 * `lean_free_small`, which BP2.1 provides over the image's own heap arena.
 *
 * This file is the toolchain's `config.h` with exactly one substitution --
 * `LEAN_MIMALLOC` dropped, `LEAN_SMALL_ALLOCATOR` added -- and
 * `scripts/build_lean_aarch64_archive.py` holds it to that relation on every
 * build: a macro the toolchain adds and this file does not classify stops the
 * build rather than being silently absent here.  The Lean runtime BP2 builds
 * must be compiled against this same file, since the allocator is a contract
 * between the inline paths in every object and the runtime that serves them.
 */
#pragma once
#include <lean/version.h>

#define LEAN_SMALL_ALLOCATOR


#define LEAN_IS_STAGE0 0
