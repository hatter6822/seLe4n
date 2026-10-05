// SPDX-License-Identifier: GPL-3.0-or-later
// seLe4n  - A Lean Microkernel
// Copyright (C) 2026  Adam Hall
// This program comes with ABSOLUTELY NO WARRANTY.
// This is free software, and you are welcome to redistribute it
// under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE

// The toolchain's own object operations, as linkable functions.  `lean.h`'s
// allocation and field accessors are `static inline`, so the Rust test reaches
// them through this file, compiled against the toolchain's `lean.h` and
// `config.h` -- the same header the compiled Lean archive was built with, so
// an object this file builds is laid out exactly as the Lean code expects.
// Nothing here knows the contexts' layouts: offsets are the caller's.

#include <lean/lean.h>

// The runtime's entry points the generated `main` of a Lean executable calls;
// `lean.h` declares neither.
void lean_initialize_runtime_module(void);
lean_object *initialize_seLe4n_SeLe4n_Testing_BoundaryProbes(uint8_t builtin, lean_object *w);

// Initialise the runtime and the probes module (and, through its imports, the
// kernel modules it reaches).  `0` on success, `1` when a module initializer
// refused, with the error shown.
int sele4n_boundary_initialize(void) {
    lean_initialize_runtime_module();
    lean_set_panic_messages(false);
    lean_object *res = initialize_seLe4n_SeLe4n_Testing_BoundaryProbes(1, lean_io_mk_world());
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        return 0;
    }
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
}

// `lean_alloc_ctor(0, 0, scalar_bytes)`: the shape a structure of `UInt64`
// fields compiles to.
lean_object *sele4n_boundary_alloc_scalar_ctor(unsigned scalar_bytes) {
    return lean_alloc_ctor(0, 0, scalar_bytes);
}

void sele4n_boundary_ctor_set_u64(lean_object *o, unsigned offset, uint64_t v) {
    lean_ctor_set_uint64(o, offset, v);
}

uint64_t sele4n_boundary_ctor_get_u64(lean_object *o, unsigned offset) {
    return lean_ctor_get_uint64(o, offset);
}

uint8_t sele4n_boundary_tag(lean_object *o) {
    return lean_ptr_tag(o);
}

unsigned sele4n_boundary_num_objs(lean_object *o) {
    return lean_ctor_num_objs(o);
}

size_t sele4n_boundary_byte_size(lean_object *o) {
    return lean_object_byte_size(o);
}

bool sele4n_boundary_is_scalar(lean_object *o) {
    return lean_is_scalar(o);
}

lean_object *sele4n_boundary_box(size_t n) {
    return lean_box(n);
}

// `some v`: constructor tag 1 with one object field -- the `Option` encoding
// the HAL's `trap_context_option_to_lean` answers.
lean_object *sele4n_boundary_some(lean_object *v) {
    lean_object *s = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(s, 0, v);
    return s;
}

void sele4n_boundary_inc(lean_object *o) {
    lean_inc(o);
}

void sele4n_boundary_dec(lean_object *o) {
    lean_dec(o);
}
