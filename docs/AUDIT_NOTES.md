# AUDIT_NOTES.md — auditor-facing cross-references

This file collects the **auditor-facing batch documentation blocks** that
were previously inlined at the top of `rust/sele4n-types/src/lib.rs` and
related source files. Inlining these long lists in the source code made
the crate's preamble unreadable; AN8-E moves them here while keeping
short pointers at the source-of-truth sites.

Each entry below ties a finding ID from the historical audits to the
current resolution location.

## v0.29.0 audit — R-ABI LOW-tier (AK4-H)

These notes track LOW-tier ABI cleanup findings from the v0.29.0 audit;
all are addressed in the v0.29.x → v0.30.x release line.

### R-ABI-L1 — `LifecycleRetypeArgs` `TypeTag` enumeration

`rust/sele4n-abi/src/args/lifecycle.rs` doc comment now enumerates the
full 7-variant `TypeTag` list. The original audit flagged that the
crate-level docstring elided the variant names; the inline doc fix is
the canonical resolution.

### R-ABI-L2 — Identifier count in `sele4n-types/src/lib.rs:6`

The crate docstring is updated to "15 newtype identifiers" when
`SchedContextId` was added in AK4-C (commit pinned by the v0.29.x
release). New identifiers must increment this count.

### R-ABI-L3 — `RegValue` export visibility

`RegValue` is exported as `pub` from `sele4n-types` because it is the
canonical wrapper for ARM64 register words and is consumed by the
hardware-binding FFI layer landing in AN9-F (DEF-R-HAL-L14 closure).
No `#[cfg(test)]` gating is applied; the type is part of the public
API contract.

### R-ABI-L4 — `ServiceQueryArgs` empty-struct marker

`ServiceQueryArgs` is intentionally kept as a marker type so per-syscall
dispatch code can treat service-query the same way it treats
argument-bearing syscalls. Lean mirror: `ServiceQueryArgs` in
`SyscallArgDecode.lean`.

### R-ABI-L5 — `lateout("x6") _` AAPCS64 redundancy

`rust/sele4n-hal/src/trap.rs` has an inline-comment annotation
explaining the `clobber_abi("C")` redundancy. Removing the explicit
`lateout("x6") _` is a no-op; it stays for clarity.

### R-ABI-L6 — Cross-crate constant duplication

Constants like `MAX_METHOD_COUNT`, `MAX_PRIORITY`, `MAX_DOMAIN`, and
`MAX_SERVICE_MESSAGE_SIZE` are owned by `sele4n-abi` (limits) and
`sele4n-types` (identifiers + error enums). De-duplication across
crates is a post-1.0 hardening candidate; no currently-active plan
file tracks it.

### R-ABI-L7 — `ThreadId::SENTINEL` vs `CPtr::NULL` naming

Both names are retained: `CPtr::NULL` mirrors the `seL4_CapNull`
convention and removing it would break external-facing Rust code.
`ThreadId::SENTINEL` is the canonical "not a valid thread"
representation. No deprecation shim added.

### R-ABI-L8 — `Hash` derive safety

`#[derive(Hash)]` is safe because all identifier wrappers are
`#[repr(transparent)] u64`; the underlying hash is identical to
`hash(&u64)`. Cross-reference: AJ2-D in `docs/spec/SELE4N_SPEC.md` §8.12.

## v0.30.6 audit — R-HAL LOW-tier (AN8-E)

The 11 LOW items addressed by Phase AN8-E are documented inline in the
respective source files (with one-line cross-references back to
`docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` §11). This file does not
duplicate them — it is intentionally a minimal index, not a full audit
log.

## How to add new entries

When a new audit finding requires a multi-paragraph rationale that
would otherwise bloat a source file's preamble, add the entry here
under a new `## <audit-version> audit — <category>` heading. Keep the
source file's annotation to a single line of the form:

```
// AUDIT-ID (HIGH/MEDIUM/LOW): summary — see docs/AUDIT_NOTES.md.
```

The goal is that source files document the WHAT (this code is here
because of finding X) and `AUDIT_NOTES.md` documents the WHY (the
multi-paragraph reasoning).
