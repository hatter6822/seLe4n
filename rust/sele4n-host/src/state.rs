// SPDX-License-Identifier: GPL-3.0-or-later
//! Host-side state placeholder.
//!
//! `HostState` is the foundation-phase placeholder for the host-side
//! mirror of the Lean kernel's `SystemState`.  Later WS-RH phases
//! (RH-A: runtime context + boot wiring; RH-D: structured trace
//! replay) populate the field set with object stores, capability
//! tables, scheduler queues, and the other components of the
//! verified state.
//!
//! ## Why a placeholder?
//!
//! The RH-H foundation phase plumbs the public API surface so that
//! later phases do not need to reshape the crate's public interface
//! on every cut.  Carrying the type now means:
//!
//! - Tests in [`crate::dispatch`] and [`crate::fixture`] can refer
//!   to `HostState` by name without a forward-reference dance.
//! - Downstream callers (later-phase test suites) can import the
//!   type with a stable path.
//! - The placeholder's `is_empty` / `empty` API mirrors the seL4-
//!   style "empty kernel state" semantics that the verified
//!   `Builder.mkEmptyIntermediateState` provides on the Lean side
//!   (`SeLe4n/Model/IntermediateState.lean`).
//!
//! No real state-machine semantics yet.  Calling [`HostState::empty`]
//! repeatedly produces structurally identical placeholder values;
//! later phases will distinguish them by their object/capability
//! contents.

/// Host-side mirror of the kernel `SystemState`.
///
/// At the foundation phase this is a structural placeholder.  Later
/// WS-RH phases populate it with object/capability/scheduler
/// content; the placeholder shape declared here is the API surface
/// every later phase must respect.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HostState {
    /// Reserved private field; the foundation phase carries no
    /// state but the field exists so later phases can extend the
    /// struct without changing its construction shape (`empty()`
    /// stays argument-free).
    _reserved: (),
}

impl HostState {
    /// Construct an empty host state.
    ///
    /// Total and infallible.  Mirrors the Lean
    /// `Builder.mkEmptyIntermediateState` shape — no objects, no
    /// services, no scheduler queue contents.
    pub const fn empty() -> Self {
        Self { _reserved: () }
    }

    /// Returns `true` if the state has no installed objects,
    /// services, or capability mappings.
    ///
    /// At the foundation phase every `HostState` constructed via
    /// [`Self::empty`] satisfies this predicate.  Later phases
    /// will distinguish populated and empty states.
    pub const fn is_empty(&self) -> bool {
        // Placeholder semantics: the type carries no observable
        // state at this phase, so every value is empty.
        true
    }
}

/// Error variants that arise when a host-side caller drives the
/// state machine.
///
/// At the foundation phase these are placeholder variants — the
/// state machine doesn't actually emit them yet, but the variants
/// are pinned so later phases (and the test suite) can reference
/// them stably.  The shape mirrors common rejection paths the
/// verified kernel emits, so the host-side caller's error-handling
/// code aligns with the on-target trap surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum HostStateError {
    /// The state was not initialised before the operation that
    /// requires it.
    ///
    /// Mirrors the Lean `bootFromPlatformChecked` precondition that
    /// no operations may dispatch through `kernelStateRef` before
    /// the boot phase initialises it.
    Uninitialised,
    /// The operation would have exceeded a host-side capacity
    /// bound (e.g., the fixture builder's maximum register count).
    ///
    /// At the foundation phase this is a placeholder shape; later
    /// phases will tie it to actual capacity policies.
    BoundedCapacity,
    /// The caller supplied a fixture whose structural invariants
    /// the host-side validator rejected.
    ///
    /// Distinct from a kernel-side rejection — this fires on the
    /// host before any kernel transition is attempted.
    InvalidFixture,
}

impl HostStateError {
    /// Returns a stable human-readable identifier for the variant.
    ///
    /// Useful for structured logging in later WS-RH phases; the
    /// identifier is the variant name in `snake_case` so that
    /// downstream consumers can grep on it without reaching for
    /// the `Debug` impl.
    pub const fn identifier(&self) -> &'static str {
        match self {
            HostStateError::Uninitialised => "uninitialised",
            HostStateError::BoundedCapacity => "bounded_capacity",
            HostStateError::InvalidFixture => "invalid_fixture",
        }
    }
}

impl core::fmt::Display for HostStateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.identifier())
    }
}

impl std::error::Error for HostStateError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_is_empty() {
        let s = HostState::empty();
        assert!(s.is_empty());
    }

    #[test]
    fn default_is_empty() {
        let s = HostState::default();
        assert!(s.is_empty());
        assert_eq!(s, HostState::empty());
    }

    #[test]
    fn empty_states_are_equal() {
        assert_eq!(HostState::empty(), HostState::empty());
    }

    #[test]
    fn error_variants_distinct() {
        // Catches accidental variant collapse (e.g., two variants
        // sharing the same identifier).  The three placeholder
        // variants must remain distinct values.
        let v = [
            HostStateError::Uninitialised,
            HostStateError::BoundedCapacity,
            HostStateError::InvalidFixture,
        ];
        for i in 0..v.len() {
            for j in (i + 1)..v.len() {
                assert_ne!(v[i], v[j], "variants {i} and {j} are equal");
                assert_ne!(
                    v[i].identifier(),
                    v[j].identifier(),
                    "variants {i} and {j} share an identifier",
                );
            }
        }
    }

    #[test]
    fn error_identifier_is_snake_case() {
        // The identifier convention is snake_case (no spaces, no
        // mixed case).  Catches drift if a later phase adds a
        // variant whose identifier accidentally uses CamelCase.
        for e in [
            HostStateError::Uninitialised,
            HostStateError::BoundedCapacity,
            HostStateError::InvalidFixture,
        ] {
            let id = e.identifier();
            assert!(
                id.chars().all(|c| c.is_ascii_lowercase() || c == '_'),
                "{e:?} identifier '{id}' is not snake_case"
            );
        }
    }

    #[test]
    fn error_implements_std_error_trait() {
        // Trait-object construction is the canonical way to check
        // that std::error::Error is implemented; if the impl is
        // missing, this line fails to compile.
        let e: HostStateError = HostStateError::Uninitialised;
        let _: &dyn std::error::Error = &e;
    }

    #[test]
    fn error_display_matches_identifier() {
        for e in [
            HostStateError::Uninitialised,
            HostStateError::BoundedCapacity,
            HostStateError::InvalidFixture,
        ] {
            assert_eq!(format!("{e}"), e.identifier());
        }
    }
}
