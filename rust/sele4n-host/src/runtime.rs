// SPDX-License-Identifier: GPL-3.0-or-later
//! Host runtime entry point.
//!
//! `HostRuntime` is the central type that later WS-RH phases attach
//! behaviour to.  At the foundation phase (RH-H) it carries
//! workspace-pinned metadata only — its substantive purpose is to
//! provide a stable construction point for later phases (RH-A
//! threads `PlatformConfig`-shaped fixtures through it; RH-F drives
//! cross-validation against the Lean kernel from it).
//!
//! ## Version pinning
//!
//! The runtime exposes the workspace's pinned package version via
//! [`HostRuntime::version`] (dynamic) and
//! [`HostRuntime::workspace_version_pinned`] (`const fn`).  Both
//! must return the same string, and that string must equal the
//! workspace version pinned in `rust/Cargo.toml`'s
//! `[workspace.package]` block.
//!
//! The integration test suite asserts these invariants on every
//! `cargo test` run.  A regression — e.g., the workspace version
//! diverging from the Lean lakefile version — fails the host
//! runtime tests, which is the desired catch-early behaviour for
//! WS-RC R8 version-sync drift.

/// Host-side runtime entry point.
///
/// At the foundation phase (RH-H) this is a metadata carrier.
/// Later WS-RH phases extend it with a state machine, fixture
/// driver, and cross-validation harness — none of which require
/// API-breaking changes to the surface declared here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct HostRuntime {
    /// Reserved private field; the foundation phase carries no
    /// state but the field exists so later phases can extend the
    /// struct without changing its construction shape (`new()`
    /// stays argument-free).
    _reserved: (),
}

impl HostRuntime {
    /// Construct a fresh host runtime.
    ///
    /// The constructor is total and infallible.  No I/O is
    /// performed; no global state is touched.
    pub const fn new() -> Self {
        Self { _reserved: () }
    }

    /// The workspace-pinned package version, as reported by Cargo
    /// at compile time.
    ///
    /// Returns the value of `env!("CARGO_PKG_VERSION")` which is
    /// materialised from the workspace `[workspace.package]`
    /// `version` field — currently `"0.31.3"`.  When the workspace
    /// version is bumped, this accessor's return value updates in
    /// lock-step.
    pub fn version(&self) -> &'static str {
        env!("CARGO_PKG_VERSION")
    }

    /// `const fn` mirror of [`HostRuntime::version`].
    ///
    /// Returns the workspace-pinned version as a `const`-evaluable
    /// expression.  Used by build-time assertions and by integration
    /// tests to verify that the static and dynamic accessors stay
    /// aligned.
    pub const fn workspace_version_pinned() -> &'static str {
        env!("CARGO_PKG_VERSION")
    }

    /// Returns `true` if the runtime is structurally equivalent to a
    /// freshly-constructed runtime.
    ///
    /// At the foundation phase every runtime is structurally
    /// equivalent (the type carries no observable state).  Later
    /// phases may make this distinction meaningful.
    pub fn is_fresh(&self) -> bool {
        *self == Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_returns_fresh_runtime() {
        let rt = HostRuntime::new();
        assert!(rt.is_fresh());
    }

    #[test]
    fn default_returns_fresh_runtime() {
        let rt = HostRuntime::default();
        assert!(rt.is_fresh());
        assert_eq!(rt, HostRuntime::new());
    }

    #[test]
    fn version_is_non_empty() {
        let rt = HostRuntime::new();
        assert!(!rt.version().is_empty());
    }

    #[test]
    fn version_starts_with_expected_major() {
        // The workspace pins the version to the lakefile version;
        // we only verify the leading "0." prefix here because the
        // canonical version-sync gate (scripts/check_version_sync.sh)
        // owns the literal-equality check.  This test catches the
        // gross regression of, e.g., the version dropping to a
        // pre-release or jumping to a `1.x` cut before the v1.0
        // gate.
        let rt = HostRuntime::new();
        assert!(
            rt.version().starts_with("0."),
            "Workspace version unexpectedly outside the pre-1.0 range: {}",
            rt.version()
        );
    }

    #[test]
    fn const_version_matches_dynamic_version() {
        let rt = HostRuntime::new();
        assert_eq!(rt.version(), HostRuntime::workspace_version_pinned());
    }
}
