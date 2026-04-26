# Contributing to seLe4n

Thanks for contributing to seLe4n — a production-oriented microkernel written in
Lean 4 with machine-checked proofs.

## License

seLe4n is licensed under the [GNU General Public License v3.0 or later](LICENSE).
By submitting a pull request or contributing code to this project, you agree that
your contributions will be licensed under the same GPL-3.0-or-later license. You
also certify that you have the right to submit the contribution under this license.

Build-time-only Rust dependencies are MIT/Apache-2.0; their attribution lives
in [`THIRD_PARTY_LICENSES.md`](THIRD_PARTY_LICENSES.md). The runtime kernel
binary contains zero third-party crates.

## 5-minute contributor path

1. **Workflow + standards:** [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md)
2. **Testing tiers:** [`docs/TESTING_FRAMEWORK_PLAN.md`](docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI policy:** [`docs/CI_POLICY.md`](docs/CI_POLICY.md)
4. **Project scope + workstreams:** [`docs/spec/SELE4N_SPEC.md`](docs/spec/SELE4N_SPEC.md)
5. **Latest audit:** [`docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md`](docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md)
6. **Workstream history:** [`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md)

Full handbook: [`docs/gitbook/README.md`](docs/gitbook/README.md)

## Branch policy

- **Never push to `main` directly.** Open a feature branch, push it, and let
  the maintainer merge via PR.
- One coherent slice per branch. If a slice grows larger than you expected,
  split it before requesting review.
- Workstream identifiers go in commit messages and the PR description, not in
  identifier names (see "Internal-first naming" in
  [`CLAUDE.md`](CLAUDE.md)).

## Pre-commit hook (mandatory)

Before your first commit, install the pre-commit hook:

```bash
./scripts/install_git_hooks.sh
```

The hook builds each modified `.lean` module via `lake build <Module>` and
rejects any commit that introduces a `sorry`. **Do not bypass it with
`--no-verify`** — if it blocks a commit, fix the underlying issue.

`scripts/setup_lean_env.sh` runs the installer automatically; CI invokes
`./scripts/install_git_hooks.sh --check` to enforce hook presence on the
contributor's clone for any merged PR.

## Required validation before opening a PR

```bash
./scripts/test_smoke.sh     # minimum gate (Tier 0-2)
./scripts/test_full.sh      # required for theorem/invariant changes (Tier 0-3)
```

For Rust-side changes, additionally run:

```bash
cd rust && cargo test --workspace && cargo clippy --workspace -- -D warnings
```

For ABI / decode-layer changes, also run:

```bash
./scripts/test_abi_roundtrip.sh
./scripts/test_rust_conformance.sh
```

## File-size convention (2000-LOC ceiling)

Production `.lean` modules SHOULD stay under **2000 LOC**. Files that have
grown past this ceiling are split into a re-export hub plus child modules
(see `SeLe4n/Kernel/IPC/Invariant/Structural.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`, and
`SeLe4n/Kernel/Lifecycle/Operations.lean` for examples). Hub files are
import-only thin re-export aggregates so that existing `import` statements
keep working unchanged after a split.

If your change pushes a file past the ceiling, plan the split as part of the
same PR — see the WS-AN AN3-C / AN4-F / AN4-G splits in
[`docs/WORKSTREAM_HISTORY.md`](docs/WORKSTREAM_HISTORY.md) for the
mechanical pattern.

`CHANGELOG.md` and other documentation/historical content are exempt from
the ceiling.

## PR requirements

- Identify workstream ID(s) advanced; tag the originating audit / sub-task
  in the commit body, **not** in identifier names.
- Keep scope to one coherent slice.
- Transitions must be deterministic (explicit success/failure).
- Invariant/theorem updates paired with implementation changes.
- Synchronize documentation in the same PR — README, SPEC, GitBook,
  CHANGELOG, and `docs/codebase_map.json` if Lean sources changed.
- No website-linked paths renamed/removed without updating
  `scripts/website_link_manifest.txt` (Tier 0 enforces this).
- Zero `sorry` / `axiom` / `native_decide` introduced into `SeLe4n/` or
  `Main.lean`.
- See the full checklist in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md).

## CI security note (DOC-M08)

The CI workflows in `.github/workflows/` use the `pull_request` trigger
exclusively (not `pull_request_target`). This is deliberate: `pull_request`
runs the workflow against the PR's HEAD commit with no access to repository
secrets, so a malicious PR cannot exfiltrate tokens. Workflows that need
write access (e.g. release tagging) live in their own gated workflow files
that only run on `push` to a protected branch and are reviewed manually.

If you add a new workflow, default to `pull_request`. Switching to
`pull_request_target` requires a security review documented in the PR
description.
