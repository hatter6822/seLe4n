# Environment Setup for seLe4

This document creates a production-ready local environment for starting the seL4
formalization effort in Lean.

## 1) Required Toolchain

- **Lean**: Lean 4 (managed by `elan`)
- **Build tool**: `lake` (installed with Lean)
- **Git**: for version control and collaboration
- **Optional editor tooling**:
  - VS Code + `lean4` extension
  - Neovim with Lean LSP support

## 2) Install Lean via elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
lean --version
lake --version
```

The repository pins Lean through:

- `lean-toolchain` → `leanprover/lean4:stable`

## 3) Build the project

```bash
lake build
```

This compiles:

- The `SeL4` Lean library
- The `seL4-spec-check` executable in `Main.lean`

## 4) Recommended editor setup

### VS Code

1. Install the **Lean 4** extension.
2. Open the repo root.
3. Run “Lean: Restart File” if initial server warmup is slow.

### Formatting and style

- Prefer explicit namespaces and module-level documentation comments.
- Keep proof scripts minimal and composable.
- Avoid introducing external dependencies until needed by proof goals.

## 5) CI behavior

GitHub Actions runs `lake build` on pushes and pull requests.

If you add dependencies or proofs requiring additional automation:

- update `lakefile.toml`
- ensure CI remains deterministic

## 6) Suggested next tools (optional)

- **Alectryon / doc-gen4** for documentation extraction.
- **LeanDojo** or custom theorem mining scripts for proof search analytics.
- Property-based scenario generators for syscall traces via extracted interpreters.
