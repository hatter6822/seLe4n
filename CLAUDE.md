# CLAUDE.md — seLe4n project guidance

> `AGENTS.md` is a short static pointer file that sends non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) here; the rules
> are stated only here, so edit `CLAUDE.md` only. These rules bind every
> contributor, human or agent; `docs/DEVELOPMENT.md` is the how-to guide that
> links back here.

## What this project is

seLe4n is a production-oriented microkernel written in Lean 4 with machine-checked
proofs, improving on seL4 architecture. Every kernel transition is an executable
pure function with zero `sorry`/`axiom`. First hardware target: Raspberry Pi 5.
Lean 4.28.0 toolchain, Lake build system, version 0.36.74.

> The version line above is one of the version sites that
> `scripts/check_version_sync.sh` (a Tier 0 gate, also run by the
> pre-commit hook) holds equal to `lakefile.toml`. When you bump
> `lakefile.toml` you must bump every site in the same PR — see the
> **Versioning policy** section below. Keep this sentence on a single
> line with the canonical trigger phrase (`Lake build system, version
> <x.y.z>`) intact: the verifier greps for the literal phrase on one
> line, so do not reword it or split it across a wrap.

## This file holds durable rules only — no workstream content

**Do not add workstream status, history, per-phase tables, review-round
narratives, landing notes, figures or measurements to this file.**  It is
loaded into every agent session, so everything in it costs context on every
task; it carries only rules, conventions and commands that stay true across
workstreams.  Workstream content goes in its canonical home instead:

- [`docs/REGISTERED_DEBT.md`](docs/REGISTERED_DEBT.md) — the workstream index,
  open obligations and the single debt register.
- [`CHANGELOG.md`](CHANGELOG.md) — the per-version narrative, one entry per PR.
- `docs/planning/*.md` — per-workstream and per-phase plans.
- [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](docs/agent_guide/WORKSTREAM_CONTEXT.md)
  — live workstream status and the standing constraints new code must assume
  (formerly this file's "Active workstream context"); update it, not this
  file, when a workstream's status changes. When a workstream closes, move its
  section to `docs/dev_history/planning/CLOSED_WORKSTREAM_CONTEXT.md`.

Long-form rationale for the rules below lives under `docs/agent_guide/`
(each section names its detail file).  Read those on demand, not up front.
When a rule here needs a worked example or a history of how it was earned,
put that in the detail file and keep this file's statement to a few lines.

## Versioning policy (every PR bumps the patch version)

**Every PR bumps the patch version and updates all version locations.**
There is no "release cut" accumulation under an `Unreleased` heading —
each merged PR ships its own `vX.Y.Z` and the docs always reflect the
live version.

- **Canonical source:** the `version` field in `lakefile.toml`. Every
  other site must equal it.
- **Bump in one step:** run `./scripts/bump_version.sh <new-version>`
  (e.g. `./scripts/bump_version.sh 0.31.11`). It rewrites every site
  listed in `scripts/version_locations.sh`, then self-verifies. Add a
  matching `## v<new-version> — <summary>` entry at the top of
  `CHANGELOG.md` by hand (the bumper reminds you).
- **Enforcement (sync gate):** `scripts/check_version_sync.sh` verifies
  that all sites equal `lakefile.toml`. It runs as a Tier 0 hygiene gate
  (CI, on every PR and push) and from the pre-commit hook (whenever a
  version-bearing file is staged), so a bump that forgets a location is
  a hard failure, never a silent drift. There is deliberately **no**
  force-bump (increment-vs-`main`) gate, so automated contributors
  (e.g. dependabot) are never blocked.
- **The version sites** (authoritative list in
  `scripts/version_locations.sh`): `lakefile.toml`; the five `sele4n-*`
  crates in `rust/Cargo.toml` / `rust/Cargo.lock`; `KERNEL_VERSION` in
  `rust/sele4n-hal/src/boot.rs`; `docs/spec/SELE4N_SPEC.md`; `CLAUDE.md`
  (not `AGENTS.md`, which carries no version); the root `README.md` badge +
  `Version` row; the eleven
  `docs/i18n/*/README.md` badges and `Version` rows (all 11 locales); the
  GitBook `README.md`, `navigation_manifest.json`, and
  `05-specification-and-roadmap.md`; and `docs/codebase_map.json`.
- **Adding a site:** register it once in
  `scripts/version_locations.sh` — both the verifier and the bumper pick
  it up automatically.
- **Not version sites (never auto-bumped):** historical prose such as
  `CHANGELOG.md` headers, "LANDED at vX.Y.Z" / "Version bumped A → B"
  notes, the Lean toolchain version (`4.28.0`), and audit-document
  filenames (`AUDIT_v0.30.6_*`).

## Build and run

```bash
# Environment setup (runs automatically via SessionStart hook — no build)
./scripts/setup_lean_env.sh --skip-test-deps

# Full setup including test dependencies (shellcheck, ripgrep)
./scripts/setup_lean_env.sh

# Manual build (run separately after setup)
source ~/.elan/env && lake build

# Run executable trace harness
lake exe sele4n
```

## Validation commands (tiered)

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # Tier 0-2: + trace + negative-state
./scripts/test_full.sh      # Tier 0-3: + invariant surface anchors
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Tier 0-4

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel's real target
```

- Run at least `test_smoke.sh` before any PR; run `test_full.sh` when changing
  theorems, invariants, or Tier 3 anchors.
- **A tier stops at its first failing check.** Pass `--continue` to any tier
  script to collect every failure in one pass.
- **After a refactor, sweep the Tier 3 anchors over every file the cut touched
  before running Tier 3** —
  `rg -n '^run_(check|negative_check|prose_check|prose_negative_check) ' scripts/test_tier3_invariant_surface.sh`
  filtered to those paths — and execute each one directly. Moving a definition
  silently breaks every anchor scoped to it.
- **Run `test_aarch64_cross_build.sh` after any change under `rust/`.** Host
  builds strip every `#[cfg(target_arch = "aarch64")]` block, so most of the
  HAL is invisible to them; `cargo check` is not a substitute (it never hands
  an `asm!` template to an assembler).

Full text: [`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).

## Module build verification (mandatory)

**Before committing any `.lean` file**, verify that the specific module
compiles: `source ~/.elan/env && lake build <Module.Path>` (e.g.
`lake build SeLe4n.Kernel.RobinHood.Bridge`). **`lake build` (default target)
is NOT sufficient** — it only builds modules reachable from `Main.lean` and
the test executables, so unimported modules pass with broken proofs.

A pre-commit hook enforces this (`./scripts/install_git_hooks.sh`, with
`--check` / `--force`; installed automatically by `setup_lean_env.sh` and CI).
It builds each staged module, rejects `sorry`, and runs the identifier-naming
gate, which reads the **git index** — so stage first, then run
`test_tier0_hygiene.sh`. **Do NOT bypass it with `--no-verify`.**

## Source layout

The subsystem map lives in [`docs/DEVELOPMENT.md`](docs/DEVELOPMENT.md) §5
(the filesystem is the authoritative file list). Each subsystem follows the
**Operations / Invariant split** (see *Key conventions*); either file may be an
import-only re-export hub over per-concern submodules in a sibling directory of
the same name, so existing `import` statements keep working.

## Reading large files

Many files in this repo exceed 500 lines. Read in chunks with `offset` and
`limit` (≤500 lines per call), and when editing, read only the region around
the target lines (e.g. `offset=380, limit=40`). Run
`./scripts/find_large_lean_files.sh` to list the files that need pagination;
the hand-curated **Known large files** list lives in
[`docs/agent_guide/LARGE_FILES.md`](docs/agent_guide/LARGE_FILES.md).

## Writing and editing large files

- **Prefer Edit for all changes to existing files**; never use Write on an
  existing file. One logical change per Edit call; read the target region
  first so `old_string` matches exactly.
- **Never pass more than 100 lines in a single Write call.** Build large new
  files incrementally (small skeleton + Edit appends of ≤80 lines) or with a
  Bash heredoc, then verify with `wc -l` and a read of the tail.
- **Build-fragile pattern:** hundreds of sequential `expectErr`/`expectOkSt`
  calls in one `do`-block can exceed clang's `-fbracket-depth=256` when the
  suite is compiled (`bracket nesting level exceeded`). Keep test helpers
  ≤ ~150 lines and use the thin-dispatcher pattern
  (`tests/NegativeStateSuite.lean`'s `runNegativeChecks`).

## Handling large search and command output

Constrain output upfront: Grep with `head_limit` and `files_with_matches`
first; Glob with a narrow `path`; pipe Bash through `head`/`tail` or redirect
to a temp file and read it in chunks. If a command might return more than
~100 lines, limit it.

## Background agent file-change protection

Background agents may finish after you edit the same files and silently
overwrite your work. **Never delegate writes to a background agent for files
you may also edit**; partition files strictly and name them in the agent's
prompt; use background agents for read-only or independent-file tasks
(builds, tests, searches); if an agent wrote a file you have since changed,
discard its version and redo the work. When in doubt, run in the foreground.

Full text and examples for these three sections:
[`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).

## Key conventions

- **Invariant/Operations split**: each kernel subsystem has
  `Operations.lean` (transitions) and `Invariant.lean` (proofs). Keep
  this separation.
- **No axiom/sorry**: forbidden in production proof surface. Tracked
  exceptions must carry a `TPI-D*` annotation.
- **Deterministic semantics**: all transitions return explicit
  success/failure. Never introduce non-deterministic branches.
- **Fixture-backed evidence**: `Main.lean` output must match
  `tests/fixtures/main_trace_smoke.expected`. Update fixture only with
  rationale. A fixture's `.sha256` checksum is not a comparison against live
  output — run the fixture's producer to check it.
- **Typed identifiers**: `ThreadId`, `ObjId`, `CPtr`, `Slot`,
  `DomainId`, etc. are wrapper structures, not `Nat` aliases. Use
  explicit `.toNat`/`.ofNat`.
- **Internal-first naming**: every identifier and path (theorems, functions,
  structures, fields, test runners, files, directories) must describe the
  semantics of what it is. Workstream IDs, audit IDs, phase codes and
  sub-task numbers (`WS-*`, `AN3-*`, `AK7-*`, `ak9ce_01`, `I-H01`, …) **must
  not** appear in any identifier or file name; they belong only in
  docstrings, commit messages, CHANGELOG entries and `docs/` prose.
  Historical names stay until a cut can rename them; new code complies from
  day one. Enforced by `scripts/check_identifier_naming.py` (Tier 0, reads
  the git index, baseline in `scripts/identifier_naming_baseline.json`).
- **Deferrals are registered, never silent.** No in-source TODO that ages out
  with its workstream: every deferred item is a row in the *Registered debt
  index* of `docs/REGISTERED_DEBT.md` with an owner and a closure target, and
  the source comment cites the row.
- **Retired code is removed, not left to pollute the tree.** A superseded
  definition, theorem, resolver or policy is deleted in the same cut, not
  kept beside its replacement. "Unused" is measured over the code view and
  over by-name consumers (Tier 1 censuses, Tier 3 anchors), not by textual
  references alone; sweep what was *pinning* the deleted thing.

**Writing gates and checks** (the project's gates are mostly text scanners;
these rules are what keeps them honest):

- **Gates and tests check code, not documentation or comment prose.** No
  gate, test or anchor reads a `.md` file, `docs/`, README or i18n text, or a
  comment or docstring; documentation is kept accurate by review.
- **Gates read code, prose reads prose.** No comment or docstring may decide
  whether a check passes. Source-scanning gates match against the code view
  (`scripts/lean_code_view.py --overlay`, `scripts/rust_code_view.py`);
  `run_check` / `run_negative_check` route through it automatically.
  `run_prose_check` / `run_prose_negative_check` read raw text, for code the
  view does not cover (fixtures produced by code; the view covers Lean, Rust,
  assembly, C headers, linker scripts and TOML); never point them at a
  comment or docstring. Never contort prose to satisfy
  a scanner.
- **A presence check is not a relation check.** Resolve the text into the
  structure it stands for (the command, the order, the scope, the element)
  before asserting; where a scanner cannot, make it over-approximate and fail
  **closed**.
- **Use the real tool or don't gate**: never hand-write a parser for a format
  that has one (shell, YAML, Dockerfile…); call it, or leave it to review. A
  refused unusual-but-valid form is failing closed: don't widen the scanner.
- **Test a gate by breaking the relation, not by deleting the token** — keep
  the token, break the relation, and confirm the gate fails.
- **Sweep every site that asks the same question** once a resolver exists;
  derive sets from the code instead of hand-written enumerations (keep the
  list only as a pin); a cardinality is not a set.
- **One question, one answer**: derive both answers from one owner or make
  the second impossible; a proxy is not the fact; a name is not a contract;
  a scanner's default branch is a decision (refuse what you cannot classify);
  a failed derivation is not an empty one.
- **A fix retires more than it changes** — sweep what was pinning the thing
  you changed, and a rule about code stated is not a rule enforced: give it
  a check.

The full text of these rules, with the measurements and review history that
earned each one, is in
[`docs/agent_guide/CONVENTIONS_DETAIL.md`](docs/agent_guide/CONVENTIONS_DETAIL.md).
Read the relevant part before writing or changing a gate.

## Implement-the-improvement rule

When code and its documentation, docstring, comment, type signature or design
intent disagree and the description is the *better* state (more complete
behaviour, symmetric API, stronger invariant, routed dispatch instead of a
stub, a function that "should" exist), the remediation is **always** to
implement the improvement. It is **forbidden** to weaken, dilute, qualify or
rewrite documentation to match inferior code.

- Missing function referenced in a comment → implement it. Truncated
  implementation under a complete spec → complete it. Stub that should route →
  wire it. Asymmetric call paths → make them symmetric. Convention-only
  invariant → enforce it structurally. Proven structure nobody consumes → wire
  it into the consumer. Capability claim on a non-functional path → make the
  path functional.
- Deferred items in source comments → fix them, or lift them into
  `docs/REGISTERED_DEBT.md` / `docs/audits/`; no aging in-source TODOs.
- The one exception: documentation describing a *worse* state than the code
  (stale `STATUS: staged`, an obsolete deprecation note) is updated to match.
- Audits and remediation plans must apply this rule; when the implementation
  is out of scope, defer the release and record tracked debt with a closure
  target rather than shipping a documentation-only patch.

Full text: [`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).

## Documentation rules

When changing behavior, theorems, or workstream status, update in the
same PR:

1. `README.md` — metrics sync from `docs/codebase_map.json`
   (`readme_sync` key)
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md` if a command or procedure changed (this file if a
   rule changed)
4. Affected GitBook chapter(s) — canonical root docs take priority
   over GitBook
5. `docs/CLAIM_EVIDENCE_INDEX.md` if claims change
6. `docs/REGISTERED_DEBT.md` (and `docs/agent_guide/WORKSTREAM_CONTEXT.md`)
   if workstream status changes
7. Regenerate `docs/codebase_map.json` if Lean sources changed

**One canonical home per topic.** Root `docs/` files own policy/spec text;
this file owns the contributor rules; `docs/DEVELOPMENT.md` owns the how-to.
GitBook chapters introduce a topic and link to its canonical document — never
restate it. `docs/REGISTERED_DEBT.md` is the single canonical source for
workstream planning, status, and history. When a workstream closes, its plan
moves to `docs/dev_history/planning/` once any obligation it still holds is
a row in `docs/REGISTERED_DEBT.md`. Source must not reference
`docs/dev_history/`, so it cites an archived plan by workstream or phase ID
(`WS-SM SM6.C`), resolved by the table in
`docs/agent_guide/WORKSTREAM_CONTEXT.md`. Review holds source to the rule;
no gate checks it. The ownership map is
[`docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`](docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md).

## Third-party attribution

seLe4n is GPLv3+ licensed (see `LICENSE`). The Rust workspace pulls a
small set of **build-time only** crates (`cc`, `find-msvc-tools`,
`shlex`) to assemble ARM64 boot assembly; no third-party code is linked
into the runtime kernel binary. Their upstream MIT copyright and
permission notices are reproduced verbatim in
`THIRD_PARTY_LICENSES.md` at repo root. Rules:

1. If you add a runtime dependency (`[dependencies]` of any crate
   under `rust/`), update `THIRD_PARTY_LICENSES.md` in the same PR
   with the verbatim upstream MIT/Apache copyright lines and add the
   path to `scripts/website_link_manifest.txt` if it's not already
   there.
2. If you bump an existing external crate, re-check the upstream
   `LICENSE-MIT` and Cargo.toml for authorship/copyright changes and
   sync `THIRD_PARTY_LICENSES.md` accordingly. Also re-check for a
   new upstream `NOTICE` file (Apache-2.0 § 4(d) propagation).
3. Prefer `core::*` and hand-written minimal code over pulling in a
   crate. A microkernel's trusted computing base must stay small.

## Website link protection

The project website
([sele4n.org](https://github.com/hatter6822/hatter6822.github.io))
links to source files, documentation, scripts, assets, and directories
in this repository. Renaming or deleting any of these paths produces
404 errors on the website.

Protected paths are listed in `scripts/website_link_manifest.txt`. The
Tier 0 hygiene check (`scripts/check_website_links.sh`, called from
`test_tier0_hygiene.sh`) verifies that every listed path still exists,
on every PR and push to main.

To rename or remove a protected path:

1. Update the website (`hatter6822.github.io`) to use the new path
   first.
2. Then update `scripts/website_link_manifest.txt` to match.
3. CI will pass only when the manifest and the repo tree are
   consistent.

## Ignoring dev_history

The `docs/dev_history/` directory contains milestone closeouts, prior
audit reports, completed workstream plans, and legacy GitBook chapters
retained only for historical traceability. **Do not read or reference
files in `docs/dev_history/` unless explicitly instructed.** All active
documentation lives under `docs/` and `docs/gitbook/`.

## Workstream planning documents

**Phases and sub-tasks are numbered in the order they are to be
implemented.** A plan's numbering is its schedule:

- **Phase number is execution order.** If phase 6 has to run second, it is
  phase 1 — renumber it rather than adding a sequencing note.
- **Sub-task numbers run sequentially within a phase** (`RR2.1`, `RR2.2`, …),
  with no letter groups and no `.0`.
- **No backward dependencies.** A sub-task may only consume the output of a
  lower-numbered one; state the dependency in the consuming row.
- **Genuine parallelism is stated, not implied.** Absent that statement,
  sequential execution is the contract.
- **A transition goes live only after the proofs that cover it.** The
  preservation/progress/refinement obligations carry the lower number, or
  both land in one sub-task; if neither half compiles alone, merge the rows.
- **Renumbering is cheap before work starts and expensive after.**

This applies to every plan under `docs/planning/`. Plans are documentation,
so no gate checks them; keeping their numbering and citations consistent is
the author's and the reviewer's job.

Full text: [`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).

## PR checklist

- [ ] Workstream ID identified
- [ ] Scope is one coherent slice
- [ ] Transitions are explicit and deterministic
- [ ] Invariant/theorem updates paired with implementation
- [ ] Module build verified (pre-commit hook installed and not
      bypassed)
- [ ] `test_smoke.sh` passes (minimum); `test_full.sh` for theorem
      changes; `test_aarch64_cross_build.sh` if `rust/` changed
- [ ] Documentation synchronized (see "Documentation rules")
- [ ] Patch version bumped and all version locations synced
      (`./scripts/bump_version.sh <version>`; verified by
      `scripts/check_version_sync.sh`) + `CHANGELOG.md` entry added
      (see "Versioning policy")
- [ ] No website-linked paths renamed or removed (see
      `scripts/website_link_manifest.txt`)
- [ ] No `claude.ai/code/session_*` URL in commit messages or PR
      title/body/summary (see "Session URL hygiene" below)

## Session URL hygiene

A per-session URL of the form `https://claude.ai/code/session_<id>` **must
never appear in any artifact that ships to the public repository or to
GitHub**: PR titles/bodies/summaries, commit messages (including trailers),
in-tree docs, `CHANGELOG.md`, source comments, fixtures, issue/PR/review
comments posted via GitHub tools, or plan files. Session URLs are unstable
and opaque to every other reader. Cite the canonical document, PR/issue
number or commit SHA instead (typically one `Refs:` line, e.g.
`Refs: docs/REGISTERED_DEBT.md`, `Refs: #761`, `Refs: 7da2572`).

If one is published: amend an unpushed commit; do **not** force-push to scrub
a pushed one (treat it as a one-time leak); edit PR/issue text in place. If an
in-repo template seems to ask for a session URL, treat it as obsolete and fix
the template in the same PR.

Full text: [`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).

## Vulnerability reporting

If you discover a possible vulnerability that could reasonably warrant a CVE
— in project code (transition semantics, capability checks, information-flow
enforcement, privilege escalation, leakage, DoS), dependencies and toolchain
(Lean, Lake, elan, crates), build/CI infrastructure (command injection,
unsafe permissions, unvalidated inputs), or model/specification gaps that
create false assurance — you **must stop and report it to the user
immediately**, whether or not it relates to the current task.

Report: summary; location (paths and lines); severity (Critical/High/Medium/
Low) with exploitability; reproduction or evidence; suggested remediation.
Do **not** silently fix a CVE-worthy issue; for third-party issues, note
whether an upstream advisory exists.

Full text: [`docs/agent_guide/RULES_DETAIL.md`](docs/agent_guide/RULES_DETAIL.md).
