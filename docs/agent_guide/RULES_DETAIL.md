# Agent rules — full text (agent reference)

> The full text of the agent rules that `CLAUDE.md` states in condensed form.  Moved verbatim from `CLAUDE.md` (and its former `AGENTS.md`
> mirror) so the auto-loaded agent guidance stays small; only relative
> link targets were rewritten to resolve from this directory.  See
> [`CLAUDE.md`](../../CLAUDE.md) for the condensed, binding statement
> of each rule.

## Validation commands (tiered)

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # Tier 0-2: + trace + negative-state
./scripts/test_full.sh      # Tier 0-3: + invariant surface anchors
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # Tier 0-4

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel's real target
```

Run at least `test_smoke.sh` before any PR. Run `test_full.sh` when changing
theorems, invariants, or documentation anchors.

**A tier stops at its first failing check.**  `run_check` calls
`finalize_report` unless `--continue` is passed, so one run names *one* broken
gate and a green run after a fix says nothing about the checks that never ran.
Pass `--continue` to any tier script to collect every failure in one pass:

```bash
./scripts/test_tier3_invariant_surface.sh --continue   # every broken anchor, once
```

That matters most after a **refactor**: moving a definition silently breaks every
Tier 3 anchor scoped to it, and Tier 3 runs last.  Before running it, sweep the
anchors over every file the cut touched —
`rg -n '^run_(check|negative_check|prose_check|prose_negative_check) ' scripts/test_tier3_invariant_surface.sh`
filtered to those paths — and execute each one directly; that is seconds against
tens of minutes per iteration.  This is the *sweep what was pinning the thing you
deleted* rule with a mechanism: `v0.35.116` moved a table parse between two
functions and three anchors over the old home went silent, of which the run
reported one.

**Run `test_aarch64_cross_build.sh` after any change under `rust/`.** The
tier scripts and `test_rust.sh` both compile the *host* target, where every
`#[cfg(target_arch = "aarch64")]` block is removed before rustc or clippy
sees it — so the hardware half of the HAL, which is most of it, is invisible
to them.  The cross gate builds `sele4n-hal` for `aarch64-unknown-none` in
both profiles, verifies `boot.S` / `vectors.S` / `trap.S` actually assembled,
and lints the cross target with `-D warnings`.  It runs in CI as the
`aarch64 Cross Build` job.  A `cargo check` is **not** a substitute: it stops
before code generation, so it never hands an `asm!` template to an assembler
— the four `TLBI *OS` encoding defects WS-RR RR1 found were all `check`-clean.

## Module build verification (mandatory)

**Before committing any `.lean` file**, you MUST verify that the specific
module compiles:

```bash
source ~/.elan/env && lake build <Module.Path>
```

For example, after editing `SeLe4n/Kernel/RobinHood/Bridge.lean`:

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (default target) is NOT sufficient.** The default target only
builds modules reachable from `Main.lean` and the test executables. Modules
not yet imported by the main kernel will silently pass `lake build` even
with broken proofs.

A pre-commit hook enforces this automatically. Install with
`./scripts/install_git_hooks.sh` (invoked automatically by
`setup_lean_env.sh` and by the Lean Action CI workflow, so fresh clones
and CI checkouts are guarded without manual action). For CI contexts:

```bash
./scripts/install_git_hooks.sh          # install (idempotent no-op if present)
./scripts/install_git_hooks.sh --check  # verify installation (non-zero if absent)
./scripts/install_git_hooks.sh --force  # overwrite; backs up any diverging hook
```

The hook detects staged `.lean` files, builds each modified module, checks
for `sorry` in staged content, and **blocks the commit** if any build fails
or sorry is found. Do NOT bypass it with `--no-verify`.  It also runs the
identifier-naming gate (`scripts/check_identifier_naming.py`) whenever a
non-documentation file is staged (PR #887 review round 3): that gate reads
the **git index**, so a Tier 0 run on unstaged edits checks the *previous*
content and passes while the commit fails in CI — which is how one review
round shipped a workstream token in a Tier 3 anchor.  Stage first, then run
`test_tier0_hygiene.sh`; the hook is the backstop.

## Writing and editing large files

The Write tool replaces an entire file in one call. For files over ~100
lines this is error-prone: the call **times out**, content gets silently
truncated, sections are accidentally dropped, and the context window
fills up. **Prefer the Edit tool for all changes to existing files**,
regardless of size.

**Hard rules:**

- **Never pass more than 100 lines of content in a single Write call.**
  Files at or above this threshold must be built incrementally
  (skeleton + Edit appends) or written via Bash `cat <<'EOF'` heredoc.
- **For existing files, never use Write at all.** Always use Edit with
  targeted `old_string`/`new_string` pairs. Edit calls do not carry the
  full file content and therefore do not time out.
- **One logical change per Edit call.** Three function changes → three
  Edit calls, not one whole-file replacement.
- **Read before you edit.** Always Read the specific region first
  (e.g. `offset=350, limit=50`) so the `old_string` matches exactly,
  including indentation and whitespace.
- **Adding large new sections.** Break inserts >80 lines into multiple
  sequential Edit calls, each anchored to context already present in
  the file.
- **Creating new large files.** Either build incrementally (small Write
  skeleton → successive Edit appends ≤80 lines each, ending with
  `wc -l` verification) or use Bash heredoc
  (`cat <<'EOF' > path/file.lean ... EOF`) to write the file in one
  shot — Bash has no content-size timeout.
- **Post-write verification.** After any large write or series of edits,
  spot-check by reading the modified region (and the file's last few
  lines) to confirm nothing was truncated or duplicated.

**Example — appending a theorem block to an invariant file:**

```
# Step 1: Read the anchor region at the end of the file
Read("SeLe4n/Kernel/Capability/Invariant.lean", offset=880, limit=20)

# Step 2: Edit using the last lines as old_string, appending new content
Edit(file_path="SeLe4n/Kernel/Capability/Invariant.lean",
     old_string="<last 2-3 lines of file>",
     new_string="<those same lines>\n<new theorem block>")

# Step 3: Verify
Bash("wc -l SeLe4n/Kernel/Capability/Invariant.lean")
```

### Build-fragile pattern: deep `do`-chain nesting in test suites

Lean test suites with hundreds of sequential `expectErr` / `expectOkSt`
calls inside a single `do`-block compile to deeply nested C `if`-trees
that can exceed clang's default `-fbracket-depth=256`. Symptom:
`lake build <suite>:exe` fails with `fatal error: bracket nesting level
exceeded maximum of 256`, even though `lake env lean --run <suite>.lean`
(the interpretation path) works fine.

**Mitigation**: keep test helper functions ≤ ~150 Lean lines and use the
thin-dispatcher pattern. `tests/NegativeStateSuite.lean`'s
`runNegativeChecks` is the canonical example: a 13-line dispatcher
calling 8 per-area sub-helpers. C-scope nesting depth resets at each
function boundary in the codegen, so each sub-helper stays well below
the limit. Factor large `do`-blocks into per-area `private def`s up
front rather than waiting for the build to break.

## Handling large search and command output

Search and command output can saturate context if unbounded. Constrain
upfront:

- **Grep**: Use `head_limit` (e.g. `head_limit=30`); paginate with
  `offset`. Prefer `output_mode: "files_with_matches"` first to identify
  relevant files, then switch to `output_mode: "content"` on specific
  files.
- **Glob**: Narrow with `path` instead of searching the whole repo.
- **Bash**: Pipe through `head` or `tail`
  (e.g. `lake build 2>&1 | tail -80`). For very large output, redirect
  to a temp file: `lake build 2>&1 > /tmp/build.log` then
  `Read("/tmp/build.log", offset=1, limit=500)`.

**Rule of thumb**: if a command or search might return more than ~100
lines, limit it upfront. Paginate rather than requesting everything at
once.

## Background agent file-change protection

Background agents (launched via the Agent tool with
`run_in_background: true`) run concurrently and may finish after the
foreground agent has already modified the same files. Their stale writes
will silently overwrite the foreground agent's progress. **You must
prevent this.**

**Rules:**

1. **Never delegate file writes to a background agent for files you may
   also edit.** If there is any chance the foreground agent will touch
   the same file, run the agent in the foreground or restructure the
   work so there is no file overlap.
2. **Partition files strictly** when parallel work is genuinely needed.
   Spell the partition out in the agent's prompt (e.g. "You own
   `Foo.lean` and `Bar.lean` only — do not modify any other file"), and
   do not touch those files yourself until the agent completes.
3. **Use background agents only for read-only or independent-file
   tasks**: running builds/tests, searching the codebase, or writing
   files the foreground will never touch. Unsafe uses include editing
   shared source files or modifying configuration.
4. **Check background results before acting on shared state.** If the
   agent wrote to a file you have since modified, discard its version
   and redo that work on top of your current file state.
5. **When in doubt, run in foreground.** The performance benefit is
   never worth silently lost work.

**Safe pattern:**

```
# Background agent runs tests (read-only, no file writes)
Agent(subagent_type="general-purpose", run_in_background=true,
      prompt="Run ./scripts/test_smoke.sh and report results")

# Meanwhile, foreground edits Operations.lean — no conflict
Edit("SeLe4n/Kernel/Scheduler/Operations.lean", ...)
```

**Unsafe pattern to avoid:**

```
# WRONG: background agent will edit Invariant.lean
Agent(subagent_type="general-purpose", run_in_background=true,
      prompt="Add theorem X to Invariant.lean")

# Foreground also edits Invariant.lean — background will overwrite!
Edit("SeLe4n/Kernel/Scheduler/Invariant.lean", ...)
```

## Implement-the-improvement rule

When an audit, code review, or any reading of the codebase surfaces a
discrepancy between the **code** and the **documentation, docstring,
comment, type signature, or design intent** that describes it, and the
description represents an *improvement* over the actual code (a more
complete behaviour, a more symmetric API, a stronger invariant, a
routed dispatch where the code is a stub, a function that "should"
exist but does not), the remediation is **always** to implement the
improvement so the description becomes true.

It is **forbidden** to weaken, dilute, qualify, or rewrite the
documentation to match inferior code. Documenting incorrect or
incomplete code in lieu of fixing it is not an acceptable engineering
outcome on this project.

Concretely:

- A comment referencing a function `X` that does not exist →
  **implement `X`**, never "remove the reference."
- A docstring describing a complete spec while the implementation is
  truncated → **complete the implementation**, never "document the
  truncation."
- A stub returning `NotImplemented` while the design says it should
  route to a verified entry point → **wire up the routing.**
- Two API call paths handling the same condition asymmetrically →
  **make them symmetric**, never "document the asymmetry."
- An implicit invariant maintained only by convention → **enforce it
  structurally** (record field, refinement type, smart-constructor
  obligation, opaque type whose constructors discharge the invariant),
  never "add an inline comment about the convention."
- A computed-and-proven data structure that the surrounding code does
  not consume → **wire it into the consumer** so the proof carries
  through to runtime, never "remove the unwired structure."
- Deferred items buried in source comments → **fix them** if the
  current scope permits; otherwise lift them into the project debt
  register (`docs/audits/`, `docs/REGISTERED_DEBT.md`). Never leave
  in-source TODOs that age out with the surrounding workstream.
- A "first hardware target" or similar capability claim while the path
  is non-functional → **make the path functional**, never qualify the
  claim with a stub-status caveat.

The single legitimate exception is when the documentation describes a
**worse** state than the code (e.g. a stale `STATUS: staged` marker on
a file that has since been wired into production, or a deprecation note
on a function the project has decided to keep). In that direction the
documentation is the inferior artefact and updating it to match the
better code is correct.

**Audit reports and remediation plans must apply this rule.** Findings
of the form "documentation describes feature X; code lacks feature X;
recommendation: weaken the documentation" are not acceptable. The
recommendation must instead be "implement feature X" — and where the
implementation is non-trivial, the audit must split the work into the
proper sequence of PRs (each one a coherent slice per the PR checklist)
rather than treating documentation surgery as a substitute for the
code change.

When the optimal implementation is genuinely out of scope for the
current cut, the correct outcome is to **defer the release**, not to
ship a documentation-only patch. Forced deferrals must be recorded as
tracked debt with an explicit closure target, not absorbed silently
into a weaker public claim.

## Workstream planning documents

**Phases and sub-tasks are numbered in the order they are to be
implemented.**  A plan's numbering is its schedule: a reader who works
`RR0, RR1, RR2, …` in order must never violate a dependency, and must never
need a separate note telling them to take a later-numbered phase early.

Concretely:

- **Phase number is execution order.**  If phase 6 has to run second, it is
  phase 1 — renumber it.  A "sequencing note" that contradicts the numbering
  means the numbering is wrong, not that the note is helpful; the plan then
  has to be read twice and will be misread once.
- **Sub-task numbers run sequentially within a phase** (`RR2.1`, `RR2.2`,
  …), in execution order, with no letter groups and no `.0`.  Thematic
  grouping belongs in prose or a column, not in the identifier — a reader
  cannot tell from `RR2.C.3` whether it precedes `RR2.B.1`.
- **No backward dependencies.**  A sub-task may only consume the output of a
  lower-numbered sub-task.  If step 3 needs what step 9 measures, either the
  order is wrong or the two steps belong in the same phase.  State the
  dependency in the row that consumes it, so the constraint is visible where
  it binds.
- **Genuine parallelism is stated, not implied.**  Say which phases may
  overlap and which may never (typically because they edit the same files).
  Absent that statement, sequential execution is the contract.
- **A transition goes live only after the proofs that cover it.**  When one
  sub-task makes a transition reachable — wiring a dispatch arm, flipping a
  seam, repointing a caller at a new base — and another supplies its
  preservation, progress or refinement obligations, the proofs carry the lower
  number, or both land in one sub-task.  This is the numbering rule's
  *semantic* half and the numeric half does not imply it: a plan can be
  perfectly sequential with no backward dependency and still schedule a live
  kernel transition three PRs ahead of its own invariant surface, which is
  precisely the blocker most remediation phases exist to close.  Three
  independent instances of this shipped in one plan (WS-RR phases RR2, RR4 and
  RR5), each caught one review round at a time, because the rule as first
  written checked only that the numbers ascended.  When splitting is
  impossible — the theorems unfold the very function the switch replaces, so
  neither half compiles alone — that is the signal to merge the rows, not to
  order them.

- **Renumbering is cheap before work starts and expensive after.**  Get the
  order right at authoring time; once sub-task IDs appear in commit messages
  and CHANGELOG entries they are effectively frozen.

This applies to every plan under `docs/planning/`, and to the per-phase
tables in the status index of `docs/agent_guide/WORKSTREAM_CONTEXT.md`.

**The structural half is machine-checked.**
`scripts/check_workstream_plan.py` (Tier 0) holds every plan that declares an
exact `Sub-task count` to its own arithmetic: sub-task numbers run 1..N per
phase, the phase map matches the rows, the declared total matches the phase
map, a findings column sums to its acceptance total, no row consumes itself or
a later one, and every `<PREFIX><phase>.<sub>` citation — in the plan and in
`UNFINISHED_SMP_WORK.md`, `REGISTERED_DEBT.md`, `CLAUDE.md`, `AGENTS.md` and
`docs/agent_guide/WORKSTREAM_CONTEXT.md` — resolves to a real row.  It reads the git index, so it checks what is being
committed rather than what happens to be in the tree.  Legacy letter-group
plans (`SM6.A.1`) and plans declaring an estimate range are reported but not
held to flat numbering; closed workstreams are not renumbered.

What it deliberately does **not** check is whether a reference that resolves
still *means* what it did before a renumber, and it cannot see the semantic
ordering rule above.  Those stay a reader's job — which is why the rule is
stated, not merely gated.

## Session URL hygiene

When this codebase is edited from inside the Claude Agent SDK / Claude
Code on the web, the runtime exposes a per-session URL of the form
`https://claude.ai/code/session_<id>`. **This URL must never appear in
any artifact that ships to the public repository or to GitHub.**

**Forbidden locations:**

1. PR titles, descriptions, summaries, or any update to a PR body.
2. Commit messages — subject, body, footers, `Refs:` lines, and
   `Co-Authored-By` trailers. Once pushed, commit metadata is
   effectively unrewritable.
3. In-tree documentation, `CHANGELOG.md` entries, source comments,
   docstrings, or test fixtures.
4. GitHub issue bodies, issue comments, PR review bodies, PR review
   comments, or any other rendered text posted via GitHub MCP tools
   (`mcp__github__add_issue_comment`,
   `mcp__github__pull_request_review_write`,
   `mcp__github__create_pull_request`,
   `mcp__github__update_pull_request`, etc.).
5. Plan files or task descriptions checked into the repo
   (e.g. `docs/planning/*.md`, `docs/audits/*.md`).

**Why**: session URLs are unstable (rotate or expire without notice),
opaque to anyone outside the original session (no audit value), and
displace useful cross-references. Internal handles do not belong in
shared artifacts. Per the minimum-disclosure norm, the URL gives a
reviewer nothing they can act on.

**Use instead** — cite the canonical document or identifier:

```
Refs: docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md §8 (Phase R4)
Refs: docs/REGISTERED_DEBT.md WS-RC R3 closeout
Refs: #761                            # related GitHub PR or issue
Refs: 7da2572                         # related commit SHA
```

A commit message or PR body should typically include exactly one
`Refs:` line pointing at the most-specific canonical document.
Multiple `Refs:` lines are acceptable when the change touches several
closure cites.

**Remediation when a session URL has already been published:**

- **Local commit not yet pushed**: amend (`git commit --amend`) and
  push.
- **Pushed commit (any branch)**: do **not** force-push to scrub it.
  Treat it as a one-time leak; ensure subsequent commits comply.
- **PR title/body or issue/review comment**: edit via the GitHub UI
  or `mcp__github__update_pull_request` — these are freely editable.

This rule applies regardless of who or what added the URL — the agent
itself, a hook or GitHub Action, a copy-paste, or a checked-in plan
that gets quoted later. If any in-repo template appears to instruct
including a session URL, treat the example as obsolete and update that
template in the same PR.

## Vulnerability reporting

While executing any task in this codebase, if you discover a possible
software vulnerability that could reasonably warrant a CVE designation,
you **must** immediately report it to the user before continuing. This
applies to vulnerabilities found in:

- **Project code** — logic errors in transition semantics, capability
  checks, information-flow enforcement, or any component that could
  lead to privilege escalation, information leakage, denial of
  service, or violation of security invariants.
- **Dependencies and toolchain** — known or suspected vulnerabilities
  in Lean, Lake, elan, or any vendored/imported library encountered
  during builds, updates, or code review.
- **Build and CI infrastructure** — insecure patterns (command
  injection in shell scripts, unsafe file permissions, unvalidated
  inputs in test harnesses) that could be exploited in a development
  or CI environment.
- **Model/specification gaps** — cases where the formal model fails
  to capture a security-relevant behavior of the real seL4 kernel,
  creating a false assurance gap that could mask a real-world
  vulnerability.

**What to report:**

1. **Summary** — concise description of the vulnerability.
2. **Location** — file path(s) and line number(s).
3. **Severity estimate** — Critical / High / Medium / Low + your
   exploitability assessment.
4. **Reproduction or evidence** — how the issue manifests or could be
   triggered.
5. **Suggested remediation** — if apparent.

**How to report:**

- Stop current work and surface the finding in your response
  immediately.
- Do **not** silently fix a CVE-worthy vulnerability — always flag it
  explicitly so it can be tracked, triaged, and disclosed
  appropriately.
- If the vulnerability is in a third-party dependency, note whether an
  upstream advisory already exists.

This requirement applies regardless of whether the vulnerability is
directly related to the current task. Vigilance during routine work is
one of the most effective ways to catch security issues early.
