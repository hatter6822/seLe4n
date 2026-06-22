# seLe4n Observatory — Web Application Specification

> **A proof-carrying execution visualizer for the seLe4n microkernel.**
> Watch a formally-verified microkernel run, inspect every object it
> touches, and pivot from any runtime transition straight to the
> machine-checked theorem that proves it safe.

---

## 0. Document control

| Field | Value |
|-------|-------|
| **Artifact** | Product + technical specification (design-complete, pre-implementation) |
| **Status** | Draft v1 — for review |
| **Scope** | A standalone web application; consumes seLe4n build artifacts. Does **not** modify the verified kernel core. |
| **Audience** | Frontend/full-stack engineers building the app; kernel maintainers reviewing data contracts; the project lead. |
| **Kernel baseline** | Metrics quoted against `docs/codebase_map.json` at time of writing (v0.31.151: 312 modules, 11,510 declarations, 79,605 call-graph edges, ~6,000 proved theorems, zero `sorry`/`axiom`). The app reads these live from the artifact, so it never hard-codes a version. |
| **Related docs** | `docs/spec/SELE4N_SPEC.md` (kernel spec), `README.md` (claims), `tests/fixtures/scenario_registry.yaml` (scenario catalog), `docs/codebase_map.json` (declaration inventory), `docs/gitbook/12-proof-and-invariant-map.md` (proof map). |
| **Naming** | "seLe4n Observatory" / "Observatory" is a working product name; the signature interaction is the **Proof Pivot**. All internal identifiers in this spec follow the project's internal-first naming rule. |

### 0.1 How to read this document

Sections 1–5 establish *what* the app is and the conceptual model that
makes it coherent. Sections 6–7 define the *data* it stands on and the
*system architecture*. Section 8 is the heart: a per-view specification of
every visualization surface. Sections 9–13 cover the cross-cutting
behaviors, design language, and engineering constraints. Sections 14–17
give the concrete contracts, backend, roadmap, and validation strategy.
Appendices A–G are reference tables the implementation will need daily.

A reader who only wants the vision can stop after §5. A reader who needs
to start building should read §6, §7, §14, and §16, then their assigned
views in §8.

---

## 1. Executive summary

The seLe4n Observatory is an interactive web application that makes a
machine-checked microkernel **legible in motion**. It fuses three layers
that are almost always shown in isolation:

1. **Execution** — the deterministic trace of kernel transitions
   (syscalls, scheduling decisions, IPC rendezvous, capability
   operations) as the kernel actually runs them.
2. **State** — the concrete kernel heap those transitions mutate: thread
   control blocks, endpoints, notifications, capability spaces, page
   tables, scheduling contexts, run queues, and per-core scheduler state.
3. **Proof** — the ~6,000 machine-checked theorems that guarantee every
   one of those transitions preserves the kernel's invariants, rendered
   as a navigable dependency cosmos that visibly bottoms out at Lean's
   foundations with no `sorry` and no `axiom`.

The novelty is not any single one of these — it is **binding them
together**. Because every seLe4n transition is a *pure, deterministic
function with a checked proof*, the Observatory can do what no
conventional kernel visualizer can:

- **Replay with perfect fidelity, forwards and backwards.** Pure
  functions mean time-travel is exact, not approximate; you can scrub,
  rewind, and branch the timeline.
- **Carry the proof alongside the run.** For any event in the trace, one
  click — the **Proof Pivot** — surfaces the source transition function,
  the invariant it must preserve, and the exact theorem that discharges
  that obligation, all the way down to the axiom-free leaves.
- **Make non-interference visible.** Render a security domain's *view* of
  the state beside the full state and watch a secret action leave the
  low-clearance view pixel-for-pixel unchanged — the visual embodiment of
  the proved non-interference property.

The Observatory is built entirely from artifacts the repository already
produces (`codebase_map.json`, `scenario_registry.yaml`, the deterministic
trace fixtures) plus a small, clearly-bounded set of **build-time
exporters** that emit machine-readable JSON without touching the kernel's
trusted computing base.

## 2. Motivation — the gap this fills

Kernel observability tooling today splits cleanly into two camps, and
neither tells the whole story:

- **Runtime tools** (tracers, `ftrace`, `gdb`, `bpftrace`, eBPF
  dashboards) show *what happened* on real hardware, but they are
  non-deterministic, lossy, and have no notion of correctness. You see a
  context switch; you cannot see *why it is guaranteed safe*.
- **Code-structure tools** (Sourcetrail, call-graph explorers, doc sites)
  show *how the code is organized*, but they are static. You can read the
  scheduler's source; you cannot watch a thread move through its run
  queue, and you certainly cannot connect a line of proof to a line of
  behavior.

seLe4n is unusual in a way that dissolves this split. The kernel **is** an
executable mathematical object: each transition is a total function over
an explicit `SystemState`, every failure is an explicit error value, and
every invariant is a `theorem` the Lean type-checker has already verified.
That means a single application can be *both* a faithful runtime
visualizer *and* a live proof explorer, with a verified bridge between
them. No real kernel affords this, because no real kernel ships its
semantics and its soundness proof as the same artifact.

The Observatory exists to exploit exactly that property. Its thesis: **if
the kernel is proof-carrying code, its visualization should be
proof-carrying too.**

## 3. Goals and non-goals

### 3.1 Goals

- **G1 — Faithful, deterministic replay.** Reproduce the exact transition
  sequence the kernel executes, byte-for-byte consistent with the trace
  fixtures, with frame-accurate forward/backward stepping.
- **G2 — Whole-state inspection.** Let a user open any object (TCB,
  endpoint, CNode, page table, sched-context, reply, untyped) at any step
  and see every field, with cross-references resolved into clickable
  links.
- **G3 — Proof-carrying behavior.** From any transition, reach the
  governing invariant and its discharging theorem(s), and visualize the
  proof-dependency subgraph down to axiom-free leaves.
- **G4 — Subsystem-native lenses.** Provide purpose-built visualizations
  for scheduling (EDF/PIP/CBS/domains), IPC (dual-queue rendezvous,
  donation), capabilities (CSpace + derivation tree), address spaces
  (ARMv8 page tables), information flow, and SMP.
- **G5 — Make the headline guarantees visceral.** Non-interference,
  deadlock-freedom under the lock hierarchy, bounded-latency scheduling,
  and "zero `sorry`/`axiom`" should each have a view that *shows* the
  property, not just asserts it.
- **G6 — Zero kernel-core risk.** All data is produced by build-time
  exporters in the testing/tooling layer; the verified kernel and its TCB
  are never modified to serve the UI.
- **G7 — Lockstep with the kernel.** A CI gate regenerates the app's data
  from the current sources and fails on drift, so the Observatory can
  never silently misrepresent the kernel.
- **G8 — Approachable depth.** Usable by a newcomer in "guided tour" mode;
  exhaustive for an auditor in "expert" mode. Density is a setting, not a
  fork.

### 3.2 Non-goals

- **N1 — Not a debugger for real hardware.** v1 visualizes the model's
  deterministic traces, not live RPi5 silicon. (A hardware-trace ingest
  is a future extension, §16.)
- **N2 — Not a proof editor.** The Observatory *reads* the proof graph; it
  does not run Lean elaboration in the browser or let users edit
  theorems. (A live "what-if" runner of the executable model is in scope
  for v3; in-browser Lean checking is not.)
- **N3 — Not a replacement for the canonical docs.** It complements
  `SELE4N_SPEC.md` and the GitBook; it links to them as the source of
  truth for prose.
- **N4 — Not a general Lean visualizer.** It is specialized to seLe4n's
  state model and subsystems; genericity is explicitly traded for depth.

---

## 4. Audiences and personas

The Observatory serves five personas. Each maps to a default landing view
and an "intent" the navigation should optimize for. The same data backs
all of them; only emphasis and density differ.

| Persona | Wants to… | Default lens | Density |
|---------|-----------|--------------|---------|
| **Kernel developer** ("Dev") | Understand a subsystem's behavior, debug a transition, see what a change touches | Trace Theater → State Inspector | Expert |
| **Verification engineer / auditor** ("Auditor") | Trace an invariant to its proof, confirm axiom-freedom, find the theorem for a behavior | Proof Graph Explorer | Expert |
| **Security researcher** ("Sec") | Probe information-flow, non-interference, capability authority, deadlock-freedom | Information-Flow Lens / Capability Forge | Expert |
| **Educator / student** ("Learner") | Learn how a capability microkernel works, guided | Guided Tour → Scheduler/IPC lenses | Guided |
| **Evaluator / public** ("Evaluator") | Assess "is this real?" — see live metrics, the proof cosmos, a headline demo | Mission Control | Curated |

**Design consequence.** The product ships a single coherent app with a
**persona switch** that re-orders the lens rail, sets default density, and
toggles inline explainers — not five separate apps. A Learner and an
Auditor looking at the same IPC rendezvous see the same animation; the
Auditor additionally sees the lock-set and the preserved `ipcInvariant`
chip, while the Learner sees a plain-language caption.

---

## 5. Core conceptual model — "The Trinity"

Everything in the Observatory is an expression of three linked layers and
the spine that connects them.

```
        ┌─────────────────────────────────────────────────────────┐
        │                      THE PROOF PIVOT                      │
        │  (select anything in one layer → reveal it in the others) │
        └─────────────────────────────────────────────────────────┘
                 ▲                    ▲                    ▲
                 │                    │                    │
        ┌────────┴───────┐  ┌─────────┴────────┐  ┌────────┴────────┐
        │   EXECUTION    │  │      STATE       │  │      PROOF      │
        │                │  │                  │  │                 │
        │ trace events   │  │ objects (heap)   │  │ declarations    │
        │ syscalls       │  │ capabilities/CDT │  │ theorems/lemmas │
        │ scheduling     │  │ run/IPC queues   │  │ invariants      │
        │ SGI / cross-   │  │ page tables      │  │ call/proof DAG  │
        │   core wakes   │  │ sched-contexts   │  │ axiom-free      │
        │ (the timeline) │  │ per-core state   │  │   leaves        │
        └────────────────┘  └──────────────────┘  └─────────────────┘
          source: trace        source: state          source:
          fixtures + JSON      snapshots/deltas        codebase_map.json
          trace exporter       (state exporter)        + proof index
```

### 5.1 The three layers, precisely

- **Execution layer.** An ordered list of `TraceEvent`s. Each event is a
  tagged checkpoint (the repo's `[TAG-NNN]` markers) or a structured
  transition record: a syscall invocation, a scheduling decision, an IPC
  rendezvous, a cross-core SGI, an invariant check. Events carry the
  scenario ID, subsystem, source function, inputs, the resulting value or
  error, and a pointer to the `StateSnapshot` after the step.

- **State layer.** A `StateSnapshot` is the kernel's `SystemState` at a
  point in the trace: the object store (`RHTable ObjId KernelObject`), the
  per-core `SchedulerState`, the capability derivation tree, the ASID
  table, the TLB, service registries, and the machine register banks.
  Snapshots are stored as a baseline plus per-step **deltas** so the app
  can render any step and *diff* any two.

- **Proof layer.** The declaration graph from `codebase_map.json`:
  11,510 nodes (`def`, `theorem`, `lemma`, `structure`, `inductive`,
  `instance`, …) and 79,605 `called` edges, enriched by a **proof index**
  that maps each invariant to its definition, its preservation theorems,
  and its axiom-dependency status.

### 5.2 The spine — the unified entity model

The three layers are stitched together by a small set of cross-cutting
identifiers. These are the join keys the entire UI relies on:

| Entity | Identity | Joins to |
|--------|----------|----------|
| `Subsystem` | enum (Scheduler, IPC, Capability, Lifecycle, SchedContext, Architecture, InformationFlow, Service, Concurrency/SMP, Platform, …) | colors & groups every other entity |
| `Module` | Lean module path (`SeLe4n.Kernel.IPC.Operations.Endpoint`) | → declarations; → subsystem |
| `Declaration` | fully-qualified Lean name | → module; → called[]; → callers[]; ← Transition.sourceFn; ← Invariant.theorems |
| `Scenario` | registry ID (`IMT-004`) | → source module+function; → subsystem; → TraceEvent; → exercised Invariant |
| `TraceEvent` | `(traceId, seq)` | → Scenario; → Transition; → StateSnapshot(before/after); → Invariant(s) checked |
| `StateSnapshot` | `(traceId, seq)` | → Objects; produced by TraceEvent |
| `Object` | `ObjId` (+ kind tag) | → fields resolve to other ObjId/ThreadId/etc.; ← Capability.target |
| `Capability` | `(CNode ObjId, Slot)` | → CapTarget (Object/CNodeSlot/Reply); → CDT node |
| `Transition` | syscall id or kernel op name | → sourceFn (Declaration); → preserved Invariant(s); → error set |
| `Invariant` | predicate name (`ipcInvariantFull`) | → defining Declaration; → preservation theorems; → axiom status; ← Transition |
| `Core` | `CoreId` (0..3 on RPi5) | → per-core scheduler fields; → SGI edges; → held LockSet |
| `Lock` | `LockId = (LockKind level 0..9, ObjId)` | → Object; → core holding it |
| `SecurityLabel` | label id | → Objects/Threads/Services; → projection visibility |

**Why this matters.** Because `Scenario → sourceFn → Declaration` and
`Transition → preserved Invariant → preservation theorem (Declaration)`
are both expressible over these keys, the app can answer the signature
question — *"show me the proof for this thing I just watched happen"* — by
a pure graph traversal over already-shipped artifacts. No heuristics, no
guessing.

### 5.3 The Proof Pivot (signature interaction)

The Proof Pivot is the single most important interaction in the product.
From **any** selection in **any** view, a persistent **Context Rail**
offers the cross-layer jumps that selection supports:

- From a **TraceEvent**: → its `Scenario` → its `sourceFn` → the
  `Invariant`(s) it preserves → the discharging `theorem`(s) → the proof
  subgraph → "what else this theorem guarantees."
- From an **Object** field that references another object: → that object,
  at the same step.
- From a **Declaration** (theorem): → the operations whose proofs use it →
  the scenarios that exercise those operations → the trace steps where you
  can *watch* it hold.
- From an **Invariant chip**: → its definition → its 12/11 conjuncts (for
  the composite invariants) → each conjunct's preservation lemma per
  operation.

This bidirectional, lossless navigation between *running*, *state*, and
*proof* is what makes the Observatory novel rather than "a nice dashboard."

### 5.4 Worked example of the spine (preview)

A user watching `[IMT-014] call/reply response registers: [100, 200]`:

1. **Execution** — the Trace Theater shows the `call`→`reply` rendezvous
   animate; registers `[100,200]` flow from server to caller.
2. **State** — the State Inspector shows the caller TCB leaving
   `blockedOnReply` → `ready`, the reply object's `caller` link consumed,
   and the donated `SchedContext` returning to the caller.
3. **Proof** — the Context Rail's Proof Pivot jumps to
   `ipcInvariantFull`, highlights the `replyCallerLinkage` and
   `blockedOnReplyHasTarget` conjuncts, opens the
   `endpointReply…_preserves_ipcInvariant` theorem, and shows its proof
   subgraph terminating at axiom-free Lean primitives.

Appendix G gives the full end-to-end walkthrough.

---

## 6. Data sources and the ingestion pipeline

The Observatory is **build-time-static-first**: a pipeline transforms repo
artifacts into a versioned bundle of JSON the SPA loads directly. Three
sources already exist; four small exporters are proposed. Every exporter
lives in the testing/tooling layer (`SeLe4n/Testing/`, `scripts/`) and is
forbidden from altering the verified kernel — satisfying goal **G6**.

### 6.1 Existing artifacts (consume as-is)

1. **`docs/codebase_map.json`** — the static structure and proof graph.
   312 modules; 11,510 declarations; per declaration `{kind, name, line,
   called[]}`; 79,605 edges; plus `readme_sync` metrics (version,
   toolchain, LOC, file counts, proved-theorem count, hardware target).
   Generated by `scripts/generate_codebase_map.py`. **This is the spine of
   the Proof layer and the Architecture Atlas.**

2. **`tests/fixtures/scenario_registry.yaml`** — the scenario catalog.
   242 entries, each `{id → source, function, subsystem, description}`.
   Validated by `scripts/scenario_catalog.py`. **This is the join between
   trace events and source/proof.**

3. **The deterministic trace fixtures** — the executable behavior:
   - `tests/fixtures/main_trace_smoke.expected` (234 tagged events, the
     primary scenario), with its `.sha256`.
   - `tests/fixtures/smp_4core_scheduler.expected` (per-core SMP trace).
   - `tests/fixtures/two_phase_arch_smoke.expected`,
     `robin_hood_smoke.expected`, `qemu_boot_expected.txt`.
   These are produced by `lake exe sele4n` and the suite runners and are
   byte-stable (CI gates on the hash). **This is the Execution layer's
   ground truth and the determinism anchor.**

### 6.2 Proposed exporters (new, build-time, TCB-safe)

These four exporters turn the human-readable, behavior-faithful artifacts
into rich machine-readable JSON. They are additive and independently
landable.

**E1 — Structured trace exporter (`lake exe sele4n --emit-json`).**
The trace harness already emits one line per checkpoint. E1 adds a
parallel, opt-in JSON sink that emits, per checkpoint, a structured
`TraceEvent` record (schema §14.1). The existing human text path is
unchanged, so the byte-stable fixture and its SHA gate are untouched; the
JSON path is verified by its *own* golden fixture
(`tests/fixtures/main_trace.events.json` + hash). Implementation is a
`ToJson`/emitter in `SeLe4n/Testing/`, mechanically mirroring the
`trace`/`checkInvariants` calls that already exist in `MainTraceHarness`.

**E2 — State snapshot/delta exporter.**
The harness threads an explicit `SystemState` through every step. E2 adds
a serialization layer (in `SeLe4n/Testing/`, **not** the kernel) that, when
enabled, emits a baseline `StateSnapshot` at step 0 and a compact
`StateDelta` after each transition (schema §14.2). It serializes the
object store, per-core scheduler state, CDT, ASID table, TLB, and service
registries. Gated behind `--emit-state` so the default trace is unaffected.
This is the single most valuable new artifact: it powers the entire State
layer and all subsystem lenses.

**E3 — Proof index (`scripts/generate_proof_index.py`).**
Extends the codebase map with proof-specific metadata into
`docs/proof_index.json` (schema §14.3): the catalog of named invariants
(`proofLayerInvariantBundle`, `crossSubsystemInvariant`'s 12 conjuncts,
`ipcInvariantFull`'s conjuncts, the per-core scheduler invariants, the
non-interference predicates); for each, its defining declaration, its
per-operation preservation theorems, and its **axiom-dependency status**
captured by running Lean's `#print axioms` on the top-level bundle proofs
(the data behind the "zero `axiom`/`sorry`" claim). The call graph already
in `codebase_map.json` supplies the proof-dependency edges.

**E4 — Scenario↔proof linkage.**
Extends `scenario_registry.yaml` with two optional fields per scenario:
`transition` (the kernel op/syscall it exercises) and `invariant` (the
governing invariant). This closes the last join in the spine, letting the
Proof Pivot go `TraceEvent → Transition → Invariant` without inference.
Backwards-compatible: absent fields degrade to "unlinked," and
`scenario_catalog.py` validates the additions.

### 6.3 The build pipeline

```
   Lean sources ──► generate_codebase_map.py ──► codebase_map.json ─┐
                └─► generate_proof_index.py  ──► proof_index.json ───┤
   scenario_registry.yaml (+E4 fields) ────────────────────────────┤
   lake exe sele4n --emit-json --emit-state ──► *.events.json ──────┤
                                            └──► *.state.json  ──────┤
                                                                     ▼
                                            scripts/build_observatory_data.py
                                                   (normalize, validate,
                                                    precompute graph layouts,
                                                    chunk by module/subsystem,
                                                    emit manifest + hashes)
                                                                     ▼
                                              web/public/data/<contentHash>/
                                                   manifest.json
                                                   atlas/*.json
                                                   proof/*.json
                                                   traces/<id>/events.json
                                                   traces/<id>/state.json
                                                                     ▼
                                              Static SPA (Vite build) ──► deploy
```

The data builder (`build_observatory_data.py`) is the only new "heavy"
tool: it validates every artifact against the §14 schemas, **precomputes
force-directed layouts** for the large graphs (so the browser never runs a
cold layout), **chunks** the 5 MB codebase map by module and subsystem for
lazy loading, and writes a content-addressed `manifest.json` that the SPA
fetches first. Determinism in → determinism out: identical sources yield
an identical bundle hash (this is itself a CI assertion).

### 6.4 Freshness and anti-drift (goal G7)

A CI job (`observatory_data_sync`) regenerates the bundle from `HEAD` and
fails if it differs from a committed checksum, exactly as the kernel's own
trace-fixture SHA gate works today. Consequence: **the Observatory cannot
display a kernel that does not exist.** If a maintainer changes a
transition or a theorem, either the data regenerates and the app updates,
or CI goes red. The app footer surfaces the bundle's source commit and
the `codebase_map.json` digest so any view is auditable back to a commit.

---

## 7. System architecture

### 7.1 Topology

- **v1–v2: fully static SPA.** No server. The pipeline (§6.3) emits a
  static `data/` bundle; the app is HTML/JS/CSS served from any static
  host (GitHub Pages alongside `sele4n.org`). This matches the project's
  determinism and reproducibility ethos, has a trivial threat surface, and
  guarantees that what you see is exactly the committed artifact.
- **v3: optional live "what-if" backend.** A thin, sandboxed service that
  runs `lake exe sele4n` (or a focused harness) against a user-specified
  initial topology/scenario and streams back `events.json` + `state.json`.
  Because the kernel model is a pure, total, I/O-free function, running it
  is safe and deterministic — the backend is a calculator, not an
  environment. Detailed in §15.

### 7.2 Frontend stack

| Concern | Choice | Rationale |
|---------|--------|-----------|
| Framework | **React + TypeScript**, Vite | Mature, typed, fast HMR; large component ecosystem |
| Big-graph rendering | **Sigma.js + graphology** (WebGL) | Renders the 11.5k-node / 79.6k-edge proof graph at interactive framerates |
| Structured graphs | **Cytoscape.js** | CDT, CSpace tree, lock hierarchy, service deps, page-table tree — compound nodes, good layouts |
| Custom domain viz | **D3** (+ visx) | Run-queue lanes, budget bars, EDF timelines, page-table walk, register diffs, SGI arcs |
| Timeline/transport | Custom D3 + React | Scrub/step/branch transport bar |
| State management | **Zustand** + URL-as-state | Lightweight; deep-linkable selections (§9.4) |
| Styling/UI | **Tailwind** + Radix UI primitives | Design-system speed; accessible primitives |
| Code/proof display | **CodeMirror 6** + a Lean grammar | Syntax-highlit Lean snippets with hover/jump |
| Layout compute | **graphology layouts** in a Web Worker; layouts also precomputed at build | Keep the main thread free; cold-start instant |
| Data fetch/cache | Fetch + IndexedDB cache keyed by bundle hash | Re-visit loads instantly; offline-capable |

### 7.3 Data-loading strategy

1. Fetch `manifest.json` (small): lists bundle hash, available traces,
   subsystem palette, chunk index, schema versions.
2. Lazily fetch per-view chunks: the Atlas loads the module graph; opening
   a module loads that module's declarations; the Proof Explorer streams
   declaration chunks on demand; a trace loads `events.json` eagerly and
   `state.json` deltas progressively (baseline + windowed deltas around the
   playhead).
3. Cache everything in IndexedDB under the bundle hash; a new bundle hash
   transparently invalidates.

### 7.4 Module/package layout (frontend)

```
web/
  public/data/…                      # generated bundle (gitignored; built in CI)
  src/
    app/                             # shell, routing, persona switch, command palette
    data/                            # loaders, schema types (generated from §14), cache
    spine/                           # the cross-layer entity model + Proof Pivot engine
    views/
      mission-control/  atlas/  proof-explorer/  trace-theater/
      state-inspector/  scheduler/  ipc/  capability/  vspace/
      schedcontext/  infoflow/  smp/  boot-hardware/  abi/  scenario-catalog/
    components/                      # transport bar, context rail, object cards, chips,
                                     #   graph canvases, diff gutters, legends
    design/                          # tokens, theme, motion, a11y helpers
    workers/                         # layout + diff workers
```

`src/spine/` is deliberately a first-class module, not a util folder: it
owns the entity model (§5.2) and the Proof-Pivot traversal logic that
every view calls into.

---

## 8. The view catalog

The Observatory is organized as a set of **lenses** over the shared data
(§5). Every lens follows the same chrome: a **lens rail** (left), a
**stage** (center, the visualization), a **transport bar** (bottom, the
time controls — present in every execution-aware lens), and a persistent
**Context Rail** (right, the Proof Pivot + details of the current
selection). Lenses share selection state: select a TCB in the Scheduler
lens, switch to the State Inspector, and it stays selected.

Each view below is specified as: **Purpose · Primary persona · Data
inputs · Layout · Visual encoding · Interactions · Cross-links · Edge
cases.**

### 8.0 Shared chrome

```
┌───────────────────────────────────────────────────────────────────────┐
│  seLe4n Observatory   [⌘K search]      persona:[Dev▾]  density:[Expert▾]│
├──────┬───────────────────────────────────────────────┬────────────────┤
│ LENS │                                                │  CONTEXT RAIL  │
│ RAIL │                  STAGE                          │  selection +   │
│      │           (the active visualization)            │  Proof Pivot   │
│ ◐ MC │                                                │                │
│ ⬡ AT │                                                │  ┌──────────┐  │
│ ❋ PR │                                                │  │ details  │  │
│ ▶ TR │                                                │  ├──────────┤  │
│ ▦ ST │                                                │  │ pivots → │  │
│ ⏱ SC │                                                │  │  exec    │  │
│ ✉ IP │                                                │  │  state   │  │
│ 🔑 CA │                                                │  │  proof   │  │
│ 🗺 VS │                                                │  └──────────┘  │
│ 🔒 IF │                                                │                │
│ ▥ SM │                                                │   invariant    │
│ ⏻ BT │                                                │   chips:       │
│ ⚙ AB │                                                │  [ipcInv ✓]    │
│ ☰ CT │                                                │  [crossSub ✓]  │
├──────┴───────────────────────────────────────────────┴────────────────┤
│  ⏮  ◀  ▮▮  ▶  ⏭   step 78 / 234   [━━━━━━━●────────]  ⤳ branch  1.0×   │
│  IMT-014 · IPC · call/reply response registers: [100, 200]              │
└───────────────────────────────────────────────────────────────────────┘
```

The transport bar's caption line always shows the current event's
`scenarioId · subsystem · description`, so the user never loses the thread
between lenses.

### 8.1 Mission Control (dashboard)

- **Purpose.** The front door: prove "this kernel is real and verified" in
  ten seconds, then route each persona to its lens.
- **Primary persona.** Evaluator; entry point for all.
- **Data inputs.** `codebase_map.json.readme_sync` (metrics);
  `proof_index.json` (axiom status, invariant count); scenario registry
  (subsystem distribution); trace manifest.
- **Layout.** A metrics hero band over a clickable subsystem map and a
  "featured runs" strip.

```
┌──────────────────────────────────────────────────────────────────────┐
│  seLe4n — a microkernel proved in Lean 4                              │
│  ┌────────────┬────────────┬────────────┬────────────┬────────────┐  │
│  │ 11,510     │ ~6,000     │  0         │ 312        │ 4 cores    │  │
│  │ decls      │ theorems   │ sorry/axiom│ modules    │ RPi5       │  │
│  └────────────┴────────────┴────────────┴────────────┴────────────┘  │
│                                                                      │
│  Subsystems (size ∝ proved theorems, click to enter its lens):       │
│   ┌─────────┐ ┌──────┐ ┌──────────┐ ┌────────┐ ┌─────────────┐       │
│   │Scheduler│ │ IPC  │ │Capability│ │InfoFlow│ │ SMP/Concurr │  …    │
│   └─────────┘ └──────┘ └──────────┘ └────────┘ └─────────────┘       │
│                                                                      │
│  Featured runs:  ▶ Smoke trace (234 steps)  ▶ 4-core scheduler       │
│                  ▶ Call/Reply with donation  ▶ Non-interference demo │
└──────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** The "0 sorry/axiom" tile is the emotional anchor —
  rendered as a verified seal that, on click, opens the Proof Explorer
  filtered to the `#print axioms` evidence for the top-level bundle.
  Subsystem tiles are sized by theorem count and colored by the canonical
  subsystem palette (Appendix A).
- **Interactions.** Each metric links to its evidence (theorems →
  Explorer; modules → Atlas; cores → SMP Theater). Featured runs deep-link
  into the Trace Theater at step 0.
- **Cross-links.** Everything here is a launch point; nothing is terminal.
- **Edge cases.** If `proof_index.json` is absent (older bundle), the
  axiom tile shows "not computed" rather than a false "0".

### 8.2 Architecture Atlas (the module galaxy)

- **Purpose.** Show the whole kernel as a navigable dependency map:
  subsystems → modules → declarations. Answer "what is this kernel made
  of, and how do its parts depend on each other?"
- **Primary persona.** Dev, Evaluator, Learner.
- **Data inputs.** `codebase_map.json` (modules, `called[]` resolved to
  module-level import/dependency edges, per-module metrics); subsystem
  mapping (module-path prefix → subsystem).
- **Layout.** A zoomable graph with three levels of detail (LOD):

```
  LOD-0 (subsystems)      LOD-1 (modules in a subsystem)   LOD-2 (decls)
  ┌───────────────┐        ┌──────────────────────┐         theorem/def
  │  ⬡ IPC        │──┐     │ IPC.Operations.Endpoint│         nodes with
  │  ⬡ Scheduler  │  ├──►  │ IPC.Invariant.Defs     │  ──►    call edges
  │  ⬡ Capability │  │     │ IPC.DualQueue.Transport│         (hands off
  │  ⬡ …          │──┘     │ …                      │          to §8.3)
  └───────────────┘        └──────────────────────┘
   edges = inter-subsystem    edges = inter-module
   dependency volume          imports/calls
```

- **Visual encoding.** Subsystem = cluster hull in its palette color; node
  size ∝ declaration count or LOC (toggle); node ring ∝ theorem density;
  edge thickness ∝ number of cross-references; a heatmap mode recolors by
  a chosen metric (theorem count, LOC, proof fan-in, "most depended upon").
  Known large files (per `CLAUDE.md`) get a subtle "heavy" badge.
- **Interactions.** Zoom to expand LOD; click a module → Context Rail
  shows its declarations, metrics, and source link; double-click → enter
  the Proof Graph Explorer scoped to that module. Search highlights and
  flies to a node. A "dependency spotlight" dims everything except a
  node's neighborhood.
- **Cross-links.** Module → its scenarios (registry) → trace steps;
  module → Proof Explorer; declaration → §8.3.
- **Edge cases.** The full declaration graph is too large for LOD-2 on the
  whole kernel at once; LOD-2 is only entered *scoped* to a module or a
  selected subgraph (enforced by the loader), which also bounds memory.

### 8.3 Proof Graph Explorer (the proof cosmos)

- **Purpose.** Render the machine-checked proof as an explorable
  dependency DAG and let a user (a) trace any invariant down to its
  axiom-free leaves, (b) see what a theorem depends on and what depends on
  it, and (c) *see* that there are no `sorry`/`axiom` sinkholes.
- **Primary persona.** Auditor, Sec.
- **Data inputs.** `codebase_map.json` (11,510 nodes, 79,605 `called`
  edges); `proof_index.json` (invariant catalog, preservation theorems,
  `#print axioms` status, leaf classification).
- **Layout.** WebGL node-link canvas (Sigma.js) with a focus+context
  layout. Default entry is *scoped* — never "draw all 11k at once" — to one
  of: a chosen invariant's proof subgraph, a module, or a search result,
  then expand outward on demand.

```
┌───────────────────────────── Proof Cosmos ───────────────────────────┐
│  focus: ipcInvariantFull        depth:[3▾]  mode:[proof-of ▾]         │
│                                                                       │
│        ● ipcInvariantFull                                             │
│        ├─● dualQueueSystemInvariant ──● tcbQueueChainAcyclic          │
│        ├─● badgeWellFormed ───────────● wordBounded                   │
│        ├─● replyCallerLinkage                                         │
│        └─● ... (12 conjuncts)                                         │
│              proved-by ▸                                              │
│        ◆ endpointReply_preserves_ipcInvariantFull                     │
│              ├─● insertOrMerge_preserves_mem_of_ne   (lemma)          │
│              └─● ...                          ⟶ leaves: Lean core ✓   │
│                                                                       │
│  legend:  ● def/pred   ◆ theorem   ▲ structure   ○ leaf(core)        │
│           red ⌀ = sorry/axiom (none present)                          │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Node glyph by `kind` (theorem ◆, def/predicate ●,
  structure/inductive ▲, instance ◇); color by subsystem; **leaf nodes
  that resolve to Lean/Mathlib foundations render hollow green** ("grounded
  in core"); any `axiom`/`sorry`/`admit` would render as a red void —
  their *absence* is the visual proof of the headline claim. Edge direction
  = "depends on / proved using." Fan-in (how many proofs use this lemma) is
  encoded as a halo, surfacing keystone lemmas.
- **Interaction modes.**
  - *Proof-of:* given a theorem/invariant, show the downward cone (its
    dependencies) — "what must be true for this to hold."
  - *Used-by:* the upward cone (its dependents) — "what breaks if this
    changes." Powerful for impact analysis.
  - *Path:* shortest dependency path between two declarations.
  - *Axiom audit:* highlight the leaf frontier and annotate each with its
    `#print axioms` result; a side panel tallies the foundation set
    (`propext`, `Classical.choice`, `Quot.sound`) and asserts no others.
- **Interactions.** Click = focus + reframe; hover = signature tooltip
  (name, kind, module, line, fan-in/out counts); "pin" keeps a node while
  exploring; "collapse subtree" for big fan-outs; export the current
  subgraph as SVG/PNG for papers and audits.
- **Cross-links.** Theorem → the `Transition`(s) whose preservation it
  proves → the `Scenario`s → trace steps (the Proof Pivot in reverse:
  *"watch this theorem hold"*). Declaration → Atlas (its module).
- **Edge cases.** Performance is the hard constraint (§13): the canvas
  caps the live node count (e.g. ≤ ~3–5k visible) and expands via the
  depth control and pinning rather than dumping the whole graph; layouts
  are precomputed at build time so focus changes are reframes, not
  recomputations.

### 8.4 Trace Theater (the execution player)

- **Purpose.** Play the kernel's deterministic transition stream like a
  film: step, scrub, rewind, and branch, with each frame tied to its
  state and its proof.
- **Primary persona.** Dev, Learner (guided), all (it is the spine of the
  execution layer).
- **Data inputs.** A trace's `events.json` (E1) and `state.json` (E2);
  `scenario_registry.yaml` (+E4) for per-event metadata and proof links.
- **Layout.** A central **event stream** (the film) with a synchronized
  **mini-stage** that shows the most relevant subsystem widget for the
  current event, over the global transport bar.

```
┌──────────────────────────── Trace Theater ───────────────────────────┐
│  trace: main_trace_smoke      filter:[all subsystems ▾] [errors only]  │
│ ┌─────────────────────────────┐  ┌────────────────────────────────┐   │
│ │ EVENT STREAM (virtualized)  │  │ MINI-STAGE (context widget)    │   │
│ │ 76 IMT-009 rendezvous [99]  │  │   endpoint ep1                 │   │
│ │ 77 IMT-012 caller blocked ✓ │  │    sendQ: [ T1(call) ]         │   │
│ │▶78 IMT-014 reply regs[100,  │  │    recvQ: [ ]                  │   │
│ │            200]             │  │   T1: blockedOnReply→ready     │   │
│ │ 79 IMT-016 blockedOnCall ✓  │  │   reply r1: caller=T1→∅        │   │
│ │ 80 IMT-018 …                │  │   SC: server → caller (return) │   │
│ └─────────────────────────────┘  └────────────────────────────────┘   │
│  caption: call/reply response registers: [100, 200]                    │
│  invariants checked here: ipcInvariantFull ✓  crossSubsystem ✓ (38th)  │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Each event row shows `seq`, `scenarioId`,
  subsystem dot, a one-line human description, and an outcome glyph: ✓
  ok, ✗ expected-error (with the `KernelError` variant), ⊘ guard/branch,
  ◆ invariant-check (with running count, e.g. "38 passed"). Error events
  are *first-class and celebrated*, not hidden — the trace deliberately
  exercises rejection paths (e.g. `policyDenied`, `targetSlotOccupied`),
  and showing them teaches the kernel's defensive structure.
- **Transport & time-travel.** Play/pause, step ±1, jump to next
  error/next subsystem boundary/next invariant check, scrub the timeline,
  and set speed. Because transitions are pure, **reverse stepping is exact**
  — the app simply renders the prior snapshot; there is no re-simulation
  drift. **Branching:** at any step the user may fork "what if this had
  returned an error / taken the other arm?" creating a parallel timeline
  shown as a second track for side-by-side comparison (data permitting; in
  v1–v2 branches are limited to alternatives present in the trace corpus,
  full what-if arrives with the v3 live backend, §15).
- **Interactions.** Click an event → selects it everywhere (the mini-stage,
  State Inspector, and Context Rail all follow). Filter by subsystem,
  outcome, or scenario tag. "Open in lens" sends the current event to its
  native subsystem lens (an IPC event → §8.7).
- **Cross-links.** Event → Scenario → sourceFn (Atlas/Explorer) →
  Invariant → theorem (the full Proof Pivot, §5.3). Event → State
  Inspector at this step.
- **Edge cases.** Traces without E2 state data still play (events-only
  mode) with the mini-stage degraded to the textual checkpoint value;
  long traces are virtualized; the playhead URL is shareable (§9.4).

### 8.5 State Inspector (heap, capabilities, queues)

- **Purpose.** Open the kernel's state at any step and inspect every
  object and relationship, with full field-level detail and step-to-step
  diffing.
- **Primary persona.** Dev, Auditor.
- **Data inputs.** `state.json` (E2) baseline + deltas; object field
  schemas (§14.2, Appendix C); the entity model for resolving references.
- **Layout.** A master object list/grid (filterable by kind) → an object
  detail card → a relationship graph, with a diff gutter against any other
  step.

```
┌──────────────────────────── State Inspector @ step 78 ────────────────┐
│ objects:[all▾] [TCB][EP][Ntfn][CNode][VSpace][SC][Reply][Untyped]      │
│ ┌───────────────┐  ┌──────────────── TCB #1 (caller) ──────────────┐   │
│ │ #1  TCB  ●ready│  │ tid 1   prio 50   domain 0   core 0          │   │
│ │ #12 TCB  ⊘block│  │ ipcState: blockedOnReply → ready   ◆changed  │   │
│ │ #20 EP        │  │ schedContextBinding: donated→own   ◆changed  │   │
│ │ #21 Ntfn      │  │ replyObject: r1 → none             ◆changed  │   │
│ │ #30 CNode rdx8│  │ registerContext: x0=100 x1=200     ◆changed  │   │
│ │ #40 SC budget │  │ queuePrev/Next · pipBoost · timeSlice 5      │   │
│ │ #50 Reply r1  │  │ cspaceRoot→#30  vspaceRoot→#31  (clickable)  │   │
│ └───────────────┘  └──────────────────────────────────────────────┘   │
│  diff vs step:[77 ▾]   3 objects changed, 6 fields   [show only Δ]     │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Object kind has an icon + palette color; thread IPC
  state is a status chip (`ready` green, `blockedOn*` amber, `inactive`
  grey); changed fields since the diff baseline are marked ◆ and
  gutter-highlighted (added/removed/modified). References (`cspaceRoot →
  #30`, `boundNotification → #21`, `caller → T1`) are chips that navigate.
- **Specialized sub-inspectors** (tabs within the detail card, each
  rendering the right structure rather than raw fields):
  - **CSpace tree** — the CNode radix structure for a thread's
    `cspaceRoot`: guard/radix per level, slots, the capability in each
    slot (target, rights bits, badge). (Shared with §8.8.)
  - **Capability Derivation Tree (CDT)** — the `childMap`/`parentMap`
    forest: which cap derived which, the spine of revocation. (Shared with
    §8.8.)
  - **Endpoint queues** — `sendQ`/`receiveQ` as ordered intrusive lists
    with `queuePrev/queueNext` links drawn. (Shared with §8.7.)
  - **Run/replenish queues, page-table, sched-context** — hand off to the
    respective lenses (§8.6, §8.9, §8.10) for the rich view; the inspector
    shows the raw fields.
- **Interactions.** Filter/search objects; pin an object to watch it
  across steps (its card updates as the playhead moves, with a per-field
  sparkline of changes); "diff against step N" or "diff against start";
  follow any reference chip.
- **Cross-links.** Object → the trace events that wrote it (reverse index
  from the delta stream) → Proof Pivot for those transitions; capability →
  CDT and target object; thread → Scheduler lane and IPC switchboard.
- **Edge cases.** The object store can hold up to 65,536 ObjIds; the list
  is virtualized and defaults to "live objects in this trace" (typically a
  handful) with an opt-in to the full store. Reserved/sentinel ids
  (`ObjId 0`) are shown distinctly. Without E2, the inspector falls back to
  the per-checkpoint scalar the trace prints.

### 8.6 Scheduler Lane

- **Purpose.** Make scheduling decisions legible: who runs next and *why*
  — priority, EDF deadline, FIFO order, domains, time slices, priority
  inheritance, and CBS budgets.
- **Primary persona.** Dev, Learner, Sec (PIP/latency).
- **Data inputs.** `state.json` scheduler fields (per-core `runQueue`,
  `current`, `activeDomain`, `domainTimeRemaining`, `replenishQueue`); TCB
  `priority`/`deadline`/`timeSlice`/`pipBoost`/`schedContextBinding`;
  scheduler trace events (`DDT`, `STD`, `ICS`, `IDLE` tags).
- **Layout.** Priority-bucketed run-queue lanes with an EDF timeline and a
  PIP overlay; per-core when SMP is engaged (else boot core).

```
┌──────────────────────────── Scheduler Lane (core 0) ──────────────────┐
│ active domain: 1   domain time left: ▓▓▓▓▓░ 5   default slice: 5       │
│ prio                                                                   │
│ 200 │ ███ T12(d=∞)                                  ◀ chosen (EDF)     │
│ 100 │ ███ T7(d=40)  ███ T9(d=55)        FIFO→                          │
│  50 │ ███ T1(d=∞)  [running ●, slice ▓▓▓▓▓]                            │
│   0 │ ░ idle(65536)                                                    │
│     └────────────────────────────────────────────────────────────────│
│ EDF deadline axis:  T7│40   T9│55   ───────────────────▶ time          │
│ PIP: T1 ──boost──▶ T_server (effective prio 50→200) [chain depth 1]    │
│ CBS: T1 budget ▓▓▓▓░ 4/5   replenish@ t=120                            │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Each priority bucket is a lane; threads are blocks
  ordered FIFO within a lane; the running thread pulses and shows its
  time-slice draining; the EDF axis plots absolute deadlines and marks the
  chosen thread per the three-tier rule (deadline → priority → FIFO). PIP
  boosts draw as arrows from blocked donor to boosted server with the
  effective-priority delta; the blocking chain depth is annotated (and its
  acyclicity, `blockingChainAcyclic`, is a clickable invariant chip). CBS
  budgets are draining bars with the next replenishment instant.
- **Interactions.** Step the trace and watch threads move between lanes
  (enqueue/dequeue-on-dispatch animates); toggle "explain choice" to show
  the comparator that selected the current thread; hover a thread for its
  full scheduling parameters; switch core (SMP).
- **Cross-links.** Thread → State Inspector / IPC switchboard; "explain
  choice" → the `chooseThread`/`isBetterCandidate` source; latency claims →
  the WCRT theorem in the Proof Explorer; PIP chip → `blockingChainAcyclic`
  and the priority-inheritance proofs.
- **Edge cases.** Empty run queue → idle thread (`65536`) shown explicitly
  (matches `IDLE-*` trace events); domain switches animate the eligibility
  mask (only the active domain's threads are selectable).

### 8.7 IPC Switchboard

- **Purpose.** Animate the kernel's message-passing: dual-queue rendezvous
  on endpoints, notification signalling, the call/reply/replyRecv
  lifecycle, badges, capability transfer, and scheduling-context donation.
- **Primary persona.** Dev, Learner, Sec.
- **Data inputs.** `state.json` endpoint/notification/reply objects and
  TCB `ipcState`/`pendingMessage`/`replyObject`; IPC trace events
  (`IMT`, `RRC`, `MEI`, `CIC`, `LEP`, `ELC`, `Z7D` tags).
- **Layout.** Endpoint-centric: each endpoint shows its two queues with
  threads docked, and a central "wire" where messages animate from sender
  to receiver; reply objects and donation are drawn as overlays.

```
┌──────────────────────────── IPC Switchboard ─────────────────────────┐
│                         Endpoint ep20                                 │
│   senders (sendQ)              wire               receivers (recvQ)    │
│   ┌──────────┐                                    ┌──────────┐        │
│   │ T1 .call │ ═══ msg[100,200] badge=123 ═══════▶│ (empty)  │        │
│   └──────────┘      caps: ⟦cap→#21⟧ donated        └──────────┘        │
│        │                                                              │
│        └─ blockedOnReply ──▶ reply r1 { caller=T1, donatedSc=sc40 }   │
│                                                                       │
│   SchedContext donation:  T1.sc40 ──▶ server (passive)  budget moves  │
│   Notification ntfn21:  badge ▒▒▒ (OR-merge)  boundTCB=T_x            │
│   invariant: ipcInvariantFull ✓   dualQueue wellformed ✓              │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Threads dock in `sendQ`/`receiveQ` in FIFO order
  with their `ipcState` label (`blockedOnSend/Receive/Call/Reply`). A
  transfer animates the message payload (register vector), the badge, and
  any transferred capabilities along the wire; on rendezvous the matched
  thread un-docks and moves to its run queue (a cross-link pulse to the
  Scheduler lane). Reply objects render as a linked token between caller
  and server; **donation** draws the `SchedContext` physically moving from
  caller to passive server and back on reply (the `Z7D` donation events),
  with the `donationChainAcyclic` invariant chip. Notification badges show
  bitwise-OR accumulation.
- **Interactions.** Step through a send/recv/call/reply and watch each
  half of the rendezvous; "slow-mo" expands a single transition into its
  micro-steps (lookup → rights check → dequeue → transfer → wake →
  reschedule); hover the wire to inspect the `IpcMessage` (registers +
  extra caps + badge); toggle the lock-set overlay (which `LockId`s the
  transition holds, in hierarchy order — ties to §8.12).
- **Cross-links.** Rendezvous → Scheduler lane (the wake); message caps →
  Capability Forge; the transition → Proof Pivot (`ipcInvariantFull`
  preservation, the dual-queue membership theorems); reply replay attempt →
  the "reply-replay barrier" theorems (a delivered reply leaves the caller
  `.ready`, so replay fails closed — a great teachable security moment).
- **Edge cases.** Bounded-message rejection (`IMB` events: oversized
  registers/caps) animates as a bounced message with the bound annotation;
  stale-endpoint sends after retype (`ELC` events) show the
  `invalidCapability` rejection; multi-endpoint interleaving (`MEI`)
  supports showing several endpoints at once with FIFO ordering preserved.

### 8.8 Capability Forge (CSpace + derivation tree)

- **Purpose.** Visualize capability-based authority: the CSpace as a radix
  tree of CNodes, the rights/badges on each capability, and the capability
  derivation tree (CDT) that governs mint/copy/move/delete/revoke.
- **Primary persona.** Sec, Dev, Auditor.
- **Data inputs.** `state.json` CNode objects (`guardWidth`, `guardValue`,
  `radixWidth`, `slots`), `Capability` records (`target`, `rights`,
  `badge`), and the CDT indices (`cdt.childMap`/`parentMap`,
  `cdtSlotNode`/`cdtNodeSlot`); capability trace events (`ENT`, `LEP`,
  `CIC`, `KSD`, `MOV`, `SRG` tags).
- **Layout.** Split: a CSpace tree (how a thread *names* authority) beside
  the CDT forest (how authority was *derived*), with a rights/badge
  inspector.

```
┌────────────────── Capability Forge ──────────────────────────────────┐
│  CSpace of T1 (root CNode #30, radix 8)        Capability Derivation  │
│  ┌─ CNode #30 (guard 0/0, radix 8) ─┐          ┌─ root cap (untyped) ┐│
│  │ slot 0 → cap→EP#20  rights:RWG    │          │  └ mint → cap A      ││
│  │ slot 1 → cap→Ntfn#21 rights:--G   │          │       ├ copy → cap B ││
│  │ slot 2 → cap→CNode#33 (recurse ▸) │          │       └ mint → cap C ││
│  │ slot 7 → reply r1                 │          │            (revoke ⌫)││
│  └───────────────────────────────────┘          └─────────────────────┘│
│  selected cap → EP#20    rights [R][W][G][gR][rty]  badge=123          │
│  derivation: parent=cap A   children=[B,C]   subtree size=2            │
│  invariant: cdtNodeWellFormed ✓   revoke removes subtree (BFS)         │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** CNodes are compound nodes; slots are cells showing
  the resolved target and a compact rights badge (`R W G gR rty` lit/unlit
  bits from `AccessRightSet`); nested CNodes expand inline (the radix
  walk). The CDT is a forest where each node is a derived capability and
  edges are derivations; minting attenuates rights (the child's lit bits
  are a subset — shown as a visible narrowing); a revoke previews the BFS
  subtree it will remove before it happens.
- **Interactions.** Walk a `CPtr` resolution step-by-step (extract guard →
  match → extract radix → index slot → recurse), which doubles as a
  teaching tool for compressed-path CSpace; select a capability to see its
  rights, badge, target, and CDT lineage; replay a `mint`/`copy`/`move`/
  `delete` and watch the slot and CDT update; "preview revoke" highlights
  the transitive descendant set.
- **Cross-links.** Capability target → the object (State Inspector / its
  lens); CDT operations → Proof Pivot (`cdtMintCompleteness`, revocation
  coverage theorems); rights checks → the syscall rights mapping (§8.14).
- **Edge cases.** `targetSlotOccupied` on insert, self-move
  (`illegalState`), and fuel-exhausted revoke (`resourceExhausted` on
  pathological CDT depth) are shown as explicit guarded outcomes;
  `NonNullCap` vs null sentinel capabilities are visually distinct.

### 8.9 Address-Space Cartographer (VSpace / page tables)

- **Purpose.** Visualize virtual memory: ARMv8 address translation, the
  per-VSpace mappings, page permissions and the W^X policy, ASID binding,
  and TLB behavior.
- **Primary persona.** Dev, Sec.
- **Data inputs.** `state.json` `VSpaceRoot` objects (`asid`, `mappings:
  VAddr → (PAddr × PagePermissions)`), the `asidTable`, `tlb` state,
  machine `systemRegisters` (TTBR/TCR/SCTLR); architecture trace events
  (`CAT` tags: map/unmap/lookupFull/W^X/TLB).
- **Layout.** A translation strip (VA → PA with permissions) over a map of
  the VSpace, plus a TLB panel and the W^X/policy guard.

```
┌─────────────────── Address-Space Cartographer ───────────────────────┐
│ VSpace #31  asid 1  (ttbr0)        TLB: 0 entries  barrier: dsb ish ✓ │
│ translate VA 0x2000 ─────────────────────────────────────────────────│
│   [ L0 ▸ L1 ▸ L2 ▸ L3 ]  ──▶  PA 0x2000   perms: R  -  -   (W^X ok)   │
│ mappings:                                                             │
│   VA 0x1000 → PA 0x1000  R W -   user                                 │
│   VA 0x2000 → PA 0x2000  R - -   (mapped, exec denied)                │
│   VA 0x3000 → ✗ unmapped → translationFault                          │
│ guard: map VA 0x4000 R W X  ⟶ policyDenied (W^X violation) ✗          │
│ out-of-bounds: map @ 2^48  ⟶ addressOutOfBounds ✗                    │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** The translation renders as a staged walk (model is
  a flat `RHTable` map, but the walk is shown as the ARMv8 L0–L3 levels for
  pedagogy, annotated as "modeled as O(1) hash lookup"); each mapping row
  shows VA → PA with R/W/X/user/cacheable bits; a **W^X violation** glows
  red and is rejected (`policyDenied`); unmapped lookups show
  `translationFault`; out-of-range shows `addressOutOfBounds`. The TLB
  panel shows cached entries and flush events with the emitted barrier
  witness (`dsb ish; isb`).
- **Interactions.** Enter a VA to translate; replay map/unmap and watch the
  mapping table and TLB update; toggle the permission overlay; inspect ASID
  binding (`asidTable` → VSpaceRoot). On SMP, the inner-shareable barrier
  and TLB-shootdown SGI cross-link to §8.12.
- **Cross-links.** Mapping ops → Proof Pivot (`VSpaceInvariant`, W^X
  compliance, no-virtual-overlap); TLB shootdown → SMP Theater; page frame
  caps → Capability Forge.
- **Edge cases.** Device vs normal memory, cacheability, and the
  no-physical-frame-collision property (not structurally enforced — shown
  as a checked-at-map-time guard, honest about the model boundary).

### 8.10 SchedContext & Budget Studio

- **Purpose.** Make CPU-time-as-a-capability tangible: budgets, periods,
  replenishment, CBS bandwidth isolation, passive-server donation, and
  budget-driven IPC timeouts.
- **Primary persona.** Dev, Sec, Learner (real-time concepts).
- **Data inputs.** `state.json` `SchedContext` objects (budget, period,
  remaining, deadline, domain, bound thread), per-core `replenishQueue`,
  TCB `schedContextBinding`/`timeoutBudget`/`timedOut`; sched-context trace
  events (`SCO`, `Z7D`, `Z8J` tags).
- **Layout.** Per-sched-context budget timelines with a replenishment
  queue and a bandwidth-admission gauge.

```
┌─────────────────── SchedContext & Budget Studio ─────────────────────┐
│ sc40  budget 5 / period 100   bound: T1   domain 0                    │
│ budget:  ▓▓▓▓▓ 5 ─tick▶ ▓▓▓▓░ 4 ─▶ ▓▓░░░ 2 ─▶ ░░░░░ 0  preempt! ⟶    │
│          └──────────── replenish @ t=100 ──────────▶ ▓▓▓▓▓ 5          │
│ replenish queue (core 0):  [ sc40@100 ] [ sc55@130 ]                  │
│ admission (Σ budget/period ≤ 1):  ▓▓▓▓▓▓░░░░ 0.62  ✓ admit sc55       │
│ donation:  caller sc40 ─▶ passive server (consumes 0 when idle)       │
│ timeout:   T blocked > budget ⟶ timeoutThread ⟶ re-enqueue ✓          │
│ invariants: cbs_bandwidth_bounded ✓  donationChainAcyclic ✓           │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Budget is a draining bar over a tick axis; period
  boundaries mark replenishment refills; the replenishment queue is a
  deadline-ordered list per core; the admission gauge sums `budget/period`
  bandwidth and shows accept/reject against the 100% bound. Donation draws
  the context migrating to a passive server (zero consumption when not
  serving) and returning on reply. Timeout shows a blocked thread spliced
  from its endpoint queue and re-enqueued on budget exhaustion.
- **Interactions.** Step ticks to watch budget drain, exhaust, preempt, and
  replenish (the `Z8J` lifecycle); bind/unbind a context to a thread and
  watch the run-queue re-bucket; trigger an admission test; follow a
  donation across an IPC call.
- **Cross-links.** Bandwidth/latency → Proof Pivot (`cbs_bandwidth_bounded`,
  the WCRT bound across the liveness modules); donation → IPC Switchboard;
  bound thread → Scheduler lane.
- **Edge cases.** Validation guards (`SCO` events: zero-period,
  budget>period, priority>max, domain≥16, zero-budget) each show the
  `invalidArgument` rejection with the offending parameter highlighted.

### 8.11 Information-Flow Lens (non-interference made visible)

- **Purpose.** *Show*, not just assert, the kernel's non-interference
  guarantee: a security domain's observable view of the state, and the
  fact that actions by a higher-clearance domain leave the lower view
  unchanged.
- **Primary persona.** Sec, Auditor, Evaluator (this is a flagship demo).
- **Data inputs.** `proof_index.json` non-interference catalog (the
  `ObservableState` projection fields, `lowEquivalent`/`lowEquivalent_smp`,
  the `NonInterferenceStep` constructors); `state.json` for the concrete
  state to project; the security-label assignment (labels on
  objects/threads/services); infoflow trace events (`InformationFlow`
  scenarios, the `SGT`/policy events).
- **Layout.** A side-by-side: the **full state** (privileged view) beside
  the **low projection** (what the chosen observer can see), with a step
  control that performs a high action and a verdict strip.

```
┌─────────────────── Information-Flow Lens ────────────────────────────┐
│ observer label:[ Low ▾ ]   policy: securityFlowsTo (N-domain)        │
│ ┌──────────── FULL STATE ───────────┐ ┌──── LOW PROJECTION ────────┐ │
│ │ objects: #1(L) #12(H) #20(L) #21(H)│ │ objects: #1(L) #20(L)      │ │
│ │ runnable: [T1(L), T12(H)]          │ │ runnable: [T1]             │ │
│ │ current: T12(H)                    │ │ current: ·(masked)         │ │
│ │ services: {api(L), secret(H)}      │ │ services: {api}            │ │
│ │ TCB#12: regs, sc, replyObj … (H)   │ │ (TCB#12 not observable)    │ │
│ └────────────────────────────────────┘ └────────────────────────────┘ │
│ action: ▶ HIGH thread T12 sends secret IPC                            │
│ verdict:  LOW projection BEFORE ≡ AFTER   →  NON-INTERFERENCE HOLDS ✓ │
│ proof: step_preserves_projection ▸  composedNonInterference_step ▸    │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Every object/thread/service carries a label badge
  (L/H or an N-domain color). The projection panel literally *removes or
  masks* what the observer cannot see (high objects, the boot-core
  `current` when high, CNode slots to high targets, the stripped TCB
  fields: `registerContext`, `schedContextBinding`, `pipBoost`,
  `pendingMessage`, …). When a high action runs, the low panel is diffed
  against itself before/after; **equality is rendered as a satisfying
  "unchanged" pulse** — the visual embodiment of the proof. A *covert*
  attempt (a high action that would change the low view) would light the
  diff red — used to demonstrate the policy gates (`flowDenied`).
- **Interactions.** Choose the observer label; pick a high action from the
  trace; watch the projection hold; toggle which projection fields are
  shown; switch boot-core vs per-core/∀-core projection
  (`lowEquivalent_smp`). An "honest boundaries" toggle surfaces the
  *documented* coverage gaps (e.g. service-layer flows treated as trusted)
  so the lens never over-claims — it shows exactly what is and isn't
  proved.
- **Cross-links.** The verdict → Proof Pivot (`step_preserves_projection`,
  `composedNonInterference_step`, the 35-constructor `NonInterferenceStep`
  inductive); labels → the objects in the State Inspector; policy gate →
  the `SGT`/enforcement-boundary events.
- **Edge cases.** Must faithfully represent the model's *actual* projection
  (driven by `proof_index.json`, not hard-coded), including the explicitly
  accepted covert channels — surfacing them, per the project's honesty
  rules, rather than hiding them.

### 8.12 SMP Multi-Core Theater

- **Purpose.** Visualize the multi-core kernel: per-core scheduling,
  cross-core IPC via software-generated interrupts (SGIs), the lock
  hierarchy, two-phase locking, and the deadlock-freedom guarantee.
- **Primary persona.** Dev, Sec, Auditor.
- **Data inputs.** `state.json` per-core scheduler fields
  (`currentOnCore`, `runQueueOnCore`, `activeDomainOnCore`,
  `regsOnCore`); the `smp_4core_scheduler` trace; lock state (per-object
  `RwLockState`, `objStoreLock`, the `LockKind` hierarchy and `LockId`s);
  SGI events; `proof_index.json` (deadlock-freedom, serializability,
  TicketLock/RwLock refinement).
- **Layout.** Four core lanes (RPi5) with per-core current/run-queue, a
  cross-core SGI arc layer, and a lock-hierarchy ladder showing held locks.

```
┌────────────────────── SMP Multi-Core Theater (RPi5: 4 cores) ────────┐
│ core0 ▸ run:[T1] cur:T1   core1 ▸ run:[T9] cur:B   core2 ▸ cur:C      │
│ core3 ▸ run:[ ] cur:idle                                             │
│   wake D from core0 ───SGI .reschedule (INTID 0)──▶ core3 ⟶ dispatch │
│   round-trip: wake blocked E ──SGI──▶ core3 handler ⟶ current=E      │
│                                                                       │
│ Lock hierarchy (acquire in increasing level — 2PL):                  │
│   L0 objStore  L1 untyped  L2 cnode  L3 tcb  L4 endpoint  L5 ntfn     │
│   L6 reply  L7 schedContext  L8 vspaceRoot  L9 page                   │
│   held by core0: [ L4 endpoint#20 ] [ L3 tcb#1 ] ✗ ORDER? → see note │
│   2PL grow/shrink: ▓▓▓▓ grow ─┊─ shrink ░░░   deadlock-free ✓        │
│ SGI kinds: reschedule | tlbShootdownReq/Ack | cacheBroadcast | halt  │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Each core is a lane with its current thread, run
  queue, and active domain; `determineTargetCore` routing is shown when a
  thread is placed; **cross-core wakes draw as labeled SGI arcs** between
  cores (INTID 0–4, color-coded by `SgiKind`), matching the
  `smp_4core_scheduler` trace ("wake D from core 0 emits SGI reschedule to
  core 3"). The **lock hierarchy** is a 10-rung ladder (L0 objStore … L9
  page); locks a core holds light up at their rung, and 2PL is shown as a
  grow/shrink phase bar. Because acquisition is constrained to increasing
  `LockId` order, a wait-for cycle is impossible — the lens can *attempt*
  to construct a cycle and show it being refused (the visual form of
  `LockId.lt_irrefl` ⟹ deadlock-freedom).
- **Interactions.** Step the SMP trace; watch per-core dispatch and SGI
  delivery; inspect a core's held lock-set in hierarchy order; "attempt
  deadlock" demo (two cores grabbing locks) shows the order constraint
  forbidding the cycle; toggle TLB-shootdown choreography (req → remote
  invalidate → ack).
- **Cross-links.** SGI → the cross-core dispatch transition and its proof
  (`endpointCall…CrossCoreDispatch`, the SGI-emission theorems); lock-set →
  Proof Pivot (2PL atomicity, `Serializability`, deadlock-freedom);
  per-core current → Scheduler lane for that core.
- **Edge cases.** Single-core inertness (the cross-core machinery must be a
  no-op on the boot core) is shown explicitly; the TicketLock/RwLock
  primitives link to their refinement proofs; locks held vs the hierarchy
  are validated so any (hypothetical) inversion is flagged.

### 8.13 Boot & Hardware Lens

- **Purpose.** Show how the verified model meets real silicon: the boot
  sequence, the Lean↔Rust HAL FFI boundary, the RPi5 (BCM2712) platform
  binding, and device-tree-driven configuration.
- **Primary persona.** Dev, Evaluator.
- **Data inputs.** `PlatformBinding` contract data (machineConfig,
  coreCount, bootCoreId, sharingDomain), the boot sequence model, the FFI
  surface (`@[extern]`/`@[export]` declarations from `codebase_map.json`),
  `qemu_boot_expected.txt`, device-tree parsing model; `Platform`
  scenarios.
- **Layout.** A boot timeline over a HAL-boundary diagram and a platform
  fact-sheet.

```
┌──────────────────── Boot & Hardware Lens ────────────────────────────┐
│ RPi5 / BCM2712 · 4× Cortex-A76 · ARMv8-A · GIC-400 · 54MHz timer      │
│ boot: UART ▸ MMU ▸ GIC ▸ Timer ▸ TPIDR_EL1=per-cpu ▸ PSCI secondaries │
│        ●────●────●────●────────●─────────────────●  Boot complete ✓   │
│ FFI boundary:                                                         │
│   Lean ──@[extern]──▶ Rust HAL:  timerRead · gicAck/Eoi · tlbi · sgi  │
│   Rust ──@[export]──▶ Lean core: syscall_dispatch · suspend_thread    │
│ device tree (FDT): RAM regions ▸ untyped partition · IRQs · CPU topo  │
│ contract: bootContract ✓  runtimeContract ✓  interruptContract ✓     │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** The boot sequence is a checkpointed timeline keyed
  to `qemu_boot_expected.txt` fragments (BOOT_BANNER, UART_INIT, MMU_INIT,
  GIC_INIT, TIMER_INIT, TPIDR_SET, PER_CPU_ID, BOOT_DONE). The FFI boundary
  is a two-column diagram: verified Lean on one side, Rust HAL on the
  other, with arrows labeled by the actual extern/export symbols; the
  boundary line is annotated "trust boundary — HAL is outside the proof."
  The platform fact-sheet renders the `PlatformBinding` contract fields.
- **Interactions.** Step the boot sequence; click an FFI symbol to see its
  Lean declaration and its role; inspect the device-tree-derived untyped
  partition feeding the boot state; toggle QEMU vs hardware notes.
- **Cross-links.** Boot state → State Inspector at step 0 (the initial
  `SystemState`); contracts → Proof Pivot (boot/runtime/interrupt contract
  witnesses, `untypedRegionsDisjoint`); coreCount → SMP Theater.
- **Edge cases.** Honestly marks the HAL as an unverified trust boundary
  and the boot orchestration scope limits; QEMU-informational vs
  hardware-validated checks are distinguished.

### 8.14 ABI / Syscall Lens

- **Purpose.** Show the user/kernel ABI: the 29 syscalls, message encoding
  (MessageInfo bit layout), register layout, and the Lean↔Rust
  conformance (the cross-validation roundtrips).
- **Primary persona.** Dev, Auditor.
- **Data inputs.** The `SyscallId` enum and rights mapping; `MessageInfo`
  bit layout; the `XVAL` cross-validation trace events (Lean↔Rust
  roundtrip vectors); register-decode events (`RDT`, `KSD`, `PIP`, `SGT`
  tags).
- **Layout.** A syscall reference grid over an encode/decode bit-field
  visualizer and a conformance panel.

```
┌──────────────────────── ABI / Syscall Lens ──────────────────────────┐
│ syscalls (29):  send(0) recv(1) call(2) reply(3) … replyRecv(16) …    │
│   bind/unbindNtfn(26/27) mintReplyCap(28)   [filter by subsystem]     │
│ selected: call(2)   rights req: .write   args: ep cap, msg, (reply)   │
│ MessageInfo bit layout:                                               │
│   ┌ label (…) ┬ caps (…) ┬ length (…) ┐  encoded=2386218             │
│   │  4660     │   2       │   42       │  ← XVAL-001 roundtrip ✓       │
│ register decode:  x0=syscall x1=capAddr x2..=msgRegs                  │
│ conformance: Lean ⇄ Rust  MessageInfo ✓  SyscallId(29) ✓  MintArgs ✓  │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Each syscall is a card (id, name, subsystem,
  required right, arg shape, error set). The `MessageInfo` encoder shows
  the bit fields (label/caps/length) packing into the encoded word, driven
  by the actual `XVAL` vectors (e.g. `encoded=2386218 length=42 extraCaps=2
  label=4660`). The conformance panel shows Lean⇄Rust roundtrips green
  (the trace's `XVAL-001..005`), making the "the Rust ABI agrees with the
  verified Lean ABI" property concrete.
- **Interactions.** Pick a syscall to see its full contract and jump to a
  trace step that invokes it; edit a `MessageInfo` and watch it
  encode/decode (a safe client-side calculator mirroring the model's bit
  layout); inspect the register-sourced syscall entry path (`RDT`).
- **Cross-links.** Syscall → its dispatch source (`API.lean`) and the
  transition's lens; rights → Capability Forge; roundtrip → the Rust
  conformance tests and `XVAL` events.
- **Edge cases.** Decode failures (`invalidSyscallNumber`,
  `invalidMessageInfo`, `invalidRegister`) are shown as the explicit
  rejections the `RDT` events exercise.

### 8.15 Scenario Catalog Browser

- **Purpose.** A searchable index of all 242 catalogued scenarios — the
  "table of contents" for kernel behavior — bridging the trace, source,
  and proof.
- **Primary persona.** All; especially Learner and Auditor.
- **Data inputs.** `scenario_registry.yaml` (+E4 linkage) — id, subsystem,
  source module+function, description, and (with E4) the exercised
  transition and invariant.
- **Layout.** A faceted table grouped by subsystem with counts (IPC 62,
  SchedContext 27, Architecture 27, Service 24, Lifecycle 24, Scheduler 20,
  Capability 20, RobinHood 12, ServiceRegistry 10, TwoPhaseArch 7, Platform
  6, ABI 5, Entry 4, InformationFlow 3, Testing 2).

```
┌──────────────────── Scenario Catalog (242) ──────────────────────────┐
│ search:[reply____]  subsystem:[IPC▾]  outcome:[any▾]                  │
│ ┌─────┬───────────┬──────────────────────────────┬──────────────────┐ │
│ │ ID  │ subsystem │ description                  │ links            │ │
│ │IMT- │ IPC       │ call/reply response regs     │ ▶trace ⌁src ❋proof│ │
│ │014  │           │ [100, 200]                   │                  │ │
│ │RRC- │ IPC       │ replyRecv caller unblocked   │ ▶trace ⌁src ❋proof│ │
│ │003  │           │                              │                  │ │
│ └─────┴───────────┴──────────────────────────────┴──────────────────┘ │
│ 62 IPC · 27 SchedContext · 27 Architecture · 24 Service · …           │
└───────────────────────────────────────────────────────────────────────┘
```

- **Visual encoding.** Faceted by subsystem (palette dots), each row a
  scenario with quick-links to its trace step, source function (Atlas), and
  governing proof (Explorer).
- **Interactions.** Full-text search; facet by subsystem/outcome; click any
  link to jump; "play all in subsystem" filters the Trace Theater.
- **Cross-links.** The universal launch table — every row is a tri-link
  into the three layers.
- **Edge cases.** Scenarios not yet E4-linked show trace+source but a
  "proof link pending" affordance rather than a broken link.

---

## 9. Cross-cutting interactions

### 9.1 The Proof Pivot (detailed)

The Context Rail (§8.0) is always present and always reflects the current
selection. It exposes three tabbed pivots — **Execution**, **State**,
**Proof** — populated by traversing the spine (§5.2):

- **Execution tab** — where in the trace this entity appears: the events
  that read/wrote it, with jump-to-step.
- **State tab** — the entity's concrete fields at the current step, with
  reference chips and a per-field change history sparkline.
- **Proof tab** — the governing invariant(s) as chips; expanding a chip
  reveals its definition, conjuncts, and the per-operation preservation
  theorem, each a one-click jump into the Proof Explorer; an "axioms"
  affordance shows the `#print axioms` grounding.

The pivot is **bidirectional and lossless**: from a theorem you can reach
the runs that exercise it; from a run you can reach the theorem that
proves it. This is the product's spine and its primary differentiator.

### 9.2 Global search & command palette (⌘K)

One palette searches across all entity types: declarations (by name),
modules, scenarios (by id/description), objects (by id), syscalls,
invariants, and trace events. Results are typed and route to the right
lens. Commands ("open trace X at step N", "diff step A vs B", "show proof
of `ipcInvariantFull`", "switch persona") are first-class palette entries.

### 9.3 Deterministic time-travel & branching

Because every transition is pure, the transport (§8.0) gives exact
forward/backward stepping with no re-simulation. **Comparison mode** pins
two steps (or two branches) and renders the State Inspector and any
subsystem lens in split view with a synchronized diff. **Branching**
forks the timeline; v1–v2 supports branches that exist in the trace corpus
(e.g. the error-arm vs success-arm pairs the harness already exercises),
v3's live runner (§15) supports arbitrary what-if forks.

### 9.4 Deep-linking (URL-as-state)

The full UI state is URL-encoded: lens, trace, step, selected entity,
diff baseline, persona, density, and graph focus. Every view is therefore
shareable and bookmarkable — an auditor can link a colleague directly to
"the step where the reply consumes the donation, with the proof open." The
URL also carries the bundle hash so a link always resolves to the kernel
revision it was made against.

### 9.5 Annotations & shareable tours

Users can drop notes on a step, an object, or a theorem and export an
ordered **tour** (a sequence of deep links + captions). Tours power the
Learner's guided mode and let maintainers ship "explainers" (e.g. "how a
call/reply donation works in 6 steps") as shareable artifacts.

### 9.6 Honest-boundary affordance

A global toggle surfaces, in every lens, the project's *documented* model
boundaries and accepted gaps (service-layer info-flow as trusted, HAL
outside the proof, fuel-bounded traversals, etc.), drawn from the proof
index. This enforces the project's honesty rule at the UI level: the
Observatory never lets a visualization over-claim what is proved.

---

## 10. Information architecture & navigation

- **Top bar:** product mark, command palette (⌘K), persona switch, density
  switch, bundle/commit badge.
- **Lens rail (left):** the 15 lenses (§8), grouped: *Overview* (Mission
  Control, Atlas, Scenario Catalog), *Execution* (Trace Theater, State
  Inspector), *Subsystems* (Scheduler, IPC, Capability, VSpace,
  SchedContext), *Assurance* (Proof Explorer, Information-Flow, SMP),
  *Platform* (Boot/Hardware, ABI). The rail reorders by persona.
- **Stage (center):** the active lens.
- **Context Rail (right):** selection + Proof Pivot (§9.1), collapsible.
- **Transport bar (bottom):** present in every execution-aware lens;
  hidden in pure-static lenses (Atlas, Proof Explorer) unless a trace is
  pinned.
- **Breadcrumbs:** subsystem ▸ module ▸ declaration, or trace ▸ step ▸
  entity, depending on lens.

Selection is **global**: an entity selected in one lens stays selected
across lens switches, so the user investigates *a thing* through multiple
lenses rather than losing context at each hop. The back/forward history is
a navigation stack over (lens, selection, step) triples.

---

## 11. Visual & interaction design language

### 11.1 Principles

1. **Rigor first, delight second.** This visualizes a proof system; the
   aesthetic is precise, calm, and legible. Motion clarifies causality
   (a wake, a transfer, a boost) and is never decorative.
2. **One palette, everywhere.** Subsystems own colors (Appendix A) and
   that mapping is invariant across all lenses, so color *means* the same
   thing in the Atlas, the trace, and the proof graph.
3. **Semantics have a fixed visual vocabulary.** ✓ ok (green), ✗
   expected-error (amber, never alarming red — rejections are correct
   behavior), ⊘ guarded branch, ◆ invariant check / changed field, ○
   axiom-free leaf, ⌀ (red) a `sorry`/`axiom` (whose *absence* is the
   point). These glyphs are identical in every view.
4. **Density is a control, not a redesign.** Guided/Curated/Expert change
   how much is shown and how much is explained, over the same layout.

### 11.2 Color, type, motion

- **Color.** A dark, observatory-toned base (deep slate) with a
  subsystem-coded accent set chosen to be color-blind-safe (Appendix A
  pairs every hue with an icon and a label so color is never the sole
  channel). Semantic colors (ok/err/branch/changed) are reserved and never
  reused for subsystems.
- **Typography.** A humanist sans for UI; a **monospace** (with Lean
  ligatures) for all Lean identifiers, signatures, and proof snippets —
  code is always visually distinct from prose.
- **Motion.** Transitions animate the *causal* element only: the message
  along the IPC wire, the thread un-docking to its run queue, the budget
  bar draining, the SGI arc firing, the low-projection "unchanged" pulse.
  Respect `prefers-reduced-motion` (§12) by collapsing animations to
  before/after states.

### 11.3 The light astronomy metaphor

The "Observatory" framing gives a *restrained* visual through-line:
subsystems read as constellations in the Atlas, the proof DAG as a cosmos,
traces as orbits along the timeline. The metaphor aids orientation
(consistent spatial mental model) but never overrides legibility — labels,
not vibes, carry meaning. It is a garnish on a rigorous core, not the
core.

### 11.4 Reusable components

Object cards, invariant chips, the transport bar, the diff gutter, the
rights-bit badge, the lock-ladder, the queue lane, the bit-field
visualizer, and the graph canvas are shared components with a single
implementation each, so every lens renders the same concept identically.

---

## 12. Accessibility & internationalization

- **Keyboard-first.** Every interaction has a keyboard path: transport
  (space = play/pause, ←/→ = step, shift+←/→ = jump to boundary), lens
  switching, palette (⌘K), graph navigation (focus/expand/collapse via
  arrow keys + enter). No interaction is mouse-only.
- **Screen readers for graphs.** Graphs ship a parallel accessible
  representation: a focusable, navigable tree/list of the same
  nodes/edges with ARIA labels (name, kind, relationships), so the proof
  graph and state graph are traversable non-visually. Trace events are a
  semantic list; the playhead announces each step's caption.
- **Color independence.** Per §11, color is never the sole channel: every
  subsystem hue is paired with an icon + text label; every semantic state
  has a glyph; the palette is color-blind-safe and ships a high-contrast
  theme.
- **Reduced motion.** `prefers-reduced-motion` collapses all animation to
  instantaneous before/after states without losing information.
- **Internationalization.** UI strings are externalized; the project
  already maintains ten locales (`docs/i18n/*`: zh-CN, es, ja, ko, ar, fr,
  pt-BR, ru, de, hi), so the shell adopts the same locale set, including
  RTL support for Arabic. Kernel identifiers and Lean snippets remain
  untranslated (they are code); captions and explainers are localized.
- **Density & guided mode** double as accessibility aids: Guided mode's
  plain-language captions help non-expert and cognitively-diverse users.

---

## 13. Performance & scale engineering

The binding constraint is the proof graph: **11,510 nodes / 79,605 edges**,
and a ~5 MB `codebase_map.json` (161k lines). The state stream and traces
are comparatively small but unbounded in principle. Strategy:

- **Precompute layouts at build time.** Force-directed layouts for the
  Atlas and Proof Explorer are computed by `build_observatory_data.py`
  (§6.3) and shipped as node coordinates. The browser never runs a cold
  global layout; focus changes are camera moves and local relayouts only.
- **Level-of-detail + scoping.** The Atlas renders subsystem/module LOD by
  default; declaration-level (LOD-2) is only ever loaded *scoped* to a
  module or a selected subgraph. The Proof Explorer caps live nodes
  (≈3–5k) and grows via the depth control and pinning, never "draw all."
- **WebGL rendering.** Sigma.js/WebGL for any canvas exceeding ~1k nodes;
  Cytoscape/SVG for the bounded structured graphs (CDT, CSpace, lock
  ladder, page-table tree) which are small by construction.
- **Chunked, lazy, cached data.** The codebase map is split per module and
  per subsystem; chunks load on demand and cache in IndexedDB keyed by the
  bundle hash. Trace `state.json` loads as baseline + a **window of deltas**
  around the playhead, so even a very long trace has bounded memory.
- **Workers.** Layout refinement, diff computation, and search indexing run
  in Web Workers; the main thread stays responsive (60 fps target for
  transport and pan/zoom).
- **State deltas, not snapshots.** E2 emits deltas; the app reconstructs
  any step by folding deltas over the baseline (and memoizes keyframes
  every N steps for O(1)-ish seeks). Diffing two steps is a delta
  comparison, not a full-state walk.
- **Budgets.** Initial load (Mission Control) < 2 s on broadband; lens
  switch < 200 ms (data cached); transport step < 16 ms (one frame);
  Proof-Explorer focus change < 100 ms; search results < 50 ms. These are
  tracked as CI performance assertions against representative bundles.
- **Graceful degradation.** On low-power devices, the app drops to
  SVG/canvas fallbacks, lowers LOD thresholds, and disables non-essential
  motion; functionality is preserved, fidelity scales down.

---

## 14. Data contracts (schemas)

All schemas are versioned (`schemaVersion`) and validated by
`build_observatory_data.py` (§6.3) and by a CI schema-check. Types are
shown as illustrative JSON; the implementation generates TypeScript types
from these for the loaders (`src/data/`). ObjId/ThreadId/etc. are emitted
as plain integers with a sibling `kind` tag where the type is ambiguous.

### 14.0 Bundle manifest (`manifest.json`)

```json
{
  "schemaVersion": "1.0.0",
  "bundleHash": "sha256:…",
  "sourceCommit": "c795063…",
  "kernelVersion": "0.31.151",
  "leanToolchain": "v4.28.0",
  "codebaseMapDigest": "sha256:ba03f5…",
  "metrics": { "modules": 312, "declarations": 11510, "edges": 79605,
               "provedTheorems": 6097, "sorryAxiomCount": 0,
               "productionLoc": 183439, "coreCount": 4 },
  "subsystems": [ { "id": "IPC", "color": "#5BA8FF", "icon": "envelope",
                    "theoremCount": 812 }, … ],
  "traces": [ { "id": "main_trace_smoke", "title": "Smoke trace",
                "events": 234, "hasState": true,
                "eventsUrl": "traces/main_trace_smoke/events.json",
                "stateUrl": "traces/main_trace_smoke/state.json" },
              { "id": "smp_4core_scheduler", "events": 14, "hasState": false } ],
  "chunks": { "atlas": "atlas/index.json",
              "proofIndex": "proof/index.json",
              "declarationsByModule": "proof/by-module/{module}.json" }
}
```

### 14.1 Trace event (E1) — `traces/<id>/events.json`

```json
{
  "schemaVersion": "1.0.0",
  "traceId": "main_trace_smoke",
  "events": [
    {
      "seq": 78,
      "tag": "IMT-014",
      "scenarioId": "IMT-014",
      "subsystem": "IPC",
      "sourceFn": "SeLe4n.Testing.runIpcMessageTransferTrace",
      "transition": "endpointReplyCrossCoreDispatch",
      "kind": "transition",
      "label": "call/reply response registers",
      "value": { "type": "registers", "data": [100, 200] },
      "outcome": { "status": "ok" },
      "stateRef": { "step": 78 },
      "invariantsChecked": ["ipcInvariantFull", "crossSubsystemInvariant"],
      "invariantCheckCount": 38
    },
    {
      "seq": 12,
      "tag": "CAT-017",
      "subsystem": "Architecture",
      "kind": "guard",
      "label": "vspace map W^X violation correctly rejected",
      "value": { "type": "error",
                 "data": "SeLe4n.Model.KernelError.policyDenied" },
      "outcome": { "status": "expectedError",
                   "error": "policyDenied" }
    }
  ]
}
```

`kind ∈ {transition, guard, invariantCheck, snapshot, scheduling, sgi}`.
`outcome.status ∈ {ok, expectedError, branch}`. `value.type ∈ {registers,
error, bool, nat, option, struct, list, text}` mirrors the `reprStr`
shapes the human trace prints, so E1 is a structured superset of the
existing fixture (and is verified against it line-for-line).

### 14.2 State snapshot & delta (E2) — `traces/<id>/state.json`

```json
{
  "schemaVersion": "1.0.0",
  "traceId": "main_trace_smoke",
  "baseline": {
    "step": 0,
    "objects": {
      "1":  { "kind": "tcb", "tid": 1, "priority": 50, "domain": 0,
              "ipcState": { "tag": "ready" }, "threadState": "Ready",
              "cspaceRoot": 30, "vspaceRoot": 31, "timeSlice": 5,
              "deadline": 0, "schedContextBinding": { "tag": "own", "sc": 40 },
              "replyObject": null, "pipBoost": null, "cpuAffinity": null,
              "registerContext": { "pc": 0, "sp": 0, "gpr": { "x0": 0 } } },
      "20": { "kind": "endpoint", "sendQ": { "head": null, "tail": null },
              "receiveQ": { "head": null, "tail": null } },
      "21": { "kind": "notification", "state": "idle",
              "waitingThreads": [], "pendingBadge": null, "boundTCB": null },
      "30": { "kind": "cnode", "guardWidth": 0, "guardValue": 0,
              "radixWidth": 8,
              "slots": { "0": { "target": { "kind": "object", "oid": 20 },
                                "rights": { "bits": 7 }, "badge": null } } },
      "40": { "kind": "schedContext", "budget": 5, "period": 100,
              "remaining": 5, "boundThread": 1, "domain": 0 }
    },
    "scheduler": {
      "perCore": [ { "core": 0, "current": 1,
                     "runQueue": { "buckets": { "50": [1] } },
                     "activeDomain": 0, "domainTimeRemaining": 5,
                     "replenishQueue": [] } ],
      "domainSchedule": [ { "domain": 0, "length": 5 } ],
      "configDefaultTimeSlice": 5
    },
    "cdt": { "nodes": { … }, "childMap": { … }, "parentMap": { … } },
    "asidTable": { "1": 31 }, "tlb": { "entries": [] },
    "labels": { "objects": { "1": "Low", "12": "High" } }
  },
  "deltas": [
    { "step": 78, "byEvent": 78,
      "changes": [
        { "op": "set", "path": "objects.1.ipcState", "value": { "tag": "ready" } },
        { "op": "set", "path": "objects.1.schedContextBinding",
          "value": { "tag": "own", "sc": 40 } },
        { "op": "set", "path": "objects.1.replyObject", "value": null },
        { "op": "set", "path": "objects.1.registerContext.gpr.x0", "value": 100 },
        { "op": "set", "path": "objects.50.caller", "value": null } ],
      "writtenObjects": [1, 50] }
  ],
  "keyframes": [0, 50, 100, 150, 200]
}
```

Deltas are JSON-Pointer-style path edits (`set`/`del`/`insert`).
`writtenObjects` powers the State Inspector's reverse index (object → the
events that wrote it). `keyframes` are full snapshots every N steps for
fast seeking. Field names mirror the kernel structures exactly (Appendix
C), so the inspector needs no translation layer.

### 14.3 Proof index (E3) — `proof/index.json`

```json
{
  "schemaVersion": "1.0.0",
  "invariants": [
    {
      "name": "ipcInvariantFull",
      "decl": { "module": "SeLe4n.Kernel.IPC.Invariant.Defs", "line": 238 },
      "summary": "Endpoint dual-queue well-formedness, link integrity, "
               + "acyclicity, bounded messages, badge well-formedness, "
               + "reply-caller linkage.",
      "conjuncts": [
        { "name": "dualQueueSystemInvariant", "summary": "sendQ/receiveQ "
          + "well-formed; TCB links bidirectional; chains acyclic." },
        { "name": "badgeWellFormed", "summary": "all badges ≤ 64 bits." },
        { "name": "replyCallerLinkage", "summary": "TCB↔Reply links agree." }
      ],
      "preservedBy": [
        { "transition": "endpointReplyCrossCoreDispatch",
          "theorem": "endpointReply…_preserves_ipcInvariantFull",
          "decl": { "module": "…EndpointReply", "line": 412 } }
      ],
      "axiomStatus": { "checked": true,
                       "axioms": ["propext", "Classical.choice", "Quot.sound"],
                       "hasSorry": false, "hasAxiom": false }
    }
  ],
  "foundationAxioms": ["propext", "Classical.choice", "Quot.sound"],
  "boundaries": [
    { "id": "service-layer-infoflow",
      "summary": "Service dependency-graph flows treated as trusted; "
               + "documented accepted covert channel.",
      "ref": "docs/spec/SELE4N_SPEC.md §11.2" }
  ]
}
```

`axiomStatus` is the data behind the "zero `axiom`/`sorry`" claim — the
Information-Flow lens and Mission Control read it directly. `boundaries`
feeds the honest-boundary affordance (§9.6).

### 14.4 Declaration graph — reuse `codebase_map.json`

The Proof Explorer and Atlas consume the existing
`codebase_map.json.modules[].declarations[] = {kind, name, line, called[]}`
verbatim; `build_observatory_data.py` adds derived fields (`callers[]`,
`subsystem`, `fanIn`, `fanOut`, precomputed `layout: {x, y}`) into the
chunked per-module files, never mutating the canonical artifact.

### 14.5 Scenario record (E4) — augmented `scenario_registry.yaml`

```yaml
IMT-014:
  source: SeLe4n/Testing/MainTraceHarness.lean
  function: runIpcMessageTransferTrace
  subsystem: IPC
  description: "call/reply response registers: [100, 200]"
  transition: endpointReplyCrossCoreDispatch   # E4 (optional)
  invariant: ipcInvariantFull                  # E4 (optional)
```

Existing consumers (`scenario_catalog.py`) ignore unknown keys; the two
new keys are optional and validated when present.

---

## 15. Backend / API design (live "what-if" mode, v3)

v1–v2 ship no backend. v3 adds an **optional** service enabling
interactive exploration beyond the pre-built trace corpus. It is justified
by a property unique to seLe4n: the kernel model is a **pure, total,
I/O-free** function, so executing it is deterministic and side-effect-free
— closer to evaluating a spreadsheet than running an OS.

### 15.1 Capabilities

- **Custom initial topology.** A user configures an initial `SystemState`
  via a builder UI (N threads, priorities, endpoints, sched-contexts,
  CSpace shape) — mirroring the harness's parameterized topologies
  (minimal/medium/large) — and runs it.
- **What-if forks.** From any step, invoke an arbitrary syscall with chosen
  arguments and see the resulting state + which invariants still hold (the
  model returns explicit success/error, so every fork is well-defined).
- **Scenario authoring.** Compose a sequence of transitions and export it
  as a reproducible scenario (and, optionally, as a candidate test fixture
  for the kernel repo).

### 15.2 Shape

```
POST /api/run        { initialTopology | baseTrace+forkStep, steps[] }
                  ─►  { events.json, state.json }   (same schemas as §14)
GET  /api/traces     ─► catalog of prebuilt traces (mirrors manifest)
POST /api/step       { stateRef, syscall, args }  ─► { delta, outcome,
                                                       invariantResults }
```

The service is a thin wrapper that invokes a focused Lean executable
(`lake exe sele4n` variants / a small `run-scenario` exe) and returns the
E1/E2 JSON. **No new schemas** — live mode produces exactly what the static
pipeline produces, so the entire frontend is mode-agnostic.

### 15.3 Safety & determinism

- The model performs **no I/O, no allocation of host resources, no
  syscalls of its own** — it is a state→state function — so the runner is
  sandboxed by construction. Standard guards still apply: CPU/time/memory
  limits per request, input-size caps, and rate limiting.
- **Determinism is contractual:** identical inputs yield identical outputs
  (the same property the fixture SHA gates rely on), so responses are
  cacheable and reproducible, and a shared what-if link re-runs to the
  identical result.
- The runner executes the **same** verified transitions as the static
  traces; live mode cannot show behavior the kernel would not produce.

### 15.4 Boundary

Live mode runs the **executable model**. It does **not** run Lean
elaboration or proof checking in the request path (that is a build-time
property, already established by CI). It does not touch hardware. These
boundaries are stated in-product so users never mistake a what-if run for
a hardware result or a re-proof.

---

## 16. Implementation roadmap & phasing

Each phase is independently shippable and demoable. Data-pipeline work
(exporters) leads its consumers.

| Phase | Theme | Deliverables | Depends on |
|-------|-------|--------------|------------|
| **P0** | Data foundation | E1 structured trace exporter + golden fixture; `build_observatory_data.py`; manifest + chunking; CI sync gate (G7). App shell, lens rail, transport, command palette, deep-linking. | existing artifacts |
| **P1** | Execution MVP | Trace Theater + Scenario Catalog + Mission Control. Plays the smoke trace from E1; events linked to scenarios/source. | P0 |
| **P2** | State | E2 state exporter + golden fixture; State Inspector; the Proof Pivot's Execution/State tabs. | P1 |
| **P3** | Structure & proof | Architecture Atlas; Proof Graph Explorer; E3 proof index; the Proof tab; axiom-audit. Mission Control's "0 sorry/axiom" seal goes live. | P1 |
| **P4** | Subsystem lenses | Scheduler, IPC, Capability, VSpace, SchedContext lenses over E2 data; E4 scenario↔proof linkage completes the Pivot. | P2, P3 |
| **P5** | Assurance flagships | Information-Flow Lens (non-interference demo); SMP Multi-Core Theater (SGI, lock ladder, deadlock-freedom). | P2, P3 |
| **P6** | Platform & polish | Boot/Hardware + ABI lenses; guided tours; i18n; a11y hardening; performance pass; visual-regression suite. | P4, P5 |
| **P7** | Live mode (optional) | What-if backend (§15); topology builder; scenario authoring/export. | P4 |

**Critical path to a compelling first demo:** P0 → P1 → P2 yields a
playable, inspectable kernel trace (the core "watch it run + open the
state" story). P3 adds the proof cosmos and the "0 axiom" seal. P5 delivers
the two flagship "wow" views. A public launch is sensible after P6.

### 16.1 Suggested first vertical slice (proof of concept)

Build the **`IMT-014` call/reply slice end-to-end** (Appendix G): E1+E2 for
the IPC segment of the smoke trace, the Trace Theater, the State Inspector,
the IPC Switchboard, and the Proof Pivot to `ipcInvariantFull`. This single
slice exercises all three layers and the spine, validating the entire
architecture before breadth work begins.

---

## 17. Testing, validation & sync

- **Golden-data tests.** E1/E2/E3 each have committed golden fixtures with
  SHA gates, exactly like the kernel's `main_trace_smoke.expected.sha256`.
  E1's output is additionally diffed against the existing human fixture
  (it must be a structured superset), so the two can never diverge.
- **Schema validation.** Every artifact is validated against the §14
  schemas in CI; TypeScript loader types are generated from the schemas so
  a contract change breaks the build, not production.
- **Anti-drift gate (G7).** `observatory_data_sync` regenerates the bundle
  from `HEAD` and fails on any difference from the committed checksum — the
  Observatory cannot lag the kernel.
- **Determinism assertion.** The bundle build is run twice in CI; identical
  input must yield an identical bundle hash.
- **Frontend tests.** Unit tests for the spine traversals (the Proof Pivot
  joins) and delta-folding; component tests for the shared widgets;
  visual-regression snapshots for each lens at representative steps;
  end-to-end tests for the deep-link round-trip and the first vertical
  slice.
- **Performance assertions.** The §13 budgets are measured against
  representative bundles in CI; regressions fail.
- **Accessibility tests.** Automated a11y checks (axe) plus keyboard-path
  and screen-reader-tree tests for the graph views.
- **Honesty checks.** A test asserts that every model boundary listed in
  `proof_index.json.boundaries` is surfaced by the honest-boundary
  affordance, so the UI cannot quietly over-claim.

---

## 18. Risks, open questions & decisions to confirm

| # | Risk / question | Disposition |
|---|-----------------|-------------|
| R1 | **E2 serialization scope.** Full `SystemState` is large; naive dumps bloat the bundle. | Mitigated by deltas + keyframes + per-trace scoping; start with the objects a trace actually touches, expand opt-in. |
| R2 | **Proof-graph scale** (11.5k/79.6k). | Precomputed layouts + scoping + WebGL + node caps (§13). Never "draw all." |
| R3 | **Exporter maintenance burden** on the kernel team. | Exporters mirror existing harness calls and live in the testing layer; the sync gate makes drift loud but the diffs are mechanical. |
| R4 | **Over-claiming** (UI implies more is proved than is). | Honest-boundary affordance (§9.6) + honesty CI check (§17), driven by `proof_index.json.boundaries`. |
| R5 | **Static `#print axioms` capture** must be trustworthy. | E3 runs it in CI against the real bundle proofs; `axiomStatus` is computed, never hand-authored. |
| R6 | **Live mode safety** (v3). | Pure/total/I/O-free model + standard resource sandboxing (§15.3); ship only after P6. |
| Q1 | Hosting: GitHub Pages (static) vs an app host (for v3 backend)? | Default static on Pages for v1–v2; revisit for v3. |
| Q2 | Should E1/E2/E3 land in the kernel repo or a sibling repo? | Recommend exporters + schemas in the kernel repo (keeps the sync gate close to source); the frontend in a sibling repo or a `web/` subtree. |
| Q3 | Telemetry/analytics? | Off by default; if added, privacy-preserving and disclosed — consistent with the project's tone. |

---

## Appendix A — Subsystem palette & trace-tag map

Colors are illustrative hex anchors; the implementation finalizes a
color-blind-safe set (each paired with the icon + label so color is never
the sole channel). Trace tags are the `[TAG-*]` prefixes the harness emits.

| Subsystem | Icon | Accent | Trace tags |
|-----------|------|--------|-----------|
| Entry/bootstrap | ⏻ | slate | `ENT` |
| Scheduler | ⏱ | teal | `DDT`, `STD`, `ICS`, `IDLE`, `BME` |
| IPC | ✉ | azure | `IMT`, `IMB`, `CIC`, `RRC`, `MEI`, `ELC`, `LEP`, `Z7D` |
| Capability | 🔑 | gold | `ENT`, `KSD`, `MOV`, `SGT` |
| Lifecycle | ♺ | violet | `LEP`, `ELC`, `UMT` |
| SchedContext | ▦ | amber | `SCO`, `Z7D`, `Z8J` |
| Architecture/VSpace | 🗺 | green | `CAT`, `RCF` |
| Service / Registry | ⬣ | indigo | `SST`, `SRG` |
| ABI / Syscall decode | ⚙ | steel | `RDT`, `KSD`, `PIP`, `XVAL` |
| InformationFlow | 🔒 | crimson | (NI scenarios), `SGT` |
| SMP / Concurrency | ▥ | magenta | `smp-4core`, SGI events |
| Inter-transition / proof | ❋ | white | `ITR`, `PTY` |

## Appendix B — Syscall reference (29 operations)

| id | syscall | subsystem | right | effect (one line) |
|----|---------|-----------|-------|-------------------|
| 0 | `send` | IPC | write | enqueue/transfer message; wake receiver |
| 1 | `receive` | IPC | read | consume pending or block on receiveQ |
| 2 | `call` | IPC | write | send + donate SC + block on reply |
| 3 | `reply` | IPC | write | wake blocked caller; return donation |
| 16 | `replyRecv` | IPC | read | reply previous + receive next (atomic) |
| 14 | `notificationSignal` | IPC | write | OR badge; wake bound/queued waiter |
| 15 | `notificationWait` | IPC | read | consume badge or block |
| 26 | `tcbBindNotification` | IPC | write | bind notification (via cap) to TCB |
| 27 | `tcbUnbindNotification` | IPC | write | unbind notification from TCB |
| 4 | `cspaceMint` | Capability | grant | derive cap with attenuated rights; CDT edge |
| 5 | `cspaceCopy` | Capability | grant | copy cap (full rights) |
| 6 | `cspaceMove` | Capability | grant | move cap atomically |
| 7 | `cspaceDelete` | Capability | write | delete + revoke CDT subtree (BFS) |
| 28 | `mintReplyCap` | Capability | grant | derive reply cap to a Reply object |
| 8 | `lifecycleRetype` | Lifecycle | retype | erase + create typed object; scrub |
| 20 | `tcbSuspend` | Lifecycle | write | thread → inactive; cleanup IPC |
| 21 | `tcbResume` | Lifecycle | write | thread → runnable |
| 9 | `vspaceMap` | Architecture | write | install PTE; W^X & bounds checked |
| 10 | `vspaceUnmap` | Architecture | write | remove PTE; TLB flush |
| 11 | `serviceRegister` | Service | write | register endpoint as service |
| 12 | `serviceRevoke` | Service | write | remove service registration |
| 13 | `serviceQuery` | Service | read | look up service by cap |
| 17 | `schedContextConfigure` | SchedContext | write | set budget/period/prio/domain; validate |
| 18 | `schedContextBind` | SchedContext | write | bind thread; propagate prio; re-bucket |
| 19 | `schedContextUnbind` | SchedContext | write | unbind; clear replenish; reschedule |
| 22 | `tcbSetPriority` | Scheduler | write | set prio (MCP-bounded); re-bucket |
| 23 | `tcbSetMCPriority` | Scheduler | write | set MCP ceiling |
| 24 | `tcbSetIPCBuffer` | Lifecycle | write | set IPC buffer VA (alignment checked) |
| 25 | `tcbSetAffinity` | SMP | write | set CPU affinity; may migrate |

## Appendix C — Object field reference (State Inspector model)

Field names mirror the kernel structures exactly so E2 needs no
translation. (Source: `SeLe4n/Model/Object/Structures.lean`,
`Model/State.lean`, `Prelude.lean`.)

- **TCB** — `tid, priority, domain, cspaceRoot, vspaceRoot, ipcBuffer,
  ipcState, threadState, timeSlice, deadline, queuePrev, queueNext,
  pendingMessage, registerContext, faultHandler, boundNotification,
  schedContextBinding, timeoutBudget, maxControlledPriority, pipBoost,
  timedOut, cpuAffinity, replyObject, pendingReceiveReply`.
- **Endpoint** — `sendQ{head,tail}, receiveQ{head,tail}`.
- **Notification** — `state(idle|waiting|active), waitingThreads,
  pendingBadge, boundTCB`.
- **CNode** — `depth, guardWidth, guardValue, radixWidth, slots(Slot→
  Capability)`.
- **Capability** — `target(object oid | cnodeSlot | replyCap), rights
  (AccessRightSet bits: read,write,grant,grantReply,retype), badge`.
- **VSpaceRoot** — `asid, mappings(VAddr → (PAddr × PagePermissions))`.
- **PagePermissions** — `read, write, execute, user, cacheable` (W^X:
  `!(write && execute)`).
- **UntypedObject** — `regionBase, regionSize, watermark, children
  (objId,offset,size), isDevice, parent`.
- **SchedContext** — `budget, period, remaining, deadline, domain,
  boundThread`.
- **Reply** — `replyId, caller, donatedSc, prev` (MCS reply stack).
- **SchedulerState (per core)** — `current, runQueue, activeDomain,
  domainTimeRemaining, domainScheduleIndex, replenishQueue`; shared:
  `domainSchedule, configDefaultTimeSlice`.
- **Thread IPC states** — `ready, blockedOnSend(ep), blockedOnReceive(ep),
  blockedOnNotification(ntfn), blockedOnReply(ep, target?),
  blockedOnCall(ep)`.
- **Thread lifecycle states** — `Running, Ready, BlockedSend, BlockedRecv,
  BlockedCall, BlockedReply, BlockedNotif, Inactive`.

## Appendix D — Invariant catalog (what each guarantees, plainly)

Surfaced as invariant chips and in the Proof tab. (Source:
`CrossSubsystem.lean`, `IPC/Invariant/Defs.lean`, `Scheduler/Invariant/`,
`InformationFlow/`, `Concurrency/Locks/`.)

- **`proofLayerInvariantBundle`** — the top-level obligation: composes 11
  subsystem invariants; holds from boot through every operation.
- **`crossSubsystemInvariant`** (12 conjuncts) — coherence across subsystem
  boundaries: live endpoint/notification queue references, service-graph
  acyclicity, sched-context binding/run-queue consistency,
  lifecycle/type lockstep, disjoint untyped regions, PIP blocking
  acyclicity.
- **`ipcInvariantFull`** — dual-queue well-formedness, bidirectional TCB
  link integrity, queue acyclicity, bounded pending messages, badge
  well-formedness, reply↔caller linkage, blocked-thread/endpoint
  consistency.
- **Per-core scheduler invariants** (16+ forms ×core) — current ∉ own run
  queue, no duplicates, EDF earliest-deadline, positive time-slice/budget,
  register bank matches current, replenishment ordering; each bridges to
  the boot-core single-core predicate.
- **`cbs_bandwidth_bounded`** — CBS provides bounded bandwidth isolation.
- **`donationChainAcyclic`** — passive-server SC donation chains never
  cycle.
- **`blockingChainAcyclic`** — PIP blocking graph is acyclic (⟹ no
  deadlock from priority inheritance); chain depth bounded.
- **WCRT bound** — `WCRT = D × L_max + N × (B + P)`, proven across the
  liveness modules.
- **Non-interference** (`composedNonInterference_step`,
  `step_preserves_projection`, `lowEquivalent`/`_smp`) — a step preserves
  each observer's projection; high actions don't change the low view.
- **Lock hierarchy & deadlock-freedom** (`LockId` total order L0..L9,
  `lt_irrefl`/`lt_trans` ⟹ no wait-for cycle under 2PL), **serializability**
  (conflict-graph acyclic under 2PL), **TicketLock/RwLock refinement**.
- **`untypedRegionsDisjoint`**, **`cdtNodeWellFormed`**,
  **VSpace invariants** (no-virtual-overlap, W^X compliance).

## Appendix E — Trace-tag glossary

`ENT` entry/bootstrap · `CAT` capability+architecture (timer/memory/vspace/
W^X/TLB/registers) · `SST`/`SRG` service + registry · `LEP` lifecycle+
endpoint · `CIC` capability-IPC completion · `IMT` IPC message transfer ·
`IMB` IPC message bounds · `DDT` dequeue-on-dispatch · `ICS` inline context
switch · `BME` bounded message extended · `STD` scheduler/timing/domain ·
`UMT` untyped memory · `SGT` syscall gate · `RCF` runtime-contract fixtures ·
`RDT` register decode · `KSD` kernel syscall decode · `PIP` pipeline
integration · `MOV` cspace move · `RRC` replyRecv roundtrip · `ELC` endpoint
lifecycle · `MEI` multi-endpoint interleaving · `SCO` sched-context ops ·
`Z7D` donation (passive server) · `Z8J` budget lifecycle · `IDLE` per-core
idle dispatch · `ITR` inter-transition invariant checks · `PTY`
parameterized topology · `XVAL` Lean⇄Rust cross-validation · `smp-4core`
SMP scheduler · `RH` Robin Hood table · `TPH` two-phase architecture.

## Appendix F — Glossary

- **Capability** — unforgeable token of authority naming an object + rights.
- **CSpace / CNode** — a thread's capability address space; a radix tree of
  CNodes resolved by guard/radix walk.
- **CDT** — Capability Derivation Tree; tracks derivation lineage for
  revocation.
- **Endpoint / Notification** — synchronous (rendezvous) and asynchronous
  (badge) IPC objects.
- **Reply object** — first-class object backing call/reply (seL4-MCS).
- **SchedContext** — CPU time as a capability: budget + period + deadline;
  threads bind to it; donated to passive servers.
- **EDF / PIP / CBS** — Earliest-Deadline-First selection; Priority
  Inheritance Protocol; Constant-Bandwidth-Server budgeting.
- **Domain** — a scheduling partition; the schedule rotates domains.
- **SGI** — Software-Generated Interrupt; how cores poke each other
  (reschedule, TLB shootdown, cache broadcast, halt).
- **Lock hierarchy / 2PL** — the L0..L9 `LockId` order + two-phase locking
  that yield deadlock-freedom.
- **Non-interference** — high-clearance actions don't affect the
  low-clearance observable projection.
- **Invariant / preservation theorem** — a property that holds in every
  reachable state / the proof that one transition keeps it true.
- **`sorry` / `axiom`** — Lean escape hatches for unproved claims; seLe4n
  has **zero** in its production proof surface (the headline claim).
- **The Proof Pivot** — the Observatory's signature jump from a runtime
  event to the theorem that proves it safe, and back.

## Appendix G — Worked vertical slice (`IMT-014`, end to end)

The recommended first build (§16.1). A user opens the smoke trace and
scrubs to step 78, `[IMT-014] call/reply response registers: [100, 200]`.

1. **Trace Theater** highlights event 78; caption "call/reply response
   registers: [100, 200]"; the invariant strip shows `ipcInvariantFull ✓`
   and the 38th `crossSubsystemInvariant ✓` check.
2. **IPC Switchboard** (open-in-lens) animates the reply: the server sends
   `[100,200]` along endpoint `ep20`'s wire to caller `T1`; `T1` un-docks
   from `blockedOnReply`; the reply object `r1`'s `caller` link is consumed;
   the donated `SchedContext sc40` migrates back from server to `T1`.
3. **State Inspector** (same step) shows `T1`: `ipcState
   blockedOnReply→ready`, `schedContextBinding donated→own`, `replyObject
   r1→null`, `registerContext.x0=100, x1=200` — each marked ◆changed; the
   diff vs step 77 lists objects `1` and `50` written.
4. **Context Rail → Proof tab** shows `ipcInvariantFull`; expanding it
   reveals the `replyCallerLinkage` and `blockedOnReplyHasTarget` conjuncts;
   clicking the transition `endpointReplyCrossCoreDispatch` opens its
   `…_preserves_ipcInvariantFull` theorem in the **Proof Explorer**.
5. **Proof Explorer** renders that theorem's dependency cone down to
   axiom-free Lean-core leaves (hollow green); the axiom audit confirms the
   only foundations used are `propext`, `Classical.choice`, `Quot.sound` —
   no `axiom`, no `sorry`.
6. **Reverse pivot:** from the theorem, "watch this hold" lists every
   scenario exercising it (e.g. `RRC-003`, `IMT-021`), each a one-click
   jump back into the Trace Theater.

This single slice traverses Execution → State → Proof and back across five
lenses and the spine — the whole product thesis in one interaction.

---

*End of specification. This document is a design artifact for a companion
application; it does not modify the seLe4n kernel or its proofs. Metrics
quoted are read live from `docs/codebase_map.json` by the application and
are accurate as of the kernel revision named in the bundle manifest.*
