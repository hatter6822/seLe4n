<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n Logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sicherheit" /></a>
  <img src="https://img.shields.io/badge/version-0.37.56-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Lizenz" /></a>
</p>

<p align="center">
  Ein Mikrokernel geschrieben in Lean 4 mit maschinengeprüften Beweisen,
  inspiriert von der <a href="https://sel4.systems">seL4</a>-Architektur. Erstes Hardware-Ziel:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Mit Bedacht erstellt mit Hilfe von:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>DIESEN KERNEL ENTSPRECHEND BEHANDELN</strong>
  </div>
</p>

<p align="center">
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  **Deutsch** ·
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## Was ist seLe4n?

seLe4n ist ein Mikrokernel, der von Grund auf in Lean 4 gebaut ist. Jeder
Kernel-Übergang ist eine ausführbare reine Funktion, und jede Invariante wird
vom Lean-Kernel geprüft: Die produktive Beweisoberfläche enthält null `sorry`
und null `axiom`. Derselbe Lean-Code wird zu nativem Code kompiliert und
zusammen mit einer kleinen Hardwareschicht in Rust zum Kernel-Image gelinkt,
das auf dem Zielsystem bootet.

Das Projekt behält das capability-basierte Sicherheitsmodell von seL4 und
zunehmend auch dessen für Nutzer sichtbare ABI bei, beweist mit Lean mehr
darüber und härtet es dort, wo seL4 eine Lücke lässt. Die vollständige
Spezifikation ist [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md); die
folgenden Punkte verweisen darauf.

### Die ABI von seL4

- **Die Systemaufrufe von seL4-MCS** — die elf MCS-Aufrufe (`Call` … `Yield`),
  in `x7` so nummeriert wie in seL4; die Operation wird aus dem Aufruf, dem Typ
  der aufgerufenen Capability und dem Nachrichtenlabel gewählt
  (`Syscall.selectOperation`), wie in seL4
- **Die Fehler- und Fault-Nutzlasten von seL4** — `LookupFault`, der
  Fehlerrahmen in der Message-Register-Reihenfolge von seL4,
  Capability-Faults auf der Empfangsseite, der Zustand `Restart`,
  Capability-Argumente als zusätzliche Capabilities und der Guard in der
  Capability mit einem einzigen `resolveAddressBits`
- Der Rest der seL4-ABI-Arbeit (die verbleibenden Invocations,
  Timeout-Faults, Rechte pro Invocation, der Running-Zustand pro Kern) ist der
  aktive Workstream WS-SX; seine Zeilen stehen in
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Scheduling und Echtzeit

- **Scheduling-Kontexte als Capabilities** — CPU-Zeit ist ein Kernel-Objekt.
  Ein `SchedContext` hält Budget, Periode und Refills von seL4-MCS, wird über
  die `SchedControl`-Autorität des Kerns konfiguriert und über Capabilities an
  Threads gebunden; seine Invarianten (`budgetWithinBounds`,
  `refillsConserved`) gehören zum obersten Bündel. Die Bandbreitenisolation
  ist `refill_window_bound`: Ein Kontext läuft in keinem Fenster einer Periode
  länger als sein Budget, die Sliding-Window-Garantie von seL4-MCS. Ein
  hierarchischer Constant-Bandwidth-Scheduler mit EDF-Wurzel, der die
  Umkehrung ergänzt (ein zugelassener Server erhält sein Budget in jedem
  Fenster), ist der geplante Workstream WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Passive Server** — ein Server läuft auf dem Scheduling-Kontext, den sein
  Client während der IPC spendet; `donationChainAcyclic` schließt zirkuläre
  Spenden aus
- **Budgetgesteuerte IPC-Timeouts** — ein blockierter Thread mit erschöpftem
  Budget wird aus der Warteschlange seines Endpoints entfernt (`timeoutThread`)
- **Prioritätsvererbung** — transitive Weitergabe mit maschinell geprüfter
  Freiheit von Blockierungszyklen (`blockingAcyclic`) und einem Theorem zur
  beschränkten Inversion (`pip_bounded_inversion`)
- **Beschränkte Latenz** — eine parametrische Schranke für die
  Worst-Case-Antwortzeit, `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, mit einer Form pro Kern), bewiesen über
  die Module in `SeLe4n/Kernel/Scheduler/Liveness/`

### Kernel-Objekte und Speicher

- **Objekte aus Untyped-Speicher geschnitten** — Retype schneidet ein Objekt
  aus der Region einer Untyped-Capability, und das Zurücksetzen eines Untyped
  ist das von seL4. Die Zellen jedes geschnittenen Objekts in den eigenen
  Speicher seines Untyped zu verlegen, ist der aktive Workstream WS-UC
- **Ein Kernel-Eintritt alloziert nichts** — die kompilierten Systemaufruf-,
  Fault- und Interrupt-Einträge machen keine Heap-Allokation; das Schneiden
  eines Retype alloziert nur die Zellen des neuen Objekts. Das QEMU-Heap-Gate
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) misst jeden Eintrag
  auf dem gebooteten Image und schlägt bei jeder anderen Zahl fehl
- **Datenstrukturen** — Objektspeicher und VSpace-Mappings sind verifizierte
  Robin-Hood-Hashtabellen (`RHTable`, mit `distCorrect`, `noDupKeys` und
  `probeChainDominant`); ein CNode ist ein flaches Array aus `2^radix` Slots,
  wie in seL4; Run-Queues, Endpoint- und Notification-Warteschlangen und
  Reply-Wartende sind über die TCBs verkettet, jeweils mit einer abstrakten
  Geister-Warteschlange, deren Übereinstimmung mit den Verweisen bewiesen ist
- **Über die Slots verketteter Capability-Ableitungsbaum** — jeder Slot hält
  seine Verweise auf Eltern, erstes Kind und Geschwister (die Mapping-Datenbank
  von seL4), bewiesen übereinstimmend mit dem Baum; Löschen, Widerruf (die
  `cteRevoke`-Schleife von seL4) und Slot-Transfer laufen über die Verweise
- **VSpace** — ARMv8-Seitentabellen mit W^X pro Frame und
  Speichertyp-Prüfungen, die einen ungecachten Alias von RAM ablehnen

### Sicherheit und Verifikation

- **Informationsfluss mit N Domänen** — parametrisierte Flussrichtlinien, die
  die Zwei-Domänen-Partition von seL4 verallgemeinern; eine
  Durchsetzungsgrenze, deren Länge `enforcementBoundaryExtended_count` festlegt
  (und `enforcementBoundaryPerCore_count` für die Grenze pro Kern); ein
  Nichtinterferenz-Theorem für jeden Konstruktor von `NonInterferenceStep`;
  und ein beschränkter, fail-closed Audit-Pfad für Deklassifizierungen, gelesen
  über eine `auditTrail`-Capability
- **Zusammengesetzte Beweisschicht** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) verbindet das
  Invariantenbündel jedes Subsystems (Scheduler, Capabilities, IPC und seine
  Kopplung an den Scheduler, Lebenszyklus, Service-Registry, VSpace,
  subsystemübergreifend, TLB- und Instruktionscache-Kohärenz, TLB-Shootdown,
  Deklassifizierungs-Auditlog und die Übereinstimmung jeder verketteten
  Struktur mit ihrem Geist) zu einer einzigen Verpflichtung, die vom Boot an
  durch jede Operation getragen wird
- **Mehrkern** — vier Kerne mit Scheduling pro Kern, kernübergreifender IPC und
  Aufwecken sowie TLB-Shootdown; der SMP-Abschluss-Workstream (WS-SM) läuft
- **Dreiphasiger Zustand** — eine Builder-Phase mit Invariantenzeugen friert
  in eine unveränderliche Darstellung mit bewiesener Lookup-Äquivalenz ein; die
  eingefrorenen Operationen decken die Systemaufrufe ab, die
  `frozenOpCoverage` aufführt, festgelegt durch `frozenOpCoverage_count`
- **Service-Registry** — eine Erweiterung von seLe4n, nicht in seL4: Dienste
  werden über eine `serviceRegistry`-Capability registriert und gesucht und am
  bedienenden Endpoint vermerkt; die Abhängigkeitsrichtlinie bleibt, wie in
  seL4, einem Service-Manager im Userspace überlassen

## Aktueller Stand

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Attribut | Wert |
|----------|------|
| **Version** | `0.37.56` |
| **Lean-Toolchain** | `v4.28.0` |
| **Produktions-LoC (Lean)** | 685.922 über 701 Dateien |
| **Test-LoC (Lean)** | 91.877 über 71 Testsuiten |
| **Bewiesene Deklarationen** | 26.488 Theorem-/Lemma-Deklarationen (null sorry/axiom) |
| **Rust-Crates** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (Userspace-Wrapper), `sele4n-hal` (die Hardwareschicht des Kernels) und der Host-Test `sele4n-lean-boundary` |
| **Zielhardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Boot-Lanes** | Jede QEMU-Lane bootet zuerst das Raspberry-Pi-5-Image auf der Maschine `raspi5b` von [rpi5_machine](https://github.com/hatter6822/rpi5_machine), dann das `virt`-Image auf QEMUs `virt` |
| **Workstreams** | Stand jedes offenen Workstreams: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); Index und Schuldenregister: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Audits** | [`docs/audits/`](../../../docs/audits/README.md) — die Artefakte des aktiven Audits; frühere Audits sind archiviert |
| **Codebase-Karte** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — maschinenlesbares Deklarationsinventar |

Die Metriken werden von `./scripts/generate_codebase_map.py` aus dem Code
abgeleitet und in [`docs/codebase_map.json`](../../../docs/codebase_map.json) unter dem
Schlüssel `readme_sync` gespeichert. Aktualisieren Sie die gesamte
Dokumentation gemeinsam mit `./scripts/sync_documentation_metrics.sh` (nur
prüfen: `--check`).

## Schnellstart

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` baut nur, was `Main.lean` und die Test-Executables erreichen; bauen
Sie vor dem Commit einer `.lean`-Datei ihr Modul namentlich
(`lake build <Module.Path>`). Der vollständige Ablauf steht in
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), die Regeln für alle Mitwirkenden
in [`CLAUDE.md`](../../../CLAUDE.md).

## Dokumentation

| Hier beginnen | Danach |
|---------------|--------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — Ablauf, Validierung, PR-Checkliste | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — Spezifikation und Meilensteine |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — vollständiges Handbuch | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — Referenzsemantik von seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — maschinenlesbares Inventar | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — jeder aufgeschobene Punkt, mit Verantwortlichem |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — Ablauf von Beiträgen | [`CHANGELOG.md`](../../../CHANGELOG.md) — Versionsgeschichte |

## Validierungsbefehle

```bash
./scripts/test_fast.sh      # Tier 0+1: hygiene + build
./scripts/test_smoke.sh     # + Tier 2: trace + negative-state
./scripts/test_full.sh      # + Tier 3: invariant surface anchors + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: nightly determinism

./scripts/test_rust.sh                 # host Rust: build, tests, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # the kernel HAL's real target

./scripts/test_qemu.sh                 # boot the image on raspi5b, then on virt
./scripts/test_qemu.sh --lean-kernel   # the Lean-linked images, on four cores
```

Führen Sie vor jedem PR mindestens `test_smoke.sh` aus und `test_full.sh`, wenn
Sie Theoreme, Invarianten oder Tier-3-Anker ändern. Ein Tier stoppt bei seiner
ersten fehlschlagenden Prüfung; mit `--continue` sammeln Sie alle Fehler in
einem Durchlauf.

Nach jeder Änderung unter `rust/` führen Sie **beide** Rust-Lanes aus. Sie
decken disjunkte Hälften derselben Crate ab: Auf dem Host wird jeder
`#[cfg(target_arch = "aarch64")]`-Block entfernt, bevor rustc oder clippy ihn
sehen, sodass die Host-Lane die bedingten Blöcke, `asm!`-Stellen und
`.S`-Quellen nicht sieht, die den Großteil der HAL ausmachen. Die Cross-Lane
baut `sele4n-hal` für `aarch64-unknown-none-softfloat` in beiden Profilen,
prüft, dass die Assembler-Quellen wirklich assembliert wurden, lintet das
Cross-Ziel und disassembliert die Release-Objekte, um zu beweisen, dass sie
kein FP/SIMD-Register verwenden. Die QEMU-Lanes bauen rpi5_machine beim ersten
Einsatz an dem in `scripts/setup_rpi5_machine.sh` festgelegten Commit; eine
Lane, der eine Voraussetzung fehlt, meldet NOT RUN statt eines Erfolgs. Die
vollständige Liste steht in [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Architektur

seLe4n ist als geschichtete Verträge organisiert, jeder mit ausführbaren
Übergängen und maschinell geprüften Beweisen der Invariantenerhaltung:

```
┌──────────────────────────────────────────────────────────────────────┐
│   Kernel entries  (syscall, fault, interrupt, per-core timer tick)   │
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Scheduler   │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│   RunQueue   │  CSpace/CDT │  DualQueue │  Untyped  │    Registry    │
│ SchedContext │             │  Donation  │  Retype   │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│  Architecture  (VSpace, page tables, TLB/cache, decode, trap frame)  │
├──────────────────────────────────────────────────────────────────────┤
│         Concurrency  (locks, memory model, per-core state)           │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│    Platform  (Contract, Boot, Sim, RPi5, QemuVirt)  ← bindings       │
├──────────────────────────────────────────────────────────────────────┤
│        Rust HAL  (rust/sele4n-hal: boot, traps, GIC, MMU, SMP)       │
└──────────────────────────────────────────────────────────────────────┘
```

## Quellcode-Struktur

```
SeLe4n/
├── Prelude.lean                 Typed identifiers, KernelM monad
├── Machine.lean                 Register file, memory, timer
├── Model/                       Object types, SystemState, slot links, builder/freeze phases
├── Kernel/
│   ├── API.lean                 Unified public API + apiInvariantBundle
│   ├── *Entry.lean              Compiled syscall, fault, interrupt and per-core timer entries
│   ├── Scheduler/               Run queues, selection, priority inheritance, liveness (WCRT)
│   ├── SchedContext/            Scheduling contexts, seL4-MCS refills, SchedControl
│   ├── Capability/              CSpace operations, derivation tree, authority proofs
│   ├── IPC/                     Dual-queue endpoints, donation, timeouts, cross-core IPC
│   ├── Lifecycle/               Untyped retype and reset, thread suspend/resume
│   ├── Service/                 Service registry and its invariants
│   ├── Architecture/            VSpace (W^X), page tables, TLB/cache models, decode, trap frame
│   ├── InformationFlow/         N-domain policy, projection, enforcement, NI proofs
│   ├── Concurrency/             Lock model, memory model, per-core runtime
│   ├── RobinHood/               Verified Robin Hood hash table (RHTable/RHSet)
│   ├── RadixTree/               CNode radix view and its bridge to the slot array
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass and boundary contracts
│   ├── Boot.lean, Boot/         Boot sequence: root server, initial threads, IRQ nodes
│   ├── FFI.lean                 The Lean side of the HAL boundary
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   ├── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO, boot VSpace)
│   └── QemuVirt/                QEMU `virt` binding and boot entry
├── Testing/                     Test harness, state builder, invariant checks, censuses
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
rust/                            sele4n-types, sele4n-abi, sele4n-sys, sele4n-hal, sele4n-lean-boundary
```

Jedes Subsystem folgt der **Operations/Invariant-Trennung**: Übergänge in
`Operations.lean`, Beweise in `Invariant.lean`. Das vereinheitlichte
`apiInvariantBundle` fasst alle Subsystem-Invarianten zu einer einzigen
Beweisverpflichtung zusammen. Die Subsystemkarte ist
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5; das vollständige Inventar pro
Datei steht in [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Vergleich mit seL4

| Merkmal | seL4 | seLe4n |
|---------|------|--------|
| **Systemaufruf-ABI** | MCS-Aufrufe, Invocation-Labels, Fehler- und Fault-Nutzlasten | Dieselbe: die elf Aufrufe von seL4-MCS mit ihrer Nummerierung, per Label gewählte Invocations und die Fehlernutzlasten von seL4; die verbleibenden Invocations sind Zeilen von WS-SX |
| **Scheduling** | MCS-Scheduling-Kontexte mit Sporadic-Server-Refills | Dieselbe Refill-Engine, mit bewiesener Erhaltungsinvariante und der Schranke von einem Budget pro Fenster (`refill_window_bound`); ein hierarchischer CBS mit EDF-Wurzel ist geplant (WS-CB) |
| **Passive Server** | SchedContext-Spende | Verifizierte Spende mit der Invariante `donationChainAcyclic` |
| **IPC** | Eine Warteschlange pro Endpoint, über die TCBs verkettet | Eine Sende- und eine Empfangswarteschlange pro Endpoint, beide über die TCBs verkettet, mit Entfernen in O(1) an jeder Position; budgetgesteuerte Timeouts |
| **Informationsfluss** | Binäre High/Low-Partition | Konfigurierbare Richtlinie mit N Domänen, eine durch `enforcementBoundaryExtended_count` festgelegte Durchsetzungsgrenze, ein Nichtinterferenz-Theorem pro Schritt und ein capability-gesteuerter Audit-Pfad für jede genehmigte Deklassifizierung |
| **Prioritätsvererbung** | Nicht im Kernel | Maschinell geprüfte transitive PIP ohne Blockierungszyklen, mit einem Theorem zur beschränkten Inversion |
| **Beschränkte Latenz** | Keine formale WCRT-Schranke | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, bewiesen über die Liveness-Module |
| **Objektspeicher** | Objekte an physischen Adressen | Verifizierte Robin-Hood-Hashtabellen (`RHTable`/`RHSet`); CNodes sind flache Slot-Arrays wie in seL4 |
| **Speicher-Mapping** | W^X vom Kernel nicht erzwungen | W^X pro Frame als Invariante erzwungen; Speichertyp-Prüfungen lehnen einen ungecachten Alias von RAM ab |
| **Dienstverwaltung** | Nicht im Kernel | Capability-gesteuerte Service-Registry am Endpoint; Abhängigkeitsrichtlinie im Userspace |
| **Beweise** | Isabelle/HOL, über den C-Code per Verfeinerung | Lean 4, neben den ausführbaren Übergängen; null sorry/axiom (Anzahl in der Tabelle oben) |
| **Plattform** | HAL auf C-Ebene | Typklasse `PlatformBinding` mit typisierten Grenzverträgen und einer HAL in Rust |

## Lizenz und Drittanbieter-Attributionen

seLe4n selbst steht unter der GNU General Public License v3.0 oder später
(GPLv3+); den vollständigen Text enthält [`LICENSE`](../../../LICENSE).
Build-Abhängigkeiten von Drittanbietern (`cc`, `find-msvc-tools`, `shlex`, alle
doppelt lizenziert unter `MIT OR Apache-2.0`) werden unter der MIT-Option
verwendet; ihre ursprünglichen Copyright- und Erlaubnisvermerke sind wörtlich in
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md) wiedergegeben. Das
Kernel-Binary enthält keinen zur Laufzeit gelinkten Drittanbietercode — der HAL
ist `#![no_std]` und verwendet nur `core::*`.

---

> Dieses Dokument ist eine Übersetzung der [englischen README](../../../README.md).
> Bei Abweichungen ist die englische Fassung maßgeblich.
