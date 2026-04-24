<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n Logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sicherheit" /></a>
  <img src="https://img.shields.io/badge/version-0.30.8-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## Was ist seLe4n?

seLe4n ist ein Mikrokernel, der von Grund auf in Lean 4 entwickelt wurde. Jeder
Kernel-Übergang ist eine ausführbare reine Funktion. Jede Invariante wird
maschinell durch den Lean-Typprüfer verifiziert — null `sorry`, null `axiom`.
Die gesamte Beweisoberfläche kompiliert zu nativem Code ohne zugelassene Beweise.

Das Projekt bewahrt das fähigkeitsbasierte Sicherheitsmodell von seL4 und
führt zugleich architektonische Verbesserungen ein, die durch das
Lean-4-Beweissystem ermöglicht werden:

### Scheduling und Echtzeitgarantien

- **Komponierbare Leistungsobjekte** — CPU-Zeit ist ein erstklassiges Kernel-Objekt. `SchedContext` kapselt Budget, Periode, Priorität, Deadline und Domäne in einen wiederverwendbaren Scheduling-Kontext, an den sich Threads über Capabilities binden. CBS-Scheduling (Constant Bandwidth Server) bietet bewiesene Bandbreitenisolation (Theorem `cbs_bandwidth_bounded`)
- **Passive Server** — untätige Server leihen sich den `SchedContext` des Clients während IPC, verbrauchen null CPU-Zeit wenn sie nicht aktiv bedienen. Die Invariante `donationChainAcyclic` verhindert zirkuläre Spendenketten
- **Budgetgesteuerte IPC-Timeouts** — blockierende Operationen sind durch das Budget des Aufrufers begrenzt. Bei Ablauf werden Threads aus der Endpoint-Queue herausgelöst und erneut eingereiht
- **Priority-Inheritance-Protokoll** — transitive Prioritätspropagation mit maschinengeprüfter Deadlock-Freiheit (`blockingChainAcyclic`) und beschränkter Kettentiefe. Verhindert unbegrenzte Prioritätsinversion
- **Theorem für beschränkte Latenz** — maschinengeprüfte WCRT-Schranke: `WCRT = D × L_max + N × (B + P)`, bewiesen über 7 Liveness-Module zu Budgetmonotonie, Replenishment-Timing, Yield-Semantik, Banderschöpfung und Domänenrotation

### Datenstrukturen und IPC

- **O(1)-hashbasierte Hotpaths** — alle Object Stores, Run Queues, CNode Slots, VSpace-Mappings und IPC-Queues verwenden formal verifizierte Robin-Hood-Hashtabellen mit `distCorrect`-, `noDupKeys`- und `probeChainDominant`-Invarianten
- **Intrusive Dual-Queue-IPC** — Rückzeiger pro Thread für O(1)-Einreihung, -Entnahme und -Entfernung aus der Warteschlangenmitte
- **Knotenstabiler Capability-Ableitungsbaum** — `childMap` + `parentMap`-Indizes für O(1)-Slot-Transfer, Widerruf und Nachfahrendurchlauf

### Sicherheit und Verifikation

- **N-Domänen-Informationsfluss** — parametrisierte Flussrichtlinien, die seL4s binäre Partitionierung verallgemeinern. 30-Einträge-Durchsetzungsgrenze mit Nichteinmischungsbeweisen pro Operation (32-Konstruktor-Induktive `NonInterferenceStep`)
- **Komponierte Beweisschicht** — `proofLayerInvariantBundle` komponiert 10 Subsystem-Invarianten (Scheduler, Capability, IPC, Lifecycle, Service, VSpace, Cross-Subsystem, TLB und CBS-Erweiterungen) zu einer einzigen übergeordneten Beweisverpflichtung, verifiziert vom Boot durch alle Operationen
- **Zweiphasen-Zustandsarchitektur** — Builder-Phase mit Invariantenzeugen fließt in eine eingefrorene unveränderliche Darstellung mit bewiesener Lookup-Äquivalenz. 20 eingefrorene Operationen spiegeln die Live-API wider
- **Vollständiger Operationssatz** — alle seL4-Operationen implementiert mit Invariantenerhaltung, einschließlich der 5 zurückgestellten Operationen (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Service-Orchestrierung** — Kernel-seitige Komponentenlebenszyklusverwaltung mit Abhängigkeitsgraphen und bewiesener Azyklizität (seLe4n-Erweiterung, nicht in seL4)

## Aktueller Stand

<!-- Metriken sind synchronisiert aus docs/codebase_map.json → readme_sync.
     Regenerieren mit: ./scripts/generate_codebase_map.py --pretty
     Primärquelle: docs/codebase_map.json (readme_sync) -->

| Eigenschaft | Wert |
|-------------|------|
| **Version** | `0.30.6` |
| **Lean-Toolchain** | `v4.28.0` |
| **Produktions-LoC (Lean)** | 103.179 über 142 Dateien |
| **Test-LoC (Lean)** | 14.890 über 24 Testsuiten |
| **Bewiesene Deklarationen** | 3.045 Theorem-/Lemma-Deklarationen (null sorry/axiom) |
| **Zielhardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Kanonisches Audit** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — umfassendes Pre-1.0-Audit (202 Befunde; behoben durch WS-AK AK1–AK10) |
| **Letztes Audit** | [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md) — Pre-1.0-Härtungsaudit (3 CRIT, 24 HIGH, 71 MED, 58 LOW, 40 INFO — anfängliche Bewertung gemäß §0.4) |
| **Codebase-Karte** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — maschinenlesbare Deklarationsinventur |

Die Metriken werden durch `./scripts/generate_codebase_map.py` aus der Codebasis
abgeleitet und unter dem `readme_sync`-Schlüssel in
[`docs/codebase_map.json`](../../../docs/codebase_map.json) gespeichert.
Alle Dokumentation gemeinsam aktualisieren mit
`./scripts/report_current_state.py` als Gegenprüfung.

## Schnellstart

```bash
./scripts/setup_lean_env.sh   # Lean-Toolchain installieren
lake build                     # alle Module kompilieren
lake exe sele4n                # Trace-Harness ausführen
./scripts/test_smoke.sh        # validieren (Hygiene + Build + Trace + Negative-State + Docs-Sync)
```

## Dokumentation

| Einstieg | Dann |
|----------|------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — Arbeitsablauf, Validierung, PR-Checkliste | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — Spezifikation und Meilensteine |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — vollständiges Handbuch | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4-Referenzsemantik |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — maschinenlesbare Inventur | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — Workstream-Geschichte und Roadmap |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — Beitragsmechanismen | [`CHANGELOG.md`](../../../CHANGELOG.md) — Versionshistorie |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) ist die Primärquelle
für Projektmetriken. Sie speist [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
und wird bei Merge automatisch via CI aktualisiert. Regenerieren mit
`./scripts/generate_codebase_map.py --pretty`.

## Validierungsbefehle

```bash
./scripts/test_fast.sh      # Tier 0+1: Hygiene + Build
./scripts/test_smoke.sh     # + Tier 2: Trace + Negative-State + Docs-Sync
./scripts/test_full.sh      # + Tier 3: Invariantenoberflächenanker + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: nächtlicher Determinismus
```

Führen Sie mindestens `test_smoke.sh` vor jedem PR aus. Führen Sie `test_full.sh`
aus, wenn Sie Theoreme, Invarianten oder Dokumentationsanker ändern.

## Architektur

seLe4n ist als geschichtete Verträge organisiert, jeweils mit ausführbaren
Übergängen und maschinengeprüften Invariantenerhaltungsbeweisen:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
│  SchedContext│             │  Donation  │           │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│          Platform  (Contract, Sim, RPi5)  ← H3-prep bindings         │
└──────────────────────────────────────────────────────────────────────┘
```

## Quelltextstruktur

```
SeLe4n/
├── Prelude.lean                 Typed identifiers, KernelM monad
├── Machine.lean                 Register file, memory, timer
├── Model/                       Object types, SystemState, builder/freeze phases
├── Kernel/
│   ├── API.lean                 Unified public API + apiInvariantBundle
│   ├── Scheduler/               RunQueue, EDF selection, PriorityInheritance, Liveness (WCRT)
│   ├── Capability/              CSpace ops + CDT tracking, authority/preservation proofs
│   ├── IPC/                     Dual-queue endpoints, donation, timeouts, structural invariants
│   ├── Lifecycle/               Object retype, thread suspend/resume
│   ├── Service/                 Service orchestration, registry, acyclicity proofs
│   ├── Architecture/            VSpace (W^X), TLB model, register/syscall decode
│   ├── InformationFlow/         N-domain policy, projection, enforcement, NI proofs
│   ├── RobinHood/               Verified Robin Hood hash table (RHTable/RHSet)
│   ├── RadixTree/               CNode radix tree (O(1) flat array)
│   ├── SchedContext/             CBS budget engine, replenishment queue, priority management
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass
│   ├── Boot.lean                Boot sequence (PlatformConfig → IntermediateState)
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO)
├── Testing/                     Test harness, state builder, invariant checks
Main.lean                        Executable entry point
tests/                           15 test suites
```

Jedes Subsystem folgt der **Operations/Invariant-Aufteilung**: Übergänge in
`Operations.lean`, Beweise in `Invariant.lean`. Das vereinheitlichte
`apiInvariantBundle` aggregiert alle Subsystem-Invarianten zu einer einzigen
Beweisverpflichtung. Für die vollständige Dateiinventur siehe
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Vergleich mit seL4

| Merkmal | seL4 | seLe4n |
|---------|------|--------|
| **Scheduling** | In C implementierter Sporadic Server (MCS) | CBS mit maschinengeprüftem Theorem `cbs_bandwidth_bounded`; `SchedContext` als Capability-gesteuertes Kernel-Objekt |
| **Passive Server** | SchedContext-Donation via C | Verifizierte Donation mit Invariante `donationChainAcyclic` |
| **IPC** | Einfach verkettete Endpoint-Queue | Intrusive Dual-Queue mit O(1)-Entfernung aus der Warteschlangenmitte; budgetgesteuerte Timeouts |
| **Informationsfluss** | Binäre High/Low-Partitionierung | N-Domänen-konfigurierbare Richtlinie mit 30-Einträge-Durchsetzungsgrenze und Nichteinmischungsbeweisen pro Operation |
| **Priority Inheritance** | In C implementiertes PIP (MCS-Branch) | Maschinengeprüftes transitives PIP mit Deadlock-Freiheit und parametrischer WCRT-Schranke |
| **Beschränkte Latenz** | Keine formale WCRT-Schranke | `WCRT = D × L_max + N × (B + P)` bewiesen über 7 Liveness-Module |
| **Object Stores** | Verkettete Listen und Arrays | Verifizierte Robin-Hood-Hashtabellen (`RHTable`/`RHSet`) mit O(1)-Hotpaths |
| **Dienstverwaltung** | Nicht im Kernel | Erstklassige Orchestrierung mit Abhängigkeitsgraph und Azyklizitätsbeweisen |
| **Beweise** | Isabelle/HOL, nachträglich | Lean-4-Typprüfer, direkt bei Übergängen platziert (2.447 Theoreme, null sorry/axiom) |
| **Plattform** | HAL auf C-Ebene | `PlatformBinding`-Typklasse mit typisierten Schnittstellenverträgen |

## Nächste Schritte

Alle Software-Workstreams (WS-B bis WS-AB) sind abgeschlossen. Die vollständige
Geschichte befindet sich in [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

### Abgeschlossene Workstreams

| Workstream | Umfang | Version |
|------------|--------|---------|
| **WS-AB** | Zurückgestellte Operationen & Liveness — suspend/resume, setPriority/setMCPriority, setIPCBuffer, Priority-Inheritance-Protokoll, Theorem für beschränkte Latenz (6 Phasen, 90 Aufgaben) | v0.24.0–v0.25.5 |
| **WS-Z** | Komponierbare Leistungsobjekte — `SchedContext` als 7. Kernel-Objekt, CBS-Budget-Engine, Replenishment-Queue, passive Server-Donation, Timeout-Endpoints (10 Phasen, 213 Aufgaben) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | Kern-Subsysteme, Robin-Hood-Hashtabellen, Radix Trees, Frozen State, Informationsfluss, Service-Orchestrierung, Plattformverträge | v0.9.0–v0.22.x |

Detaillierte Pläne: [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### Nächster großer Meilenstein

**Raspberry Pi 5 Hardware-Anbindung** — ARMv8 Page-Table-Walk, GIC-400
Interrupt-Routing, Boot-Sequenz. Frühere Audits und Meilensteinabschlüsse
sind in [`docs/dev_history/`](../../../docs/dev_history/README.md) archiviert.

---

> Dieses Dokument ist eine Übersetzung der [englischen README](../../../README.md).
> Bei Abweichungen ist die englische Fassung maßgeblich.
