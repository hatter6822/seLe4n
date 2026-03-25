<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n Logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sicherheit" /></a>
  <img src="https://img.shields.io/badge/version-0.21.4-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Lizenz" /></a>
</p>

<p align="center">
  Ein Mikrokernel geschrieben in Lean 4 mit maschinengeprüften Beweisen (Machine-Checked Proofs),
  inspiriert von der <a href="https://sel4.systems">seL4</a>-Architektur. Erstes Hardware-Ziel:
  <strong>Raspberry Pi 5</strong>.
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | **Deutsch** | [हिन्दी](../hi/README.md)

---

## Was ist seLe4n?

seLe4n ist ein Mikrokernel, der von Grund auf in Lean 4 entwickelt wurde. Jeder
Kernel-Übergang (Transition) ist eine ausführbare reine Funktion (Pure Function).
Jede Invariante wird maschinell durch den Lean-Typprüfer verifiziert — null
`sorry`, null `axiom`. Die gesamte Beweisoberfläche (Proof Surface) kompiliert
zu nativem Code ohne zugelassene Beweise.

Das Projekt verwendet ein fähigkeitsbasiertes Sicherheitsmodell (Capability-Based
Security) und führt neuartige architektonische Verbesserungen gegenüber anderen
Mikrokerneln ein:

- **O(1)-hashbasierte Kernel-Hotpaths** — alle Object Stores, Run Queues, CNode Slots, VSpace-Mappings und IPC-Queues verwenden formal verifizierte `RHTable`/`RHSet` (Robin-Hood-Hashtabellen mit maschinengeprüften Invarianten, kein `Std.HashMap`/`Std.HashSet` im Zustand)
- **Service-Orchestrierungsschicht** für Komponentenlebenszyklusverwaltung und Abhängigkeitsmanagement mit deterministischer Teilfehler-Semantik (Partial-Failure Semantics)
- **Knotenstabiler Capability-Ableitungsbaum** mit `childMap` + `parentMap` RHTable-Indizes für O(1) Slot-Transfer, Widerruf (Revocation), Elternsuche und Nachfahrendurchlauf
- **Intrusive Dual-Queue-IPC** mit `queuePrev`/`queuePPrev`/`queueNext`-Verkettung pro Thread für O(1) Einreihung, Entnahme und Entfernung aus der Warteschlangenmitte
- **Parametrisiertes N-Domänen-Informationsfluss-Framework** mit konfigurierbaren Flussrichtlinien (Flow Policies), das herkömmliche Vertraulichkeits-/Integritätslabels verallgemeinert (über seL4s binäre Partitionierung hinaus)
- **EDF- + Prioritätsscheduling** mit Dequeue-on-Dispatch-Semantik, pro-TCB-Registerkontext mit Inline-Kontextwechsel, prioritätsgestaffelter `RunQueue`, domänenbasierter Partitionierung

## Aktueller Stand

| Eigenschaft | Wert |
|-------------|------|
| **Version** | `0.21.4` |
| **Lean-Toolchain** | `v4.28.0` |
| **Produktions-LoC (Lean)** | 64.039 über 101 Dateien |
| **Test-LoC (Lean)** | 8.318 über 10 Testsuiten |
| **Bewiesene Deklarationen** | 1.901 Theorem-/Lemma-Deklarationen (null sorry/axiom) |
| **Zielhardware** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Letztes Audit** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — Vollständiges Kernel- + Rust-Codebase-Pre-Release-Audit |
| **Codebase-Karte** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — maschinenlesbare Deklarationsinventur |

Die Metriken werden durch `./scripts/generate_codebase_map.py` aus der Codebasis
abgeleitet und unter dem `readme_sync`-Schlüssel in
[`docs/codebase_map.json`](../../../docs/codebase_map.json) gespeichert.

## Schnellstart

```bash
./scripts/setup_lean_env.sh   # Lean-Toolchain installieren
lake build                     # Alle Module kompilieren
lake exe sele4n                # Trace-Harness ausführen
./scripts/test_smoke.sh        # Validierung (Hygiene + Build + Trace + Negative-State + Docs-Sync)
```

Ausführliche Anleitung finden Sie in der [Schnellstart-Anleitung](QUICKSTART.md).

## Einstiegspfad

Neu im Projekt? Folgen Sie dieser Lesereihenfolge:

1. **Diese README** — Projektidentität, Architektur und Quelltextstruktur
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — Täglicher Arbeitsablauf, Validierungsschleife, PR-Checkliste
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — Vollständiges Handbuch (Architektur-Vertiefungen, Beweise, Hardware-Pfad)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — Maschinenlesbare Modul- und Deklarationsinventur

Für die Workstream-Planung und -Geschichte siehe [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

## Projektdokumentation

| Dokument | Zweck |
|----------|-------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Projektspezifikation und Meilensteine |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | seL4-Referenzsemantik |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Täglicher Arbeitsablauf, Validierungsschleife, PR-Checkliste |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | Gestufte Test-Gates und CI-Vertrag |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Vollständige Workstream-Geschichte, Roadmap und Audit-Plan-Index |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Vollständiges Handbuch (Architektur, Design, Beweise, Hardware-Pfad) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Maschinenlesbare Codebase-Inventur (synchronisiert mit README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | Beitragsmechanismen und PR-Anforderungen |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | Versionshistorie |

## Validierungsbefehle

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (Hygiene + Build, semantische Beweistiefe L-08)
./scripts/test_smoke.sh     # + Tier 2 (Trace + Negative-State + Dokumentationssynchronisation)
./scripts/test_full.sh      # + Tier 3 (Invariantenoberflächenanker + Lean #check-Korrektheit)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (nächtlicher Determinismus)
```

Führen Sie mindestens `test_smoke.sh` vor jedem PR aus. Führen Sie `test_full.sh`
aus, wenn Sie Theoreme, Invarianten oder Dokumentationsanker ändern.

## Architektur

seLe4n ist als geschichtete Verträge (Layered Contracts) organisiert, jeweils mit
ausführbaren Übergängen und maschinengeprüften Invariantenerhaltungsbeweisen:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│       Informationsfluss  (Policy, Projection, Enforcement)           │
├──────────────────────────────────────────────────────────────────────┤
│       Architektur  (VSpace, VSpaceBackend, Adapter, Assumptions)     │
├──────────────────────────────────────────────────────────────────────┤
│                     Modell  (Object, State, CDT)                     │
├──────────────────────────────────────────────────────────────────────┤
│           Grundlagen  (Prelude, Machine, MachineConfig)              │
├──────────────────────────────────────────────────────────────────────┤
│          Plattform  (Contract, Sim, RPi5)  ← H3-prep Bindings       │
└──────────────────────────────────────────────────────────────────────┘
```

Jedes Kernel-Subsystem folgt der **Operations/Invariant-Aufteilung**: Übergänge
in `Operations.lean`, Beweise in `Invariant.lean`. Das vereinheitlichte
`apiInvariantBundle` aggregiert alle Subsystem-Invarianten in eine einzige
Beweisverpflichtung (Proof Obligation).

## Vergleich mit seL4

| Merkmal | seL4 | seLe4n |
|---------|------|--------|
| **IPC-Mechanismus** | Einfach verkettete Endpoint-Queue | Intrusive Dual-Queue mit `queuePPrev`-Rückwärtszeigern für O(1)-Entfernung aus der Warteschlangenmitte |
| **Informationsfluss** | Binäre High/Low-Partitionierung | N-Domänen-konfigurierbare Flussrichtlinie (verallgemeinert herkömmliche Vertraulichkeits- x Integritätslabels) |
| **Dienstverwaltung** | Nicht im Kernel | Erstklassige Service-Orchestrierung mit Abhängigkeitsgraph und DFS-Zykluserkennung |
| **Capability-Ableitung** | CDT mit verketteter Kindliste | `childMap`-HashMap für O(1)-Kindersuche |
| **Scheduler** | Flache Prioritätswarteschlange | Prioritätsgestaffelte `RunQueue` mit Inline-`maxPriority`-Tracking und EDF |
| **VSpace** | Hardware-Seitentabellen | `HashMap VAddr (PAddr x PagePermissions)` mit W^X-Durchsetzung |
| **Beweismethodik** | Isabelle/HOL, nachträglich (Post-hoc) | Lean 4-Typprüfer, Beweise direkt bei Übergängen platziert |
| **Plattformabstraktion** | HAL auf C-Ebene | `PlatformBinding`-Typklasse mit typisierten Schnittstellenverträgen (Boundary Contracts) |

## Nächste Schritte

Die aktuellen Prioritäten und die vollständige Workstream-Geschichte werden in
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) gepflegt. Zusammenfassung:

- **WS-R** — Umfassende Audit-Behebung (Comprehensive Audit Remediation, 8 Phasen, R1–R8, 111 Teilaufgaben). Behandelt alle 82 Befunde aus dem [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). R1–R7 abgeschlossen (v0.18.0–v0.18.6), R8 ausstehend.
- **Raspberry Pi 5 Hardware-Anbindung** — ARMv8 Page-Table-Walk, GIC-400 Interrupt-Routing, Boot-Sequenz (RPi5-Plattformverträge nun substantiell durch WS-H15)

Alle vorherigen Portfolios (WS-B bis WS-Q) sind abgeschlossen. Frühere Audits
(v0.8.0–v0.9.32), Meilensteinabschlüsse und ältere GitBook-Kapitel sind in
[`docs/dev_history/`](../../../docs/dev_history/README.md) archiviert.

---

> Dieses Dokument ist eine Übersetzung der [englischen README](../../../README.md).
> Bei Abweichungen ist die englische Fassung maßgeblich.
