# Schnellstart-Anleitung

Diese Anleitung führt Sie durch die Einrichtung und erste Schritte mit seLe4n —
einem produktionsorientierten Mikrokernel, geschrieben in Lean 4 mit
maschinengeprüften Beweisen (Machine-Checked Proofs).

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | **Deutsch** | [हिन्दी](../hi/QUICKSTART.md)

---

## Voraussetzungen

- **Betriebssystem:** Linux (empfohlen), macOS oder WSL2 unter Windows
- **Git:** Version 2.0 oder höher
- **Bash:** Bash-kompatible Shell
- **Internetverbindung:** Für den Download der Lean-Toolchain und Abhängigkeiten
- **Festplattenspeicher:** Mindestens 2 GB freier Speicherplatz

> **Hinweis:** Die Lean-Toolchain (einschließlich elan und Lake) wird automatisch
> durch das Setup-Skript installiert. Eine vorherige Installation von Lean ist
> nicht erforderlich.

## Schritt 1: Repository klonen

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## Schritt 2: Lean-Toolchain installieren

Das Setup-Skript installiert den Lean-Toolchain-Manager (elan) und die
projektspezifische Lean-Version (v4.28.0):

```bash
./scripts/setup_lean_env.sh
```

Dieses Skript führt folgende Schritte durch:
- Installation von elan (Lean-Versionsverwaltung)
- Download und Einrichtung von Lean v4.28.0
- Installation des Lake-Build-Systems (Version 0.18.6)
- Installation optionaler Testabhängigkeiten (shellcheck, ripgrep)

Wenn Sie die Testabhängigkeiten überspringen möchten:

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

## Schritt 3: Projekt kompilieren

```bash
source ~/.elan/env && lake build
```

Der Build kompiliert alle 98 Produktionsmodule und überprüft dabei automatisch
alle 1.686 Theorem-/Lemma-Deklarationen durch den Lean-Typprüfer. Bei
erfolgreichem Build sind alle Beweise maschinell verifiziert — null `sorry`,
null `axiom`.

> **Erwartete Build-Dauer:** Der erste Build kann 5–15 Minuten dauern, da alle
> Abhängigkeiten kompiliert werden müssen. Nachfolgende Builds (Incremental
> Builds) sind deutlich schneller.

## Schritt 4: Trace-Harness ausführen

```bash
lake exe sele4n
```

Dieser Befehl führt den ausführbaren Trace-Harness aus, der eine vollständige
Kernel-Trace-Sequenz durchläuft. Die Ausgabe zeigt die Ausführung verschiedener
Kernel-Operationen einschließlich:

- Scheduler-Operationen (Scheduling, Yield, Timer-Tick)
- Capability-Operationen (Lookup, Mint, Copy, Move, Delete)
- IPC-Operationen (Send, Receive, Call, ReplyRecv, Notification)
- Lifecycle-Operationen (Retype)
- Service-Orchestrierung
- Informationsfluss-Durchsetzung

## Schritt 5: Tests ausführen

### Schnelltest (empfohlen als erster Schritt)

```bash
./scripts/test_fast.sh
```

Führt Tier 0 (Hygienechecks) und Tier 1 (Build-Validierung) aus.

### Smoke-Test (Mindestanforderung vor einem PR)

```bash
./scripts/test_smoke.sh
```

Umfasst zusätzlich Tier 2: Trace-Validierung, Negative-State-Tests und
Dokumentationssynchronisation.

### Vollständiger Test (bei Theorem-/Invariantenänderungen)

```bash
./scripts/test_full.sh
```

Umfasst zusätzlich Tier 3: Invariantenoberflächenanker und Lean `#check`-Korrektheit.

### Nächtlicher Test

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

Umfasst Tier 4: Determinismusprüfungen.

## Projektstruktur verstehen

### Quelltextstruktur (Source Layout)

Die Quelltextdateien befinden sich im Verzeichnis `SeLe4n/`:

| Verzeichnis | Beschreibung |
|-------------|-------------|
| `SeLe4n/Prelude.lean` | Typisierte Bezeichner (Typed Identifiers), KernelM-Monade |
| `SeLe4n/Machine.lean` | Registerdatei, Speicher, Timer, MachineConfig |
| `SeLe4n/Model/` | Kernobjekte (Objects), Zustand (State), CDT |
| `SeLe4n/Kernel/Scheduler/` | Prioritätsgestaffelte RunQueue, EDF-Scheduling |
| `SeLe4n/Kernel/Capability/` | CSpace-Lookup/Mint/Copy/Move/Delete/Revoke |
| `SeLe4n/Kernel/IPC/` | Dual-Queue-IPC-Subsystem |
| `SeLe4n/Kernel/Lifecycle/` | Objekt-Retype mit Lifecycle-Metadaten |
| `SeLe4n/Kernel/Service/` | Service-Orchestrierung mit Abhängigkeitsgraph |
| `SeLe4n/Kernel/InformationFlow/` | N-Domänen-Sicherheitslabels, Nichtinterferenz (Non-Interference) |
| `SeLe4n/Kernel/RobinHood/` | Verifizierte Robin-Hood-Hashtabelle |
| `SeLe4n/Kernel/RadixTree/` | Verifizierter CNode-Radix-Baum |
| `SeLe4n/Kernel/Architecture/` | VSpace, Registerdecodierung, Architekturannahmen |
| `SeLe4n/Kernel/API.lean` | Öffentliche Kernel-Schnittstelle |
| `SeLe4n/Platform/` | Plattformverträge (Sim + RPi5) |
| `SeLe4n/Testing/` | Test-Harness und Hilfsmittel |

### Operations/Invariant-Aufteilung

Jedes Kernel-Subsystem folgt einer strikten Trennung:
- **`Operations.lean`** — Ausführbare Zustandsübergänge (Transitions)
- **`Invariant.lean`** — Maschinengeprüfte Erhaltungsbeweise (Preservation Proofs)

Diese Trennung stellt sicher, dass Implementierung und formale Verifikation
klar voneinander abgegrenzt sind.

## Editor-Einrichtung

### VS Code (empfohlen)

1. Installieren Sie die [Lean 4-Erweiterung](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
2. Öffnen Sie das Projektverzeichnis in VS Code
3. Die Erweiterung erkennt automatisch die Lean-Toolchain aus `lean-toolchain`

Funktionen der Erweiterung:
- Syntaxhervorhebung und Fehlermarkierung
- Interaktive Beweiszustände (Tactic State) im InfoView
- Typinformationen beim Überfahren mit der Maus (Hover)
- Go-to-Definition und Referenzsuche

### Neovim

Für Neovim-Benutzer gibt es das Plugin
[lean.nvim](https://github.com/Julian/lean.nvim), das ähnliche Funktionen
bietet.

## Pre-Commit-Hook einrichten

Installieren Sie den Pre-Commit-Hook, um fehlerhafte Commits zu vermeiden:

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

Der Hook:
1. Erkennt gestufte `.lean`-Dateien (Staged Files)
2. Kompiliert jedes geänderte Modul über `lake build <Modul.Pfad>`
3. Prüft auf `sorry` im gestuften Inhalt
4. **Blockiert den Commit** bei Build-Fehlern oder vorhandenen `sorry`-Einträgen

## Nächste Schritte

Nachdem Sie die Umgebung eingerichtet und die Tests erfolgreich ausgeführt haben:

1. **Architektur verstehen** — Lesen Sie die [README](README.md) für einen
   Überblick über die Architektur und den Vergleich mit seL4
2. **Entwicklungsworkflow lernen** — Studieren Sie
   [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) für den täglichen
   Arbeitsablauf und die PR-Checkliste
3. **Handbuch erkunden** — Das vollständige Handbuch unter
   [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) enthält
   Architektur-Vertiefungen, Beweisstrategien und den Hardware-Pfad
4. **Beitragen** — Lesen Sie die [Beitragsrichtlinien](CONTRIBUTING.md) und
   suchen Sie sich ein passendes Issue aus

## Häufige Probleme und Lösungen

### `elan` wird nicht gefunden

```bash
source ~/.elan/env
```

Fügen Sie diese Zeile zu Ihrem `~/.bashrc` oder `~/.zshrc` hinzu, damit elan
bei jeder neuen Shell-Sitzung verfügbar ist.

### Build schlägt mit Abhängigkeitsfehlern fehl

```bash
lake update
lake build
```

### Typprüferfehler bei Beweisen

Stellen Sie sicher, dass Sie die korrekte Lean-Version verwenden:

```bash
elan show
```

Die Ausgabe sollte `leanprover/lean4:v4.28.0` anzeigen. Falls nicht:

```bash
elan override set leanprover/lean4:v4.28.0
```

### Einzelnes Modul kompilieren

Wenn Sie nur ein bestimmtes Modul überprüfen möchten:

```bash
source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations
```

---

> Dieses Dokument ist eine Übersetzung und Erweiterung der Schnellstart-Abschnitte
> aus der [englischen README](../../../README.md).
> Bei Abweichungen ist die englische Fassung maßgeblich.
