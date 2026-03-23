# Zum Projekt seLe4n beitragen

Vielen Dank für Ihr Interesse an seLe4n — einem produktionsorientierten Mikrokernel,
geschrieben in Lean 4 mit maschinengeprüften Beweisen (Machine-Checked Proofs).

---

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | [العربية](../ar/CONTRIBUTING.md) | [Français](../fr/CONTRIBUTING.md) | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | **Deutsch** | [हिन्दी](../hi/CONTRIBUTING.md)

---

## Lizenz

seLe4n steht unter der [GNU General Public License v3.0 oder später](../../../LICENSE).
Mit der Einreichung eines Pull Requests oder der Bereitstellung von Code erklären
Sie sich damit einverstanden, dass Ihre Beiträge unter derselben GPL-3.0-or-later-Lizenz
veröffentlicht werden. Sie bestätigen außerdem, dass Sie berechtigt sind, den
Beitrag unter dieser Lizenz einzureichen.

## Schnelleinstieg für Beitragende (5 Minuten)

1. **Arbeitsablauf + Standards:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **Teststufen (Testing Tiers):** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI-Richtlinie:** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **Projektumfang + Workstreams:** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **Aktive Audit-Befunde:** [`docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md)
6. **Workstream-Geschichte:** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

Vollständiges Handbuch: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## Entwicklungsumgebung einrichten

### Voraussetzungen

- Git
- Bash-kompatible Shell
- Internetverbindung (für den Download der Lean-Toolchain)

### Installation

```bash
# Repository klonen
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n

# Lean-Toolchain installieren (elan + Lean 4.28.0)
./scripts/setup_lean_env.sh

# Projekt kompilieren
source ~/.elan/env && lake build

# Trace-Harness ausführen
lake exe sele4n
```

### Editor-Einrichtung

Für die beste Entwicklungserfahrung empfehlen wir VS Code mit der
[Lean 4-Erweiterung](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
Diese bietet Syntaxhervorhebung, Typinformation, interaktive Beweiszustände und
automatische Fehlererkennung.

## Pflichtvalidierung vor dem Öffnen eines Pull Requests

```bash
./scripts/test_smoke.sh     # Mindestanforderung (Tier 0–2)
./scripts/test_full.sh      # Erforderlich bei Theorem-/Invariantenänderungen (Tier 0–3)
```

### Modulspezifische Kompilierung

Bevor Sie eine `.lean`-Datei committen, **müssen** Sie überprüfen, dass das
betreffende Modul kompiliert:

```bash
source ~/.elan/env && lake build <Modul.Pfad>
```

Beispiel: Wenn Sie `SeLe4n/Kernel/RobinHood/Bridge.lean` geändert haben:

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

> **Hinweis:** `lake build` (Standardziel) ist **nicht ausreichend**. Das Standardziel
> kompiliert nur Module, die über `Main.lean` erreichbar sind. Module, die noch
> nicht vom Hauptkernel importiert werden, bestehen `lake build` auch mit
> fehlerhaften Beweisen.

### Pre-Commit-Hook installieren

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

Der Hook erkennt gestufte `.lean`-Dateien, kompiliert jedes geänderte Modul,
prüft auf `sorry` im gestuften Inhalt und **blockiert den Commit** bei Fehlern.

## PR-Anforderungen

- **Workstream-ID angeben** — Identifizieren Sie die Workstream-ID(s), die durch Ihren Beitrag vorangebracht werden
- **Kohärenter Umfang** — Beschränken Sie den PR auf eine zusammenhängende Änderung
- **Deterministische Übergänge** — Transitionen müssen deterministisch sein (expliziter Erfolg/Fehler)
- **Beweise gepaart mit Implementierung** — Invarianten-/Theoremaktualisierungen müssen mit Implementierungsänderungen einhergehen
- **Dokumentation synchronisieren** — Aktualisieren Sie relevante Dokumentation im selben PR
- **Kein `sorry`/`axiom`** — Verboten in der Produktionsbeweisoberfläche
- **Typisierte Bezeichner verwenden** — `ThreadId`, `ObjId`, `CPtr`, `Slot` usw. sind Wrapper-Strukturen, keine `Nat`-Aliase

Vollständige Checkliste in [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Validierungsstufen (Tiers)

| Stufe | Befehl | Prüfumfang |
|-------|--------|-----------|
| Tier 0+1 | `./scripts/test_fast.sh` | Hygiene + Build |
| Tier 0–2 | `./scripts/test_smoke.sh` | + Trace + Negative-State + Dokumentationssync |
| Tier 0–3 | `./scripts/test_full.sh` | + Invariantenoberflächenanker + Lean #check |
| Tier 0–4 | `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | + Nächtlicher Determinismus |

## Konventionen im Quelltext

### Operations/Invariant-Aufteilung

Jedes Kernel-Subsystem trennt Übergänge (Transitions) von Beweisen (Proofs):
- `Operations.lean` — Ausführbare Zustandsübergänge
- `Invariant.lean` — Maschinengeprüfte Erhaltungsbeweise (Preservation Proofs)

### Namensgebung

Theorem-, Funktions- und Definitionsnamen sollten die Semantik beschreiben
(Zustandsänderungsform, erhaltene Invariante, Übergangspfad). Kodieren Sie
**keine** Workstream-IDs (`WS-*`, `wsH*` usw.) in Bezeichnernamen.

### Deterministische Semantik

Alle Übergänge geben expliziten Erfolg oder Fehler zurück. Führen Sie niemals
nichtdeterministische Verzweigungen ein.

## Dokumentationsregeln

Bei Verhaltens-, Theorem- oder Workstream-Statusänderungen aktualisieren Sie
im selben PR:

1. `README.md` — Metriksynchronisation aus `docs/codebase_map.json`
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. Betroffene GitBook-Kapitel
5. `docs/CLAIM_EVIDENCE_INDEX.md` bei Anspruchsänderungen
6. `docs/WORKSTREAM_HISTORY.md` bei Workstream-Statusänderungen
7. `docs/codebase_map.json` bei Lean-Quelltextänderungen neu generieren

## Website-Linkschutz

Die Projektwebsite ([sele4n.org](https://github.com/hatter6822/hatter6822.github.io))
verlinkt auf Quelldateien, Dokumentation, Skripte und Verzeichnisse in diesem
Repository. Geschützte Pfade sind in `scripts/website_link_manifest.txt` aufgeführt.
Benennen Sie geschützte Pfade nicht um und löschen Sie sie nicht, ohne vorher die
Website zu aktualisieren.

## Schwachstellenmeldung

Wenn Sie während der Arbeit an diesem Projekt eine mögliche Sicherheitslücke
entdecken, die eine CVE-Bezeichnung (Common Vulnerabilities and Exposures) rechtfertigen
könnte, melden Sie diese bitte umgehend. Dies gilt für Schwachstellen in:

- **Projektcode** — Logikfehler in Übergangssemantik, Capability-Prüfungen oder Informationsfluss-Durchsetzung
- **Abhängigkeiten und Toolchain** — Bekannte oder vermutete Schwachstellen in Lean, Lake, elan oder importierten Bibliotheken
- **Build- und CI-Infrastruktur** — Unsichere Skriptmuster (z.B. Command Injection, unsichere Dateiberechtigungen)

## Hilfe erhalten

- Erstellen Sie ein [Issue](https://github.com/hatter6822/seLe4n/issues) für Fragen oder Fehlerberichte
- Lesen Sie das vollständige Handbuch unter [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)
- Konsultieren Sie die [Workstream-Geschichte](../../../docs/WORKSTREAM_HISTORY.md) für den aktuellen Projektstatus

---

> Dieses Dokument ist eine Übersetzung der [englischen CONTRIBUTING.md](../../../CONTRIBUTING.md).
> Bei Abweichungen ist die englische Fassung maßgeblich.
