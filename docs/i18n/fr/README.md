<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="Logo seLe4n" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sécurité" /></a>
  <img src="https://img.shields.io/badge/version-0.21.5-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Licence" /></a>
</p>

<p align="center">
  Un micro-noyau (microkernel) écrit en Lean 4 avec des preuves vérifiées par machine,
  inspiré de l'architecture <a href="https://sel4.systems">seL4</a>. Première cible matérielle :
  <strong>Raspberry Pi 5</strong>.
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | **Français** | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## Qu'est-ce que seLe4n ?

seLe4n est un micro-noyau (microkernel) conçu de zéro en Lean 4. Chaque
transition du noyau est une fonction pure exécutable. Chaque invariant est
vérifié par machine via le vérificateur de types de Lean — zéro `sorry`,
zéro `axiom`. L'ensemble de la surface de preuve se compile en code natif
sans aucune preuve admise.

Le projet utilise un modèle de sécurité basé sur les capacités (capabilities)
tout en introduisant des améliorations architecturales novatrices par rapport
aux autres micro-noyaux :

- **Chemins chauds du noyau en O(1) par hachage** — tous les magasins d'objets (object stores), files d'exécution (run queues), emplacements CNode, projections VSpace et files IPC utilisent des `RHTable`/`RHSet` (tables de hachage Robin Hood avec invariants vérifiés par machine, zéro `Std.HashMap`/`Std.HashSet` dans l'état)
- **Couche d'orchestration de services** pour la gestion du cycle de vie des composants et des dépendances avec une sémantique déterministe de défaillance partielle
- **Arbre de dérivation de capacités à nœuds stables** avec des index `childMap` + `parentMap` en RHTable pour le transfert d'emplacements (slots), la révocation, la recherche de parents et la traversée des descendants en O(1)
- **IPC à double file intrusive** (intrusive dual-queue IPC) avec liens `queuePrev`/`queuePPrev`/`queueNext` par thread pour la mise en file, le retrait et la suppression en milieu de file en O(1)
- **Cadre de flux d'information paramétré à N domaines** (N-domain information flow) avec politiques de flux configurables, généralisant les étiquettes héritées de confidentialité/intégrité (au-delà du partitionnement binaire de seL4)
- **Ordonnancement EDF + priorité** (EDF + priority scheduling) avec sémantique de retrait à la distribution (dequeue-on-dispatch), contexte de registres par TCB avec changement de contexte en ligne, `RunQueue` par tranche de priorité, partitionnement par domaine

## État actuel

<!-- Les métriques ci-dessous sont synchronisées depuis docs/codebase_map.json → section readme_sync.
     Regénérer avec : ./scripts/generate_codebase_map.py --pretty
     Source de vérité : docs/codebase_map.json (readme_sync) -->

| Attribut | Valeur |
|----------|--------|
| **Version** | `0.21.5` |
| **Chaîne d'outils Lean** | `v4.28.0` |
| **LoC Lean de production** | 64 039 réparties sur 101 fichiers |
| **LoC Lean de test** | 8 318 réparties sur 10 suites de tests |
| **Déclarations prouvées** | 1 901 déclarations theorem/lemma (zéro sorry/axiom) |
| **Matériel cible** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Dernier audit** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — Audit complet pré-publication du noyau et de la base Rust |
| **Carte de la base de code** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventaire lisible par machine des déclarations |

Les métriques sont extraites de la base de code par `./scripts/generate_codebase_map.py`
et stockées dans [`docs/codebase_map.json`](../../../docs/codebase_map.json) sous la
clé `readme_sync`. Mettez à jour l'ensemble de la documentation à l'aide de
`./scripts/report_current_state.py` comme vérification croisée.

## Démarrage rapide

```bash
./scripts/setup_lean_env.sh   # installer la chaîne d'outils Lean
lake build                     # compiler tous les modules
lake exe sele4n                # exécuter le harnais de trace
./scripts/test_smoke.sh        # valider (hygiène + compilation + trace + état négatif + synchronisation docs)
```

## Parcours d'intégration

Nouveau sur le projet ? Suivez cet ordre de lecture :

1. **Ce README** — identité du projet, architecture et organisation des sources
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flux de travail quotidien, boucle de validation, liste de contrôle des PR
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manuel complet (architecture approfondie, preuves, chemin matériel)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventaire lisible par machine des modules et déclarations

Pour la planification et l'historique des flux de travail (workstreams), consultez [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

## Documentation du projet

| Document | Objectif |
|----------|----------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Spécification du projet et jalons |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | Sémantique de référence seL4 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Flux de travail quotidien, boucle de validation, liste de contrôle des PR |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | Niveaux de tests et contrat CI |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Historique complet des workstreams, feuille de route et index des audits |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Manuel complet (architecture, conception, preuves, chemin matériel) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Inventaire lisible par machine de la base de code (synchronisé avec le README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | Modalités de contribution et exigences pour les PR |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | Historique des versions |

## Commandes de validation

```bash
./scripts/test_fast.sh      # Niveau 0 + Niveau 1 (hygiène + compilation, profondeur sémantique de preuve L-08)
./scripts/test_smoke.sh     # + Niveau 2 (trace + état négatif + synchronisation docs)
./scripts/test_full.sh      # + Niveau 3 (ancres de surface d'invariants + vérification Lean #check)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Niveau 4 (déterminisme nocturne)
```

Exécutez au minimum `test_smoke.sh` avant toute PR. Exécutez `test_full.sh`
lors de modifications des théorèmes, invariants ou ancres de documentation.

## Architecture

seLe4n est organisé en couches contractuelles, chacune dotée de transitions
exécutables et de preuves de préservation d'invariants vérifiées par machine :

```
┌──────────────────────────────────────────────────────────────────────┐
│                 API du noyau  (SeLe4n/Kernel/API.lean)               │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│ Ordonnanceur │  Capacités  │    IPC     │ Cycle de  │  Services      │
│  RunQueue    │  CSpace/CDT │  DualQueue │   vie     │  Orchestration │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│       Flux d'information  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Modèle  (Object, State, CDT)                     │
├──────────────────────────────────────────────────────────────────────┤
│             Fondations  (Prelude, Machine, MachineConfig)            │
├──────────────────────────────────────────────────────────────────────┤
│          Plateforme  (Contract, Sim, RPi5)  ← liaisons H3-prep       │
└──────────────────────────────────────────────────────────────────────┘
```

Chaque sous-système du noyau suit la séparation **Operations/Invariant** :
les transitions dans `Operations.lean`, les preuves dans `Invariant.lean`.
Le `apiInvariantBundle` unifié agrège tous les invariants des sous-systèmes
en une seule obligation de preuve.

## Comparaison avec seL4

| Fonctionnalité | seL4 | seLe4n |
|----------------|------|--------|
| **Mécanisme IPC** | File d'attente à liste chaînée simple | Double file intrusive avec pointeurs arrière `queuePPrev` pour suppression en milieu de file en O(1) |
| **Flux d'information** | Partition binaire haut/bas | Politique de flux configurable à N domaines (généralise les étiquettes héritées confidentialité × intégrité) |
| **Gestion des services** | Hors noyau | Orchestration de services de première classe avec graphe de dépendances et détection de cycles par DFS |
| **Dérivation de capacités** | CDT avec liste chaînée d'enfants | `childMap` HashMap pour recherche d'enfants en O(1) |
| **Ordonnanceur** | File de priorité plate | `RunQueue` par tranche de priorité avec suivi inline de `maxPriority` et EDF |
| **VSpace** | Tables de pages matérielles | `HashMap VAddr (PAddr x PagePermissions)` avec application W^X |
| **Méthodologie de preuve** | Isabelle/HOL, a posteriori | Vérificateur de types Lean 4, preuves co-localisées avec les transitions |
| **Abstraction de plateforme** | HAL au niveau C | Classe de types `PlatformBinding` avec contrats de frontière typés |

## Prochaines étapes

Les priorités actuelles et l'historique complet des flux de travail sont maintenus dans
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md). En résumé :

- **WS-R** — Remédiation d'audit complète (8 phases, R1–R8, 111 sous-tâches). Traite les 82 constats de l'[`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). R1–R7 terminées (v0.18.0–v0.18.6), R8 en attente. Plan : [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **Liaison matérielle Raspberry Pi 5** — parcours de tables de pages ARMv8, routage d'interruptions GIC-400, séquence de démarrage (les contrats de plateforme RPi5 sont désormais substantifs via WS-H15)

Les portefeuilles précédents (WS-B à WS-Q) sont tous terminés. Les audits antérieurs (v0.8.0–v0.9.32),
les clôtures de jalons et les chapitres GitBook historiques sont archivés dans
[`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Ce document est une traduction du [README anglais](../../../README.md).
> En cas de divergence, la version anglaise fait foi.
