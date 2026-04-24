<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="Logo seLe4n" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sécurité" /></a>
  <img src="https://img.shields.io/badge/version-0.30.7-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Licence" /></a>
</p>

<p align="center">
  Un micro-noyau écrit en Lean 4 avec des preuves vérifiées par machine,
  inspiré de l'architecture <a href="https://sel4.systems">seL4</a>. Première cible matérielle :
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Conçu avec soin grâce à :
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>TRAITEZ CE KERNEL EN CONSÉQUENCE</strong>
  </div>
</p>

<p align="center">
  <a href="../../../README.md">English</a> ·
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <strong>Français</strong> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## Qu'est-ce que seLe4n ?

seLe4n est un micro-noyau conçu de zéro en Lean 4. Chaque transition du noyau
est une fonction pure exécutable. Chaque invariant est vérifié par machine via
le vérificateur de types de Lean — zéro `sorry`, zéro `axiom`. L'ensemble de
la surface de preuve se compile en code natif sans aucune preuve admise.

Le projet conserve le modèle de sécurité par capacités de seL4 tout en
introduisant des améliorations architecturales rendues possibles par le cadre
de preuve de Lean 4 :

### Ordonnancement et garanties temps réel

- **Objets de performance composables** — le temps CPU est un objet noyau de première classe. `SchedContext` encapsule budget, période, priorité, échéance et domaine dans un contexte d'ordonnancement réutilisable auquel les threads se lient via des capacités. L'ordonnancement CBS (Constant Bandwidth Server) fournit un isolement de bande passante prouvé (théorème `cbs_bandwidth_bounded`)
- **Serveurs passifs** — les serveurs inactifs empruntent le `SchedContext` du client pendant l'IPC, consommant zéro CPU lorsqu'ils ne servent pas. L'invariant `donationChainAcyclic` empêche les chaînes de donation circulaires
- **Délais d'IPC pilotés par le budget** — les opérations bloquantes sont bornées par le budget de l'appelant. À l'expiration, les threads sont extraits de la file du endpoint et remis en file d'attente
- **Protocole d'héritage de priorité** — propagation transitive de priorité avec absence d'interblocage vérifiée par machine (`blockingChainAcyclic`) et profondeur de chaîne bornée. Empêche l'inversion de priorité non bornée
- **Théorème de latence bornée** — borne WCRT vérifiée par machine : `WCRT = D × L_max + N × (B + P)`, prouvée à travers 7 modules de vivacité couvrant la monotonie du budget, la temporisation des réapprovisionnements, la sémantique du yield, l'épuisement de bande et la rotation de domaine

### Structures de données et IPC

- **Chemins chauds en O(1) par hachage** — tous les magasins d'objets, files d'exécution, emplacements CNode, projections VSpace et files IPC utilisent des tables de hachage Robin Hood formellement vérifiées avec les invariants `distCorrect`, `noDupKeys` et `probeChainDominant`
- **IPC à double file intrusive** — pointeurs inverses par thread pour la mise en file, le retrait et la suppression en milieu de file en O(1)
- **Arbre de dérivation de capacités à nœuds stables** — index `childMap` + `parentMap` pour le transfert d'emplacements, la révocation et la traversée des descendants en O(1)

### Sécurité et vérification

- **Flux d'information à N domaines** — politiques de flux paramétrées généralisant la partition binaire de seL4. Frontière d'application de 30 entrées avec preuves de non-interférence par opération (inductif `NonInterferenceStep` à 32 constructeurs)
- **Couche de preuve composée** — `proofLayerInvariantBundle` compose 10 invariants de sous-systèmes (ordonnanceur, capacité, IPC, cycle de vie, service, VSpace, inter-sous-systèmes, TLB et extensions CBS) en une unique obligation de niveau supérieur vérifiée du démarrage à travers toutes les opérations
- **Architecture d'état en deux phases** — la phase de construction avec témoins d'invariants alimente une représentation immuable gelée avec équivalence de consultation prouvée. 20 opérations gelées reproduisent l'API en temps réel
- **Ensemble complet d'opérations** — toutes les opérations seL4 implémentées avec préservation d'invariants, y compris les 5 opérations différées (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Orchestration de services** — cycle de vie des composants au niveau noyau avec graphes de dépendances et preuves d'acyclicité (extension seLe4n, absente de seL4)

## État actuel

<!-- Les métriques ci-dessous sont synchronisées depuis docs/codebase_map.json → section readme_sync.
     Regénérer avec : ./scripts/generate_codebase_map.py --pretty
     Source de vérité : docs/codebase_map.json (readme_sync) -->

| Attribut | Valeur |
|----------|--------|
| **Version** | `0.30.6` |
| **Chaîne d'outils Lean** | `v4.28.0` |
| **LoC Lean de production** | 103 179 réparties sur 142 fichiers |
| **LoC Lean de test** | 14 890 réparties sur 24 suites de tests |
| **Déclarations prouvées** | 3 045 déclarations theorem/lemma (zéro sorry/axiom) |
| **Matériel cible** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Audit canonique** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — audit complet pré-1.0 (202 résultats ; corrigés par WS-AK AK1–AK10) |
| **Dernier audit** | [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.6_COMPREHENSIVE.md) — audit de durcissement pré-1.0 (3 CRIT, 24 HIGH, 71 MED, 58 LOW, 40 INFO — notation initiale selon §0.4) |
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
./scripts/test_smoke.sh        # valider (hygiène + compilation + trace + état négatif + synchro docs)
```

## Documentation

| Commencez ici | Ensuite |
|---------------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flux de travail, validation, liste de contrôle des PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — spécification et jalons |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manuel complet | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — sémantique de référence seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventaire lisible par machine | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — historique des flux de travail et feuille de route |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — modalités de contribution | [`CHANGELOG.md`](../../../CHANGELOG.md) — historique des versions |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) est la source de vérité pour
les métriques du projet. Il alimente [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
et est actualisé automatiquement à chaque merge via CI. Regénérez avec
`./scripts/generate_codebase_map.py --pretty`.

## Commandes de validation

```bash
./scripts/test_fast.sh      # Niveau 0+1 : hygiène + compilation
./scripts/test_smoke.sh     # + Niveau 2 : trace + état négatif + synchro docs
./scripts/test_full.sh      # + Niveau 3 : ancres de surface d'invariants + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Niveau 4 : déterminisme nocturne
```

Exécutez au minimum `test_smoke.sh` avant toute PR. Exécutez `test_full.sh`
lors de modifications des théorèmes, invariants ou ancres de documentation.

## Architecture

seLe4n est organisé en couches contractuelles, chacune dotée de transitions
exécutables et de preuves de préservation d'invariants vérifiées par machine :

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

## Structure du code source

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

Chaque sous-système suit la séparation **Operations/Invariant** : les transitions
dans `Operations.lean`, les preuves dans `Invariant.lean`. Le
`apiInvariantBundle` unifié agrège tous les invariants des sous-systèmes en une
seule obligation de preuve. Pour l'inventaire complet par fichier, consultez
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparaison avec seL4

| Fonctionnalité | seL4 | seLe4n |
|----------------|------|--------|
| **Ordonnancement** | Serveur sporadique implémenté en C (MCS) | CBS avec théorème `cbs_bandwidth_bounded` vérifié par machine ; `SchedContext` comme objet noyau contrôlé par capacités |
| **Serveurs passifs** | Donation de SchedContext via C | Donation vérifiée avec invariant `donationChainAcyclic` |
| **IPC** | File d'attente endpoint à liste chaînée simple | Double file intrusive avec suppression en milieu de file en O(1) ; délais pilotés par le budget |
| **Flux d'information** | Partition binaire haut/bas | Politique configurable à N domaines avec frontière d'application de 30 entrées et preuves de non-interférence par opération |
| **Héritage de priorité** | PIP implémenté en C (branche MCS) | PIP transitif vérifié par machine avec absence d'interblocage et borne WCRT paramétrique |
| **Latence bornée** | Aucune borne WCRT formelle | `WCRT = D × L_max + N × (B + P)` prouvée à travers 7 modules de vivacité |
| **Magasins d'objets** | Listes chaînées et tableaux | Tables de hachage Robin Hood vérifiées (`RHTable`/`RHSet`) avec chemins chauds en O(1) |
| **Gestion des services** | Hors noyau | Orchestration de première classe avec graphe de dépendances et preuves d'acyclicité |
| **Preuves** | Isabelle/HOL, a posteriori | Vérificateur de types Lean 4, co-localisées avec les transitions (2 447 théorèmes, zéro sorry/axiom) |
| **Plateforme** | HAL au niveau C | Classe de types `PlatformBinding` avec contrats de frontière typés |

## Prochaines étapes

L'ensemble des flux de travail logiciels (WS-B à WS-AB) est terminé.
L'historique complet se trouve dans [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

### Flux de travail terminés

| Flux de travail | Périmètre | Version |
|-----------------|-----------|---------|
| **WS-AB** | Opérations différées et vivacité — suspend/resume, setPriority/setMCPriority, setIPCBuffer, Protocole d'Héritage de Priorité, Théorème de Latence Bornée (6 phases, 90 tâches) | v0.24.0–v0.25.5 |
| **WS-Z** | Objets de performance composables — `SchedContext` comme 7e objet noyau, moteur de budget CBS, file de réapprovisionnement, donation de serveur passif, endpoints avec timeout (10 phases, 213 tâches) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | Sous-systèmes centraux du noyau, tables de hachage Robin Hood, arbres radix, état gelé, flux d'information, orchestration de services, contrats de plateforme | v0.9.0–v0.22.x |

Plans détaillés : [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### Prochain jalon majeur

**Liaison matérielle Raspberry Pi 5** — parcours de tables de pages ARMv8,
routage d'interruptions GIC-400, séquence de démarrage. Les audits antérieurs
et les clôtures de jalons sont archivés dans
[`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Ce document est une traduction du [README anglais](../../../README.md).
> En cas de divergence, la version anglaise fait foi.
