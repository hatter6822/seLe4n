<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="Logo seLe4n" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Sécurité" /></a>
  <img src="https://img.shields.io/badge/version-0.37.35-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## Qu'est-ce que seLe4n ?

seLe4n est un micro-noyau conçu de zéro en Lean 4. Chaque transition du noyau
est une fonction pure exécutable, et chaque invariant est vérifié par le noyau
de Lean : la surface de preuve de production compte zéro `sorry` et zéro
`axiom`. Ce même code Lean est compilé en code natif et lié, avec une petite
couche matérielle en Rust, à l'image du noyau qui démarre sur la cible.

Le projet conserve le modèle de sécurité par capacités de seL4 et, de plus en
plus, l'ABI de seL4 visible par l'utilisateur, tout en utilisant Lean pour en
prouver davantage et le durcir là où seL4 laisse une lacune. La spécification
complète est [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) ; les
points ci-dessous y renvoient.

### L'ABI de seL4

- **Les appels système de seL4-MCS** — les onze appels MCS (`Call` … `Yield`),
  numérotés dans `x7` comme seL4 les numérote ; l'opération est choisie à partir
  de l'appel, du type de la capacité invoquée et de l'étiquette du message
  (`Syscall.selectOperation`), comme dans seL4
- **Les charges d'erreur et de faute de seL4** — `LookupFault`, la trame
  d'erreur dans l'ordre des registres de message de seL4, les fautes de capacité
  côté réception, l'état `Restart`, les arguments de capacité passés comme
  capacités supplémentaires, et la garde portée par la capacité avec un seul
  `resolveAddressBits`
- Le reste du travail sur l'ABI de seL4 (les invocations restantes, les fautes
  de délai, les droits par invocation, l'état Running par cœur) est le flux de
  travail actif WS-SX ; ses lignes sont dans
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Ordonnancement et temps réel

- **Contextes d'ordonnancement comme capacités** — le temps CPU est un objet
  noyau. Un `SchedContext` porte le budget, la période et les recharges de
  seL4-MCS, se configure via l'autorité `SchedControl` du cœur et se lie aux
  threads par des capacités ; ses invariants (`budgetWithinBounds`,
  `refillsConserved`) font partie du faisceau de premier niveau. L'isolation de
  bande passante est `refill_window_bound` : un contexte ne consomme pas plus
  que son budget dans toute fenêtre d'une période, la garantie à fenêtre
  glissante de seL4-MCS. Un ordonnanceur hiérarchique à bande passante
  constante avec une racine EDF, qui ajoute la réciproque (un serveur admis
  reçoit son budget à chaque fenêtre), est le flux de travail prévu WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Serveurs passifs** — un serveur s'exécute sur le contexte d'ordonnancement
  que son client lui donne pendant l'IPC ; `donationChainAcyclic` exclut les
  donations circulaires
- **Délais d'IPC pilotés par le budget** — un thread bloqué dont le budget est
  épuisé est retiré de la file de son endpoint (`timeoutThread`)
- **Héritage de priorité** — propagation transitive avec absence de cycles de
  blocage vérifiée par machine (`blockingAcyclic`) et un théorème d'inversion
  bornée (`pip_bounded_inversion`)
- **Latence bornée** — une borne paramétrique du temps de réponse au pire cas,
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, avec une forme par cœur), prouvée sur
  les modules de `SeLe4n/Kernel/Scheduler/Liveness/`

### Objets noyau et mémoire

- **Objets taillés dans la mémoire untyped** — le retype taille un objet dans
  la région d'une capacité untyped, et la remise à zéro d'un untyped est celle
  de seL4. Déplacer les cellules de chaque objet taillé dans la mémoire même de
  son untyped est le flux de travail actif WS-UC
- **Une entrée du noyau n'alloue rien** — les entrées compilées d'appel
  système, de faute et d'interruption ne font aucune allocation sur le tas ; la
  taille d'un retype n'alloue que les cellules du nouvel objet. La porte de tas
  QEMU (`scripts/test_qemu_heap_allocations_per_syscall.sh`) mesure chaque
  entrée sur l'image démarrée et échoue sur tout autre compte
- **Structures de données** — le magasin d'objets et les mappages VSpace sont
  des tables de hachage Robin Hood vérifiées (`RHTable`, avec `distCorrect`,
  `noDupKeys` et `probeChainDominant`) ; un CNode est un tableau plat de
  `2^radix` emplacements, comme dans seL4 ; les files d'exécution, les files
  d'endpoint et de notification et les attentes de réponse sont chaînées à
  travers les TCB, chacune avec une file abstraite fantôme dont l'accord avec
  les liens est prouvé
- **Arbre de dérivation des capacités chaîné par les emplacements** — chaque
  emplacement porte ses liens parent, premier enfant et frère (la base de
  mappage de seL4), dont l'accord avec l'arbre est prouvé ; la suppression, la
  révocation (la boucle `cteRevoke` de seL4) et le transfert d'emplacement
  parcourent les liens
- **VSpace** — tables de pages ARMv8 avec W^X imposé par cadre et contrôles du
  type de mémoire qui refusent un alias non mis en cache de la RAM

### Sécurité et vérification

- **Flux d'information à N domaines** — politiques de flux paramétrées
  généralisant la partition à deux domaines de seL4 ; une frontière
  d'application dont la longueur est épinglée par
  `enforcementBoundaryExtended_count` (et par `enforcementBoundaryPerCore_count`
  pour la frontière par cœur) ; un théorème de non-interférence pour chaque
  constructeur de `NonInterferenceStep` ; et une piste d'audit de
  déclassification bornée et fail-closed, lue via une capacité `auditTrail`
- **Couche de preuve composée** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) conjoint le faisceau
  d'invariants de chaque sous-système (ordonnanceur, capacités, IPC et son
  couplage à l'ordonnanceur, cycle de vie, registre de services, VSpace,
  inter-sous-systèmes, cohérence TLB et cache d'instructions, shootdown TLB,
  journal d'audit de déclassification, et accord de chaque structure chaînée
  avec son fantôme) en une seule obligation portée du démarrage à travers
  chaque opération
- **Multicœur** — quatre cœurs avec ordonnancement par cœur, IPC et réveil
  inter-cœurs, et shootdown TLB ; le flux de travail d'achèvement SMP (WS-SM)
  est en cours
- **État en trois phases** — une phase de construction avec témoins
  d'invariants se fige en une représentation immuable avec équivalence de
  recherche prouvée ; les opérations figées couvrent les appels système que
  liste `frozenOpCoverage`, épinglés par `frozenOpCoverage_count`
- **Registre de services** — une extension de seLe4n, absente de seL4 : les
  services sont enregistrés et recherchés via une capacité `serviceRegistry` et
  consignés sur l'endpoint qui les sert ; la politique de dépendances reste,
  comme dans seL4, à un gestionnaire de services en espace utilisateur

## État actuel

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Attribut | Valeur |
|----------|--------|
| **Version** | `0.37.35` |
| **Chaîne d'outils Lean** | `v4.28.0` |
| **LoC Lean de production** | 663 097 réparties sur 655 fichiers |
| **LoC Lean de test** | 92 061 réparties sur 71 suites de tests |
| **Déclarations prouvées** | 25 286 déclarations theorem/lemma (zéro sorry/axiom) |
| **Crates Rust** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (enveloppes en espace utilisateur), `sele4n-hal` (la couche matérielle du noyau), et le test hôte `sele4n-lean-boundary` |
| **Matériel cible** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Voies de démarrage** | Chaque voie QEMU démarre d'abord l'image Raspberry Pi 5 sur la machine `raspi5b` de [rpi5_machine](https://github.com/hatter6822/rpi5_machine), puis l'image `virt` sur la machine `virt` de QEMU |
| **Flux de travail** | État de chaque flux de travail ouvert : [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md) ; index et registre de dette : [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Audits** | [`docs/audits/`](../../../docs/audits/README.md) — les artefacts de l'audit actif ; les audits antérieurs sont archivés |
| **Carte de la base de code** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventaire lisible par machine des déclarations |

Les métriques sont dérivées du code par `./scripts/generate_codebase_map.py` et
stockées dans [`docs/codebase_map.json`](../../../docs/codebase_map.json) sous la clé
`readme_sync`. Mettez toute la documentation à jour ensemble avec
`./scripts/sync_documentation_metrics.sh` (vérification seule : `--check`).

## Démarrage rapide

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` ne construit que ce qu'atteignent `Main.lean` et les exécutables
de test ; avant de valider un fichier `.lean`, construisez son module par son
nom (`lake build <Module.Path>`). Le flux de travail complet est dans
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), et les règles que suit chaque
contributeur sont dans [`CLAUDE.md`](../../../CLAUDE.md).

## Documentation

| Commencer ici | Ensuite |
|---------------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — flux de travail, validation, liste de contrôle des PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — spécification et jalons |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manuel complet | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — sémantique de référence de seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventaire lisible par machine | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — chaque élément différé, avec un responsable |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — mécanique de contribution | [`CHANGELOG.md`](../../../CHANGELOG.md) — historique des versions |

## Commandes de validation

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

Exécutez au moins `test_smoke.sh` avant toute PR, et `test_full.sh` lorsque
vous modifiez des théorèmes, des invariants ou des ancres de Tier 3. Un tier
s'arrête à son premier contrôle en échec ; passez `--continue` pour collecter
tous les échecs en une passe.

Après tout changement sous `rust/`, exécutez **les deux** voies Rust. Elles
couvrent des moitiés disjointes de la même crate : sur l'hôte, chaque bloc
`#[cfg(target_arch = "aarch64")]` est retiré avant que rustc ou clippy ne le
voie, si bien que la voie hôte ne voit pas les blocs conditionnels, les sites
`asm!` et les sources `.S` qui forment l'essentiel du HAL. La voie croisée
construit `sele4n-hal` pour `aarch64-unknown-none-softfloat` dans les deux
profils, vérifie que les sources assembleur ont bien été assemblées, analyse la
cible croisée et désassemble les objets release pour prouver qu'ils n'utilisent
aucun registre FP/SIMD. Les voies QEMU construisent rpi5_machine au commit
épinglé dans `scripts/setup_rpi5_machine.sh` au premier usage ; une voie dont
un prérequis manque est signalée NOT RUN plutôt que réussie. La liste complète
est dans [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Architecture

seLe4n est organisé en contrats en couches, chacun avec des transitions
exécutables et des preuves de préservation d'invariants vérifiées par machine :

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

## Structure du code source

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

Chaque sous-système suit la **séparation Operations/Invariant** : les
transitions dans `Operations.lean`, les preuves dans `Invariant.lean`. Le
`apiInvariantBundle` unifié agrège tous les invariants des sous-systèmes en une
seule obligation de preuve. La carte des sous-systèmes est
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5 ; pour l'inventaire complet
par fichier, voir [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparaison avec seL4

| Caractéristique | seL4 | seLe4n |
|-----------------|------|--------|
| **ABI des appels système** | Appels MCS, étiquettes d'invocation, charges d'erreur et de faute | Les mêmes : les onze appels de seL4-MCS et leur numérotation, invocations choisies par étiquette et charges d'erreur de seL4 ; les invocations restantes sont des lignes de WS-SX |
| **Ordonnancement** | Contextes d'ordonnancement MCS avec recharges de serveur sporadique | Le même moteur de recharge, avec son invariant de conservation et la borne d'un budget par fenêtre (`refill_window_bound`) prouvés ; un CBS hiérarchique à racine EDF est prévu (WS-CB) |
| **Serveurs passifs** | Donation de SchedContext | Donation vérifiée avec l'invariant `donationChainAcyclic` |
| **IPC** | Une file par endpoint, chaînée à travers les TCB | Une file d'envoi et une file de réception par endpoint, toutes deux chaînées à travers les TCB avec retrait en O(1) à toute position ; délais pilotés par le budget |
| **Flux d'information** | Partition binaire haut/bas | Politique configurable à N domaines, frontière d'application épinglée par `enforcementBoundaryExtended_count`, un théorème de non-interférence par pas, et une piste d'audit contrôlée par capacité pour chaque déclassification autorisée |
| **Héritage de priorité** | Absent du noyau | PIP transitif vérifié par machine, sans cycles de blocage, avec un théorème d'inversion bornée |
| **Latence bornée** | Aucune borne WCRT formelle | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, prouvée sur les modules de vivacité |
| **Magasin d'objets** | Objets à des adresses physiques | Tables de hachage Robin Hood vérifiées (`RHTable`/`RHSet`) ; les CNodes sont des tableaux plats d'emplacements comme dans seL4 |
| **Mappage mémoire** | W^X non imposé par le noyau | W^X imposé par cadre comme invariant ; les contrôles du type de mémoire refusent un alias non mis en cache de la RAM |
| **Gestion des services** | Hors noyau | Registre de services contrôlé par capacité sur l'endpoint ; politique de dépendances en espace utilisateur |
| **Preuves** | Isabelle/HOL, sur le C par raffinement | Lean 4, co-localisées avec les transitions exécutables ; zéro sorry/axiom (nombre dans le tableau ci-dessus) |
| **Plateforme** | HAL au niveau C | Classe de types `PlatformBinding` avec contrats de frontière typés et un HAL en Rust |

## Licence et attributions tierces

seLe4n lui-même est distribué sous la GNU General Public License v3.0 ou
ultérieure (GPLv3+) ; voir [`LICENSE`](../../../LICENSE) pour le texte intégral.
Les dépendances de compilation tierces (`cc`, `find-msvc-tools`, `shlex`, toutes
sous double licence `MIT OR Apache-2.0`) sont utilisées sous l'option MIT ;
leurs avis de copyright et de permission d'origine sont reproduits à
l'identique dans [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md).
Aucun code tiers lié à l'exécution n'est présent dans le binaire du noyau — le
HAL est `#![no_std]` et n'utilise que `core::*`.

---

> Ce document est une traduction du [README anglais](../../../README.md).
> En cas de divergence, la version anglaise fait foi.
