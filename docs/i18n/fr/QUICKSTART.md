# Démarrage rapide — seLe4n

Guide d'installation et de premiers pas pour seLe4n, un micro-noyau (microkernel)
orienté production écrit en Lean 4 avec des preuves vérifiées par machine.

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | **Français** | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

---

## Prérequis système

| Outil | Version | Description |
|-------|---------|-------------|
| **Git** | 2.30+ | Gestion de version |
| **curl** | toute version récente | Requis par le programme d'installation elan |
| **Lean 4** | v4.28.0 | Installé automatiquement par le script de configuration |
| **Lake** | 0.18.6+ | Système de build (build system) — fourni avec Lean |

### Outils optionnels (pour les tests)

| Outil | Objectif |
|-------|----------|
| **ShellCheck** | Analyse statique des scripts shell (Tier 0) |
| **ripgrep** (`rg`) | Recherche rapide dans la base de code |

## Installation

### Étape 1 : Cloner le dépôt

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

### Étape 2 : Configurer la chaîne d'outils Lean

Le script de configuration installe [elan](https://github.com/leanprover/elan)
(le gestionnaire de versions Lean) et la chaîne d'outils Lean v4.28.0 :

```bash
# Installation de base (sans les dépendances de test)
./scripts/setup_lean_env.sh --skip-test-deps

# Installation complète (avec ShellCheck et ripgrep)
./scripts/setup_lean_env.sh
```

Ce script :
- Installe elan si nécessaire
- Configure la chaîne d'outils Lean v4.28.0
- Installe les dépendances de test (sauf avec `--skip-test-deps`)
- Ajoute Lean au `PATH` de votre shell

### Étape 3 : Compiler le projet

```bash
source ~/.elan/env && lake build
```

La première compilation télécharge les dépendances Lake et compile l'ensemble
des 98 fichiers Lean de production. Cette étape peut prendre plusieurs minutes
lors de la première exécution.

### Étape 4 : Exécuter le harnais de trace

```bash
lake exe sele4n
```

Cette commande exécute le harnais de trace principal, qui démontre les
transitions du noyau sur un état construit par programme. La sortie attendue
est comparée au fichier de référence `tests/fixtures/main_trace_smoke.expected`.

## Vérification de l'installation

Exécutez la suite de tests smoke pour valider que tout fonctionne correctement :

```bash
./scripts/test_smoke.sh
```

Cette commande exécute les niveaux 0 à 2 :
- **Niveau 0** — Hygiène : vérification de l'absence de `sorry`/`axiom`, analyse ShellCheck
- **Niveau 1** — Compilation : `lake build` complet, profondeur sémantique de preuve
- **Niveau 2** — Trace + état négatif + synchronisation de la documentation

En cas de succès, vous verrez un résumé indiquant que tous les niveaux ont passé.

## Commandes de validation détaillées

| Commande | Niveaux | Quand l'utiliser |
|----------|---------|------------------|
| `./scripts/test_fast.sh` | 0 + 1 | Vérification rapide lors du développement |
| `./scripts/test_smoke.sh` | 0–2 | **Minimum requis** avant toute PR |
| `./scripts/test_full.sh` | 0–3 | Modifications de théorèmes ou d'invariants |
| `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | 0–4 | Tests nocturnes et déterminisme |

## Vérification de compilation par module

Lors de la modification d'un fichier `.lean`, vérifiez que le module spécifique
compile avant de soumettre (commit) :

```bash
source ~/.elan/env && lake build <Chemin.Du.Module>
```

**Exemple :**

```bash
# Si vous avez modifié SeLe4n/Kernel/Scheduler/Operations/Core.lean
lake build SeLe4n.Kernel.Scheduler.Operations.Core
```

**Important :** `lake build` (sans argument) ne compile que les modules
accessibles depuis `Main.lean`. Les modules non importés par le point d'entrée
principal ne seront pas vérifiés par la cible par défaut.

### Hook de pre-commit

Installez le hook de pre-commit pour automatiser cette vérification :

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

Le hook :
1. Détecte les fichiers `.lean` indexés (staged)
2. Compile chaque module modifié via `lake build <Chemin.Du.Module>`
3. Vérifie l'absence de `sorry` dans le contenu indexé
4. **Bloque le commit** en cas d'échec de compilation ou de `sorry` détecté

## Structure du projet

```
SeLe4n/Prelude.lean              Identifiants typés, monade KernelM
SeLe4n/Machine.lean              Fichier de registres, mémoire, minuterie
SeLe4n/Model/                    Objets du noyau, état du système, CDT
SeLe4n/Kernel/Scheduler/         Ordonnanceur EDF à priorités
SeLe4n/Kernel/Capability/        Espace de capacités (CSpace), CDT
SeLe4n/Kernel/IPC/               Sous-système IPC à double file
SeLe4n/Kernel/Lifecycle/         Cycle de vie des objets (retype)
SeLe4n/Kernel/Service/           Orchestration de services
SeLe4n/Kernel/Architecture/      VSpace, hypothèses architecturales
SeLe4n/Kernel/InformationFlow/   Étiquettes de sécurité, non-interférence
SeLe4n/Kernel/RobinHood/         Table de hachage Robin Hood vérifiée
SeLe4n/Kernel/RadixTree/         Arbre radix pour CNode (tableau plat)
SeLe4n/Kernel/FrozenOps/         Opérations sur état gelé (frozen state)
SeLe4n/Kernel/API.lean           Interface publique du noyau
SeLe4n/Platform/                 Contrats de plateforme (Sim, RPi5)
SeLe4n/Testing/                  Harnais de test, constructeur d'état
Main.lean                        Point d'entrée exécutable
tests/                           Suites de tests exécutables
```

Chaque sous-système suit la séparation **Operations/Invariant** :
- `Operations.lean` — transitions (fonctions pures de transition d'état)
- `Invariant.lean` — preuves (théorèmes de préservation d'invariants)

## Documentation complémentaire

| Ressource | Description |
|-----------|-------------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Flux de travail de développement complet |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Manuel d'architecture approfondi |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Guide de contribution (en français) |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Historique et feuille de route |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Inventaire lisible par machine |

## Résolution de problèmes courants

### `lean` n'est pas trouvé après l'installation

```bash
source ~/.elan/env
```

Ajoutez cette ligne à votre `~/.bashrc` ou `~/.zshrc` pour un chargement
automatique.

### Échec de compilation lors du premier `lake build`

Vérifiez que la bonne version de la chaîne d'outils est installée :

```bash
lean --version
# Doit afficher : leanprover/lean4:v4.28.0
```

Si la version est incorrecte :

```bash
elan override set leanprover/lean4:v4.28.0
```

### Le hook de pre-commit bloque un commit

Le hook bloque le commit si :
- Un module modifié ne compile pas — corrigez les erreurs de compilation
- Un `sorry` est détecté dans le contenu indexé — complétez la preuve

Ne contournez **pas** le hook avec `--no-verify`.

---

> Ce document est une traduction et une extension du [guide de démarrage rapide anglais](../../../README.md#quick-start).
> En cas de divergence, la version anglaise fait foi.
