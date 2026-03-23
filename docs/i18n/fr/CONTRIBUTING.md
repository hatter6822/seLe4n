# Contribuer à seLe4n

Merci de contribuer à seLe4n — un micro-noyau (microkernel) orienté production,
écrit en Lean 4 avec des preuves vérifiées par machine.

---

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | [العربية](../ar/CONTRIBUTING.md) | **Français** | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

---

## Licence

seLe4n est distribué sous la [licence publique générale GNU v3.0 ou ultérieure](../../../LICENSE).
En soumettant une pull request ou en contribuant du code à ce projet, vous acceptez
que vos contributions soient placées sous la même licence GPL-3.0-or-later. Vous
certifiez également que vous avez le droit de soumettre la contribution sous cette licence.

## Parcours du contributeur en 5 minutes

1. **Flux de travail et standards :** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **Niveaux de tests :** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **Politique CI :** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **Portée du projet et workstreams :** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **Constats d'audit actifs :** [`docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md)
6. **Historique des workstreams :** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

Manuel complet : [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## Prérequis

Avant de commencer, assurez-vous d'avoir :

- **Lean 4** (v4.28.0) — installé via [elan](https://github.com/leanprover/elan)
- **Lake** — le système de build de Lean (fourni avec l'installation de Lean)
- **Git** — pour le clonage et la gestion des versions
- **ShellCheck** et **ripgrep** — requis pour les tests d'hygiène

```bash
# Installation de la chaîne d'outils Lean
./scripts/setup_lean_env.sh

# Vérification de l'installation
lean --version    # doit afficher v4.28.0
lake --version    # fourni avec Lean
```

## Configurer l'environnement de développement

```bash
# Cloner le dépôt
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n

# Configurer l'environnement Lean
./scripts/setup_lean_env.sh

# Compiler le projet
source ~/.elan/env && lake build

# Exécuter le harnais de trace
lake exe sele4n

# Installer le hook de pre-commit
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

## Validation requise avant d'ouvrir une PR

```bash
./scripts/test_smoke.sh     # niveau minimum requis (Niveau 0-2)
./scripts/test_full.sh      # requis pour les modifications de théorèmes/invariants (Niveau 0-3)
```

### Niveaux de validation

| Niveau | Commande | Portée |
|--------|----------|--------|
| 0 + 1 | `./scripts/test_fast.sh` | Hygiène + compilation |
| 0–2 | `./scripts/test_smoke.sh` | + trace + état négatif + synchronisation docs |
| 0–3 | `./scripts/test_full.sh` | + ancres de surface d'invariants + vérification Lean `#check` |
| 0–4 | `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | + déterminisme nocturne |

## Exigences pour les PR

### Liste de contrôle

- [ ] Identifiant(s) de workstream identifié(s)
- [ ] La portée est un ensemble cohérent et ciblé
- [ ] Les transitions sont déterministes (succès/échec explicite)
- [ ] Les mises à jour d'invariants/théorèmes sont couplées aux changements d'implémentation
- [ ] La documentation est synchronisée dans la même PR
- [ ] Aucun chemin lié au site web n'a été renommé ou supprimé (voir `scripts/website_link_manifest.txt`)
- [ ] `test_smoke.sh` passe (minimum) ; `test_full.sh` pour les changements de théorèmes

### Vérification de compilation par module

**Avant de soumettre un fichier `.lean`**, vous devez vérifier que le module
spécifique compile :

```bash
source ~/.elan/env && lake build <Chemin.Du.Module>
```

Par exemple, si vous avez modifié `SeLe4n/Kernel/RobinHood/Bridge.lean` :

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (cible par défaut) ne suffit pas.** La cible par défaut ne
compile que les modules accessibles depuis `Main.lean` et les exécutables de
test. Les modules qui ne sont pas encore importés par le noyau principal
passeront silencieusement `lake build` même avec des preuves cassées.

## Conventions clés

### Séparation Invariant/Operations

Chaque sous-système du noyau possède :
- `Operations.lean` — les transitions (fonctions de transition d'état)
- `Invariant.lean` — les preuves (théorèmes de préservation)

Maintenez toujours cette séparation.

### Pas de sorry ni d'axiom

L'utilisation de `sorry` et `axiom` est interdite dans la surface de preuve
de production. Les exceptions suivies doivent porter une annotation `TPI-D*`.

### Sémantique déterministe

Toutes les transitions renvoient un succès ou un échec explicite. N'introduisez
jamais de branchements non déterministes.

### Identifiants typés

`ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, etc. sont des structures
d'encapsulation (wrappers), pas des alias de `Nat`. Utilisez explicitement
`.toNat`/`.ofNat`.

### Nommage interne

Les noms de théorèmes, fonctions et définitions doivent décrire la sémantique
(forme de mise à jour de l'état, invariant préservé, chemin de transition). Ne
codez **pas** d'identifiants de workstream (`WS-*`, `wsH*`, etc.) dans les
noms d'identifiants.

## Synchronisation de la documentation

Lors de modifications du comportement, des théorèmes ou du statut d'un
workstream, mettez à jour dans la même PR :

1. `README.md` — synchronisation des métriques depuis `docs/codebase_map.json`
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. Les chapitres GitBook concernés
5. `docs/CLAIM_EVIDENCE_INDEX.md` si les revendications changent
6. `docs/WORKSTREAM_HISTORY.md` si le statut d'un workstream change
7. Regénérer `docs/codebase_map.json` si les sources Lean ont changé

## Signalement de vulnérabilités

Si, au cours de votre travail sur la base de code, vous découvrez une
vulnérabilité logicielle pouvant raisonnablement justifier une désignation CVE
(Common Vulnerabilities and Exposures), vous **devez** la signaler immédiatement
avant de continuer. Cela s'applique aux vulnérabilités trouvées dans :

- Le code du projet
- Les dépendances et la chaîne d'outils
- L'infrastructure de build et de CI
- Les lacunes du modèle/de la spécification

Ne corrigez pas silencieusement une vulnérabilité digne d'un CVE — signalez-la
toujours explicitement pour un suivi, un triage et une divulgation appropriés.

## Besoin d'aide ?

- Consultez le [manuel complet](../../../docs/gitbook/README.md) pour des
  explications approfondies sur l'architecture et les preuves
- Ouvrez une issue sur GitHub pour les questions ou les rapports de bogues
- Consultez l'[historique des workstreams](../../../docs/WORKSTREAM_HISTORY.md)
  pour comprendre l'évolution du projet

---

> Ce document est une traduction du [CONTRIBUTING.md anglais](../../../CONTRIBUTING.md).
> En cas de divergence, la version anglaise fait foi.
