<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Segurança" /></a>
  <img src="https://img.shields.io/badge/version-0.21.5-blue" alt="Versão" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Licença" /></a>
</p>

<p align="center">
  Um microkernel escrito em Lean 4 com provas verificadas por máquina (machine-checked proofs),
  inspirado na arquitetura do <a href="https://sel4.systems">seL4</a>. Primeiro alvo de hardware:
  <strong>Raspberry Pi 5</strong>.
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | **Português** | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## O que é o seLe4n?

O seLe4n é um microkernel construído do zero em Lean 4. Cada transição do kernel
é uma função pura executável. Cada invariante é verificado por máquina pelo
type-checker do Lean — zero `sorry`, zero `axiom`. Toda a superfície de provas
compila para código nativo sem nenhuma prova admitida (admitted proof).

O projeto utiliza um modelo de segurança baseado em capabilities, introduzindo
melhorias arquiteturais inovadoras em comparação com outros microkernels:

- **Caminhos críticos O(1) baseados em hash (hash-based hot paths)** — todos os armazenamentos de objetos (object stores), filas de execução (run queues), slots de CNode, mapeamentos de VSpace e filas de IPC utilizam `RHTable`/`RHSet` (tabela hash Robin Hood com invariantes verificados por máquina, zero `Std.HashMap`/`Std.HashSet` no estado)
- **Camada de orquestração de serviços (service orchestration)** para gerenciamento de ciclo de vida de componentes e dependências com semântica determinística de falha parcial
- **Árvore de derivação de capabilities estável por nó (node-stable CDT)** com índices `childMap` + `parentMap` em RHTable para transferência de slot, revogação, busca de pai e travessia de descendentes em O(1)
- **IPC intrusivo com fila dupla (dual-queue IPC)** com ponteiros `queuePrev`/`queuePPrev`/`queueNext` por thread para enfileiramento, desenfileiramento e remoção no meio da fila em O(1)
- **Framework de fluxo de informação parametrizado em N domínios (N-domain information-flow)** com políticas de fluxo configuráveis, generalizando os rótulos legados de confidencialidade/integridade (além da partição binária do seL4)
- **Escalonamento EDF + prioridade (EDF + priority scheduling)** com semântica de desenfileiramento no despacho, contexto de registradores por TCB com troca de contexto inline, `RunQueue` com baldes de prioridade e particionamento por domínio

## Estado atual

| Atributo | Valor |
|----------|-------|
| **Versão** | `0.21.5` |
| **Toolchain Lean** | `v4.28.0` |
| **LoC Lean de produção** | 64.039 em 101 arquivos |
| **LoC Lean de testes** | 8.318 em 10 suítes de testes |
| **Declarações provadas** | 1.901 declarações de teorema/lema (zero sorry/axiom) |
| **Hardware alvo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Auditoria mais recente** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — Auditoria completa pré-lançamento do kernel + codebase Rust |
| **Mapa do codebase** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário de declarações legível por máquina |

As métricas são derivadas do codebase por `./scripts/generate_codebase_map.py`
e armazenadas em [`docs/codebase_map.json`](../../../docs/codebase_map.json) na
chave `readme_sync`. Atualize toda a documentação usando
`./scripts/report_current_state.py` como verificação cruzada.

## Início rápido

```bash
./scripts/setup_lean_env.sh   # instalar o toolchain do Lean
lake build                     # compilar todos os módulos
lake exe sele4n                # executar o harness de rastreamento (trace harness)
./scripts/test_smoke.sh        # validar (higiene + build + trace + estado negativo + sincronia de docs)
```

## Roteiro de integração

Novo no projeto? Siga esta ordem de leitura:

1. **Este README** — identidade do projeto, arquitetura e layout dos fontes
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — fluxo de trabalho diário, ciclo de validação, checklist de PR
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo (aprofundamentos em arquitetura, provas, caminho para hardware)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário de módulos e declarações legível por máquina

Para planejamento e histórico de workstreams, consulte [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

## Documentação do projeto

| Documento | Finalidade |
|-----------|------------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Especificação do projeto e marcos (milestones) |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | Semântica de referência do seL4 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Fluxo de trabalho diário, ciclo de validação, checklist de PR |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | Gates de teste em camadas e contrato de CI |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Histórico completo de workstreams, roadmap e índice de auditorias |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Manual completo (arquitetura, design, provas, caminho para hardware) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Inventário do codebase legível por máquina (sincronizado com o README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | Mecânica de contribuição e requisitos de PR |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | Histórico de versões |

## Comandos de validação

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (higiene + build, profundidade semântica de prova L-08)
./scripts/test_smoke.sh     # + Tier 2 (trace + estado negativo + sincronia de docs)
./scripts/test_full.sh      # + Tier 3 (âncoras de superfície de invariantes + corretude de #check Lean)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (determinismo noturno)
```

Execute pelo menos `test_smoke.sh` antes de qualquer PR. Execute `test_full.sh`
ao alterar teoremas, invariantes ou âncoras de documentação.

## Mapa do codebase

[`docs/codebase_map.json`](../../../docs/codebase_map.json) é o inventário
legível por máquina de cada módulo e declaração no projeto. Ele alimenta o site
[seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) e serve como
fonte única da verdade para métricas do projeto.

```bash
./scripts/generate_codebase_map.py --pretty          # regenerar
./scripts/generate_codebase_map.py --pretty --check   # validar sem escrever
```

O mapa inclui:
- **`readme_sync`** — métricas do projeto (versão, LoC, contagem de teoremas) usadas pelo README e documentação
- **`source_sync`** — digest SHA256 determinístico de todos os fontes Lean para invalidação de cache
- **`modules`** — inventário de declarações por módulo com arrays `called` para referências internas

## Arquitetura

O seLe4n é organizado como contratos em camadas, cada um com transições executáveis
e provas de preservação de invariantes verificadas por máquina:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Escalonador │ Capability  │    IPC     │ Ciclo de  │  Serviço (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │   Vida    │  Orquestração  │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│       Fluxo de Informação  (Policy, Projection, Enforcement)         │
├──────────────────────────────────────────────────────────────────────┤
│       Arquitetura  (VSpace, VSpaceBackend, Adapter, Assumptions)     │
├──────────────────────────────────────────────────────────────────────┤
│                     Modelo  (Object, State, CDT)                     │
├──────────────────────────────────────────────────────────────────────┤
│            Fundamentos  (Prelude, Machine, MachineConfig)            │
├──────────────────────────────────────────────────────────────────────┤
│          Plataforma  (Contract, Sim, RPi5)  ← bindings H3-prep      │
└──────────────────────────────────────────────────────────────────────┘
```

Cada subsistema do kernel segue a **separação Operations/Invariant**: transições em
`Operations.lean`, provas em `Invariant.lean`. O `apiInvariantBundle` unificado
agrega todos os invariantes de subsistema em uma única obrigação de prova.

## Comparação com o seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **Mecanismo de IPC** | Fila de endpoint com lista encadeada simples | IPC intrusivo com fila dupla e back-pointers `queuePPrev` para remoção no meio da fila em O(1) |
| **Fluxo de informação** | Partição binária alto/baixo | Política de fluxo configurável com N domínios (generaliza rótulos legados de confidencialidade × integridade) |
| **Gerenciamento de serviços** | Fora do kernel | Orquestração de serviços de primeira classe com grafo de dependências e detecção de ciclos via DFS |
| **Derivação de capabilities** | CDT com lista encadeada de filhos | HashMap `childMap` para consulta de filhos em O(1) |
| **Escalonador** | Fila de prioridade simples (flat) | `RunQueue` com baldes de prioridade, rastreamento inline de `maxPriority` e EDF |
| **VSpace** | Tabelas de página de hardware | `HashMap VAddr (PAddr x PagePermissions)` com enforcement W^X |
| **Metodologia de provas** | Isabelle/HOL, pós-hoc | Type-checker do Lean 4, provas co-localizadas com transições |
| **Abstração de plataforma** | HAL em nível C | Typeclass `PlatformBinding` com contratos de fronteira tipados |

## Próximos passos

As prioridades atuais e o histórico completo de workstreams são mantidos em
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md). Resumo:

- **WS-R** — Remediação Abrangente de Auditoria (8 fases, R1–R8, 111 subtarefas). Aborda todas as 82 descobertas da [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). R1–R7 completas (v0.18.0–v0.18.6), R8 pendente. Plano: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **Binding para hardware Raspberry Pi 5** — page table walk ARMv8, roteamento de interrupções GIC-400, sequência de boot (contratos de plataforma RPi5 agora substanciais via WS-H15)

Portfólios anteriores (WS-B até WS-Q) estão todos completos. Auditorias anteriores
(v0.8.0–v0.9.32), fechamentos de marcos e capítulos legados do GitBook estão
arquivados em [`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Este documento é uma tradução do [README em inglês](../../../README.md).
> Em caso de divergência, o original em inglês prevalece.
