<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Segurança" /></a>
  <img src="https://img.shields.io/badge/version-0.36.42-blue" alt="Versão" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Licença" /></a>
</p>

<p align="center">
  Um microkernel escrito em Lean 4 com provas verificadas por máquina, inspirado na
  arquitetura do <a href="https://sel4.systems">seL4</a>. Primeiro alvo de hardware:
  <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Criado cuidadosamente com a ajuda de:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>TRATE ESTE KERNEL DE ACORDO</strong>
  </div>
</p>

<p align="center">
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  **Português** ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## O que é o seLe4n?

O seLe4n é um microkernel construído do zero em Lean 4. Cada transição do kernel
é uma função pura executável. Cada invariante é verificado por máquina pelo
type-checker do Lean — zero `sorry`, zero `axiom`. Toda a superfície de provas
compila para código nativo sem nenhuma prova admitida.

O projeto preserva o modelo de segurança baseado em capabilities do seL4, ao mesmo
tempo em que introduz melhorias arquiteturais possibilitadas pelo framework de
provas do Lean 4:

### Escalonamento e garantias de tempo real

- **Objetos de desempenho composicionais** — tempo de CPU é um objeto de kernel de primeira classe. `SchedContext` encapsula budget, período, prioridade, deadline e domínio em um contexto de escalonamento reutilizável ao qual threads se vinculam via capabilities. O escalonamento CBS (Constant Bandwidth Server) oferece isolamento de banda comprovado (teorema `cbs_bandwidth_bounded`)
- **Servidores passivos** — servidores ociosos emprestam o `SchedContext` do cliente durante IPC, consumindo zero CPU quando não estão atendendo. O invariante `donationChainAcyclic` impede cadeias de doação circulares
- **Timeouts de IPC orientados por budget** — operações bloqueantes são limitadas pelo budget do chamador. Ao expirar, threads são removidas da fila do endpoint e reenfileiradas
- **Protocolo de Herança de Prioridade** — propagação transitiva de prioridade com ausência de deadlock verificada por máquina (`blockingAcyclic`) e profundidade de cadeia limitada. Previne inversão de prioridade ilimitada
- **Teorema de latência limitada** — limite WCRT verificado por máquina: `WCRT = D × L_max + N × (B + P)`, provado em 8 módulos de liveness cobrindo monotonicidade de budget, temporização de reabastecimento, semântica de yield, exaustão de banda e rotação de domínio

### Estruturas de dados e IPC

- **Caminhos críticos O(1) baseados em hash** — todos os armazenamentos de objetos, filas de execução, slots de CNode, mapeamentos de VSpace e filas de IPC utilizam tabelas hash Robin Hood formalmente verificadas com invariantes `distCorrect`, `noDupKeys` e `probeChainDominant`
- **IPC intrusivo com fila dupla** — back-pointers por thread para enfileiramento, desenfileiramento e remoção no meio da fila em O(1)
- **Árvore de derivação de capabilities estável por nó** — índices `childMap` + `parentMap` para transferência de slot, revogação e travessia de descendentes em O(1)

### Segurança e verificação

- **Fluxo de informação com N domínios** — políticas de fluxo parametrizadas que generalizam a partição binária do seL4. Fronteira de enforcement com 44 entradas e provas de não-interferência por operação (indutivo `NonInterferenceStep` com 35 construtores), além de uma trilha de auditoria de desclassificação limitada e fail-closed, com um leitor controlado por capability
- **Camada de provas compostas** — `proofLayerInvariantBundle` compõe 16 pacotes de invariantes de subsistema (núcleo do escalonador + extensões CBS, capabilities, IPC + acoplamento IPC–escalonador, ciclo de vida, serviço, VSpace, inter-subsistema, consistência de TLB, consistência de waiters de notificação, limites de pending/ack do TLB shootdown, invalidação de TLB por núcleo e coerência de I-cache, e o limite do log de auditoria de desclassificação) em uma única obrigação de nível superior verificada desde o boot até todas as operações
- **Arquitetura de estado em três fases** — fase de construção com testemunhas de invariante flui para uma representação imutável congelada com equivalência de lookup provada. 24 operações congeladas espelham a API ativa
- **Conjunto completo de operações** — todas as operações do seL4 implementadas com preservação de invariantes, incluindo suspensão/retomada de threads, gerenciamento de prioridades (setPriority/setMCPriority) e configuração do buffer de IPC
- **Orquestração de serviços** — ciclo de vida de componentes no nível do kernel com grafos de dependência e aciclicidade provada (extensão seLe4n, não presente no seL4)

## Estado atual

<!-- As métricas abaixo são sincronizadas de docs/codebase_map.json → seção readme_sync.
     Regenere com: ./scripts/generate_codebase_map.py --pretty
     Fonte da verdade: docs/codebase_map.json (readme_sync) -->

<!-- MAINTAINERS/TRANSLATORS: the three metric rows below (production LoC,
     test LoC, proved declarations) are WRITTEN by
     scripts/sync_translated_metrics.py from docs/codebase_map.json.  A hand
     edit is overwritten on the next sync.  To reword a label, a preposition
     or an inflected noun, edit that script's TARGETS table in the same
     commit: it matches the surrounding literals verbatim and fails loudly
     when they change, so it can never quietly stop syncing this file. -->

| Atributo | Valor |
|----------|-------|
| **Versão** | `0.36.42` |
| **Toolchain Lean** | `v4.28.0` |
| **LoC Lean de produção** | 433.986 em 361 arquivos |
| **LoC Lean de testes** | 88.629 em 71 suítes de testes |
| **Declarações provadas** | 14.408 declarações de teorema/lema (zero sorry/axiom) |
| **Crates Rust** | 4 (`sele4n-types`, `sele4n-abi`, `sele4n-sys`, `sele4n-hal`) em 80 arquivos-fonte |
| **Hardware alvo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Integração com o hardware** | **H3 CONCLUÍDO** (WS-AG AG1–AG10): HAL, GIC-400, temporizador, tabelas de páginas ARMv8, ponte FFI, boot no QEMU |
| **Auditoria canônica** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — auditoria abrangente pré-1.0 (202 achados; remediados por WS-AK AK1–AK10; arquivada) |
| **Auditoria mais recente** | [`AUDIT_v0.30.11_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../../../docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) — auditoria de prontidão pré-1.0 realizada após o encerramento do WS-AN (sucede a agora arquivada [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md), remediada por WS-AN AN0–AN12). WS-RC R0..R5 LANDED em v0.31.2; WS-RC R6..R14 absorvidos no WS-SM conforme o mapeamento de absorção SM0.Q.1 (ver [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §15`](../../../docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)). Plano de workstream ativo: [`SMP_MULTICORE_COMPLETION_PLAN.md`](../../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md). |
| **Mapa do codebase** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário de declarações legível por máquina |

As métricas são derivadas do código por `./scripts/generate_codebase_map.py`
e armazenadas em [`docs/codebase_map.json`](../../../docs/codebase_map.json) sob a
chave `readme_sync`. Atualize toda a documentação de uma só vez com
`./scripts/sync_documentation_metrics.sh` (somente verificação: `--check`);
`./scripts/report_current_state.py` continua sendo uma verificação cruzada manual.

## Início rápido

```bash
./scripts/setup_lean_env.sh   # instalar o toolchain do Lean
lake build                     # compilar todos os módulos
lake exe sele4n                # executar o harness de rastreamento
./scripts/test_smoke.sh        # validar (higiene + build + trace + estado negativo + sincronia de docs)
```

## Documentação

| Comece aqui | Depois |
|-------------|--------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — fluxo de trabalho, validação, checklist de PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — especificação e marcos |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — semântica de referência do seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário legível por máquina | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — cada item adiado, com um responsável |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — mecânica de contribuição | [`CHANGELOG.md`](../../../CHANGELOG.md) — histórico de versões |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) é a fonte da verdade
para métricas do projeto. Alimenta o [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
e é atualizado automaticamente no merge via CI. Regenere com
`./scripts/generate_codebase_map.py --pretty`.

## Comandos de validação

```bash
./scripts/test_fast.sh      # Tier 0+1: higiene + build
./scripts/test_smoke.sh     # + Tier 2: trace + estado negativo + sincronia de docs
./scripts/test_full.sh      # + Tier 3: âncoras de superfície de invariantes + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: determinismo noturno

./scripts/test_rust.sh                 # Rust no host: build, testes, fmt, clippy
./scripts/test_aarch64_cross_build.sh  # o alvo real do HAL do kernel
```

Execute pelo menos `test_smoke.sh` antes de qualquer PR. Execute `test_full.sh`
ao alterar teoremas, invariantes ou âncoras de documentação.

Após qualquer alteração em `rust/`, execute **as duas** trilhas de Rust. Elas
cobrem metades disjuntas do mesmo crate: no host, todo bloco
`#[cfg(target_arch = "aarch64")]` é removido antes que o rustc ou o clippy o
vejam, então a trilha do host não enxerga os 67 blocos condicionados por cfg,
os 57 pontos de `asm!` nem as quatro fontes `.S` que compõem a maior parte do
HAL. A trilha cruzada compila `sele4n-hal` para
`aarch64-unknown-none-softfloat` nos dois perfis, verifica se as fontes em
assembly foram de fato montadas, executa o lint no alvo cruzado e desmonta os
objetos de release para provar que eles não usam nenhum registrador FP/SIMD —
o kernel não usa ponto flutuante e intercepta FP/SIMD em EL1 desde a sua
primeira instrução — e é uma compilação, não um `cargo check`, porque o
`check` para antes da geração de código e nunca chega a um montador.

## Arquitetura

O seLe4n é organizado como contratos em camadas, cada um com transições executáveis
e provas de preservação de invariantes verificadas por máquina:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Scheduler   │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│   RunQueue   │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
│ SchedContext │             │  Donation  │           │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│        Platform  (Contract, Sim, RPi5)  ← production bindings        │
└──────────────────────────────────────────────────────────────────────┘
```

## Layout dos fontes

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
│   ├── SchedContext/            CBS budget engine, replenishment queue, priority management
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass + BootVSpaceRootEntry
│   ├── Boot.lean                Boot sequence (PlatformConfig → IntermediateState).
│   │                            installBootVSpaceRoot threads canonical boot VSpace
│   │                            through bootFromPlatformChecked (WS-RC R3).
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO).
│                                VSpaceBoot.lean holds the canonical W^X-compliant
│                                boot VSpaceRoot (production-wired since WS-RC R3).
├── Testing/                     Test harness, state builder, invariant checks
Main.lean                        Executable entry point
tests/                           Suítes de testes executáveis + fixtures
```

Cada subsistema segue a **separação Operations/Invariant**: transições em
`Operations.lean`, provas em `Invariant.lean`. O `apiInvariantBundle` unificado
agrega todos os invariantes de subsistema em uma única obrigação de prova. Para o
inventário completo por arquivo, consulte [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparação com o seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **Escalonamento** | Servidor esporádico em C (MCS) | CBS com teorema `cbs_bandwidth_bounded` verificado por máquina; `SchedContext` como objeto de kernel controlado por capabilities |
| **Servidores passivos** | Doação de SchedContext via C | Doação verificada com invariante `donationChainAcyclic` |
| **IPC** | Fila de endpoint com lista encadeada simples | Fila dupla intrusiva com remoção no meio da fila em O(1); timeouts orientados por budget |
| **Fluxo de informação** | Partição binária alto/baixo | Política configurável com N domínios, fronteira de enforcement com 44 entradas (contagem fixada por `enforcementBoundaryExtended_count`), provas de NI por operação e trilha de auditoria controlada por capability para cada desclassificação autorizada |
| **Herança de prioridade** | PIP em C (branch MCS) | PIP transitivo verificado por máquina com ausência de deadlock e limite WCRT paramétrico |
| **Latência limitada** | Sem limite WCRT formal | `WCRT = D × L_max + N × (B + P)` provado em 8 módulos de liveness |
| **Armazenamento de objetos** | Listas encadeadas e arrays | Tabelas hash Robin Hood verificadas (`RHTable`/`RHSet`) com caminhos críticos O(1) |
| **Gerenciamento de serviços** | Ausente no kernel | Orquestração de primeira classe com grafo de dependências e provas de aciclicidade |
| **Provas** | Isabelle/HOL, pós-hoc | Type-checker do Lean 4, co-localizadas com transições — zero sorry/axiom (contagem de declarações provadas na tabela [Estado atual](#estado-atual)) |
| **Plataforma** | HAL em nível C | Typeclass `PlatformBinding` com contratos de fronteira tipados |

## Licença e atribuições de terceiros

O próprio seLe4n é licenciado sob a GNU General Public License v3.0 ou
posterior (GPLv3+); consulte [`LICENSE`](../../../LICENSE) para o texto
completo. As dependências de build de terceiros (`cc`, `find-msvc-tools`,
`shlex`, todas com licença dupla `MIT OR Apache-2.0`) são usadas sob a opção
MIT; seus avisos originais de copyright e de permissão são reproduzidos na
íntegra em [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md).
Nenhum código de terceiros ligado em tempo de execução está presente no
binário do kernel — o HAL é `#![no_std]` e usa apenas `core::*`.

---

> Este documento é uma tradução do [README em inglês](../../../README.md).
> Em caso de divergência, o original em inglês prevalece.
