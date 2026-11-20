<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Segurança" /></a>
  <img src="https://img.shields.io/badge/version-0.37.35-blue" alt="Versão" />
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

O seLe4n é um micronúcleo construído do zero em Lean 4. Cada transição do
núcleo é uma função pura executável, e cada invariante é verificado pelo núcleo
do Lean: a superfície de provas de produção tem zero `sorry` e zero `axiom`. O
mesmo código Lean é compilado para código nativo e ligado, com uma pequena
camada de hardware em Rust, à imagem do núcleo que inicializa no alvo.

O projeto mantém o modelo de segurança baseado em capacidades do seL4 e, cada
vez mais, a ABI do seL4 visível ao usuário, usando o Lean para provar mais
sobre ela e endurecê-la onde o seL4 deixa uma lacuna. A especificação completa
é [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md); os itens abaixo
apontam para ela.

### A ABI do seL4

- **As chamadas de sistema do seL4-MCS** — as onze chamadas MCS (`Call` …
  `Yield`), numeradas em `x7` como o seL4 as numera; a operação é escolhida a
  partir da chamada, do tipo da capacidade invocada e do rótulo da mensagem
  (`Syscall.selectOperation`), como no seL4
- **As cargas de erro e de falta do seL4** — `LookupFault`, o quadro de erro na
  ordem de registradores de mensagem do seL4, faltas de capacidade no lado
  receptor, o estado `Restart`, argumentos de capacidade passados como
  capacidades extras, e a guarda mantida na capacidade com um único
  `resolveAddressBits`
- O restante do trabalho na ABI do seL4 (as invocações restantes, faltas de
  timeout, direitos por invocação, o estado Running por núcleo) é o fluxo de
  trabalho ativo WS-SX; suas linhas estão em
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Escalonamento e tempo real

- **Contextos de escalonamento como capacidades** — o tempo de CPU é um objeto
  do núcleo. Um `SchedContext` guarda o orçamento, o período e as recargas do
  seL4-MCS, é configurado pela autoridade `SchedControl` do núcleo de CPU e
  vinculado a threads por capacidades; seus invariantes (`budgetWithinBounds`,
  `refillsConserved`) fazem parte do pacote de nível superior. O isolamento de
  largura de banda é `refill_window_bound`: um contexto não executa mais que
  seu orçamento em nenhuma janela de um período, a garantia de janela
  deslizante do seL4-MCS. Um escalonador hierárquico de largura de banda
  constante com raiz EDF, que acrescenta a recíproca (um servidor admitido
  recebe seu orçamento a cada janela), é o fluxo de trabalho planejado WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Servidores passivos** — um servidor executa no contexto de escalonamento
  que seu cliente doa durante o IPC; `donationChainAcyclic` exclui doações
  circulares
- **Timeouts de IPC guiados pelo orçamento** — uma thread bloqueada cujo
  orçamento se esgota é removida da fila do seu endpoint (`timeoutThread`)
- **Herança de prioridade** — propagação transitiva com ausência de ciclos de
  bloqueio verificada por máquina (`blockingAcyclic`) e um teorema de inversão
  limitada (`pip_bounded_inversion`)
- **Latência limitada** — um limite paramétrico do tempo de resposta no pior
  caso, `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, com uma forma por núcleo), provado
  sobre os módulos de `SeLe4n/Kernel/Scheduler/Liveness/`

### Objetos do núcleo e memória

- **Objetos talhados em memória untyped** — o retype talha um objeto na região
  de uma capacidade untyped, e o reset de um untyped é o do seL4. Mover as
  células de cada objeto talhado para a própria memória do seu untyped é o
  fluxo de trabalho ativo WS-UC
- **Uma entrada do núcleo não aloca nada** — as entradas compiladas de chamada
  de sistema, falta e interrupção não fazem alocação no heap; o talho de um
  retype aloca apenas as células do novo objeto. O portão de heap do QEMU
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) mede cada entrada na
  imagem inicializada e falha em qualquer outra contagem
- **Estruturas de dados** — o armazém de objetos e os mapeamentos de VSpace são
  tabelas hash Robin Hood verificadas (`RHTable`, com `distCorrect`,
  `noDupKeys` e `probeChainDominant`); um CNode é um vetor plano de `2^radix`
  slots, como no seL4; filas de execução, filas de endpoint e de notificação e
  esperas de resposta são encadeadas pelos TCBs, cada uma com uma fila
  abstrata fantasma cuja concordância com os elos é provada
- **Árvore de derivação de capacidades encadeada pelos slots** — cada slot
  guarda seus elos de pai, primeiro filho e irmão (o banco de mapeamento do
  seL4), com concordância com a árvore provada; remoção, revogação (o laço
  `cteRevoke` do seL4) e transferência de slot percorrem os elos
- **VSpace** — tabelas de páginas ARMv8 com W^X imposto por quadro e
  verificações de tipo de memória que recusam um alias sem cache da RAM

### Segurança e verificação

- **Fluxo de informação com N domínios** — políticas de fluxo parametrizadas
  que generalizam a partição de dois domínios do seL4; uma fronteira de
  aplicação cujo tamanho é fixado por `enforcementBoundaryExtended_count` (e
  por `enforcementBoundaryPerCore_count` para a fronteira por núcleo); um
  teorema de não interferência para cada construtor de `NonInterferenceStep`; e
  uma trilha de auditoria de desclassificação limitada e fail-closed, lida por
  uma capacidade `auditTrail`
- **Camada de provas composta** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) une o pacote de invariantes de
  cada subsistema (escalonador, capacidades, IPC e seu acoplamento com o
  escalonador, ciclo de vida, registro de serviços, VSpace, entre subsistemas,
  coerência de TLB e de cache de instruções, shootdown de TLB, log de auditoria
  de desclassificação, e a concordância de cada estrutura encadeada com seu
  fantasma) em uma única obrigação mantida desde a inicialização em cada
  operação
- **Multinúcleo** — quatro núcleos com escalonamento por núcleo, IPC e
  despertar entre núcleos, e shootdown de TLB; o fluxo de trabalho de
  conclusão de SMP (WS-SM) está em andamento
- **Estado em três fases** — uma fase de construção com testemunhas de
  invariantes congela numa representação imutável com equivalência de busca
  provada; as operações congeladas cobrem as chamadas que `frozenOpCoverage`
  lista, fixadas por `frozenOpCoverage_count`
- **Registro de serviços** — uma extensão do seLe4n, ausente no seL4: serviços
  são registrados e consultados por uma capacidade `serviceRegistry` e
  anotados no endpoint que os atende; a política de dependências fica, como no
  seL4, a cargo de um gerenciador de serviços em espaço de usuário

## Estado atual

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Atributo | Valor |
|----------|-------|
| **Versão** | `0.37.35` |
| **Toolchain Lean** | `v4.28.0` |
| **LoC Lean de produção** | 652.027 em 646 arquivos |
| **LoC Lean de testes** | 91.310 em 70 suítes de testes |
| **Declarações provadas** | 24.838 declarações de teorema/lema (zero sorry/axiom) |
| **Crates Rust** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (wrappers em espaço de usuário), `sele4n-hal` (a camada de hardware do núcleo) e o teste de host `sele4n-lean-boundary` |
| **Hardware alvo** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Trilhas de boot** | Cada trilha QEMU inicializa primeiro a imagem do Raspberry Pi 5 na máquina `raspi5b` do [rpi5_machine](https://github.com/hatter6822/rpi5_machine) e depois a imagem `virt` na máquina `virt` do QEMU |
| **Fluxos de trabalho** | Estado de cada fluxo de trabalho aberto: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); índice e registro de dívidas: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Auditorias** | [`docs/audits/`](../../../docs/audits/README.md) — os artefatos da auditoria ativa; as anteriores estão arquivadas |
| **Mapa do código** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário de declarações legível por máquina |

As métricas são derivadas do código por `./scripts/generate_codebase_map.py` e
guardadas em [`docs/codebase_map.json`](../../../docs/codebase_map.json) na chave
`readme_sync`. Atualize toda a documentação junto com
`./scripts/sync_documentation_metrics.sh` (apenas verificação: `--check`).

## Início rápido

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` constrói apenas o que `Main.lean` e os executáveis de teste
alcançam; antes de fazer commit de um arquivo `.lean`, construa seu módulo pelo
nome (`lake build <Module.Path>`). O fluxo completo está em
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), e as regras que todo
colaborador segue estão em [`CLAUDE.md`](../../../CLAUDE.md).

## Documentação

| Comece aqui | Depois |
|-------------|--------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — fluxo de trabalho, validação, checklist de PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — especificação e marcos |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — manual completo | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — semântica de referência do seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — inventário legível por máquina | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — cada item adiado, com um responsável |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — mecânica de contribuição | [`CHANGELOG.md`](../../../CHANGELOG.md) — histórico de versões |

## Comandos de validação

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

Execute pelo menos `test_smoke.sh` antes de qualquer PR, e `test_full.sh` ao
alterar teoremas, invariantes ou âncoras de Tier 3. Um tier para na primeira
verificação que falha; passe `--continue` para coletar todas as falhas de uma
vez.

Depois de qualquer mudança em `rust/`, execute **as duas** trilhas Rust. Elas
cobrem metades disjuntas da mesma crate: no host, cada bloco
`#[cfg(target_arch = "aarch64")]` é removido antes que rustc ou clippy o vejam,
então a trilha de host não vê os blocos condicionais, os sítios `asm!` nem as
fontes `.S` que formam a maior parte do HAL. A trilha cruzada constrói
`sele4n-hal` para `aarch64-unknown-none-softfloat` nos dois perfis, verifica
que as fontes assembly foram montadas, analisa o alvo cruzado e desmonta os
objetos de release para provar que não usam nenhum registrador FP/SIMD. As
trilhas QEMU constroem o rpi5_machine no commit fixado em
`scripts/setup_rpi5_machine.sh` no primeiro uso; uma trilha sem um
pré-requisito é reportada como NOT RUN em vez de aprovada. A lista completa
está em [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Arquitetura

O seLe4n é organizado em contratos em camadas, cada um com transições
executáveis e provas de preservação de invariantes verificadas por máquina:

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

## Estrutura do código-fonte

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

Cada subsistema segue a **separação Operations/Invariant**: transições em
`Operations.lean`, provas em `Invariant.lean`. O `apiInvariantBundle`
unificado agrega todos os invariantes dos subsistemas numa única obrigação de
prova. O mapa de subsistemas é [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
§5; para o inventário completo por arquivo, veja
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Comparação com o seL4

| Característica | seL4 | seLe4n |
|----------------|------|--------|
| **ABI de chamadas de sistema** | Chamadas MCS, rótulos de invocação, cargas de erro e de falta | As mesmas: as onze chamadas do seL4-MCS com sua numeração, invocações escolhidas por rótulo e as cargas de erro do seL4; as invocações restantes são linhas do WS-SX |
| **Escalonamento** | Contextos de escalonamento MCS com recargas de servidor esporádico | O mesmo motor de recargas, com seu invariante de conservação e o limite de um orçamento por janela (`refill_window_bound`) provados; um CBS hierárquico com raiz EDF está planejado (WS-CB) |
| **Servidores passivos** | Doação de SchedContext | Doação verificada com o invariante `donationChainAcyclic` |
| **IPC** | Uma fila por endpoint, encadeada pelos TCBs | Uma fila de envio e uma de recepção por endpoint, ambas encadeadas pelos TCBs com remoção em O(1) de qualquer posição; timeouts guiados pelo orçamento |
| **Fluxo de informação** | Partição binária alto/baixo | Política configurável de N domínios, fronteira de aplicação fixada por `enforcementBoundaryExtended_count`, um teorema de não interferência por passo, e uma trilha de auditoria controlada por capacidade para cada desclassificação autorizada |
| **Herança de prioridade** | Fora do núcleo | PIP transitivo verificado por máquina, sem ciclos de bloqueio, com um teorema de inversão limitada |
| **Latência limitada** | Sem limite WCRT formal | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, provado sobre os módulos de vivacidade |
| **Armazém de objetos** | Objetos em endereços físicos | Tabelas hash Robin Hood verificadas (`RHTable`/`RHSet`); CNodes são vetores planos de slots como no seL4 |
| **Mapeamento de memória** | W^X não imposto pelo núcleo | W^X imposto por quadro como invariante; verificações de tipo de memória recusam um alias sem cache da RAM |
| **Gerenciamento de serviços** | Fora do núcleo | Registro de serviços controlado por capacidade no endpoint; política de dependências em espaço de usuário |
| **Provas** | Isabelle/HOL, sobre o C por refinamento | Lean 4, junto às transições executáveis; zero sorry/axiom (contagem na tabela acima) |
| **Plataforma** | HAL em nível de C | Typeclass `PlatformBinding` com contratos de fronteira tipados e um HAL em Rust |

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
