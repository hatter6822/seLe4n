# Guia de Início Rápido do seLe4n

Um guia prático para começar a trabalhar com o seLe4n — um microkernel
orientado a produção escrito em Lean 4 com provas verificadas por máquina
(machine-checked proofs).

> Este documento complementa o [README em português](README.md).
> Para a documentação completa, consulte o [README em inglês](../../../README.md).

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | **Português** | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

---

## Pré-requisitos

- **Sistema operacional**: Linux (recomendado) ou macOS
- **Git**: versão 2.20 ou superior
- **Conexão com a internet**: necessária para baixar o toolchain do Lean e dependências
- **Espaço em disco**: pelo menos 2 GB livres para o toolchain e cache de build

O script de configuração instalará automaticamente:
- **elan**: gerenciador de toolchains do Lean (similar ao rustup para Rust)
- **Lean 4**: versão `v4.28.0` (especificada no `lean-toolchain`)
- **Lake**: sistema de build do Lean (incluído com o Lean)

## Instalação passo a passo

### 1. Clonar o repositório

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

### 2. Configurar o ambiente

O script de configuração instala o elan (se necessário) e configura o toolchain
correto do Lean:

```bash
# Configuração básica (sem dependências de teste)
./scripts/setup_lean_env.sh --skip-test-deps

# Configuração completa (inclui shellcheck, ripgrep para testes)
./scripts/setup_lean_env.sh
```

### 3. Compilar o projeto

```bash
source ~/.elan/env
lake build
```

A primeira compilação pode levar vários minutos enquanto o Lean compila todas
as dependências e verifica as provas. Compilações subsequentes serão incrementais
e muito mais rápidas.

### 4. Executar o harness de rastreamento (trace harness)

```bash
lake exe sele4n
```

Esse comando executa o harness principal de rastreamento, que demonstra as
transições do kernel em ação. A saída deve corresponder ao fixture esperado
em `tests/fixtures/main_trace_smoke.expected`.

### 5. Validar a instalação

```bash
./scripts/test_smoke.sh
```

Se todos os testes passarem, seu ambiente está configurado corretamente.

## Comandos de validação em camadas (tiered validation)

O seLe4n utiliza um sistema de validação em camadas progressivas:

| Comando | Camadas | O que valida |
|---------|---------|-------------|
| `./scripts/test_fast.sh` | Tier 0 + 1 | Higiene do código + compilação (build) |
| `./scripts/test_smoke.sh` | Tier 0–2 | + Rastreamento (trace) + estado negativo + sincronia de docs |
| `./scripts/test_full.sh` | Tier 0–3 | + Âncoras de superfície de invariantes + corretude de `#check` |
| `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh` | Tier 0–4 | + Determinismo noturno |

**Regras de ouro:**
- Execute `test_smoke.sh` **antes de cada PR**
- Execute `test_full.sh` ao **alterar teoremas, invariantes ou âncoras de documentação**
- O CI executará automaticamente a validação apropriada

## Verificação de módulo individual

Ao trabalhar em um módulo específico, você pode verificá-lo individualmente,
o que é mais rápido do que compilar todo o projeto:

```bash
# Sintaxe: lake build <Caminho.Do.Modulo>
# Exemplos:
lake build SeLe4n.Kernel.Scheduler.Operations.Core
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
lake build SeLe4n.Kernel.RobinHood.Core
lake build SeLe4n.Model.State
```

**Importante:** `lake build` sem argumentos compila apenas módulos alcançáveis
a partir de `Main.lean`. Módulos não importados pelo kernel principal podem ter
erros que passam despercebidos. Sempre use `lake build <Modulo>` para os
arquivos que você modificou.

## Estrutura do projeto

Familiarize-se com a organização principal do código-fonte:

```
SeLe4n/
├── Prelude.lean                 Identificadores tipados, mônada KernelM
├── Machine.lean                 Primitivas de estado da máquina
├── Model/                       Objetos e estado do kernel
│   ├── Object/                  Tipos de dados (TCB, Endpoint, CNode, etc.)
│   └── State.lean               Representação do estado do sistema
├── Kernel/                      Subsistemas do kernel
│   ├── Scheduler/               Escalonador (RunQueue, EDF, domínios)
│   ├── Capability/              CSpace, CDT, operações de capability
│   ├── IPC/                     IPC com fila dupla (dual-queue)
│   ├── Lifecycle/               Retype e gerenciamento de ciclo de vida
│   ├── Service/                 Orquestração de serviços
│   ├── Architecture/            VSpace, decodificação de registradores
│   ├── InformationFlow/         Segurança de fluxo de informação
│   ├── RobinHood/               Tabela hash Robin Hood verificada
│   ├── RadixTree/               Árvore radix (flat array) para CNode
│   ├── FrozenOps/               Operações sobre estado congelado
│   ├── API.lean                 API pública unificada
│   └── CrossSubsystem.lean      Invariantes cross-subsystem
├── Platform/                    Contratos de plataforma
│   ├── Sim/                     Plataforma de simulação (para testes)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712)
└── Testing/                     Harness de testes e builder de estado

tests/                           Suítes de teste executáveis
docs/                            Documentação do projeto
scripts/                         Scripts de validação e CI
```

## Conceitos-chave

### Provas verificadas por máquina (machine-checked proofs)

Cada transição do kernel é uma função pura em Lean 4. Os invariantes são
expressos como teoremas que o type-checker do Lean verifica automaticamente.
O projeto mantém **zero `sorry`** (provas adiadas) e **zero `axiom`**
(axiomas adicionais).

### Modelo de capabilities

O seLe4n utiliza um modelo de segurança baseado em capabilities, onde o acesso
a recursos do kernel é mediado por capabilities (tokens de autoridade) organizadas
em uma árvore de derivação (CDT — Capability Derivation Tree).

### Separação Operations/Invariant

Cada subsistema do kernel mantém uma separação estrita:
- **`Operations.lean`** — transições de estado (funções puras executáveis)
- **`Invariant.lean`** — provas de preservação de invariantes

### RHTable (Robin Hood Hash Table)

O seLe4n substitui `Std.HashMap`/`Std.HashSet` por `RHTable`/`RHSet`, uma
implementação de tabela hash Robin Hood com invariantes formalmente verificados
e operações O(1). Todas as estruturas de dados críticas do kernel usam essa
implementação.

## Roteiro de aprendizado

Depois de configurar o ambiente, siga esta ordem para se aprofundar:

1. **Leia o README completo** — [README em português](README.md) para visão geral da arquitetura
2. **Explore o fluxo de trabalho** — [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) para entender o ciclo diário
3. **Consulte o manual** — [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) para aprofundamentos
4. **Examine o código** — comece por `SeLe4n/Prelude.lean` e `SeLe4n/Model/State.lean`
5. **Estude uma transição** — veja `SeLe4n/Kernel/Scheduler/Operations/Core.lean` como exemplo
6. **Leia uma prova** — examine `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`

## Solução de problemas

### O `lake build` falha na primeira compilação

Certifique-se de que o ambiente do elan está carregado:
```bash
source ~/.elan/env
```

Se o problema persistir, tente reconfigurar:
```bash
lake clean
lake build
```

### Erros de versão do toolchain

O seLe4n requer exatamente a versão `v4.28.0` do Lean. Verifique sua versão:
```bash
lean --version
```

Se estiver incorreta, o elan deve selecionar automaticamente a versão correta
com base no arquivo `lean-toolchain` no repositório.

### Testes falham após alterações

Execute a verificação do módulo específico que você alterou:
```bash
lake build SeLe4n.Caminho.Do.Modulo
```

Se houver erros de prova, verifique se suas alterações preservam os invariantes
existentes. O type-checker do Lean indicará exatamente onde a prova falha.

## Próximos passos

- Consulte o [guia de contribuição em português](CONTRIBUTING.md) para abrir PRs
- Explore as [issues abertas](https://github.com/hatter6822/seLe4n/issues) para encontrar tarefas
- Leia o [histórico de workstreams](../../../docs/WORKSTREAM_HISTORY.md) para entender o roadmap
