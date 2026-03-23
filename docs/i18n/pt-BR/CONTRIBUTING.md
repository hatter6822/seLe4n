# Contribuindo com o seLe4n

Obrigado por contribuir com o seLe4n — um microkernel orientado a produção
escrito em Lean 4 com provas verificadas por máquina (machine-checked proofs).

> Este documento é uma tradução do [CONTRIBUTING.md em inglês](../../../CONTRIBUTING.md).
> Em caso de divergência, o original em inglês prevalece.

---

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | [العربية](../ar/CONTRIBUTING.md) | [Français](../fr/CONTRIBUTING.md) | **Português** | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

---

## Licença

O seLe4n é licenciado sob a [GNU General Public License v3.0 ou posterior](../../../LICENSE).
Ao enviar um pull request ou contribuir com código para este projeto, você concorda
que suas contribuições serão licenciadas sob a mesma licença GPL-3.0-or-later. Você
também certifica que tem o direito de enviar a contribuição sob esta licença.

## Caminho do contribuidor em 5 minutos

1. **Fluxo de trabalho + padrões:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **Camadas de teste (testing tiers):** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **Política de CI:** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **Escopo do projeto + workstreams:** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **Descobertas de auditoria ativas:** [`docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.18.7_PRE_BENCHMARK.md)
6. **Histórico de workstreams:** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

Manual completo: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## Configuração do ambiente de desenvolvimento

Antes de começar a contribuir, configure seu ambiente local:

```bash
# Clonar o repositório
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n

# Instalar o toolchain do Lean (elan + Lean 4)
./scripts/setup_lean_env.sh

# Compilar o projeto
source ~/.elan/env && lake build

# Executar os testes de fumaça (smoke tests) para verificar a configuração
./scripts/test_smoke.sh
```

## Validação obrigatória antes de abrir um PR

```bash
./scripts/test_smoke.sh     # gate mínimo (Tier 0-2)
./scripts/test_full.sh      # obrigatório para alterações em teoremas/invariantes (Tier 0-3)
```

### Verificação de build por módulo

**Antes de fazer commit de qualquer arquivo `.lean`**, você DEVE verificar que o
módulo específico compila:

```bash
source ~/.elan/env && lake build <Caminho.Do.Modulo>
```

Por exemplo, se você modificou `SeLe4n/Kernel/RobinHood/Bridge.lean`:
```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (alvo padrão) NÃO é suficiente.** O alvo padrão compila apenas
módulos alcançáveis a partir de `Main.lean` e executáveis de teste. Módulos que
ainda não são importados pelo kernel principal passarão silenciosamente no
`lake build` mesmo com provas quebradas.

## Requisitos de PR

- Identificar o(s) ID(s) de workstream avançado(s)
- Manter o escopo em uma fatia coerente
- Transições devem ser determinísticas (sucesso/falha explícitos)
- Atualizações de invariantes/teoremas emparelhadas com mudanças de implementação
- Sincronizar documentação no mesmo PR
- Consulte o checklist completo em [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)

## Convenções de código

### Separação Operations/Invariant

Cada subsistema do kernel mantém uma separação estrita entre transições e provas:

- `Operations.lean` — funções de transição de estado (executáveis, puras, determinísticas)
- `Invariant.lean` — teoremas de preservação de invariantes

Não misture lógica de transição com provas no mesmo arquivo.

### Identificadores tipados (typed identifiers)

O seLe4n usa tipos wrapper em vez de aliases de `Nat` para identificadores:

- `ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId`, etc.
- Use `.toNat` / `.ofNat` para conversões explícitas
- Nunca passe um `Nat` bruto onde um identificador tipado é esperado

### Proibição de sorry/axiom

Nenhum `sorry` ou `axiom` é permitido na superfície de provas de produção.
Se um teorema não puder ser provado imediatamente, discuta a abordagem antes
de enviar um stub.

### Semântica determinística

Todas as transições retornam sucesso/falha explícitos. Nunca introduza
branches não determinísticos. Use tipos de resultado (result types) para
comunicar falhas de forma explícita.

## Estrutura de diretórios

```
SeLe4n/                          Código-fonte principal do kernel
  Prelude.lean                   Identificadores tipados, mônada KernelM
  Machine.lean                   Arquivo de registradores, memória, timer
  Model/                         Objetos do kernel, estado, CDT
  Kernel/                        Subsistemas do kernel
    Scheduler/                   Escalonador com RunQueue e EDF
    Capability/                  CSpace, CDT, operações de capability
    IPC/                         IPC com fila dupla intrusiva
    Lifecycle/                   Retype e ciclo de vida de objetos
    Service/                     Orquestração de serviços
    Architecture/                VSpace, VSpaceBackend, Adapter
    InformationFlow/             Rótulos de segurança, projeção, não interferência
    RobinHood/                   Tabela hash Robin Hood verificada
    RadixTree/                   Árvore radix para CNode (flat array)
    FrozenOps/                   Operações sobre estado congelado (frozen)
    API.lean                     API pública unificada
  Platform/                      Contratos de plataforma (Sim, RPi5)
  Testing/                       Harness de testes, builder de estado
tests/                           Suítes de teste executáveis
docs/                            Documentação do projeto
```

## Fluxo de trabalho de contribuição

1. **Fork e branch**: crie um fork e trabalhe em uma branch descritiva
   (ex: `fix/scheduler-priority-overflow`, `feat/vspace-guard-pages`)
2. **Implemente**: faça suas alterações seguindo as convenções acima
3. **Prove**: se sua alteração afeta transições, atualize ou adicione os
   teoremas de preservação correspondentes
4. **Teste**: execute `./scripts/test_smoke.sh` (mínimo) ou
   `./scripts/test_full.sh` (para alterações em teoremas)
5. **Documente**: atualize a documentação relevante no mesmo PR
6. **Envie**: abra um pull request com escopo claro e workstream identificado

## Reportando vulnerabilidades

Se você descobrir uma possível vulnerabilidade de segurança durante a revisão
de código ou testes, por favor reporte-a diretamente aos mantenedores antes de
divulgá-la publicamente. Consulte a seção de relatório de vulnerabilidades no
[README](../../../README.md) para detalhes completos.

## Obtendo ajuda

- **Manual completo**: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)
- **Especificação do projeto**: [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
- **Histórico de workstreams**: [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)
- **Issues**: [GitHub Issues](https://github.com/hatter6822/seLe4n/issues)
