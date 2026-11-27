<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Безопасность" /></a>
  <img src="https://img.shields.io/badge/version-0.37.64-blue" alt="Версия" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Лицензия" /></a>
</p>

<p align="center">
  Микроядро, написанное на Lean 4 с машинно-проверяемыми доказательствами,
  вдохновлённое архитектурой <a href="https://sel4.systems">seL4</a>.
  Первая аппаратная платформа: <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Создано с заботой при участии:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>ОТНОСИТЕСЬ К ЭТОМУ ЯДРУ СООТВЕТСТВЕННО</strong>
  </div>
</p>

<p align="center">
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  **Русский** ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## Что такое seLe4n?

seLe4n — микроядро, построенное с нуля на Lean 4. Каждый переход ядра — это
исполняемая чистая функция, и каждый инвариант проверяется ядром Lean:
производственная поверхность доказательств содержит ноль `sorry` и ноль
`axiom`. Тот же код на Lean компилируется в машинный код и вместе с небольшим
аппаратным слоем на Rust компонуется в образ ядра, который загружается на
целевой платформе.

Проект сохраняет модель безопасности seL4 на основе capability и всё в большей
степени — видимый пользователю ABI seL4, используя Lean, чтобы доказать о нём
больше и укрепить его там, где seL4 оставляет пробел. Полная спецификация —
[`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md); пункты ниже ссылаются
на неё.

### ABI seL4

- **Системные вызовы seL4-MCS** — одиннадцать вызовов MCS (`Call` … `Yield`),
  пронумерованные в `x7` так же, как в seL4; операция выбирается по вызову,
  типу вызываемой capability и метке сообщения (`Syscall.selectOperation`),
  как в seL4
- **Полезные данные ошибок и отказов seL4** — `LookupFault`, кадр ошибки в
  порядке регистров сообщений seL4, отказы capability на стороне приёма,
  состояние `Restart`, аргументы-capability, передаваемые как дополнительные
  capability, и guard внутри capability с единственным `resolveAddressBits`
- Остальная работа над ABI seL4 (оставшиеся вызовы, отказы по тайм-ауту,
  права для каждого вызова, состояние Running на ядро) — активный поток работ
  WS-SX; его строки в
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Планирование и реальное время

- **Контексты планирования как capability** — процессорное время является
  объектом ядра. `SchedContext` хранит бюджет, период и пополнения seL4-MCS,
  настраивается через полномочие `SchedControl` ядра процессора и
  привязывается к потокам через capability; его инварианты
  (`budgetWithinBounds`, `refillsConserved`) входят в верхний набор.
  Изоляция полосы пропускания — это `refill_window_bound`: контекст не
  выполняется дольше своего бюджета ни в одном окне длиной в период — гарантия
  скользящего окна seL4-MCS. Иерархический планировщик с постоянной полосой
  пропускания и корнем EDF, добавляющий обратное утверждение (допущенный
  сервер получает свой бюджет в каждом окне), — запланированный поток WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Пассивные серверы** — сервер работает на контексте планирования, который
  ему передаёт клиент во время IPC; `donationChainAcyclic` исключает
  циклические передачи
- **Тайм-ауты IPC по бюджету** — заблокированный поток с исчерпанным бюджетом
  удаляется из очереди своего endpoint (`timeoutThread`)
- **Наследование приоритетов** — транзитивное распространение с машинно
  проверенным отсутствием циклов блокировки (`blockingAcyclic`) и теоремой об
  ограниченной инверсии (`pip_bounded_inversion`)
- **Ограниченная задержка** — параметрическая граница времени отклика в худшем
  случае, `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, с вариантом на ядро), доказанная над
  модулями `SeLe4n/Kernel/Scheduler/Liveness/`

### Объекты ядра и память

- **Объекты, вырезаемые из untyped-памяти** — retype вырезает объект из
  области untyped-capability, а сброс untyped устроен как в seL4. Перенос ячеек
  каждого вырезанного объекта в собственную память его untyped — активный
  поток работ WS-UC
- **Вход в ядро ничего не выделяет** — скомпилированные входы системных
  вызовов, отказов и прерываний не делают выделений в куче; вырезание при
  retype выделяет только ячейки нового объекта. Проверка кучи в QEMU
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) измеряет каждый вход
  на загруженном образе и падает при любом другом значении
- **Структуры данных** — хранилище объектов и отображения VSpace — это
  проверенные хеш-таблицы Robin Hood (`RHTable`, с `distCorrect`, `noDupKeys` и
  `probeChainDominant`); CNode — плоский массив из `2^radix` слотов, как в
  seL4; очереди выполнения, очереди endpoint и уведомлений и ожидающие ответа
  связаны через TCB, каждая с абстрактной призрачной очередью, согласие которой
  со ссылками доказано
- **Дерево производных capability, связанное через слоты** — каждый слот
  хранит ссылки на родителя, первого потомка и соседа (база отображений seL4),
  согласие которых с деревом доказано; удаление, отзыв (цикл `cteRevoke` seL4)
  и перенос слота идут по ссылкам
- **VSpace** — таблицы страниц ARMv8 с W^X для каждого кадра и проверками типа
  памяти, отвергающими некэшируемый псевдоним ОЗУ

### Безопасность и верификация

- **Информационные потоки с N доменами** — параметризованные политики
  потоков, обобщающие двухдоменное разбиение seL4; граница применения, длина
  которой закреплена `enforcementBoundaryExtended_count` (и
  `enforcementBoundaryPerCore_count` для границы на ядро); теорема
  невмешательства для каждого конструктора `NonInterferenceStep`; и
  ограниченный журнал аудита деклассификации с отказом по умолчанию, читаемый
  через capability `auditTrail`
- **Составной слой доказательств** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) объединяет набор инвариантов
  каждой подсистемы (планировщик, capability, IPC и его связь с
  планировщиком, жизненный цикл, реестр сервисов, VSpace, межподсистемные,
  когерентность TLB и кэша инструкций, shootdown TLB, журнал аудита
  деклассификации и согласие каждой связанной структуры с её призраком) в одно
  обязательство, сохраняемое от загрузки через каждую операцию
- **Многоядерность** — четыре ядра с планированием на ядро, межъядерными IPC
  и пробуждением, shootdown TLB; поток завершения SMP (WS-SM) в работе
- **Трёхфазное состояние** — фаза построения со свидетелями инвариантов
  замораживается в неизменяемое представление с доказанной эквивалентностью
  поиска; замороженные операции покрывают вызовы из списка
  `frozenOpCoverage`, закреплённые `frozenOpCoverage_count`
- **Реестр сервисов** — расширение seLe4n, которого нет в seL4: сервисы
  регистрируются и ищутся через capability `serviceRegistry` и записываются в
  обслуживающий endpoint; политика зависимостей, как и в seL4, остаётся
  менеджеру сервисов в пространстве пользователя

## Текущее состояние

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Атрибут | Значение |
|---------|----------|
| **Версия** | `0.37.64` |
| **Тулчейн Lean** | `v4.28.0` |
| **Продуктовый код (Lean LoC)** | 699 838 строк в 710 файлах |
| **Тестовый код (Lean LoC)** | 91 919 строк в 71 тест-сьюте |
| **Доказанные декларации** | 27 055 деклараций theorem/lemma (ноль sorry/axiom) |
| **Крейты Rust** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (обёртки пространства пользователя), `sele4n-hal` (аппаратный слой ядра) и хостовый тест `sele4n-lean-boundary` |
| **Целевое оборудование** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Линии загрузки** | Каждая линия QEMU сначала загружает образ Raspberry Pi 5 на машине `raspi5b` из [rpi5_machine](https://github.com/hatter6822/rpi5_machine), затем образ `virt` на машине `virt` QEMU |
| **Потоки работ** | Состояние каждого открытого потока: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); индекс и реестр долга: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Аудиты** | [`docs/audits/`](../../../docs/audits/README.md) — артефакты активного аудита; предыдущие аудиты в архиве |
| **Карта кодовой базы** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машиночитаемый перечень деклараций |

Метрики выводятся из кода скриптом `./scripts/generate_codebase_map.py` и
хранятся в [`docs/codebase_map.json`](../../../docs/codebase_map.json) под ключом
`readme_sync`. Обновляйте всю документацию вместе через
`./scripts/sync_documentation_metrics.sh` (только проверка: `--check`).

## Быстрый старт

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` собирает только то, что достижимо из `Main.lean` и тестовых
исполняемых файлов; перед коммитом файла `.lean` соберите его модуль по имени
(`lake build <Module.Path>`). Полный процесс описан в
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), а правила для всех участников —
в [`CLAUDE.md`](../../../CLAUDE.md).

## Документация

| Начните здесь | Затем |
|---------------|-------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — процесс, проверка, чек-лист PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — спецификация и вехи |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — полное руководство | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — эталонная семантика seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машиночитаемый перечень | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — каждый отложенный пункт с ответственным |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — порядок участия | [`CHANGELOG.md`](../../../CHANGELOG.md) — история версий |

## Команды проверки

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

Перед любым PR запускайте как минимум `test_smoke.sh`, а `test_full.sh` — при
изменении теорем, инвариантов или якорей Tier 3. Уровень останавливается на
первой неудачной проверке; передайте `--continue`, чтобы собрать все ошибки за
один проход.

После любого изменения в `rust/` запускайте **обе** линии Rust. Они покрывают
непересекающиеся половины одного крейта: на хосте каждый блок
`#[cfg(target_arch = "aarch64")]` удаляется до того, как его увидят rustc или
clippy, поэтому хостовая линия не видит условных блоков, мест `asm!` и
исходников `.S`, составляющих большую часть HAL. Кросс-линия собирает
`sele4n-hal` для `aarch64-unknown-none-softfloat` в обоих профилях, проверяет,
что ассемблерные исходники действительно собраны, прогоняет линтер по
кросс-цели и дизассемблирует release-объекты, доказывая, что они не используют
регистры FP/SIMD. Линии QEMU при первом запуске собирают rpi5_machine на
коммите, закреплённом в `scripts/setup_rpi5_machine.sh`; линия без нужного
условия сообщает NOT RUN, а не успех. Полный список — в
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Архитектура

seLe4n организован как многоуровневые контракты, каждый с исполняемыми
переходами и машинно проверенными доказательствами сохранения инвариантов:

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

## Структура исходного кода

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

Каждая подсистема следует **разделению Operations/Invariant**: переходы в
`Operations.lean`, доказательства в `Invariant.lean`. Единый
`apiInvariantBundle` собирает все инварианты подсистем в одно обязательство
доказательства. Карта подсистем — [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
§5; полный перечень по файлам — в
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Сравнение с seL4

| Характеристика | seL4 | seLe4n |
|----------------|------|--------|
| **ABI системных вызовов** | Вызовы MCS, метки вызовов, данные ошибок и отказов | То же: одиннадцать вызовов seL4-MCS с их нумерацией, вызовы, выбираемые по метке, и данные ошибок seL4; оставшиеся вызовы — строки WS-SX |
| **Планирование** | Контексты планирования MCS с пополнениями спорадического сервера | Тот же механизм пополнений с доказанными инвариантом сохранения и границей в один бюджет на окно (`refill_window_bound`); запланирован иерархический CBS с корнем EDF (WS-CB) |
| **Пассивные серверы** | Передача SchedContext | Проверенная передача с инвариантом `donationChainAcyclic` |
| **IPC** | Одна очередь на endpoint, связанная через TCB | Очередь отправки и очередь приёма на endpoint, обе связаны через TCB с удалением за O(1) из любой позиции; тайм-ауты по бюджету |
| **Информационные потоки** | Бинарное разбиение high/low | Настраиваемая политика с N доменами, граница применения, закреплённая `enforcementBoundaryExtended_count`, теорема невмешательства для каждого шага и журнал аудита под управлением capability для каждой разрешённой деклассификации |
| **Наследование приоритетов** | Нет в ядре | Машинно проверенное транзитивное PIP без циклов блокировки, с теоремой об ограниченной инверсии |
| **Ограниченная задержка** | Нет формальной границы WCRT | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, доказано над модулями живости |
| **Хранилище объектов** | Объекты по физическим адресам | Проверенные хеш-таблицы Robin Hood (`RHTable`/`RHSet`); CNode — плоские массивы слотов, как в seL4 |
| **Отображение памяти** | W^X ядром не обеспечивается | W^X для каждого кадра как инвариант; проверки типа памяти отвергают некэшируемый псевдоним ОЗУ |
| **Управление сервисами** | Вне ядра | Реестр сервисов под управлением capability на endpoint; политика зависимостей в пространстве пользователя |
| **Доказательства** | Isabelle/HOL, над кодом на C через уточнение | Lean 4, рядом с исполняемыми переходами; ноль sorry/axiom (количество в таблице выше) |
| **Платформа** | HAL на уровне C | Класс типов `PlatformBinding` с типизированными контрактами границы и HAL на Rust |

## Лицензия и атрибуция сторонних компонентов

Сам seLe4n распространяется по лицензии GNU General Public License v3.0 или
более поздней версии (GPLv3+); полный текст — в [`LICENSE`](../../../LICENSE).
Сторонние зависимости сборки (`cc`, `find-msvc-tools`, `shlex`, все под
двойной лицензией `MIT OR Apache-2.0`) используются на условиях MIT; их
исходные уведомления об авторских правах и разрешениях воспроизведены
дословно в [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md). В
двоичном файле ядра нет стороннего кода, связываемого во время выполнения, —
HAL является `#![no_std]` и использует только `core::*`.

---

> Этот документ является переводом [README на английском языке](../../../README.md).
> В случае расхождений приоритет имеет английский оригинал.
