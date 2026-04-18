<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Безопасность" /></a>
  <img src="https://img.shields.io/badge/version-0.29.14-blue" alt="Версия" />
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
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## Что такое seLe4n?

seLe4n — это микроядро, построенное с нуля на языке Lean 4. Каждый переход
ядра представляет собой исполняемую чистую функцию. Каждый инвариант
машинно-проверяется средствами системы типов Lean — ноль `sorry`, ноль `axiom`.
Вся поверхность доказательств компилируется в нативный код без каких-либо
допущений (admitted proofs).

Проект сохраняет модель безопасности на основе мандатов (capability-based
security model) от seL4, вводя при этом архитектурные улучшения, ставшие
возможными благодаря системе доказательств Lean 4:

### Планирование и гарантии реального времени

- **Композиционные объекты производительности** — процессорное время является полноценным объектом ядра. `SchedContext` инкапсулирует бюджет, период, приоритет, дедлайн и домен в переиспользуемый контекст планирования, к которому потоки привязываются через мандаты. Планировщик CBS (Constant Bandwidth Server) обеспечивает доказанную изоляцию полосы пропускания (теорема `cbs_bandwidth_bounded`)
- **Пассивные серверы** — бездействующие серверы заимствуют `SchedContext` клиента во время IPC, потребляя ноль CPU в неактивном состоянии. Инвариант `donationChainAcyclic` предотвращает циклические цепочки донации
- **Таймауты IPC на основе бюджета** — блокирующие операции ограничены бюджетом вызывающей стороны. По истечении бюджета потоки извлекаются из очереди endpoint и ставятся в очередь заново
- **Протокол наследования приоритетов** — транзитивное распространение приоритета с машинно-проверяемым отсутствием взаимоблокировок (`blockingChainAcyclic`) и ограниченной глубиной цепочки. Предотвращает неограниченную инверсию приоритетов
- **Теорема ограниченной латентности** — машинно-проверяемая граница WCRT: `WCRT = D × L_max + N × (B + P)`, доказанная в 7 модулях liveness, охватывающих монотонность бюджета, тайминг пополнения, семантику yield, исчерпание полосы и ротацию доменов

### Структуры данных и IPC

- **O(1) хеш-операции на критических путях** — все хранилища объектов, очереди планировщика, слоты CNode, отображения VSpace и очереди IPC используют формально верифицированные хеш-таблицы Robin Hood с инвариантами `distCorrect`, `noDupKeys` и `probeChainDominant`
- **Интрузивная двойная очередь IPC** — обратные указатели (back-pointers) на каждый поток для O(1) постановки, извлечения и удаления из середины очереди
- **Дерево вывода мандатов со стабильными узлами** — индексы `childMap` + `parentMap` для O(1) передачи слотов, отзыва и обхода потомков

### Безопасность и верификация

- **N-доменный информационный поток** — параметризованные политики потоков, обобщающие бинарное разделение seL4. Граница принудительного применения (enforcement) с 30 точками входа и доказательствами невмешательства по каждой операции (индуктивный тип `NonInterferenceStep` с 32 конструкторами)
- **Составной слой доказательств** — `proofLayerInvariantBundle` объединяет 10 инвариантов подсистем (планировщик, мандаты, IPC, жизненный цикл, сервисы, VSpace, межсистемные, TLB и расширения CBS) в единое обязательство верхнего уровня, проверяемое от загрузки до всех операций
- **Двухфазная архитектура состояния** — фаза построения с свидетелями инвариантов переходит в замороженное неизменяемое представление с доказанной эквивалентностью поиска. 20 замороженных операций зеркалируют активный API
- **Полный набор операций** — все операции seL4 реализованы с сохранением инвариантов, включая 5 отложенных операций (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Оркестрация сервисов** — управление жизненным циклом компонентов на уровне ядра с графами зависимостей и доказанной ацикличностью (расширение seLe4n, отсутствует в seL4)

## Текущее состояние

<!-- Метрики синхронизированы из docs/codebase_map.json → секция readme_sync.
     Регенерация: ./scripts/generate_codebase_map.py --pretty
     Источник истины: docs/codebase_map.json (readme_sync) -->

| Атрибут | Значение |
|---------|----------|
| **Версия** | `0.25.5` |
| **Тулчейн Lean** | `v4.28.0` |
| **Продуктовый код (Lean LoC)** | 83 286 строк в 132 файлах |
| **Тестовый код (Lean LoC)** | 10 564 строк в 15 тест-сьютах |
| **Доказанные декларации** | 2 447 деклараций theorem/lemma (ноль sorry/axiom) |
| **Целевое оборудование** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Последний аудит** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — полный аудит ядра Lean + Rust (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
| **Карта кодовой базы** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машиночитаемая опись деклараций |

Метрики формируются скриптом `./scripts/generate_codebase_map.py` и хранятся
в [`docs/codebase_map.json`](../../../docs/codebase_map.json) в секции
`readme_sync`. Обновление всей документации выполняется через
`./scripts/report_current_state.py` в качестве перекрёстной проверки.

## Быстрый старт

```bash
./scripts/setup_lean_env.sh   # установка тулчейна Lean
lake build                     # компиляция всех модулей
lake exe sele4n                # запуск трассировочного стенда (trace harness)
./scripts/test_smoke.sh        # валидация (гигиена + сборка + трассировка + негативные состояния + синхронизация документации)
```

## Документация

| Начните здесь | Затем |
|---------------|-------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — рабочий процесс, валидация, чек-лист для PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — спецификация и этапы |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — полное руководство | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — справочная семантика seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машиночитаемая опись | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — история рабочих потоков и дорожная карта |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — механика внесения вклада | [`CHANGELOG.md`](../../../CHANGELOG.md) — история версий |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) является источником
истины для метрик проекта. Он питает [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
и автоматически обновляется при merge через CI. Регенерация:
`./scripts/generate_codebase_map.py --pretty`.

## Команды валидации

```bash
./scripts/test_fast.sh      # Уровень 0+1: гигиена + сборка
./scripts/test_smoke.sh     # + Уровень 2: трассировка + негативные состояния + синхронизация документации
./scripts/test_full.sh      # + Уровень 3: якоря поверхности инвариантов + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Уровень 4: ночной тест детерминизма
```

Перед любым PR выполните как минимум `test_smoke.sh`. Запускайте `test_full.sh`
при изменении теорем, инвариантов или якорей документации.

## Архитектура

seLe4n организован как набор послойных контрактов, каждый из которых содержит
исполняемые переходы и машинно-проверяемые доказательства сохранения инвариантов:

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

## Структура исходного кода

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

Каждая подсистема следует разделению **Operations/Invariant**: переходы в
`Operations.lean`, доказательства — в `Invariant.lean`. Объединённый
`apiInvariantBundle` агрегирует инварианты всех подсистем в единое обязательство
доказательства. Полная поимённая опись находится в [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Сравнение с seL4

| Свойство | seL4 | seLe4n |
|----------|------|--------|
| **Планирование** | Спорадический сервер на C (MCS) | CBS с машинно-проверяемой теоремой `cbs_bandwidth_bounded`; `SchedContext` как объект ядра, управляемый мандатами |
| **Пассивные серверы** | Донация SchedContext через C | Верифицированная донация с инвариантом `donationChainAcyclic` |
| **IPC** | Очередь endpoint на односвязном списке | Интрузивная двойная очередь с O(1) удалением из середины; таймауты на основе бюджета |
| **Информационный поток** | Бинарное разделение high/low | N-доменная настраиваемая политика с границей enforcement из 30 точек и доказательствами невмешательства по операциям |
| **Наследование приоритетов** | PIP на C (ветка MCS) | Машинно-проверяемый транзитивный PIP с отсутствием взаимоблокировок и параметрической границей WCRT |
| **Ограниченная латентность** | Нет формальной границы WCRT | `WCRT = D × L_max + N × (B + P)`, доказано в 7 модулях liveness |
| **Хранилища объектов** | Связные списки и массивы | Верифицированные хеш-таблицы Robin Hood (`RHTable`/`RHSet`) с O(1) критическими путями |
| **Управление сервисами** | Отсутствует в ядре | Полноценная оркестрация с графом зависимостей и доказательствами ацикличности |
| **Доказательства** | Isabelle/HOL, post-hoc | Type-checker Lean 4, совмещены с переходами (2 447 теорем, ноль sorry/axiom) |
| **Платформа** | HAL уровня C | Typeclass `PlatformBinding` с типизированными контрактами границ |

## Дальнейшие шаги

Все рабочие потоки программного уровня (WS-B по WS-AB) завершены. Полная
история находится в [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

### Завершённые рабочие потоки

| Рабочий поток | Охват | Версия |
|---------------|-------|--------|
| **WS-AB** | Отложенные операции и Liveness — suspend/resume, setPriority/setMCPriority, setIPCBuffer, Протокол наследования приоритетов, Теорема ограниченной латентности (6 фаз, 90 задач) | v0.24.0–v0.25.5 |
| **WS-Z** | Композиционные объекты производительности — `SchedContext` как 7-й объект ядра, движок бюджетов CBS, очередь пополнения, донация пассивных серверов, endpoint с таймаутами (10 фаз, 213 задач) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | Основные подсистемы ядра, хеш-таблицы Robin Hood, radix-деревья, замороженное состояние, информационный поток, оркестрация сервисов, контракты платформы | v0.9.0–v0.22.x |

Подробные планы: [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### Следующий крупный этап

**Привязка к оборудованию Raspberry Pi 5** — обход таблицы страниц ARMv8,
маршрутизация прерываний GIC-400, последовательность загрузки. Предыдущие аудиты
и закрытия этапов архивированы в [`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Этот документ является переводом [README на английском языке](../../../README.md).
> В случае расхождений приоритет имеет английский оригинал.
