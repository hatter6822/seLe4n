<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.21.5-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Микроядро (microkernel), написанное на Lean 4 с машинно-проверяемыми доказательствами,
  вдохновлённое архитектурой <a href="https://sel4.systems">seL4</a>.
  Первая аппаратная платформа: <strong>Raspberry Pi 5</strong>.
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | **Русский** | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## Что такое seLe4n?

seLe4n — это микроядро, построенное с нуля на языке Lean 4. Каждый переход
ядра (kernel transition) представляет собой исполняемую чистую функцию. Каждый
инвариант (invariant) машинно-проверяется средствами системы типов Lean — ноль
`sorry`, ноль `axiom`. Вся поверхность доказательств компилируется в нативный
код без каких-либо допущений (admitted proofs).

Проект использует модель безопасности на основе мандатов (capability-based
security model), при этом вводя ряд архитектурных нововведений по сравнению
с другими микроядрами:

- **O(1) хеш-операции на критических путях ядра** — все хранилища объектов, очереди планировщика, слоты CNode, отображения VSpace и очереди IPC используют формально верифицированные `RHTable`/`RHSet` (Robin Hood хеш-таблица с машинно-проверяемыми инвариантами, ноль `Std.HashMap`/`Std.HashSet` в состоянии ядра)
- **Слой оркестрации сервисов (Service Orchestration)** для управления жизненным циклом компонентов и зависимостями с детерминированной семантикой частичных отказов
- **Дерево вывода мандатов (Capability Derivation Tree)** со стабильными узлами, индексами `childMap` + `parentMap` на основе RHTable для O(1) операций передачи слотов, отзыва, поиска родителей и обхода потомков
- **Интрузивная двойная очередь IPC (Dual-Queue IPC)** с указателями `queuePrev`/`queuePPrev`/`queueNext` для каждого потока, обеспечивающая O(1) постановку, извлечение и удаление из середины очереди
- **Параметризованная N-доменная модель информационных потоков (Information Flow)** с настраиваемыми политиками, обобщающая традиционные метки конфиденциальности и целостности (выходя за рамки бинарного разделения seL4)
- **Планировщик EDF + приоритеты** с семантикой вывода из очереди при диспетчеризации, регистровым контекстом на уровне TCB с встроенным переключением контекста, приоритетно-группированной очередью `RunQueue` и доменным разделением

## Текущее состояние

| Атрибут | Значение |
|---------|----------|
| **Версия** | `0.21.5` |
| **Тулчейн Lean** | `v4.28.0` |
| **Продуктовый код (Lean LoC)** | 64 039 строк в 101 файлах |
| **Тестовый код (Lean LoC)** | 8 318 строк в 10 тест-сьютах (test suites) |
| **Доказанные декларации** | 1 901 деклараций theorem/lemma (ноль sorry/axiom) |
| **Целевое оборудование** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Последний аудит** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — полный аудит ядра и Rust-кодовой базы перед релизом |
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

## Путь освоения

Начинаете работу с проектом? Рекомендуемый порядок изучения:

1. **Этот README** — идентификация проекта, архитектура и структура исходников
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — ежедневный рабочий процесс, цикл валидации, чек-лист для PR
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — полное руководство (глубокий разбор архитектуры, доказательства, путь к оборудованию)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машиночитаемая опись модулей и деклараций

Для планирования и истории рабочих потоков (workstreams) см. [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

## Документация проекта

| Документ | Назначение |
|----------|------------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | Спецификация проекта и этапы (milestones) |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | Справочная семантика seL4 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | Ежедневный рабочий процесс, цикл валидации, чек-лист для PR |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | Уровневые тестовые шлюзы (tiered test gates) и контракт CI |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | Полная история рабочих потоков, дорожная карта и индекс аудитов |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | Полное руководство (архитектура, проектирование, доказательства, путь к оборудованию) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | Машиночитаемая опись кодовой базы (синхронизирована с README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | Механика внесения вклада и требования к PR |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | История версий |

## Команды валидации

```bash
./scripts/test_fast.sh      # Уровень 0 + 1 (гигиена + сборка, семантическая глубина доказательств L-08)
./scripts/test_smoke.sh     # + Уровень 2 (трассировка + негативные состояния + синхронизация документации)
./scripts/test_full.sh      # + Уровень 3 (якоря поверхности инвариантов + проверка корректности Lean #check)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Уровень 4 (ночной тест детерминизма)
```

Перед любым PR выполните как минимум `test_smoke.sh`. Запускайте `test_full.sh`
при изменении теорем, инвариантов или якорей документации.

## Архитектура

seLe4n организован как набор послойных контрактов (layered contracts), каждый
из которых содержит исполняемые переходы и машинно-проверяемые доказательства
сохранения инвариантов:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Планировщик │   Мандаты   │    IPC     │ Жизненный │  Сервисы (расш)│
│  RunQueue    │  CSpace/CDT │  DualQueue │  цикл     │  Оркестрация   │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│     Информационные потоки (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Архитектура  (VSpace, VSpaceBackend, Adapter, Assumptions)       │
├──────────────────────────────────────────────────────────────────────┤
│                     Модель  (Object, State, CDT)                     │
├──────────────────────────────────────────────────────────────────────┤
│             Основания  (Prelude, Machine, MachineConfig)             │
├──────────────────────────────────────────────────────────────────────┤
│          Платформа  (Contract, Sim, RPi5)  ← привязки H3-prep        │
└──────────────────────────────────────────────────────────────────────┘
```

Каждая подсистема ядра следует разделению **Operations/Invariant**: переходы
в файле `Operations.lean`, доказательства — в `Invariant.lean`. Объединённый
`apiInvariantBundle` агрегирует инварианты всех подсистем в единое обязательство
доказательства (proof obligation).

## Сравнение с seL4

| Свойство | seL4 | seLe4n |
|----------|------|--------|
| **Механизм IPC** | Однонаправленная очередь на основе связного списка | Интрузивная двойная очередь с указателями `queuePPrev` для O(1) удаления из середины |
| **Информационные потоки** | Бинарное разделение high/low | N-доменная настраиваемая политика (обобщение традиционных меток конфиденциальности и целостности) |
| **Управление сервисами** | Отсутствует в ядре | Встроенная оркестрация сервисов с графом зависимостей и обнаружением циклов (DFS) |
| **Вывод мандатов** | CDT на основе связного списка | `childMap` HashMap для O(1) поиска потомков |
| **Планировщик** | Плоская очередь приоритетов | Приоритетно-группированная `RunQueue` с отслеживанием `maxPriority` и EDF |
| **VSpace** | Аппаратные таблицы страниц | `HashMap VAddr (PAddr x PagePermissions)` с контролем W^X |
| **Методология доказательств** | Isabelle/HOL, post-hoc | Lean 4 type-checker, доказательства совмещены с переходами |
| **Абстракция платформы** | HAL уровня C | `PlatformBinding` typeclass с типизированными контрактами границ |

## Дальнейшие шаги

Текущие приоритеты и полная история рабочих потоков описаны в
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md). Краткое изложение:

- **WS-R** — Комплексное устранение замечаний аудита (Comprehensive Audit Remediation): 8 фаз, R1–R8, 111 подзадач. Охватывает все 82 замечания из [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). R1–R7 завершены (v0.18.0–v0.18.6), R8 в ожидании.
- **Привязка к оборудованию Raspberry Pi 5** — обход таблицы страниц ARMv8, маршрутизация прерываний GIC-400, последовательность загрузки (boot sequence).

Все предшествующие рабочие потоки (WS-B по WS-Q) завершены. Предыдущие аудиты
(v0.8.0–v0.9.32), закрытия этапов и унаследованные главы GitBook заархивированы
в [`docs/dev_history/`](../../../docs/dev_history/README.md).

---

> Этот документ является переводом [English README](../../../README.md).
