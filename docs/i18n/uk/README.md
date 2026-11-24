<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Безпека" /></a>
  <img src="https://img.shields.io/badge/version-0.37.43-blue" alt="Версія" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="Ліцензія" /></a>
</p>

<p align="center">
  Мікроядро, написане на Lean 4 з машинно-перевіреними доведеннями,
  натхненне архітектурою <a href="https://sel4.systems">seL4</a>.
  Перша апаратна платформа: <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    Створено з турботою за участі:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>СТАВТЕСЯ ДО ЦЬОГО ЯДРА ВІДПОВІДНО</strong>
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
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a> ·
  **Українська**
</p>

---

## Що таке seLe4n?

seLe4n — мікроядро, побудоване з нуля на Lean 4. Кожен перехід ядра — це
виконувана чиста функція, і кожен інваріант перевіряє ядро Lean: виробнича
поверхня доведень містить нуль `sorry` і нуль `axiom`. Той самий код на Lean
компілюється в машинний код і разом із невеликим апаратним шаром на Rust
компонується в образ ядра, який завантажується на цільовій платформі.

Проєкт зберігає модель безпеки seL4 на основі capability і дедалі більше —
видимий користувачу ABI seL4, використовуючи Lean, щоб довести про нього
більше та посилити його там, де seL4 залишає прогалину. Повна специфікація —
[`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md); пункти нижче
посилаються на неї.

### ABI seL4

- **Системні виклики seL4-MCS** — одинадцять викликів MCS (`Call` … `Yield`),
  пронумеровані в `x7` так само, як у seL4; операція обирається за викликом,
  типом викликаної capability та міткою повідомлення
  (`Syscall.selectOperation`), як у seL4
- **Корисні дані помилок і збоїв seL4** — `LookupFault`, кадр помилки в
  порядку регістрів повідомлень seL4, збої capability на боці приймання, стан
  `Restart`, аргументи-capability, що передаються як додаткові capability, і
  guard усередині capability з єдиним `resolveAddressBits`
- Решта роботи над ABI seL4 (решта викликів, збої за тайм-аутом, права для
  кожного виклику, стан Running на ядро) — активний потік робіт WS-SX; його
  рядки в
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### Планування та реальний час

- **Контексти планування як capability** — процесорний час є об'єктом ядра.
  `SchedContext` зберігає бюджет, період і поповнення seL4-MCS,
  налаштовується через повноваження `SchedControl` ядра процесора та
  прив'язується до потоків через capability; його інваріанти
  (`budgetWithinBounds`, `refillsConserved`) входять до верхнього набору.
  Ізоляція смуги пропускання — це `refill_window_bound`: контекст не
  виконується довше за свій бюджет у жодному вікні завдовжки в період —
  гарантія ковзного вікна seL4-MCS. Ієрархічний планувальник зі сталою смугою
  пропускання та коренем EDF, що додає обернене твердження (допущений сервер
  отримує свій бюджет у кожному вікні), — запланований потік WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **Пасивні сервери** — сервер працює на контексті планування, який йому
  передає клієнт під час IPC; `donationChainAcyclic` виключає циклічні
  передачі
- **Тайм-аути IPC за бюджетом** — заблокований потік із вичерпаним бюджетом
  видаляється з черги свого endpoint (`timeoutThread`)
- **Успадкування пріоритетів** — транзитивне поширення з машинно перевіреною
  відсутністю циклів блокування (`blockingAcyclic`) і теоремою про обмежену
  інверсію (`pip_bounded_inversion`)
- **Обмежена затримка** — параметрична межа часу відгуку в найгіршому
  випадку, `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, з варіантом на ядро), доведена над
  модулями `SeLe4n/Kernel/Scheduler/Liveness/`

### Об'єкти ядра та пам'ять

- **Об'єкти, вирізані з untyped-пам'яті** — retype вирізає об'єкт з області
  untyped-capability, а скидання untyped влаштоване як у seL4. Перенесення
  комірок кожного вирізаного об'єкта до власної пам'яті його untyped —
  активний потік робіт WS-UC
- **Вхід у ядро нічого не виділяє** — скомпільовані входи системних викликів,
  збоїв і переривань не роблять виділень у купі; вирізання під час retype
  виділяє лише комірки нового об'єкта. Перевірка купи в QEMU
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) вимірює кожен вхід на
  завантаженому образі й падає за будь-якого іншого значення
- **Структури даних** — сховище об'єктів і відображення VSpace — це перевірені
  хеш-таблиці Robin Hood (`RHTable`, з `distCorrect`, `noDupKeys` і
  `probeChainDominant`); CNode — плаский масив із `2^radix` слотів, як у seL4;
  черги виконання, черги endpoint і сповіщень та ті, хто чекає на відповідь,
  зв'язані через TCB, кожна з абстрактною примарною чергою, узгодженість якої
  з посиланнями доведено
- **Дерево похідних capability, зв'язане через слоти** — кожен слот зберігає
  посилання на батька, першого нащадка й сусіда (база відображень seL4),
  узгодженість яких із деревом доведено; видалення, відкликання (цикл
  `cteRevoke` seL4) і перенесення слота йдуть за посиланнями
- **VSpace** — таблиці сторінок ARMv8 з W^X для кожного кадру та перевірками
  типу пам'яті, що відхиляють некешований псевдонім ОЗП

### Безпека та верифікація

- **Інформаційні потоки з N доменами** — параметризовані політики потоків,
  що узагальнюють дводоменний поділ seL4; межа застосування, довжину якої
  закріплює `enforcementBoundaryExtended_count` (і
  `enforcementBoundaryPerCore_count` для межі на ядро); теорема
  невтручання для кожного конструктора `NonInterferenceStep`; і обмежений
  журнал аудиту декласифікації з відмовою за замовчуванням, що читається через
  capability `auditTrail`
- **Складений шар доведень** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) об'єднує набір інваріантів
  кожної підсистеми (планувальник, capability, IPC та його зв'язок із
  планувальником, життєвий цикл, реєстр сервісів, VSpace, міжпідсистемні,
  когерентність TLB і кешу інструкцій, shootdown TLB, журнал аудиту
  декласифікації та узгодженість кожної зв'язаної структури з її примарою) в
  одне зобов'язання, що зберігається від завантаження через кожну операцію
- **Багатоядерність** — чотири ядра з плануванням на ядро, міжядерними IPC і
  пробудженням, shootdown TLB; потік завершення SMP (WS-SM) триває
- **Трифазний стан** — фаза побудови зі свідками інваріантів заморожується в
  незмінне подання з доведеною еквівалентністю пошуку; заморожені операції
  покривають виклики зі списку `frozenOpCoverage`, закріплені
  `frozenOpCoverage_count`
- **Реєстр сервісів** — розширення seLe4n, якого немає в seL4: сервіси
  реєструються й шукаються через capability `serviceRegistry` і записуються в
  обслуговуючий endpoint; політика залежностей, як і в seL4, лишається
  менеджеру сервісів у просторі користувача

## Поточний стан

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| Атрибут | Значення |
|---------|----------|
| **Версія** | `0.37.43` |
| **Тулчейн Lean** | `v4.28.0` |
| **Продуктовий код (Lean LoC)** | 683 255 рядків у 703 файлах |
| **Тестовий код (Lean LoC)** | 92 060 рядків у 71 тест-сьюті |
| **Доведені декларації** | 26 211 декларацій theorem/lemma (нуль sorry/axiom) |
| **Крейти Rust** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (обгортки простору користувача), `sele4n-hal` (апаратний шар ядра) і хостовий тест `sele4n-lean-boundary` |
| **Цільове обладнання** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Лінії завантаження** | Кожна лінія QEMU спершу завантажує образ Raspberry Pi 5 на машині `raspi5b` з [rpi5_machine](https://github.com/hatter6822/rpi5_machine), потім образ `virt` на машині `virt` QEMU |
| **Потоки робіт** | Стан кожного відкритого потоку: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); індекс і реєстр боргу: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **Аудити** | [`docs/audits/`](../../../docs/audits/README.md) — артефакти активного аудиту; попередні аудити в архіві |
| **Карта кодової бази** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машинозчитуваний перелік декларацій |

Метрики виводяться з коду скриптом `./scripts/generate_codebase_map.py` і
зберігаються в [`docs/codebase_map.json`](../../../docs/codebase_map.json) під ключем
`readme_sync`. Оновлюйте всю документацію разом через
`./scripts/sync_documentation_metrics.sh` (лише перевірка: `--check`).

## Швидкий старт

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` збирає лише те, що досяжне з `Main.lean` і тестових виконуваних
файлів; перед комітом файлу `.lean` зберіть його модуль за іменем
(`lake build <Module.Path>`). Повний процес описано в
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md), а правила для всіх учасників —
у [`CLAUDE.md`](../../../CLAUDE.md).

## Документація

| Почніть тут | Далі |
|-------------|------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — процес, перевірка, чек-лист PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — специфікація та віхи |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — повний посібник | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — еталонна семантика seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — машинозчитуваний перелік | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — кожен відкладений пункт із відповідальним |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — порядок участі | [`CHANGELOG.md`](../../../CHANGELOG.md) — історія версій |

## Команди перевірки

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

Перед будь-яким PR запускайте щонайменше `test_smoke.sh`, а `test_full.sh` —
у разі зміни теорем, інваріантів або якорів Tier 3. Рівень зупиняється на
першій невдалій перевірці; передайте `--continue`, щоб зібрати всі помилки за
один прохід.

Після будь-якої зміни в `rust/` запускайте **обидві** лінії Rust. Вони
покривають неперетинні половини одного крейта: на хості кожен блок
`#[cfg(target_arch = "aarch64")]` видаляється до того, як його побачать rustc
або clippy, тож хостова лінія не бачить умовних блоків, місць `asm!` і
вихідних файлів `.S`, що складають більшу частину HAL. Крос-лінія збирає
`sele4n-hal` для `aarch64-unknown-none-softfloat` в обох профілях, перевіряє,
що асемблерні вихідні файли справді зібрано, проганяє лінтер по крос-цілі й
дизасемблює release-об'єкти, доводячи, що вони не використовують регістрів
FP/SIMD. Лінії QEMU під час першого запуску збирають rpi5_machine на коміті,
закріпленому в `scripts/setup_rpi5_machine.sh`; лінія без потрібної умови
повідомляє NOT RUN, а не успіх. Повний список — у
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## Архітектура

seLe4n організовано як багаторівневі контракти, кожен із виконуваними
переходами та машинно перевіреними доведеннями збереження інваріантів:

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

## Структура вихідного коду

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

Кожна підсистема дотримується **розділення Operations/Invariant**: переходи в
`Operations.lean`, доведення в `Invariant.lean`. Єдиний `apiInvariantBundle`
збирає всі інваріанти підсистем в одне зобов'язання доведення. Карта
підсистем — [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5; повний перелік за
файлами — у [`docs/codebase_map.json`](../../../docs/codebase_map.json).

## Порівняння з seL4

| Характеристика | seL4 | seLe4n |
|----------------|------|--------|
| **ABI системних викликів** | Виклики MCS, мітки викликів, дані помилок і збоїв | Те саме: одинадцять викликів seL4-MCS з їхньою нумерацією, виклики, що обираються за міткою, і дані помилок seL4; решта викликів — рядки WS-SX |
| **Планування** | Контексти планування MCS з поповненнями спорадичного сервера | Той самий механізм поповнень із доведеними інваріантом збереження та межею в один бюджет на вікно (`refill_window_bound`); заплановано ієрархічний CBS з коренем EDF (WS-CB) |
| **Пасивні сервери** | Передача SchedContext | Перевірена передача з інваріантом `donationChainAcyclic` |
| **IPC** | Одна черга на endpoint, зв'язана через TCB | Черга надсилання та черга приймання на endpoint, обидві зв'язані через TCB з видаленням за O(1) з будь-якої позиції; тайм-аути за бюджетом |
| **Інформаційні потоки** | Бінарний поділ high/low | Налаштовувана політика з N доменами, межа застосування, закріплена `enforcementBoundaryExtended_count`, теорема невтручання для кожного кроку та журнал аудиту під керуванням capability для кожної дозволеної декласифікації |
| **Успадкування пріоритетів** | Немає в ядрі | Машинно перевірене транзитивне PIP без циклів блокування, з теоремою про обмежену інверсію |
| **Обмежена затримка** | Немає формальної межі WCRT | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, доведено над модулями живості |
| **Сховище об'єктів** | Об'єкти за фізичними адресами | Перевірені хеш-таблиці Robin Hood (`RHTable`/`RHSet`); CNode — пласкі масиви слотів, як у seL4 |
| **Відображення пам'яті** | W^X ядро не забезпечує | W^X для кожного кадру як інваріант; перевірки типу пам'яті відхиляють некешований псевдонім ОЗП |
| **Керування сервісами** | Поза ядром | Реєстр сервісів під керуванням capability на endpoint; політика залежностей у просторі користувача |
| **Доведення** | Isabelle/HOL, над кодом на C через уточнення | Lean 4, поряд із виконуваними переходами; нуль sorry/axiom (кількість у таблиці вище) |
| **Платформа** | HAL на рівні C | Клас типів `PlatformBinding` з типізованими контрактами межі та HAL на Rust |

## Ліцензія та атрибуції третіх сторін

Сам seLe4n ліцензовано за GNU General Public License v3.0 або пізнішою
версією (GPLv3+); повний текст — у [`LICENSE`](../../../LICENSE).
Сторонні залежності збірки (`cc`, `find-msvc-tools`, `shlex`, усі під
подвійною ліцензією `MIT OR Apache-2.0`) використовуються за умовами MIT;
їхні оригінальні повідомлення про авторські права та дозволи відтворено
дослівно в [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md). У
двійковому файлі ядра немає стороннього коду, що компонується під час
виконання, — HAL є `#![no_std]` і використовує лише `core::*`.

---

> Цей документ є перекладом [README англійською мовою](../../../README.md).
> У разі розбіжностей пріоритет має англійський оригінал.
