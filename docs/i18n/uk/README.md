<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Безпека" /></a>
  <img src="https://img.shields.io/badge/version-0.33.72-blue" alt="Версія" />
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

seLe4n — це мікроядро, побудоване з нуля на мові Lean 4. Кожен перехід
ядра є виконуваною чистою функцією. Кожен інваріант машинно перевіряється
засобами системи типів Lean — нуль `sorry`, нуль `axiom`. Уся поверхня
доведень компілюється в нативний код без жодних припущень (admitted
proofs).

Проєкт зберігає модель безпеки на основі мандатів (capability-based
security model) від seL4, водночас впроваджуючи архітектурні покращення,
які стали можливими завдяки системі доведень Lean 4:

### Планування та гарантії реального часу

- **Композиційні об'єкти продуктивності** — процесорний час є повноцінним об'єктом ядра. `SchedContext` інкапсулює бюджет, період, пріоритет, дедлайн і домен у придатний для повторного використання контекст планування, до якого потоки прив'язуються через мандати. Планування CBS (Constant Bandwidth Server) забезпечує доведену ізоляцію смуги пропускання (теорема `cbs_bandwidth_bounded`)
- **Пасивні сервери** — неактивні сервери позичають `SchedContext` клієнта під час IPC, споживаючи нуль CPU, коли не обслуговують запити. Інваріант `donationChainAcyclic` запобігає циклічним ланцюгам передавання (donation)
- **Тайм-аути IPC на основі бюджету** — блокувальні операції обмежені бюджетом викликача. Після вичерпання бюджету потоки вилучаються з черги endpoint і ставляться в чергу повторно
- **Протокол успадкування пріоритетів** — транзитивне поширення пріоритету з машинно перевіреною відсутністю взаємних блокувань (`blockingChainAcyclic`) та обмеженою глибиною ланцюга. Запобігає необмеженій інверсії пріоритетів
- **Теорема обмеженої затримки** — машинно перевірена межа WCRT: `WCRT = D × L_max + N × (B + P)`, доведена у 7 модулях liveness, що охоплюють монотонність бюджету, тайминг поповнення, семантику yield, вичерпання смуги та ротацію доменів

### Структури даних та IPC

- **O(1) хеш-операції на критичних шляхах** — усі сховища об'єктів, черги планувальника, слоти CNode, відображення VSpace та черги IPC використовують формально верифіковані хеш-таблиці Robin Hood з інваріантами `distCorrect`, `noDupKeys` та `probeChainDominant`
- **Інтрузивна подвійна черга IPC** — зворотні вказівники (back-pointers) для кожного потоку для O(1) постановки, вилучення та видалення з середини черги
- **Дерево виведення мандатів зі стабільними вузлами** — індекси `childMap` + `parentMap` для O(1) передачі слотів, відкликання та обходу нащадків

### Безпека та верифікація

- **N-доменний інформаційний потік** — параметризовані політики потоків, що узагальнюють бінарний поділ seL4. Межа примусового застосування (enforcement) з 33 точками входу та доведеннями неінтерференції (non-interference) для кожної операції (індуктивний тип `NonInterferenceStep` з 35 конструкторами)
- **Складений шар доведень** — `proofLayerInvariantBundle` об'єднує 11 інваріантів підсистем (планувальник, мандати, IPC, життєвий цикл, сервіси, VSpace, міжпідсистемні, TLB, розширення CBS та узгодженість очікувачів сповіщень) в єдине зобов'язання верхнього рівня, що перевіряється від завантаження до всіх операцій
- **Трифазна архітектура стану** — фаза побудови зі свідками інваріантів переходить у заморожене незмінне представлення з доведеною еквівалентністю пошуку. 20 заморожених операцій дзеркалять активний API
- **Повний набір операцій** — усі операції seL4 реалізовано зі збереженням інваріантів, включно з 5 відкладеними операціями (suspend/resume, setPriority/setMCPriority, setIPCBuffer)
- **Оркестрація сервісів** — керування життєвим циклом компонентів на рівні ядра з графами залежностей і доведеною ациклічністю (розширення seLe4n, відсутнє в seL4)

## Поточний стан

<!-- Метрики нижче синхронізовано з docs/codebase_map.json → секція readme_sync.
     Регенерація: ./scripts/generate_codebase_map.py --pretty
     Джерело істини: docs/codebase_map.json (readme_sync) -->

| Атрибут | Значення |
|---------|----------|
| **Версія** | `0.33.1` |
| **Тулчейн Lean** | `v4.28.0` |
| **Продуктовий код (Lean LoC)** | 239 252 рядки у 266 файлах |
| **Тестовий код (Lean LoC)** | 48 581 рядок у 67 тест-сьютах |
| **Доведені декларації** | 7 834 декларації theorem/lemma (нуль sorry/axiom) |
| **Крейти Rust** | 4 (`sele4n-types`, `sele4n-abi`, `sele4n-sys`, `sele4n-hal`) у 48 файлах вихідного коду |
| **Цільове обладнання** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **Прив'язка до обладнання** | **H3 ЗАВЕРШЕНО** (WS-AG AG1–AG10): HAL, GIC-400, таймер, таблиці сторінок ARMv8, FFI-міст, завантаження в QEMU |
| **Канонічний аудит** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — комплексний передрелізний аудит 1.0 (202 знахідки; усунуто WS-AK AK1–AK10; заархівовано) |
| **Останній аудит** | [`AUDIT_v0.30.11_COMPREHENSIVE`](../../audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../../audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) — аудит готовності перед 1.0 після завершення WS-AN (наступник заархівованого [`AUDIT_v0.30.6_COMPREHENSIVE`](../../dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md), усунутого WS-AN AN0–AN12). WS-RC R0..R5 ЗАВЕРШЕНО у v0.31.2; WS-RC R6..R14 поглинуто WS-SM згідно з мапою поглинання SM0.Q.1 (див. [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §15`](../../audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)). Активний план робочого потоку: [`SMP_MULTICORE_COMPLETION_PLAN.md`](../../planning/SMP_MULTICORE_COMPLETION_PLAN.md). |
| **Карта кодової бази** | [`docs/codebase_map.json`](../../codebase_map.json) — машинозчитуваний опис декларацій |

Метрики формуються скриптом `./scripts/generate_codebase_map.py` і
зберігаються в [`docs/codebase_map.json`](../../codebase_map.json) у
секції `readme_sync`. Оновлення всієї документації виконується через
`./scripts/report_current_state.py` як перехресну перевірку.

## Швидкий старт

```bash
./scripts/setup_lean_env.sh   # встановлення тулчейна Lean
lake build                     # компіляція всіх модулів
lake exe sele4n                # запуск трасувального стенда
./scripts/test_smoke.sh        # валідація (гігієна + збірка + трасування + негативні стани + синхронізація документації)
```

## Документація

| Почніть тут | Далі |
|-------------|------|
| [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md) — робочий процес, валідація, чек-лист для PR | [`docs/spec/SELE4N_SPEC.md`](../../spec/SELE4N_SPEC.md) — специфікація та етапи |
| [`docs/gitbook/README.md`](../../gitbook/README.md) — повний посібник | [`docs/spec/SEL4_SPEC.md`](../../spec/SEL4_SPEC.md) — довідкова семантика seL4 |
| [`docs/codebase_map.json`](../../codebase_map.json) — машинозчитуваний опис | [`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md) — історія робочих потоків і дорожня карта |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) — механіка внеску | [`CHANGELOG.md`](../../../CHANGELOG.md) — історія версій |

[`docs/codebase_map.json`](../../codebase_map.json) є джерелом істини
для метрик проєкту. Він живить [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
і автоматично оновлюється під час merge через CI. Регенерація:
`./scripts/generate_codebase_map.py --pretty`.

## Команди валідації

```bash
./scripts/test_fast.sh      # Рівень 0+1: гігієна + збірка
./scripts/test_smoke.sh     # + Рівень 2: трасування + негативні стани + синхронізація документації
./scripts/test_full.sh      # + Рівень 3: якорі поверхні інваріантів + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Рівень 4: нічний тест детермінізму
```

Перед будь-яким PR виконайте щонайменше `test_smoke.sh`. Запускайте
`test_full.sh` при зміні теорем, інваріантів чи якорів документації.

## Архітектура

seLe4n організовано як набір пошарових контрактів, кожен з яких містить
виконувані переходи та машинно перевірені доведення збереження
інваріантів:

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
│          Platform  (Contract, Sim, RPi5)  ← H3-prep bindings         │
└──────────────────────────────────────────────────────────────────────┘
```

## Структура вихідного коду

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
tests/                           38 test suites
```

Кожна підсистема слідує розподілу **Operations/Invariant**: переходи в
`Operations.lean`, доведення — в `Invariant.lean`. Об'єднаний
`apiInvariantBundle` агрегує інваріанти всіх підсистем в єдине
зобов'язання доведення. Повний поіменний опис — у
[`docs/codebase_map.json`](../../codebase_map.json).

## Порівняння з seL4

| Властивість | seL4 | seLe4n |
|-------------|------|--------|
| **Планування** | Спорадичний сервер на C (MCS) | CBS з машинно перевіреною теоремою `cbs_bandwidth_bounded`; `SchedContext` як об'єкт ядра, керований мандатами |
| **Пасивні сервери** | Передавання SchedContext через C | Верифіковане передавання (donation) з інваріантом `donationChainAcyclic` |
| **IPC** | Черга endpoint на однозв'язному списку | Інтрузивна подвійна черга з O(1) видаленням із середини; тайм-аути на основі бюджету |
| **Інформаційний потік** | Бінарний поділ high/low | N-доменна конфігурована політика з межею enforcement із 33 точками входу та доведеннями неінтерференції по операціях |
| **Успадкування пріоритетів** | PIP на C (гілка MCS) | Машинно перевірений транзитивний PIP з відсутністю взаємних блокувань і параметричною межею WCRT |
| **Обмежена затримка** | Немає формальної межі WCRT | `WCRT = D × L_max + N × (B + P)`, доведено у 7 модулях liveness |
| **Сховища об'єктів** | Зв'язні списки та масиви | Верифіковані хеш-таблиці Robin Hood (`RHTable`/`RHSet`) з O(1) критичними шляхами |
| **Керування сервісами** | Відсутнє в ядрі | Повноцінна оркестрація з графом залежностей і доведеннями ациклічності |
| **Доведення** | Isabelle/HOL, post-hoc | Type-checker Lean 4, поєднані з переходами (2 725 доведених декларацій, нуль sorry/axiom) |
| **Платформа** | HAL рівня C | Typeclass `PlatformBinding` з типізованими контрактами меж |

## Що далі

Усі робочі потоки програмного рівня (WS-B по WS-AB) та робочий потік
прив'язки до апаратури H3 (WS-AG) завершено. Повна історія — у
[`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md).

### Завершені робочі потоки

| Робочий потік | Охоплення | Версія |
|---------------|-----------|--------|
| **WS-AG** | Усунення результатів аудиту прив'язки до апаратури H3 — 10 фаз (AG1–AG10), 67 підзадач. HAL-крейт, драйвер GIC-400, ARM Generic Timer, таблиці сторінок ARMv8, менеджер ASID, FFI-міст (17 функцій `@[extern]`), моделі винятків/переривань, модель когерентності кешу, тестування інтеграції з QEMU, бар'єри спекуляції, набір апаратної валідації. **ПОРТФЕЛЬ ЗАВЕРШЕНО** | v0.26.0–v0.27.1 |
| **WS-AF** | Усунення результатів комплексного передрелізного аудиту — 6 фаз (AF1–AF6), 49 підзадач. **ПОРТФЕЛЬ ЗАВЕРШЕНО** | v0.25.22–v0.25.27 |
| **WS-AE** | Усунення результатів продуктового аудиту — 6 фаз (AE1–AE6), 53 підзадачі. **ПОРТФЕЛЬ ЗАВЕРШЕНО** | v0.25.15–v0.25.21 |

### Наступний великий етап

**WS-V**: Підтримка багатоядерного SMP, промоція FrozenOps у продукт,
доведення достатності fuel для CDT та формальний міст ланцюга передавання (donation).
Попередні аудити та закриття етапів заархівовано в
[`docs/dev_history/`](../../dev_history/README.md).

## Ліцензія та атрибуції третіх сторін

Сам seLe4n ліцензовано за GNU General Public License v3.0 або пізнішою
версією (GPLv3+); повний текст — у [`LICENSE`](../../../LICENSE).
Залежності Rust, що використовуються лише під час збірки (`cc`,
`find-msvc-tools`, `shlex`, усі під подвійною ліцензією
`MIT OR Apache-2.0`), використовуються за умовами MIT; їхні оригінальні
повідомлення про авторські права та дозволи відтворено дослівно в
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md). У
двійковому файлі ядра, що виконується під час роботи, немає жодного
стороннього коду — HAL є `#![no_std]` і використовує лише `core::*`.

---

> Цей документ є перекладом [README англійською мовою](../../../README.md).
> У разі розбіжностей пріоритет має англійський оригінал.
