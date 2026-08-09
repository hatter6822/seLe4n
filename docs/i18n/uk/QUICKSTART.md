# Швидкий старт seLe4n

Покроковий посібник із налаштування середовища розробки, збірки та
запуску мікроядра seLe4n.

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md) | **Українська**

---

## Передумови

| Компонент | Версія | Призначення |
|-----------|--------|-------------|
| **Git** | ≥ 2.30 | Керування версіями |
| **curl** | будь-яка | Завантаження інсталятора elan |
| **bash** | ≥ 4.0 | Скрипти збірки та тестування |
| **Python 3** | ≥ 3.8 | Генерація `codebase_map.json` та звітів |

Тулчейн Lean (включно з `elan`, `lean` і `lake`) встановлюється
автоматично скриптом налаштування.

## Крок 1. Клонування репозиторію

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## Крок 2. Встановлення тулчейна Lean

Скрипт налаштування завантажує [elan](https://github.com/leanprover/elan) —
менеджер версій Lean — і встановлює версію тулчейна, вказану у файлі
`lean-toolchain` проєкту (наразі Lean v4.28.0).

```bash
./scripts/setup_lean_env.sh
```

Якщо потрібно пропустити встановлення залежностей для тестування
(shellcheck, ripgrep), використайте:

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

Після встановлення активуйте середовище:

```bash
source ~/.elan/env
```

### Перевірка встановлення

```bash
lean --version
# Очікуваний вивід: leanprover/lean4:v4.28.0

lake --version
# Очікуваний вивід: Lake version ... (Lean version 4.28.0)
```

## Крок 3. Збірка проєкту

```bash
lake build
```

Перша збірка завантажує залежності та компілює всі модулі — це може
зайняти кілька хвилин. Наступні інкрементальні збірки значно швидші.

### Збірка окремого модуля

Для перевірки конкретного модуля без повної перезбірки:

```bash
lake build SeLe4n.Kernel.Scheduler.Operations
lake build SeLe4n.Kernel.IPC.Invariant
lake build SeLe4n.Kernel.RobinHood.Core
```

Формат імені модуля: шлях до файлу із заміною `/` на `.` і без
розширення `.lean`.

**Перед комітом будь-якого `.lean` файлу** обов'язково перевірте, що
саме змінений модуль компілюється — цільова збірка `lake build` за
замовчуванням збирає лише модулі, досяжні з `Main.lean` і тестових
виконуваних файлів, тож зламаний модуль поза цим охопленням мовчки
пройде перевірку.

## Крок 4. Запуск трасувального стенда

```bash
lake exe sele4n
```

Ця команда запускає виконуваний трасувальний стенд (trace harness), що
демонструє переходи ядра. Вивід повинен збігатися з очікуваним файлом
фікстури:

```
tests/fixtures/main_trace_smoke.expected
```

## Крок 5. Валідація

### Мінімальна перевірка (перед будь-яким PR)

```bash
./scripts/test_smoke.sh
```

Охоплює:
- **Рівень 0** — гігієна: перевірка відсутності `sorry`/`axiom`,
  цілісність посилань сайту, синтаксичні перевірки
- **Рівень 1** — збірка: `lake build` завершується успішно
- **Рівень 2** — трасування, негативні стани, синхронізація документації

### Повна перевірка (при зміні теорем/інваріантів)

```bash
./scripts/test_full.sh
```

Додатково охоплює:
- **Рівень 3** — якорі поверхні інваріантів, перевірка коректності
  Lean `#check`

### Швидка перевірка (лише гігієна + збірка)

```bash
./scripts/test_fast.sh
```

### Нічний тест

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

## Структура проєкту

```
seLe4n/
├── SeLe4n/                    # Вихідний код ядра (Lean 4)
│   ├── Prelude.lean           # Типізовані ідентифікатори, монада KernelM
│   ├── Machine.lean           # Регістровий файл, пам'ять, таймер
│   ├── Model/                 # Об'єкти ядра, стан, CDT
│   ├── Kernel/                # Підсистеми ядра
│   │   ├── Scheduler/         # Планувальник (RunQueue, EDF)
│   │   ├── Capability/        # Мандати (CSpace, CDT)
│   │   ├── IPC/               # Міжпроцесна взаємодія (DualQueue)
│   │   ├── Lifecycle/         # Життєвий цикл об'єктів
│   │   ├── Service/           # Оркестрація сервісів
│   │   ├── InformationFlow/   # Інформаційні потоки (N-доменна модель)
│   │   ├── RobinHood/         # Верифікована хеш-таблиця Robin Hood
│   │   ├── RadixTree/         # Верифіковане radix-дерево для CNode
│   │   ├── FrozenOps/         # Операції над замороженим станом
│   │   ├── Architecture/      # VSpace, декодування регістрів
│   │   └── API.lean           # Публічний API ядра
│   ├── Platform/              # Абстракція платформи
│   │   ├── Sim/               # Симуляційна платформа (для тестів)
│   │   └── RPi5/              # Raspberry Pi 5 (BCM2712)
│   └── Testing/                # Тестовий стенд і фікстури
├── tests/                     # Тестові сьюти (test suites)
├── Main.lean                  # Точка входу виконуваного файлу
├── docs/                      # Документація
│   ├── spec/                  # Специфікації
│   ├── gitbook/               # Повний посібник (handbook)
│   └── audits/                # Звіти аудитів
└── scripts/                   # Скрипти збірки, тестування, CI
```

## Встановлення pre-commit хука

Перед першим комітом обов'язково встановіть хук, що блокує коміти з
помилками компіляції чи `sorry`:

```bash
./scripts/install_git_hooks.sh
```

Хук автоматично перевіряє кожен змінений `.lean` файл перед комітом. Не
обходьте його за допомогою `--no-verify` — якщо він блокує коміт,
виправте першопричину.

## Типовий цикл розробки

```bash
# 1. Створення гілки для задачі
git checkout -b feature/my-change

# 2. Внесення змін у .lean файли
#    (пам'ятайте: Operations.lean — переходи, Invariant.lean — доведення)

# 3. Перевірка компіляції змінених модулів
source ~/.elan/env && lake build SeLe4n.Kernel.MyModule

# 4. Валідація
./scripts/test_smoke.sh

# 5. Коміт і PR
git add <змінені файли>
git commit -m "Опис зміни"
git push -u origin feature/my-change
```

## Корисні команди

| Команда | Опис |
|---------|------|
| `lake build` | Збірка всіх модулів проєкту |
| `lake build <Module.Path>` | Збірка конкретного модуля |
| `lake exe sele4n` | Запуск трасувального стенда |
| `lake clean` | Очищення артефактів збірки |
| `./scripts/test_fast.sh` | Швидка перевірка (гігієна + збірка) |
| `./scripts/test_smoke.sh` | Стандартна перевірка (перед PR) |
| `./scripts/test_full.sh` | Повна перевірка (теореми/інваріанти) |
| `./scripts/generate_codebase_map.py --pretty` | Регенерація карти кодової бази |

## Вирішення типових проблем

### Помилка «unknown package»

Переконайтеся, що ви активували середовище elan:

```bash
source ~/.elan/env
```

### Помилка компіляції після оновлення тулчейна

Очистіть кеш збірки і перезберіть:

```bash
lake clean && lake build
```

### Тест `test_smoke.sh` не проходить

Перевірте, що вивід `lake exe sele4n` збігається з фікстурою:

```bash
lake exe sele4n > /tmp/actual.txt
diff tests/fixtures/main_trace_smoke.expected /tmp/actual.txt
```

### Хук pre-commit блокує коміт

Хук виявив `sorry` або помилку компіляції. Виправте проблему — **не**
обходьте хук за допомогою `--no-verify`.

## Що вивчати далі

- [README (українською)](README.md) — огляд проєкту та архітектура
- [Внесок у розвиток (українською)](CONTRIBUTING.md) — правила та
  чек-лист для PR
- [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md) — детальний робочий
  процес (англійською)
- [`docs/gitbook/README.md`](../../gitbook/README.md) — повний посібник
  (англійською)

---

> Цей документ є адаптованим перекладом матеріалів із
> [docs/DEVELOPMENT.md](../../DEVELOPMENT.md) та
> [англійського README](../../../README.md).
