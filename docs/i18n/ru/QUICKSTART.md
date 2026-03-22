# Быстрый старт seLe4n

Пошаговое руководство по настройке среды разработки, сборке и запуску
микроядра seLe4n.

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | **Русский** | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

---

## Предварительные требования

| Компонент | Версия | Назначение |
|-----------|--------|------------|
| **Git** | ≥ 2.30 | Управление версиями |
| **curl** | любая | Загрузка установщика elan |
| **bash** | ≥ 4.0 | Скрипты сборки и тестирования |
| **Python 3** | ≥ 3.8 | Генерация `codebase_map.json` и отчётов |

Тулчейн Lean (включая `elan`, `lean` и `lake`) устанавливается автоматически
скриптом настройки.

## Шаг 1. Клонирование репозитория

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## Шаг 2. Установка тулчейна Lean

Скрипт установки загружает [elan](https://github.com/leanprover/elan) —
менеджер версий Lean, — и устанавливает версию тулчейна, указанную в файле
`lean-toolchain` проекта (в настоящее время Lean v4.28.0).

```bash
./scripts/setup_lean_env.sh
```

Если вы хотите пропустить установку зависимостей для тестирования (shellcheck,
ripgrep), используйте:

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

После установки активируйте окружение:

```bash
source ~/.elan/env
```

### Проверка установки

```bash
lean --version
# Ожидаемый вывод: leanprover/lean4:v4.28.0

lake --version
# Ожидаемый вывод: Lake version ... (Lean version 4.28.0)
```

## Шаг 3. Сборка проекта

```bash
lake build
```

Первая сборка загружает зависимости и компилирует все модули — это может
занять несколько минут. Последующие инкрементальные сборки значительно быстрее.

### Сборка отдельного модуля

Для проверки конкретного модуля без полной пересборки:

```bash
lake build SeLe4n.Kernel.Scheduler.Operations
lake build SeLe4n.Kernel.IPC.Invariant
lake build SeLe4n.Kernel.RobinHood.Core
```

Формат имени модуля: путь к файлу с заменой `/` на `.` и без расширения `.lean`.

## Шаг 4. Запуск трассировочного стенда

```bash
lake exe sele4n
```

Команда запускает исполняемый стенд трассировки (trace harness), демонстрирующий
переходы ядра. Вывод должен совпадать с ожидаемым файлом-фикстурой:

```
tests/fixtures/main_trace_smoke.expected
```

## Шаг 5. Валидация

### Минимальная проверка (перед любым PR)

```bash
./scripts/test_smoke.sh
```

Включает:
- **Уровень 0** — гигиена: проверка отсутствия `sorry`/`axiom`, целостность
  ссылок сайта, синтаксические проверки
- **Уровень 1** — сборка: `lake build` завершается успешно
- **Уровень 2** — трассировка, негативные состояния, синхронизация документации

### Полная проверка (при изменении теорем/инвариантов)

```bash
./scripts/test_full.sh
```

Дополнительно включает:
- **Уровень 3** — якоря поверхности инвариантов, проверка корректности
  Lean `#check`

### Быстрая проверка (только гигиена + сборка)

```bash
./scripts/test_fast.sh
```

### Ночной тест

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

## Структура проекта

```
seLe4n/
├── SeLe4n/                    # Исходный код ядра (Lean 4)
│   ├── Prelude.lean           # Типизированные идентификаторы, монада KernelM
│   ├── Machine.lean           # Регистровый файл, память, таймер
│   ├── Model/                 # Объекты ядра, состояние, CDT
│   ├── Kernel/                # Подсистемы ядра
│   │   ├── Scheduler/         # Планировщик (RunQueue, EDF)
│   │   ├── Capability/        # Мандаты (CSpace, CDT)
│   │   ├── IPC/               # Межпроцессное взаимодействие (DualQueue)
│   │   ├── Lifecycle/         # Жизненный цикл объектов
│   │   ├── Service/           # Оркестрация сервисов
│   │   ├── InformationFlow/   # Информационные потоки (N-доменная модель)
│   │   ├── RobinHood/         # Верифицированная хеш-таблица Robin Hood
│   │   ├── RadixTree/         # Верифицированное radix-дерево для CNode
│   │   ├── FrozenOps/         # Операции над замороженным состоянием
│   │   ├── Architecture/      # VSpace, декодирование регистров
│   │   └── API.lean           # Публичный API ядра
│   ├── Platform/              # Абстракция платформы
│   │   ├── Sim/               # Симуляционная платформа (для тестов)
│   │   └── RPi5/              # Raspberry Pi 5 (BCM2712)
│   └── Testing/               # Тестовый стенд и фикстуры
├── tests/                     # Тестовые сьюты (test suites)
├── Main.lean                  # Точка входа исполняемого файла
├── docs/                      # Документация
│   ├── spec/                  # Спецификации
│   ├── gitbook/               # Полное руководство (handbook)
│   └── audits/                # Отчёты аудитов
└── scripts/                   # Скрипты сборки, тестирования, CI
```

## Установка pre-commit хука

Настоятельно рекомендуется установить хук, предотвращающий коммит файлов
с ошибками компиляции или `sorry`:

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

Хук автоматически проверяет каждый изменённый `.lean` файл перед коммитом.

## Типичный цикл разработки

```bash
# 1. Создание ветки для задачи
git checkout -b feature/my-change

# 2. Внесение изменений в .lean файлы
#    (помните: Operations.lean — переходы, Invariant.lean — доказательства)

# 3. Проверка компиляции изменённых модулей
source ~/.elan/env && lake build SeLe4n.Kernel.MyModule

# 4. Валидация
./scripts/test_smoke.sh

# 5. Коммит и PR
git add <изменённые файлы>
git commit -m "Описание изменения"
git push -u origin feature/my-change
```

## Полезные команды

| Команда | Описание |
|---------|----------|
| `lake build` | Сборка всех модулей проекта |
| `lake build <Module.Path>` | Сборка конкретного модуля |
| `lake exe sele4n` | Запуск трассировочного стенда |
| `lake clean` | Очистка артефактов сборки |
| `./scripts/test_fast.sh` | Быстрая проверка (гигиена + сборка) |
| `./scripts/test_smoke.sh` | Стандартная проверка (перед PR) |
| `./scripts/test_full.sh` | Полная проверка (теоремы/инварианты) |
| `./scripts/generate_codebase_map.py --pretty` | Регенерация карты кодовой базы |

## Решение типичных проблем

### Ошибка «unknown package»

Убедитесь, что вы активировали окружение elan:

```bash
source ~/.elan/env
```

### Ошибка компиляции после обновления тулчейна

Очистите кеш сборки и пересоберите:

```bash
lake clean && lake build
```

### Тест `test_smoke.sh` не проходит

Проверьте, что вывод `lake exe sele4n` совпадает с фикстурой:

```bash
lake exe sele4n > /tmp/actual.txt
diff tests/fixtures/main_trace_smoke.expected /tmp/actual.txt
```

### Хук pre-commit блокирует коммит

Хук обнаружил `sorry` или ошибку компиляции. Исправьте проблему — **не**
обходите хук с помощью `--no-verify`.

## Дальнейшее изучение

- [README (русский)](README.md) — обзор проекта и архитектура
- [Внесение вклада (русский)](CONTRIBUTING.md) — правила и чек-лист для PR
- [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — подробный рабочий процесс (на английском)
- [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — полное руководство (на английском)

---

> Этот документ является адаптированным переводом материалов из
> [docs/DEVELOPMENT.md](../../../docs/DEVELOPMENT.md) и
> [English README](../../../README.md).
