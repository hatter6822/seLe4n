# دليل البداية السريعة لـ seLe4n

<div dir="rtl">

هذا الدليل يأخذك من الصفر إلى بناء وتشغيل واختبار نواة seLe4n المصغرة (microkernel).
seLe4n مكتوب بلغة Lean 4 ويستخدم نظام البناء Lake.

</div>

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | **العربية** | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

---

## المتطلبات الأساسية

<div dir="rtl">

- نظام تشغيل Linux أو macOS (يُفضَّل Ubuntu 22.04+)
- اتصال بالإنترنت (لتنزيل سلسلة أدوات Lean)
- `git` مثبّت
- `bash` الإصدار 4 أو أحدث

</div>

## الخطوة 1: استنساخ المستودع

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## الخطوة 2: إعداد البيئة

<div dir="rtl">

يقوم سكريبت الإعداد بتثبيت سلسلة أدوات Lean (عبر `elan`) وتهيئة البيئة:

</div>

```bash
# إعداد البيئة (تثبيت Lean v4.28.0 عبر elan)
./scripts/setup_lean_env.sh

# أو بدون تبعيات الاختبار (أسرع)
./scripts/setup_lean_env.sh --skip-test-deps
```

<div dir="rtl">

بعد تشغيل سكريبت الإعداد، فعِّل بيئة elan في جلسة الطرفية الحالية:

</div>

```bash
source ~/.elan/env
```

## الخطوة 3: البناء

```bash
# بناء جميع الوحدات
lake build

# بناء وحدة محددة (مطلوب قبل التثبيت)
lake build SeLe4n.Kernel.API
```

<div dir="rtl">

**ملاحظة مهمة:** الأمر `lake build` (بدون وسيطات) يبني فقط الأهداف المُعرَّفة في `lakefile.lean`.
للتحقق من أن وحدة محددة تُترجم بنجاح (مثلًا بعد تعديلها)، استخدم:

</div>

```bash
lake build <Module.Path>
# مثال:
lake build SeLe4n.Kernel.Scheduler.Operations.Core
```

## الخطوة 4: تشغيل أداة التتبع (Trace Harness)

```bash
lake exe sele4n
```

<div dir="rtl">

يُنفذ هذا الأمر أداة التتبع الرئيسية التي تحاكي سيناريوهات النواة وتُخرج تتبعًا (trace) لكل انتقال.
الخرج المتوقع محفوظ في `tests/fixtures/main_trace_smoke.expected`.

</div>

## الخطوة 5: التحقق والاختبار

<div dir="rtl">

seLe4n يستخدم نظام اختبار متدرج (tiered testing). اختر المستوى المناسب:

</div>

### المستوى 0 + 1: النظافة والبناء (الأسرع)

```bash
./scripts/test_fast.sh
```

<div dir="rtl">

يتحقق من: نظافة الشفرة، ونجاح البناء، وعمق البرهان الدلالي.

</div>

### المستوى 0-2: اختبار الدخان (Smoke Test) — الحد الأدنى لطلبات السحب

```bash
./scripts/test_smoke.sh
```

<div dir="rtl">

يضيف: تحقق التتبع (trace)، واختبارات الحالة السلبية (negative-state)، ومزامنة الوثائق.
**هذا هو الحد الأدنى المطلوب قبل فتح أي طلب سحب (PR).**

</div>

### المستوى 0-3: الاختبار الكامل — مطلوب لتغييرات المبرهنات

```bash
./scripts/test_full.sh
```

<div dir="rtl">

يضيف: مراسي سطح الثوابت (invariant surface anchors) والتحقق من صحة تصريحات Lean `#check`.
**شغِّل هذا عند تغيير أي مبرهنة (theorem) أو ثابت (invariant) أو مرساة وثائق.**

</div>

### المستوى 0-4: الاختبار الليلي

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

<div dir="rtl">

يشمل اختبارات الحتمية (determinism) الليلية. يُشغَّل عادةً في التكامل المستمر (CI) فقط.

</div>

## تخطيط المصدر

<div dir="rtl">

فيما يلي نظرة عامة على البنية الرئيسية للمشروع:

</div>

```
SeLe4n/
├── Prelude.lean                 # معرّفات مُنمَّطة (typed identifiers)، موناد KernelM
├── Machine.lean                 # ملف السجلات (register file)، الذاكرة، المؤقت
├── Model/
│   ├── Object.lean              # محور إعادة التصدير: TCB, Endpoint, Notification, CNode
│   ├── State.lean               # حالة النظام (SystemState) مع مخازن HashMap
│   ├── IntermediateState.lean   # حالة مرحلة البناء (builder-phase) مع شهود الثوابت
│   ├── Builder.lean             # عمليات البناء المحافظة على الثوابت
│   ├── FrozenState.lean         # FrozenMap, FrozenSet, FrozenSystemState
│   └── FreezeProofs.lean        # براهين صحة التجميد (freeze correctness)
├── Kernel/
│   ├── API.lean                 # واجهة النواة العامة الموحدة
│   ├── Scheduler/               # جدولة RunQueue ذات الأولوية المقسّمة، EDF
│   ├── Capability/              # عمليات CSpace/CDT + ثوابت
│   ├── IPC/                     # نظام IPC بطابور مزدوج
│   ├── Lifecycle/               # إعادة تنميط الكائنات (object retype)
│   ├── Service/                 # تنسيق الخدمات مع كشف الدورات
│   ├── Architecture/            # VSpace, VSpaceBackend, فك ترميز السجلات
│   ├── InformationFlow/         # تسميات أمنية ثنائية البعد، مبرهنات عدم التداخل (NI)
│   ├── RobinHood/               # جدول تجزئة Robin Hood محقق
│   ├── RadixTree/               # شجرة جذرية (radix tree) CNode بمصفوفة مسطحة
│   ├── FrozenOps/               # عمليات النواة المجمّدة (frozen kernel operations)
│   └── CrossSubsystem.lean      # ثوابت عبر الأنظمة الفرعية
├── Platform/
│   ├── Contract.lean            # فئة نمطية PlatformBinding (typeclass)
│   ├── Sim/                     # عقود منصة المحاكاة
│   ├── RPi5/                    # منصة Raspberry Pi 5 (BCM2712)
│   └── Boot.lean                # تسلسل الإقلاع
├── Testing/                     # أداة الاختبار، بنّاء الحالة، الملفات المرجعية
Main.lean                        # نقطة الدخول التنفيذية
tests/                           # حزم اختبار: حالة سلبية، تدفق معلومات، تتبع
```

## تثبيت خُطاف ما قبل التثبيت (Pre-commit Hook)

<div dir="rtl">

يُنصح بشدة بتثبيت خُطاف ما قبل التثبيت لمنع تثبيت شفرة لا تُترجم أو تحتوي على `sorry`:

</div>

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

<div dir="rtl">

يقوم الخُطاف تلقائيًا بـ:

</div>

- بناء كل وحدة `.lean` معدّلة عبر `lake build <Module.Path>`
- التحقق من عدم وجود `sorry` في المحتوى المُجهَّز
- منع التثبيت (commit) إذا فشل أي بناء أو وُجد sorry

## خريطة قاعدة الشفرة (Codebase Map)

<div dir="rtl">

الملف [`docs/codebase_map.json`](../../../docs/codebase_map.json) هو الجرد القابل للقراءة آليًا لكل وحدة وتصريح في المشروع. يُغذّي موقع [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) ويُعدّ مصدر الحقيقة الموحد لمقاييس المشروع.

</div>

```bash
# إعادة توليد خريطة قاعدة الشفرة
./scripts/generate_codebase_map.py --pretty

# التحقق من صحتها دون كتابة
./scripts/generate_codebase_map.py --pretty --check
```

## المقاييس الحالية

| المقياس | القيمة |
|---------|--------|
| **الإصدار** | `0.18.6` |
| **سلسلة أدوات Lean** | `v4.28.0` |
| **أسطر Lean الإنتاجية** | 55,499 عبر 98 ملفًا |
| **التصريحات المُبرهَنة** | 1,686 (بدون أي sorry/axiom) |
| **العتاد المستهدف** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |

## الموارد الإضافية

<div dir="rtl">

- [الملف التعريفي الرئيسي (README)](README.md) — نظرة عامة شاملة على المشروع
- [دليل المساهمة](CONTRIBUTING.md) — قواعد المساهمة ومتطلبات طلبات السحب
- [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — سير العمل اليومي المفصّل
- [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — الدليل الكامل (معمارية، تصميم، براهين)
- [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — تاريخ تيارات العمل وخارطة الطريق

</div>

---

<div dir="rtl">

هذا المستند مترجم ومُكيَّف من [English DEVELOPMENT.md](../../../docs/DEVELOPMENT.md) و[English README](../../../README.md).

</div>
