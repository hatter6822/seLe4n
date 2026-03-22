<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.18.6-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  نواة مصغرة (microkernel) مكتوبة بلغة Lean 4 مع براهين محققة آليًا (machine-checked proofs)،
  مستوحاة من معمارية <a href="https://sel4.systems">seL4</a>.
  المنصة المستهدفة الأولى: <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    صُمِم بعناية بمساعدة:
  </div>
  <div align="center">
    claude 🤖 ❤️ 🤖 codex
  </div>
  <div align="center">
    <strong>تعامَل مع هذه النواة وفقًا لذلك</strong>
  </div>
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | **العربية** | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## ما هو seLe4n؟

<div dir="rtl">

seLe4n هو نواة مصغرة (microkernel) بُنيت من الصفر بلغة Lean 4. كل انتقال في النواة (kernel transition) هو دالة نقية قابلة للتنفيذ (executable pure function). كل ثابت (invariant) محقق آليًا بواسطة مدقق الأنماط في Lean — بدون أي `sorry`، وبدون أي `axiom`. سطح البراهين بالكامل يُترجم إلى شفرة أصلية (native code) دون أي براهين مُسلَّم بها (admitted proofs).

يعتمد المشروع نموذج أمان قائمًا على الصلاحيات (capability-based security model) مع تقديم تحسينات معمارية مبتكرة مقارنة بالنوى المصغرة الأخرى:

</div>

- **مسارات النواة الساخنة بتعقيد O(1) باستخدام التجزئة (hash-based hot paths)** — جميع مخازن الكائنات (object stores)، وطوابير التشغيل (run queues)، وفتحات CNode، وتعيينات VSpace، وطوابير IPC تستخدم `RHTable`/`RHSet` (جدول تجزئة Robin Hood مع ثوابت محققة آليًا، بدون أي `Std.HashMap`/`Std.HashSet` في الحالة)
- **طبقة تنسيق الخدمات (service orchestration layer)** لإدارة دورة حياة المكونات والتبعيات مع دلالات فشل جزئي حتمية (deterministic partial-failure semantics)
- **شجرة اشتقاق صلاحيات مستقرة العقد (node-stable capability derivation tree)** مع فهارس `childMap` + `parentMap` من نوع RHTable لنقل الفتحات وإبطالها والبحث عن الأصل والتجول بين الفروع بتعقيد O(1)
- **IPC بطابور مزدوج مضمّن (intrusive dual-queue IPC)** مع روابط `queuePrev`/`queuePPrev`/`queueNext` لكل خيط (thread) للإدراج والإزالة والإزالة من منتصف الطابور بتعقيد O(1)
- **إطار تدفق معلومات معيّن بعدد N من النطاقات (N-domain information-flow)** مع سياسات تدفق قابلة للتهيئة، يُعمِّم تسميات السرية/السلامة التقليدية (يتجاوز التقسيم الثنائي في seL4)
- **جدولة EDF + أولوية (EDF + priority scheduling)** مع دلالات إخراج عند الإرسال (dequeue-on-dispatch)، وسياق سجلات لكل TCB مع تبديل سياق مضمّن، و`RunQueue` مقسّم حسب الأولوية، وتقسيم واعٍ بالنطاقات (domain-aware partitioning)

## الحالة الراهنة

<!-- المقاييس أدناه مُزامنة من docs/codebase_map.json → readme_sync.
     أعد التوليد بالأمر: ./scripts/generate_codebase_map.py --pretty
     مصدر الحقيقة: docs/codebase_map.json (readme_sync) -->

| السمة | القيمة |
|-------|--------|
| **الإصدار** | `0.18.6` |
| **سلسلة أدوات Lean** | `v4.28.0` |
| **أسطر Lean الإنتاجية** | 55,732 عبر 98 ملفًا |
| **أسطر Lean الاختبارية** | 7,317 عبر 10 حزم اختبار |
| **التصريحات المُبرهَنة** | 1,692 تصريح theorem/lemma (بدون أي sorry/axiom) |
| **العتاد المستهدف** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **أحدث تدقيق** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — تدقيق شامل للنواة + شفرة Rust قبل الإصدار |
| **خريطة قاعدة الشفرة** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد تصريحات قابل للقراءة آليًا |

<div dir="rtl">

تُستخرج المقاييس من قاعدة الشفرة بواسطة `./scripts/generate_codebase_map.py`
وتُخزَّن في [`docs/codebase_map.json`](../../../docs/codebase_map.json) تحت مفتاح `readme_sync`.
حدِّث جميع الوثائق معًا باستخدام `./scripts/report_current_state.py` كتحقق تقاطعي.

</div>

## البداية السريعة

```bash
./scripts/setup_lean_env.sh   # تثبيت سلسلة أدوات Lean
lake build                     # ترجمة جميع الوحدات
lake exe sele4n                # تشغيل أداة التتبع (trace harness)
./scripts/test_smoke.sh        # التحقق (نظافة + بناء + تتبع + حالة سلبية + مزامنة وثائق)
```

<div dir="rtl">

لمزيد من التفاصيل حول الإعداد والتطوير اليومي، راجع [دليل البداية السريعة](QUICKSTART.md).

</div>

## مسار التعلم

<div dir="rtl">

هل أنت جديد على المشروع؟ اتبع ترتيب القراءة التالي:

</div>

1. **هذا الملف (README)** — هوية المشروع، والمعمارية، وتخطيط المصدر
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — سير العمل اليومي، وحلقة التحقق، وقائمة مراجعة طلبات السحب (PR)
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — الدليل الكامل (تعمق في المعمارية، والبراهين، ومسار العتاد)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد الوحدات والتصريحات القابل للقراءة آليًا

<div dir="rtl">

لتخطيط تيارات العمل (workstreams) وتاريخها، راجع [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md).

</div>

## وثائق المشروع

| المستند | الغرض |
|---------|-------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | مواصفات المشروع والمعالم |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | الدلالات المرجعية لـ seL4 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | سير العمل اليومي، وحلقة التحقق، وقائمة مراجعة طلبات السحب |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | بوابات الاختبار المتدرجة وعقد التكامل المستمر (CI) |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | تاريخ تيارات العمل الكامل، وخارطة الطريق، وفهرس خطط التدقيق |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | الدليل الكامل (معمارية، تصميم، براهين، مسار العتاد) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | جرد قاعدة الشفرة القابل للقراءة آليًا (مُزامن مع README) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | آليات المساهمة ومتطلبات طلبات السحب |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | سجل الإصدارات |

## أوامر التحقق

```bash
./scripts/test_fast.sh      # المستوى 0 + 1 (نظافة + بناء، عمق برهان دلالي L-08)
./scripts/test_smoke.sh     # + المستوى 2 (تتبع + حالة سلبية + مزامنة وثائق)
./scripts/test_full.sh      # + المستوى 3 (مراسي سطح الثوابت + التحقق من صحة Lean #check)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + المستوى 4 (حتمية ليلية)
```

<div dir="rtl">

شغِّل `test_smoke.sh` على الأقل قبل أي طلب سحب (PR). شغِّل `test_full.sh` عند تغيير المبرهنات (theorems) أو الثوابت (invariants) أو مراسي الوثائق.

</div>

## البنية المعمارية

<div dir="rtl">

seLe4n منظّم كعقود متدرجة (layered contracts)، لكل منها انتقالات قابلة للتنفيذ وبراهين حفظ ثوابت (invariant preservation proofs) محققة آليًا:

</div>

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
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

<div dir="rtl">

يتبع كل نظام فرعي في النواة (kernel subsystem) نمط **فصل العمليات/الثوابت (Operations/Invariant split)**: الانتقالات في `Operations.lean`، والبراهين في `Invariant.lean`. يُجمِّع `apiInvariantBundle` الموحد جميع ثوابت الأنظمة الفرعية في التزام برهاني واحد.

</div>

## مقارنة مع seL4

| الميزة | seL4 | seLe4n |
|--------|------|--------|
| **آلية IPC** | طابور نقطة نهاية (endpoint queue) بقائمة مرتبطة مفردة | طابور مزدوج مضمّن (intrusive dual-queue) مع مؤشرات خلفية `queuePPrev` لإزالة من منتصف الطابور بتعقيد O(1) |
| **تدفق المعلومات** | تقسيم ثنائي عالي/منخفض (binary high/low) | سياسة تدفق قابلة للتهيئة بعدد N من النطاقات (تُعمِّم تسميات السرية × السلامة التقليدية) |
| **إدارة الخدمات** | غير موجودة في النواة | تنسيق خدمات من الدرجة الأولى (first-class) مع رسم بياني للتبعيات وكشف الدورات بالبحث المعمّق (DFS) |
| **اشتقاق الصلاحيات** | CDT بقائمة مرتبطة للأبناء | `childMap` من نوع HashMap للبحث عن الأبناء بتعقيد O(1) |
| **المُجدوِل** | طابور أولوية مسطح | `RunQueue` مقسّم حسب الأولوية مع تتبع `maxPriority` مضمّن وجدولة EDF |
| **VSpace** | جداول صفحات عتادية | `HashMap VAddr (PAddr x PagePermissions)` مع فرض W^X |
| **منهجية البرهان** | Isabelle/HOL، بأثر رجعي (post-hoc) | مدقق أنماط Lean 4، البراهين مُشتركة الموقع مع الانتقالات |
| **تجريد المنصة** | HAL على مستوى C | فئة نمطية `PlatformBinding` (typeclass) مع عقود حدود مُنمَّطة |

## الخطوات القادمة

<div dir="rtl">

تُحفَظ الأولويات الحالية والتاريخ الكامل لتيارات العمل في
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md). ملخص:

</div>

- **WS-R** — معالجة شاملة لنتائج التدقيق (Comprehensive Audit Remediation) — 8 مراحل (R1–R8، 111 مهمة فرعية). تعالج جميع النتائج الـ 82 من [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md). المراحل R1–R7 مكتملة (v0.18.0–v0.18.6)، R8 قيد الانتظار. الخطة: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **ربط عتاد Raspberry Pi 5** — تجول جداول صفحات ARMv8 (page table walk)، وتوجيه مقاطعات GIC-400 (interrupt routing)، وتسلسل الإقلاع (boot sequence) — عقود منصة RPi5 أصبحت جوهرية عبر WS-H15

<div dir="rtl">

جميع الحافظات السابقة (WS-B حتى WS-Q) مكتملة. التدقيقات السابقة (v0.8.0–v0.9.32)، وإغلاقات المعالم، وفصول GitBook القديمة مؤرشفة في
[`docs/dev_history/`](../../../docs/dev_history/README.md).

</div>

---

<div dir="rtl">

هذا المستند مترجم من [English README](../../../README.md).

</div>
