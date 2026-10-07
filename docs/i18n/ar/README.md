<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.36.71-blue" alt="Version" />
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
    صُنع بعناية بمساعدة:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>تعامل مع هذه النواة على هذا الأساس</strong>
  </div>
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | **العربية** | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md) | [Українська](../uk/README.md)

---

## ما هو seLe4n؟

seLe4n هو نواة مصغرة بُنيت من الصفر بلغة Lean 4. كل انتقال في النواة هو دالة
نقية قابلة للتنفيذ. كل ثابت (invariant) محقق آليًا بواسطة مدقق الأنماط في Lean —
بدون أي `sorry`، وبدون أي `axiom`. سطح البراهين بالكامل يُترجم إلى شفرة أصلية
دون أي براهين مُسلَّم بها.

يحافظ المشروع على نموذج الأمان القائم على الصلاحيات (capability-based security model)
الخاص بـ seL4 مع تقديم تحسينات معمارية أتاحها إطار عمل براهين Lean 4:

### الجدولة وضمانات الوقت الحقيقي

- **كائنات أداء قابلة للتركيب (Composable performance objects)** — وقت المعالج هو كائن نواة من الدرجة الأولى. يغلّف `SchedContext` الميزانية والفترة والأولوية والموعد النهائي والنطاق في سياق جدولة قابل لإعادة الاستخدام ترتبط به الخيوط عبر الصلاحيات. جدولة CBS (Constant Bandwidth Server) توفر عزل نطاق ترددي مُبرهَن (نظرية `cbs_bandwidth_bounded`)
- **الخوادم السلبية (Passive servers)** — تستعير الخوادم الخاملة `SchedContext` العميل أثناء IPC، مستهلكةً صفر وحدة معالجة عند عدم الخدمة. ثابت `donationChainAcyclic` يمنع سلاسل التبرع الدائرية
- **مُهَل IPC مدفوعة بالميزانية** — العمليات المحجوبة محدودة بميزانية المُستدعي. عند الانتهاء تُنتزع الخيوط من طابور نقطة النهاية وتُعاد إدراجها
- **بروتوكول وراثة الأولوية (Priority Inheritance Protocol)** — نشر أولوية متعدٍّ مع حرية تامة من الجمود مُحققة آليًا (`blockingAcyclic`) وعمق سلسلة محدود. يمنع انعكاس الأولوية غير المحدود
- **نظرية الكمون المحدود (Bounded latency theorem)** — حد WCRT محقق آليًا: `WCRT = D × L_max + N × (B + P)`، مُبرهَن عبر 8 وحدات حيوية تغطي رتابة الميزانية وتوقيت التجديد ودلالات التنازل واستنفاد النطاق ودوران النطاق

### هياكل البيانات و IPC

- **مسارات ساخنة بتعقيد O(1) قائمة على التجزئة** — جميع مخازن الكائنات وطوابير التشغيل وفتحات CNode وتعيينات VSpace وطوابير IPC تستخدم جداول تجزئة Robin Hood محققة رسميًا مع ثوابت `distCorrect` و`noDupKeys` و`probeChainDominant`
- **IPC بطابور مزدوج مضمّن (Intrusive dual-queue IPC)** — مؤشرات خلفية لكل خيط لإدراج وحذف وإزالة من منتصف الطابور بتعقيد O(1)
- **شجرة اشتقاق صلاحيات مستقرة العقد** — فهارس `childMap` + `parentMap` لنقل الفتحات والإلغاء وتجول الأحفاد بتعقيد O(1)

### الأمان والتحقق

- **تدفق معلومات بعدد N من النطاقات** — سياسات تدفق ذات معاملات (parameterized) تعمّم التقسيم الثنائي لـ seL4. حدود تنفيذ من 44 مُدخلاً مع براهين عدم تداخل لكل عملية (استقرائي `NonInterferenceStep` بـ 35 مُنشئًا)، وسجل تدقيق لإلغاء التصنيف محدود ومُغلق عند الفشل (fail-closed) مع قارئ مُقيَّد بالصلاحيات
- **طبقة برهان مركّبة** — يجمع `proofLayerInvariantBundle` 16 حزمة ثوابت أنظمة فرعية (نواة المجدول + امتدادات CBS، الصلاحيات، IPC + اقتران IPC بالمجدول، دورة الحياة، الخدمة، VSpace، العبور بين الأنظمة الفرعية، اتساق TLB، اتساق منتظري الإشعارات، حدود التعليق/الإقرار لإسقاط TLB، إبطال TLB لكل نواة وتماسك I-cache، وحد سجل تدقيق إلغاء التصنيف) في التزام واحد على المستوى الأعلى محقق من الإقلاع عبر جميع العمليات
- **معمارية حالة ثلاثية الأطوار** — مرحلة بناء مع شواهد ثوابت تتدفق إلى تمثيل مجمّد غير قابل للتغيير مع تكافؤ بحث مُبرهَن. 24 عملية مجمّدة تعكس واجهة API الحية
- **مجموعة عمليات كاملة** — جميع عمليات seL4 مُنفَّذة مع الحفاظ على الثوابت، وصولًا إلى تعليق الخيوط واستئنافها (suspend/resume)، وإدارة الأولويات (setPriority/setMCPriority)، وتهيئة مخزن IPC المؤقت
- **تنسيق الخدمات** — دورة حياة مكونات على مستوى النواة مع رسوم بيانية للتبعيات ولاحلقية مُبرهَنة (امتداد seLe4n، غير موجود في seL4)

## الحالة الراهنة

<!-- MAINTAINERS/TRANSLATORS: the three metric rows below (production LoC,
     test LoC, proved declarations) are WRITTEN by
     scripts/sync_translated_metrics.py from docs/codebase_map.json.  A hand
     edit is overwritten on the next sync.  To reword a label, a preposition
     or an inflected noun, edit that script's TARGETS table in the same
     commit: it matches the surrounding literals verbatim and fails loudly
     when they change, so it can never quietly stop syncing this file. -->

| السمة | القيمة |
|-------|--------|
| **الإصدار** | `0.36.71` |
| **سلسلة أدوات Lean** | `v4.28.0` |
| **أسطر Lean الإنتاجية** | 442,695 عبر 376 ملفًا |
| **أسطر Lean للاختبارات** | 89,432 عبر 72 مجموعة اختبار |
| **الإعلانات المُبرهَنة** | 14,871 إعلانًا theorem/lemma (صفر sorry/axiom) |
| **حزم Rust (crates)** | 4 (`sele4n-types`، `sele4n-abi`، `sele4n-sys`، `sele4n-hal`) عبر 80 ملفًا مصدريًا |
| **العتاد المستهدف** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **الربط بالعتاد** | **H3 مكتمل** (WS-AG AG1–AG10): HAL، GIC-400، المؤقِّت، جداول صفحات ARMv8، جسر FFI، الإقلاع على QEMU |
| **التدقيق القياسي** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) — تدقيق شامل ما قبل الإصدار 1.0 (202 نتيجة؛ تمت المعالجة بواسطة WS-AK AK1–AK10؛ مؤرشف) |
| **آخر تدقيق** | [`AUDIT_v0.30.11_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../../../docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) — تدقيق جاهزية ما قبل الإصدار 1.0 أُجري بعد إغلاق WS-AN (يخلف [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md) المؤرشف الآن والذي عولج بواسطة WS-AN AN0–AN12). WS-RC R0..R5 أُنجز في v0.31.2؛ WS-RC R6..R14 استُوعب في WS-SM وفق خريطة الاستيعاب SM0.Q.1 (انظر [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §15`](../../../docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)). خطة تيار العمل النشطة: [`SMP_MULTICORE_COMPLETION_PLAN.md`](../../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md). |
| **خريطة قاعدة الشفرة** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد إعلانات قابل للقراءة آليًا |

تُشتق المقاييس من قاعدة الشفرة بواسطة `./scripts/generate_codebase_map.py` وتُخزَّن
في [`docs/codebase_map.json`](../../../docs/codebase_map.json) تحت مفتاح `readme_sync`.
حدِّث التوثيق كله معًا باستخدام `./scripts/sync_documentation_metrics.sh`
(للتحقق فقط: `--check`)؛ ويبقى `./scripts/report_current_state.py` أداةً يدوية للتحقق المتبادل.

## البداية السريعة

```bash
./scripts/setup_lean_env.sh   # تثبيت سلسلة أدوات Lean
lake build                     # ترجمة جميع الوحدات
lake exe sele4n                # تشغيل أداة التتبع (trace harness)
./scripts/test_smoke.sh        # التحقق (نظافة + بناء + تتبع + حالة سلبية)
```

## التوثيق

| ابدأ هنا | ثم |
|----------|-----|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — سير العمل، التحقق، قائمة مراجعة PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — المواصفات والمعالم |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — الدليل الكامل | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — دلالات مرجعية لـ seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد قابل للقراءة آليًا | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — كل بند مؤجَّل، مع الجهة المسؤولة عنه |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — آليات المساهمة | [`CHANGELOG.md`](../../../CHANGELOG.md) — سجل الإصدارات |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) هو المصدر الوحيد للحقيقة
لمقاييس المشروع. يغذي [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
ويُحدَّث تلقائيًا عند الدمج عبر CI. أعد التوليد بـ:
`./scripts/generate_codebase_map.py --pretty`.

## أوامر التحقق

```bash
./scripts/test_fast.sh      # المستوى 0+1: نظافة + بناء
./scripts/test_smoke.sh     # + المستوى 2: تتبع + حالة سلبية
./scripts/test_full.sh      # + المستوى 3: مراسي سطح الثوابت + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + المستوى 4: حتمية ليلية

./scripts/test_rust.sh                 # Rust على المضيف: البناء، الاختبارات، fmt، clippy
./scripts/test_aarch64_cross_build.sh  # الهدف الفعلي لطبقة HAL في النواة
```

شغّل `test_smoke.sh` على الأقل قبل أي PR. شغّل `test_full.sh` عند تغيير
النظريات أو الثوابت أو مراسي التوثيق.

بعد أي تغيير تحت `rust/`، شغِّل مساري Rust **كليهما**. فهما يغطيان نصفين
منفصلين من الحزمة نفسها: على المضيف تُزال كل كتلة
`#[cfg(target_arch = "aarch64")]` قبل أن يراها rustc أو clippy، لذا لا يستطيع
مسار المضيف رؤية الكتل الـ 67 المشروطة بـ cfg، ولا مواضع `asm!` الـ 57، ولا
مصادر `.S` الأربعة التي تشكّل معظم HAL. أما المسار المتقاطع فيبني `sele4n-hal`
للهدف `aarch64-unknown-none-softfloat` في كلا ملفَّي التعريف (profiles)، ويتحقق
من أن مصادر التجميع قد جُمِّعت فعلًا، ويُجري الفحص (lint) على الهدف المتقاطع،
ويفكّك كائنات الإصدار (release) ليثبت أنها لا تستخدم أي سجل FP/SIMD — فالنواة
خالية من الفاصلة العائمة وتعترض FP/SIMD عند EL1 منذ أول تعليمة لها — وهو بناء
فعلي لا `cargo check`، لأن `check` يتوقف قبل توليد الشفرة ولا يصل أبدًا إلى
المُجمِّع.

## المعمارية

seLe4n منظم كعقود متعددة الطبقات، كل منها يحتوي على انتقالات قابلة للتنفيذ
وبراهين حفظ ثوابت محققة آليًا:

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
│        Platform  (Contract, Sim, RPi5)  ← production bindings        │
└──────────────────────────────────────────────────────────────────────┘
```

## تخطيط المصادر

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
tests/                           مجموعات اختبار قابلة للتنفيذ + تجهيزات (fixtures)
```

يتبع كل نظام فرعي نمط **الفصل بين Operations/Invariant**: الانتقالات في
`Operations.lean`، والبراهين في `Invariant.lean`. يجمع `apiInvariantBundle` الموحد
جميع ثوابت الأنظمة الفرعية في التزام برهاني واحد. للجرد الكامل لكل ملف، انظر
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## المقارنة مع seL4

| الميزة | seL4 | seLe4n |
|--------|------|--------|
| **الجدولة** | خادم متقطع مُنفَّذ بـ C (MCS) | CBS مع نظرية `cbs_bandwidth_bounded` محققة آليًا؛ `SchedContext` ككائن نواة خاضع للصلاحيات |
| **الخوادم السلبية** | تبرع SchedContext عبر C | تبرع محقق مع ثابت `donationChainAcyclic` |
| **IPC** | طابور نقطة نهاية بقائمة مرتبطة مفردة | طابور مزدوج مضمّن مع إزالة من المنتصف بتعقيد O(1)؛ مُهَل مدفوعة بالميزانية |
| **تدفق المعلومات** | تقسيم ثنائي عالي/منخفض | سياسة N-نطاق قابلة للتهيئة مع حدود تنفيذ من 44 مُدخلاً (العدد مثبَّت بواسطة `enforcementBoundaryExtended_count`) وبراهين NI لكل عملية وسجل تدقيق مُقيَّد بالصلاحيات لكل إلغاء تصنيف مُصرَّح به |
| **وراثة الأولوية** | PIP مُنفَّذ بـ C (فرع MCS) | PIP متعدٍّ محقق آليًا مع حرية من الجمود وحد WCRT بارامتري |
| **الكمون المحدود** | لا يوجد حد WCRT رسمي | `WCRT = D × L_max + N × (B + P)` مُبرهَن عبر 8 وحدات حيوية |
| **مخازن الكائنات** | قوائم مرتبطة ومصفوفات | جداول تجزئة Robin Hood محققة (`RHTable`/`RHSet`) مع مسارات ساخنة بتعقيد O(1) |
| **إدارة الخدمات** | غير موجودة في النواة | تنسيق من الدرجة الأولى مع رسم بياني للتبعيات وبراهين لاحلقية |
| **البراهين** | Isabelle/HOL، بأثر رجعي | مدقق أنماط Lean 4، مشتركة الموقع مع الانتقالات — صفر sorry/axiom (عدد الإعلانات المُبرهَنة في جدول [الحالة الراهنة](#الحالة-الراهنة)) |
| **المنصة** | HAL على مستوى C | فئة نمطية `PlatformBinding` مع عقود حدود مُنمَّطة |

## الترخيص وإسناد الأطراف الثالثة

seLe4n نفسه مرخَّص بموجب GNU General Public License v3.0 أو أي إصدار لاحق
(GPLv3+)؛ راجع [`LICENSE`](../../../LICENSE) للاطلاع على النص الكامل.
تُستخدم تبعيات البناء الخارجية (`cc`، `find-msvc-tools`، `shlex`، وجميعها
مرخَّصة ترخيصًا مزدوجًا `MIT OR Apache-2.0`) بموجب خيار MIT؛ وتُستنسخ إشعارات
حقوق النشر والأذونات الأصلية الخاصة بها حرفيًا في
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md). لا توجد في
الملف الثنائي للنواة أي شفرة خارجية مربوطة وقت التشغيل — فطبقة HAL هي
`#![no_std]` ولا تستخدم إلا `core::*`.

---

> هذا المستند مترجم من [English README](../../../README.md).
