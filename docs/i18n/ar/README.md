<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.37.35-blue" alt="Version" />
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

seLe4n نواة مصغّرة (microkernel) مبنية من الصفر بلغة Lean 4. كل انتقال في النواة
دالة نقية قابلة للتنفيذ، وكل لامتغيّر تتحقق منه نواة Lean: سطح البراهين الإنتاجي
لا يحوي أي `sorry` ولا أي `axiom`. تُترجَم شيفرة Lean نفسها إلى شيفرة أصلية وتُربط،
مع طبقة عتاد صغيرة مكتوبة بلغة Rust، في صورة النواة التي تُقلع على العتاد المستهدف.

يحافظ المشروع على نموذج الأمان القائم على القدرات (capabilities) في seL4، وبصورة
متزايدة على واجهة ABI التي يراها المستخدم في seL4، مع استخدام Lean لإثبات المزيد
عنها وتقويتها حيث يترك seL4 ثغرة. المواصفة الكاملة هي
[`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)، والبنود أدناه مداخل إليها.

### واجهة ABI الخاصة بـ seL4

- **استدعاءات نظام seL4-MCS** — استدعاءات MCS الأحد عشر (`Call` … `Yield`) مرقّمة
  في `x7` كما يرقّمها seL4؛ وتُختار العملية من الاستدعاء ونوع القدرة المستدعاة
  ووسم الرسالة (`Syscall.selectOperation`) كما في seL4
- **حمولات الأخطاء والأعطال في seL4** — `LookupFault`، وإطار الخطأ بترتيب سجلات
  الرسائل في seL4، وأعطال القدرات في جهة الاستقبال، والحالة `Restart`، ووسائط
  القدرات الممرَّرة قدراتٍ إضافية، والحارس المحفوظ داخل القدرة مع
  `resolveAddressBits` واحد
- بقية العمل على واجهة seL4 (الاستدعاءات المتبقية، وأعطال المهلة، والحقوق لكل
  استدعاء، وحالة Running لكل نواة معالج) هي مسار العمل النشط WS-SX؛ وصفوفه في
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)

### الجدولة والزمن الحقيقي

- **سياقات الجدولة بوصفها قدرات** — زمن المعالج كائن من كائنات النواة. يحمل
  `SchedContext` ميزانية seL4-MCS ودورتها وعمليات إعادة تعبئتها، ويُضبط عبر سلطة
  `SchedControl` الخاصة بنواة المعالج، ويُربط بالخيوط عبر القدرات؛ ولامتغيّراته
  (`budgetWithinBounds` و`refillsConserved`) جزء من الحزمة العليا. عزل عرض النطاق
  هو `refill_window_bound`: لا يعمل السياق أكثر من ميزانيته في أي نافذة طولها دورة
  واحدة، وهو ضمان النافذة المنزلقة في seL4-MCS. أما المجدول الهرمي ذو عرض النطاق
  الثابت بجذر EDF، الذي يضيف الاتجاه المعاكس (الخادم المقبول ينال ميزانيته في كل
  نافذة)، فهو مسار العمل المخطط WS-CB
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **الخوادم السلبية** — يعمل الخادم على سياق الجدولة الذي يمنحه إياه عميله أثناء
  IPC؛ ويستبعد `donationChainAcyclic` المنح الدائري
- **مهلات IPC المدفوعة بالميزانية** — يُزال الخيط المحجوب الذي نفدت ميزانيته من
  طابور نقطة النهاية الخاصة به (`timeoutThread`)
- **وراثة الأولوية** — انتشار متعدٍّ مع خلوّ مُتحقَّق آليًا من دورات الحجب
  (`blockingAcyclic`) ومبرهنة انعكاس محدود (`pip_bounded_inversion`)
- **زمن استجابة محدود** — حدّ وسيطي لأسوأ زمن استجابة،
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`، مع صيغة لكل نواة معالج)، مُبرهَن على وحدات
  `SeLe4n/Kernel/Scheduler/Liveness/`

### كائنات النواة والذاكرة

- **كائنات تُقتطع من ذاكرة untyped** — تقتطع عملية retype كائنًا من منطقة قدرة
  untyped، وإعادة ضبط untyped هي إعادة ضبط seL4. ونقل خلايا كل كائن مقتطع إلى ذاكرة
  الـ untyped نفسها هو مسار العمل النشط WS-UC
- **مدخل النواة لا يخصّص شيئًا** — لا تجري مداخل استدعاء النظام والعطل والمقاطعة
  المترجمة أي تخصيص في الكومة؛ واقتطاع retype لا يخصّص إلا خلايا الكائن الجديد.
  وتقيس بوابة الكومة في QEMU
  (`scripts/test_qemu_heap_allocations_per_syscall.sh`) كل مدخل على الصورة المُقلعة
  وتفشل عند أي قيمة أخرى
- **بنى البيانات** — مخزن الكائنات وتعيينات VSpace جداول تجزئة Robin Hood مُتحقَّق
  منها (`RHTable`، مع `distCorrect` و`noDupKeys` و`probeChainDominant`)؛ وعقدة CNode
  مصفوفة مسطّحة من `2^radix` خانة كما في seL4؛ وطوابير التشغيل وطوابير نقاط النهاية
  والإشعارات ومنتظرو الردود مربوطة عبر كتل TCB، ولكلٍّ منها طابور مجرد شبحي مُبرهَن
  توافقه مع الروابط
- **شجرة اشتقاق القدرات المربوطة عبر الخانات** — تحفظ كل خانة روابط الأب والابن
  الأول والأخ (قاعدة بيانات التعيين في seL4)، مع برهان توافقها مع الشجرة؛ وتسير
  عمليات الحذف والإبطال (حلقة `cteRevoke` في seL4) ونقل الخانات على هذه الروابط
- **VSpace** — جداول صفحات ARMv8 مع فرض W^X لكل إطار، وفحوص لنوع الذاكرة ترفض
  الاسم المستعار غير المخزَّن مؤقتًا لذاكرة RAM

### الأمان والتحقق

- **تدفق المعلومات بعدد N من النطاقات** — سياسات تدفق وسيطية تعمّم تقسيم seL4
  الثنائي؛ وحدّ إنفاذ يثبّت طوله `enforcementBoundaryExtended_count` (و
  `enforcementBoundaryPerCore_count` للحدّ الخاص بكل نواة معالج)؛ ومبرهنة عدم تداخل
  لكل باني من بُناة `NonInterferenceStep`؛ وسجل تدقيق محدود ومغلق عند الفشل لعمليات
  رفع السرية، يُقرأ عبر قدرة `auditTrail`
- **طبقة براهين مركّبة** — يجمع `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) حزمة لامتغيّرات كل نظام فرعي
  (المجدول، القدرات، IPC واقترانه بالمجدول، دورة الحياة، سجل الخدمات، VSpace،
  ما بين الأنظمة الفرعية، اتساق TLB وذاكرة التعليمات المؤقتة، إسقاط TLB، سجل تدقيق
  رفع السرية، وتوافق كل بنية مربوطة مع شبحها) في التزام واحد يُحمل من الإقلاع عبر كل
  عملية
- **تعدد الأنوية** — أربع أنوية مع جدولة لكل نواة، وIPC وإيقاظ بين الأنوية، وإسقاط
  TLB؛ ومسار عمل إكمال SMP (WS-SM) جارٍ
- **حالة بثلاث مراحل** — تتجمّد مرحلة البناء ذات شواهد اللامتغيّرات إلى تمثيل ثابت
  مع برهان تكافؤ البحث؛ وتغطي العمليات المجمّدة الاستدعاءات التي يسردها
  `frozenOpCoverage`، ويثبّتها `frozenOpCoverage_count`
- **سجل الخدمات** — امتداد في seLe4n غير موجود في seL4: تُسجَّل الخدمات ويُبحث عنها
  عبر قدرة `serviceRegistry` وتُدوَّن على نقطة النهاية التي تخدمها؛ وتُترك سياسة
  الاعتماديات، كما في seL4، لمدير خدمات في فضاء المستخدم

## الحالة الراهنة

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| السمة | القيمة |
|-------|--------|
| **الإصدار** | `0.37.35` |
| **سلسلة أدوات Lean** | `v4.28.0` |
| **أسطر Lean الإنتاجية** | 662,957 عبر 655 ملفًا |
| **أسطر Lean للاختبارات** | 92,061 عبر 71 مجموعة اختبار |
| **الإعلانات المُبرهَنة** | 25,284 إعلانًا theorem/lemma (صفر sorry/axiom) |
| **حزم Rust** | `sele4n-types` و`sele4n-abi` و`sele4n-sys` (أغلفة فضاء المستخدم) و`sele4n-hal` (طبقة عتاد النواة)، واختبار المضيف `sele4n-lean-boundary` |
| **العتاد المستهدف** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **مسارات الإقلاع** | كل مسار QEMU يُقلع أولًا صورة Raspberry Pi 5 على الآلة `raspi5b` من [rpi5_machine](https://github.com/hatter6822/rpi5_machine)، ثم صورة `virt` على آلة `virt` في QEMU |
| **مسارات العمل** | حالة كل مسار عمل مفتوح: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md)؛ الفهرس وسجل الديون: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **التدقيقات** | [`docs/audits/`](../../../docs/audits/README.md) — مخرجات التدقيق النشط؛ التدقيقات السابقة مؤرشفة |
| **خريطة الشيفرة** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد للتصريحات قابل للقراءة آليًا |

تُستخرج المقاييس من الشيفرة بواسطة `./scripts/generate_codebase_map.py` وتُحفظ في
[`docs/codebase_map.json`](../../../docs/codebase_map.json) تحت المفتاح `readme_sync`.
حدّث الوثائق كلها معًا عبر `./scripts/sync_documentation_metrics.sh` (للتحقق فقط:
`--check`).

## البدء السريع

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

لا يبني `lake build` إلا ما يصل إليه `Main.lean` وملفات الاختبار التنفيذية؛ وقبل
إيداع ملف `.lean` ابنِ وحدته باسمها (`lake build <Module.Path>`). سير العمل الكامل
في [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)، والقواعد التي يتبعها كل مساهم في
[`CLAUDE.md`](../../../CLAUDE.md).

## التوثيق

| ابدأ هنا | ثم |
|----------|-----|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — سير العمل والتحقق وقائمة PR | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — المواصفة والمعالم |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — الدليل الكامل | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — الدلالات المرجعية لـ seL4 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — جرد قابل للقراءة آليًا | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — كل بند مؤجل مع مسؤوله |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — آلية المساهمة | [`CHANGELOG.md`](../../../CHANGELOG.md) — تاريخ الإصدارات |

## أوامر التحقق

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

شغّل على الأقل `test_smoke.sh` قبل أي PR، و`test_full.sh` عند تغيير المبرهنات أو
اللامتغيّرات أو مراسي Tier 3. يتوقف كل مستوى عند أول فحص يفشل؛ مرّر `--continue`
لجمع كل الإخفاقات في تمريرة واحدة.

بعد أي تغيير تحت `rust/` شغّل مساري Rust **كليهما**. فهما يغطيان نصفين منفصلين من
الحزمة نفسها: على المضيف تُزال كل كتلة `#[cfg(target_arch = "aarch64")]` قبل أن
يراها rustc أو clippy، فلا يرى مسار المضيف الكتل الشرطية ومواضع `asm!` ومصادر `.S`
التي تشكّل معظم HAL. ويبني المسار المتقاطع `sele4n-hal` للهدف
`aarch64-unknown-none-softfloat` في الملفين التعريفيين، ويتحقق من أن مصادر التجميع
قد جُمّعت فعلًا، ويفحص الهدف المتقاطع، ويفكّك كائنات الإصدار ليثبت أنها لا تستخدم أي
سجل FP/SIMD. تبني مسارات QEMU عند أول استخدام rpi5_machine عند الإيداع المثبّت في
`scripts/setup_rpi5_machine.sh`؛ والمسار الذي ينقصه شرط مسبق يُبلَّغ عنه NOT RUN لا
نجاحًا. القائمة الكاملة في [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

## البنية

يُنظَّم seLe4n في عقود متراصّة الطبقات، لكلٍّ منها انتقالات قابلة للتنفيذ وبراهين
حفظ لامتغيّرات مُتحقَّق منها آليًا:

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

## بنية الشيفرة المصدرية

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

يتبع كل نظام فرعي **فصل Operations/Invariant**: الانتقالات في `Operations.lean`،
والبراهين في `Invariant.lean`. ويجمع `apiInvariantBundle` الموحّد لامتغيّرات الأنظمة
الفرعية كلها في التزام برهاني واحد. خريطة الأنظمة الفرعية في
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5، والجرد الكامل لكل ملف في
[`docs/codebase_map.json`](../../../docs/codebase_map.json).

## المقارنة مع seL4

| الميزة | seL4 | seLe4n |
|--------|------|--------|
| **واجهة استدعاءات النظام** | استدعاءات MCS، أوسمة الاستدعاء، حمولات الأخطاء والأعطال | نفسها: استدعاءات seL4-MCS الأحد عشر بترقيمها، واستدعاءات تُختار بالوسم، وحمولات أخطاء seL4؛ والاستدعاءات المتبقية صفوف في WS-SX |
| **الجدولة** | سياقات جدولة MCS مع إعادة تعبئة الخادم المتقطع | محرّك إعادة التعبئة نفسه، مع برهان لامتغيّر الحفظ وحدّ ميزانية واحدة لكل نافذة (`refill_window_bound`)؛ ومخطط لـ CBS هرمي بجذر EDF (WS-CB) |
| **الخوادم السلبية** | منح SchedContext | منح مُتحقَّق منه مع اللامتغيّر `donationChainAcyclic` |
| **IPC** | طابور واحد لكل نقطة نهاية، مربوط عبر كتل TCB | طابور إرسال وطابور استقبال لكل نقطة نهاية، كلاهما مربوط عبر كتل TCB مع إزالة بزمن O(1) من أي موضع؛ مهلات مدفوعة بالميزانية |
| **تدفق المعلومات** | تقسيم ثنائي مرتفع/منخفض | سياسة قابلة للضبط بعدد N من النطاقات، وحدّ إنفاذ يثبّته `enforcementBoundaryExtended_count`، ومبرهنة عدم تداخل لكل خطوة، وسجل تدقيق تتحكم فيه القدرات لكل رفع سرية مصرّح به |
| **وراثة الأولوية** | ليست في النواة | PIP متعدٍّ مُتحقَّق منه آليًا بلا دورات حجب، مع مبرهنة انعكاس محدود |
| **زمن استجابة محدود** | لا حدّ WCRT رسمي | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`، مُبرهَن على وحدات الحيوية |
| **مخزن الكائنات** | كائنات في عناوين فيزيائية | جداول تجزئة Robin Hood مُتحقَّق منها (`RHTable`/`RHSet`)؛ وعُقد CNode مصفوفات خانات مسطّحة كما في seL4 |
| **تعيين الذاكرة** | لا تفرض النواة W^X | فرض W^X لكل إطار لامتغيّرًا؛ وفحوص نوع الذاكرة ترفض الاسم المستعار غير المخزَّن مؤقتًا لذاكرة RAM |
| **إدارة الخدمات** | خارج النواة | سجل خدمات تتحكم فيه القدرات على نقطة النهاية؛ وسياسة الاعتماديات في فضاء المستخدم |
| **البراهين** | Isabelle/HOL، على شيفرة C عبر التنقيح | Lean 4، بجوار الانتقالات القابلة للتنفيذ؛ صفر sorry/axiom (العدد في الجدول أعلاه) |
| **المنصة** | HAL على مستوى C | صنف الأنواع `PlatformBinding` بعقود حدود مُنمَّطة وطبقة HAL بلغة Rust |

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
