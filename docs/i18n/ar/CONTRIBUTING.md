# المساهمة في seLe4n

<div dir="rtl">

شكرًا لمساهمتك في seLe4n — نواة مصغرة (microkernel) موجهة للإنتاج مكتوبة بلغة Lean 4 مع براهين محققة آليًا (machine-checked proofs).

</div>

---

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | **العربية** | [Français](../fr/CONTRIBUTING.md) | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

---

## الترخيص

<div dir="rtl">

seLe4n مرخص بموجب [رخصة جنو العمومية الإصدار 3.0 أو أحدث](../../../LICENSE) (GNU General Public License v3.0 or later).
بتقديم طلب سحب (pull request) أو مساهمة بشفرة في هذا المشروع، فإنك توافق على أن مساهماتك ستُرخَّص بموجب نفس الرخصة GPL-3.0-or-later.
كما تُقرّ بأن لديك الحق في تقديم المساهمة بموجب هذه الرخصة.

</div>

## مسار المساهم في 5 دقائق

<div dir="rtl">

ابدأ بقراءة هذه المستندات بالترتيب:

</div>

1. **سير العمل والمعايير:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **مستويات الاختبار:** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **سياسة التكامل المستمر (CI):** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **نطاق المشروع وتيارات العمل:** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **نتائج التدقيق النشطة:** [`docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md)
6. **تاريخ تيارات العمل:** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

<div dir="rtl">

الدليل الكامل: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

</div>

## التحقق المطلوب قبل فتح طلب سحب (PR)

```bash
./scripts/test_smoke.sh     # الحد الأدنى (المستوى 0-2)
./scripts/test_full.sh      # مطلوب عند تغيير المبرهنات/الثوابت (المستوى 0-3)
```

<div dir="rtl">

شغِّل `test_smoke.sh` كحد أدنى قبل كل طلب سحب. إذا عدّلت مبرهنات (theorems) أو ثوابت (invariants) أو مراسي وثائق، فشغِّل `test_full.sh` أيضًا.

</div>

## متطلبات طلب السحب (PR)

<div dir="rtl">

كل طلب سحب يجب أن يستوفي الشروط التالية:

</div>

- **تحديد معرّف تيار العمل (workstream ID)** — حدِّد تيار (تيارات) العمل التي يُسهم فيها طلب السحب
- **نطاق متماسك** — اجعل النطاق شريحة واحدة متماسكة، لا تخلط تغييرات من أنظمة فرعية مختلفة
- **انتقالات حتمية (deterministic transitions)** — جميع الانتقالات يجب أن تُرجع نجاحًا أو فشلًا صريحًا، دون فروع غير حتمية
- **تزاوج الثوابت مع التنفيذ** — كل تحديث لمبرهنة (theorem) أو ثابت (invariant) يجب أن يأتي مقترنًا بتغيير التنفيذ المقابل
- **مزامنة الوثائق** — حدِّث الوثائق ذات الصلة في نفس طلب السحب
- **لا sorry ولا axiom** — ممنوع في سطح البراهين الإنتاجي
- **لا إعادة تسمية لمسارات الموقع** — لا تُعِد تسمية أو حذف مسارات مدرجة في `scripts/website_link_manifest.txt`

<div dir="rtl">

راجع القائمة الكاملة في [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md).

</div>

## بناء الوحدات والتحقق منها

<div dir="rtl">

**قبل تثبيت أي ملف `.lean`**، يجب التحقق من أن الوحدة المحددة تُترجم بنجاح:

</div>

```bash
source ~/.elan/env && lake build <Module.Path>
```

<div dir="rtl">

على سبيل المثال، إذا عدّلت `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`:

</div>

```bash
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
```

<div dir="rtl">

**`lake build` (الهدف الافتراضي) غير كافٍ.** الهدف الافتراضي يبني فقط الوحدات التي يصل إليها `Main.lean` والملفات التنفيذية للاختبار. الوحدات غير المستوردة بعد من النواة الرئيسية ستتجاوز `lake build` بصمت حتى مع براهين معطلة.

</div>

## خُطاف ما قبل التثبيت (Pre-commit Hook)

<div dir="rtl">

ثبِّت خُطاف ما قبل التثبيت لفرض التحقق التلقائي:

</div>

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

<div dir="rtl">

يقوم الخُطاف بما يلي:

</div>

1. يكتشف ملفات `.lean` الموجودة في منطقة التجهيز (staging area)
2. يبني كل وحدة معدّلة عبر `lake build <Module.Path>`
3. يتحقق من عدم وجود `sorry` في المحتوى المُجهَّز
4. **يمنع التثبيت** إذا فشل أي بناء أو وُجد sorry

<div dir="rtl">

**لا تتجاوز الخُطاف** باستخدام `--no-verify`.

</div>

## الاصطلاحات الرئيسية

<div dir="rtl">

- **فصل العمليات/الثوابت (Operations/Invariant split)**: لكل نظام فرعي في النواة ملف `Operations.lean` (انتقالات) وملف `Invariant.lean` (براهين). حافظ على هذا الفصل.
- **دلالات حتمية (deterministic semantics)**: جميع الانتقالات تُرجع نجاحًا أو فشلًا صريحًا. لا تُدخل فروعًا غير حتمية أبدًا.
- **معرّفات مُنمَّطة (typed identifiers)**: `ThreadId`، `ObjId`، `CPtr`، `Slot`، `DomainId`، إلخ. هي هياكل مغلّفة (wrapper structures)، وليست أسماء بديلة لـ `Nat`. استخدم `.toNat`/`.ofNat` الصريحة.
- **تسمية داخلية أولًا (internal-first naming)**: أسماء المبرهنات/الدوال/التعريفات يجب أن تصف الدلالات. لا تُرمِّز معرّفات تيارات العمل (`WS-*`) في أسماء المعرّفات.
- **دليل مدعوم بأدلة مادية (fixture-backed evidence)**: يجب أن يتطابق خرج `Main.lean` مع `tests/fixtures/main_trace_smoke.expected`. حدِّث الملف المرجعي فقط مع مبرر.

</div>

## قواعد التوثيق

<div dir="rtl">

عند تغيير السلوك أو المبرهنات أو حالة تيارات العمل، حدِّث في نفس طلب السحب:

</div>

1. `README.md` — مزامنة المقاييس من `docs/codebase_map.json` (مفتاح `readme_sync`)
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. فصول GitBook المتأثرة — وثائق الجذر القانونية لها الأولوية على GitBook
5. `docs/CLAIM_EVIDENCE_INDEX.md` إذا تغيرت الادعاءات
6. `docs/WORKSTREAM_HISTORY.md` إذا تغيرت حالة تيار العمل
7. أعد توليد `docs/codebase_map.json` إذا تغيرت مصادر Lean

## الإبلاغ عن الثغرات الأمنية

<div dir="rtl">

أثناء تنفيذ أي مهمة في قاعدة الشفرة هذه، إذا اكتشفت ثغرة برمجية محتملة قد تستوجب تعيين CVE (Common Vulnerabilities and Exposures)، **يجب** عليك الإبلاغ عنها فورًا قبل المتابعة. يشمل ذلك الثغرات في:

- **شفرة هذا المشروع** — أخطاء منطقية في دلالات الانتقال، أو فحوصات الصلاحيات، أو فرض تدفق المعلومات
- **التبعيات وسلسلة الأدوات** — ثغرات معروفة أو مشتبه بها في Lean أو Lake أو elan
- **البنية التحتية للبناء والتكامل المستمر** — أنماط نصوص غير آمنة (مثل حقن الأوامر)
- **فجوات النموذج/المواصفات** — حالات يفشل فيها النموذج الرسمي في التقاط سلوك أمني ذي صلة

</div>

---

<div dir="rtl">

هذا المستند مترجم من [English CONTRIBUTING.md](../../../CONTRIBUTING.md).

</div>
