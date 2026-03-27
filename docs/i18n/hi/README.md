<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n लोगो" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="सुरक्षा" /></a>
  <img src="https://img.shields.io/badge/version-0.22.7-blue" alt="संस्करण" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="लाइसेंस" /></a>
</p>

<p align="center">
  Lean 4 में मशीन-जाँचित प्रमाणों (machine-checked proofs) के साथ लिखा गया एक
  सूक्ष्म नाभिक (microkernel), जो <a href="https://sel4.systems">seL4</a>
  वास्तुकला (architecture) से प्रेरित है। प्रथम हार्डवेयर लक्ष्य:
  <strong>Raspberry Pi 5</strong>।
</p>

<p align="center">
  <div align="center">
    इसके निर्माण में सहायक रहे:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>इस कर्नेल के साथ तदनुसार व्यवहार करें</strong>
  </div>
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | **हिन्दी**

---

## seLe4n क्या है?

seLe4n एक सूक्ष्म नाभिक (microkernel) है जो Lean 4 में शून्य से निर्मित किया गया है। प्रत्येक कर्नेल संक्रमण (kernel transition) एक निष्पादन योग्य शुद्ध फ़ंक्शन (executable pure function) है। प्रत्येक अपरिवर्तनीय (invariant) Lean प्रकार-परीक्षक (type-checker) द्वारा मशीन-जाँचित है — शून्य `sorry`, शून्य `axiom`। सम्पूर्ण प्रमाण सतह (proof surface) बिना किसी स्वीकृत प्रमाण (admitted proof) के मूल कोड (native code) में संकलित होती है।

यह परियोजना क्षमता-आधारित सुरक्षा मॉडल (capability-based security model) का उपयोग करती है और अन्य सूक्ष्म नाभिकों की तुलना में नवीन वास्तुशिल्प सुधार (architectural improvements) प्रस्तुत करती है:

- **O(1) हैश-आधारित कर्नेल हॉट पाथ (hot paths)** — सभी ऑब्जेक्ट स्टोर (object stores), रन क्यू (run queues), CNode स्लॉट (slots), VSpace मैपिंग (mappings), और IPC क्यू (queues) औपचारिक रूप से सत्यापित `RHTable`/`RHSet` (Robin Hood हैश टेबल, मशीन-जाँचित अपरिवर्तनीयों सहित, स्थिति में शून्य `Std.HashMap`/`Std.HashSet`) का उपयोग करते हैं
- **सेवा समन्वय परत (service orchestration layer)** — घटक जीवनचक्र (component lifecycle) और निर्भरता प्रबंधन (dependency management) के लिए, नियतात्मक आंशिक-विफलता शब्दार्थ (deterministic partial-failure semantics) के साथ
- **नोड-स्थिर क्षमता व्युत्पत्ति वृक्ष (node-stable capability derivation tree)** — O(1) स्लॉट स्थानांतरण (slot transfer), निरसन (revocation), मूल खोज (parent lookup), और वंशज अन्वेषण (descendant traversal) के लिए `childMap` + `parentMap` RHTable सूचकांकों के साथ
- **इंट्रूसिव ड्यूअल-क्यू IPC (intrusive dual-queue IPC)** — O(1) एनक्यू (enqueue), डिक्यू (dequeue), और मध्य-क्यू निष्कासन (mid-queue removal) के लिए प्रति-थ्रेड `queuePrev`/`queuePPrev`/`queueNext` लिंक के साथ
- **पैरामीटरयुक्त N-डोमेन सूचना प्रवाह (parameterized N-domain information-flow)** ढाँचा — विन्यासयोग्य प्रवाह नीतियों (configurable flow policies) के साथ, पुराने गोपनीयता/अखंडता लेबलों (legacy confidentiality/integrity labels) को सामान्यीकृत करते हुए (seL4 के द्विआधारी विभाजन से परे)
- **EDF + प्राथमिकता शेड्यूलिंग (priority scheduling)** — डिक्यू-ऑन-डिस्पैच शब्दार्थ (dequeue-on-dispatch semantics), प्रति-TCB रजिस्टर संदर्भ (register context) इनलाइन संदर्भ स्विच (inline context switch) के साथ, प्राथमिकता-बकेटेड `RunQueue`, डोमेन-सचेत विभाजन (domain-aware partitioning)

## वर्तमान स्थिति

<!-- मेट्रिक्स docs/codebase_map.json → readme_sync अनुभाग से समन्वयित हैं।
     पुनः उत्पन्न करें: ./scripts/generate_codebase_map.py --pretty
     सत्य का स्रोत: docs/codebase_map.json (readme_sync) -->

| विशेषता | मान |
|----------|------|
| **संस्करण (Version)** | `0.22.7` |
| **Lean टूलचेन (Toolchain)** | `v4.28.0` |
| **उत्पादन Lean LoC** | 103 फ़ाइलों में 72,569 |
| **परीक्षण Lean LoC** | 10 परीक्षण सुइट्स में 8,437 |
| **प्रमाणित घोषणाएँ (Proved declarations)** | 2,138 प्रमेय/लेम्मा घोषणाएँ (शून्य sorry/axiom) |
| **लक्ष्य हार्डवेयर (Target hardware)** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **नवीनतम लेखापरीक्षा (Latest audit)** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — पूर्ण कर्नेल + Rust कोडबेस प्री-रिलीज़ लेखापरीक्षा |
| **कोडबेस मानचित्र (Codebase map)** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय घोषणा सूची |

मेट्रिक्स `./scripts/generate_codebase_map.py` द्वारा कोडबेस से प्राप्त किए जाते हैं
और [`docs/codebase_map.json`](../../../docs/codebase_map.json) में `readme_sync`
कुंजी (key) के अंतर्गत संग्रहीत होते हैं।

## त्वरित प्रारंभ (Quick Start)

```bash
./scripts/setup_lean_env.sh   # Lean टूलचेन स्थापित करें
lake build                     # सभी मॉड्यूल संकलित करें
lake exe sele4n                # ट्रेस हार्नेस चलाएँ
./scripts/test_smoke.sh        # सत्यापन (स्वच्छता + निर्माण + ट्रेस + नकारात्मक-स्थिति + दस्तावेज़ समन्वय)
```

## प्रारंभिक मार्गदर्शन (Onboarding Path)

परियोजना में नए हैं? इस क्रम में पढ़ें:

1. **यह README** — परियोजना पहचान, वास्तुकला, और स्रोत विन्यास
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — दैनिक कार्यप्रवाह (workflow), सत्यापन चक्र (validation loop), PR चेकलिस्ट
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — पूर्ण पुस्तिका (वास्तुकला गहन अध्ययन, प्रमाण, हार्डवेयर पथ)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय मॉड्यूल और घोषणा सूची

कार्यधारा (workstream) योजना और इतिहास के लिए, [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) देखें।

## प्रोजेक्ट दस्तावेज़ (Project Documentation)

| दस्तावेज़ | उद्देश्य |
|-----------|---------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | परियोजना विशिष्टता (specification) और मील के पत्थर (milestones) |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | seL4 संदर्भ शब्दार्थ (reference semantics) |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | दैनिक कार्यप्रवाह, सत्यापन चक्र, PR चेकलिस्ट |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | स्तरीय परीक्षण द्वार (tiered test gates) और CI अनुबंध (contract) |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | पूर्ण कार्यधारा इतिहास, रोडमैप, और लेखापरीक्षा योजना सूचकांक |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | पूर्ण पुस्तिका (वास्तुकला, डिज़ाइन, प्रमाण, हार्डवेयर पथ) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | मशीन-पठनीय कोडबेस सूची (README के साथ समन्वयित) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | योगदान तंत्र (contribution mechanics) और PR आवश्यकताएँ |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | संस्करण इतिहास (version history) |

## सत्यापन कमांड (Validation Commands)

```bash
./scripts/test_fast.sh      # टियर 0 + टियर 1 (स्वच्छता + निर्माण, शब्दार्थ प्रमाण-गहराई L-08)
./scripts/test_smoke.sh     # + टियर 2 (ट्रेस + नकारात्मक-स्थिति + दस्तावेज़ समन्वय)
./scripts/test_full.sh      # + टियर 3 (अपरिवर्तनीय सतह एंकर + Lean #check शुद्धता)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + टियर 4 (रात्रिकालीन नियतिवाद)
```

किसी भी PR से पहले कम से कम `test_smoke.sh` चलाएँ। प्रमेयों (theorems), अपरिवर्तनीयों (invariants), या दस्तावेज़ एंकरों में परिवर्तन करते समय `test_full.sh` चलाएँ।

## वास्तुकला (Architecture)

seLe4n स्तरित अनुबंधों (layered contracts) के रूप में संगठित है, प्रत्येक में निष्पादन योग्य संक्रमण (executable transitions) और मशीन-जाँचित अपरिवर्तनीय संरक्षण प्रमाण (machine-checked invariant preservation proofs) हैं:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 कर्नेल API  (SeLe4n/Kernel/API.lean)                  │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  शेड्यूलर    │  क्षमता      │    IPC     │ जीवनचक्र  │  सेवा (बाह्य)   │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         सूचना प्रवाह  (नीति, प्रक्षेपण, प्रवर्तन)                       │
├──────────────────────────────────────────────────────────────────────┤
│     वास्तुकला  (VSpace, VSpaceBackend, Adapter, Assumptions)          │
├──────────────────────────────────────────────────────────────────────┤
│                     मॉडल  (Object, State, CDT)                       │
├──────────────────────────────────────────────────────────────────────┤
│             आधार  (Prelude, Machine, MachineConfig)                  │
├──────────────────────────────────────────────────────────────────────┤
│          प्लेटफ़ॉर्म  (Contract, Sim, RPi5)  ← H3-prep बाइंडिंग       │
└──────────────────────────────────────────────────────────────────────┘
```

प्रत्येक कर्नेल उपप्रणाली (subsystem) **Operations/Invariant विभाजन** का पालन करती है: संक्रमण `Operations.lean` में, प्रमाण `Invariant.lean` में। एकीकृत `apiInvariantBundle` सभी उपप्रणाली अपरिवर्तनीयों को एक एकल प्रमाण दायित्व (proof obligation) में एकत्रित करता है।

## seL4 से तुलना (Comparison with seL4)

| विशेषता | seL4 | seLe4n |
|----------|------|--------|
| **IPC तंत्र (mechanism)** | एकल लिंक्ड-लिस्ट एंडपॉइंट क्यू | O(1) मध्य-क्यू निष्कासन के लिए `queuePPrev` बैक-पॉइंटर के साथ इंट्रूसिव ड्यूअल-क्यू |
| **सूचना प्रवाह (Information flow)** | द्विआधारी उच्च/निम्न विभाजन (binary high/low partition) | N-डोमेन विन्यासयोग्य प्रवाह नीति (पुराने गोपनीयता × अखंडता लेबलों को सामान्यीकृत करती है) |
| **सेवा प्रबंधन (Service management)** | कर्नेल में नहीं | निर्भरता ग्राफ़ और DFS चक्र पहचान के साथ प्रथम-श्रेणी सेवा समन्वय |
| **क्षमता व्युत्पत्ति (Capability derivation)** | लिंक्ड-लिस्ट चिल्ड्रेन के साथ CDT | O(1) चिल्ड्रेन लुकअप के लिए `childMap` HashMap |
| **शेड्यूलर (Scheduler)** | फ्लैट प्राथमिकता क्यू | इनलाइन `maxPriority` ट्रैकिंग और EDF के साथ प्राथमिकता-बकेटेड `RunQueue` |
| **VSpace** | हार्डवेयर पेज टेबल | W^X प्रवर्तन (enforcement) के साथ `HashMap VAddr (PAddr x PagePermissions)` |
| **प्रमाण पद्धति (Proof methodology)** | Isabelle/HOL, उत्तर-प्रभावी (post-hoc) | Lean 4 प्रकार-परीक्षक, संक्रमणों के साथ सह-स्थित प्रमाण |
| **प्लेटफ़ॉर्म अमूर्तन (Platform abstraction)** | C-स्तरीय HAL | टाइप्ड सीमा अनुबंधों (typed boundary contracts) के साथ `PlatformBinding` typeclass |

## अगले कदम (What's Next)

वर्तमान प्राथमिकताएँ और पूर्ण कार्यधारा इतिहास
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) में बनाए रखे जाते हैं। सारांश:

- **WS-R** — व्यापक लेखापरीक्षा उपचार (Comprehensive Audit Remediation) (8 चरण, R1–R8, 111 उप-कार्य)। [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) से सभी 82 निष्कर्षों को संबोधित करता है। R1–R7 पूर्ण (v0.18.0–v0.18.6), R8 लंबित। योजना: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md)।
- **Raspberry Pi 5 हार्डवेयर बाइंडिंग** — ARMv8 पेज टेबल वॉक, GIC-400 इंटरप्ट रूटिंग, बूट अनुक्रम (boot sequence) (WS-H15 के माध्यम से RPi5 प्लेटफ़ॉर्म अनुबंध अब ठोस हैं)

पूर्व पोर्टफ़ोलियो (WS-B से WS-Q) सभी पूर्ण हैं। पूर्व लेखापरीक्षाएँ (v0.8.0–v0.9.32),
मील के पत्थर समापन, और पुराने GitBook अध्याय
[`docs/dev_history/`](../../../docs/dev_history/README.md) में संग्रहीत हैं।

---

> यह दस्तावेज़ [English README](../../../README.md) का अनुवाद है।
