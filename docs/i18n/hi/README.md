<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n लोगो" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="सुरक्षा" /></a>
  <img src="https://img.shields.io/badge/version-0.30.5-blue" alt="संस्करण" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="लाइसेंस" /></a>
</p>

<p align="center">
  Lean 4 में मशीन-जाँचित प्रमाणों (machine-checked proofs) के साथ लिखा गया एक
  सूक्ष्म नाभिक (microkernel), जो <a href="https://sel4.systems">seL4</a>
  वास्तुकला से प्रेरित है। प्रथम हार्डवेयर लक्ष्य:
  <strong>Raspberry Pi 5</strong>।
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | **हिन्दी**

---

## seLe4n क्या है?

seLe4n एक सूक्ष्म नाभिक है जो Lean 4 में शून्य से निर्मित किया गया है। प्रत्येक
कर्नेल संक्रमण एक निष्पादन योग्य शुद्ध फ़ंक्शन है। प्रत्येक अपरिवर्तनीय (invariant)
Lean प्रकार-परीक्षक द्वारा मशीन-जाँचित है — शून्य `sorry`, शून्य `axiom`। सम्पूर्ण
प्रमाण सतह बिना किसी स्वीकृत प्रमाण के मूल कोड में संकलित होती है।

यह परियोजना seL4 के क्षमता-आधारित सुरक्षा मॉडल को बनाए रखते हुए Lean 4 प्रमाण
ढाँचे द्वारा सक्षम वास्तुशिल्प सुधार प्रस्तुत करती है:

### शेड्यूलिंग और वास्तविक-समय गारंटी

- **संयोजनीय प्रदर्शन वस्तुएँ (Composable performance objects)** — CPU समय एक प्रथम-श्रेणी कर्नेल वस्तु है। `SchedContext` बजट, अवधि, प्राथमिकता, समय-सीमा, और डोमेन को एक पुनःप्रयोज्य शेड्यूलिंग संदर्भ में समाहित करता है जिससे थ्रेड क्षमताओं के माध्यम से बाइंड होते हैं। CBS (Constant Bandwidth Server) शेड्यूलिंग प्रमाणित बैंडविड्थ पृथक्करण (`cbs_bandwidth_bounded` प्रमेय) प्रदान करता है
- **निष्क्रिय सर्वर (Passive servers)** — निष्क्रिय सर्वर IPC के दौरान क्लाइंट का `SchedContext` उधार लेते हैं, सेवा न करते समय शून्य CPU उपभोग करते हैं। `donationChainAcyclic` अपरिवर्तनीय चक्रीय दान श्रृंखलाओं को रोकता है
- **बजट-चालित IPC टाइमआउट** — अवरुद्ध संचालन कॉलर के बजट द्वारा सीमित होते हैं। समाप्ति पर थ्रेड एंडपॉइंट क्यू से निकाले जाते हैं और पुनः सम्मिलित किए जाते हैं
- **प्राथमिकता वंशानुक्रम प्रोटोकॉल (Priority Inheritance Protocol)** — मशीन-जाँचित गतिरोध स्वतंत्रता (`blockingChainAcyclic`) और सीमित श्रृंखला गहराई के साथ सकर्मक प्राथमिकता प्रसारण। असीमित प्राथमिकता व्युत्क्रम को रोकता है
- **परिबद्ध विलंबता प्रमेय (Bounded latency theorem)** — मशीन-जाँचित WCRT सीमा: `WCRT = D × L_max + N × (B + P)`, बजट एकदिशता, पुनःपूर्ति समय, यील्ड शब्दार्थ, बैंड थकावट, और डोमेन चक्रण को कवर करने वाले 7 सजीवता मॉड्यूल में प्रमाणित

### डेटा संरचनाएँ और IPC

- **O(1) हैश-आधारित हॉट पाथ** — सभी ऑब्जेक्ट स्टोर, रन क्यू, CNode स्लॉट, VSpace मैपिंग, और IPC क्यू `distCorrect`, `noDupKeys`, और `probeChainDominant` अपरिवर्तनीयों सहित औपचारिक रूप से सत्यापित Robin Hood हैश टेबल का उपयोग करते हैं
- **इंट्रूसिव ड्यूअल-क्यू IPC** — O(1) एनक्यू, डिक्यू, और मध्य-क्यू निष्कासन के लिए प्रति-थ्रेड बैक-पॉइंटर
- **नोड-स्थिर क्षमता व्युत्पत्ति वृक्ष** — O(1) स्लॉट स्थानांतरण, निरसन, और वंशज अन्वेषण के लिए `childMap` + `parentMap` सूचकांक

### सुरक्षा और सत्यापन

- **N-डोमेन सूचना प्रवाह** — seL4 के द्विआधारी विभाजन को सामान्यीकृत करने वाली पैरामीटरयुक्त प्रवाह नीतियाँ��� प्रति-संचालन अ-हस्तक्षेप प्रमाणों सहित 30-प्रविष्टि प्रवर्तन सीमा (32-निर्माता `NonInterferenceStep` आगमनात्मक)
- **संयुक्त प्रमाण परत** — `proofLayerInvariantBundle` 10 उपप्रणाली अपरिवर्तनीयों (शेड्यूलर, क्षमता, IPC, जीवनचक्र, सेवा, VSpace, अंतर-उपप्रणाली, TLB, और CBS विस्तार) को बूट से सभी संचालनों तक सत्यापित एकल शीर्ष-स्तर दायित्व में संयोजित करता है
- **द्वि-चरण स्थिति वास्तुकला** — अपरिवर्तनीय साक्षियों सहित बिल्डर चरण प्रमाणित लुकअप तुल्यता सहित जमे हुए अपरिवर्तनीय प्रतिनिधित्व में प्रवाहित होता है। 20 जमे हुए संचालन लाइव API को दर्पणित करते हैं
- **पूर्ण संचालन समूह** — 5 स्थगित संचालनों (suspend/resume, setPriority/setMCPriority, setIPCBuffer) सहित, अपरिवर्तनीय संरक्षण के साथ सभी seL4 संचालन कार्यान्वित
- **सेवा समन्वय** — निर्भरता ग्राफ़ और प्रमाणित अचक्रीयता सहित कर्नेल-स्तर घटक जीवनचक्र (seLe4n विस्तार, seL4 में नहीं)

## वर्तमान स्थिति

| विशेषता | मान |
|----------|------|
| **संस्करण** | `0.25.5` |
| **Lean टूलचेन** | `v4.28.0` |
| **उत्पादन Lean LoC** | 132 फ़ाइलों में 83,286 |
| **परीक्षण Lean LoC** | 15 परीक्षण सुइट्स में 10,564 |
| **प्रमाणित घोषणाएँ** | 2,447 प्रमेय/लेम्मा घोषणाएँ (शून्य sorry/axiom) |
| **लक्ष्य हार्डवेयर** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **नवीनतम लेखापरीक्षा** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — पूर्ण कर्नेल Lean + Rust लेखापरीक्षा (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
| **कोडबेस मानचित्र** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय घोषणा सूची |

मेट्रिक्स `./scripts/generate_codebase_map.py` द्वारा कोडबेस से प्राप्त किए जाते हैं
और [`docs/codebase_map.json`](../../../docs/codebase_map.json) में `readme_sync`
कुंजी के अंतर्गत संग्रहीत होते हैं। `./scripts/report_current_state.py` को
पारस्परिक जाँच के रूप में उपयोग करें।

## त्वरित प्रारंभ

```bash
./scripts/setup_lean_env.sh   # Lean टूलचेन स्थापित करें
lake build                     # सभी मॉड्यूल संकलित करें
lake exe sele4n                # ट्रेस हार्नेस चलाएँ
./scripts/test_smoke.sh        # सत्यापन (स्वच्छता + निर्माण + ट्रेस + नकारात्मक-स्थिति + दस्तावेज़ समन्वय)
```

## दस्तावेज़ीकरण

| यहाँ से शुरू करें | फिर |
|-------------------|------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — कार्यप्रवाह, सत्यापन, PR चेकलिस्ट | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — विशिष्टता और मील के पत्थर |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — पूर्ण पुस्तिका | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4 संदर्भ शब्दार्थ |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय सूची | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — कार्यधारा इतिहास और रोडमैप |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — योगदान तंत्र | [`CHANGELOG.md`](../../../CHANGELOG.md) — संस्करण इतिहास |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) परियोजना मेट्रिक्स का
एकल सत्य स्रोत है। यह [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)
को डेटा प्रदान करता है और मर्ज पर CI के माध्यम से स्वतः नवीनीकृत होता है। पुनः उत्पन्न करें:
`./scripts/generate_codebase_map.py --pretty`।

## सत्यापन कमांड

```bash
./scripts/test_fast.sh      # टियर 0+1: स्वच्छता + निर्माण
./scripts/test_smoke.sh     # + टियर 2: ट्रेस + नकारात्मक-स्थिति + दस्तावेज़ समन्वय
./scripts/test_full.sh      # + टियर 3: अपरिवर्तनीय सतह एंकर + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + टियर 4: रात्रिकालीन नियतिवाद
```

किसी भी PR से पहले कम से कम `test_smoke.sh` चलाएँ। प्रमेयों, अपरिवर्तनीयों, या
दस्तावेज़ एंकरों में परिवर्तन करते समय `test_full.sh` चलाएँ।

## वास्तुकला

seLe4n स्तरित अनुबंधों के रूप में संगठित है, प्रत्येक में निष्पादन योग्य संक्रमण
और मशीन-जाँचित अपरिवर्तनीय संरक्षण प्रमाण हैं:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
│  SchedContext│             │  Donation  │           │                │
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

## स्रोत विन्यास

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
│   ├── SchedContext/             CBS budget engine, replenishment queue, priority management
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass
│   ├── Boot.lean                Boot sequence (PlatformConfig → IntermediateState)
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO)
├── Testing/                     Test harness, state builder, invariant checks
Main.lean                        Executable entry point
tests/                           15 test suites
```

प्रत्येक उपप्रणाली **Operations/Invariant विभाजन** का पालन करती है: संक्रमण
`Operations.lean` में, प्रमाण `Invariant.lean` में। एकीकृत `apiInvariantBundle`
सभी उपप्रणाली अपरिवर्तनीयों को एकल प्रमाण दायित्व में एकत्रित करता है। पूर्ण
फ़ाइलवार सूची के लिए [`docs/codebase_map.json`](../../../docs/codebase_map.json) देखें।

## seL4 से तुलना

| विशेषता | seL4 | seLe4n |
|----------|------|--------|
| **शेड्यूलिंग** | C-कार्यान्वित छिटपुट सर्वर (MCS) | मशीन-जाँचित `cbs_bandwidth_bounded` प्रमेय सहित CBS; `SchedContext` क्षमता-नियंत्रित कर्नेल वस्तु के रूप में |
| **निष्क्रिय सर्वर** | C के माध्यम से SchedContext दान | `donationChainAcyclic` अपरिवर्तनीय सहित सत्यापित दान |
| **IPC** | एकल लिंक्ड-लिस्ट एंडपॉइंट क्यू | O(1) मध्य-क्यू निष्कासन सहित इंट्रूसिव ड्यूअल-क्यू; बजट-चालित टाइमआउट |
| **सूचना प्रवाह** | द्विआधारी उच्च/निम्न विभाजन | 30-प्रविष्टि प्रवर्तन सीमा और प्रति-संचालन NI प्रमाणों सहित N-डोमेन विन्यासयोग्य नीति |
| **प्राथमिकता वंशानुक्रम** | C-कार्यान्वित PIP (MCS शाखा) | गतिरोध स्वतंत्रता और पैरामीट्रिक WCRT सीमा सहित मशीन-जाँचित सकर्मक PIP |
| **परिबद्ध विलंबता** | कोई औपचारिक WCRT सीमा नहीं | 7 सजीवता मॉड्यूल में प्रमाणित `WCRT = D × L_max + N × (B + P)` |
| **ऑब्जेक्ट स्टोर** | लिंक्ड लिस्ट और एरे | O(1) हॉट पाथ सहित सत्यापित Robin Hood हैश टेबल (`RHTable`/`RHSet`) |
| **सेवा प्रबंधन** | कर्नेल में नहीं | निर्भरता ग्राफ़ और अचक्रीयता प्रमाणों सहित प्रथम-श्रेणी समन्वय |
| **प्रमाण** | Isabelle/HOL, उत्तर-प्रभावी | Lean 4 प्रकार-परीक्षक, संक्रमणों के साथ सह-स्थित (2,447 प्रमेय, शून्य sorry/axiom) |
| **प्लेटफ़ॉर्म** | C-स्तरीय HAL | टाइप्ड सीमा अनुबंधों सहित `PlatformBinding` typeclass |

## अगले कदम

सभी सॉफ़्टवेयर-स्तर कार्यधाराएँ (WS-B से WS-AB) पूर्ण हैं। पूर्ण इतिहास
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) में है।

### पूर्ण कार्यधाराएँ

| कार्यधारा | दायरा | संस्करण |
|-----------|-------|---------|
| **WS-AB** | स्थगित संचालन और सजीवता पूर्णता — suspend/resume, setPriority/setMCPriority, setIPCBuffer, प्राथमिकता वंशानुक्रम प्रोटोकॉल, परिबद्ध विलंबता प्रमेय (6 चरण, 90 कार्य) | v0.24.0–v0.25.5 |
| **WS-Z** | संयोजनीय प्रदर्शन वस्तुएँ — `SchedContext` 7वीं कर्नेल वस्तु के रूप में, CBS बजट इंजन, पुनःपूर्ति क्यू, निष्क्रिय सर्वर दान, टाइमआउट एंडपॉइंट (10 चरण, 213 कार्य) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | मूल कर्नेल उपप्रणालियाँ, Robin Hood हैश टेबल, रेडिक्स ट्री, जमी हुई स्थिति, सूचना प्रवाह, सेवा समन्वय, प्लेटफ़ॉर्म अनुबंध | v0.9.0–v0.22.x |

विस्तृत योजनाएँ: [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### अगला प्रमुख मील का पत्थर

**Raspberry Pi 5 हार्डवेयर बाइंडिंग** — ARMv8 पेज टेबल वॉक, GIC-400 इंटरप्ट रूटिंग,
बूट अनुक्रम। पूर्व लेखापरीक्षाएँ और मील के पत्थर समापन
[`docs/dev_history/`](../../../docs/dev_history/README.md) में संग्रहीत हैं।

---

> यह दस्तावेज़ [English README](../../../README.md) का अनुवाद है।
