<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n लोगो" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="सुरक्षा" /></a>
  <img src="https://img.shields.io/badge/version-0.37.54-blue" alt="संस्करण" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="लाइसेंस" /></a>
</p>

<p align="center">
  Lean 4 में मशीन-जाँचित प्रमाणों (machine-checked proofs) के साथ लिखा गया एक
  सूक्ष्म नाभिक (microkernel), जो <a href="https://sel4.systems">seL4</a>
  वास्तुकला से प्रेरित है। प्रथम हार्डवेयर लक्ष्य:
  <strong>Raspberry Pi 5</strong>।
</p>
<p align="center">
  <div align="center">
    सोच-समझकर इनकी सहायता से बनाया गया:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>इस कर्नेल के साथ उसी के अनुरूप व्यवहार करें</strong>
  </div>
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | **हिन्दी** | [Українська](../uk/README.md)

---

## seLe4n क्या है?

seLe4n Lean 4 में शुरू से बनाया गया एक माइक्रोकर्नेल है। कर्नेल का हर संक्रमण एक
निष्पादन योग्य शुद्ध फ़ंक्शन है, और हर अपरिवर्तनीय (invariant) की जाँच Lean का कर्नेल
करता है: उत्पादन प्रमाण-सतह में शून्य `sorry` और शून्य `axiom` हैं। वही Lean कोड नेटिव
कोड में संकलित होता है और Rust की एक छोटी हार्डवेयर परत के साथ उस कर्नेल इमेज में
लिंक होता है जो लक्ष्य हार्डवेयर पर बूट होती है।

यह परियोजना seL4 के capability-आधारित सुरक्षा मॉडल को और, बढ़ते हुए, seL4 के
उपयोगकर्ता को दिखने वाले ABI को बनाए रखती है, जबकि Lean से उसके बारे में और अधिक
सिद्ध करती है और जहाँ seL4 कोई कमी छोड़ता है वहाँ उसे सुदृढ़ करती है। पूर्ण विनिर्देश
[`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) है; नीचे के बिंदु उसी के
प्रवेश-द्वार हैं।

### seL4 का ABI

- **seL4-MCS के सिस्टम कॉल** — MCS के ग्यारह सिस्टम कॉल (`Call` … `Yield`), `x7` में
  उसी क्रमांकन से जैसे seL4 करता है; संक्रिया सिस्टम कॉल, आह्वानित capability के
  प्रकार और संदेश लेबल से चुनी जाती है (`Syscall.selectOperation`), seL4 की तरह
- **seL4 के त्रुटि और फ़ॉल्ट पेलोड** — `LookupFault`, seL4 के संदेश-रजिस्टर क्रम में
  त्रुटि फ़्रेम, प्राप्ति-पक्ष के capability फ़ॉल्ट, `Restart` अवस्था, अतिरिक्त
  capability के रूप में दिए गए capability तर्क, और capability में रखा गार्ड तथा एक ही
  `resolveAddressBits`
- seL4 ABI का शेष कार्य (बाकी आह्वान, टाइमआउट फ़ॉल्ट, प्रति-आह्वान अधिकार, प्रति-कोर
  Running अवस्था) सक्रिय वर्कस्ट्रीम WS-SX है; इसकी पंक्तियाँ
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)
  में हैं

### शेड्यूलिंग और रियल-टाइम

- **capability के रूप में शेड्यूलिंग संदर्भ** — CPU समय एक कर्नेल ऑब्जेक्ट है।
  `SchedContext` seL4-MCS का बजट, अवधि और रीफ़िल रखता है, कोर के `SchedControl`
  प्राधिकार से कॉन्फ़िगर होता है और capability के ज़रिए थ्रेड से बँधता है; इसके
  अपरिवर्तनीय (`budgetWithinBounds`, `refillsConserved`) शीर्ष-स्तरीय बंडल का हिस्सा हैं।
  बैंडविड्थ पृथक्करण `refill_window_bound` है: कोई संदर्भ एक अवधि की किसी भी खिड़की में
  अपने बजट से अधिक नहीं चलता, यह seL4-MCS की स्लाइडिंग-विंडो गारंटी है। EDF मूल वाला
  पदानुक्रमित स्थिर-बैंडविड्थ शेड्यूलर, जो विपरीत गारंटी जोड़ता है (स्वीकृत सर्वर को हर
  खिड़की में अपना बजट मिलता है), नियोजित वर्कस्ट्रीम WS-CB है
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **निष्क्रिय सर्वर** — सर्वर उस शेड्यूलिंग संदर्भ पर चलता है जो IPC के दौरान उसका
  क्लाइंट दान करता है; `donationChainAcyclic` चक्रीय दान को बाहर रखता है
- **बजट-संचालित IPC टाइमआउट** — जिस अवरुद्ध थ्रेड का बजट समाप्त हो जाए, वह अपने
  एंडपॉइंट की कतार से हटा दिया जाता है (`timeoutThread`)
- **प्राथमिकता वंशानुक्रम** — सकर्मक प्रसार, मशीन-जाँचित अवरोध-चक्र-मुक्ति
  (`blockingAcyclic`) और सीमित व्युत्क्रम प्रमेय (`pip_bounded_inversion`)
- **सीमित विलंब** — सबसे खराब प्रतिक्रिया-समय की प्राचलिक सीमा,
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, प्रति-कोर रूप सहित),
  `SeLe4n/Kernel/Scheduler/Liveness/` के मॉड्यूलों पर सिद्ध

### कर्नेल ऑब्जेक्ट और मेमोरी

- **untyped मेमोरी से काटे गए ऑब्जेक्ट** — retype किसी untyped capability के क्षेत्र से
  ऑब्जेक्ट काटता है, और untyped का रीसेट seL4 जैसा है। हर काटे गए ऑब्जेक्ट की सेलों को
  उसके untyped की अपनी मेमोरी में ले जाना सक्रिय वर्कस्ट्रीम WS-UC है
- **कर्नेल प्रवेश कुछ भी आवंटित नहीं करता** — संकलित सिस्टम-कॉल, फ़ॉल्ट और इंटरप्ट
  प्रवेश कोई हीप आवंटन नहीं करते; retype की कटाई केवल नए ऑब्जेक्ट की अपनी सेलें आवंटित
  करती है। QEMU हीप गेट (`scripts/test_qemu_heap_allocations_per_syscall.sh`) बूट हुई
  इमेज पर हर प्रवेश मापता है और किसी अन्य गिनती पर विफल होता है
- **डेटा संरचनाएँ** — ऑब्जेक्ट स्टोर और VSpace मैपिंग सत्यापित Robin Hood हैश तालिकाएँ
  हैं (`RHTable`, `distCorrect`, `noDupKeys` और `probeChainDominant` सहित); CNode seL4
  की तरह `2^radix` स्लॉटों की सपाट सरणी है; रन कतारें, एंडपॉइंट और नोटिफ़िकेशन कतारें
  तथा उत्तर-प्रतीक्षक TCB के ज़रिए जुड़े हैं, हर एक के साथ एक भूतिया अमूर्त कतार जिसकी
  लिंकों से सहमति सिद्ध है
- **स्लॉटों से जुड़ा capability व्युत्पत्ति वृक्ष** — हर स्लॉट अपने जनक, पहले शिशु और
  सहोदर के लिंक (seL4 का मैपिंग डेटाबेस) रखता है, जिनकी वृक्ष से सहमति सिद्ध है; हटाना,
  निरस्तीकरण (seL4 का `cteRevoke` लूप) और स्लॉट स्थानांतरण इन लिंकों पर चलते हैं
- **VSpace** — प्रति फ़्रेम W^X लागू करने वाली ARMv8 पेज तालिकाएँ, और मेमोरी-प्रकार
  जाँचें जो RAM के बिना-कैश उपनाम को अस्वीकार करती हैं

### सुरक्षा और सत्यापन

- **N-डोमेन सूचना प्रवाह** — seL4 के दो-डोमेन विभाजन का सामान्यीकरण करने वाली
  प्राचलिक प्रवाह नीतियाँ; एक प्रवर्तन सीमा जिसकी लंबाई
  `enforcementBoundaryExtended_count` (और प्रति-कोर सीमा के लिए
  `enforcementBoundaryPerCore_count`) तय करता है; `NonInterferenceStep` के हर
  कंस्ट्रक्टर के लिए एक अहस्तक्षेप प्रमेय; और `auditTrail` capability से पढ़ा जाने
  वाला सीमित, विफलता-पर-बंद डीक्लासिफ़िकेशन ऑडिट ट्रेल
- **संयोजित प्रमाण परत** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`) हर उपप्रणाली के अपरिवर्तनीय बंडल
  (शेड्यूलर, capability, IPC और शेड्यूलर से उसका युग्मन, जीवनचक्र, सेवा रजिस्ट्री,
  VSpace, अंतर-उपप्रणाली, TLB और निर्देश-कैश सुसंगति, TLB शूटडाउन, डीक्लासिफ़िकेशन ऑडिट
  लॉग, और हर जुड़ी संरचना की अपने भूत से सहमति) को एक दायित्व में जोड़ती है, जो बूट से
  हर संक्रिया तक बना रहता है
- **बहु-कोर** — प्रति-कोर शेड्यूलिंग, अंतर-कोर IPC और जागरण, तथा TLB शूटडाउन के साथ
  चार कोर; SMP पूर्णता वर्कस्ट्रीम (WS-SM) जारी है
- **त्रि-चरण अवस्था** — अपरिवर्तनीय साक्ष्यों वाला बिल्डर चरण सिद्ध लुकअप-समतुल्यता
  वाले अपरिवर्तनशील निरूपण में जम जाता है; जमी हुई संक्रियाएँ उन सिस्टम कॉलों को कवर
  करती हैं जिन्हें `frozenOpCoverage` सूचीबद्ध करता है, `frozenOpCoverage_count` द्वारा
  तय
- **सेवा रजिस्ट्री** — seLe4n का विस्तार, seL4 में नहीं: सेवाएँ `serviceRegistry`
  capability से पंजीकृत और खोजी जाती हैं और सेवा देने वाले एंडपॉइंट पर दर्ज होती हैं;
  निर्भरता नीति, seL4 की तरह, उपयोगकर्ता-स्थान सेवा प्रबंधक पर छोड़ी जाती है

## वर्तमान स्थिति

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| विशेषता | मान |
|---------|-----|
| **संस्करण** | `0.37.54` |
| **Lean टूलचेन** | `v4.28.0` |
| **उत्पादन Lean LoC** | 704 फ़ाइलों में 685,251 |
| **परीक्षण Lean LoC** | 71 परीक्षण सुइट्स में 91,877 |
| **प्रमाणित घोषणाएँ** | 26,455 प्रमेय/लेम्मा घोषणाएँ (शून्य sorry/axiom) |
| **Rust क्रेट** | `sele4n-types`, `sele4n-abi`, `sele4n-sys` (उपयोगकर्ता-स्थान रैपर), `sele4n-hal` (कर्नेल की हार्डवेयर परत), और होस्ट परीक्षण `sele4n-lean-boundary` |
| **लक्ष्य हार्डवेयर** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **बूट लेन** | हर QEMU लेन पहले [rpi5_machine](https://github.com/hatter6822/rpi5_machine) की `raspi5b` मशीन पर Raspberry Pi 5 इमेज बूट करती है, फिर QEMU की `virt` पर `virt` इमेज |
| **वर्कस्ट्रीम** | हर खुले वर्कस्ट्रीम की स्थिति: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); सूचकांक और ऋण रजिस्टर: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **ऑडिट** | [`docs/audits/`](../../../docs/audits/README.md) — सक्रिय ऑडिट की सामग्री; पिछले ऑडिट संग्रहीत हैं |
| **कोडबेस मानचित्र** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय घोषणा सूची |

मेट्रिक्स `./scripts/generate_codebase_map.py` कोड से निकालता है और
[`docs/codebase_map.json`](../../../docs/codebase_map.json) में `readme_sync` कुंजी के अंतर्गत
रखता है। सारे दस्तावेज़ एक साथ `./scripts/sync_documentation_metrics.sh` (केवल जाँच:
`--check`) से अद्यतन करें।

## त्वरित आरंभ

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` केवल वही बनाता है जो `Main.lean` और परीक्षण निष्पादनयोग्यों से पहुँच में
है; किसी `.lean` फ़ाइल को कमिट करने से पहले उसका मॉड्यूल नाम से बनाएँ
(`lake build <Module.Path>`)। पूरा कार्यप्रवाह
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) में है, और हर योगदानकर्ता के नियम
[`CLAUDE.md`](../../../CLAUDE.md) में।

## दस्तावेज़ीकरण

| यहाँ से शुरू करें | फिर |
|-------------------|-----|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — कार्यप्रवाह, सत्यापन, PR चेकलिस्ट | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — विनिर्देश और पड़ाव |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — पूरी पुस्तिका | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4 का संदर्भ शब्दार्थ |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — मशीन-पठनीय सूची | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — हर स्थगित मद, उत्तरदायी सहित |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — योगदान प्रक्रिया | [`CHANGELOG.md`](../../../CHANGELOG.md) — संस्करण इतिहास |

## सत्यापन कमांड

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

किसी भी PR से पहले कम से कम `test_smoke.sh` चलाएँ, और प्रमेय, अपरिवर्तनीय या Tier 3
एंकर बदलते समय `test_full.sh`। हर टियर अपनी पहली विफल जाँच पर रुकता है; सभी विफलताएँ
एक बार में इकट्ठी करने के लिए `--continue` दें।

`rust/` के अंतर्गत किसी भी बदलाव के बाद Rust की **दोनों** लेन चलाएँ। वे एक ही क्रेट के
असंयुक्त आधे भागों को कवर करती हैं: होस्ट पर हर `#[cfg(target_arch = "aarch64")]`
ब्लॉक rustc या clippy के देखने से पहले हटा दिया जाता है, इसलिए होस्ट लेन HAL का
अधिकांश भाग बनाने वाले सशर्त ब्लॉक, `asm!` स्थल और `.S` स्रोत नहीं देख पाती। क्रॉस लेन
`sele4n-hal` को `aarch64-unknown-none-softfloat` के लिए दोनों प्रोफ़ाइलों में बनाती है,
जाँचती है कि असेंबली स्रोत सचमुच असेंबल हुए, क्रॉस लक्ष्य पर lint चलाती है, और release
ऑब्जेक्टों को डिसअसेंबल करके सिद्ध करती है कि वे कोई FP/SIMD रजिस्टर उपयोग नहीं करते।
QEMU लेनें पहली बार `scripts/setup_rpi5_machine.sh` में पिन किए कमिट पर rpi5_machine
बनाती हैं; जिस लेन की कोई पूर्व-शर्त अनुपस्थित हो, वह सफल नहीं बल्कि NOT RUN बताती है।
पूरी सूची [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) में है।

## वास्तुकला

seLe4n स्तरित अनुबंधों के रूप में संगठित है, हर एक में निष्पादन योग्य संक्रमण और
मशीन-जाँचित अपरिवर्तनीय-संरक्षण प्रमाण हैं:

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

## स्रोत संरचना

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

हर उपप्रणाली **Operations/Invariant विभाजन** का पालन करती है: संक्रमण
`Operations.lean` में, प्रमाण `Invariant.lean` में। एकीकृत `apiInvariantBundle` सभी
उपप्रणाली अपरिवर्तनीयों को एक प्रमाण-दायित्व में एकत्र करता है। उपप्रणाली मानचित्र
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5 है; प्रति-फ़ाइल पूरी सूची के लिए
[`docs/codebase_map.json`](../../../docs/codebase_map.json) देखें।

## seL4 से तुलना

| विशेषता | seL4 | seLe4n |
|---------|------|--------|
| **सिस्टम कॉल ABI** | MCS सिस्टम कॉल, आह्वान लेबल, त्रुटि और फ़ॉल्ट पेलोड | वही: seL4-MCS के ग्यारह सिस्टम कॉल और उनका क्रमांकन, लेबल से चुने गए आह्वान और seL4 के त्रुटि पेलोड; शेष आह्वान WS-SX की पंक्तियाँ हैं |
| **शेड्यूलिंग** | छिटपुट-सर्वर रीफ़िल वाले MCS शेड्यूलिंग संदर्भ | वही रीफ़िल इंजन, संरक्षण अपरिवर्तनीय और प्रति खिड़की एक बजट की सीमा (`refill_window_bound`) सिद्ध; EDF मूल वाला पदानुक्रमित CBS नियोजित (WS-CB) |
| **निष्क्रिय सर्वर** | SchedContext दान | `donationChainAcyclic` अपरिवर्तनीय के साथ सत्यापित दान |
| **IPC** | प्रति एंडपॉइंट एक कतार, TCB से जुड़ी | प्रति एंडपॉइंट एक भेजने और एक प्राप्ति कतार, दोनों TCB से जुड़ी और किसी भी स्थान से O(1) में हटाने योग्य; बजट-संचालित टाइमआउट |
| **सूचना प्रवाह** | द्विआधारी high/low विभाजन | विन्यास-योग्य N-डोमेन नीति, `enforcementBoundaryExtended_count` द्वारा तय प्रवर्तन सीमा, प्रति चरण एक अहस्तक्षेप प्रमेय, और हर अधिकृत डीक्लासिफ़िकेशन के लिए capability-नियंत्रित ऑडिट ट्रेल |
| **प्राथमिकता वंशानुक्रम** | कर्नेल में नहीं | अवरोध-चक्र-मुक्त, मशीन-जाँचित सकर्मक PIP, सीमित व्युत्क्रम प्रमेय सहित |
| **सीमित विलंब** | कोई औपचारिक WCRT सीमा नहीं | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, लाइवनेस मॉड्यूलों पर सिद्ध |
| **ऑब्जेक्ट स्टोर** | भौतिक पतों पर ऑब्जेक्ट | सत्यापित Robin Hood हैश तालिकाएँ (`RHTable`/`RHSet`); CNode seL4 की तरह सपाट स्लॉट सरणियाँ |
| **मेमोरी मैपिंग** | कर्नेल W^X लागू नहीं करता | प्रति फ़्रेम W^X अपरिवर्तनीय के रूप में लागू; मेमोरी-प्रकार जाँचें RAM के बिना-कैश उपनाम को अस्वीकार करती हैं |
| **सेवा प्रबंधन** | कर्नेल से बाहर | एंडपॉइंट पर capability-नियंत्रित सेवा रजिस्ट्री; निर्भरता नीति उपयोगकर्ता-स्थान में |
| **प्रमाण** | Isabelle/HOL, परिशोधन द्वारा C कोड पर | Lean 4, निष्पादन योग्य संक्रमणों के साथ; शून्य sorry/axiom (गिनती ऊपर की तालिका में) |
| **प्लेटफ़ॉर्म** | C-स्तरीय HAL | टाइप किए सीमा अनुबंधों वाला `PlatformBinding` टाइपक्लास और Rust HAL |

## लाइसेंस और तृतीय-पक्ष श्रेय

seLe4n स्वयं GNU General Public License v3.0 या उसके बाद के संस्करण (GPLv3+)
के अंतर्गत लाइसेंस प्राप्त है; पूर्ण पाठ के लिए [`LICENSE`](../../../LICENSE) देखें।
तृतीय-पक्ष बिल्ड निर्भरताएँ (`cc`, `find-msvc-tools`, `shlex`, सभी
`MIT OR Apache-2.0` के अंतर्गत द्वि-लाइसेंस प्राप्त) MIT विकल्प के अंतर्गत उपयोग
की जाती हैं; उनके मूल कॉपीराइट और अनुमति नोटिस
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md) में शब्दशः
पुनः प्रस्तुत किए गए हैं। कर्नेल बाइनरी में रनटाइम पर लिंक किया गया कोई
तृतीय-पक्ष कोड मौजूद नहीं है — HAL `#![no_std]` है और केवल `core::*` का उपयोग
करता है।

---

> यह दस्तावेज़ [English README](../../../README.md) का अनुवाद है।
