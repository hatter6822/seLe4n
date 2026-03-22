# seLe4n त्वरित प्रारंभ मार्गदर्शिका (Quick Start Guide)

यह मार्गदर्शिका आपको seLe4n को शीघ्रता से स्थापित करने, निर्माण करने और चलाने में सहायता करती है। seLe4n एक उत्पादन-उन्मुख सूक्ष्म नाभिक (production-oriented microkernel) है जो Lean 4 में मशीन-जाँचित प्रमाणों (machine-checked proofs) के साथ लिखा गया है।

---

🌐 [English](../../../README.md#quick-start) | [简体中文](../zh-CN/QUICKSTART.md) | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | **हिन्दी**

---

## पूर्वापेक्षाएँ (Prerequisites)

- **ऑपरेटिंग सिस्टम (Operating System):** Linux (अनुशंसित), macOS, या WSL2
- **Git:** संस्करण 2.x या नवीनतर
- **इंटरनेट कनेक्शन:** Lean टूलचेन डाउनलोड के लिए

Lean 4 टूलचेन (`elan` और `lake`) स्वचालित रूप से सेटअप स्क्रिप्ट द्वारा स्थापित होते हैं — किसी पूर्व-स्थापना (pre-installation) की आवश्यकता नहीं है।

## चरण 1: रिपॉजिटरी क्लोन करें (Clone the Repository)

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## चरण 2: परिवेश स्थापना (Environment Setup)

सेटअप स्क्रिप्ट Lean टूलचेन (`elan`), Lake बिल्ड सिस्टम, और आवश्यक निर्भरताएँ (dependencies) स्थापित करती है:

```bash
# मूल स्थापना (परीक्षण निर्भरताओं के बिना)
./scripts/setup_lean_env.sh --skip-test-deps

# पूर्ण स्थापना (shellcheck, ripgrep सहित)
./scripts/setup_lean_env.sh
```

स्थापना के बाद, Lean परिवेश को सक्रिय करें:

```bash
source ~/.elan/env
```

## चरण 3: परियोजना का निर्माण करें (Build the Project)

```bash
lake build
```

यह सभी कर्नेल मॉड्यूल (kernel modules), परीक्षण सुइट्स (test suites), और निष्पादनयोग्य (executables) संकलित करता है। प्रथम निर्माण में कुछ मिनट लग सकते हैं क्योंकि Lean निर्भरताएँ (Lean dependencies) डाउनलोड और संकलित होती हैं।

### विशिष्ट मॉड्यूल का निर्माण (Building Specific Modules)

यदि आप किसी विशिष्ट मॉड्यूल पर कार्य कर रहे हैं, तो आप केवल उसे निर्मित कर सकते हैं:

```bash
lake build SeLe4n.Kernel.Scheduler.Operations
lake build SeLe4n.Kernel.IPC.Operations
lake build SeLe4n.Kernel.Capability.Invariant
```

**महत्वपूर्ण:** कमिट करने से पहले सदैव विशिष्ट मॉड्यूल निर्माण सत्यापित करें। डिफ़ॉल्ट `lake build` केवल `Main.lean` से पहुँच योग्य मॉड्यूल बनाता है।

## चरण 4: ट्रेस हार्नेस चलाएँ (Run the Trace Harness)

```bash
lake exe sele4n
```

यह निष्पादनयोग्य ट्रेस हार्नेस (executable trace harness) चलाता है, जो कर्नेल संक्रमणों (kernel transitions) का प्रदर्शन करता है और प्रमाणित करता है कि सभी अपेक्षित व्यवहार (expected behaviors) सही हैं। आउटपुट `tests/fixtures/main_trace_smoke.expected` से मेल खाना चाहिए।

## चरण 5: परीक्षण चलाएँ (Run Tests)

seLe4n एक स्तरित परीक्षण प्रणाली (tiered testing system) का उपयोग करता है:

### स्तरित परीक्षण (Tiered Tests)

```bash
# टियर 0 + 1: स्वच्छता जाँच + निर्माण
./scripts/test_fast.sh

# टियर 0-2: + ट्रेस + नकारात्मक-स्थिति परीक्षण (अनुशंसित न्यूनतम)
./scripts/test_smoke.sh

# टियर 0-3: + अपरिवर्तनीय सतह एंकर + Lean #check शुद्धता
./scripts/test_full.sh

# टियर 0-4: रात्रिकालीन नियतिवाद परीक्षण
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

### कब कौन सा परीक्षण चलाएँ (When to Run Which Test)

| परिस्थिति | न्यूनतम परीक्षण |
|-----------|----------------|
| कोई भी PR प्रस्तुत करने से पहले | `test_smoke.sh` |
| प्रमेय (theorem) या अपरिवर्तनीय (invariant) बदलने पर | `test_full.sh` |
| दस्तावेज़ीकरण एंकर बदलने पर | `test_full.sh` |
| नियमित विकास (regular development) | `test_fast.sh` |

## चरण 6: प्री-कमिट हुक स्थापित करें (Install Pre-commit Hook)

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

यह हुक (hook) प्रत्येक कमिट से पहले स्वचालित रूप से:
- संशोधित `.lean` फ़ाइलों के मॉड्यूल निर्माण का सत्यापन करता है
- स्टेज की गई सामग्री में `sorry` की जाँच करता है
- विफलता पर कमिट को अवरोधित करता है

## परियोजना संरचना अवलोकन (Project Structure Overview)

```
seLe4n/
├── SeLe4n/                    # मुख्य कर्नेल स्रोत कोड (main kernel source)
│   ├── Prelude.lean           # प्रकारित पहचानकर्ता (typed identifiers), मोनैड आधार
│   ├── Machine.lean           # मशीन स्थिति आदिम (machine state primitives)
│   ├── Model/                 # कर्नेल ऑब्जेक्ट और स्थिति प्रतिनिधित्व (state representation)
│   ├── Kernel/                # कर्नेल उपप्रणालियाँ (subsystems)
│   │   ├── Scheduler/         # शेड्यूलर (EDF + प्राथमिकता)
│   │   ├── Capability/        # क्षमता स्थान (CSpace) संचालन
│   │   ├── IPC/               # अंतर-प्रक्रिया संचार (inter-process communication)
│   │   ├── Lifecycle/         # ऑब्जेक्ट जीवनचक्र (object lifecycle)
│   │   ├── Service/           # सेवा समन्वय (service orchestration)
│   │   ├── InformationFlow/   # सूचना प्रवाह नियंत्रण (information flow control)
│   │   ├── RobinHood/         # Robin Hood हैश टेबल (सत्यापित)
│   │   ├── RadixTree/         # रेडिक्स ट्री (CNode फ्लैट ऐरे)
│   │   ├── FrozenOps/         # फ्रोज़न कर्नेल संचालन (frozen kernel operations)
│   │   ├── Architecture/      # VSpace, रजिस्टर डिकोड
│   │   ├── CrossSubsystem.lean # क्रॉस-उपप्रणाली अपरिवर्तनीय
│   │   └── API.lean           # एकीकृत सार्वजनिक API
│   ├── Platform/              # प्लेटफ़ॉर्म बाइंडिंग (Sim, RPi5)
│   └── Testing/               # परीक्षण हार्नेस (test harness)
├── tests/                     # परीक्षण सुइट्स और फिक्सचर
├── Main.lean                  # निष्पादनयोग्य प्रवेश बिंदु (executable entry point)
├── docs/                      # दस्तावेज़ीकरण
└── scripts/                   # निर्माण और सत्यापन स्क्रिप्ट
```

## सामान्य कार्यप्रवाह (Common Workflows)

### नई सुविधा विकसित करना (Developing a New Feature)

```bash
# 1. नई शाखा बनाएँ
git checkout -b feature/my-feature

# 2. परिवर्तन करें
# ... अपनी .lean फ़ाइलें संपादित करें ...

# 3. विशिष्ट मॉड्यूल का निर्माण सत्यापित करें
source ~/.elan/env && lake build SeLe4n.Kernel.MyModule

# 4. परीक्षण चलाएँ
./scripts/test_smoke.sh

# 5. कमिट और PR प्रस्तुत करें
git add <modified-files>
git commit -m "विवरणात्मक कमिट संदेश"
```

### प्रमाण डिबगिंग (Debugging Proofs)

यदि कोई प्रमाण (proof) विफल हो रहा है:

```bash
# विशिष्ट मॉड्यूल बनाएँ और त्रुटियाँ देखें
lake build SeLe4n.Kernel.Capability.Invariant 2>&1 | head -50

# पूर्ण निर्माण लॉग के लिए
lake build 2>&1 > /tmp/build.log
```

### कोडबेस मानचित्र पुनः उत्पन्न करना (Regenerating the Codebase Map)

```bash
./scripts/generate_codebase_map.py --pretty           # पुनः उत्पन्न करें
./scripts/generate_codebase_map.py --pretty --check    # बिना लिखे सत्यापित करें
```

## सहायता और संसाधन (Help and Resources)

| संसाधन | विवरण |
|--------|-------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | विस्तृत विकास मार्गदर्शिका |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | पूर्ण परियोजना पुस्तिका (handbook) |
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | परियोजना विशिष्टता (specification) |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | परीक्षण ढाँचा (testing framework) योजना |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | योगदान दिशानिर्देश (contribution guidelines) |

## समस्या निवारण (Troubleshooting)

### Lean टूलचेन स्थापित नहीं हो रहा (Lean Toolchain Not Installing)

```bash
# elan को मैन्युअली स्थापित करें
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
source ~/.elan/env

# सही संस्करण सत्यापित करें
lean --version   # v4.28.0 दिखना चाहिए
lake --version
```

### निर्माण विफलताएँ (Build Failures)

```bash
# निर्भरताएँ ताज़ा करें
lake update

# स्वच्छ निर्माण
lake clean && lake build
```

### परीक्षण विफलताएँ (Test Failures)

```bash
# ट्रेस आउटपुट सत्यापित करें
lake exe sele4n > /tmp/actual_output.txt
diff tests/fixtures/main_trace_smoke.expected /tmp/actual_output.txt
```

---

> यह दस्तावेज़ [English README](../../../README.md) के त्वरित प्रारंभ अनुभाग का विस्तारित हिन्दी अनुवाद है।
