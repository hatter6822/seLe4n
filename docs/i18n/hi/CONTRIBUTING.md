# seLe4n में योगदान (Contributing to seLe4n)

seLe4n में योगदान देने के लिए धन्यवाद — Lean 4 में मशीन-जाँचित प्रमाणों (machine-checked proofs) के साथ लिखा गया एक उत्पादन-उन्मुख सूक्ष्म नाभिक (production-oriented microkernel)।

---

🌐 [English](../../../CONTRIBUTING.md) | **हिन्दी**

---

## लाइसेंस (License)

seLe4n [GNU General Public License v3.0 या बाद के संस्करण](../../../LICENSE) के अंतर्गत लाइसेंस प्राप्त है। पुल अनुरोध (pull request) प्रस्तुत करके या इस परियोजना में कोड का योगदान देकर, आप सहमत होते हैं कि आपके योगदान उसी GPL-3.0-or-later लाइसेंस के अंतर्गत लाइसेंस प्राप्त होंगे। आप यह भी प्रमाणित करते हैं कि आपके पास इस लाइसेंस के अंतर्गत योगदान प्रस्तुत करने का अधिकार है।

## 5-मिनट योगदानकर्ता पथ (5-Minute Contributor Path)

1. **कार्यप्रवाह + मानक (Workflow + standards):** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **परीक्षण स्तर (Testing tiers):** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI नीति (CI policy):** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **परियोजना दायरा + कार्यधाराएँ (Project scope + workstreams):** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **कार्यधारा इतिहास (Workstream history):** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

पूर्ण पुस्तिका (handbook): [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## PR खोलने से पहले आवश्यक सत्यापन (Required Validation Before Opening a PR)

```bash
./scripts/test_smoke.sh     # न्यूनतम द्वार (minimum gate) (टियर 0-2)
./scripts/test_full.sh      # प्रमेय/अपरिवर्तनीय परिवर्तनों के लिए आवश्यक (टियर 0-3)
```

कोई भी PR प्रस्तुत करने से पहले कम से कम `test_smoke.sh` चलाएँ। यदि आपने प्रमेयों (theorems) या अपरिवर्तनीयों (invariants) में परिवर्तन किया है, तो `test_full.sh` चलाएँ।

## PR आवश्यकताएँ (PR Requirements)

- उन्नत की गई कार्यधारा ID (workstream ID) की पहचान करें
- दायरा (scope) एक सुसंगत खंड (coherent slice) तक सीमित रखें
- संक्रमण (transitions) नियतात्मक (deterministic) होने चाहिए (स्पष्ट सफलता/विफलता)
- अपरिवर्तनीय/प्रमेय (invariant/theorem) अद्यतन कार्यान्वयन परिवर्तनों के साथ युग्मित (paired) होने चाहिए
- दस्तावेज़ीकरण (documentation) उसी PR में समन्वयित करें
- पूर्ण चेकलिस्ट [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) में देखें

## कोड शैली और परंपराएँ (Code Style and Conventions)

### प्रकारित पहचानकर्ता (Typed Identifiers)

`ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId` आदि आवरण संरचनाएँ (wrapper structures) हैं, `Nat` उपनाम (aliases) नहीं। स्पष्ट `.toNat`/`.ofNat` का उपयोग करें।

### Operations/Invariant विभाजन (Split)

प्रत्येक कर्नेल उपप्रणाली (kernel subsystem) में `Operations.lean` (संक्रमण/transitions) और `Invariant.lean` (प्रमाण/proofs) अलग-अलग होते हैं। इस विभाजन को बनाए रखें।

### शून्य sorry/axiom नीति (Zero sorry/axiom Policy)

उत्पादन प्रमाण सतह (production proof surface) में `sorry` और `axiom` वर्जित हैं। ट्रैक किए गए अपवादों (tracked exceptions) में `TPI-D*` एनोटेशन होना चाहिए।

### नियतात्मक शब्दार्थ (Deterministic Semantics)

सभी संक्रमण स्पष्ट सफलता/विफलता लौटाते हैं। कभी भी अनियतात्मक शाखाएँ (non-deterministic branches) प्रस्तुत न करें।

### नामकरण परंपरा (Naming Convention)

प्रमेय/फ़ंक्शन/परिभाषा (theorem/function/definition) के नाम शब्दार्थ (semantics) का वर्णन करने चाहिए (स्थिति अद्यतन आकार, संरक्षित अपरिवर्तनीय, संक्रमण पथ)। पहचानकर्ता नामों में कार्यधारा ID (`WS-*`, `wsH*`, आदि) एन्कोड **न करें**।

## मॉड्यूल निर्माण सत्यापन (Module Build Verification)

**किसी भी `.lean` फ़ाइल को कमिट करने से पहले**, आपको यह सत्यापित करना **अनिवार्य** है कि विशिष्ट मॉड्यूल संकलित होता है:

```bash
source ~/.elan/env && lake build <Module.Path>
```

उदाहरण के लिए, यदि आपने `SeLe4n/Kernel/RobinHood/Bridge.lean` को संशोधित किया:
```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build` (डिफ़ॉल्ट लक्ष्य) पर्याप्त नहीं है।** डिफ़ॉल्ट लक्ष्य केवल `Main.lean` और परीक्षण निष्पादनयोग्यों (test executables) से पहुँच योग्य मॉड्यूल ही बनाता है।

## प्री-कमिट हुक स्थापना (Pre-commit Hook Installation)

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

हुक (hook) यह करता है:
1. स्टेज की गई `.lean` फ़ाइलों का पता लगाता है
2. प्रत्येक संशोधित मॉड्यूल को `lake build <Module.Path>` के माध्यम से बनाता है
3. स्टेज की गई सामग्री में `sorry` की जाँच करता है
4. यदि कोई निर्माण विफल होता है या sorry मिलता है तो **कमिट को अवरोधित** करता है

`--no-verify` के साथ हुक को बायपास **न करें**।

## दस्तावेज़ीकरण नियम (Documentation Rules)

व्यवहार, प्रमेय, या कार्यधारा स्थिति बदलते समय, उसी PR में अद्यतन करें:

1. `README.md` — `docs/codebase_map.json` से मेट्रिक्स समन्वय
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. प्रभावित GitBook अध्याय — मूल (canonical) रूट दस्तावेज़ GitBook पर प्राथमिकता रखते हैं
5. `docs/CLAIM_EVIDENCE_INDEX.md` यदि दावे (claims) बदलते हैं
6. `docs/WORKSTREAM_HISTORY.md` यदि कार्यधारा स्थिति बदलती है
7. यदि Lean स्रोत बदले तो `docs/codebase_map.json` पुनः उत्पन्न करें

## भेद्यता रिपोर्टिंग (Vulnerability Reporting)

यदि आप किसी ऐसी सॉफ़्टवेयर भेद्यता (vulnerability) की खोज करते हैं जो CVE (Common Vulnerabilities and Exposures) पदनाम (designation) की गारंटी दे सकती है, तो कृपया तुरंत अनुरक्षकों (maintainers) को रिपोर्ट करें। इसमें शामिल हैं:

- इस परियोजना के कोड में तर्क त्रुटियाँ (logic errors)
- निर्भरताओं और टूलचेन में ज्ञात या संदिग्ध भेद्यताएँ
- निर्माण और CI अवसंरचना (infrastructure) में असुरक्षित पैटर्न
- मॉडल/विशिष्टता अंतराल (specification gaps) जो सुरक्षा-प्रासंगिक व्यवहार को पकड़ने में विफल रहते हैं

## PR चेकलिस्ट (PR Checklist)

- [ ] कार्यधारा ID (Workstream ID) पहचानी गई
- [ ] दायरा एक सुसंगत खंड है
- [ ] संक्रमण स्पष्ट और नियतात्मक हैं
- [ ] अपरिवर्तनीय/प्रमेय अद्यतन कार्यान्वयन के साथ युग्मित हैं
- [ ] `test_smoke.sh` पास होता है (न्यूनतम); प्रमेय परिवर्तनों के लिए `test_full.sh`
- [ ] दस्तावेज़ीकरण समन्वयित है
- [ ] कोई भी वेबसाइट-लिंक पथ नाम-परिवर्तित या हटाया नहीं गया (`scripts/website_link_manifest.txt` देखें)

---

> यह दस्तावेज़ [English CONTRIBUTING.md](../../../CONTRIBUTING.md) का अनुवाद है।
