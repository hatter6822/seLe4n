# License Review Report (Updated)

Date: 2026-02-18  
Repository: `seLe4n`  
Reviewer: Codex (GPT-5.2-Codex)

> Important: This is a technical compliance review, not legal advice.

## 1) Executive summary

I performed a repository-wide licensing review and a dependency/tooling license review covering:
- all tracked source and documentation files,
- declared build dependencies,
- CI/public-action dependencies and tool bootstrap sources.

### Bottom line

- **No direct code-license conflict was found in this repository’s tracked code and docs.**
- The project’s own distribution posture is consistent with the root **MIT** license.
- **Operational legal watchpoint:** one CI action (`gitleaks/gitleaks-action`) uses a proprietary EULA rather than a standard OSS license; this is not a redistribution conflict in the repository code itself, but it can create usage/commercial-policy constraints for CI operations.

## 2) Scope reviewed

### 2.1 Tracked repository files

All tracked files (`git ls-files`) were inventoried.

For conflict-marker counts, I used a primary scan that excludes `docs/licensing_research/` so report text itself does not contaminate marker counts.

- Total tracked files reviewed: **120**.

### 2.2 Build/dependency declarations

- `lake-manifest.json`
- `lakefile.toml`
- `lean-toolchain`

### 2.3 CI/toolchain and public-code surfaces

- `.github/workflows/*.yml`
- `scripts/setup_lean_env.sh`

## 3) Methodology and command evidence

```bash
# 1) File inventory / total scope
git ls-files
git ls-files | wc -l

# 2) Repository-wide marker scan (strong license signals, excluding licensing reports)
python3 - <<'PY'
import subprocess,re
files=[f for f in subprocess.check_output(['git','ls-files'],text=True).splitlines() if not f.startswith('docs/licensing_research/')]
checks={
'gpl_family':re.compile(r'\b(?:AGPL|GPL|LGPL)\b',re.I),
'mpl':re.compile(r'\bMPL(?:\s*2\.0|-2\.0)?\b|Mozilla Public License',re.I),
'epl':re.compile(r'\bEPL(?:\s*2\.0|-2\.0)?\b|Eclipse Public License',re.I),
'apache':re.compile(r'\bApache(?:\s+License)?(?:\s*2\.0)?\b',re.I),
'bsd':re.compile(r'\bBSD(?:[- ]?\d?-Clause)?\b',re.I),
'mit':re.compile(r'\bMIT\b|MIT License',re.I),
'spdx':re.compile(r'SPDX-License-Identifier',re.I),
}
for name,pat in checks.items():
    hits=[]
    for f in files:
        txt=open(f,encoding='utf-8').read()
        if pat.search(txt):
            hits.append(f)
    print(name,len(hits))
    for f in hits[:8]:
        print(' ',f)
PY

# 3) Provenance-marker search
rg -n "copied from|borrowed from|vendored|upstream source excerpt|SPDX-License-Identifier" . --glob "!docs/licensing_research/**"

# 4) Dependency declarations
cat lake-manifest.json
cat lakefile.toml
cat lean-toolchain

# 5) CI/action and bootstrap surfaces
rg -n "uses:|curl|wget|git clone|lake add|elan" .github/workflows scripts/setup_lean_env.sh

# 6) Public dependency license lookup (GitHub API)
python3 - <<'PY'
import json,urllib.request
repos=[
'actions/cache','actions/checkout','actions/github-script','actions/upload-artifact',
'aquasecurity/trivy-action','github/codeql-action','gitleaks/gitleaks-action',
'leanprover/elan','leanprover/lean4'
]
for r in repos:
    url=f'https://api.github.com/repos/{r}/license'
    req=urllib.request.Request(url,headers={'Accept':'application/vnd.github+json','User-Agent':'codex'})
    with urllib.request.urlopen(req,timeout=20) as resp:
        data=json.load(resp)
    print(r, data.get('license',{}).get('spdx_id'), data.get('html_url'))
PY

# 7) Inspect non-OSI action license text
curl -fsSL https://raw.githubusercontent.com/gitleaks/gitleaks-action/master/LICENSE.txt | sed -n '1,120p'
```

## 4) Findings

## 4.1 Project license baseline

- Root `LICENSE` file is present and is MIT.
- Core project documentation references this posture.

**Result:** ✅ Project baseline license is explicit and permissive.

## 4.2 Full tracked-file conflict scan (repository contents)

The conflict-focused scan (excluding `docs/licensing_research/*`) found:

- `GPL/LGPL/AGPL`: **0 files**
- `MPL`: **0 files**
- `EPL`: **0 files**
- `Apache`: **0 files**
- `BSD`: **0 files**
- `SPDX-License-Identifier`: **0 files**

MIT markers appear in expected places (primarily root `LICENSE` plus historical docs).

**Result:** ✅ No textual evidence of conflicting copyleft/restrictive license headers in tracked repository files.

## 4.3 Provenance markers

A direct search for provenance-risk-style markers (`copied from`, `borrowed from`, `vendored`, `upstream source excerpt`) did not identify any in-tree code-copy attribution blocks that suggest imported third-party source files.

**Result:** ✅ No provenance-risk markers indicating copied public code were identified in tracked files.

## 4.4 Declared build dependencies

- `lake-manifest.json` contains `"packages": []`.
- `lakefile.toml` declares local lib/executables only.

**Result:** ✅ No declared third-party Lean package dependency conflict at present.

## 4.5 Public code and CI/tooling license surfaces

GitHub Action / tool license lookups:

| Component | Reported license | Compatibility posture with MIT project |
|---|---|---|
| `actions/checkout` | MIT | Compatible |
| `actions/cache` | MIT | Compatible |
| `actions/upload-artifact` | MIT | Compatible |
| `actions/github-script` | MIT | Compatible |
| `github/codeql-action` | MIT | Compatible |
| `aquasecurity/trivy-action` | Apache-2.0 | Compatible (notice/patent terms are permissive) |
| `leanprover/elan` | Apache-2.0 | Compatible for tool use |
| `leanprover/lean4` | Apache-2.0 | Compatible for tool use |
| `gitleaks/gitleaks-action` | Non-OSI EULA (`NOASSERTION`) | **Policy watchpoint** |

### Specific watchpoint: `gitleaks/gitleaks-action`

The reviewed license text is a commercial EULA with use constraints and license-key terms (organization-account use conditions). This does **not** automatically contaminate the repository’s MIT source license, but it can impose operational/commercial obligations on CI use.

**Result:** ⚠️ No in-repo source conflict, but CI legal-policy review is advisable for this action.

## 5) Conflict analysis conclusion

### 5.1 Distribution conflict (repository code)

No conflict identified. The repository’s tracked source/doc content remains consistent with MIT distribution.

### 5.2 Operational/legal risk (tooling)

Primary residual risk is not source-code relicensing conflict; it is **CI service/license compliance** for `gitleaks/gitleaks-action` terms in environments that may require paid licensing.

## 6) Recommended remediations

1. Keep project code/docs under current MIT baseline unless intentional relicensing is approved.
2. Add a lightweight `THIRD_PARTY_TOOLS_LICENSES.md` inventory documenting CI/action licenses.
3. For `gitleaks/gitleaks-action`, choose one:
   - confirm policy acceptance and any needed license key arrangements, or
   - replace with an OSS-licensed scanning path if legal/commercial constraints are undesirable.
4. Re-run this review whenever:
   - a new GitHub Action is introduced,
   - `lake-manifest.json` gains packages,
   - external code snippets are imported.

## 7) Requested file placement confirmation

✅ Existing review file is located at:
- `docs/licensing_research/LICENSE_REVIEW.md`

✅ Updated report file is located at:
- `docs/licensing_research/LICENSE_REVIEW_UPDATED.md`
