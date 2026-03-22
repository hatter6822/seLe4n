# seLe4n 빠른 시작 가이드

이 가이드는 seLe4n 개발 환경을 설정하고, 프로젝트를 빌드하며, 검증 스위트를 실행하는 방법을 안내합니다.

---

🌐 [English](../../../README.md#quick-start) | **한국어**

---

## 필수 조건

### 시스템 요구사항

- **운영체제**: Linux (권장), macOS
- **메모리**: 최소 8GB RAM (Lean 빌드에 필요)
- **디스크**: 최소 5GB 여유 공간
- **Git**: 버전 관리를 위해 필요

### 소프트웨어 의존성

| 소프트웨어 | 버전 | 용도 |
|-----------|------|------|
| **Lean 4** | v4.28.0 | 핵심 언어 및 증명 검사기(proof checker) |
| **Lake** | 0.18.6 | 빌드 시스템 |
| **elan** | 최신 | Lean 툴체인 관리자 |
| **ShellCheck** | 최신 (선택) | 셸 스크립트 린트(lint) |
| **ripgrep** | 최신 (선택) | 테스트 하니스에서 사용 |

## 설치 및 설정

### 1단계: 저장소 클론

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

### 2단계: Lean 툴체인 설치

seLe4n은 환경 설정을 자동화하는 설정 스크립트를 제공합니다:

```bash
# 기본 설치 (빌드 의존성만)
./scripts/setup_lean_env.sh --skip-test-deps

# 전체 설치 (테스트 의존성 포함: shellcheck, ripgrep)
./scripts/setup_lean_env.sh
```

이 스크립트는 다음을 수행합니다:
- `elan`이 설치되어 있지 않으면 설치합니다
- 프로젝트에 필요한 Lean 툴체인(v4.28.0)을 설치합니다
- 필요한 환경 변수를 설정합니다

### 3단계: 프로젝트 빌드

```bash
source ~/.elan/env && lake build
```

첫 빌드는 의존성을 다운로드하고 전체 프로젝트를 컴파일하므로 몇 분이 소요될 수 있습니다. 이후 빌드는 증분(incremental) 빌드로 훨씬 빠릅니다.

### 4단계: 트레이스 하니스 실행

```bash
lake exe sele4n
```

이 명령은 커널 전이(kernel transitions)의 실행 가능한 트레이스를 실행합니다. 출력은 `tests/fixtures/main_trace_smoke.expected`의 예상 결과와 일치해야 합니다.

### 5단계: 검증 스위트 실행

```bash
./scripts/test_smoke.sh
```

이것은 PR 제출 전 필수 최소 검증입니다. 위생 검사, 빌드, 트레이스 검증, 음성 상태 테스트, 문서 동기화를 포함합니다.

## 검증 명령어 상세

seLe4n은 단계별(tiered) 검증 시스템을 사용합니다. 각 단계는 이전 단계를 포함합니다:

### Tier 0+1: 빠른 검증

```bash
./scripts/test_fast.sh
```

- 위생 검사(hygiene checks): 코드 스타일, `sorry`/`axiom` 부재 확인
- 전체 빌드: 모든 모듈이 컴파일되는지 확인
- 의미론적 증명 깊이(semantic proof depth) L-08 검증

### Tier 0-2: 스모크 테스트

```bash
./scripts/test_smoke.sh
```

- Tier 0+1의 모든 검증 포함
- 트레이스 하니스(trace harness) 출력 비교
- 음성 상태 테스트(negative-state tests): 잘못된 입력이 올바르게 거부되는지 확인
- 문서 동기화 검증

### Tier 0-3: 전체 테스트

```bash
./scripts/test_full.sh
```

- Tier 0-2의 모든 검증 포함
- 불변량 표면 앵커(invariant surface anchors) 검증
- Lean `#check` 정확성 검증
- **정리(theorem), 불변량(invariant), 또는 문서 앵커를 변경할 때 필수**

### Tier 0-4: 야간 테스트

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

- Tier 0-3의 모든 검증 포함
- 결정론(determinism) 검증
- 실험적 테스트 포함

## 개별 모듈 빌드

특정 모듈만 빌드하려면 모듈 경로를 지정합니다:

```bash
source ~/.elan/env && lake build <Module.Path>
```

예시:

```bash
# 스케줄러 모듈 빌드
lake build SeLe4n.Kernel.Scheduler.Operations

# IPC 모듈 빌드
lake build SeLe4n.Kernel.IPC.Operations

# Robin Hood 해시 테이블 빌드
lake build SeLe4n.Kernel.RobinHood.Core

# 능력(Capability) 불변량 빌드
lake build SeLe4n.Kernel.Capability.Invariant
```

**중요:** `lake build`(기본 대상)은 `Main.lean`에서 도달 가능한 모듈만 빌드합니다. 새로운 모듈이나 아직 메인 커널에 통합되지 않은 모듈은 반드시 명시적 모듈 경로로 빌드해야 합니다.

## Pre-commit 훅 설치

커밋 전에 자동으로 모듈 빌드 검증과 `sorry` 검사를 수행하는 pre-commit 훅을 설치할 수 있습니다:

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

이 훅은 다음을 수행합니다:
1. 스테이징된 `.lean` 파일을 감지합니다
2. 각 수정된 모듈을 `lake build <Module.Path>`로 빌드합니다
3. 스테이징된 내용에서 `sorry`를 검사합니다
4. 빌드 실패 또는 `sorry`가 발견되면 **커밋을 차단합니다**

## 코드베이스 맵

프로젝트의 기계 판독 가능한 인벤토리를 생성하거나 검증할 수 있습니다:

```bash
# 코드베이스 맵 재생성
./scripts/generate_codebase_map.py --pretty

# 파일 쓰기 없이 검증만
./scripts/generate_codebase_map.py --pretty --check
```

## 문제 해결

### 빌드 실패 시

1. Lean 툴체인 버전을 확인합니다:
   ```bash
   lean --version
   # 예상 출력: leanprover/lean4:v4.28.0
   ```

2. Lake 캐시를 정리하고 재빌드합니다:
   ```bash
   lake clean && lake build
   ```

3. elan 환경이 로드되었는지 확인합니다:
   ```bash
   source ~/.elan/env
   ```

### 테스트 실패 시

1. 실패한 테스트의 출력을 확인합니다 — 각 테스트 스크립트는 실패 원인에 대한 상세한 진단 메시지를 제공합니다.

2. 트레이스 출력이 예상 결과와 다른 경우, `tests/fixtures/main_trace_smoke.expected`와 실제 출력을 비교합니다.

3. 모듈 빌드 실패의 경우, 해당 모듈을 개별적으로 빌드하여 정확한 오류 메시지를 확인합니다:
   ```bash
   lake build SeLe4n.Kernel.<Subsystem>.<Module>
   ```

## 다음 단계

환경 설정이 완료되었다면, 다음 문서를 참고하십시오:

- **일상적인 개발 작업 흐름**: [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
- **기여 가이드**: [CONTRIBUTING.md](CONTRIBUTING.md)
- **전체 핸드북**: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)
- **프로젝트 사양**: [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)

---

> 이 문서는 [English README — Quick Start](../../../README.md#quick-start)의 번역 및 확장입니다.
> 원문과 번역본 사이에 차이가 있는 경우, 영문 원본이 우선합니다.
