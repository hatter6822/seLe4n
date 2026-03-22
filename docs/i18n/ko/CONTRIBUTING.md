# seLe4n 기여 가이드

seLe4n에 기여해 주셔서 감사합니다. seLe4n은 Lean 4로 작성된 기계 검증 증명(machine-checked proofs)을 갖춘 프로덕션 지향 마이크로커널(microkernel)입니다.

---

🌐 [English](../../../CONTRIBUTING.md) | [简体中文](../zh-CN/CONTRIBUTING.md) | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | **한국어** | [العربية](../ar/CONTRIBUTING.md) | [Français](../fr/CONTRIBUTING.md) | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

---

## 라이선스

seLe4n은 [GNU General Public License v3.0 이상](../../../LICENSE)에 따라 라이선스가 부여됩니다. 풀 리퀘스트(pull request)를 제출하거나 이 프로젝트에 코드를 기여함으로써, 귀하의 기여물이 동일한 GPL-3.0 이상 라이선스에 따라 라이선스된다는 데 동의하게 됩니다. 또한 귀하가 이 라이선스 하에서 기여물을 제출할 권리가 있음을 인증합니다.

## 5분 기여자 경로

1. **작업 흐름 + 표준:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **테스트 단계(Testing tiers):** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI 정책:** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **프로젝트 범위 + 작업 스트림:** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **활성 감사 결과:** [`docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md)
6. **작업 스트림 이력:** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

전체 핸드북: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## 개발 환경 설정

### 필수 조건

- **Lean 4 툴체인** (v4.28.0) — `elan`을 통해 관리됩니다
- **Lake 빌드 시스템** (v0.18.6)
- **Git** (버전 관리)
- **ShellCheck** (셸 스크립트 린트용, 선택 사항)

### 설정 단계

```bash
# 1. 저장소 클론
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n

# 2. Lean 툴체인 설치 (elan이 없는 경우)
./scripts/setup_lean_env.sh

# 3. 프로젝트 빌드
source ~/.elan/env && lake build

# 4. 트레이스 하니스 실행
lake exe sele4n

# 5. 스모크 테스트 실행
./scripts/test_smoke.sh
```

## PR 제출 전 필수 검증

```bash
./scripts/test_smoke.sh     # 최소 게이트 (Tier 0-2)
./scripts/test_full.sh      # 정리/불변량 변경 시 필수 (Tier 0-3)
```

### 모듈 빌드 검증 (필수)

**`.lean` 파일을 커밋하기 전에**, 해당 모듈이 컴파일되는지 반드시 확인해야 합니다:

```bash
source ~/.elan/env && lake build <Module.Path>
```

예를 들어, `SeLe4n/Kernel/RobinHood/Bridge.lean`을 수정한 경우:

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build`(기본 대상)만으로는 충분하지 않습니다.** 기본 대상은 `Main.lean`과 테스트 실행 파일에서 도달 가능한 모듈만 빌드합니다. 아직 메인 커널에서 임포트하지 않는 모듈(예: N4 통합 전의 `RobinHood`)은 증명이 깨져 있어도 `lake build`를 통과합니다.

## PR 요구사항

### 체크리스트

- [ ] 작업 스트림 ID 식별 완료
- [ ] 범위가 하나의 일관된 슬라이스(coherent slice)로 제한됨
- [ ] 전이(transitions)가 결정론적(deterministic) — 명시적 성공/실패
- [ ] 불변량/정리(invariant/theorem) 업데이트가 구현 변경과 쌍을 이룸
- [ ] `test_smoke.sh` 통과 (최소); 정리 변경 시 `test_full.sh`
- [ ] 문서가 동일 PR에서 동기화됨
- [ ] 웹사이트 연결 경로가 이름 변경 또는 삭제되지 않음 (`scripts/website_link_manifest.txt` 참조)

### 코딩 규칙

#### sorry/axiom 금지

프로덕션 증명 표면(proof surface)에서 `sorry`와 `axiom`은 금지됩니다. 추적 대상인 예외는 반드시 `TPI-D*` 어노테이션(annotation)을 포함해야 합니다.

#### 결정론적 의미론(Deterministic semantics)

모든 전이(transition)는 명시적인 성공/실패를 반환해야 합니다. 비결정론적 분기(non-deterministic branch)를 절대 도입하지 마십시오.

#### 타입이 지정된 식별자(Typed identifiers)

`ThreadId`, `ObjId`, `CPtr`, `Slot`, `DomainId` 등은 래퍼 구조체(wrapper structure)이며 `Nat` 별칭이 아닙니다. 명시적인 `.toNat`/`.ofNat`를 사용하십시오.

#### Operations/Invariant 분리

각 커널 서브시스템은 전이를 위한 `Operations.lean`과 증명을 위한 `Invariant.lean`으로 분리됩니다. 이 분리를 유지하십시오.

#### 내부 우선 명명(Internal-first naming)

정리/함수/정의 이름은 의미론(semantics)을 기술해야 합니다 (상태 업데이트 형태, 보존된 불변량, 전이 경로). 작업 스트림 ID(`WS-*`, `wsH*` 등)를 식별자 이름에 인코딩하지 마십시오.

## 문서 업데이트

동작, 정리, 또는 작업 스트림 상태를 변경할 때는 동일한 PR에서 다음을 업데이트하십시오:

1. `README.md` — `docs/codebase_map.json`의 메트릭 동기화 (`readme_sync` 키)
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. 영향을 받는 GitBook 챕터 — 정규 루트 문서가 GitBook보다 우선
5. `docs/CLAIM_EVIDENCE_INDEX.md` (주장이 변경된 경우)
6. `docs/WORKSTREAM_HISTORY.md` (작업 스트림 상태가 변경된 경우)
7. `docs/codebase_map.json` 재생성 (Lean 소스가 변경된 경우)

## 테스트 단계

seLe4n은 4단계 검증 시스템을 사용합니다:

| 단계 | 명령어 | 내용 |
|------|--------|------|
| **Tier 0+1** | `./scripts/test_fast.sh` | 위생 검사(hygiene) + 빌드 |
| **Tier 0-2** | `./scripts/test_smoke.sh` | + 트레이스 + 음성 상태 + 문서 동기화 |
| **Tier 0-3** | `./scripts/test_full.sh` | + 불변량 표면 앵커 + Lean #check |
| **Tier 0-4** | `./scripts/test_nightly.sh` | + 야간 결정론 |

## 이슈 보고

버그를 보고하거나 기능을 제안할 때는 다음 정보를 포함해 주십시오:

- **seLe4n 버전** (`git describe --tags`)
- **Lean 툴체인 버전** (`lean --version`)
- **재현 단계** (해당하는 경우)
- **예상 동작과 실제 동작**

## 보안 취약점

보안 취약점을 발견한 경우, 공개 이슈 대신 관리자에게 직접 보고해 주십시오. 자세한 내용은 영문 [CONTRIBUTING.md](../../../CONTRIBUTING.md)를 참고하십시오.

---

> 이 문서는 [English CONTRIBUTING.md](../../../CONTRIBUTING.md)의 번역입니다.
> 원문과 번역본 사이에 차이가 있는 경우, 영문 원본이 우선합니다.
