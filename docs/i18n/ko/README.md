<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n 로고" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.18.6-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Lean 4로 작성된 기계 검증 증명(machine-checked proofs)을 갖춘 마이크로커널로,
  <a href="https://sel4.systems">seL4</a> 아키텍처에서 영감을 받았습니다.
  첫 번째 하드웨어 대상: <strong>Raspberry Pi 5</strong>.
</p>

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | [日本語](../ja/README.md) | **한국어** | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## seLe4n이란?

seLe4n은 Lean 4로 처음부터 설계된 마이크로커널(microkernel)입니다. 모든 커널 전이(kernel transition)는 실행 가능한 순수 함수(pure function)입니다. 모든 불변량(invariant)은 Lean 타입 검사기(type-checker)를 통해 기계적으로 검증됩니다 — `sorry` 제로, `axiom` 제로. 전체 증명 표면(proof surface)은 인정된 증명(admitted proof) 없이 네이티브 코드로 컴파일됩니다.

본 프로젝트는 능력 기반 보안 모델(capability-based security model)을 활용하면서 다른 마이크로커널 대비 혁신적인 아키텍처 개선을 도입합니다:

- **O(1) 해시 기반 커널 핫 패스(hot path)** — 모든 객체 저장소, 실행 큐, CNode 슬롯, VSpace 매핑, IPC 큐가 형식 검증된 `RHTable`/`RHSet`(기계 검증 불변량을 갖춘 Robin Hood 해시 테이블, 상태에 `Std.HashMap`/`Std.HashSet` 제로)을 사용합니다
- **서비스 오케스트레이션 레이어(Service orchestration layer)** — 결정론적 부분 실패 의미론(deterministic partial-failure semantics)을 갖춘 컴포넌트 생명주기 및 의존성 관리
- **노드 안정 능력 파생 트리(Node-stable capability derivation tree)** — `childMap` + `parentMap` RHTable 인덱스로 O(1) 슬롯 전송, 폐기(revocation), 부모 조회, 자손 순회 지원
- **침입형 이중 큐 IPC(Intrusive dual-queue IPC)** — 스레드별 `queuePrev`/`queuePPrev`/`queueNext` 링크로 O(1) 삽입, 삭제, 큐 중간 제거 지원
- **매개변수화된 N-도메인 정보 흐름(Information-flow) 프레임워크** — 구성 가능한 흐름 정책으로 레거시 기밀성/무결성 레이블을 일반화(seL4의 이진 파티션을 넘어선)
- **EDF + 우선순위 스케줄링** — 디스패치 시 디큐 의미론, TCB별 레지스터 컨텍스트와 인라인 컨텍스트 스위치, 우선순위 버킷 `RunQueue`, 도메인 인식 파티셔닝

## 현재 상태

| 속성 | 값 |
|------|-----|
| **버전** | `0.18.6` |
| **Lean 툴체인** | `v4.28.0` |
| **프로덕션 Lean LoC** | 55,499 (98개 파일) |
| **테스트 Lean LoC** | 7,309 (10개 테스트 스위트) |
| **증명된 선언** | 1,686개 theorem/lemma 선언 (sorry/axiom 제로) |
| **대상 하드웨어** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **최신 감사** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — 전체 커널 + Rust 코드베이스 사전 릴리스 감사 |
| **코드베이스 맵** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계 판독 가능한 선언 인벤토리 |

지표는 `./scripts/generate_codebase_map.py`에 의해 코드베이스에서 파생되며,
`readme_sync` 키 아래 [`docs/codebase_map.json`](../../../docs/codebase_map.json)에
저장됩니다.

## 빠른 시작

```bash
./scripts/setup_lean_env.sh   # Lean 툴체인 설치
lake build                     # 모든 모듈 컴파일
lake exe sele4n                # 트레이스 하니스 실행
./scripts/test_smoke.sh        # 검증 (위생 + 빌드 + 트레이스 + 음성 상태 + 문서 동기화)
```

자세한 설정 안내는 [빠른 시작 가이드](QUICKSTART.md)를 참고하십시오.

## 온보딩 경로

프로젝트에 처음이신가요? 다음 순서로 읽어보시기 바랍니다:

1. **이 README** — 프로젝트 개요, 아키텍처, 소스 레이아웃
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — 일상적인 작업 흐름, 검증 루프, PR 체크리스트
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — 전체 핸드북 (아키텍처 심층 분석, 증명, 하드웨어 경로)
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계 판독 가능한 모듈 및 선언 인벤토리

작업 스트림(workstream) 계획 및 이력은 [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)를 참고하십시오.

## 프로젝트 문서

| 문서 | 용도 |
|------|------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | 프로젝트 사양 및 마일스톤 |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | seL4 참조 의미론 |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | 일상적인 작업 흐름, 검증 루프, PR 체크리스트 |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | 단계별 테스트 게이트 및 CI 계약 |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | 전체 작업 스트림 이력, 로드맵, 감사 계획 색인 |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | 전체 핸드북 (아키텍처, 설계, 증명, 하드웨어 경로) |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | 기계 판독 가능한 코드베이스 인벤토리 (README와 동기화) |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | 기여 방법 및 PR 요구사항 |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | 버전 이력 |

## 검증 명령어

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1 (위생 검사 + 빌드, 의미론적 증명 깊이 L-08)
./scripts/test_smoke.sh     # + Tier 2 (트레이스 + 음성 상태 + 문서 동기화)
./scripts/test_full.sh      # + Tier 3 (불변량 표면 앵커 + Lean #check 정확성)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4 (야간 결정론)
```

PR을 제출하기 전에 최소한 `test_smoke.sh`를 실행하십시오. 정리(theorem), 불변량(invariant),
또는 문서 앵커를 변경할 때는 `test_full.sh`를 실행하십시오.

## 아키텍처

seLe4n은 계층화된 계약(layered contracts)으로 구성되어 있으며, 각 계층은 실행 가능한 전이(executable transitions)와 기계 검증된 불변량 보존 증명(invariant preservation proofs)을 갖추고 있습니다:

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│   Scheduler  │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│          Platform  (Contract, Sim, RPi5)  ← H3-prep 바인딩            │
└──────────────────────────────────────────────────────────────────────┘
```

각 커널 서브시스템은 **Operations/Invariant 분리** 패턴을 따릅니다: 전이(transitions)는
`Operations.lean`에, 증명(proofs)은 `Invariant.lean`에 위치합니다. 통합된
`apiInvariantBundle`이 모든 서브시스템 불변량을 단일 증명 의무(proof obligation)로
집합합니다.

## seL4와의 비교

| 기능 | seL4 | seLe4n |
|------|------|--------|
| **IPC 메커니즘** | 단일 연결 리스트 엔드포인트 큐 | `queuePPrev` 백 포인터를 갖춘 침입형 이중 큐로 O(1) 큐 중간 제거 지원 |
| **정보 흐름** | 이진 고/저 파티션 | N-도메인 구성 가능한 흐름 정책 (레거시 기밀성 × 무결성 레이블을 일반화) |
| **서비스 관리** | 커널에 없음 | 의존성 그래프와 DFS 순환 탐지를 갖춘 일급 서비스 오케스트레이션 |
| **능력 파생(Capability derivation)** | 연결 리스트 자식을 갖춘 CDT | O(1) 자식 조회를 위한 `childMap` HashMap |
| **스케줄러** | 플랫 우선순위 큐 | 인라인 `maxPriority` 추적과 EDF를 갖춘 우선순위 버킷 `RunQueue` |
| **VSpace** | 하드웨어 페이지 테이블 | W^X 강제를 갖춘 `HashMap VAddr (PAddr x PagePermissions)` |
| **증명 방법론** | Isabelle/HOL, 사후(post-hoc) | Lean 4 타입 검사기, 증명이 전이와 동일 위치(co-located) |
| **플랫폼 추상화** | C 수준 HAL | 타입이 지정된 경계 계약을 갖춘 `PlatformBinding` 타입클래스 |

## 다음 단계

현재 우선순위와 전체 작업 스트림 이력은
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)에서 관리됩니다.
요약:

- **WS-R** — 종합 감사 개선(Comprehensive Audit Remediation) (8단계, R1–R8, 111개 하위 작업). [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md)의 82개 발견 사항을 모두 다룹니다. R1–R7 완료 (v0.18.0–v0.18.6), R8 진행 중. 계획: [`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md).
- **Raspberry Pi 5 하드웨어 바인딩** — ARMv8 페이지 테이블 워크, GIC-400 인터럽트 라우팅, 부트 시퀀스 (RPi5 플랫폼 계약은 WS-H15를 통해 실질적 구현 완료)

이전 포트폴리오(WS-B~WS-Q)는 모두 완료되었습니다. 이전 감사(v0.8.0–v0.9.32),
마일스톤 마감 보고서, 레거시 GitBook 챕터는
[`docs/dev_history/`](../../../docs/dev_history/README.md)에 보관되어 있습니다.

---

> 이 문서는 [English README](../../../README.md)의 번역입니다. 원문과 번역본 사이에
> 차이가 있는 경우, 영문 원본이 우선합니다.
