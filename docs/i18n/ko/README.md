<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n 로고" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.29.5-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Lean 4로 작성된 기계 검증 증명을 갖춘 마이크로커널로,
  <a href="https://sel4.systems">seL4</a> 아키텍처에서 영감을 받았습니다.
  첫 번째 하드웨어 대상: <strong>Raspberry Pi 5</strong>.
</p>
<p align="center">
  <div align="center">
    다음의 도움으로 정성껏 만들었습니다:
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>이 커널을 그에 맞게 취급하십시오</strong>
  </div>
</p>

<p align="center">
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  **한국어** ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## seLe4n이란?

seLe4n은 Lean 4로 처음부터 설계된 마이크로커널입니다. 모든 커널 전이(kernel transition)는
실행 가능한 순수 함수입니다. 모든 불변량(invariant)은 Lean 타입 검사기를 통해 기계적으로
검증됩니다 — `sorry` 제로, `axiom` 제로. 전체 증명 표면은 인정된 증명(admitted proof) 없이
네이티브 코드로 컴파일됩니다.

본 프로젝트는 seL4의 능력 기반 보안 모델을 보존하면서, Lean 4 증명 프레임워크가 가능케 하는
아키텍처 개선을 도입합니다:

### 스케줄링과 실시간 보장

- **조합 가능한 성능 객체** — CPU 시간은 일급 커널 객체입니다. `SchedContext`는 예산, 주기, 우선순위, 마감 시한, 도메인을 재사용 가능한 스케줄링 컨텍스트로 캡슐화하며, 스레드는 능력(capability)을 통해 바인딩합니다. CBS(Constant Bandwidth Server) 스케줄링은 증명된 대역폭 격리(`cbs_bandwidth_bounded` 정리)를 제공합니다
- **수동 서버** — 유휴 서버는 IPC 중 클라이언트의 `SchedContext`를 빌려 사용하여, 서비스하지 않을 때 CPU를 제로로 소비합니다. `donationChainAcyclic` 불변량이 순환 기부 체인을 방지합니다
- **예산 기반 IPC 타임아웃** — 블로킹 연산은 호출자의 예산으로 한정됩니다. 만료 시, 스레드는 엔드포인트 큐에서 분리되어 재삽입됩니다
- **우선순위 상속 프로토콜** — 기계 검증된 교착 상태 자유(`blockingChainAcyclic`)와 한정된 체인 깊이를 갖춘 전이적 우선순위 전파. 무한 우선순위 역전을 방지합니다
- **유계 지연 정리** — 기계 검증된 WCRT 한계: `WCRT = D × L_max + N × (B + P)`, 예산 단조성, 보충 타이밍, yield 의미론, 대역 소진, 도메인 순환을 다루는 7개 활성 모듈에 걸쳐 증명됨

### 자료 구조와 IPC

- **O(1) 해시 기반 핫 패스** — 모든 객체 저장소, 실행 큐, CNode 슬롯, VSpace 매핑, IPC 큐가 `distCorrect`, `noDupKeys`, `probeChainDominant` 불변량을 갖춘 형식 검증된 Robin Hood 해시 테이블을 사용합니다
- **침입형 이중 큐 IPC** — 스레드별 역방향 포인터로 O(1) 삽입, 삭제, 큐 중간 제거 지원
- **노드 안정 능력 파생 트리** — O(1) 슬롯 전송, 폐기, 자손 순회를 위한 `childMap` + `parentMap` 인덱스

### 보안과 검증

- **N-도메인 정보 흐름** — seL4의 이진 파티션을 일반화하는 매개변수화된 흐름 정책. 연산별 비간섭 증명(32-생성자 `NonInterferenceStep` 귀납형)을 갖춘 30-항목 시행 경계
- **합성 증명 계층** — `proofLayerInvariantBundle`이 10개 서브시스템 불변량(스케줄러, 능력, IPC, 생명주기, 서비스, VSpace, 교차 서브시스템, TLB, CBS 확장)을 부트에서 모든 연산까지 검증되는 단일 최상위 의무로 합성합니다
- **2단계 상태 아키텍처** — 불변량 증거를 갖춘 빌더 단계가 증명된 조회 동치를 갖춘 동결 불변 표현으로 이행합니다. 20개 동결 연산이 라이브 API를 반영합니다
- **완전한 연산 집합** — 5개 지연 연산(suspend/resume, setPriority/setMCPriority, setIPCBuffer)을 포함하여 모든 seL4 연산이 불변량 보존과 함께 구현되었습니다
- **서비스 오케스트레이션** — 의존성 그래프와 비순환성 증명을 갖춘 커널 수준 컴포넌트 생명주기 (seL4에 없는 seLe4n 확장)

## 현재 상태

<!-- 지표는 docs/codebase_map.json → readme_sync 섹션에서 동기화됩니다.
     재생성: ./scripts/generate_codebase_map.py --pretty
     진실의 원천: docs/codebase_map.json (readme_sync) -->

| 속성 | 값 |
|------|-----|
| **버전** | `0.25.5` |
| **Lean 툴체인** | `v4.28.0` |
| **프로덕션 Lean LoC** | 132개 파일, 83,286줄 |
| **테스트 Lean LoC** | 15개 테스트 스위트, 10,564줄 |
| **증명된 선언** | 2,447개 theorem/lemma 선언 (sorry/axiom 제로) |
| **대상 하드웨어** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **최신 감사** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — 전체 커널 Lean + Rust 감사 (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
| **코드베이스 맵** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계 판독 가능한 선언 인벤토리 |

지표는 `./scripts/generate_codebase_map.py`에 의해 코드베이스에서 산출되며,
[`docs/codebase_map.json`](../../../docs/codebase_map.json)의 `readme_sync` 키에
저장됩니다. `./scripts/report_current_state.py`로 교차 검증할 수 있습니다.

## 빠른 시작

```bash
./scripts/setup_lean_env.sh   # Lean 툴체인 설치
lake build                     # 모든 모듈 컴파일
lake exe sele4n                # 트레이스 하니스 실행
./scripts/test_smoke.sh        # 검증 (위생 + 빌드 + 트레이스 + 음성 상태 + 문서 동기화)
```

## 문서

| 여기서 시작 | 그다음 |
|-------------|--------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — 작업 흐름, 검증, PR 체크리스트 | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — 사양 및 마일스톤 |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — 전체 핸드북 | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4 참조 의미론 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계 판독 가능 인벤토리 | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) — 작업 스트림 이력 및 로드맵 |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — 기여 방법 | [`CHANGELOG.md`](../../../CHANGELOG.md) — 버전 이력 |

[`docs/codebase_map.json`](../../../docs/codebase_map.json)이 프로젝트 지표의 진실의 원천입니다.
이 파일은 [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io)에 공급되며,
병합 시 CI를 통해 자동 갱신됩니다. `./scripts/generate_codebase_map.py --pretty`로
재생성할 수 있습니다.

## 검증 명령어

```bash
./scripts/test_fast.sh      # Tier 0+1: 위생 검사 + 빌드
./scripts/test_smoke.sh     # + Tier 2: 트레이스 + 음성 상태 + 문서 동기화
./scripts/test_full.sh      # + Tier 3: 불변량 표면 앵커 + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4: 야간 결정론
```

PR 제출 전 최소 `test_smoke.sh`를 실행하십시오. 정리, 불변량, 또는 문서 앵커 변경 시
`test_full.sh`를 실행하십시오.

## 아키텍처

seLe4n은 계층화된 계약으로 구성되어 있으며, 각 계층은 실행 가능한 전이와
기계 검증된 불변량 보존 증명을 갖추고 있습니다:

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

## 소스 레이아웃

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

각 서브시스템은 **Operations/Invariant 분리** 패턴을 따릅니다: 전이는
`Operations.lean`에, 증명은 `Invariant.lean`에 위치합니다. 통합된 `apiInvariantBundle`이
모든 서브시스템 불변량을 단일 증명 의무로 집합합니다. 전체 파일별 인벤토리는
[`docs/codebase_map.json`](../../../docs/codebase_map.json)을 참고하십시오.

## seL4와의 비교

| 기능 | seL4 | seLe4n |
|------|------|--------|
| **스케줄링** | C 구현 산발 서버 (MCS) | 기계 검증 `cbs_bandwidth_bounded` 정리를 갖춘 CBS; `SchedContext`를 능력 제어 커널 객체로 |
| **수동 서버** | C를 통한 SchedContext 기부 | `donationChainAcyclic` 불변량을 갖춘 검증된 기부 |
| **IPC** | 단일 연결 리스트 엔드포인트 큐 | O(1) 큐 중간 제거를 갖춘 침입형 이중 큐; 예산 기반 타임아웃 |
| **정보 흐름** | 이진 고/저 파티션 | 30-항목 시행 경계와 연산별 NI 증명을 갖춘 N-도메인 구성 가능 정책 |
| **우선순위 상속** | C 구현 PIP (MCS 브랜치) | 교착 상태 자유와 매개변수적 WCRT 한계를 갖춘 기계 검증 전이적 PIP |
| **유계 지연** | 공식 WCRT 한계 없음 | 7개 활성 모듈에 걸쳐 증명된 `WCRT = D × L_max + N × (B + P)` |
| **객체 저장소** | 연결 리스트와 배열 | O(1) 핫 패스를 갖춘 검증된 Robin Hood 해시 테이블 (`RHTable`/`RHSet`) |
| **서비스 관리** | 커널에 없음 | 의존성 그래프와 비순환성 증명을 갖춘 일급 오케스트레이션 |
| **증명** | Isabelle/HOL, 사후(post-hoc) | Lean 4 타입 검사기, 전이와 동일 위치 (2,447개 정리, sorry/axiom 제로) |
| **플랫폼** | C 수준 HAL | 타입된 경계 계약을 갖춘 `PlatformBinding` 타입클래스 |

## 다음 단계

모든 소프트웨어 수준 작업 스트림(WS-B~WS-AB)이 완료되었습니다. 전체 이력은
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)에 있습니다.

### 완료된 작업 스트림

| 작업 스트림 | 범위 | 버전 |
|-------------|------|------|
| **WS-AB** | 지연 연산 및 활성 완성 — suspend/resume, setPriority/setMCPriority, setIPCBuffer, 우선순위 상속 프로토콜, 유계 지연 정리 (6단계, 90개 작업) | v0.24.0–v0.25.5 |
| **WS-Z** | 조합 가능한 성능 객체 — `SchedContext`를 7번째 커널 객체로, CBS 예산 엔진, 보충 큐, 수동 서버 기부, 타임아웃 엔드포인트 (10단계, 213개 작업) | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | 핵심 커널 서브시스템, Robin Hood 해시 테이블, 기수 트리, 동결 상태, 정보 흐름, 서비스 오케스트레이션, 플랫폼 계약 | v0.9.0–v0.22.x |

상세 계획: [WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### 다음 주요 마일스톤

**Raspberry Pi 5 하드웨어 바인딩** — ARMv8 페이지 테이블 워크, GIC-400 인터럽트 라우팅,
부트 시퀀스. 이전 감사 및 마일스톤 마감 보고서는
[`docs/dev_history/`](../../../docs/dev_history/README.md)에 보관되어 있습니다.

---

> 이 문서는 [English README](../../../README.md)의 번역입니다.
> 원문과 번역본 사이에 차이가 있는 경우, 영문 원본이 우선합니다.
