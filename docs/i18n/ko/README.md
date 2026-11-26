<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n 로고" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.37.56-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## seLe4n이란?

seLe4n은 Lean 4로 처음부터 만든 마이크로커널입니다. 모든 커널 전이는 실행 가능한
순수 함수이며, 모든 불변식은 Lean 커널이 검사합니다. 프로덕션 증명 영역에는
`sorry`도 `axiom`도 없습니다. 같은 Lean 코드가 네이티브 코드로 컴파일되어, 작은
Rust 하드웨어 계층과 함께 대상 기기에서 부팅되는 커널 이미지로 링크됩니다.

이 프로젝트는 seL4의 capability 기반 보안 모델을 유지하고, 점점 더 seL4의 사용자에게
보이는 ABI까지 따르면서, Lean으로 더 많은 것을 증명하고 seL4가 남긴 빈틈을
강화합니다. 전체 명세는 [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)이며,
아래 항목은 그 명세로 들어가는 입구입니다.

### seL4의 ABI

- **seL4-MCS의 시스템 콜** — MCS의 시스템 콜 11개(`Call` … `Yield`)를 seL4와 같은
  번호로 `x7`에 둡니다. 연산은 시스템 콜, 호출된 capability의 타입, 메시지 레이블로
  선택됩니다(`Syscall.selectOperation`). seL4와 같습니다
- **seL4의 오류 및 폴트 페이로드** — `LookupFault`, seL4 메시지 레지스터 순서의 오류
  프레임, 수신 측 capability 폴트, `Restart` 상태, 추가 capability로 전달되는
  capability 인자, 그리고 capability 안에 담긴 가드와 단일 `resolveAddressBits`
- seL4 ABI의 나머지 작업(나머지 호출, 타임아웃 폴트, 호출별 권한, 코어별 Running
  상태)은 진행 중인 워크스트림 WS-SX입니다. 그 행들은
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)에
  있습니다

### 스케줄링과 실시간

- **capability로서의 스케줄링 컨텍스트** — CPU 시간은 커널 객체입니다.
  `SchedContext`는 seL4-MCS의 예산, 주기, 리필을 담고, 코어의 `SchedControl` 권한으로
  설정되며, capability를 통해 스레드에 바인딩됩니다. 그 불변식(`budgetWithinBounds`,
  `refillsConserved`)은 최상위 번들에 포함됩니다. 대역폭 격리는
  `refill_window_bound`입니다. 컨텍스트는 한 주기 길이의 어떤 창에서도 예산보다 오래
  실행되지 않으며, 이는 seL4-MCS의 슬라이딩 윈도 보장입니다. 반대 방향(승인된
  서버는 매 창마다 예산을 받는다)을 더하는, EDF 루트를 가진 계층형 고정 대역폭
  스케줄러는 계획된 워크스트림 WS-CB입니다
  ([`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md))
- **수동 서버** — 서버는 IPC 동안 클라이언트가 기부한 스케줄링 컨텍스트로 실행됩니다.
  `donationChainAcyclic`이 순환 기부를 배제합니다
- **예산 기반 IPC 타임아웃** — 예산이 소진된 차단 스레드는 엔드포인트 큐에서
  제거됩니다(`timeoutThread`)
- **우선순위 상속** — 전이적 전파, 기계 검사된 차단 순환 부재(`blockingAcyclic`),
  유계 역전 정리(`pip_bounded_inversion`)
- **유계 지연** — 최악 응답 시간의 매개변수 상한
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  (`bounded_scheduling_latency_exists`, 코어별 형태 포함)를
  `SeLe4n/Kernel/Scheduler/Liveness/`의 모듈에서 증명합니다

### 커널 객체와 메모리

- **untyped 메모리에서 잘라 낸 객체** — retype은 untyped capability의 영역에서 객체를
  잘라 내고, untyped 리셋은 seL4와 같습니다. 잘라 낸 각 객체의 셀을 그 untyped 자신의
  메모리로 옮기는 일은 진행 중인 워크스트림 WS-UC입니다
- **커널 진입은 아무것도 할당하지 않는다** — 컴파일된 시스템 콜, 폴트, 인터럽트
  진입은 힙 할당을 하지 않습니다. retype의 잘라 내기는 새 객체 자신의 셀만
  할당합니다. QEMU 힙 게이트(`scripts/test_qemu_heap_allocations_per_syscall.sh`)가
  부팅된 이미지에서 모든 진입을 측정하고, 다른 값이면 실패합니다
- **자료 구조** — 객체 저장소와 VSpace 매핑은 검증된 Robin Hood 해시 테이블
  (`RHTable`, `distCorrect`·`noDupKeys`·`probeChainDominant` 포함)입니다. CNode는
  seL4와 같이 `2^radix`개 슬롯의 평면 배열입니다. 실행 큐, 엔드포인트·알림 큐, 응답
  대기자는 TCB를 통해 연결되며, 각각 링크와의 일치가 증명된 고스트 추상 큐를 가집니다
- **슬롯으로 연결된 capability 파생 트리** — 각 슬롯은 부모, 첫 자식, 형제 링크(seL4의
  매핑 데이터베이스)를 가지며 트리와의 일치가 증명되어 있습니다. 삭제, 취소(seL4의
  `cteRevoke` 루프), 슬롯 이전은 링크를 따라갑니다
- **VSpace** — 프레임별 W^X를 강제하는 ARMv8 페이지 테이블과, RAM의 비캐시 별칭을
  거부하는 메모리 타입 검사

### 보안과 검증

- **N 도메인 정보 흐름** — seL4의 2 도메인 분할을 일반화한 매개변수화된 흐름 정책,
  길이가 `enforcementBoundaryExtended_count`(코어별 경계는
  `enforcementBoundaryPerCore_count`)로 고정되는 강제 경계, `NonInterferenceStep`의 각
  생성자에 대한 비간섭 정리, 그리고 `auditTrail` capability로 읽는 유계·fail-closed
  기밀 해제 감사 기록
- **합성된 증명 계층** — `proofLayerInvariantBundle`
  (`SeLe4n/Kernel/Architecture/Invariant.lean`)은 각 서브시스템의 불변식 번들(스케줄러,
  capability, IPC와 그 스케줄러 결합, 생명주기, 서비스 레지스트리, VSpace, 서브시스템
  간, TLB·명령 캐시 일관성, TLB 슈트다운, 기밀 해제 감사 로그, 그리고 연결 구조 각각과
  그 고스트의 일치)을 하나의 의무로 묶어 부팅부터 모든 연산에 걸쳐 유지합니다
- **멀티코어** — 코어별 스케줄링, 코어 간 IPC와 깨우기, TLB 슈트다운을 갖춘 4코어.
  SMP 완성 워크스트림(WS-SM)이 진행 중입니다
- **3단계 상태** — 불변식 증인을 가진 빌더 단계가 조회 동등성이 증명된 불변 표현으로
  동결됩니다. 동결된 연산은 `frozenOpCoverage`가 나열하는 시스템 콜을 다루며,
  `frozenOpCoverage_count`로 고정됩니다
- **서비스 레지스트리** — seL4에 없는 seLe4n 확장입니다. 서비스는 `serviceRegistry`
  capability로 등록·조회되고 서비스를 제공하는 엔드포인트에 기록됩니다. 의존성 정책은
  seL4와 같이 사용자 공간 서비스 관리자에게 맡깁니다

## 현재 상태

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| 항목 | 값 |
|------|-----|
| **버전** | `0.37.56` |
| **Lean 툴체인** | `v4.28.0` |
| **프로덕션 Lean LoC** | 701개 파일, 686,360줄 |
| **테스트 Lean LoC** | 71개 테스트 스위트, 91,877줄 |
| **증명된 선언** | 26,502개 theorem/lemma 선언 (sorry/axiom 제로) |
| **Rust 크레이트** | `sele4n-types`, `sele4n-abi`, `sele4n-sys`(사용자 공간 래퍼), `sele4n-hal`(커널의 하드웨어 계층), 호스트 테스트 `sele4n-lean-boundary` |
| **대상 하드웨어** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **부팅 레인** | 모든 QEMU 레인은 먼저 [rpi5_machine](https://github.com/hatter6822/rpi5_machine)의 `raspi5b` 머신에서 Raspberry Pi 5 이미지를 부팅하고, 그다음 QEMU의 `virt`에서 `virt` 이미지를 부팅합니다 |
| **워크스트림** | 열린 각 워크스트림의 상태: [`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md); 색인과 부채 대장: [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **감사** | [`docs/audits/`](../../../docs/audits/README.md) — 현재 감사의 산출물. 이전 감사는 보관됨 |
| **코드베이스 맵** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계가 읽을 수 있는 선언 목록 |

지표는 `./scripts/generate_codebase_map.py`가 코드에서 도출하여
[`docs/codebase_map.json`](../../../docs/codebase_map.json)의 `readme_sync` 키에 저장합니다.
모든 문서는 `./scripts/sync_documentation_metrics.sh`(검증만: `--check`)로 함께
갱신하세요.

## 빠른 시작

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build`는 `Main.lean`과 테스트 실행 파일에서 도달 가능한 것만 빌드합니다.
`.lean` 파일을 커밋하기 전에 해당 모듈을 이름으로 빌드하세요
(`lake build <Module.Path>`). 전체 작업 흐름은
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)에, 모든 기여자가 따르는 규칙은
[`CLAUDE.md`](../../../CLAUDE.md)에 있습니다.

## 문서

| 여기서 시작 | 다음 |
|-------------|------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — 작업 흐름, 검증, PR 체크리스트 | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — 명세와 마일스톤 |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — 전체 핸드북 | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4 참조 의미론 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 기계 판독 목록 | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — 담당자가 있는 모든 연기 항목 |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — 기여 절차 | [`CHANGELOG.md`](../../../CHANGELOG.md) — 버전 이력 |

## 검증 명령

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

모든 PR 전에 최소 `test_smoke.sh`를 실행하고, 정리·불변식·Tier 3 앵커를 바꿀 때는
`test_full.sh`를 실행하세요. 각 티어는 처음 실패한 검사에서 멈춥니다. `--continue`를
넘기면 모든 실패를 한 번에 모을 수 있습니다.

`rust/` 아래를 바꾼 뒤에는 Rust **두** 레인을 모두 실행하세요. 둘은 같은 크레이트의
서로소인 절반을 다룹니다. 호스트에서는 모든 `#[cfg(target_arch = "aarch64")]` 블록이
rustc나 clippy가 보기 전에 제거되므로, 호스트 레인은 HAL의 대부분을 이루는 조건부
블록, `asm!` 위치, `.S` 소스를 보지 못합니다. 크로스 레인은 `sele4n-hal`을
`aarch64-unknown-none-softfloat`용으로 두 프로필에서 빌드하고, 어셈블리 소스가 실제로
어셈블되었는지 확인하고, 크로스 대상에 lint를 돌리고, release 객체를 역어셈블하여
FP/SIMD 레지스터를 쓰지 않음을 증명합니다. QEMU 레인은 처음 사용할 때
`scripts/setup_rpi5_machine.sh`에 고정된 커밋의 rpi5_machine을 빌드합니다. 전제
조건이 없는 레인은 통과가 아니라 NOT RUN으로 보고됩니다. 전체 목록은
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)에 있습니다.

## 아키텍처

seLe4n은 계층형 계약으로 구성되며, 각 계층은 실행 가능한 전이와 기계 검사된 불변식
보존 증명을 가집니다.

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

## 소스 구조

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

각 서브시스템은 **Operations/Invariant 분리**를 따릅니다. 전이는
`Operations.lean`에, 증명은 `Invariant.lean`에 있습니다. 통합된
`apiInvariantBundle`이 모든 서브시스템 불변식을 하나의 증명 의무로 모읍니다.
서브시스템 지도는 [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5, 파일별 전체
목록은 [`docs/codebase_map.json`](../../../docs/codebase_map.json)을 보세요.

## seL4와의 비교

| 기능 | seL4 | seLe4n |
|------|------|--------|
| **시스템 콜 ABI** | MCS 시스템 콜, 호출 레이블, 오류·폴트 페이로드 | 동일: seL4-MCS의 시스템 콜 11개와 그 번호, 레이블로 선택하는 호출, seL4의 오류 페이로드. 나머지 호출은 WS-SX의 행 |
| **스케줄링** | 산발 서버 리필을 갖춘 MCS 스케줄링 컨텍스트 | 같은 리필 엔진. 보존 불변식과 창당 예산 하나의 상한(`refill_window_bound`)이 증명됨. EDF 루트를 가진 계층형 CBS 계획(WS-CB) |
| **수동 서버** | SchedContext 기부 | `donationChainAcyclic` 불변식을 갖춘 검증된 기부 |
| **IPC** | 엔드포인트마다 하나의 큐, TCB를 통해 연결 | 엔드포인트마다 송신 큐와 수신 큐. 둘 다 TCB를 통해 연결되며 어느 위치에서든 O(1) 제거. 예산 기반 타임아웃 |
| **정보 흐름** | 이진 high/low 분할 | 설정 가능한 N 도메인 정책, `enforcementBoundaryExtended_count`로 고정된 강제 경계, 단계별 비간섭 정리, 승인된 모든 기밀 해제에 대한 capability 제어 감사 기록 |
| **우선순위 상속** | 커널에 없음 | 차단 순환이 없는 기계 검사된 전이적 PIP와 유계 역전 정리 |
| **유계 지연** | 형식적 WCRT 상한 없음 | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`, 활성 모듈에서 증명 |
| **객체 저장소** | 물리 주소의 객체 | 검증된 Robin Hood 해시 테이블(`RHTable`/`RHSet`). CNode는 seL4와 같이 평면 슬롯 배열 |
| **메모리 매핑** | 커널이 W^X를 강제하지 않음 | 프레임별 W^X를 불변식으로 강제. 메모리 타입 검사가 RAM의 비캐시 별칭을 거부 |
| **서비스 관리** | 커널 밖 | 엔드포인트의 capability 제어 서비스 레지스트리. 의존성 정책은 사용자 공간 |
| **증명** | Isabelle/HOL, 정제를 통해 C 코드 대상 | Lean 4, 실행 가능한 전이와 같은 곳. sorry/axiom 0(개수는 위 표) |
| **플랫폼** | C 수준 HAL | 타입이 있는 경계 계약을 가진 `PlatformBinding` 타입클래스와 Rust HAL |

## 라이선스 및 서드파티 저작자 표시

seLe4n 자체는 GNU General Public License v3.0 이상(GPLv3+)으로 라이선스됩니다.
전문은 [`LICENSE`](../../../LICENSE)를 참조하십시오. 서드파티 빌드 의존성(`cc`,
`find-msvc-tools`, `shlex`, 모두 `MIT OR Apache-2.0` 이중 라이선스)은 MIT
옵션으로 사용되며, 각 업스트림의 저작권 및 허가 고지는
[`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md)에 원문 그대로
수록되어 있습니다. 커널 바이너리에는 런타임에 링크되는 서드파티 코드가 전혀
없습니다 — HAL은 `#![no_std]`이며 `core::*`만 사용합니다.

---

> 이 문서는 [English README](../../../README.md)의 번역입니다.
> 원문과 번역본 사이에 차이가 있는 경우, 영문 원본이 우선합니다.
