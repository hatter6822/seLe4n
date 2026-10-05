<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.36.44-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  一个使用 Lean 4 编写并附带机器验证证明的微内核，受
  <a href="https://sel4.systems">seL4</a> 架构启发。首个硬件目标平台：
  <strong>Raspberry Pi 5</strong>。
</p>
<p align="center">
  <div align="center">
    在以下工具的协助下精心打造：
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>请据此理解本内核的性质</strong>
  </div>
</p>

<p align="center">
  <a href="../../../README.md">English</a> ·
  **简体中文** ·
  <a href="../es/README.md">Español</a> ·
  <a href="../ja/README.md">日本語</a> ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## 什么是 seLe4n？

seLe4n 是一个完全使用 Lean 4 从零构建的微内核。每一个内核状态转换都是可执行的纯函数。每一条不变量都由 Lean 类型检查器进行机器验证——零 `sorry`、零 `axiom`。整个证明层面可编译为原生代码，没有任何被承认但未证明的命题。

本项目保留了 seL4 基于能力的安全模型，同时借助 Lean 4 证明框架引入了若干架构改进：

### 调度与实时保证

- **可组合的性能对象** —— CPU 时间是一等内核对象。`SchedContext` 将预算、周期、优先级、截止期限和域封装为可复用的调度上下文，线程通过能力绑定到该对象。CBS（恒定带宽服务器）调度提供经过证明的带宽隔离（`cbs_bandwidth_bounded` 定理）
- **被动服务器** —— 空闲服务器在 IPC 期间借用客户端的 `SchedContext`，不服务时消耗零 CPU。`donationChainAcyclic` 不变量防止循环捐赠链
- **预算驱动的 IPC 超时** —— 阻塞操作受调用方预算约束。超时后，线程从端点队列中移出并重新入队
- **优先级继承协议** —— 传递性优先级传播，具有机器验证的无死锁保证（`blockingAcyclic`）和有界链深度，防止无界优先级反转
- **有界延迟定理** —— 机器验证的 WCRT 上界：`WCRT = D × L_max + N × (B + P)`，在 8 个活性模块中证明，覆盖预算单调性、补充时序、让出语义、频带耗尽和域轮转

### 数据结构与 IPC

- **O(1) 基于哈希的热路径** —— 所有对象存储、运行队列、CNode 槽位、VSpace 映射和 IPC 队列均使用经过形式化验证的 Robin Hood 哈希表，具有 `distCorrect`、`noDupKeys` 和 `probeChainDominant` 不变量
- **侵入式双队列 IPC** —— 每线程反向指针，实现 O(1) 入队、出队和队中移除
- **节点稳定的能力派生树** —— `childMap` + `parentMap` 索引，实现 O(1) 槽位转移、撤销和后代节点遍历

### 安全与验证

- **N 域信息流** —— 参数化的流策略，将 seL4 的二元分区泛化。44 条目执行边界，配有逐操作的非干扰证明（35 构造子 `NonInterferenceStep` 归纳类型），以及有界、失效即封闭（fail-closed）的降密审计追踪，配备能力门控的读取器
- **组合证明层** —— `proofLayerInvariantBundle` 将 16 个子系统不变量束（调度器核心 + CBS 扩展、能力、IPC + IPC–调度器耦合、生命周期、服务、VSpace、跨子系统、TLB 一致性、通知等待者一致性、TLB 击落 pending/ack 上界、每核 TLB 失效与 I-cache 一致性，以及降密审计日志上界）组合为单一顶层义务，从引导到所有操作均经过验证
- **三阶段状态架构** —— 带不变量见证的构建阶段流向冻结的不可变表示，具有经过证明的查找等价性。24 个冻结操作镜像活跃 API
- **完整操作集** —— 所有 seL4 操作均已实现并保持不变量，涵盖线程挂起/恢复（suspend/resume）、优先级管理（setPriority/setMCPriority）以及 IPC 缓冲区配置
- **服务编排** —— 内核级组件生命周期管理，带依赖图和经过证明的无环性（seLe4n 扩展，seL4 中不存在）

## 当前状态

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

<!-- MAINTAINERS/TRANSLATORS: the three metric rows below (production LoC,
     test LoC, proved declarations) are WRITTEN by
     scripts/sync_translated_metrics.py from docs/codebase_map.json.  A hand
     edit is overwritten on the next sync.  To reword a label, a preposition
     or an inflected noun, edit that script's TARGETS table in the same
     commit: it matches the surrounding literals verbatim and fails loudly
     when they change, so it can never quietly stop syncing this file. -->

| 属性 | 值 |
|------|------|
| **版本** | `0.36.44` |
| **Lean 工具链** | `v4.28.0` |
| **生产代码行数** | 433,982 行，分布于 361 个文件 |
| **测试代码行数** | 88,629 行，分布于 71 个测试套件 |
| **已证明的声明** | 14,408 个定理/引理声明（零 sorry/axiom） |
| **Rust crate** | 4 个（`sele4n-types`、`sele4n-abi`、`sele4n-sys`、`sele4n-hal`），共 80 个源文件 |
| **目标硬件** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **硬件绑定** | **H3 已完成**（WS-AG AG1–AG10）：HAL、GIC-400、定时器、ARMv8 页表、FFI 桥接、QEMU 启动 |
| **规范审计** | [`AUDIT_v0.29.0_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.29.0_COMPREHENSIVE.md) —— 1.0 前综合审计（202 项发现；已由 WS-AK AK1–AK10 修复；已归档） |
| **最新审计** | [`AUDIT_v0.30.11_COMPREHENSIVE`](../../../docs/audits/AUDIT_v0.30.11_COMPREHENSIVE.md) + [`AUDIT_v0.30.11_DEEP_VERIFICATION`](../../../docs/audits/AUDIT_v0.30.11_DEEP_VERIFICATION.md) —— WS-AN 收尾后进行的 1.0 前就绪审计（接替现已归档、由 WS-AN AN0–AN12 修复的 [`AUDIT_v0.30.6_COMPREHENSIVE`](../../../docs/dev_history/audits/AUDIT_v0.30.6_COMPREHENSIVE.md)）。WS-RC R0..R5 已于 v0.31.2 落地；WS-RC R6..R14 已按 SM0.Q.1 吸收映射并入 WS-SM（见 [`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §15`](../../../docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md)）。当前活跃的工作流计划：[`SMP_MULTICORE_COMPLETION_PLAN.md`](../../../docs/planning/SMP_MULTICORE_COMPLETION_PLAN.md)。 |
| **代码库映射** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) —— 机器可读的声明清单 |

指标由 `./scripts/generate_codebase_map.py` 从代码库中导出，并存储在
[`docs/codebase_map.json`](../../../docs/codebase_map.json) 的 `readme_sync` 键下。
使用 `./scripts/sync_documentation_metrics.sh`（仅验证：`--check`）统一更新所有文档；`./scripts/report_current_state.py` 仍作为人工交叉检查。

## 快速入门

```bash
./scripts/setup_lean_env.sh   # 安装 Lean 工具链
lake build                     # 编译所有模块
lake exe sele4n                # 运行跟踪测试工具
./scripts/test_smoke.sh        # 验证（格式检查 + 构建 + 跟踪 + 负状态）
```

## 文档

| 从这里开始 | 然后阅读 |
|-----------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) —— 开发流程、验证、PR 检查清单 | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) —— 项目规格与里程碑 |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) —— 完整手册 | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) —— seL4 参考语义 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) —— 机器可读清单 | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) —— 每一项延期事项及其负责人 |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) —— 贡献指南 | [`CHANGELOG.md`](../../../CHANGELOG.md) —— 版本变更历史 |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) 是项目指标的权威数据源，
为 [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) 提供数据，
并在合并时通过 CI 自动刷新。使用 `./scripts/generate_codebase_map.py --pretty` 重新生成。

## 验证命令

```bash
./scripts/test_fast.sh      # Tier 0+1：格式检查 + 构建
./scripts/test_smoke.sh     # + Tier 2：跟踪 + 负状态
./scripts/test_full.sh      # + Tier 3：不变量表面锚点 + Lean #check
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4：夜间确定性测试

./scripts/test_rust.sh                 # 主机 Rust：构建、测试、fmt、clippy
./scripts/test_aarch64_cross_build.sh  # 内核 HAL 的真实目标平台
```

提交 PR 前至少运行 `test_smoke.sh`。如果修改了定理、不变量或文档锚点，则需运行 `test_full.sh`。

修改 `rust/` 下的任何内容后，请运行**两条** Rust 通道。它们覆盖同一 crate 中互不重叠的两半：在主机上，每个 `#[cfg(target_arch = "aarch64")]` 代码块都会在 rustc 或 clippy 看到之前被移除，因此主机通道看不到构成 HAL 大部分内容的 67 个 cfg 门控代码块、57 处 `asm!` 以及四个 `.S` 源文件。交叉通道以两种配置（profile）为 `aarch64-unknown-none-softfloat` 构建 `sele4n-hal`，验证汇编源文件确实已被汇编，对交叉目标执行 lint，并反汇编 release 目标文件以证明它们不使用任何 FP/SIMD 寄存器——内核不使用浮点，并从第一条指令起就在 EL1 捕获 FP/SIMD。此外，它执行的是真正的构建而非 `cargo check`，因为 `check` 在代码生成之前就会停止，永远不会到达汇编器。

## 架构

seLe4n 按分层契约组织，每一层都包含可执行的状态转换和经过机器验证的不变量保持证明：

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  Scheduler   │  Capability │    IPC     │ Lifecycle │  Service (ext) │
│   RunQueue   │  CSpace/CDT │  DualQueue │  Retype   │  Orchestration │
│ SchedContext │             │  Donation  │           │                │
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│         Information Flow  (Policy, Projection, Enforcement)          │
├──────────────────────────────────────────────────────────────────────┤
│     Architecture  (VSpace, VSpaceBackend, Adapter, Assumptions)      │
├──────────────────────────────────────────────────────────────────────┤
│                     Model  (Object, State, CDT)                      │
├──────────────────────────────────────────────────────────────────────┤
│             Foundations  (Prelude, Machine, MachineConfig)           │
├──────────────────────────────────────────────────────────────────────┤
│        Platform  (Contract, Sim, RPi5)  ← production bindings        │
└──────────────────────────────────────────────────────────────────────┘
```

## 源码布局

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
│   ├── SchedContext/            CBS budget engine, replenishment queue, priority management
│   ├── FrozenOps/               Frozen-state operations + commutativity proofs
│   └── CrossSubsystem.lean      Cross-subsystem invariant composition
├── Platform/
│   ├── Contract.lean            PlatformBinding typeclass + BootVSpaceRootEntry
│   ├── Boot.lean                Boot sequence (PlatformConfig → IntermediateState).
│   │                            installBootVSpaceRoot threads canonical boot VSpace
│   │                            through bootFromPlatformChecked (WS-RC R3).
│   ├── Sim/                     Simulation platform (permissive contracts for testing)
│   └── RPi5/                    Raspberry Pi 5 (BCM2712, GIC-400, MMIO).
│                                VSpaceBoot.lean holds the canonical W^X-compliant
│                                boot VSpaceRoot (production-wired since WS-RC R3).
├── Testing/                     Test harness, state builder, invariant checks
Main.lean                        Executable entry point
tests/                           Executable test suites + fixtures
```

每个子系统遵循 **Operations/Invariant 分离**原则：状态转换位于 `Operations.lean`，证明位于 `Invariant.lean`。统一的 `apiInvariantBundle` 将所有子系统不变量聚合为单一的证明义务。完整的逐文件清单参见 [`docs/codebase_map.json`](../../../docs/codebase_map.json)。

## 与 seL4 的比较

| 特性 | seL4 | seLe4n |
|------|------|--------|
| **调度** | C 实现的偶发服务器（MCS） | CBS 调度，具有机器验证的 `cbs_bandwidth_bounded` 定理；`SchedContext` 作为能力控制的内核对象 |
| **被动服务器** | 通过 C 实现的 SchedContext 捐赠 | 经过验证的捐赠机制，具有 `donationChainAcyclic` 不变量 |
| **IPC** | 单链表端点队列 | 侵入式双队列，支持 O(1) 队中移除；预算驱动的超时机制 |
| **信息流** | 二元高/低分区 | N 域可配置策略，具有 44 条目执行边界（数量由 `enforcementBoundaryExtended_count` 锁定）、逐操作非干扰证明，以及针对每次授权降密的能力门控审计追踪 |
| **优先级继承** | C 实现的 PIP（MCS 分支） | 机器验证的传递性 PIP，具有无死锁保证和参数化 WCRT 上界 |
| **有界延迟** | 无形式化 WCRT 上界 | `WCRT = D × L_max + N × (B + P)`，在 8 个活性模块中证明 |
| **对象存储** | 链表和数组 | 经过验证的 Robin Hood 哈希表（`RHTable`/`RHSet`），O(1) 热路径 |
| **服务管理** | 不在内核中 | 一等服务编排，带依赖图和无环性证明 |
| **证明方法论** | Isabelle/HOL，事后验证 | Lean 4 类型检查器，证明与转换并置——零 sorry/axiom（已证明声明数见[当前状态](#当前状态)表） |
| **平台抽象** | C 级 HAL | `PlatformBinding` 类型类，带类型化边界契约 |

## 许可证与第三方署名

seLe4n 本身采用 GNU General Public License v3.0 或更高版本（GPLv3+）授权；完整文本见 [`LICENSE`](../../../LICENSE)。第三方构建依赖（`cc`、`find-msvc-tools`、`shlex`，均为 `MIT OR Apache-2.0` 双重许可）按 MIT 选项使用；其上游版权声明和许可声明原文收录于 [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md)。内核二进制文件中不包含任何运行时链接的第三方代码——HAL 为 `#![no_std]`，仅使用 `core::*`。

---

本文档翻译自 [English README](../../../README.md)。
