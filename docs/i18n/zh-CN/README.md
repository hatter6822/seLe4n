<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.29.7-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## 什么是 seLe4n？

seLe4n 是一个完全使用 Lean 4 从零构建的微内核。每一个内核状态转换都是可执行的纯函数。每一条不变量都由 Lean 类型检查器进行机器验证——零 `sorry`、零 `axiom`。整个证明层面可编译为原生代码，没有任何被承认但未证明的命题。

本项目保留了 seL4 基于能力的安全模型，同时借助 Lean 4 证明框架引入了若干架构改进：

### 调度与实时保证

- **可组合的性能对象** —— CPU 时间是一等内核对象。`SchedContext` 将预算、周期、优先级、截止期限和域封装为可复用的调度上下文，线程通过能力绑定到该对象。CBS（恒定带宽服务器）调度提供经过证明的带宽隔离（`cbs_bandwidth_bounded` 定理）
- **被动服务器** —— 空闲服务器在 IPC 期间借用客户端的 `SchedContext`，不服务时消耗零 CPU。`donationChainAcyclic` 不变量防止循环捐赠链
- **预算驱动的 IPC 超时** —— 阻塞操作受调用方预算约束。超时后，线程从端点队列中移出并重新入队
- **优先级继承协议** —— 传递性优先级传播，具有机器验证的无死锁保证（`blockingChainAcyclic`）和有界链深度，防止无界优先级反转
- **有界延迟定理** —— 机器验证的 WCRT 上界：`WCRT = D × L_max + N × (B + P)`，在 7 个活性模块中证明，覆盖预算单调性、补充时序、让出语义、频带耗尽和域轮转

### 数据结构与 IPC

- **O(1) 基于哈希的热路径** —— 所有对象存储、运行队列、CNode 槽位、VSpace 映射和 IPC 队列均使用经过形式化验证的 Robin Hood 哈希表，具有 `distCorrect`、`noDupKeys` 和 `probeChainDominant` 不变量
- **侵入式双向队列 IPC** —— 每线程反向指针，实现 O(1) 入队、出队和队中移除
- **节点稳定的能力派生树** —— `childMap` + `parentMap` 索引，实现 O(1) 槽位转移、撤销和子节点遍历

### 安全与验证

- **N 域信息流** —— 参数化的流策略，将 seL4 的二元分区泛化。30 条目执行边界，配有逐操作的非干扰证明（32 构造子 `NonInterferenceStep` 归纳类型）
- **组合证明层** —— `proofLayerInvariantBundle` 将 10 个子系统不变量（调度器、能力、IPC、生命周期、服务、VSpace、跨子系统、TLB 和 CBS 扩展）组合为单一顶层义务，从引导到所有操作均经过验证
- **两阶段状态架构** —— 带不变量见证的构建阶段流向冻结的不可变表示，具有经过证明的查找等价性。20 个冻结操作镜像活跃 API
- **完整操作集** —— 所有 seL4 操作均已实现并保持不变量，包括 5 个延迟操作（suspend/resume、setPriority/setMCPriority、setIPCBuffer）
- **服务编排** —— 内核级组件生命周期管理，带依赖图和经过证明的无环性（seLe4n 扩展，seL4 中不存在）

## 当前状态

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| 属性 | 值 |
|------|------|
| **版本** | `0.25.5` |
| **Lean 工具链** | `v4.28.0` |
| **生产代码行数** | 83,286 行，分布于 132 个文件 |
| **测试代码行数** | 10,564 行，分布于 15 个测试套件 |
| **已证明的声明** | 2,447 个定理/引理声明（零 sorry/axiom） |
| **目标硬件** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **最新审计** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) —— 完整的内核 Lean + Rust 审计（0 CRIT、5 HIGH、8 MED、30 LOW） |
| **代码库映射** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) —— 机器可读的声明清单 |

指标由 `./scripts/generate_codebase_map.py` 从代码库中提取，存储在
[`docs/codebase_map.json`](../../../docs/codebase_map.json) 的 `readme_sync` 字段下。
使用 `./scripts/report_current_state.py` 作为交叉校验来同步更新所有文档。

## 快速入门

```bash
./scripts/setup_lean_env.sh   # 安装 Lean 工具链
lake build                     # 编译所有模块
lake exe sele4n                # 运行跟踪测试工具
./scripts/test_smoke.sh        # 验证（格式检查 + 构建 + 跟踪 + 负状态 + 文档同步）
```

## 文档

| 从这里开始 | 然后阅读 |
|-----------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) —— 开发流程、验证、PR 检查清单 | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) —— 项目规格与里程碑 |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) —— 完整手册 | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) —— seL4 参考语义 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) —— 机器可读清单 | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) —— 工作流历史与路线图 |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) —— 贡献指南 | [`CHANGELOG.md`](../../../CHANGELOG.md) —— 版本变更历史 |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) 是项目指标的权威数据源，
为 [seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) 提供数据，
并在合并时通过 CI 自动刷新。使用 `./scripts/generate_codebase_map.py --pretty` 重新生成。

## 验证命令

```bash
./scripts/test_fast.sh      # Tier 0+1：格式检查 + 构建
./scripts/test_smoke.sh     # + Tier 2：跟踪 + 负状态 + 文档同步
./scripts/test_full.sh      # + Tier 3：不变量表面锚点 + Lean #check 正确性
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4：夜间确定性测试
```

提交 PR 前至少运行 `test_smoke.sh`。如果修改了定理、不变量或文档锚点，则需运行 `test_full.sh`。

## 架构

seLe4n 按分层契约组织，每一层都包含可执行的状态转换和经过机器验证的不变量保持证明：

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

每个子系统遵循 **Operations/Invariant 分离**原则：状态转换位于 `Operations.lean`，证明位于 `Invariant.lean`。统一的 `apiInvariantBundle` 将所有子系统不变量聚合为单一的证明义务。完整的逐文件清单参见 [`docs/codebase_map.json`](../../../docs/codebase_map.json)。

## 与 seL4 的比较

| 特性 | seL4 | seLe4n |
|------|------|--------|
| **调度** | C 实现的偶发服务器（MCS） | CBS 调度，具有机器验证的 `cbs_bandwidth_bounded` 定理；`SchedContext` 作为能力控制的内核对象 |
| **被动服务器** | 通过 C 实现的 SchedContext 捐赠 | 经过验证的捐赠机制，具有 `donationChainAcyclic` 不变量 |
| **IPC** | 单链表端点队列 | 侵入式双向队列，支持 O(1) 队中移除；预算驱动的超时机制 |
| **信息流** | 二元高/低分区 | N 域可配置策略，具有 30 条目执行边界和逐操作非干扰证明 |
| **优先级继承** | C 实现的 PIP（MCS 分支） | 机器验证的传递性 PIP，具有无死锁保证和参数化 WCRT 上界 |
| **有界延迟** | 无形式化 WCRT 上界 | `WCRT = D × L_max + N × (B + P)`，在 7 个活性模块中证明 |
| **对象存储** | 链表和数组 | 经过验证的 Robin Hood 哈希表（`RHTable`/`RHSet`），O(1) 热路径 |
| **服务管理** | 不在内核中 | 一等服务编排，带依赖图和无环性证明 |
| **证明方法论** | Isabelle/HOL，事后验证 | Lean 4 类型检查器，证明与转换并置（2,447 个定理，零 sorry/axiom） |
| **平台抽象** | C 级 HAL | `PlatformBinding` 类型类，带类型化边界契约 |

## 下一步

所有软件层面的工作流（WS-B 至 WS-AB）均已完成。完整历史记录见
[`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)。

### 已完成的工作流

| 工作流 | 范围 | 版本 |
|--------|------|------|
| **WS-AB** | 延迟操作与活性——suspend/resume、setPriority/setMCPriority、setIPCBuffer、优先级继承协议、有界延迟定理（6 阶段，90 个任务） | v0.24.0–v0.25.5 |
| **WS-Z** | 可组合性能对象——`SchedContext` 作为第 7 个内核对象、CBS 预算引擎、补充队列、被动服务器捐赠、超时端点（10 阶段，213 个任务） | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | 核心内核子系统、Robin Hood 哈希表、基数树、冻结状态、信息流、服务编排、平台契约 | v0.9.0–v0.22.x |

详细计划：[WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### 下一个主要里程碑

**Raspberry Pi 5 硬件绑定** —— ARMv8 页表遍历、GIC-400 中断路由、引导序列。此前的审计和里程碑结项报告已归档至 [`docs/dev_history/`](../../../docs/dev_history/README.md)。

---

本文档翻译自 [English README](../../../README.md)。
