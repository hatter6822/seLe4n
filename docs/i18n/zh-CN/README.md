<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.22.7-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  一个使用 Lean 4 编写并附带机器验证证明的微内核（microkernel），受
  <a href="https://sel4.systems">seL4</a> 架构启发。首个硬件目标平台：
  <strong>Raspberry Pi 5</strong>。
</p>

---

🌐 [English](../../../README.md) | **简体中文** | [Español](../es/README.md) | [日本語](../ja/README.md) | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## 什么是 seLe4n？

seLe4n 是一个完全使用 Lean 4 从零构建的微内核（microkernel）。每一个内核状态转换（kernel transition）都是可执行的纯函数。每一条不变量（invariant）都由 Lean 类型检查器进行机器验证——零 `sorry`、零 `axiom`。整个证明层面可编译为原生代码，没有任何被承认但未证明的命题。

本项目采用基于能力（capability）的安全模型，同时在架构上引入了若干相较于其他微内核的创新改进：

- **O(1) 基于哈希的内核热路径** —— 所有对象存储、运行队列、CNode 槽位、VSpace 映射和 IPC 队列均使用经过形式化验证的 `RHTable`/`RHSet`（Robin Hood 哈希表，附带机器验证的不变量，状态中不使用 `Std.HashMap`/`Std.HashSet`）
- **服务编排层（service orchestration layer）** —— 管理组件生命周期和依赖关系，具有确定性的部分失败语义
- **节点稳定的能力派生树（capability derivation tree）** —— 使用 `childMap` + `parentMap` RHTable 索引，实现 O(1) 槽位转移、撤销、父节点查找和子节点遍历
- **侵入式双向队列 IPC（intrusive dual-queue IPC）** —— 每个线程具备 `queuePrev`/`queuePPrev`/`queueNext` 链接，实现 O(1) 入队、出队和队中移除
- **参数化 N 域信息流（N-domain information flow）框架** —— 支持可配置的流策略，将传统的保密性/完整性标签泛化（超越 seL4 的二元分区模型）
- **EDF + 优先级调度（scheduling）** —— 带有分发时出队语义、每 TCB 寄存器上下文与内联上下文切换、按优先级分桶的 `RunQueue`、域感知分区

## 当前状态

| 属性 | 值 |
|------|------|
| **版本** | `0.22.7` |
| **Lean 工具链** | `v4.28.0` |
| **生产代码行数** | 72,569 行，分布于 103 个文件 |
| **测试代码行数** | 8,437 行，分布于 10 个测试套件 |
| **已证明的声明** | 2,138 个定理（theorem）/引理（lemma）声明（零 sorry/axiom） |
| **目标硬件** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **最新审计** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) —— 完整的内核 + Rust 代码库预发布审计 |
| **代码库映射** | [`docs/codebase_map.json`](../../codebase_map.json) —— 机器可读的声明清单 |

指标由 `./scripts/generate_codebase_map.py` 从代码库中提取，存储在
[`docs/codebase_map.json`](../../codebase_map.json) 的 `readme_sync` 字段下。

## 快速入门

```bash
./scripts/setup_lean_env.sh   # 安装 Lean 工具链
lake build                     # 编译所有模块
lake exe sele4n                # 运行跟踪测试工具
./scripts/test_smoke.sh        # 验证（格式检查 + 构建 + 跟踪 + 负状态 + 文档同步）
```

## 入门路径

初次接触本项目？建议按以下顺序阅读：

1. **本 README** —— 项目定位、架构和源码布局
2. [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md) —— 日常开发流程、验证循环、PR 检查清单
3. [`docs/gitbook/README.md`](../../gitbook/README.md) —— 完整手册（架构深入探讨、证明体系、硬件路径）
4. [`docs/codebase_map.json`](../../codebase_map.json) —— 机器可读的模块与声明清单

工作流规划和历史记录请参见 [`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md)。

## 项目文档

| 文档 | 用途 |
|------|------|
| [`docs/spec/SELE4N_SPEC.md`](../../spec/SELE4N_SPEC.md) | 项目规格说明与里程碑 |
| [`docs/spec/SEL4_SPEC.md`](../../spec/SEL4_SPEC.md) | seL4 参考语义 |
| [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md) | 日常开发流程、验证循环、PR 检查清单 |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../TESTING_FRAMEWORK_PLAN.md) | 分层测试门控与 CI 规约 |
| [`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md) | 完整的工作流历史、路线图与审计计划索引 |
| [`docs/gitbook/README.md`](../../gitbook/README.md) | 完整手册（架构、设计、证明、硬件路径） |
| [`docs/codebase_map.json`](../../codebase_map.json) | 机器可读的代码库清单（与 README 同步） |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | 贡献指南与 PR 要求 |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | 版本变更历史 |

## 验证命令

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1（格式检查 + 构建，语义证明深度 L-08）
./scripts/test_smoke.sh     # + Tier 2（跟踪 + 负状态 + 文档同步）
./scripts/test_full.sh      # + Tier 3（不变量表面锚点 + Lean #check 正确性）
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4（夜间确定性测试）
```

提交 PR 前至少运行 `test_smoke.sh`。如果修改了定理（theorem）、不变量（invariant）或文档锚点，则需运行 `test_full.sh`。

## 架构

seLe4n 按分层契约组织，每一层都包含可执行的状态转换和经过机器验证的不变量保持证明：

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
│          Platform  (Contract, Sim, RPi5)  ← H3-prep bindings         │
└──────────────────────────────────────────────────────────────────────┘
```

每个内核子系统遵循 **Operations/Invariant 分离**原则：状态转换位于 `Operations.lean`，证明位于 `Invariant.lean`。统一的 `apiInvariantBundle` 将所有子系统的不变量聚合为单一的证明义务。

## 与 seL4 的比较

| 特性 | seL4 | seLe4n |
|------|------|--------|
| **IPC 机制** | 单链表端点队列 | 侵入式双向队列，带 `queuePPrev` 反向指针，支持 O(1) 队中移除 |
| **信息流（information flow）** | 二元高/低分区 | N 域可配置流策略（泛化传统保密性 x 完整性标签） |
| **服务管理** | 不在内核中 | 一等服务编排，带依赖图和 DFS 环检测 |
| **能力派生（capability derivation）** | CDT 带链表子节点 | `childMap` HashMap 实现 O(1) 子节点查找 |
| **调度器（scheduler）** | 扁平优先级队列 | 按优先级分桶的 `RunQueue`，带内联 `maxPriority` 跟踪和 EDF |
| **虚拟地址空间（VSpace）** | 硬件页表 | `HashMap VAddr (PAddr x PagePermissions)`，强制 W^X |
| **证明方法论** | Isabelle/HOL，事后验证 | Lean 4 类型检查器，证明与状态转换并置 |
| **平台抽象** | C 级 HAL | `PlatformBinding` 类型类，带类型化边界契约 |

## 下一步

当前优先事项和完整的工作流历史记录维护在
[`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md) 中。概要：

- **WS-R** —— 综合审计修复（8 个阶段，R1–R8，111 个子任务）。针对 [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) 中的全部 82 项发现进行修复。R1–R7 已完成（v0.18.0–v0.18.6），R8 待处理。计划详见：[`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md)。
- **Raspberry Pi 5 硬件绑定** —— ARMv8 页表遍历、GIC-400 中断路由、引导序列（RPi5 平台契约已通过 WS-H15 实质化）

此前的工作流组合（WS-B 至 WS-Q）已全部完成。此前的审计（v0.8.0–v0.9.32）、里程碑结项报告和历史 GitBook 章节已归档至 [`docs/dev_history/`](../../dev_history/README.md)。

---

本文档翻译自 [English README](../../../README.md)。
