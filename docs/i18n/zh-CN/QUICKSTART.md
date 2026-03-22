🌐 [English](../../../README.md#quick-start) | **简体中文** | [Español](../es/QUICKSTART.md) | [日本語](../ja/QUICKSTART.md) | [한국어](../ko/QUICKSTART.md) | [العربية](../ar/QUICKSTART.md) | [Français](../fr/QUICKSTART.md) | [Português](../pt-BR/QUICKSTART.md) | [Русский](../ru/QUICKSTART.md) | [Deutsch](../de/QUICKSTART.md) | [हिन्दी](../hi/QUICKSTART.md)

---

# 快速入门指南

本指南将帮助您从零开始搭建 seLe4n 开发环境、构建项目并运行测试。

## 前提条件

- **Git** —— 用于克隆代码仓库
- **网络连接** —— 首次设置时需下载 Lean 4 工具链（约 1 GB）
- **Linux 或 macOS** —— 推荐的开发平台（Windows 用户请使用 WSL2）

无需预先安装 Lean 4。安装脚本会通过 [elan](https://github.com/leanprover/elan) 自动管理 Lean 工具链。

## 第一步：克隆代码仓库

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

## 第二步：安装开发环境

运行环境配置脚本以安装 Lean 4 工具链和构建系统 Lake：

```bash
./scripts/setup_lean_env.sh
```

此脚本将：
- 安装 [elan](https://github.com/leanprover/elan)（Lean 版本管理器）
- 安装项目指定的 Lean v4.28.0 工具链
- 安装测试依赖项（shellcheck、ripgrep）

如果只需安装核心工具链而不安装测试依赖项：

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

安装完成后，请确保环境变量已加载：

```bash
source ~/.elan/env
```

## 第三步：构建项目

```bash
lake build
```

首次构建需要下载依赖项并编译所有模块，可能需要几分钟。后续的增量构建会快得多。

## 第四步：运行跟踪测试工具

```bash
lake exe sele4n
```

此命令会执行主跟踪测试工具（trace harness），运行一系列内核状态转换并输出结果。输出将与 `tests/fixtures/main_trace_smoke.expected` 中的预期结果进行比对。

## 第五步：运行测试

seLe4n 采用分层测试体系，按严格程度递增排列：

### Tier 0 + Tier 1：格式检查与构建

```bash
./scripts/test_fast.sh
```

检查代码格式规范并确认所有模块能够编译通过。这是最快速的验证方式。

### Tier 0-2：烟雾测试（最低 PR 门控要求）

```bash
./scripts/test_smoke.sh
```

在 Tier 0-1 的基础上，增加跟踪验证（trace validation）、负状态测试（negative-state tests）和文档同步检查。**提交 PR 前至少需通过此测试。**

### Tier 0-3：完整测试

```bash
./scripts/test_full.sh
```

在 Tier 0-2 的基础上，增加不变量（invariant）表面锚点验证和 Lean `#check` 正确性检查。**修改定理（theorem）或不变量时需运行此测试。**

### Tier 0-4：夜间测试

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

包含所有层级的测试以及夜间确定性验证。适用于发布前的全面检查。

## 架构概览

seLe4n 按分层契约组织，从底层基础到顶层 API：

| 层级 | 说明 |
|------|------|
| **Platform** | 平台绑定（simulation 仿真 / Raspberry Pi 5） |
| **Foundations** | 类型化标识符、机器状态原语 |
| **Model** | 内核对象（TCB、Endpoint、Notification、CNode 等） |
| **Architecture** | 虚拟地址空间（VSpace）、寄存器解码 |
| **Information Flow** | 安全标签、投影、非干扰（non-interference）证明 |
| **Kernel Subsystems** | 调度器（Scheduler）、能力（Capability）、IPC、生命周期（Lifecycle）、服务（Service） |
| **Kernel API** | 统一公共接口与 `apiInvariantBundle` |

每个子系统遵循 **Operations/Invariant 分离**原则：
- `Operations.lean` —— 状态转换（可执行纯函数）
- `Invariant.lean` —— 不变量保持证明（定理）

## 下一步

环境搭建完成后，建议按以下顺序深入了解项目：

1. [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md) —— 日常开发流程与 PR 检查清单
2. [`docs/gitbook/README.md`](../../gitbook/README.md) —— 完整手册（架构详解、证明体系、硬件路径）
3. [`docs/spec/SELE4N_SPEC.md`](../../spec/SELE4N_SPEC.md) —— 项目规格说明与里程碑
4. [`docs/codebase_map.json`](../../codebase_map.json) —— 机器可读的模块与声明清单
5. [`CONTRIBUTING.md`](CONTRIBUTING.md) —— 贡献指南

## 常见问题

### `lake build` 报错找不到工具链？

请确保已运行 `source ~/.elan/env` 或重新打开终端。如果问题持续，尝试重新运行：

```bash
./scripts/setup_lean_env.sh
source ~/.elan/env
```

### 构建很慢？

首次构建需要编译所有模块和依赖项，这是正常的。后续构建只会重新编译发生变化的模块。

### 测试失败？

请确保使用项目指定的 Lean 工具链版本（v4.28.0）。运行 `lean --version` 确认版本。如果版本不匹配，请删除 `lake-packages/` 并重新构建。

---

本文档翻译自 [English README](../../../README.md)。
