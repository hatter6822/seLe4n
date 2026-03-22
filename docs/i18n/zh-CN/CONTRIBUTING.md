🌐 [English](../../../CONTRIBUTING.md) | **简体中文** | [Español](../es/CONTRIBUTING.md) | [日本語](../ja/CONTRIBUTING.md) | [한국어](../ko/CONTRIBUTING.md) | [العربية](../ar/CONTRIBUTING.md) | [Français](../fr/CONTRIBUTING.md) | [Português](../pt-BR/CONTRIBUTING.md) | [Русский](../ru/CONTRIBUTING.md) | [Deutsch](../de/CONTRIBUTING.md) | [हिन्दी](../hi/CONTRIBUTING.md)

---

# 为 seLe4n 做贡献

感谢您为 seLe4n 做出贡献——一个使用 Lean 4 编写并附带机器验证证明的生产级微内核（microkernel）。

## 许可证

seLe4n 基于 [GNU 通用公共许可证 v3.0 或更高版本](../../../LICENSE) 发布。提交拉取请求（pull request）或贡献代码即表示您同意您的贡献将以相同的 GPL-3.0-or-later 许可证发布。您同时保证您有权在此许可证下提交该贡献。

## 五分钟贡献者入门路径

1. **开发流程与标准：** [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md)
2. **分层测试体系：** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../TESTING_FRAMEWORK_PLAN.md)
3. **CI 策略：** [`docs/CI_POLICY.md`](../../CI_POLICY.md)
4. **项目范围与工作流：** [`docs/spec/SELE4N_SPEC.md`](../../spec/SELE4N_SPEC.md)
5. **活跃审计发现：** [`docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md)
6. **工作流历史：** [`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md)

完整手册：[`docs/gitbook/README.md`](../../gitbook/README.md)

## 提交 PR 前的必要验证

```bash
./scripts/test_smoke.sh     # 最低门控要求（Tier 0-2）
./scripts/test_full.sh      # 修改定理/不变量时需运行（Tier 0-3）
```

在打开拉取请求之前，**至少**需通过 `test_smoke.sh`。如果您的变更涉及定理（theorem）、不变量（invariant）或文档锚点，请运行 `test_full.sh`。

## PR 要求

- **标识工作流 ID** —— 注明本次 PR 推进了哪个（些）工作流
- **保持范围聚焦** —— 每个 PR 应为一个连贯的功能切片
- **确定性语义** —— 所有状态转换（transition）必须是确定性的，采用显式的成功/失败返回
- **证明与实现成对提交** —— 不变量/定理的更新必须与实现变更在同一个 PR 中提交
- **同步文档** —— 在同一个 PR 中更新所有受影响的文档
- **禁止 sorry/axiom** —— 生产证明层面禁止使用 `sorry` 或 `axiom`

完整的 PR 检查清单请参见 [`docs/DEVELOPMENT.md`](../../DEVELOPMENT.md)。

## 代码组织约定

- **Operations/Invariant 分离** —— 每个内核子系统将状态转换（`Operations.lean`）和证明（`Invariant.lean`）分文件管理
- **类型化标识符** —— 使用 `ThreadId`、`ObjId`、`CPtr`、`Slot`、`DomainId` 等封装结构，而非裸 `Nat` 别名
- **语义化命名** —— 定理、函数和定义的名称应描述语义（状态更新形状、保持的不变量、转换路径），而非编码工作流 ID

## 验证命令

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1：格式检查 + 构建
./scripts/test_smoke.sh     # + Tier 2：跟踪 + 负状态 + 文档同步
./scripts/test_full.sh      # + Tier 3：不变量表面锚点 + Lean #check 正确性
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4：夜间确定性测试
```

## 模块构建验证

**在提交任何 `.lean` 文件之前**，您必须验证该模块能够编译通过：

```bash
source ~/.elan/env && lake build <Module.Path>
```

例如，如果修改了 `SeLe4n/Kernel/RobinHood/Bridge.lean`：

```bash
lake build SeLe4n.Kernel.RobinHood.Bridge
```

**`lake build`（默认目标）是不够的。** 默认目标只会构建从 `Main.lean` 和测试可执行文件可达的模块。尚未被主内核导入的模块（如集成前的 `RobinHood`）即使存在证明错误，`lake build` 也会静默通过。

## 获取帮助

如有疑问，请查阅以下资源：

- 完整手册：[`docs/gitbook/README.md`](../../gitbook/README.md)
- 项目规格说明：[`docs/spec/SELE4N_SPEC.md`](../../spec/SELE4N_SPEC.md)
- 工作流历史：[`docs/WORKSTREAM_HISTORY.md`](../../WORKSTREAM_HISTORY.md)

---

本文档翻译自 [English CONTRIBUTING.md](../../../CONTRIBUTING.md)。
