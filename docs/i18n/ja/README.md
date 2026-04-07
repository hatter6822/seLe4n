<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.25.19-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Lean 4 で記述され、機械検証済み証明を備えたマイクロカーネル。
  <a href="https://sel4.systems">seL4</a> アーキテクチャに着想を得た設計。初のハードウェアターゲット：
  <strong>Raspberry Pi 5</strong>。
</p>
<p align="center">
  <div align="center">
    以下の協力のもと丁寧に開発されています：
  </div>
  <div align="center">
    claude :robot: :heart: :robot: codex
  </div>
  <div align="center">
    <strong>このカーネルの性質をご理解の上ご利用ください</strong>
  </div>
</p>

<p align="center">
  <a href="../../../README.md">English</a> ·
  <a href="../zh-CN/README.md">简体中文</a> ·
  <a href="../es/README.md">Español</a> ·
  **日本語** ·
  <a href="../ko/README.md">한국어</a> ·
  <a href="../ar/README.md">العربية</a> ·
  <a href="../fr/README.md">Français</a> ·
  <a href="../pt-BR/README.md">Português</a> ·
  <a href="../ru/README.md">Русский</a> ·
  <a href="../de/README.md">Deutsch</a> ·
  <a href="../hi/README.md">हिन्दी</a>
</p>

---

## seLe4n とは

seLe4n は Lean 4 で一から構築されたマイクロカーネルです。すべてのカーネル遷移は実行可能な純粋関数として定義されています。すべての不変条件は Lean の型検査器によって機械検証されています――`sorry` ゼロ、`axiom` ゼロ。証明面全体が未承認の証明なしにネイティブコードへコンパイルされます。

本プロジェクトは seL4 のケイパビリティベースのセキュリティモデルを継承しつつ、Lean 4 の証明フレームワークによって可能になったアーキテクチャ改善を導入しています：

### スケジューリングとリアルタイム保証

- **合成可能なパフォーマンスオブジェクト** ―― CPU 時間はファーストクラスのカーネルオブジェクトです。`SchedContext` はバジェット、周期、優先度、デッドライン、ドメインを再利用可能なスケジューリングコンテキストにカプセル化し、スレッドはケイパビリティを通じてバインドします。CBS（Constant Bandwidth Server）スケジューリングにより、証明済みの帯域幅分離を提供します（`cbs_bandwidth_bounded` 定理）
- **パッシブサーバー** ―― アイドル状態のサーバーは IPC 中にクライアントの `SchedContext` を借用し、サービス提供時以外は CPU を消費しません。`donationChainAcyclic` 不変条件により循環ドネーションチェーンを防止します
- **バジェット駆動型 IPC タイムアウト** ―― ブロッキング操作は呼び出し元のバジェットによって制限されます。期限切れ時、スレッドはエンドポイントキューから取り出され再エンキューされます
- **優先度継承プロトコル** ―― 推移的な優先度伝搬と、機械検証されたデッドロックフリー保証（`blockingChainAcyclic`）および有界チェーン深度を備え、無制限の優先度逆転を防止します
- **有界レイテンシ定理** ―― 機械検証された WCRT 上界：`WCRT = D × L_max + N × (B + P)`。7 つの活性モジュールにわたって証明され、バジェット単調性、補充タイミング、yield セマンティクス、バンド枯渇、ドメインローテーションを網羅します

### データ構造と IPC

- **O(1) ハッシュベースのホットパス** ―― すべてのオブジェクトストア、ランキュー、CNode スロット、VSpace マッピング、IPC キューは、`distCorrect`、`noDupKeys`、`probeChainDominant` 不変条件を備えた形式検証済み Robin Hood ハッシュテーブルを使用
- **侵入型デュアルキュー IPC** ―― スレッドごとのバックポインタにより O(1) のエンキュー、デキュー、キュー途中削除を実現
- **ノード安定型ケイパビリティ派生ツリー** ―― `childMap` + `parentMap` インデックスにより O(1) のスロット転送、失効、子孫走査を実現

### セキュリティと検証

- **N ドメイン情報フロー** ―― パラメータ化されたフローポリシーにより seL4 の二値パーティションを一般化。30 エントリのエンフォースメント境界と、操作ごとの非干渉証明（32 コンストラクタの `NonInterferenceStep` 帰納型）
- **合成証明レイヤー** ―― `proofLayerInvariantBundle` が 10 のサブシステム不変条件（スケジューラ、ケイパビリティ、IPC、ライフサイクル、サービス、VSpace、クロスサブシステム、TLB、CBS 拡張）を単一のトップレベル義務に合成し、ブートからすべての操作まで検証
- **二段階状態アーキテクチャ** ―― 不変条件ウィットネス付きビルダーフェーズからフリーズされた不変表現へ遷移し、証明済みのルックアップ等価性を保証。20 のフリーズ操作がライブ API をミラー
- **完全な操作セット** ―― すべての seL4 操作が不変条件保存付きで実装済み。5 つの遅延操作（suspend/resume、setPriority/setMCPriority、setIPCBuffer）を含む
- **サービスオーケストレーション** ―― カーネルレベルのコンポーネントライフサイクル管理。依存グラフと証明済み非循環性を備える（seLe4n 独自の拡張、seL4 には存在しない）

## 現在の状態

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| 属性 | 値 |
|------|-----|
| **バージョン** | `0.25.5` |
| **Lean ツールチェーン** | `v4.28.0` |
| **本番 Lean コード行数** | 132 ファイルにわたる 83,286 行 |
| **テスト Lean コード行数** | 15 テストスイートにわたる 10,564 行 |
| **証明済み宣言数** | 2,447 件の定理/補題宣言（sorry/axiom ゼロ） |
| **ターゲットハードウェア** | Raspberry Pi 5（BCM2712 / ARM Cortex-A76 / ARMv8-A） |
| **最新監査** | [`AUDIT_COMPREHENSIVE_v0.23.21`](../../../docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) ―― カーネル全体 Lean + Rust 監査（0 CRIT、5 HIGH、8 MED、30 LOW） |
| **コードベースマップ** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) ―― 機械可読な宣言インベントリ |

メトリクスは `./scripts/generate_codebase_map.py` によってコードベースから導出され、
[`docs/codebase_map.json`](../../../docs/codebase_map.json) の `readme_sync` キーに格納されています。
`./scripts/report_current_state.py` をクロスチェックとして使用し、すべてのドキュメントを同時に更新してください。

## クイックスタート

```bash
./scripts/setup_lean_env.sh   # Lean ツールチェーンのインストール
lake build                     # 全モジュールのコンパイル
lake exe sele4n                # トレースハーネスの実行
./scripts/test_smoke.sh        # 検証（衛生チェック + ビルド + トレース + ネガティブステート + ドキュメント同期）
```

## ドキュメント

| まずはここから | 次に読む |
|-------------|---------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) ―― ワークフロー、検証、PR チェックリスト | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) ―― 仕様とマイルストーン |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) ―― 完全なハンドブック | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) ―― seL4 リファレンスセマンティクス |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) ―― 機械可読インベントリ | [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) ―― ワークストリーム履歴とロードマップ |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) ―― コントリビューション手順 | [`CHANGELOG.md`](../../../CHANGELOG.md) ―― バージョン履歴 |

[`docs/codebase_map.json`](../../../docs/codebase_map.json) はプロジェクトメトリクスの信頼できるソースであり、
[seLe4n.org](https://github.com/hatter6822/hatter6822.github.io) にデータを提供し、
マージ時に CI で自動更新されます。`./scripts/generate_codebase_map.py --pretty` で再生成できます。

## 検証コマンド

```bash
./scripts/test_fast.sh      # Tier 0+1：衛生チェック + ビルド
./scripts/test_smoke.sh     # + Tier 2：トレース + ネガティブステート + ドキュメント同期
./scripts/test_full.sh      # + Tier 3：不変条件サーフェスアンカー + Lean #check 正確性
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4：ナイトリー決定性検証
```

PR を提出する前に最低限 `test_smoke.sh` を実行してください。定理、不変条件、またはドキュメントアンカーを変更した場合は `test_full.sh` を実行してください。

## アーキテクチャ

seLe4n は階層化されたコントラクトとして構成されており、各層は実行可能な遷移と機械検証済みの不変条件保存証明を備えています：

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

## ソースレイアウト

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

各サブシステムは **Operations/Invariant 分離**パターンに従います：遷移は `Operations.lean` に、証明は `Invariant.lean` に記述されます。統合された `apiInvariantBundle` がすべてのサブシステムの不変条件を単一の証明義務に集約します。ファイルごとの完全なインベントリは [`docs/codebase_map.json`](../../../docs/codebase_map.json) を参照してください。

## seL4 との比較

| 機能 | seL4 | seLe4n |
|------|------|--------|
| **スケジューリング** | C 実装の散発サーバー（MCS） | CBS スケジューリング、機械検証済み `cbs_bandwidth_bounded` 定理付き。`SchedContext` をケイパビリティ制御のカーネルオブジェクトとして提供 |
| **パッシブサーバー** | C による SchedContext ドネーション | `donationChainAcyclic` 不変条件付きの検証済みドネーション |
| **IPC** | 単一リンクリストのエンドポイントキュー | 侵入型デュアルキューによる O(1) キュー途中削除、バジェット駆動型タイムアウト |
| **情報フロー** | 二値 high/low パーティション | N ドメイン設定可能ポリシー、30 エントリのエンフォースメント境界と操作ごとの NI 証明 |
| **優先度継承** | C 実装の PIP（MCS ブランチ） | 機械検証済みの推移的 PIP、デッドロックフリー保証とパラメトリック WCRT 上界付き |
| **有界レイテンシ** | 形式的な WCRT 上界なし | `WCRT = D × L_max + N × (B + P)` を 7 つの活性モジュールで証明 |
| **オブジェクトストア** | リンクリストと配列 | 検証済み Robin Hood ハッシュテーブル（`RHTable`/`RHSet`）による O(1) ホットパス |
| **サービス管理** | カーネル外 | ファーストクラスのオーケストレーション、依存グラフと非循環性証明付き |
| **証明手法** | Isabelle/HOL、事後検証 | Lean 4 型検査器、遷移と共存配置（2,447 定理、sorry/axiom ゼロ） |
| **プラットフォーム抽象化** | C レベル HAL | `PlatformBinding` 型クラスと型付き境界コントラクト |

## 次のステップ

ソフトウェアレベルのワークストリーム（WS-B から WS-AB）はすべて完了しています。
完全な履歴は [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) を参照してください。

### 完了したワークストリーム

| ワークストリーム | 範囲 | バージョン |
|---------------|------|----------|
| **WS-AB** | 遅延操作と活性――suspend/resume、setPriority/setMCPriority、setIPCBuffer、優先度継承プロトコル、有界レイテンシ定理（6 フェーズ、90 タスク） | v0.24.0–v0.25.5 |
| **WS-Z** | 合成可能パフォーマンスオブジェクト――`SchedContext` を第 7 のカーネルオブジェクトとして、CBS バジェットエンジン、補充キュー、パッシブサーバードネーション、タイムアウトエンドポイント（10 フェーズ、213 タスク） | v0.23.0–v0.23.21 |
| **WS-B – WS-Y** | コアカーネルサブシステム、Robin Hood ハッシュテーブル、基数木、フリーズ状態、情報フロー、サービスオーケストレーション、プラットフォームコントラクト | v0.9.0–v0.22.x |

詳細な計画：[WS-AB](../../../docs/dev_history/planning/WS_AB_DEFERRED_OPERATIONS_WORKSTREAM_PLAN.md) | [WS-Z](../../../docs/dev_history/planning/WS_Z_COMPOSABLE_PERFORMANCE_OBJECTS.md)

### 次の主要マイルストーン

**Raspberry Pi 5 ハードウェアバインディング** ―― ARMv8 ページテーブルウォーク、GIC-400 割り込みルーティング、ブートシーケンス。過去の監査とマイルストーンクローズアウトは [`docs/dev_history/`](../../../docs/dev_history/README.md) にアーカイブされています。

---

このドキュメントは [English README](../../../README.md) の翻訳です。
