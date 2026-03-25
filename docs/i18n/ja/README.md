<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n ロゴ" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.21.7-blue" alt="Version" />
  <img src="https://img.shields.io/badge/Lean-v4.28.0-blueviolet" alt="Lean 4" />
  <a href="../../../LICENSE"><img src="https://img.shields.io/badge/license-GPLv3-blue" alt="License" /></a>
</p>

<p align="center">
  Lean 4 で記述され、機械検証済み証明を備えた本番志向のマイクロカーネル (microkernel)。<br/>
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

---

🌐 [English](../../../README.md) | [简体中文](../zh-CN/README.md) | [Español](../es/README.md) | **日本語** | [한국어](../ko/README.md) | [العربية](../ar/README.md) | [Français](../fr/README.md) | [Português](../pt-BR/README.md) | [Русский](../ru/README.md) | [Deutsch](../de/README.md) | [हिन्दी](../hi/README.md)

---

## seLe4n とは

seLe4n は Lean 4 で一から構築されたマイクロカーネル (microkernel) です。すべてのカーネル遷移は実行可能な純粋関数として定義されており、すべての不変条件 (invariant) は Lean の型検査器によって機械検証されています — `sorry` ゼロ、`axiom` ゼロ。証明面全体が未承認の証明なしにネイティブコードへコンパイルされます。

本プロジェクトはケイパビリティ (capability) ベースのセキュリティモデルを採用しつつ、他のマイクロカーネルと比較して以下の新規アーキテクチャ改善を導入しています：

- **O(1) ハッシュベースのカーネルホットパス** — すべてのオブジェクトストア、ランキュー、CNode スロット、VSpace マッピング、IPC キューは、形式検証済みの `RHTable`/`RHSet`（Robin Hood ハッシュテーブル、機械検証済み不変条件付き、状態内に `Std.HashMap`/`Std.HashSet` ゼロ）を使用
- **サービスオーケストレーション層** — コンポーネントのライフサイクルと依存関係管理を担い、決定的な部分障害セマンティクスを提供
- **ノード安定型ケイパビリティ派生ツリー (CDT)** — `childMap` + `parentMap` の RHTable インデックスにより、O(1) でのスロット転送、失効 (revocation)、親参照、子孫走査を実現
- **侵入型デュアルキュー IPC** — スレッドごとの `queuePrev`/`queuePPrev`/`queueNext` リンクにより、O(1) でのエンキュー、デキュー、キュー途中の削除を実現
- **パラメータ化された N ドメイン情報フロー (information flow) フレームワーク** — 設定可能なフローポリシーにより、従来の機密性/完全性ラベルを一般化（seL4 の二値パーティションを超越）
- **EDF + 優先度スケジューリング (scheduling)** — ディスパッチ時デキューセマンティクス、TCB ごとのレジスタコンテキストとインラインコンテキストスイッチ、優先度バケット型 `RunQueue`、ドメイン対応パーティショニング

## 現在の状態

| 属性 | 値 |
|------|-----|
| **バージョン** | `0.21.7` |
| **Lean ツールチェーン** | `v4.28.0` |
| **本番 Lean コード行数** | 101 ファイルにわたる 64,824 行 |
| **テスト Lean コード行数** | 10 テストスイートにわたる 8,322 行 |
| **証明済み宣言数** | 1,922 件の定理 (theorem) / 補題 (lemma) 宣言（sorry/axiom ゼロ） |
| **ターゲットハードウェア** | Raspberry Pi 5（BCM2712 / ARM Cortex-A76 / ARMv8-A） |
| **最新監査** | [`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) — カーネル全体 + Rust コードベースのプレリリース監査 |
| **コードベースマップ** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 機械可読な宣言インベントリ |

メトリクスは `./scripts/generate_codebase_map.py` によってコードベースから導出され、[`docs/codebase_map.json`](../../../docs/codebase_map.json) の `readme_sync` キーに格納されています。

## クイックスタート

```bash
./scripts/setup_lean_env.sh   # Lean ツールチェーンのインストール
lake build                     # 全モジュールのコンパイル
lake exe sele4n                # トレースハーネスの実行
./scripts/test_smoke.sh        # 検証（衛生チェック + ビルド + トレース + ネガティブステート + ドキュメント同期）
```

## オンボーディングパス

本プロジェクトが初めての方は、以下の順序で読み進めてください：

1. **この README** — プロジェクトの概要、アーキテクチャ、ソースレイアウト
2. [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — 日常のワークフロー、検証ループ、PR チェックリスト
3. [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — 完全なハンドブック（アーキテクチャの詳細解説、証明、ハードウェアパス）
4. [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 機械可読なモジュール・宣言インベントリ

ワークストリームの計画と履歴については [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) を参照してください。

## プロジェクトドキュメント

| ドキュメント | 目的 |
|------------|------|
| [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) | プロジェクト仕様とマイルストーン |
| [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) | seL4 リファレンスセマンティクス |
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) | 日常のワークフロー、検証ループ、PR チェックリスト |
| [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md) | 段階的テストゲートと CI コントラクト |
| [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) | ワークストリーム完全履歴、ロードマップ、監査計画インデックス |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) | 完全なハンドブック（アーキテクチャ、設計、証明、ハードウェアパス） |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) | 機械可読なコードベースインベントリ（README と同期） |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) | コントリビューションの手順と PR 要件 |
| [`CHANGELOG.md`](../../../CHANGELOG.md) | バージョン履歴 |

## 検証コマンド

```bash
./scripts/test_fast.sh      # Tier 0 + Tier 1（衛生チェック + ビルド、セマンティック証明深度 L-08）
./scripts/test_smoke.sh     # + Tier 2（トレース + ネガティブステート + ドキュメント同期）
./scripts/test_full.sh      # + Tier 3（不変条件サーフェスアンカー + Lean #check 正確性検証）
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh  # + Tier 4（ナイトリー決定性検証）
```

PR を提出する前に最低限 `test_smoke.sh` を実行してください。定理 (theorem)、不変条件 (invariant)、またはドキュメントアンカーを変更した場合は `test_full.sh` を実行してください。

## アーキテクチャ

seLe4n は階層化されたコントラクトとして構成されており、各層は実行可能な遷移と機械検証済みの不変条件保存証明を備えています：

```
┌──────────────────────────────────────────────────────────────────────┐
│                 Kernel API  (SeLe4n/Kernel/API.lean)                 │
├──────────────┬─────────────┬────────────┬───────────┬────────────────┤
│  スケジューラ │ ケイパビリティ│    IPC     │ライフサイクル│ サービス (ext) │
│  RunQueue    │  CSpace/CDT │  DualQueue │  Retype   │ オーケストレーション│
├──────────────┴─────────────┴────────────┴───────────┴────────────────┤
│       情報フロー (Information Flow)  (Policy, Projection, Enforcement)│
├──────────────────────────────────────────────────────────────────────┤
│   アーキテクチャ (VSpace, VSpaceBackend, Adapter, Assumptions)        │
├──────────────────────────────────────────────────────────────────────┤
│                  モデル (Object, State, CDT)                         │
├──────────────────────────────────────────────────────────────────────┤
│           基盤 (Prelude, Machine, MachineConfig)                     │
├──────────────────────────────────────────────────────────────────────┤
│        プラットフォーム (Contract, Sim, RPi5)  ← H3-prep バインディング │
└──────────────────────────────────────────────────────────────────────┘
```

各カーネルサブシステムは **Operations/Invariant 分離** パターンに従います：遷移は `Operations.lean` に、証明は `Invariant.lean` に記述されます。統合された `apiInvariantBundle` がすべてのサブシステムの不変条件を単一の証明義務に集約します。

## seL4 との比較

| 機能 | seL4 | seLe4n |
|------|------|--------|
| **IPC メカニズム** | 単一リンクリストのエンドポイントキュー | `queuePPrev` バックポインタ付き侵入型デュアルキューによる O(1) キュー途中削除 |
| **情報フロー** | 二値 high/low パーティション | N ドメイン設定可能フローポリシー（従来の機密性 × 完全性ラベルを一般化） |
| **サービス管理** | カーネル外 | ファーストクラスのサービスオーケストレーション（依存グラフと DFS 循環検出付き） |
| **ケイパビリティ派生** | リンクリスト子ノードの CDT | `childMap` HashMap による O(1) 子ノード参照 |
| **スケジューラ (scheduler)** | フラット優先度キュー | インライン `maxPriority` 追跡と EDF 付き優先度バケット型 `RunQueue` |
| **VSpace** | ハードウェアページテーブル | `HashMap VAddr (PAddr x PagePermissions)` と W^X 強制 |
| **証明手法** | Isabelle/HOL、事後検証 | Lean 4 型検査器、証明と遷移の共存配置 |
| **プラットフォーム抽象化** | C レベル HAL | `PlatformBinding` 型クラスと型付き境界コントラクト |

## 次のステップ

現在の優先事項と完全なワークストリーム履歴は [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md) に管理されています。概要：

- **WS-R** — 包括的監査是正（8 フェーズ、R1〜R8、111 サブタスク）。[`AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md`](../../../docs/dev_history/audits/AUDIT_COMPREHENSIVE_v0.17.13_PRE_RELEASE.md) の全 82 件の発見事項に対応。R1〜R7 完了（v0.18.0〜v0.18.6）、R8 は保留中。計画：[`AUDIT_v0.17.14_WORKSTREAM_PLAN.md`](../../../docs/dev_history/audits/AUDIT_v0.17.14_WORKSTREAM_PLAN.md)。
- **Raspberry Pi 5 ハードウェアバインディング** — ARMv8 ページテーブルウォーク、GIC-400 割り込みルーティング、ブートシーケンス（WS-H15 により RPi5 プラットフォームコントラクトは実質的な内容に整備済み）

過去のポートフォリオ（WS-B〜WS-Q）はすべて完了しています。過去の監査（v0.8.0〜v0.9.32）、マイルストーンクローズアウト、レガシー GitBook チャプターは [`docs/dev_history/`](../../../docs/dev_history/README.md) にアーカイブされています。

---

このドキュメントは [English README](../../../README.md) の翻訳です。
