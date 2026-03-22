# seLe4n クイックスタートガイド

Lean 4 で記述され、機械検証済み証明を備えた本番志向のマイクロカーネル (microkernel)、seLe4n を素早く始めるためのガイドです。

---

🌐 [English](../../../README.md#quick-start) | **日本語**

---

## 前提条件

- **Linux** または **macOS**（x86_64 / ARM64）
- **Git**（バージョン管理用）
- **curl** または **wget**（Lean ツールチェーンのダウンロード用）
- インターネット接続（初回セットアップ時）

## 環境セットアップ

### 手順 1: リポジトリのクローン

```bash
git clone https://github.com/hatter6822/seLe4n.git
cd seLe4n
```

### 手順 2: Lean ツールチェーンのインストール

セットアップスクリプトが Lean 4 (v4.28.0) と Lake ビルドシステムを自動的にインストールします：

```bash
./scripts/setup_lean_env.sh
```

このスクリプトは以下を実行します：

- **elan**（Lean のバージョンマネージャ）のインストール（未インストールの場合）
- プロジェクトが必要とする正確な Lean ツールチェーンバージョンの設定
- テスト依存関係（shellcheck、ripgrep）のインストール

テスト依存関係が不要な場合は、軽量セットアップオプションを使用できます：

```bash
./scripts/setup_lean_env.sh --skip-test-deps
```

### 手順 3: 環境変数の読み込み

elan を新規にインストールした場合、パスを読み込む必要があります：

```bash
source ~/.elan/env
```

## ビルドと実行

### プロジェクトのビルド

```bash
lake build
```

初回ビルドでは依存関係のダウンロードとコンパイルが行われるため、時間がかかる場合があります。以降のビルドはインクリメンタルに実行されます。

### 特定モジュールのビルド

特定のモジュールのみをビルドする場合：

```bash
lake build SeLe4n.Kernel.Scheduler.Operations
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
lake build SeLe4n.Kernel.RobinHood.Core
```

**重要:** `.lean` ファイルを変更した場合、`lake build` だけでなく、変更したモジュールを個別にビルドして検証してください。デフォルトターゲットは `Main.lean` から到達可能なモジュールのみをビルドするため、未接続のモジュールのエラーを見逃す可能性があります。

### トレースハーネスの実行

```bash
lake exe sele4n
```

トレースハーネスは、カーネル遷移の実行トレースを生成し、期待される出力（`tests/fixtures/main_trace_smoke.expected`）と照合します。

## テストと検証

seLe4n は段階的な検証システムを採用しています。目的に応じて適切なレベルを選択してください：

### Tier 0 + 1: 高速検証（衛生チェック + ビルド）

```bash
./scripts/test_fast.sh
```

日常の開発中に素早く実行できる最小限の検証です。コードの衛生状態とビルドの成功を確認します。

### Tier 0〜2: スモーク検証（推奨最小限）

```bash
./scripts/test_smoke.sh
```

**PR 提出前に最低限必須です。** 以下を検証します：

- 衛生チェック（sorry/axiom の不在確認）
- 全モジュールのビルド
- トレースハーネスの実行と期待値との照合
- ネガティブステートテスト
- ドキュメント同期の確認

### Tier 0〜3: フル検証

```bash
./scripts/test_full.sh
```

定理 (theorem)、不変条件 (invariant)、またはドキュメントアンカーを変更した場合に必須です。上記に加え、不変条件サーフェスアンカーと Lean `#check` の正確性検証を実施します。

### Tier 0〜4: ナイトリー検証

```bash
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
```

最も包括的な検証スイートです。決定性の検証を含みます。

## プロジェクト構造の概要

```
seLe4n/
├── SeLe4n/                    # メインカーネルソース
│   ├── Prelude.lean           # 型付き識別子、KernelM モナド
│   ├── Machine.lean           # レジスタファイル、メモリ、タイマー
│   ├── Model/                 # カーネルオブジェクトと状態の定義
│   │   ├── Object/            # TCB、Endpoint、Notification、CNode 等
│   │   └── State.lean         # SystemState
│   ├── Kernel/                # カーネルサブシステム
│   │   ├── Scheduler/         # EDF + 優先度スケジューリング
│   │   ├── Capability/        # CSpace 操作と CDT 管理
│   │   ├── IPC/               # デュアルキュー IPC
│   │   ├── Lifecycle/         # オブジェクトの Retype
│   │   ├── Service/           # サービスオーケストレーション
│   │   ├── Architecture/      # VSpace、RegisterDecode
│   │   ├── InformationFlow/   # セキュリティラベルと非干渉性証明
│   │   ├── RobinHood/         # 検証済み Robin Hood ハッシュテーブル
│   │   ├── RadixTree/         # CNode 基数木
│   │   ├── FrozenOps/         # 凍結カーネル操作
│   │   └── API.lean           # 統合公開 API
│   ├── Platform/              # プラットフォーム抽象化
│   │   ├── Contract.lean      # PlatformBinding 型クラス
│   │   ├── Sim/               # シミュレーションプラットフォーム
│   │   └── RPi5/              # Raspberry Pi 5 プラットフォーム
│   └── Testing/               # テストハーネスとフィクスチャ
├── Main.lean                  # 実行可能エントリーポイント
├── tests/                     # テストスイート
├── docs/                      # ドキュメント
│   ├── spec/                  # 仕様書
│   ├── gitbook/               # ハンドブック
│   └── audits/                # 監査レポート
└── scripts/                   # ビルド・テストスクリプト
```

## 主要な概念

### Operations/Invariant 分離

各カーネルサブシステムは二つのファイルに分割されています：

- **`Operations.lean`** — 状態遷移を定義する実行可能な純粋関数
- **`Invariant.lean`** — 遷移が不変条件を保存することの機械検証済み証明

この分離により、実装と証明を独立して管理・レビューできます。

### 型付き識別子

seLe4n では、生の `Nat` の代わりに型付きラッパーを使用します：

- `ThreadId` — スレッド識別子
- `ObjId` — オブジェクト識別子
- `CPtr` — ケイパビリティポインタ
- `Slot` — スロット番号
- `DomainId` — ドメイン識別子

変換には `.toNat` および `.ofNat` を明示的に使用してください。

### sorry/axiom ゼロポリシー

本番コードでは `sorry`（未証明のマーカー）と `axiom`（公理）の使用が禁止されています。すべての定理は Lean の型検査器によって完全に検証されている必要があります。

## 次のステップ

環境のセットアップが完了したら、以下を参照してください：

1. **[開発ガイド](../../../docs/DEVELOPMENT.md)** — 日常のワークフロー、検証ループ、PR チェックリスト
2. **[コントリビューションガイド](./CONTRIBUTING.md)** — 貢献の手順と要件
3. **[プロジェクト仕様](../../../docs/spec/SELE4N_SPEC.md)** — プロジェクトの全体像とマイルストーン
4. **[ハンドブック](../../../docs/gitbook/README.md)** — アーキテクチャの詳細解説、証明戦略、ハードウェアパス

## トラブルシューティング

### `lake build` が失敗する場合

1. Lean ツールチェーンのバージョンを確認してください：
   ```bash
   lean --version
   # 期待値: leanprover/lean4:v4.28.0
   ```

2. ツールチェーンが正しくない場合は、再セットアップを実行してください：
   ```bash
   ./scripts/setup_lean_env.sh
   source ~/.elan/env
   ```

3. キャッシュをクリアして再ビルドしてください：
   ```bash
   lake clean
   lake build
   ```

### elan が見つからない場合

パスの読み込みを確認してください：

```bash
source ~/.elan/env
```

恒久的に設定するには、シェルの設定ファイル（`~/.bashrc` や `~/.zshrc`）に以下を追加してください：

```bash
source ~/.elan/env
```

### テストが失敗する場合

テスト依存関係がインストールされていることを確認してください：

```bash
./scripts/setup_lean_env.sh  # --skip-test-deps なしで実行
```

---

このドキュメントは seLe4n プロジェクトのクイックスタートガイドの日本語翻訳です。最新の情報については [English README](../../../README.md) を参照してください。
