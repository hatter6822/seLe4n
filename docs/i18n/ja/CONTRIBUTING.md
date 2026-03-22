# seLe4n への貢献

seLe4n にご貢献いただきありがとうございます。seLe4n は Lean 4 で記述され、機械検証済み証明を備えた本番志向のマイクロカーネル (microkernel) です。

---

🌐 [English](../../../CONTRIBUTING.md) | **日本語**

---

## ライセンス

seLe4n は [GNU General Public License v3.0 以降](../../../LICENSE) の下でライセンスされています。プルリクエストの提出またはコードの貢献をもって、お客様の貢献物が同一の GPL-3.0-or-later ライセンスの下で提供されることに同意したものとみなされます。また、当該ライセンスの下で貢献を提出する権利を有していることを証明するものとします。

## 5 分間コントリビューターパス

以下のドキュメントを順に確認することで、貢献に必要な知識を素早く把握できます：

1. **ワークフローと標準:** [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)
2. **テスト段階:** [`docs/TESTING_FRAMEWORK_PLAN.md`](../../../docs/TESTING_FRAMEWORK_PLAN.md)
3. **CI ポリシー:** [`docs/CI_POLICY.md`](../../../docs/CI_POLICY.md)
4. **プロジェクトスコープとワークストリーム:** [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md)
5. **ワークストリーム履歴:** [`docs/WORKSTREAM_HISTORY.md`](../../../docs/WORKSTREAM_HISTORY.md)

完全なハンドブック: [`docs/gitbook/README.md`](../../../docs/gitbook/README.md)

## 開発環境のセットアップ

```bash
# Lean ツールチェーンと依存関係のインストール
./scripts/setup_lean_env.sh

# ビルド
source ~/.elan/env && lake build

# トレースハーネスの実行
lake exe sele4n
```

### 前提条件

- **Lean 4** (v4.28.0) — `setup_lean_env.sh` により自動インストールされます
- **Lake** — Lean のビルドシステム（ツールチェーンに同梱）
- **Git** — バージョン管理

## PR 提出前の必須検証

```bash
./scripts/test_smoke.sh     # 最低限のゲート（Tier 0〜2）
./scripts/test_full.sh      # 定理 (theorem) / 不変条件 (invariant) の変更時に必須（Tier 0〜3）
```

### 検証コマンドの詳細

| コマンド | 対象 Tier | 内容 |
|---------|----------|------|
| `./scripts/test_fast.sh` | Tier 0 + 1 | 衛生チェック + ビルド |
| `./scripts/test_smoke.sh` | Tier 0〜2 | + トレース + ネガティブステート + ドキュメント同期 |
| `./scripts/test_full.sh` | Tier 0〜3 | + 不変条件サーフェスアンカー + Lean `#check` 正確性検証 |
| `./scripts/test_nightly.sh` | Tier 0〜4 | + ナイトリー決定性検証（`NIGHTLY_ENABLE_EXPERIMENTAL=1` 要設定） |

## モジュールビルド検証（必須）

`.lean` ファイルをコミットする前に、変更したモジュールが個別にコンパイルされることを確認してください：

```bash
source ~/.elan/env && lake build <Module.Path>
```

例えば `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` を変更した場合：

```bash
source ~/.elan/env && lake build SeLe4n.Kernel.IPC.Operations.Endpoint
```

**`lake build`（デフォルトターゲット）だけでは不十分です。** デフォルトターゲットは `Main.lean` から到達可能なモジュールのみをビルドします。メインカーネルからまだインポートされていないモジュールは、証明が壊れていても `lake build` を通過してしまいます。

### pre-commit フックのインストール

```bash
cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit
```

このフックは以下を自動的に実行します：

1. ステージングされた `.lean` ファイルを検出
2. 変更された各モジュールを `lake build <Module.Path>` でビルド
3. ステージングされた内容に `sorry` がないか確認
4. ビルド失敗または `sorry` 検出時にコミットをブロック

`--no-verify` でフックをバイパスしないでください。

## PR 要件

### チェックリスト

- [ ] ワークストリーム ID の特定
- [ ] スコープが一つの整合性のある単位であること
- [ ] 遷移が決定的であること（明示的な成功/失敗）
- [ ] 不変条件 (invariant) / 定理 (theorem) の更新が実装変更と対になっていること
- [ ] ドキュメントが同一 PR 内で同期されていること
- [ ] ウェブサイトリンクのパスが変更・削除されていないこと（`scripts/website_link_manifest.txt` を参照）

### コーディング規約

- **`sorry`/`axiom` の禁止** — 本番の証明面では使用禁止です。追跡対象の例外には `TPI-D*` アノテーションが必要です。
- **決定的セマンティクス** — すべての遷移は明示的な成功/失敗を返す必要があります。非決定的な分岐を導入しないでください。
- **型付き識別子** — `ThreadId`、`ObjId`、`CPtr`、`Slot`、`DomainId` 等はラッパー構造体であり、`Nat` のエイリアスではありません。明示的に `.toNat`/`.ofNat` を使用してください。
- **Operations/Invariant 分離** — 各カーネルサブシステムは遷移用の `Operations.lean` と証明用の `Invariant.lean` を分離して管理します。
- **内部優先の命名規則** — 定理/関数/定義の名前はセマンティクス（状態更新の形状、保存される不変条件、遷移パス）を記述する必要があります。ワークストリーム ID（`WS-*`、`wsH*` 等）を識別子名にエンコードしないでください。

### ドキュメント更新規則

動作、定理、またはワークストリームステータスを変更する場合、同一 PR 内で以下を更新してください：

1. `README.md` — `docs/codebase_map.json`（`readme_sync` キー）からのメトリクス同期
2. `docs/spec/SELE4N_SPEC.md`
3. `docs/DEVELOPMENT.md`
4. 影響を受ける GitBook チャプター（正規のルートドキュメントが GitBook より優先）
5. `docs/CLAIM_EVIDENCE_INDEX.md`（クレームが変更された場合）
6. `docs/WORKSTREAM_HISTORY.md`（ワークストリームステータスが変更された場合）
7. `docs/codebase_map.json` の再生成（Lean ソースが変更された場合）

## セキュリティ脆弱性の報告

コードベースで作業中に CVE 指定の対象となり得るソフトウェア脆弱性を発見した場合は、直ちに報告してください。サイレントに修正せず、適切な追跡、トリアージ、開示が行えるよう明示的にフラグを立ててください。

## お問い合わせ

ご質問やご不明な点がございましたら、GitHub Issues をご利用ください。

---

このドキュメントは [English CONTRIBUTING.md](../../../CONTRIBUTING.md) の翻訳です。
