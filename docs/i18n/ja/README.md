<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="../../../assets/logo_dark.png" />
    <img src="../../../assets/logo.png" alt="seLe4n logo" width="200" />
  </picture>
</p>

<p align="center">
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/lean_action_ci.yml/badge.svg?branch=main" alt="CI" /></a>
  <a href="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml"><img src="https://github.com/hatter6822/seLe4n/actions/workflows/platform_security_baseline.yml/badge.svg" alt="Security" /></a>
  <img src="https://img.shields.io/badge/version-0.37.37-blue" alt="Version" />
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
  <a href="../hi/README.md">हिन्दी</a> ·
  <a href="../uk/README.md">Українська</a>
</p>

---

## seLe4n とは

seLe4n は Lean 4 でゼロから構築されたマイクロカーネルです。カーネルのすべての
遷移は実行可能な純粋関数であり、すべての不変条件は Lean のカーネルが検査しま
す。本番の証明面には `sorry` も `axiom` もありません。同じ Lean コードがネイティ
ブコードにコンパイルされ、小さな Rust のハードウェア層とともに、ターゲット上で
起動するカーネルイメージにリンクされます。

本プロジェクトは seL4 のケイパビリティベースのセキュリティモデルと、ますます
seL4 のユーザーから見える ABI そのものを保ちながら、Lean を使ってより多くを証明
し、seL4 が隙間を残す箇所を強化します。完全な仕様は
[`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) です。以下の項目はその
仕様への入口です。

### seL4 の ABI

- **seL4-MCS のシステムコール** — MCS の 11 個のシステムコール（`Call` …
  `Yield`）を、seL4 と同じ番号で `x7` に置きます。操作は、システムコール、呼び出
  したケイパビリティの型、メッセージラベルから選ばれます
  （`Syscall.selectOperation`）。seL4 と同じです
- **seL4 のエラーとフォールトのペイロード** — `LookupFault`、seL4 のメッセージ
  レジスタ順のエラーフレーム、受信側のケイパビリティフォールト、`Restart` 状態、
  追加ケイパビリティとして渡されるケイパビリティ引数、そしてケイパビリティ内に
  保持されるガードと単一の `resolveAddressBits`
- seL4 ABI の残りの作業（残りの呼び出し、タイムアウトフォールト、呼び出しごとの
  権限、コアごとの Running 状態）は進行中のワークストリーム WS-SX です。その行は
  [`docs/planning/SEL4_ABI_FIDELITY_PLAN.md`](../../../docs/planning/SEL4_ABI_FIDELITY_PLAN.md)
  にあります

### スケジューリングとリアルタイム

- **ケイパビリティとしてのスケジューリングコンテキスト** — CPU 時間はカーネル
  オブジェクトです。`SchedContext` は seL4-MCS の予算、周期、リフィルを持ち、コア
  の `SchedControl` 権限を通じて設定され、ケイパビリティでスレッドに結び付けら
  れます。その不変条件（`budgetWithinBounds`、`refillsConserved`）は最上位の束に
  含まれます。帯域の隔離は `refill_window_bound` です。コンテキストは一周期のど
  の窓でも予算を超えて実行されません。これは seL4-MCS のスライディングウィンド
  ウ保証です。逆方向（受け入れられたサーバーは毎窓その予算を受け取る）を加える、
  EDF ルートを持つ階層型定帯域スケジューラは、計画中のワークストリーム WS-CB で
  す（[`docs/planning/HIERARCHICAL_CBS_PLAN.md`](../../../docs/planning/HIERARCHICAL_CBS_PLAN.md)）
- **パッシブサーバー** — サーバーは IPC 中にクライアントが提供するスケジューリン
  グコンテキストで動作します。`donationChainAcyclic` が循環的な提供を排除します
- **予算に基づく IPC タイムアウト** — 予算を使い切ったブロック中のスレッドは、
  そのエンドポイントのキューから取り除かれます（`timeoutThread`）
- **優先度継承** — 推移的な伝播と、機械検査されたブロッキング循環の不在
  （`blockingAcyclic`）、そして有界な逆転の定理（`pip_bounded_inversion`）
- **有界な遅延** — 最悪応答時間のパラメトリックな上界
  `wcrtBound D L_max N B P = D × L_max + N × (B + P)`
  （`bounded_scheduling_latency_exists`、コアごとの形もあり）。
  `SeLe4n/Kernel/Scheduler/Liveness/` のモジュール上で証明されています

### カーネルオブジェクトとメモリ

- **untyped メモリから切り出されるオブジェクト** — retype は untyped ケイパビリ
  ティの領域からオブジェクトを切り出し、untyped のリセットは seL4 と同じです。切
  り出した各オブジェクトのセルをその untyped 自身のメモリへ移すことは、進行中の
  ワークストリーム WS-UC です
- **カーネルエントリは何も割り当てない** — コンパイルされたシステムコール、フォ
  ールト、割り込みのエントリはヒープ割り当てを行いません。retype の切り出しが割
  り当てるのは新しいオブジェクト自身のセルだけです。QEMU のヒープゲート
  （`scripts/test_qemu_heap_allocations_per_syscall.sh`）は起動したイメージ上で全
  エントリを計測し、それ以外の値で失敗します
- **データ構造** — オブジェクトストアと VSpace のマッピングは検証済みの Robin
  Hood ハッシュテーブル（`RHTable`。`distCorrect`、`noDupKeys`、
  `probeChainDominant` 付き）です。CNode は seL4 と同じく `2^radix` 個のスロット
  の平坦な配列です。実行キュー、エンドポイントと通知のキュー、応答待ちは TCB を
  通じて連結され、それぞれに、リンクとの一致が証明されたゴーストの抽象キューがあ
  ります
- **スロットで連結されたケイパビリティ導出木** — 各スロットは親、最初の子、兄弟
  へのリンク（seL4 のマッピングデータベース）を持ち、木との一致が証明されていま
  す。削除、取り消し（seL4 の `cteRevoke` ループ）、スロットの転送はリンクをたど
  ります
- **VSpace** — フレームごとに W^X を強制する ARMv8 ページテーブルと、RAM の非キ
  ャッシュエイリアスを拒否するメモリタイプ検査

### セキュリティと検証

- **N ドメインの情報フロー** — seL4 の 2 ドメイン分割を一般化した、パラメータ化
  されたフローポリシー。長さが `enforcementBoundaryExtended_count`（コアごとの境
  界は `enforcementBoundaryPerCore_count`）で固定される強制境界。
  `NonInterferenceStep` の各コンストラクタに対する非干渉定理。そして
  `auditTrail` ケイパビリティを通じて読む、有界でフェイルクローズドな機密解除の
  監査証跡
- **合成された証明層** — `proofLayerInvariantBundle`
  （`SeLe4n/Kernel/Architecture/Invariant.lean`）は、各サブシステムの不変条件の束
  （スケジューラ、ケイパビリティ、IPC とそのスケジューラとの結合、ライフサイク
  ル、サービスレジストリ、VSpace、サブシステム横断、TLB と命令キャッシュの一貫
  性、TLB シュートダウン、機密解除の監査ログ、そして連結構造それぞれとそのゴース
  トの一致）を一つの義務にまとめ、起動からすべての操作を通じて保ちます
- **マルチコア** — コアごとのスケジューリング、コア間 IPC と起床、TLB シュート
  ダウンを備えた 4 コア。SMP 完成のワークストリーム（WS-SM）は進行中です
- **3 段階の状態** — 不変条件の証拠を持つビルダー段階が、検索の同値性が証明され
  た不変の表現へ凍結されます。凍結された操作は `frozenOpCoverage` が列挙するシス
  テムコールをカバーし、`frozenOpCoverage_count` で固定されます
- **サービスレジストリ** — seL4 にはない seLe4n の拡張です。サービスは
  `serviceRegistry` ケイパビリティを通じて登録・検索され、提供するエンドポイント
  に記録されます。依存関係のポリシーは、seL4 と同じくユーザー空間のサービスマネ
  ージャーに任されます

## 現在の状態

<!-- Metrics below are synced from docs/codebase_map.json → readme_sync section.
     Regenerate with: ./scripts/generate_codebase_map.py --pretty
     Source of truth: docs/codebase_map.json (readme_sync) -->

| 項目 | 値 |
|------|-----|
| **バージョン** | `0.37.37` |
| **Lean ツールチェーン** | `v4.28.0` |
| **本番 Lean コード行数** | 687 ファイルにわたる 680,393 行 |
| **テスト Lean コード行数** | 71 テストスイートにわたる 92,469 行 |
| **証明済み宣言数** | 25,997 件の定理/補題宣言（sorry/axiom ゼロ） |
| **Rust クレート** | `sele4n-types`、`sele4n-abi`、`sele4n-sys`（ユーザー空間ラッパー）、`sele4n-hal`（カーネルのハードウェア層）、およびホストテスト `sele4n-lean-boundary` |
| **ターゲットハードウェア** | Raspberry Pi 5 (BCM2712 / ARM Cortex-A76 / ARMv8-A) |
| **起動レーン** | すべての QEMU レーンは、まず [rpi5_machine](https://github.com/hatter6822/rpi5_machine) の `raspi5b` マシンで Raspberry Pi 5 イメージを起動し、次に QEMU の `virt` で `virt` イメージを起動します |
| **ワークストリーム** | 開いている各ワークストリームの状態：[`docs/agent_guide/WORKSTREAM_CONTEXT.md`](../../../docs/agent_guide/WORKSTREAM_CONTEXT.md)。索引と負債台帳：[`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) |
| **監査** | [`docs/audits/`](../../../docs/audits/README.md) — 現在の監査の成果物。以前の監査はアーカイブ済み |
| **コードベースマップ** | [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 機械可読な宣言インベントリ |

メトリクスは `./scripts/generate_codebase_map.py` がコードから導出し、
[`docs/codebase_map.json`](../../../docs/codebase_map.json) の `readme_sync` キーに保存
されます。ドキュメント全体は `./scripts/sync_documentation_metrics.sh`
（検証のみ：`--check`）でまとめて更新してください。

## クイックスタート

```bash
./scripts/setup_lean_env.sh    # install the Lean toolchain and test dependencies
source ~/.elan/env
lake build                     # build the default targets
lake exe sele4n                # run the trace harness
./scripts/test_smoke.sh        # hygiene + build + trace + negative-state
```

`lake build` がビルドするのは `Main.lean` とテスト実行ファイルから到達できるもの
だけです。`.lean` ファイルをコミットする前に、そのモジュールを名前でビルドしてく
ださい（`lake build <Module.Path>`）。作業手順の全体は
[`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md)、すべての貢献者が従う規則は
[`CLAUDE.md`](../../../CLAUDE.md) にあります。

## ドキュメント

| まずここから | 次に |
|--------------|------|
| [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) — 作業手順、検証、PR チェックリスト | [`docs/spec/SELE4N_SPEC.md`](../../../docs/spec/SELE4N_SPEC.md) — 仕様とマイルストーン |
| [`docs/gitbook/README.md`](../../../docs/gitbook/README.md) — ハンドブック全体 | [`docs/spec/SEL4_SPEC.md`](../../../docs/spec/SEL4_SPEC.md) — seL4 の参照意味論 |
| [`docs/codebase_map.json`](../../../docs/codebase_map.json) — 機械可読なインベントリ | [`docs/REGISTERED_DEBT.md`](../../../docs/REGISTERED_DEBT.md) — 担当者付きの、すべての先送り項目 |
| [`CONTRIBUTING.md`](../../../CONTRIBUTING.md) — 貢献の手順 | [`CHANGELOG.md`](../../../CHANGELOG.md) — バージョン履歴 |

## 検証コマンド

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

PR の前には少なくとも `test_smoke.sh` を、定理・不変条件・Tier 3 アンカーを変更
したときは `test_full.sh` を実行してください。各ティアは最初に失敗した検査で止ま
ります。`--continue` を渡すと、すべての失敗を一度に集められます。

`rust/` 以下を変更したら、Rust の **両方の** レーンを実行してください。両者は同
じクレートの互いに素な半分を扱います。ホストでは
`#[cfg(target_arch = "aarch64")]` ブロックがすべて rustc や clippy に見える前に
取り除かれるため、ホストのレーンは HAL の大部分を占める条件付きブロック、`asm!`
箇所、`.S` ソースを見られません。クロスレーンは `sele4n-hal` を
`aarch64-unknown-none-softfloat` 向けに両プロファイルでビルドし、アセンブリソー
スが実際にアセンブルされたことを確かめ、クロスターゲットを lint し、release オ
ブジェクトを逆アセンブルして FP/SIMD レジスタを使っていないことを証明します。
QEMU レーンは初回に `scripts/setup_rpi5_machine.sh` で固定されたコミットの
rpi5_machine をビルドします。前提条件が欠けたレーンは成功ではなく NOT RUN と報告
されます。完全な一覧は [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) にあります。

## アーキテクチャ

seLe4n は層状の契約として構成され、それぞれが実行可能な遷移と、機械検査された
不変条件保存の証明を持ちます。

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

## ソースの構成

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

各サブシステムは **Operations/Invariant 分離** に従います。遷移は
`Operations.lean`、証明は `Invariant.lean` にあります。統一された
`apiInvariantBundle` が、すべてのサブシステムの不変条件を一つの証明義務にまとめ
ます。サブシステムの地図は [`docs/DEVELOPMENT.md`](../../../docs/DEVELOPMENT.md) §5、
ファイル単位の完全なインベントリは
[`docs/codebase_map.json`](../../../docs/codebase_map.json) を参照してください。

## seL4 との比較

| 機能 | seL4 | seLe4n |
|------|------|--------|
| **システムコール ABI** | MCS のシステムコール、呼び出しラベル、エラーとフォールトのペイロード | 同じです。seL4-MCS の 11 個のシステムコールとその番号、ラベルで選ぶ呼び出し、seL4 のエラーペイロード。残りの呼び出しは WS-SX の行です |
| **スケジューリング** | 散発サーバーのリフィルを持つ MCS スケジューリングコンテキスト | 同じリフィル機構。保存の不変条件と、一窓あたり一予算の上界（`refill_window_bound`）が証明済み。EDF ルートを持つ階層型 CBS を計画中（WS-CB） |
| **パッシブサーバー** | SchedContext の提供 | 不変条件 `donationChainAcyclic` を持つ検証済みの提供 |
| **IPC** | エンドポイントごとに 1 本のキュー、TCB を通じて連結 | エンドポイントごとに送信キューと受信キュー。どちらも TCB を通じて連結され、任意の位置から O(1) で除去可能。予算に基づくタイムアウト |
| **情報フロー** | 二値の high/low 分割 | 設定可能な N ドメインポリシー、`enforcementBoundaryExtended_count` で固定される強制境界、ステップごとの非干渉定理、承認された各機密解除に対するケイパビリティ制御の監査証跡 |
| **優先度継承** | カーネルにはない | ブロッキング循環のない、機械検査された推移的 PIP と有界な逆転の定理 |
| **有界な遅延** | 形式的な WCRT 上界はない | `wcrtBound D L_max N B P = D × L_max + N × (B + P)`。活性モジュール上で証明 |
| **オブジェクトストア** | 物理アドレス上のオブジェクト | 検証済みの Robin Hood ハッシュテーブル（`RHTable`/`RHSet`）。CNode は seL4 と同じく平坦なスロット配列 |
| **メモリマッピング** | カーネルは W^X を強制しない | フレームごとの W^X を不変条件として強制。メモリタイプ検査が RAM の非キャッシュエイリアスを拒否 |
| **サービス管理** | カーネル外 | エンドポイント上のケイパビリティ制御のサービスレジストリ。依存関係ポリシーはユーザー空間 |
| **証明** | Isabelle/HOL、C に対する詳細化 | Lean 4、実行可能な遷移と同じ場所。sorry/axiom ゼロ（件数は上の表） |
| **プラットフォーム** | C レベルの HAL | 型付き境界契約を持つ `PlatformBinding` 型クラスと Rust の HAL |

## ライセンスとサードパーティの帰属表示

seLe4n 本体は GNU General Public License v3.0 以降（GPLv3+）の下でライセンスされています。全文は [`LICENSE`](../../../LICENSE) を参照してください。サードパーティのビルド依存関係（`cc`、`find-msvc-tools`、`shlex`。いずれも `MIT OR Apache-2.0` のデュアルライセンス）は MIT の選択肢の下で使用しており、それらの上流の著作権表示および許諾表示は [`THIRD_PARTY_LICENSES.md`](../../../THIRD_PARTY_LICENSES.md) に原文のまま転載しています。カーネルバイナリには実行時にリンクされるサードパーティのコードは一切含まれていません ―― HAL は `#![no_std]` であり、`core::*` のみを使用します。

---

このドキュメントは [English README](../../../README.md) の翻訳です。
