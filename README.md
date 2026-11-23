# lean-playground

Lean 4 でライブラリを実装して遊ぶためのモノレポ。各ライブラリは `packages/` 以下の独立した
Lake パッケージで、単体で依存として取り込めます。

## パッケージ

| パッケージ | 概要 |
|---|---|
| [`uuid`](packages/uuid) | RFC 9562 UUID（v3/v4/v5/v7/v8、単調増加 v7、パース / フォーマット、コンパイル時リテラル、証明付き） |

## 必要なもの

- [elan](https://github.com/leanprover/elan)（Lean のツールチェーンマネージャ）

ツールチェーンはリポジトリ直下の [`lean-toolchain`](lean-toolchain) で全パッケージ共通に固定しています
（各パッケージの `lean-toolchain` はそこへのシンボリックリンク）。elan が初回に自動でインストールします。

## 開発

```console
$ cd packages/uuid
$ lake build          # ビルド
$ lake test           # テスト
$ lake exe uuidgen    # パッケージが提供する実行ファイル

$ scripts/check.sh            # 全パッケージを --wfail（警告もエラー扱い）でビルドしてテスト
$ scripts/check.sh uuid       # 指定したパッケージだけ
```

エディタは VS Code + [Lean 4 拡張](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)を推奨。
リポジトリ直下を開けば、各ファイルは最寄りの `lakefile.toml` のパッケージとして扱われます。

### 新しいパッケージを追加する

```console
$ scripts/new-package.sh base64 Base64
```

`packages/base64/` に lakefile・ライブラリ・テスト・README の雛形ができます。CI は `packages/*/lakefile.*`
を自動検出するので、設定の追加は不要です。上のパッケージ表への追記だけ忘れずに。

## レイアウト

```
lean-toolchain            全パッケージ共通の Lean バージョン
packages/<name>/
  lakefile.toml           パッケージ定義（ライブラリ・テストドライバ・実行ファイル）
  lean-toolchain          -> ../../lean-toolchain
  <Lib>.lean, <Lib>/      ライブラリ本体
  <Lib>Test.lean          テストドライバ（`lake test` で実行）
  <Lib>Test/              テスト（`#guard` によるコンパイル時テスト + 実行時テスト）
scripts/                  check.sh, new-package.sh
.github/workflows/ci.yml  パッケージごとの matrix ビルド
```

## 規約

- **モジュールシステム**: ライブラリのファイルは `module` で始め、公開 API は `public import` /
  `@[expose] public section` で明示する
- **`autoImplicit = false`**: 暗黙の自動束縛は使わない
- **`linter.missingDocs`**: ライブラリの公開宣言にはすべて docstring を付ける
- **純粋な中核 + 薄い `IO` ラッパー**: 乱数や時刻を使う関数は、それらを引数に取る純粋関数を別に用意し、
  テストと証明はそちらに対して書く
- **ライブラリから `Lean`（コンパイラ本体）を import しない**: 実行ファイルに Lean 全体がリンクされて
  サイズが 20 倍近くになる。メタプログラミングは `Init` だけで書ける `macro` を優先する
- 1 行 100 文字まで

## 依存として使う

各パッケージは Lake の `subDir` 指定で個別に取り込めます。

```toml
[[require]]
name = "uuid"
git = "https://github.com/moshg/lean-playground"
rev = "main"
subDir = "packages/uuid"
```
