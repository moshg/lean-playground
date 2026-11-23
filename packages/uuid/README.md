# uuid

[RFC 9562](https://www.rfc-editor.org/rfc/rfc9562) 準拠の UUID ライブラリ。外部依存なし（Lean コアのみ）。

- **生成**: v3 / v5（名前ベース）、v4（乱数）、v7（Unix 時刻）、v8（カスタム）
- **単調増加 v7 ジェネレータ**: 同一ミリ秒内や時計の巻き戻りでも厳密に増加（RFC 9562 §6.2）
- **文字列**: 正規形（ハイフン区切り）・32 桁・`{…}`・`urn:uuid:` のフォーマット / パース、エラー位置付き
- **バイト列 / 整数**: `Vector UInt8 16`・`ByteArray`・`BitVec 128`・`Nat` との相互変換
- **コンパイル時リテラル**: `uuid!"…"`（不正な文字列はコンパイルエラー）
- **証明付き**: 主要な性質を `bv_decide` などで証明済み（下表）

## 使い方

```lean
import UUID

def main : IO Unit := do
  IO.println (← UUID.v4)                               -- 9bb72e42-da16-404b-9be2-719ab9ed5485
  IO.println (← UUID.v7)                               -- 01a2065c-0c30-7105-89b8-fcc5c7e81c38
  IO.println (UUID.v5 UUID.namespaceDNS "www.example.com")
                                                       -- 2ed6657d-e927-568b-95e1-2665a8aea6a2

  -- 厳密に単調増加する v7
  let gen ← UUID.V7Generator.new
  let a ← gen.next
  let b ← gen.next
  assert! a < b

  -- パース（hyphenated / simple / braced / URN、大文字小文字どちらも可）
  match UUID.parse "urn:uuid:F81D4FAE-7DEC-11D0-A765-00A0C91E6BF6" with
  | .ok u => IO.println (repr u.version?)              -- some (UUID.Version.gregorian)
  | .error e => IO.eprintln e                          -- e.g. "invalid character 'g' at index 35 of UUID"

-- コンパイル時に検証されるリテラル
def myNamespace : UUID := uuid!"6ba7b810-9dad-11d1-80b4-00c04fd430c8"
```

### 依存として追加する

```toml
[[require]]
name = "uuid"
git = "https://github.com/moshg/lean-playground"
rev = "main"
subDir = "packages/uuid"
```

### CLI

```console
$ lake exe uuidgen                       # v4
$ lake exe uuidgen v7 -n 3               # 単調増加する v7 を 3 つ
$ lake exe uuidgen v5 dns www.example.com --upper
$ lake exe uuidgen inspect 017f22e2-79b0-7cc3-98c4-dc0c0c07398f
uuid:    017f22e2-79b0-7cc3-98c4-dc0c0c07398f
variant: RFC 9562
version: 7 (Unix time)
unix_ts_ms: 1645557742000
```

## API 概要

| モジュール | 内容 |
|---|---|
| `UUID.Basic` | `UUID`（`hi lo : UInt64`, ビッグエンディアン）, `nil`, `max`, `Ord`, `Variant`, `Version`, `version?`, `withVersion`, `v8Of` |
| `UUID.Bytes` | `toBytes` / `ofBytes`, `toByteArray` / `ofByteArray?`, `toBitVec` / `ofBitVec`, `toNat` / `ofNat` |
| `UUID.Format` | `toString`（`ToString` / `Repr`）, `toHexString`, `toUrn`, `toBraced` |
| `UUID.Parse` | `parse : String → Except ParseError UUID`, `parse?`, `parse!` |
| `UUID.Literal` | `uuid!"…"` マクロ |
| `UUID.Random` | `randomBits`, `v4`, `v4Of` |
| `UUID.NameBased` | `namespaceDNS/URL/OID/X500`, `v3`, `v5`, `v3Bytes`, `v5Bytes` |
| `UUID.UnixTime` | `v7`, `v7Of`, `unixTimeMs?`, `V7.succ`, `V7.next`, `V7Generator` |
| `UUID.Hash.*` | 内部用の MD5 / SHA-1（定数時間ではないのでセキュリティ用途には使わないこと） |

`IO` を使う関数（`v4`, `v7`, `V7Generator.next`）には、必ず純粋な中核関数（`v4Of`, `v7Of`, `V7.next`）があり、テストや証明はそちらに対して行えます。

## 証明済みの性質

| 定理 | 内容 |
|---|---|
| `UUID.version?_withVersion` | `(u.withVersion v).version? = some v` |
| `UUID.variant_withVersion` | `withVersion` の結果は RFC 9562 variant |
| `UUID.withVersion_withVersion` | `withVersion` は最後の適用だけが効く |
| `UUID.lt_iff` | 順序は `(hi, lo)` の辞書式順序（= 128bit 符号なし整数の順序） |
| `UUID.ofBytes_toBytes`, `UUID.toBytes_injective` | バイト列変換の往復と単射性 |
| `UUID.ofByteArray?_toByteArray` | `ByteArray` 変換の往復 |
| `UUID.ofBitVec_toBitVec`, `UUID.toBitVec_ofBitVec`, `UUID.ofNat_toNat` | 整数表現との往復 |
| `UUID.version?_v3`, `version?_v4Of`, `version?_v5`, `version?_v7Of` | 各生成関数のバージョン |
| `UUID.unixTimeMs?_v7Of` | v7 から埋め込んだタイムスタンプ（下位 48bit）を取り出せる |
| `UUID.V7.lt_next` | **単調性**: `V7.next` は直前の UUID より厳密に大きい（48bit タイムスタンプが溢れない限り） |
| `UUID.V7.version?_succ` | カウンタのインクリメントは version / variant を保つ |

## テスト

```console
$ lake test
```

- `UUIDTest/Static.lean`: `#guard` によるコンパイル時テスト（RFC 9562 付録のテストベクタ、Python `uuid` / `hashlib` とのクロスチェック、パースエラー、MD5 / SHA-1 のパディング境界など）
- `UUIDTest/Properties.lean`: 乱数入力によるプロパティテスト（文字列・バイト列の往復、文字列順序と UUID 順序の一致、v4 の一意性、v7 の時刻と単調性など）

## 今後の候補

- v1 / v6（グレゴリオ暦タイムスタンプ）の生成
- `parse? (toString u) = some u` の証明（現在はプロパティテストで確認）
- `Lean.Json` の `ToJson` / `FromJson` インスタンス（`Lean` への依存を避けるため別モジュールで）
