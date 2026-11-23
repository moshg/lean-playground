# array-deque 設計（#4）

両端キュー `ArrayDeque` の実装前の設計。パッケージ `packages/collections`、モジュール `Collections.ArrayDeque`
（名前空間 `Collections`）。
当初は単独のパッケージ `packages/array-deque` だったが、データ構造は `collections` にまとめる方針に変えた。

## 1. 表現

```lean
universe u

-- `namespace ArrayDeque` の外で宣言する（中だと `ArrayDeque.ArrayDeque` になる）
structure ArrayDeque (α : Type u) where
  /-- リングバッファ。長さが容量で、0 か 2 の冪。 -/
  buf : Array α
  /-- 先頭要素の物理添字。 -/
  head : Nat
  /-- 要素数。 -/
  size : Nat
  size_le : size ≤ buf.size
  cap_pow2 : buf.size = 0 ∨ buf.size.isPowerOfTwo
  head_lt : head < buf.size ∨ buf.size = 0
```

- 容量 `capacity d := d.buf.size` は 0 か 2 の冪。容量 0 を許すので、`∅` は `#[]` を持つだけで済み、
  `Inhabited α` を要求しない（`EmptyCollection` / `Inhabited (ArrayDeque α)` は無条件）。
- 論理添字 `i` の物理添字は `physIdx head i cap := (head + i) &&& (cap - 1)`。生の `Nat` を取る関数にして、
  構造体を分解した後でも使えるようにする。
  - 範囲の証明は `Nat.and_le_right` と `0 < cap` だけで足り、2 の冪である必要はない。
  - 意味論の証明では `Nat.and_two_pow_sub_one_eq_mod` で `(head + i) % cap` に書き換える。
    さらに `head < cap` かつ `i < cap` なら `if head + i < cap then head + i else head + i - cap` に落ち、
    あとは `omega` で処理できる。`head_lt` を不変条件に入れるのはこのため。
  - `bv_decide` は不要の見込み（ビット演算は上の補題 1 本で剰余に変わる）。
- **`module` 内では `Nat.isPowerOfTwo` / `Nat.nextPowerOfTwo` の本体が見えない**（4.36 で確認済み）。
  - `⟨2, rfl⟩`、`unfold`、`simp only [Nat.isPowerOfTwo]`、`rcases h with ⟨k, hk⟩` がどれも失敗する。
  - `∃ k, n = 2 ^ k` に開く公開補題もない。
  - `Basic.lean` の証明は、公開されている補題だけで書ける：`Nat.isPowerOfTwo_nextPowerOfTwo`、
    `Nat.le_nextPowerOfTwo`、`Nat.isPowerOfTwo_one`、`Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo`。
  - 2 の冪を `∃ k` に開く必要がある `Lemmas.lean`（`physIdx_eq_mod` など）にだけ、非公開の
    `import all Init.Data.Nat.Power2.Basic` を置く。
    - 試作では、`lake build --wfail` が通り、下流のパッケージ（module 版と非 module 版の両方）もビルド・実行できた。
    - 下流から `isPowerOfTwo` の本体は見えないまま（漏れない）。
    - コアの `Power2/Lemmas.lean` も同じ import をしている。
  - これは `Lean` パッケージではなく `Init` の import なので、バイナリサイズの規約には触れない。
  - 同じ理由で `decide` / `rfl` では容量を計算できない。`#guard`（評価する）なら使える。
- 不変条件は構造体のフィールドにする（後付けの述語 `WF d` にはしない）。
  - 「全操作で不変条件が保たれる」は型で保証され、各操作の定義でその証明を書くことになる。
  - 添字アクセスに境界検査が要らない（`buf[physIdx ..]'h`）。
  - 証明フィールドは実行時には消える。
- `toList` は抽象モデルであって等価性ではない。同じ `toList` を持つ 2 つの deque が `=` になるとは限らない
  （バッファや `head` が違いうる）。`DecidableEq` / `BEq` は提供しない。

## 2. 空きスロット：`[Inhabited α]` を採用

issue で指定された選択肢の比較。

| 案 | 制約 | コスト | 取り出した要素の参照 |
|---|---|---|---|
| **A. `Array α` + `default` で埋める（採用）** | 変更系の操作に `[Inhabited α]` | 追加なし | 取り出したスロットを `default` で上書きして解放 |
| B. `Array (Option α)` | なし | 要素ごとに `some` の割り当て 1 回と間接参照 1 段 | `none` で上書きして解放 |
| C. 埋めずに放置（既存要素のコピーで埋める） | なし | 追加なし | 取り出し済み要素への参照が最大で容量個まで残る |

- C はメモリリークになるので不採用。Java の `ArrayDeque` が取り出したスロットに `null` を書くのと同じ理由。
- A と B の実測（完成した実装の A と、同じアルゴリズムで書いた B。要素は `Nat`、`-O3`、3 回の中央値）：

  | 操作 | A | B |
  |---|---|---|
  | 1000 要素の窓で `pushBack` + `popFront?` を 2000 万回 | 367 ms | 359 ms |
  | 空から `pushBack` で 1000 万要素（拡張を含む） | 447 ms | 499 ms |
  | 1000 万要素の `foldl` | 34 ms | 54 ms |
  | 1000 万要素を `popFront?` で空にする | 150 ms | 100–152 ms |

  - **速度の差は小さく、向きは操作による。**
    - B は push のたびに `some` を 1 つ割り当てるが、pop ではスロットの `some x` をそのまま返せる。
    - A は逆に、pop のたびに戻り値の `some x` を割り当てる。
    - 読み取りと走査は、間接参照が 1 段少ない A の方が約 1.5 倍速い。
  - **メモリは A が有利。** B は格納している要素ごとに `some` セル（16 バイト）を持つ。A は持たない。
  - 設計の初版にあった「B は約 1.6 倍遅い」は誤り。試作の B が pop のたびに `some` を作り直していた
    （割り当てが 1 回多かった）ための数字だった。
  - A を選ぶ理由は、主に要素ごとのメモリと、読み取り・走査の速さ。代わりに `Inhabited` の制約がかかる。
- A の制約は、スロットを新しく作る・空ける操作だけにかける。対象は push/pop 系、`grow`、`ofList`、
  `emptyWithCapacity` で、§4 の表の [Inh] がその一覧。
  - 既存の要素を書き換えるだけの `set`/`setIfInBounds`、読むだけの操作（`get`/`toList`/`foldl`/`ForIn` など）、
    `∅` は無条件。
  - push に `Inhabited` が要る理由：拡張時に新しいバッファを埋める値が要る。押し込む要素 `x` で埋めると、
    `x` を取り出した後もコピーが残るのでリークになる。
- `Inhabited` を持たない型（証明付き部分型、`Fin n` など）で使えないのが A の欠点。この比較を PR 本文にも書く。

## 3. 破壊的更新（参照カウント 1 のときの in-place 更新）

試作で踏んだ落とし穴：`buf.set` の後に `buf.size` を評価すると、`set` の時点で `buf` がまだ生きているので
共有扱いになる。すると毎回配列がコピーされ、上のベンチで **11.7 秒（約 40 倍遅い）** になった。
実装では次の形を守る。

1. `buf.set` を呼ぶ関数では、最初に `match d with | ⟨buf, head, size, ..⟩ => ...` で構造体を分解する。
   - 避けるべきなのは、`set` の時点で `buf`（または `d`）がまだ生きている状態。
   - `set` より前に `d` からスカラー（`d.size` など）を読み、そのあと `d` を丸ごと次の関数に渡すのは構わない。
     例：`if h : d.size < d.capacity then core d x h else core (grow d) x _` は in-place になることを確認済み。
2. `buf.size`、読み出す要素、物理添字など、`buf` から読む値は **すべて `set` の前に `let` で束縛する**。
3. 新しい構造体を作るのに必要な証明は `Array.size_set` で `buf'.size = buf.size` に帰着させる。

```lean
def popFront? [Inhabited α] (d : ArrayDeque α) : Option α × ArrayDeque α :=
  match d with
  | ⟨buf, head, size, h₁, h₂, h₃⟩ =>
    if hs : size = 0 then (none, ⟨buf, head, size, h₁, h₂, h₃⟩)
    else
      let cap := buf.size                      -- set より前に読む
      let x := buf[head]'(by omega)
      let buf' := buf.set head default (by omega)
      (some x, ⟨buf', (head + 1) &&& (cap - 1), size - 1, by .., by .., by ..⟩)
```

`buf[head]` を読んでから `set` する代わりに、`Array.swapAt` で取り出しと上書きを一度に行えば、参照カウントの
inc/dec を 1 組省ける（任意の最適化）。

### `popFront?` / `popBack?` の戻り値の型：`Option α × ArrayDeque α`

issue の想定（`Std.Queue.dequeue?` と同じ `Option (α × ArrayDeque α)`）からは変えて、空のときも含めて
deque を常に返す。

`Option (α × ArrayDeque α)` だと、空のときに deque が返らない。そのため呼び出し側は `none` の分岐で
元の `d` を使い続けることになり、次のいちばん自然な書き方で毎回の pop がバッファ全体のコピーになる。

```lean
let mut d := ...
match d.popFront? with          -- Option (α × ArrayDeque α) だった場合
| some (x, d') => d := d'; ...
| none => pure ()               -- 古い d が呼び出しをまたいで生き残る → popFront? 内の set がコピー
```

- 試作での実測（容量 2^20 で 1000 回 pop）：この書き方は 1225 ms、`| none => d := ∅` と再代入すれば 2 ms。
- `Option α × ArrayDeque α` なら、`let (x?, d') := d.popFront?; d := d'` で古い `d` は必ず死ぬ。
  この落とし穴が構造的に起きない。
- 前例：配列ベースの `Std.HashMap.getThenInsertIfNew? : … → Option β × HashMap α β` も、コンテナを常に返す形。
  `?` 付きの名前とも矛盾しない。
- 仕様の定理も、2 本の単純な等式に分かれる（第 5 節）。

### 検出（テスト）

所要時間で検出するのはやめる。2^20 の容量でコピーが起きても 1 回 1.2 ms 程度で、10^6 回でも約 20 分で
終わってしまう。CI の既定のタイムアウト（360 分）では落ちない。

- 代わりに、テストコードだけで `ptrAddrUnsafe d.buf` を比べる。
  - `unsafe def` を用意し、それを `@[implemented_by]` 経由で安全な名前に包む。
  - 各操作の前後で、`buf` のアドレスが変わらないことを確かめる。対象は `pushBack`/`pushFront`（拡張しない場合）、
    `popFront?`/`popBack?`/`popFront`/`popBack`/`set`/`setIfInBounds`。
- テストに使う deque は、**検査ごとに別々の**実行時の値から作る（例：`mk (n+1)`、`mk (n+2)`、…）。
  そうしないと、正しい実装でも毎回コピーしているように見えてしまう（試作で確認済み）。原因は 2 つある。
  - リテラルだけで作った deque は、closed-term extraction でグローバル定数に持ち上げられ、恒久的に共有される。
  - 同じ純粋な呼び出し `mk n` を何度も書くと、共通部分式の除去で 1 つの値にまとめられて共有される。
- 逆の誤判定（コピーしているのに「in-place」と出る）は起きない。コピーするには古いバッファと新しいバッファが
  同時に生きている必要があり、そのときアドレスは必ず変わるため。
- 開発中は、上と併せて `dbgTraceIfShared` を一時的に挟んで確認する。

## 4. API

`namespace ArrayDeque`。`[Inh]` は `[Inhabited α]` を要求するもの。

| 名前 | 型 | 備考 |
|---|---|---|
| `∅` / `empty` | `ArrayDeque α` | 容量 0 |
| `emptyWithCapacity` [Inh] | `Nat → ArrayDeque α` | 容量は `capFor n`（下記） |
| `size` | `ArrayDeque α → Nat` | フィールド |
| `capacity` | `ArrayDeque α → Nat` | `buf.size` |
| `isEmpty` | `ArrayDeque α → Bool` | `size == 0` |
| `get` | `(d : _) → (i : Nat) → i < d.size → α` | `d[i]` の実体 |
| `GetElem` / `GetElem?` / `LawfulGetElem` | `d[i]`, `d[i]?`, `d[i]!` | dom は `i < d.size` |
| `front?` / `back?` | `ArrayDeque α → Option α` | |
| `set` | `(d : _) → (i : Nat) → α → i < d.size → ArrayDeque α` | 証明は `by get_elem_tactic` を既定値にする |
| `setIfInBounds` | `ArrayDeque α → Nat → α → ArrayDeque α` | 範囲外なら何もしない |
| `pushBack` / `pushFront` [Inh] | `ArrayDeque α → α → ArrayDeque α` | 満杯なら先に `grow` |
| `popFront?` / `popBack?` [Inh] | `ArrayDeque α → Option α × ArrayDeque α` | 空なら `(none, d)` |
| `popFront` / `popBack` [Inh] | `ArrayDeque α → ArrayDeque α` | `(popFront? d).2`。空なら何もしない |
| `toArray` / `toList` | | `toArray := Array.ofFn (n := d.size) fun i => d.get i i.2`、`toList := toArray.toList` |
| `ofList` [Inh] | `List α → ArrayDeque α` | `l.toArray ++ replicate (capFor n - n) default`、`head = 0`。O(n) |
| `foldl` | `(β → α → β) → β → ArrayDeque α → β` | 引数順は `Array.foldl` に合わせる |
| `ForIn m (ArrayDeque α) α` | | 添字のループで書く。`toArray` を経由しない |
| `Repr` | | `Collections.ArrayDeque.ofList [..]` と表示する |
| `grow` [Inh] | `ArrayDeque α → ArrayDeque α` | 内部用だが公開（exposed な定義から参照するため）。docstring を付ける |

issue から変えた点：

- `withCapacity` → **`emptyWithCapacity`**：`Array.emptyWithCapacity` と揃える。
  - ただし `Array` 版と違い、スロットを `default` で埋めるので `[Inhabited α]` が要る。
- `get?` → **`d[i]?`**（`GetElem?` インスタンス）：コアは `Array.get?` を非推奨にして `xs[i]?` に移行済み。
  名前付きの関数 `get?` は作らない。
- 容量の不変条件は issue の「2 の冪」ではなく「0 または 2 の冪」にする。`∅` を割り当てなし・制約なしにするため。
- `popFront?` / `popBack?` の戻り値は `Option α × ArrayDeque α`（第 3 節）。

### 主な操作の中身

- **`pushBack`**：満杯（`size = cap`）なら `grow`。`buf.set (physIdx head size cap) x`、`size + 1`。
- **`pushFront`**：満杯なら `grow`。`head' := (head + cap - 1) &&& (cap - 1)`（`Nat` の引き算で 0 を
  下回らないように `+ cap` する）。`buf.set head' x`、`size + 1`。
- **`popBack?`**：`i := physIdx head (size - 1) cap` を読み、`default` を書き込む。`head` はそのまま。
- **`popFront` / `popBack`**：`(d.popFront?).2`。`d` を丸ごと渡すので in-place のまま。
  - 一意性テストの対象に含めて、in-place であることを確かめる。
  - 戻り値が `Option (α × _)` だった頃の試作では、`match … | none => d` と書くと毎回コピーになった
    （1283 ms 対 29 ms）。
- **`capFor n := if n = 0 then 0 else n.nextPowerOfTwo`**：`emptyWithCapacity` と `ofList` で共用する。
  - こうすれば `ofList []` も容量 0 になり、割り当てが起きない。
  - 内部用だが公開し、docstring を付ける。
- **`grow`**：新しい容量は `if cap = 0 then 4 else 2 * cap`。
  - 新しいバッファは `Array.ofFn (n := newCap) fun i => if h : i < size then get d i h else default`、
    `head := 0`。
  - 証明は `Array.getElem_ofFn` で済む。毎回新しい配列を確保するので、Rust のような部分的なコピーの最適化はしない
    （償却 O(1) は保たれる）。
  - 事後条件 `size < (grow d).capacity` を補題にして、push の高速路に渡す。
- **`foldl` / `forIn`**：`i` を `0` から `size` まで回すループで書き、`termination_by size - i` か
  `Nat.fold` 系を使う。`toList` を作らない。

## 5. 証明

`Collections/ArrayDeque/Lemmas.lean`。`sorry` と独自の公理は置かない。

基礎となる補題：

- `physIdx_lt`
- `physIdx_eq`（第 1 節の if 形）
- 単射性 `physIdx_inj`：`i, j < cap` で物理添字が等しいなら `i = j`
- `getElem_toList : d.toList[i] = d[i]`（simp 補題にはしない）

simp の正規形はモデル側に寄せる。そうすると、各操作の `toList_*` 補題がそのまま効く。

- `d[i]` は `d.toList[i]` に書き換える（`getElem_eq_getElem_toList`）。
- `d[i]?` と `d[i]!` も、それぞれ `d.toList[i]?` と `d.toList[i]!` に書き換える。
- `d.toArray` は `d.toList.toArray` に書き換える。
- `d.toList = []` は `d.size = 0` に書き換える。

仕様の定理（`@[simp]` を付けられるものは付ける）：

```lean
theorem toList_empty : (∅ : ArrayDeque α).toList = []
theorem toList_emptyWithCapacity [Inhabited α] : (emptyWithCapacity n : ArrayDeque α).toList = []
theorem toList_pushBack  [Inhabited α] : (d.pushBack x).toList = d.toList ++ [x]
theorem toList_pushFront [Inhabited α] : (d.pushFront x).toList = x :: d.toList
theorem popFront?_fst [Inhabited α] : d.popFront?.1 = d.toList.head?
theorem toList_popFront?_snd [Inhabited α] : d.popFront?.2.toList = d.toList.tail
theorem popBack?_fst [Inhabited α] : d.popBack?.1 = d.toList.getLast?
theorem toList_popBack?_snd [Inhabited α] : d.popBack?.2.toList = d.toList.dropLast
theorem toList_popFront [Inhabited α] : d.popFront.toList = d.toList.tail
theorem toList_popBack  [Inhabited α] : d.popBack.toList = d.toList.dropLast
theorem getElem?_eq : d[i]? = d.toList[i]?
theorem toList_set : (d.set i x h).toList = d.toList.set i x
theorem toList_setIfInBounds : (d.setIfInBounds i x).toList = d.toList.set i x
theorem front?_eq : d.front? = d.toList.head?
theorem back?_eq  : d.back? = d.toList.getLast?
theorem length_toList : d.toList.length = d.size
theorem isEmpty_eq : d.isEmpty = d.toList.isEmpty
theorem toList_toArray : d.toArray.toList = d.toList
theorem toList_ofList [Inhabited α] : (ofList l).toList = l
theorem foldl_eq : d.foldl f init = d.toList.foldl f init
theorem forIn_eq [Monad m] [LawfulMonad m] : forIn d b f = forIn d.toList b f
-- 不変条件（フィールドから直接言える）
theorem size_le_capacity : d.size ≤ d.capacity
theorem capacity_eq_zero_or_isPowerOfTwo : d.capacity = 0 ∨ d.capacity.isPowerOfTwo
```

`List.set` は範囲外なら何もしないので、`toList_setIfInBounds` に範囲の仮定は要らない。

push/pop/set の証明は、どれも次の流れになる見込み。

1. `List.ext_getElem` でリストの等式を要素ごとの等式にする。
2. `Array.getElem_set`（または `getElem_ofFn`）で `if` に開く。
3. `physIdx_eq` と `physIdx_inj` を使い、残りを `omega` で片付ける。

`pushFront`/`popFront?` では新しい `head` 自体がマスク済みの値なので、次の 2 つの補題も用意する。

- `physIdx_eq_mod : physIdx h i c = (h + i) % c`
- `physIdx_physIdx : physIdx (physIdx h a c) b c = physIdx h (a + b) c`

`head` の式を `rw` で書き換えようとすると、`head_lt` の証明フィールドがそれに依存しているため
"motive is not type correct" で失敗する。`simp only [...]` を使う。

試作（module 化した `lake build --wfail`、`sorry` なし）で通ることを確認済みのもの：

- 補題：`physIdx_lt`、`physIdx_eq`、`physIdx_inj`、`physIdx_eq_mod`、`physIdx_physIdx`
- 仕様：上の一覧にある定理すべて（`grow` を経由する push も含む）
- 公理：`#print axioms` で出るのは `propext`/`Classical.choice`/`Quot.sound` だけ
- `foldl_eq`/`forIn_eq`：`termination_by d.size - i` のループと `fun_induction` で証明
- `LawfulGetElem`：`getElem?` を `if h : i < d.size` で定義すれば、既定の証明で通る

実装時の注意：4.36 では `if_pos`/`if_neg`/`dif_pos`/`dif_neg` が非推奨になっている。代わりに
`ite_eq_left` などを使う。非推奨の警告も `--wfail` で落ちる。

## 6. テスト

- **`CollectionsTest/ArrayDeque/Basic.lean`（`#guard`）**：
  - 空：`toList`、`popFront?.1`/`popBack?.1` が `none`、`capacity = 0`。
  - `emptyWithCapacity 0/1/5` の容量がそれぞれ 0/1/8。
  - 折り返し：`emptyWithCapacity 4` に 1,2,3 を `pushBack` し、2 回 `popFront` し、4,5,6 を `pushBack`
    すると `toList = [3,4,5,6]`、`capacity = 4`、`head = 2`。
  - 拡張の境界：上の状態（満杯で折り返している）にもう 1 つ `pushBack` すると `capacity = 8`、
    `toList = [3,4,5,6,7]`。
  - `pushFront` の折り返し（`head = 0` から `cap - 1` へ）、空（容量 0）への `pushFront`。
  - 折り返しをまたぐ `d[i]?`、`setIfInBounds`、`popBack?`。
    - 具体的な deque に対する `set` では、`get_elem_tactic` や `decide` が `i < d.size` を示せないことがある。
      - 例えば `emptyWithCapacity` を経由すると、`capFor` が簡約できず止まる。
      - `#guard` では `setIfInBounds` を使う。
    - `set` そのものを試すときは、`(by rw [← length_toList]; simp [...])` のように証明を明示する。
  - `foldl`、`for x in d do` の結果が `toList` と一致する。
  - 公理の検査：主要な定理について `#guard_msgs in #print axioms ArrayDeque.toList_pushBack` などを置き、
    標準の公理（`propext`/`Classical.choice`/`Quot.sound` の部分集合）しか使っていないことを固定する。
    - 期待される出力は定理ごとに違い、証明を変えると変わりうる。その場合は出力を更新する。
- **`CollectionsTest/ArrayDeque/Property.lean`（実行時）**：
  - 純粋な中核 `checkRandom (seed n : Nat) : Except String Unit` を作る。`mkStdGen seed` と `randNat` で
    操作列（pushBack/pushFront/popFront?/popBack?/set/popFront/popBack）を生成し、`ArrayDeque Nat` と
    `List Nat` のモデルに同じ操作を適用する。
  - 各ステップで `toList`、`size`、`front?`、`back?`、ランダムな `i` での `d[i]?`、`capacity` が 0 か 2 の冪か、
    を比較する。
  - 成長と縮小の両方を通すため、push 優勢と pop 優勢のフェーズを交互にする。
  - `IO` 側は固定のシード列（再現用）を回すだけ。
  - モデルとの比較ループでも、pop は第 3 節の安全な書き方で書く。
- **`CollectionsTest/ArrayDeque/InPlace.lean`（実行時）**：第 3 節の一意性テスト（`ptrAddrUnsafe` で比べるもの）。

## 7. ファイル構成

```
packages/collections/
  Collections.lean                     public import Collections.ArrayDeque
  Collections/ArrayDeque.lean          public import Collections.ArrayDeque.Basic, .Lemmas
  Collections/ArrayDeque/Basic.lean    構造体・physIdx とその範囲の補題・操作・インスタンス
  Collections/ArrayDeque/Lemmas.lean   仕様の定理
  CollectionsTest.lean                 テストドライバ
  CollectionsTest/ArrayDeque/Basic.lean     #guard
  CollectionsTest/ArrayDeque/Axioms.lean    #guard_msgs in #print axioms
  CollectionsTest/ArrayDeque/Property.lean  List モデルとのランダム比較（実行時）
  CollectionsTest/ArrayDeque/InPlace.lean   ptrAddrUnsafe による in-place 検査（実行時）
```

## 8. スコープ外

`map`/`Functor`、`foldr`、`append`、`shrinkToFit`、`clear`、`ofArray`、範囲指定の反復。
必要になったら別 issue にする。

## 完了条件（issue より）

- `scripts/check.sh array-deque` が警告なしで通る
- README のパッケージ一覧に追加する
- PR 本文に第 2 節のトレードオフ（ベンチ結果つき）を書く
  - ベンチはリポジトリにはコミットしない。PR 本文にコードを載せる。
  - 数値は試作のものを流用せず、完成した実装で測り直す。比較するのは A/B 表現と、第 3 節の安全な書き方と悪い書き方。
