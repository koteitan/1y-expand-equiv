# 1y-expand-equiv

1-Y 数列の展開規則について、次の 2 つが同じ関数であることの Lean 4 による証明。

| | 何か | 場所 |
|---|---|---|
| Yukito 版 | Yukito 氏による 1-Y の展開規則 | [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の `script.js` の `expand` |
| Phyrion 版 | Phyrion 氏が独自に定めた祖先保存アルゴリズム | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の `OneY.Numeric.expandValues` |

Phyrion 版は 1-Y の展開の整礎性と標準生成集合の辞書式整列を Lean 4 で証明している。

ただし **Phyrion 版は Yukito 版の形式化であるとは主張していない**。論文はこう書いている。

> The precise convention considered here is the ancestor-preserving algorithm below and in
> the fixed source snapshot. No equivalence with every variant described elsewhere is assumed.

つまり対象は論文とソーススナップショットで定義された規則そのものであり、他所で記述された
変種との同値性は仮定されていない。そこが本リポジトリの問いだった。

## 答え：同じ関数である

```
theorem expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N
```

`ZeroY.Legal s` は「すべての要素が正」かつ「先頭が 1」で、Phyrion 版が `expandValues` に
課している条件そのものである。標準形の Y 数列はこれを満たす。`m` と `efuel` は燃料で、
`sequenceBound s`（値の最大）と列の長さ以上あれば足りる。

`sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

したがって Phyrion 版の整礎性・整列性の結果は、そのまま Yukito 版の 1-Y についての
結果になる。

## 座標の対応

Yukito 版は疎配列、Phyrion 版は列ごとの値の関数である。対応は次のとおり。

```
Yukito 版 (行 r, position P)  ↔  Phyrion 版 (行 r, 列 c = P + r)
```

この変換のもとで、`script.js` の「右腿で下へ、親を取り、左腿で上へ」という歩行は、
前の行の親チェーンをそのまま辿ることになる。

## 証明の骨格

`expand` は 4 つの部品でできている。それぞれについて両版が一致することを示し、
最後に層の再帰で束ねる。

```
calcMountain   差分山脈を作る
calcDiagonal   列の頂をたどって次の層の行を作る（抽出段）
getBadRoot     bad root を探す
Mt.Fuji シェル 山をコピーして継ぎ足し、値を埋める
```

### 山（差分山脈）の段

行 `r+1` の親は「行 `r` の祖先鎖のうち、値が正で自分より小さい最も右のもの」である。
JS はこれを疎配列の走査で計算する。両者が一致することを示すには、一般の行について

```
(a) 鎖の根 root は、根より右で最初に生きている列 j の祖先である
(1) U p ≤ U j     （p は鎖で root の 1 つ手前）
```

の 2 つが要る。`j` が `p` の祖先である場合とそうでない場合に分かれ、後者では `j` と
`p` は共通の親 `root` を持つ兄弟になる。

**兄弟であるだけでは (1) は出ない。一般の行で兄弟の単調性は偽である。** 反例は列
`(1,1,2,5,7,5)` の行 1（`Equiv/Sibling.lean` に記載）。効いているのは `j` が
「`root` より右で最初に生きている列」であることで、この条件を落とした一般化はすべて偽になる。

代わりに成り立つのは次の 2 つで、こちらは全層で真である。

```
leftmost_child_all  root が子を持つなら root+1 も子である
sibSucc_all         root+1 と e が root の子で root+1 < e なら U e ≤ U (root+1)
```

`sibSucc_all` は、層を 1 つ降りる前に `e` を `root` の子まで引き上げるのが要点である。
引き上げずに降りると主張の形が変わってしまい閉じない。

### 抽出段

JS の `calcDiagonal` は列の頂から脚をたどり、**その行で親を持たない節点**で止まる。
Lean の `Pseudo.parent` は代わりに高さの条件 `H p ∈ {H c − 1, H c}` を課す。この 2 つは
同値である。JS が訪れる節点 `(h, p)` は必ず行 `h` で生きているので

```
その行で親を持たない  ⟺  H p ≤ h  ⟺  H p = h
```

となり、歩行は高さ `H c` から始まって脚 1 つで高さが変わらないか 1 下がるだけなので、
止まった高さは `H c` か `H c − 1` に限られる。

抽出後の行の下にある frame は擬親森ではなく `topForest` を取る。擬親森は
「高さが同じか 1 小さい祖先のうち最も右」で `topForest` を細かくする方向に働くため、
そのままでは塔の義務（最左の子・兄弟の単調性）が引き継げない。

### bad root

JS の `getBadRoot` は対角の最後の値が 1 になるまで抽出を繰り返し、その層で
「頂の 1 つ下の段での親」を返す。これが Phyrion の `findBadRoot` の列に一致する
(`getBadRoot_eq_findBadRoot`)。分岐条件（行 0 の最後のセルに親が無い ⟺ `findBadRoot` が
`none`）も一致する。

### 値の層

Phyrion 側の復元は閉じた式である。

```
Reconstruction.value M top r c
  = if r ≤ height c then top c + Σ_{u=r}^{height c − 1}（行 u での c の親の値）else 0
```

JS 側は最後に `result[i][j].value = 親の値 + 1 つ上の段の同じ列の値` で `NaN` を埋める。
これは差分の関係 `V_r(c) = V_r(親) + V_{r+1}(c)` で、上の閉じた式を展開したものにあたる。

そこで「疎な山が森 `G` と頂の値 `top` を表している」ことを `ShapeRep` として切り出し、
森の具体形に踏み込まずに値の層を閉じた。

```
ShapeRep Rs G top W  →  expandOut (fillValues Rs) = (range W).map (value G top 0)
```

`ShapeRep` の `step`（差分の関係）は、値 0 のセルでは埋めから、値が入っているセル
（コピー元のまま残る列）では元の山の差分の関係から出る。「親を持つセルの値は 0」は
**偽**である。JS の `fillRow` は値が 0 でないセルを触らないので、元の列は古い値を保つ。

### 森のコピー

Phyrion 側の `expandedMountain a hbad k` は層ごとに 3 通りに分かれる。

```
k < K   badAtLowerContext      下位のコピー
k = K   badAtTerminalMountain  終端のコピー
k > K   OrdinaryCopy           通常のコピー
```

JS の Mt.Fuji シェルは 1 つの三重ループでこの 3 通りをまとめて作る。層ごとにどの枝に
あたるかを読み合わせた。

**`k = K`（山崎噴火の枝）** では落差が 0 で、`fujiSource` の 4 枝が 1 つに潰れる。
新しい対角は `yamaVal` による周期的なコピーで、これが `K+1` 段目以上の `assemble` に
一致する。

**`k < K`** では落差 `rise = height x − height y` が正で、4 枝がすべて効く。原文の 3 つの
枝は 1 つにまとめられる。上りの列では `r < floor + b*rise` なら段 `floor`、そうでなければ
`r − b*rise` を使うが、これは `floor` で下から押さえた

```
max floor (r − b*rise)
```

に等しい。JS の `fujiSrcRow` もこれに一致する。

この枝では **落差は幅を超えない**ことが要る。段 `r ∈ [floor, height x]` について
`rootAt r x` は真に増え、`rootAt floor x = y`、`rootAt (height x) x = x` なので

```
rise = height x − floor ≤ x − y
```

である。これで積む段の数の一様な上界が取れ、三重ループの不変量が使える。

### 上りでない列

`script.js` の Mt.Fuji シェルは `isAscending` で 2 つのループに分かれる。偽のほうは
段が `seamHeight` までで、枝も Bb（`sy = k`）1 本しかない。原文の `¬InCone` の枝も
段 `r` そのものを使うので、そのまま対応する。親のセルが積まれていることは

```
parent_endpoint        r ≤ M.height p
height_parentCopy_ge   M.height p ≤ height (parentCopy b p)
```

から出る。この枝に幾何的な追加の義務は無い。

上りでない列が `badRootHeight` より高くなるのは値が大きいときだけである。`#guard` に
固定してある例は値 15 と 17 で、値 8 までの例では 2 つのループの違いは表に出ない。

### 層の再帰

JS は `newDiagonal = expand(diagonal, n, false)` で層をまたいで再帰する。これが
`assemble` のリストに対応する。bad root の層 `K` を底にして下向きに 1 段ずつ降りる。

```
expandOut_base_yama   層 K（山崎噴火の枝）が底
expandOut_step_lower  層 k < K：対角の展開が k+1 段目以上の畳み込みなら、
                      この層の展開は k 段目以上の畳み込みになる
expandOut_layers      上の 2 つを束ねた帰納
```

`k+1` 段目以上の畳み込みが列 `x` より左では層 `k+1` の値そのものであること
(`assemble_above_layer`) は、原文の `assemble_family_prefix`（前置きが一致すれば
畳み込みも一致する）と `assemble_originalGraphs`（元の塔の畳み込みはその層の値）から出る。

## 潰した予想

森の非交差性から出そうに見えて、実際には**偽**だったもの。反例は `Equiv/Sibling.lean` と
`Equiv/NoCross.lean` の冒頭に記録してある。

* 一般の行の兄弟の単調性（列 `(1,1,2,5,7,5)` の行 1）
* 「`root` と `q2` の間の列はすべて値が `U q2` 以上」（列 `(1,1,1,1,2,4,5,4)` の行 1）
* 祖先版の非交差性（列 `(1,1,1,1,2,3,3)` の行 0）

上 2 つの反例は値を 7 以上にしないと現れない。値 6 までの探索では見つからないので、
予想を確かめるときは値の範囲を十分に取ること。

## 書き起こしの忠実さ

`script.js` は Lean の対象ではないので、`Equiv/Yukito.lean` が原本の忠実な写しである
ことは証明の対象にできない。代わりに、原本を実行した出力と突き合わせて `#guard` に
固定してある（`Equiv/YukitoCheck.lean`）。`calcMountain` / `calcDiagonal` / `getBadRoot` /
`expand` の各段階と、分岐を一通り通す例、および上りでない列が `badRootHeight` より
高くなる例を含む。

原本と写しを並べた対応は [correspondence.md](correspondence.md) にある。

`badRootSeamHeight` と `afterCutMountain` は JS で計算されるがその後どこでも使われて
いないので写していない。`newDiagonal` は `.value` しか読まれないので値の関数
`Nat → Nat` として持つ。JS は `newDiagonal[0].push(newDiagonal[0][j])` で同じセルの
参照を積むため `position` が重複するが、値だけを見るぶんには影響しない。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
