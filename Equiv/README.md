[← 戻る](../README.md)

# 証明の骨格

`expand` は 4 つの部品でできている。それぞれについて両版が一致することを示し、
最後に層の再帰で束ねる。

```
calcMountain   差分山脈を作る
calcDiagonal   列の頂をたどって次の層の行を作る（抽出段）
getBadRoot     bad root を探す
Mt.Fuji シェル 山をコピーして継ぎ足し、値を埋める
```

## 山（差分山脈）の段

行 `r+1` の親は「行 `r` の祖先鎖のうち、値が正で自分より小さい最も右のもの」である。
JS はこれを疎配列の走査で計算する。両者が一致することを示すには、一般の行について

```
(a) 鎖の根 root は、根より右で最初に生きている列 j の祖先である
(1) U p ≤ U j     （p は鎖で root の 1 つ手前）
```

の 2 つが要る。`j` が `p` の祖先である場合とそうでない場合に分かれ、後者では `j` と
`p` は共通の親 `root` を持つ兄弟になる。

**兄弟であるだけでは (1) は出ない。一般の行で兄弟の単調性は偽である。** 反例は列
`(1,1,2,5,7,5)` の行 1。効いているのは `j` が
「`root` より右で最初に生きている列」であることで、この条件を落とした一般化はすべて偽になる。

代わりに成り立つのは次の 2 つで、こちらは全層で真である。

```
leftmost_child_all  root が子を持つなら root+1 も子である
sibSucc_all         root+1 と e が root の子で root+1 < e なら U e ≤ U (root+1)
```

`sibSucc_all` は、層を 1 つ降りる前に `e` を `root` の子まで引き上げるのが要点である。
引き上げずに降りると主張の形が変わってしまい閉じない。

## 抽出段

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

## bad root

JS の `getBadRoot` は対角の最後の値が 1 になるまで抽出を繰り返し、その層で
「頂の 1 つ下の段での親」を返す。これはまず密表現側の同じ探索 `badRootOf` に一致し
（`getBadRoot_eq`）、bad root の層では原文の `BadAt` の親、すなわち bad root の列を返す
（`badRootOf_of_badAt`）。分岐条件（行 0 の最後のセルに親が無い ⟺ `findBadRoot` が
`none`）も一致する（`last_parent_none_iff`）。

## 値の層

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

## 森のコピー

Phyrion 側の `expandedMountain a hbad k` は層ごとに 3 通りに分かれる。

```
k < K   badAtLowerContext      下位のコピー
k = K   badAtTerminalMountain  終端のコピー
k > K   OrdinaryCopy           通常のコピー
```

JS の Mt.Fuji シェルは 1 つの三重ループでこの 3 通りをまとめて作る。層ごとにどの枝に
あたるかを読み合わせた。

2 つの枝で違うのは、コピー先の山と、新しく積んだセルの親についての事実だけである。
それを `FujiSpec`（[`Spec.lean`](Spec.lean)）にまとめ、`ShapeRep` から出力までは一度だけ
組み立てた。枝ごとには `yamaSpec` と `lowerSpec` を作るだけである。

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

## 上りでない列

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

## 層の再帰

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
