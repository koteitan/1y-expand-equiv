# 1y-expand-equiv

1-Y 数列の展開規則について、次の 2 つが同じ関数であるかどうかの Lean 4 による検証。

| | 何か | 場所 |
|---|---|---|
| Yukito 版 | Yukito 氏による 1-Y の展開規則 | [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の `script.js` の `expand` |
| Phyrion 版 | Phyrion 氏が独自に定めた祖先保存アルゴリズム | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) の `OneY.Numeric.expandValues` |

Phyrion 版は 1-Y の展開の整礎性と標準生成集合の辞書式整列を Lean 4 で証明している。

ただし **Phyrion 版は Yukito 版の形式化であるとは主張していない**。論文はこう書いている。

> The precise convention considered here is the ancestor-preserving algorithm below and in
> the fixed source snapshot. No equivalence with every variant described elsewhere is assumed.

つまり対象は論文とソーススナップショットで定義された規則そのものであり、他所で記述された
変種との同値性は仮定されていない。

そこで残るのが本リポジトリの問いである。**この 2 つは実際に同じ関数なのか。**
同じであれば、Phyrion 版の整礎性・整列性の結果はそのまま Yukito 版の 1-Y についての
結果になる。

## いま示せていること

`sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

| ファイル | 内容 |
|---|---|
| `Equiv/Yukito.lean` | `script.js` の `calcMountain` を Lean へ書き起こしたもの。疎配列・添字演算・`break` の位置まで写す |
| `Equiv/YukitoCheck.lean` | 書き起こしが `script.js` の出力と一致することの検査 |
| `Equiv/Sparse.lean` | 疎配列の走査（`firstAtLeast`）の性質 |
| `Equiv/Rep.lean` | 疎配列が密表現を表していること（`Rep`）と読み替えの正しさ |
| `Equiv/Lookup.lean` | 列番号での引き方と、JS の隙間 break が無害であること |
| `Equiv/Search.lean` | **親探索が `chainFind` に 1 歩ずつ重なること** |
| `Equiv/Bridge.lean` | 疎表現（生きたセルだけを並べる）と密表現（値 0 が不在）の読み替え |
| `Equiv/Row0.lean` | **行 0 の親写像が一致する**（`restrictedParent_linear`） |
| `Equiv/Row0Spec.lean` | 行 0 の親の初等的な特徴づけ |
| `Equiv/RowSucc.lean` | 正値条件が「鎖の根を除く」ことと同値（`succ_parent_iff`） |
| `Equiv/RootCase.lean` | 残る義務の明文化と、Lean 側が根を親にしないこと |
| `Equiv/RootZero.lean` | 行 0 について残る義務を証明（`firstLive_not_smaller_zero`） |
| `Equiv/RootGen.lean` | 一般の行への還元。義務が 2 本に減ることを示す |
| `Equiv/NoCross.lean` | 辺の非交差性。線形森の場合と、帰納段の主要な場合 |
| `Equiv/Sibling.lean` | 兄弟の単調性。行 0 では真、一般の行では偽であることの記録 |
| `Equiv/FirstLive.lean` | 「最初に生きている列」の条件から出ること。`j` の親が `root` になる |
| `Equiv/SibLive.lean` | 生きた左の兄弟についての単調性。基底と 2 つの場合、liveness の伝播 |
| `Equiv/Tower.lean` | 森の塔。frame と値を層ごとに並べ、行 0 を特別扱いせずに済ませる |
| `Equiv/SibSucc.lean` | **右隣の兄弟の単調性と `RootChildAdjacent`。山の段の残り 2 本** |
| `Equiv/Chain.lean` | 親鎖についての小補題 |
| `Equiv/Mountain.lean` | **山の段の組み上げ。`FirstLiveNotSmaller`** |
| `Equiv/TopFrame.lean` | 抽出後の行の下にある frame（`topForest`）についての底の義務 |
| `Equiv/Extract.lean` | 抽出段。JS の脚歩行が Phyrion の `Pseudo.parent` に一致すること |
| `Equiv/Diagonal.lean` | 抽出段。対角の親が `rawExtract` の親に一致すること |

## 座標の対応

疎表現と密表現は次で対応する。

```
Yukito 版 (行 r, position P)  ↔  Phyrion 版 (行 r, 列 c = P + r)
```

この変換のもとで、`script.js` の「右腿で下へ、親を取り、左腿で上へ」という歩行は、
前の行の親チェーンをそのまま辿ることになる。

## 山（差分山脈）の段

一般の行では次の 2 つが要る。

```
(a) 鎖の根 root は、根より右で最初に生きている列 j の祖先である
(1) U p ≤ U j     （p は鎖で root の 1 つ手前）
```

これがあれば `diff_le_of_a_and_one` で山の段の一致が従う。

場合分けすると次のようになる。`j` が `p` の祖先かどうかで分かれる。

| 場合 | (a) | (1) |
|---|---|---|
| `j` が `p` の祖先 | 済（`a_of_ancestor`） | 済（`one_of_ancestor`） |
| そうでない | 済（`a_of_gparent`） | 済（`one_of_nonancestor_closed`） |

非祖先の場合は `j` と `p` が共通の親 `root` を持つ兄弟になる。しかし
**兄弟であるだけでは (1) は出ない。一般の行で兄弟の単調性は偽である。**
反例は列 `(1,1,2,5,7,5)` の行 1（`Sibling.lean` に記載）。

実際の配置では `j` は「`root` より右で最初に生きている列」であり、この条件が
効いている。上の反例でも `root` の次に生きている列は別の列であって、
実際の配置には現れない。

この条件を落とさずに使うと次が出る（`FirstLive.lean`）。

```
no_dead_ancestor  root より右で j より左にある死んだ列は j の F 祖先になれない
fparent_eq_root   したがって j の F 親は root そのものである
```

型はこうである。そのような列 `w` があると、`w` が死んでいることから
`U w ≤ U root`、`w` が `root` より右の `F` 祖先であることから最大性で
`U j ≤ U w` が出る。ところが `U root < U j` なので

```
U root < U j ≤ U w ≤ U root
```

で矛盾する。

さらに実測で **`j = root + 1`** が分かった。`root` が `Φ` の子を持つなら
`root + 1` は生きている（値 10 まで全数 111,110 列、215,290 件で反例なし）。
子を持つという条件は外せない（列 `(1,1,1,1,1,2)` の行 0 が反例。ただしその
`root = 0` はどの列の鎖の根にもならない）。実際の配置では `root` は必ず `Φ` の
子を持つので、`j` は `root` の右隣になる。

これは大きな簡約で、`root` と `j` の間に列が無いため「間の列はすべて死んでいる」
という仮定が自明になる。`firstLive_eq_succ` に入れた。

`j = root + 1` により次が仮定なしで出る。

```
fparent_succ         j の F 親は root（「間の列が死んでいる」が自明になる）
succ_lt_child        非祖先の場合は j < e
one_of_lower_ancestor  j が一段下で e の祖先なら U e ≤ U j
```

さらに `fparent_succ` は層をまたいで連鎖する。結論
`F.parent (root+1) = some root` が、山ではそのまま一段下の仮定になるからである。
`Compat` は `rows_parent_iff_next_live` が与えるので仮定も要らない。

```
compat_rows        山では値と frame の対応が成り立つ
fparent_succ_step  1 段の連鎖
fparent_succ_down  下まで回した形。行 k+m で成り立てば行 k でも成り立つ
```

したがって `j = root + 1` さえ言えれば、`j` の親が `root` であることが
すべての層で従う。線形 frame まで降りると `root = j - 1` になり整合する。
値の不等式も同時に降りる。

```
value_lt_of_fparent  F 親が root なら その層で U root < U (root+1)
value_lt_down        行 k+m で成り立てば行 k でも成り立つ
root_pos_down        root がその層で生きていることも出る
```

`RootChildAdjacent` は下で証明する（`rootChildAdjacent_tower`）。以前は
「必須ではない」と書いていたが、それは `j = root + 1` を経由しない一般形
（`F` 兄弟で `j` が生きていれば足りる）を目指していたときの話である。その一般形は
**偽**なので、`j = root + 1` は必須である。

これで残る義務は次の 1 本になった。

```
U e ≤ U j     j = root + 1 と e は F 兄弟で j < e
```

## 右隣の兄弟の単調性（解決）

上の 1 本を閉じた（`SibSucc.lean`）。示したのは次である。

```
root の restricted 子である root+1 と e があり root+1 < e なら
  U e ≤ U (root+1)
```

一般の兄弟についてこれは**偽**である（列 `(1,1,2,5,7,5)` の反例）。効いているのは
片方が `root + 1`、すなわち `root` の右隣であるという条件である。上の反例も、
その層で `root + 1` にあたるのは別の列なので除外される。

### 詰まっていた所と抜け道

層で兄弟なら差分の関係で目標は一段下に移る（`tower_case_descent`）。ところが
移った先で `e` は `root` の**子**とは限らず、子孫でしかない。そこで 3 択
（祖先・兄弟・どちらでもない）に分かれ、3 番目が閉じなかった。

抜け道は、一段下がる**前に** `e` を `root` の子まで引き上げることである。
`root` はその層の frame で `e` の祖先なので、`root` の子で `e` に至る道の上に
あるもの `a` が取れる（`child_toward`）。

```
a = root + 1     root+1 は e の祖先なので restrictedParent の最大性で終わる
a ≠ root + 1     root+1 < a で、最大性から U e ≤ U a
                 a と root+1 は frame の親を共有するので、差分の関係で
                 U a ≤ U (root+1) は一段下のまったく同じ主張になる
```

`e` を `a` に置き換えてから降りると、主張の形が層をまたいで変わらない。3 択に
分かれていたのは `e` を引き上げずに降りたからであった。

基底は層 0 である。frame が線形森なので `root < q < e` なる列はすべて `e` の
祖先であり、最大性がそのまま効く。

```
fparent_of_succ          restricted 親が root で列が root+1 なら frame 親も root
child_toward             root の子で e に至る道の上にあるものが取れる
frame_parent_iff_pos     層 m+1 で親を持つ ⟺ 層 m+1 の値が正
sibSucc                  主定理
sibSucc_rows             行の形で書いたもの
one_of_nonancestor_closed  非祖先の場合の (1)。仮定 hsib が消える
```

### 段の対応

`frameAt s (m+1) = restrictedParent (frameAt s m) (towerVal s m)` なので、
`(frameAt s (m+1)).parent x = some root` は「層 `m` の restricted 親が `root`」
を意味する。結論の値は `towerVal s (m+1)` である。層を 1 つ取り違えると
成り立たなくなるので、両方を `SibSucc` の定義に明示してある。

## 最左の子は右隣（`RootChildAdjacent`）

`SibSucc` があると、次が層に関する帰納で出る。

```
root が層 k の frame で子を持つなら、frame での root+1 の親は root である
```

すなわち **`root` の最左の子は `root + 1`** である。これが `RootChildAdjacent` で、
JS の `firstAtLeast` が指す列が `root + 1` であることを与える。

帰納の 1 段はこうである。`e` を `root` の restricted 子とすると、`root` は frame で
`e` の祖先なので、`root` の frame 子 `a` で `e` に至る道の上にあるものが取れる。
1 つ下の段の主張から `root + 1` も `root` の frame 子である。あとは

```
W e ≤ W a         restrictedParent の最大性（a は e の祖先）
W a ≤ W (root+1)  SibSucc（a と root+1 は frame 兄弟で root+1 ≤ a）
W root < W e      e の restricted 親が root であること
```

を繋いで `W root < W (root+1)` を得る。`root` は `root+1` の frame 親なので最も右の
祖先でもあり、restricted 親の条件をすべて満たす。基底の層では frame が線形森なので
`sibling_mono_zero` がそのまま効く。

```
leftmost_child           主定理
rootChildAdjacent_tower  RootChildAdjacent が全層で成り立つ
leftmost_child_rows      行の形で書いたもの
```

`SibSucc` と `RootChildAdjacent` は循環していない。`SibSucc` の証明は
`RootChildAdjacent` を使わない。

### 潰した道（記録）

`Tower.lean` には、層に関する帰納を「3 択が場合 1 か場合 2 に落ちる」という条件
`Resolves` に還元する組み立てがある。この道は使わなかった。条件を満たす不変量が
見つからなかったためである。

```
CommonBelow    結論すら含意しない（列 (1,1,1,2,3) の層 0 が反例）
「層 k+1 で兄弟」  含意しない（列 (1,1,2,5,7,5) の層 1 が反例）
Inv            結論を含意し降下でも保たれるが、3 択が尽きない
```

`Tower.lean` の `frameAt` / `towerVal` / `tower_case_descent` / `frameAt_step` は
`SibSucc.lean` がそのまま使っている。`Resolves` と `Inv` は使っていない。

## 山の段の組み上げ

`RootCase.lean` で立てた残る義務 `FirstLiveNotSmaller` を、揃った部品から
組み立てた（`Mountain.lean`）。要素がすべて正の列について成り立つ。

記号は行 `r` について次のとおり。

```
G = (rows base r).forest = frameAt s (r+1)      その行の森
F = frameAt s r                                 frame（行 0 では線形森）
U = towerVal s r = (rows base r).value          frame の上の値
v = towerVal s (r+1) = (rows base (r+1)).value  次の行の値（= U の差分）
```

手順はこうである。

```
1  root の G 子 p で c に至る道の上にあるものを取る    child_toward
2  hreach から v c ≤ v p
3  root は G 子 p を持つので root+1 は生きている       rootChildAdjacent_tower
4  したがって firstLiveAfter が返す j は root+1        firstLiveAfter_eq_succ
5  root の F 子 e で p に至る道の上にあるものを取る
6  (1)  U p ≤ U (root+1)                              one_of_nonancestor_tower
7  (a)  root は root+1 の F 祖先                       leftmost_child_all
8  v p ≤ v (root+1)                                   diff_le_of_a_and_one
9  1 と 8 を繋いで v c ≤ v j
```

`hroot`（`root` がその行の森の根であること）は使わない。必要なのは `root` が
`G` 子を持つことだけである。

これで `js_root_step_no_parent` の仮定が外れ、**密表現での山の段の一致が閉じた**。

## 抽出段

JS の `calcDiagonal` は列の頂から脚をたどり、**その行で親を持たない節点**で止まる。
Lean の `Pseudo.parent` は代わりに高さの条件 `H p ∈ {H c − 1, H c}` を課す。
この 2 つが同値であることを示した。

JS が訪れる節点 `(h, p)` は必ず行 `h` で生きている（`h ≤ H p`）。その状況で

```
その行で親を持たない  ⟺  H p ≤ h  ⟺  H p = h
```

となる。`≤` の側は `RowMountain.parent_none_iff` が与える。歩行は高さ `H c` から
始まり脚 1 つで高さが変わらないか 1 下がるので、止まった高さは `H c` か `H c − 1`
であり、そこで Lean の条件が成り立つ。

```
top_iff_height_eq  その行で親を持たない ⟺ 高さがちょうどその行
stop_at_top        高さ H c で止まった場合は H p = H c
stop_after_drop    H c − 1 に降りて止まった場合は H p + 1 = H c
```

歩行の停止位置についても、JS の条件と Lean の条件が同値であることを示した。
JS は実質「高さが `H c` 以下」で止まる。歩行が辿るのは行 `H c − 1` の祖先鎖で、
その要素は必ずその行で生きているので高さが `H c − 1` 以上に押さえられる。
上からの `≤ H c` と合わせると、ちょうど Lean の 2 通りに絞られる。

```
chain_height_ge    行 r の祖先鎖の要素はその行で生きている
stop_iff_candidate 鎖の上で「高さ ≤ H c」と「H ∈ {H c − 1, H c}」は同値
```

### 歩行そのもの

停止条件だけでなく、歩行の全体が `Pseudo.parent` に一致することを示した。

JS の脚 1 歩は `position` を 1 ずらしたセルを 2 回引く。行 `r` の `position` は
`列 − r` なので、これは列座標では次になる。

```
position が 1 大きい 1 段下のセル  =  同じ列の 1 段下
position が 1 小さい同じ段のセル    =  同じ列の 1 段上
```

したがって 1 歩は「行 `h − 1` で親 `q` を取り、`q` が行 `h` で生きていれば
その場に留まり、死んでいれば行を 1 つ下げる」である。`height == 0` の枝は
`h − 1` を自然数の切り捨て引き算にしたものと一致するので、JS の 2 つの枝は
1 つの式で足りる。

行の記録は要らない。行が下がるのは `H q < h` のときだけで、そのとき
`parent_endpoint` から `H q = h − 1` となり、下がった先で必ず停止条件が
成り立つ。すなわち歩行は高々 1 回しか降りず、降りたその場で止まる。よって
歩行が辿る列は行 `H c − 1` の祖先鎖そのものである。

```
legStep           JS の脚 1 歩（行, 列）
jsWalk            行と列を持つ歩行。その行で親を持たないところで止まる
legWalk           列だけの歩行。高さが bound 以下で止まる
jsWalk_eq_legWalk 行の記録は要らない
legWalk_sound     止まった列は鎖の上にあり、それより右の鎖の要素は高さ条件を破る
legWalk_isSome    高さ条件を満たす鎖の要素があれば歩行は止まる
jsWalk_eq_pseudo  JS の脚歩行 = Phyrion の Pseudo.parent
```

`legStep_defined` は、JS が `parentIndex = -1` を引かない理由を記録する。
行 `h ≥ 1` で生きている列は行 `h − 1` に親を持つので、`l` は必ず実在のセルを指す。

なお `calcDiagonal` の 2 つの `while` は、`l` 側が完全一致で探し、`m` 側が
`<` で走ってから `==` を確かめる。後者はそのまま「その列が生きているか」の判定に
なっており、山の段で見つかった `firstAtLeast` のようなずれは起きない。

### 対角の親

`calcDiagonal` の後半は 2 つの探索からなる。どちらも「森の親を辿り、最初に値が
小さい所で止まる」形をしている。

```
pw            線形森（i−1, i−2, …）を辿る
後半のループ  diagonalTree（擬親森）を辿る
```

`diagonal[i]` は列 `i` の頂の値 `topValue base i`、`diagonalTree[i]` は脚歩行の
結果すなわち `Pseudo.parent` である。Phyrion 側で対応するのは

```
rawExtract base hpos = select (Pseudo.forest (mountain base hpos)) (topValue base)
```

で、その値は `topValue base`、その親は
`restrictedParent (Pseudo.forest …) (topValue base)` である。

値がすべて正なので `restrictedParent` の `0 < value p` の条件は自動になり、
JS の「値が小さい所で止まる」がそのまま `restrictedParent` に一致する。

```
chainFind                     森の親を辿り最初に pred を満たす所で止まる探索
chainFind_some / chainFind_none  止まった列の特徴づけ
chainFind_eq_restrictedParent 探索 = restrictedParent
rawExtract_value              対角の値 = rawExtract の値
rawExtract_parent             対角の親 = rawExtract の親
pw_eq_restrictedParent        pw = 線形森の restrictedParent
```

JS は対角を文字列にしてから `calcMountain` に渡す。素の数として書けば読み直しの
際に行 0 の規則で親が振られ、それは `restrictedParent linearForest` である
（`restrictedParent_linear`）。一致しないときだけ `"値v親"` の形で親を明示し、
`parseSequenceElement` が `forcedParent` を立てて行 0 の規則を飛ばす。どちらの枝
でも復元される親は擬親森の `restrictedParent` である。明示側の添字は
`Math.max(Math.min(i-1,p),-1)` で丸められるが、`p` は `i` の祖先なので `p < i`
であり丸めは効かない。親が無い場合は `"値v-1"` と書かれ、読み直しでも `-1` に戻る。

### 疎配列側の書き起こし

`calcDiagonal` を写した（`Yukito.lean`）。

```
topAt        列 i を含む最上段とその添字
legStepJS    脚 1 歩（疎配列版）
legWalkJS    脚歩行。着いた列を返す（none が JS の -1）
diagEntry    列 i についての値と歩行結果
diagList     JS の diagonal と diagonalTree
pwScan       JS の pw
treeScan     diagonalTree 上の探索
calcDiagonal 出力（文字列にする前）。forced が JS の `"v"` 付き
clampPar     JS の Math.max(Math.min(i-1,p),-1)
parseDiag    parseSequenceElement 相当
```

写すときに 1 か所つまずいた。JS の脚は `position - 1` を目標にするが、
`position = 0` のとき目標は `-1` になり、どのセルにも一致しないので必ず段が下がる。
自然数の切り捨て引き算では `0` になってしまい、同じ場所に留まる。そこだけ場合分け
した。`searchUpper` の `position - 1` は等号判定に使われず `firstAtLeast` に渡る
だけなので、`-1` と `0` で結果が変わらず、この問題は起きない。

出力とその読み直しも `#guard` で JS と突き合わせてある（`"v"` が出る例を含む 5 列）。

### 疎配列側と密表現の対応

頂の探索と値の対応を示した（`DiagBridge.lean`）。

```
MountainRep   山の各行が Rep と ParRep を満たすこと
rowAt_eq      範囲内なら rowAt はその行
topAt_eq      topAt は height i の段とその添字を返す
diagEntry_value  JS が diagonal に積む値は Phyrion の topValue
```

`topAt` は段を上から下へ走らせて列 `i` を含む最上段を探す。密表現側でそれにあたる
のが Phyrion の `height` で、「行 `r` に列 `i` がある ⟺ `r ≤ height i`」
（`live_iff_le_height`）がそのまま効く。

脚 1 歩も繋いだ（`legStepJS_eq`）。状態の読み替えは「（段, 添字）→（段, 列）」で、
JS の 1 歩と密表現の `legStep` が 1 対 1 に対応する。段が下がるのは

```
親の列が -1 の位置にある（position = 0）  → height q ≤ q < h なので必ず下がる
親の列がこの段で死んでいる                → h ≤ height q が偽
```

の 2 通りで、どちらも `live_iff_le_height` と `height_le_self` で判定が一致する。

位置引きは `lookupPos` として切り出した。`lookupPos_some` / `lookupPos_none` が
「生きた列は引ける・死んだ列は引けない」を与える。

1 歩の対応を歩行全体に回した（`legWalkJS_eq`）。密表現側の `jsWalk_eq_pseudo` と
繋いで、**対角の 1 要素が一致する**ところまで来た（`diagEntry_eq`）。

```
JS の diagonal[i]      = topValue base i
JS の diagonalTree[i]  = Pseudo.parent (mountainOf s hs) i
```

対角のリスト全体も繋いだ（`diagList_eq`）。

```
diagList (calcMountain s (fuel+1))
  = (List.range s.length).map (fun i => (topValue base i, Pseudo.parent MM i))
```

これには「山が十分な段を持つ」ことが要る（`height_lt_length`）。`mountainGo` は
「その行の全セルが親を持たない」ところで止まるが、密表現ではそれが「次の行が空」に
あたるので、生きた列がある限り段は伸びる（`mountainGo_length`）。段の数は
`height_lt` と `sequence_value_le_bound` から `sequenceBound s` で押さえられる。

2 つの探索も繋いだ。

```
treeScan_eq      treeScan は chainFind（擬親森を辿る）
pwScan_eq        pwScan は scanLeft（線形森を辿る）
calcDiagonal_eq  出力全体
```

`calcDiagonal` の出力はこうなる。

```
値      topValue base i
親      擬親森の restrictedParent（= rawExtract の親）
"v"     線形森の restrictedParent（= 読み直しの既定の親）と食い違うときだけ付く
```

### 読み直し

JS は対角を文字列にして `calcMountain` に渡す。`parseSequenceElement` にあたるのが
`parseDiag` で、`"v"` 付きは `forced` を立てて親を固定し、素の数は行 0 の規則に
任せる。素の数になるのは擬親森と線形森の `restrictedParent` が一致するときだけ
なので、**どちらの枝でも親は擬親森の `restrictedParent`** になる（`diagItem_par`）。

明示側の丸め `Math.max(Math.min(i-1,p),-1)` は、親が左にあるので効かない
（`clampPar_of_lt`）。

```
rep_parseDiag    読み直した行は抽出後の値を表す
parRep_extract   行 0 に親を付けた行の親 = rawExtract の親
extract_value    列番号で引いた値 = rawExtract の値
extract_parent   列番号で引いた親 = rawExtract の親
```

**これで抽出段が閉じた。**

## 疎配列との橋渡し

JS は行を「生きたセルだけを `position` 昇順に並べた配列」で持つ。列番号で引くには
`while (row[j].position < target) j++` で走査する。この走査の性質を証明した
（`Sparse.lean`）。

```
firstAtLeast_before     それより手前のセルは position が target 未満
firstAtLeast_at         止まった所のセルは position が target 以上
firstAtLeast_eq_of_mem  position がちょうど target のセルがあれば、そこで止まる
firstAtLeast_gt_of_not_mem  無ければ、指すセルは target より右にある
```

3 つ目が「疎配列を列番号で引く」の正しさである。4 つ目が山の段で唯一の食い違いに
なる箇所で、`firstLiveNotSmaller_ofSequence` がそこを埋める。

その上に表現述語を置いた（`Rep.lean`）。

```
mono   position は狭義単調増加
val    セルの値は密表現の値
live   セルの値は正
cover  生きている列はすべてセルとして現れる
```

これがあれば、疎配列を列番号で引いた値は密表現の値にそのまま一致する
（`rep_read`）。列 `r` 未満については JS 側は `position ≥ 0` なのでセルが無く 0、
密表現側も 0 である（`rows_value_zero_of_lt`：列 `c` が行 `r+1` で生きるには親が
行 `r` で生きていなければならず、親は左にあるので、生きた列は 1 行ごとに右へ
1 つ以上ずれる）。`assignParents` は `par` しか書き換えないのでこの 4 条件を保つ。

`Rep` には列の上限が付いている。`ofSequence` が列 `n` 以降を値 1 で埋めるからで
ある。埋めた列は値 1 なので親を持てず（親には真に小さい正の値が要る）、他の列の
親にもならない。行 1 以降では死んでいるので、上限が効くのは行 0 だけである。
行 0 が入力列を表すことは示した（`rep_row0`）。

`nextRow`（階差行の構成）が表現を保つことも示した（`rep_nextRow`）。JS の
`nextRow` は「親を持つセルだけを残し、`position` を 1 減らし、値を親との差にする」
で、これが密表現の `Row.difference` にあたる。

`position` を 1 減らすところは自然数の切り捨て引き算なので、`position = 0` のセルが
残ると単調性が壊れる。壊れないのは、親を持つセルの `position` が 1 以上だから
である（親は左にあるので `position` が真に小さい列が存在する）。この事実には
`par` が森に対応していること（`ParRep`）が要る。

```
stepCell       nextRow が 1 セルに対して行う操作
nextRow_toList 畳み込みが filterMap であること
ParRep         par が森に対応している（列番号で読んだ形）
pos_pos_of_step  残るセルの position は 1 以上
step_facts     残るセル 1 つぶんの事実（列・値・正値）
rep_nextRow    階差行も表現になっている
```

### JS の隙間 break

JS の親探索には Lean 側に対応するもののない条件がもう 1 つある。

```js
if (j<0 || j<lastLayer.length-1 && lastLayer[j].position+1!=lastLayer[j+1].position) break;
```

「`j` のすぐ右に隙間があれば打ち切る」というもので、`Yukito.lean` の `breakHere`
である。これは**右隣の列も生きていれば発動しない**（`not_breakHere`）。右隣の列が
生きていれば配列でも隣り合うからである。

親探索が見る列は鎖の要素であり、鎖の要素 `q` は必ず「ある列の親」なので、
`leftmost_child_rows`（最左の子は右隣）から `q + 1` も生きている
（`chain_succ_live`）。したがって**鎖の上では隙間 break は発動しない**。発動しうる
のは鎖の根に降りたときだけで、そこは `firstLiveNotSmaller_ofSequence` が押さえる。

```
firstAtLeast_eq   走査の特徴づけ
rep_lookup        生きた列は配列の中にあり、firstAtLeast はその添字を指す
rep_lookup_dead   死んだ列を引くと、firstAtLeast は右隣を指す
rep_succ_index    生きている 2 列が隣り合えば配列でも隣り合う
not_breakHere     右隣が生きていれば隙間 break は発動しない
chain_succ_live   鎖の要素の右隣はその行で生きている
```

`chainFind_eq_restrictedParent'` は、止まる条件に「値が正」も入れた形である。
疎配列では死んだ列がそもそも見えないので、JS 側ではこの条件が自動になる。

### 親探索が `chainFind` に重なること

JS の `searchUpper` は、1 つ下の行の親チェーンを辿り、各要素の列を今の行で引いて
値を比べ、最初に小さいものを親にする。Lean 側の `chainFind` は同じ形をしており、
`chainFind_eq_restrictedParent'` で `restrictedParent` に一致する。この 2 つが
1 歩ずつ重なることを証明した（`searchUpper_eq`）。

食い違いうるのは 2 か所だけで、どちらも押さえてある。

```
firstAtLeast のずれ  鎖の要素が今の行で死んでいるときだけ起きる（= 鎖の根）
                     そこで指す列の値は c の値以上（root_step_le）
隙間 break           鎖の要素の右隣は生きているので鎖の上では発動しない
                     （chain_succ_live と not_breakHere）
```

根に降りたときは JS も Lean も親を返さない。JS は隙間 break で、あるいは値の比較に
失敗してもう 1 歩進んだ先で親が無くなって止まる。Lean は正値条件で根を弾く。

帰納で担ぐのは「今いる位置 `x` 以上の生きた祖先はすべて値が `c` の値以上」という
条件である。これまでの比較が失敗してきたことを表しており、根に着いたときに
`root_step_le` の仮定にそのまま渡る。

### `assignParents` への接続

`searchUpper_eq` の頭に `firstAtLeast prev (c.pos + 1)`（列 `c` 自身の引き当て）を
差し込み、`assignParents` が計算する親が `restrictedParent` に一致することを示した
（`parRep_assignParents`）。これで **1 行ぶんの橋渡しが閉じた**。

燃料は JS が `prev.size + 1` を使う。これで足りることは、鎖に沿って真に減る量として
「その列の疎配列での添字」を取れば出る（`idx_measure`、`chainFind_ge`）。列番号その
ものは燃料より大きくなりうるので、添字を測度にするのが要点である。

```
searchUpper_lt        探索が返す添字は配列の中にある
col_lt_of_parent      親を持つ列は入力列の中にある
idx_measure           疎配列での添字は鎖に沿って真に減る
chainFind_stable / chainFind_ge   燃料が足りていれば増やしても答えは変わらない
parRep_assignParents  assignParents の親 = restrictedParent
```

残るのは、この 1 行ぶんを `calcMountain` の全行に回して `Rep` と `ParRep` を同時に
持ち上げることである。

書き起こしが原本と一致していることは、`script.js` の `calcMountain` の出力と
突き合わせてビルド時に検査している（`YukitoCheck.lean`、5 列）。

セルには `forced` を持たせてある。JS の `forcedParent` で、入力が `"値v親"` の形
だったときに立ち、親探索を飛ばす。素の数から作った行では常に `false` だが、抽出段が
作る列は `"v"` を含みうるので、写しておく必要がある（`NoForced` で持ち回る）。

## bad root と、一般の行から作る山

JS の `getBadRoot` は、対角の最後の値が 1 になるまで抽出を繰り返し、そこで最後の列
`n−1` の頂の 1 つ下の段でその親を返す。

Phyrion 側の対応物は `findBadRoot`（`OneY.Numeric.RootSearch`）で、
`BadAt a k r c p`（層 `k`、行 `r` で `c` の親が `p` かつ値の差がちょうど 1）を満たす
唯一の場所を返す。`badAt_height_and_top` が「そこでは `height c = r+1` かつ
`topValue c = 1`」を与えるので、JS の停止条件（最後の値が 1）とちょうど対応する。
読みでは

```
JS の getBadRoot(s) = (findBadRoot s hs (n−1)).column
```

である。

### 何が要るか

JS は抽出のたびに山を作り直す。したがって橋渡しを**一般の行から作る山**へ広げる
必要がある。ここまでの橋渡しは `ofSequence s` から始まる山に固定されていた。

広げるときの難所は、塔の底である。`ofSequence s` の下にある frame は線形森だが、
抽出後の行の下にある frame は擬親森（`Pseudo.forest`）である。山の段の証明は底で
線形性を使っていた。

```
leftmost_child_all の底  線形森では parent e = some root が e = root+1 を強制する
sibSucc_all の底         同上により root+1 < e が起きえず、主張が空虚になる
```

擬親森ではどちらも自明ではない。実測（読みの補助）では

```
「最左の子が右隣」   擬親森でも成り立つ（全数 v≤6 L≤7 の 55,986 列、破れ 0）
sibSucc の一般形     擬親森では偽（同じ範囲で 912 列が反例。例: (1,3,6,5)）
sibSucc の実配置形   成り立つ（56,917 件、破れ 0）
```

となった。山の段でも一般形は偽で実配置形だけが真だったので、同じ構図である。

なお、抽出後の行を底にした山そのものは JS と密表現で一致している（同じ範囲で
破れ 0）。つまり結果は成り立っており、証明の道筋だけが底で効かない。

### 擬親森ではなく `topForest` を使う

Phyrion は `rawExtract` の親が `topForest` 上の `restrictedParent` に一致することを
示している（`rawExtract_parent_eq_topForest`）。

```
topForest.parent c = if height c = 0 then none else some (rootAt (height c − 1) c)
```

「頂の 1 つ下の段での成分の根」である。擬親森より構造がはっきりしていて、山の段で
作った道具がそのまま効く。**底の義務は 2 本とも `topForest` について証明できた**
（`TopFrame.lean`）。

```
topForest_heights         topForest の親から段の関係を読む（H e = H root + 1）
topForest_leftmost_child  最左の子は右隣
topForest_sibSucc         root+1 と e について topValue e ≤ topValue (root+1)
```

2 本目の筋はこうである。`topForest` の親が `root` なら段はちょうど `H root + 1` な
ので、両方の `topValue` はその段の値である。`e` はその段が頂なので次の段では親を
持たず、`restrictedParent` の最大性から `root` の子 `a`（`e` へ至る道の上）について
`V e ≤ V a`。あとは `sibSucc_rows` で `V a ≤ V (root+1)` を繋ぐ。

残るのは、塔をこの底に対して立て直し（`frameAt 0` を `topForest` にする形へ
一般化し）、山の段の各定理をその形で通すことである。

## 残っている課題

```
山の段    済（密表現・疎配列とも）
抽出段    済（密表現・疎配列とも）
bad root  読みは付いた。橋渡しを一般の行へ広げるのが先
コピー層  未
```

コピー層が全体の大半である。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
