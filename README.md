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
| `Equiv/Extract.lean` | 抽出段。JS の脚歩行が Phyrion の `Pseudo.parent` に一致すること |
| `Equiv/Diagonal.lean` | 抽出段。対角の親が `rawExtract` の親に一致すること |

## 座標の対応

疎表現と密表現は次で対応する。

```
Yukito 版 (行 r, position P)  ↔  Phyrion 版 (行 r, 列 c = P + r)
```

この変換のもとで、`script.js` の「右腿で下へ、親を取り、左腿で上へ」という歩行は、
前の行の親チェーンをそのまま辿ることになる。

## 残っている課題

山（差分山脈）の段について、一般の行では次の 2 つが要る。

```
(a) 鎖の根 root は、根より右で最初に生きている列 j の祖先である
(1) U p ≤ U j     （p は鎖で root の 1 つ手前）
```

これがあれば `diff_le_of_a_and_one` で山の段の一致が従う。

場合分けすると次のようになる。`j` が `p` の祖先かどうかで分かれる。

| 場合 | (a) | (1) |
|---|---|---|
| `j` が `p` の祖先 | 済（`a_of_ancestor`） | 済（`one_of_ancestor`） |
| そうでない | 済（`a_of_gparent`） | **未** |

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

`RootChildAdjacent` については、`root + 1` が `p` の `F` 祖先（または `p` 自身）
である場合を証明した（`rootChildAdjacent_of_ancestor`）。`e` を `root` の `F` 子で
`p` の鎖にあるものとすると `root + 1 ≤ e` であり、`root + 1 = e` のときが
これにあたる。残るのは `root + 1 < e` の場合である。この場合は
「`root` が `root+1` の `F'` 祖先である」ことと「その層で値の大小が成り立つ」ことが
互いを要求して噛み合わない。

ただし `RootChildAdjacent` は必須ではない。`fparent_eq_root` は
「間の列が死んでいる」という条件だけで `F.parent j = root` を与えるので、
`j` と `e` が `F` 兄弟であることは `j = root + 1` を経由せずに出る
（`j_e_siblings`）。非祖先の場合の組み上げも済んでいる（`one_of_nonancestor`）。

したがって残る義務は次の 1 本に集約される。

```
U e ≤ U j     j と e は F 兄弟で j < e、j は生きている
```

これを回す帰納のために `Tower.lean` で層を並べた。

```
frameAt 0     = linearForest
frameAt (k+1) = (rows (ofSequence s) k).forest
towerVal k    = (rows (ofSequence s) k).value
```

この形にすると行 0 を特別扱いせずに済む。層 0 の frame は線形森なので

* 相異なる 2 列は兄弟になれない（親は必ず 1 つ前の列）
* `q1 < q2` なら常に `q1` は `q2` の祖先

したがって降下は層 0 で必ず場合 1 になって止まる。

3 択も塔の形で揃えた。

```
tower_case_ancestor  層 k の frame で q1 が q2 の祖先なら最大性で閉じる
tower_case_descent   層 k+1 の frame で兄弟なら、層 k の目標から層 k+1 の目標が出る
tower_case_meet      合流点の直上 z で q2 側を押さえて連鎖する
```

帰納の組み立ても済ませた。層 `k` で「場合 1 が成り立つ」か「場合 2 が成り立つ」
かのどちらかであることを `Resolves` として切り出すと、層に関する帰納で結論まで
通る（`sib_mono_of_resolves`）。層 0 では兄弟が存在しないので、`Resolves` は
必ず場合 1 を与えて止まる。

`Resolves` は無条件には成り立たない。降下で保たれる不変量を条件に付ける。

```
CommonBelow k q1 q2 :  q1 と q2 は層 k の frame で共通の祖先を q1 より左に持つ
```

層 `k+1` で兄弟なら、その親 `t` は層 `k` の frame で両者の祖先で `t < q1` なので
`CommonBelow` が従う（`commonBelow_of_siblings`）。したがって降下で保たれる。

**注意。** `CommonBelow` は結論すら含意しない（列 `(1,1,1,2,3)` の層 0 が反例）。
「層 `k+1` で兄弟」も含意しない（列 `(1,1,2,5,7,5)` の層 1 が反例）。
したがって `sib_mono_of_resolves` の仮定が満たせるかはまだ示せていない。

実測で確かめてある正しい対応は次である。

```
兄弟      frameAt s k
値        towerVal s k
liveness  (frameAt s (k+1)).parent q1 ≠ none
```

この形なら値 12 まで 123,641 件で反例が無い。上の 2 つの反例も、この対応では
該当層で `q1` が死んでいるため除外される。層の対応は取り違えやすい。

正しい不変量を立て直した。目標が層 `m` のとき担ぐべき条件は

```
Inv m q1 q2 :  (frameAt s (m+1)).parent q2 = some t かつ t < q1 < q2
               かつ (frameAt s (m+2)).parent q1 ≠ none
```

である。liveness を一段上に取るのが要点で、降下すると弱まるだけなので保たれる。
実測では値 12 まで 271,452 列・191,959 件でこの条件から結論が出て反例が無い。
内訳は祖先 189,600、兄弟 1,775、どちらでもない 584。

```
frame_live_down  liveness は一段下へ伝わる
frame_live_pos   liveness からその層で値が正であることが出る
inv_pos          不変量から q1 の値が正
inv_descend      兄弟なら不変量が一段下へ移る
```

ただし `Inv` のもとで 3 択は尽きない。「`q1` は `t` の次に生きている列」という
条件を足しても 556 件残り、そのうち 501 件は合流点で `u < q1` となって閉じない。

実際の配置では合流点は 69,364 件中 5 件だけで、いずれも `u = q1` であった。
つまり `Inv` は実際の配置より弱く、余計な組を拾っている。

山の段について残るのは、降下で保たれてかつ 3 択が尽きるだけ強い不変量を
見つけることである。
すなわち各層で

* `q1` が `q2` の祖先であって、`q2` の親より右にある
* または `q1` と `q2` が兄弟である

のどちらかが成り立つこと。実測では 3 番目の場合（合流点）が 69,364 件中 5 件
だけ現れ、いずれも `q2` を小さい列に置き換えれば 2 番目に帰着した。

これにより `j` と、`root` の `F` 子で `p` の鎖にある列 `e` が `F` 兄弟になる。
`U e ≥ U p` は最大性から出るので、残るのは `U j ≥ U e` だけである。すなわち

```
F 兄弟 q1 < q2 で q1 が生きているなら U q1 ≥ U q2
```

を示せばよい。左の兄弟が生きているという条件が要る。これを外した形は偽である。

これは層を降りる再帰で片付く見込みである。各層で次の 3 つのいずれかになる。

1. `q1` が `q2` の祖先 → その層の最大性で完了
2. `q1` と `q2` が兄弟 → `sibling_descent` で一段下の同じ問題に移る
3. どちらでもない → 合流点を取り、`q2` を置き換えて続ける

基底は行 0 で、frame が線形なので `q1 < q2` なら必ず 1 になる。
値 12 までの探索では 69,364 件すべてがこの再帰で尽き、未処理は 0 件だった。

`SibLive.lean` に基底（`sibling_mono_zero`）、場合 1（`sibling_case_ancestor`）、
場合 2（`sibling_case_descent`）、および liveness の伝播（`live_descends`）を置いた。
帰納法の仮定が層をまたいで一様になることも確かめてある。降下すると liveness の
仮定は一段弱まるが、それは下の層がちょうど要求する形である。

残るのは場合 3 の処理と、この 3 択を回す整礎帰納の組み立てである。
場合 3 では `q2` が真に小さい列へ置き換わるので、`(層, q2)` の辞書式順序で減る。

### 反例を探すときの注意

一般の行についての予想は、値を 7 以上にしないと反例が現れないものが複数あった。
値 6 までの探索では真に見えてしまう。範囲を十分に取ること。

主要な主張（(a)、(1)、(D)）は次の範囲で反例が無いことを確かめてある。

```
全数   長さ 6 まで・値 12 まで      271,452 列
乱択   長さ 3〜5・値 40 まで        300,000 列
乱択   長さ 6〜10・値 20 まで        60,000 列
```

鍵になるのは **辺の非交差性**（`NoCross`）である。「`F.parent b = a` と
`F.parent y = x` で `a < x < b < y` は無い」という形で、入れ子は許す。
祖先まで一般化した形は偽である（列 `(1,1,1,1,2,3,3)` の行 0 が反例）ので、
`Refines` を経由した継承は使えず、辺版を直接扱う。

非交差性があれば (a) が出る。`j` の `F` 鎖が `root` を跨ぐとすると、跨ぐ辺と
`p` の鎖にある辺 `(root, b')` が真に交差するか、`root` が跨ぐ辺の下端に一致して
矛盾するからである。

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

抽出段に残るのは、疎配列と密表現の橋渡し（`Bridge.lean` の続き）である。

山の段が済んでも、抽出の残り・bad root・コピー層が残る。コピー層が全体の大半である。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
