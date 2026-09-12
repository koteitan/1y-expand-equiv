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

## 答え：同じ関数である

```
theorem expand_eq (s : List Nat) (hs : ZeroY.Legal s) (N m efuel : Nat)
    (hm : sequenceBound s ≤ m) (hml : s.length ≤ m) (hef : sequenceBound s ≤ efuel)
    (hn : 0 < s.length) :
    expandOut (expandJS N (m + 1) efuel (calcMountain s (m + 1))) = expandValues s hs N
```

`ZeroY.Legal s` は「すべての要素が正」かつ「先頭が 1」で、Phyrion 版が
`expandValues` に課している条件そのものである。`m` と `efuel` は燃料で、
`sequenceBound s`（値の最大）と列の長さ以上であれば足りる。

`sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ
（`Equiv/Lower.lean` の `expand_eq`）。

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
| `Equiv/BadRoot.lean` | `expand` の分岐条件と、JS の `getBadRoot` が `findBadRoot` に一致すること |
| `Equiv/Recon.lean` | **差分の関係を満たす値は `Reconstruction.value` に一致する**（`value_of_diff`） |
| `Equiv/Fuji.lean` | Mt.Fuji シェルの補助走査（列の有無・継ぎ目の高さ・上りの判定） |
| `Equiv/Fill.lean` | **値の埋めの構造**。`fillRow` / `fillValues` が満たす差分の関係 |
| `Equiv/NoBad.lean` | **bad root が無いときの一致**（`expand_eq_no_bad`） |
| `Equiv/Copy.lean` | Mt.Fuji シェルの三重ループの構造・座標・出力の幅 |
| `Equiv/Shape.lean` | **`ShapeRep` と値の層の結論**（`expandOut_eq_value`） |
| `Equiv/Yama.lean` | 山崎噴火の枝（原文の層 `k = K`）の組み立て |
| `Equiv/Lower.lean` | **`k < K` の枝の組み立て・層の再帰・全体の一致**（`expand_eq`） |

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

### 塔を一般の底へ

塔を `Tower` として立て直した（`Tower.lean`）。

```
structure Tower where
  frame0 : ParentForest                      底の frame
  base   : Row                               その上に載る行
  hbase  : base.forest.parent = restrictedParent frame0 base.value
  hpos   : ∀ c, 0 < base.value c
  A0     : 底での「最左の子は右隣」
  B0     : 底での「右隣の兄弟の単調性」
```

`frameAt T 0 = T.frame0`、`frameAt T (k+1) = (rows T.base k).forest` である。山の段の
定理はすべてこの形に書き直した。底の 2 つの義務だけが塔ごとに変わる。

```
linearTower s hs   入力列から作る塔。底は線形森で、A0 と B0 は自明
（抽出後の行の塔）  底は topForest。A0 と B0 は TopFrame.lean で証明済み
```

底の 1 歩は `base_step` にまとめた。`Φ0` の子 `e` について、`frame0` 親が `root` で
あることと `V e ≤ V (root+1)` が同時に出る。ここだけが底の義務を使う。

以前の `ofSequence` 版の定理は `linearTower` での特殊化として言い直してある
（`leftmost_child_seq`、`sibSucc_seq`、`root_step_le_seq`、
`firstLiveNotSmaller_ofSequence`）。

抽出後の行の塔も組み立てた（`extractTower`）。

```
frame0  (mountainOf s hs).topForest
base    extractRow s hs = rawExtract
hbase   rawExtract_parent_eq_topForest（Phyrion 側の定理）
hpos    topValue_pos
A0      topForest_leftmost_child
B0      topForest_sibSucc
```

これで**抽出後の行についても山の段が閉じた**（`firstLiveNotSmaller_extract`）。

橋渡しの側も一般の底へ広げた。塔に列の上限を足した `Setting` を使う。

```
structure Setting where
  tower : Tower
  n     : Nat                              列の上限
  htail : ∀ c, n ≤ c → tower.base.value c = 1
```

上限より右の列は行 1 以降で死ぬ（`setting_value_zero_of_ge`）。`Search.lean` と
`Lift.lean` の `mountainGo_rep` / `mountainGo_length` をこの形に書き直し、
一般の行から始める入口を足した（`calcMountainFrom_rep`）。

```
linearSetting s hs   入力列から作る設定
extractSetting s hs  抽出後の行から作る設定
```

これで**抽出後の行から作った山も全行が一致する**（`calcMountain_extract_rep`）。
抽出の繰り返し（`getBadRoot` や `expand` の再帰）を支える土台になる。

抽出段（`DiagBridge`）も一般の設定へ広げた。JS の山が設定に対応していることを
`MtRep` にまとめ、すべての定理をその形にした。

```
structure MtRep (S : Setting) (M : List Rowj) : Prop where
  rowRep  各行が Rep と ParRep を満たす
  size0   行 0 の大きさは列の上限
  tall    段が足りている
```

これで `calcDiagonal` の対応（`diagList_eq` / `calcDiagonal_eq` / `parRep_extract` /
`extract_value` / `extract_parent`）が、入力列の山でも抽出後の行から作った山でも
そのまま使える。入力列の場合は `mtRep_calcMountain` が `MtRep` を与える。

抽出後の行から作った山についても `MtRep` を組み立てた（`mtRep_extract`）。

```
extractTowerOf T   塔を 1 回抽出した塔（底の frame は topForest）
extractSet S       設定を 1 回抽出した設定
mtRep_extract      抽出後の行から作った山も設定に対応している
```

`Setting` には値の上限 `bnd` を持たせた。段の数を押さえるのに使う。抽出しても
上限は増えない（`topValue ≤ value`）ので、同じ `bnd` を引き継げる。

**これで抽出を任意回繰り返せる。** 入力列から `mtRep_calcMountain` で始め、
`mtRep_extract` を繰り返し適用すればよい。

## `expand` の分岐

Phyrion の `expandValues` は最後の列の bad root で分岐する。

```
match findBadRoot s hs (s.length − 1) with
| none   => s.take (s.length − 1)
| some z => reconstructedValues … (x + N*(x − z.column))
```

JS の `expand` は「行 0 の最後のセルが親を持たない」で分岐し、持たなければ最後の列を
落とす。この 2 つの分岐条件が同じであることを示した（`last_parent_none_iff`）。

`getBadRoot` も写した（`Yukito.lean`）。出力は `script.js` の `getBadRoot` と
`#guard` で突き合わせてある（7 列）。

### JS の `getBadRoot` は密表現側の探索である

密表現側の探索を `badRootOf` として書き、両者が一致することを示した
（`getBadRoot_eq`）。

```
badRootOf S c (fuel+1) =
  if topValue S.base c = 1 then (rows S.base (height S.base c − 1)).forest.parent c
  else badRootOf (extractSet S) c fuel
```

要る部品は 3 つだった。

```
lastCol_eq_iff    行の最後のセルが列 n−1 ⟺ その列がその行で生きている
topRowOfLast_eq   JS の段の探索は height (n−1) を返す
badRoot_found     見つけた段の 1 つ下で最後のセルの親を読むと密表現の親になる
lastVal_eq        行 0 の最後のセルの値は列 n−1 の値（停止条件の対応）
```

再帰は `mtRep_extract` に乗る。担ぐ不変量は `1 < base.value (n−1)`（列 n−1 の値が
1 より大きい）で、停止しなかった層では `topValue > 1` なので次の層でも保たれる。
これがあると停止した層で `height (n−1) ≥ 1` が言え、JS が `mountain[i-1]` を
触るのが安全になる。

`badRootOf` が Phyrion の `findBadRoot` に一致することも示した。

```
iterSet_base          k 回抽出した設定の底は layers の k 段目
badRootOf_of_badAt    bad root の層まで降りるとその親を返す
badRootOf_eq          badRootOf = findBadRoot の column
getBadRoot_eq_findBadRoot   JS の getBadRoot = findBadRoot の column
```

手前の層で止まらないことは `badAt_unique`（bad root は唯一）から出る。もし手前の
層 `j` で `topValue = 1` なら `badAt_of_top_one` がそこに bad root を作ってしまい、
唯一性に反する。

**これで bad root が閉じた。** `expand` の `none` の枝と合わせて、残るのは `some` の
枝、すなわちコピー層だけである。

## コピー層（`some` の枝）

Phyrion 側はこうなっている。

```
expandValues s hs N (some z の枝)
  = reconstructedValues (expandedGraphs a hbad (sequenceBound s)) (x + N*(x − z.column))

expandedGraphs a hbad bound = (range bound).map (expandedMountain a hbad)
reconstructedValues graphs width = (range width).map (assemble graphs (fun _ => 1))

assemble []          top = top
assemble (M :: rest) top = Reconstruction.value M (assemble rest top) 0
```

`expandedMountain a hbad k` は層 `k` ごとに 3 通りに分かれる。

```
k < K   badAtLowerContext      下位のコピー
k = K   badAtTerminalMountain  終端のコピー
k > K   OrdinaryCopy           通常のコピー
```

値の復元は

```
Reconstruction.value M top r c
  = if r ≤ height c then top c + Σ_{u=r}^{height c − 1}（行 u での c の親の値）else 0
```

である。JS 側は最後に

```js
result[i][j].value = result[i][result[i][j].parentIndex].value + result[i+1][k].value;
```

で `NaN` を埋める。これは `V_r(c) = V_r(親) + V_{r+1}(c)` で、上の閉じた式を
展開したものにあたる。JS も `newDiagonal = expand(diagonal,n,false)` で層をまたいで
再帰するので、`assemble` のリストと対応する。

### 攻め方

```
1. 値の復元      差分の関係を満たす値は Reconstruction.value に一致する（森に依らない）
2. 層の再帰      JS の expand の再帰 ↔ expandedGraphs のリスト
3. 森のコピー    Mt.Fuji の枝 ↔ badAtLowerContext / badAtTerminalMountain / OrdinaryCopy
```

1 は森の形に依らないので先に片付けた（`Recon.lean`）。

```
recon_step     行を 1 つ剥がす：value r c = 親の値 + value (r+1) c
recon_top      頂では value = top
recon_above    頂より上では 0
value_of_diff  差分の関係を満たす値は Reconstruction.value に一致する
```

`value_of_diff` は列についての強帰納（親は左にある）と、行についての上からの帰納の
2 重帰納である。JS の埋め方がこの 3 条件（差分・頂・頂より上）を満たすことを言えば、
値の部分は済む。

3 の下ごしらえとして、`expand` の本体で使う走査を写して密表現に翻訳した。

```
hasCol         行 r に列 j があるか        ⟺ 0 < (rows base r).value j
seamHeightOf   列 j を含む最上段の 1 つ上  = height j + 1
isAscending    行 bh で列 j の親鎖が列 seam に届くか
                 ⟺ 列 j がその行で生きていて、seam が j 自身かその祖先
```

`isAscending` の翻訳では、鎖が列について真に減ることを使う。JS は「`seam` より左に
出たら false」で打ち切るが、密表現ではそれが「祖先でない」に対応する
（`ascendTo_iff`）。親の添字が子の添字より小さいこと（`par_index_lt`）が燃料の
減少を与える。

Phyrion 側の `OrdinaryCopy`（層 `k > K`）は次の形である。

```
source0 c    = if c < y then c else y + (c − y) % length      元の列
block0 c     = if c < y then 0 else (c − y) / length          何番目のコピーか
parentCopy b p = if p < y then p else p + b*length            親の写り先
parent r c   = ((mountain.row r).parent (source0 c)).map (parentCopy (block0 c))
height c     = height (source0 c)
```

`y` が bad root の列、`x` が最後の列、`length = x − y` である。JS 側の

```js
parentPosition = 元の親の position
  + parentShifts*(afterCutLength−badRootSeam)*(元の親の列 >= badRootSeam) − (k−sy)
```

がこれにあたる。`(元の親の列 >= badRootSeam)` の掛け算が `parentCopy` の場合分けで
ある。

### Mt.Fuji シェルのセル 1 個ぶん

3 つの枝（Bb / Br / Be）は `sy`（元の段）と `sx`（元の列の添字）の選び方だけが違い、
積むセルの形は共通である。共通部分を写した。

```
FujiParams   badRootSeam / badRootHeight / cutHeight / afterCutLength / yamakazi
len          コピー 1 つぶんの長さ（afterCutLength − badRootSeam）
sourceIdx    元のセルの添字（isReplacingCut のときは行の最後）
parentPos    親の position。JS で負になる場合は none（どのセルにも一致しない）
fujiCell     積むセル 1 個
```

`parentPos` で自然数の切り捨て引き算に注意が要る。JS の `parentPosition` は負に
なりうるが、そのときはどのセルにも一致しないので親なしになる。切り捨てて 0 に
すると位置 0 のセルに誤って一致してしまうので、`none` で表す。

値は、親が無いときだけ確定し、あるときは後で埋める。JS は後者を `NaN` にするが、
ここでは値 0 を「未確定」の印にした。実際の値はつねに正なので混ざらない。

### 三重ループと後処理

`expand` の本体も写した。

```
pushAt        段 k にセルを積む（段が無ければ作る）
fujiSource    上りの列の枝の選択（Bb / Br replace / Br extend / Be）
fujiSourceAt  上りでない列は Bb 枝だけ（sy = k）
fujiRows      段 k = 0 … kmax−1
fujiSeams     継ぎ目の列 j = badRootSeam …
fujiIters     繰り返し i = 1 … n
cutChild      子を切る
fillRow       段 1 つぶんの値の埋め
fillValues    上から下へ値を埋める
dropEmptyTop  末尾の空の段を落とす
```

枝は `sy`（元の段）と `sx`（元のセルを行の最後から取るか）の選び方だけが違うので、
`fujiSource` にまとめた。`script.js` は `isAscending` で 2 つのループに分かれており、
偽のほうは段が `k < seamHeight` までで枝も Bb だけである。`fujiSourceAt` がその
場合分けにあたる。上りでない列が `badRootHeight` より高くなるのは値が 16 以上の
ときなので、小さい例では 2 つのループの違いは表に出ない。

入口も写した。

```
valAtIdx       添字で値を読む
topRowWithCol  列 j を含む最上段（badRootHeight の走査）
yamaVal        山崎噴火の枝での newDiagonal の値（周期的なコピー）
expandJS       expand 本体
expandOut      行 0 の値の列（JS の出力）
```

`badRootSeamHeight` と `afterCutMountain` は JS で計算されるがその後どこでも使われて
いないので写していない。`newDiagonal` は `.value` しか読まれないので値の関数
`Nat → Nat` として持つ。JS は `newDiagonal[0].push(newDiagonal[0][j])` で同じセルの
参照を積むため `position` が重複するが、値だけを見るぶんには影響しない。

**写しは `script.js` の `expand` の出力と一致した。** 長さ 2〜5・値 4 以下・`n ∈ {1,2}`
の 680 例と、上りでない列が `badRootHeight` より高くなる例で食い違いなし。分岐を
一通り通す 11 例を `#guard` に固定してある（`YukitoCheck.lean`）。

残るのは 2（層の再帰）と 3（森のコピー）の証明で、3 が全体の大半である。

### 三重ループの構造（済）

コピーの中身に踏み込む前に、ループが段をどう変えるかだけを取り出した（`Copy.lean`）。

```
pushAt_length / rowAt_pushAt   段への積み足し。k ≤ res.length のもとで
                                 rowAt (pushAt res k c) m
                                   = if m = k then (rowAt res k).push c else rowAt res m
fujiRows_length / rowAt_fujiRows  段のループ。段 m < kmax に 1 個ずつ積む
RowExt / rowExt_fujiIters      段は後ろに伸びるだけ。既にある添字のセルは変わらない
popFold / rowAt_cutChild       子を切る。残る段は cutH 以下なら pop されたもの
```

`fujiCell` に渡る「今の段」がループに入る前の段そのものであることは、段のループが
`k = 0, 1, 2, …` の順に積むことから出る（段 `k` を触るとき上の段はまだ未着手）。
`RowExt` はそれを繰り返しループ全体へ広げたもので、`fujiCell` が `lookupPos` で
引く親の添字が最終形でも同じ添字であることに使う。

座標の対応も取れている。

```
fujiCell_col          積むセルの列は段によらず j + len*i（= encode j i）
parentPos_eq          親の新しい列 = 元の親の列 + （継ぎ目以上なら shifts*len）
fujiCell_par_col      積むセルの par が指す先の列も同じ式になる
js_shift_eq_parentCopy  その桁上げは Phyrion の parentCopy そのもの
yamaVal_eq_source0    山崎噴火の枝の周期的コピーは OrdinaryCopy の source0
```

段に載る列も確定した。

```
RowsMono / ColLt          どの段も位置が真に増加、どのセルの列も上限未満
fujiIters_invariant       繰り返しのあと上限は badRootSeam + len + len*n
HasCol / hasCol_fujiIters  m < kmax(i,j) なら段 m に列 j + len*i が載る
cell_fujiIters            逆に、載っているのは元のセルかそれらだけ
lookupPos_of_rowExt       積む時点で引いた親の添字は最終形でも同じ
```

積む列は `(i,j)` の辞書式順で真に増えるので、末尾への積み足しで各段の位置の単調性が
保たれる。これらは 2 つの仮定
「継ぎ目の高さ ≤ `j+1`」と「切りの落差 `d` ≤ コピー 1 つぶんの長さ」
のもとで成り立つ（`kmaxAt_le`）。前者は `seamHeightOf_le_succ` として証明した
（`seamHeightOf_eq` と `height_le_self'` から出る）。残る仮定は `d ≤ len` だけである。
「元の段 ≤ 行き先の段」は枝の形から直ちに出る（`fujiSource_le`）。

### 出力の幅は一致する（済）

`badRootSeam + len = afterCutLength` なので、繰り返し `i` の継ぎ目の列 `j` は列
`j + len*i` に写り、`i = 1 … n` で `afterCutLength … afterCutLength + len*n − 1` を
隙間なく埋める。もとの `0 … afterCutLength−1` と合わせて、行 0 は
`0 … afterCutLength + len*n − 1` をちょうど覆う。

```
dense_of_cover        位置が真に増加し列を覆うなら、大きさ = 幅、位置 = 添字
row0_dense_fujiIters  行 0 の大きさは afterCutLength + len*n
expandJS_some         some の枝の展開（expP / expNd / expRes を名前付きにした）
expandOut_eq_range    出力は列 0 … W−1 の値を並べたもの
expandOut_some        expandOut (expandJS …)
                        = (List.range (afterCutLength + len*nrep)).map (列の値)
```

Phyrion 側は

```
reconstructedValues graphs W = (List.range W).map (assemble graphs (fun _ => 1))
```

で、`W = x + N*(x − z.column)`。`x = afterCutLength`、`x − z.column = len` なので
**幅は一致する。**

### 値の層は閉じた

疎な山が密な山を表していることを `ShapeRep` として書いた（`Shape.lean`）。

```
mono     各段の位置は真に増加
parLt    親の添字は自分より前
cellCol  段 r にあるセルの列は高さ r 以上
cover    高さ r 以上の列は段 r にある
parCol   親を持つセルの親の列は密な山の親
parNone  親を持たないセルは密な山でも根
step     差分の関係 V r c = V r（親の列）+ V (r+1) c
valTop   親を持たないセルの値は頂の値
topPos   頂の値は正
tall     段が足りている
```

`tall` ももともと `height c + 1 < 段数` としていたが、コピーの最上段について
偽になりうるので `height c < 段数` に弱めた。最上段は `fillValues` が触らない
ので、その段の値はセルの値そのものである（`colVal_top_last`）。

`step` はもともと「親を持つセルの値は 0」としていたが、それは誤りだった。
JS の `fillRow` は値が 0 でないセルを触らないので、**元からある列のセルは
元の値をそのまま残す**。そこで条件を差分の関係そのものに変えた。値 0 のセルでは
値の埋めから、値が入っているセルでは元の山の差分の関係から出る。

値の整合性は保たれている。列 `c < x` では原文の復元値も元の値に一致する
（`top c = topValue base c`、`source0 c = c` のため）。

`ShapeRep Rs G top W` から、`value_of_diff_prefix`（`value_of_diff` の前半だけ版）を
使って

```
expandOut (fillValues Rs) = (List.range W).map (Reconstruction.value G top 0)
```

が出る（`expandOut_eq_value`）。原文は

```
assemble (G :: rest) top c = Reconstruction.value G (assemble rest top) 0 c
```

なので、`top = assemble rest (fun _ => 1)` とすれば**そのまま同じ式**である。

途中で使った橋渡しは次の 3 つ。

```
readValAt_eq_readVal  r ≤ c なら position で読むのと列で読むのは同じ
readVal_of_index      添字で読んだ値はその列で読んだ値
posMono_fillValues    埋めは位置と親を変えないので単調性も保つ
```

JS が 1 つ上の段を position `pos−1` で引くのが「同じ列を引くこと」に等しいのは
`r+1 ≤ c` のときである。値 0 のセルは親を持つので頂ではなく、列 > 段だから
条件は満たされる。

**つまり残る義務は `ShapeRep` を作ることだけになった。**

### 山崎噴火の枝

JS の `yama` は「対角の最後の値が 1」、すなわち bad root がその層自身で見つかること
である。原文の `expandedMountain` は層 `k` について

```
k < K  : badAtLowerContext
k = K  : badAtTerminalMountain
k > K  : OrdinaryCopy
```

と分かれるので、`yama` の枝が `k = K`（`badAtTerminalMountain`）にあたる。

落差 `d = cutHeight − badRootHeight` はこの枝では 0 である（`cutHeight' =
badRootHeight = cutH − 1`）。そこで枝の選び方が単純になる。

```
fujiSource_yama   d = 0 かつ yamakazi のとき
                    fujiSource P i k isRep = (k, isRep && k < badRootHeight)
kmaxAt_yama       積む段の数は継ぎ目の高さそのもの（上りの判定によらない）
kmaxAt_le_yama'   d ≤ len が自明なので kmax ≤ j + len*i + 1 が仮定なしで出る
```

`kmax ≤ j + len*i + 1` の仮定だった「継ぎ目の高さ ≤ `j+1`」は仮定なしで出せた。
`hasCol M r j` が真なら段 `r` に列 `j` のセルがあり position は非負なので `r ≤ j`
である（`hasCol_le`）。したがって `seamHeightOf M j hi ≤ j + 1`
（`seamHeightOf_le_col`）。積む段の数が正であることも、行 0 にすべての列がある
ことから出る（`hasCol_zero` / `kmaxAt_pos'`）。

親の添字が自分より前であることもループ全体へ広げた。積むセルの親は
`lookupPos` で「今の段」を引いた添字なので、積む場所の添字より必ず小さい。

```
ParLt / ParLt.dep                   どの段でも親の添字は自分より前
fujiCell_par_lt / fujiCellAt_par_lt 積むセルについて
parLt_fujiRows / parLt_fujiSeams / parLt_fujiIters  ループで保たれる
parLt_of_mtRep / parLt_cutChild     元の山と子を切ったあとでも成り立つ
```

原文の `TerminalCopy.Context` は

```
height c = if c < x then M.height c
           else if source c = x then M.height y else M.height (source c)
parent r c = if c < x then (M.row r).parent c
             else if source c = x ∧ level ≤ r then (M.row r).parent y
             else ((M.row r).parent (source c)).map (parentCopy (block c))
```

で、`source c = y+1 + (c−y−1) % L`、`block c = (c−y−1)/L`、`L = x−y`、
`level` は `M.height x = level + 1` を満たす段である。JS 側の継ぎ目 `j` は
`y ≤ j < x` を走り列 `j + L*i` に写る。JS の `badRootHeight` は `level` にあたる。

座標と親の対応を式として揃えた。

```
coord_source_block       y < j < x なら source (j+L*i) = j、block = i
coord_source_block_seam  0 < i なら source (y+L*i) = x、block = i−1
srcColYama               元の列は isRep かつ k < badRootHeight なら x、そうでなければ j
sourceIdx_col            列 j が段 k で生きていれば sourceIdx はその列のセル
sourceIdx_last_col       列 x が段 k で生きていれば行の最後のセルはその列
parRep_some / parRep_none  疎配列の親を密表現の親として読む
fujiCell_par_parentCopy  積むセルの親の列 = parentCopy shifts（元の親の列）
fujiCellAt_par_yama      それを山崎噴火の枝に当てはめた形
parentCopy_of_parent_y   根 y の親は y より左なので桁上げは恒等
```

`j = y` が原文の retained seam（`source = x`）にあたり、そのときの桁上げは `i−1`。
JS が渡す `shifts = i − ir`（`ir` は `isRep` なら 1）と一致する。最後の
`parentCopy_of_parent_y` が、原文が `level ≤ r` の場合に `parentCopy` を掛けず
JS が掛ける、という見かけの違いを埋める。

子を切る操作も原文と同じである。

```
size_rowAt_cutChild      cutH 以下の段は最後のセルが 1 つ減る
rowAt_cutChild_getElem?  残ったセルは元のセルそのもの
posMono_pop / rowsMono_cutChild  位置の単調性は保たれる
size_rowAt_cutChild_zero 行 0 の大きさは n−1（= afterCutLength）
colLt_cutChild           残るセルの列はすべて n−1 より小さい（列 n−1 が消える）
hasCol_cutChild_zero     行 0 は列 0 … n−2 を覆う
cutChild_length_ge       段の数は 1 つしか減らない
```

JS は列 `x` を切ってから `i = 1` の継ぎ目 `j = y` で列 `y + L = x` を積み直す。
原文はこれを「`source x = x`、`height x = M.height y`」と書いている。

新しい対角の値も形が揃った。

```
expNd_yama_source0  expNd c = valAtIdx (対角の行 0) (source0 c)
```

原文の `assemble_expanded_above` は、`K+1` 段目以上のコピーを畳むと
`ordinaryContext.copyValue (layers a (K+1)).row.value` になると言う。
`layers a (K+1)` の値は `layers a K` の `topValue`、すなわち対角の値なので、
これは上の式と同じものである。

### 山崎噴火の枝の組み立て（`Yama.lean`）

部品を繋いで、この枝での**出力の幅が仮定なしで定まる**ところまで来た。

```
expP_yama_cut            この枝では cutHeight = badRootHeight（落差 0）
expCutH_eq               切る段は列 n−1 の高さ
expP_afterCutLength      切ったあとの列数は n−1
two_cells / one_cell     生きている列の数だけその段のセルがある
height_lt_expRes_length  切ったあとも列 j < n−1 の高さは段の数より小さい
kmaxAt_expRes_eq         kmax(i,j) = height j + 1
hasCol_yama              列 j + len*i は段 0 … height j に載る
expandOut_some_yama      expandOut (expandJS …)
                           = (List.range ((n−1) + len*nrep)).map (列の値)
```

`height_lt_expRes_length` が要るのは、子を切ると最上段が空になって段が 1 つ減る
ことがあるからである。減るのは最上段に列 `n−1` しか無かったときで、そのとき
`j ≠ n−1` がそこに生きていればセルは 2 つ以上あり、pop しても空にならない。
したがって `height j = M.length − 1` なら段は減らない。

`kmaxAt_expRes_eq` は原文の `TerminalCopy.height` と一致する。列 `j + L*i` について、
`j = y` なら `source = x` で `M.height y`、そうでなければ `M.height j` であり、
どちらの場合も `M.height j` だからである。

枝の判定と bad root も密表現の言葉になった。

```
lastVal_of_rep    行の最後の値は最後の列の値
lastVal_expDg     対角の最後の値は topValue base (n−1)
expYama_iff       expYama M (f+1) ↔ topValue base (n−1) = 1
getBadRoot_yama   この枝では getBadRoot = (rows base (height(n−1)−1)).forest.parent (n−1)
expSeam_yama      継ぎ目 y は「最後の列 x = n−1 の、頂の 1 つ下の段での親」
```

密表現側の `badRootOf` は「頂の値が 1 ならその層で止まり、頂の 1 つ下の段での親を
返す」なので、JS の `yama` はまさに「bad root がこの層で見つかる」場合である。

そこでコピー先の山を組み立てた。

```
yamaContext S y … : TerminalCopy.Context
  mountain    = mountainOf' S（設定の底から作る山）
  coordinates = ⟨y, n−1, y < n−1⟩
  level       = height (n−1) − 1
  last_parent = 「最後の列の親が y」（expSeam_yama）
  last_height = height (n−1) = level + 1
```

これが原文の `badAtTerminalMountain` にあたる山である。

その山の高さと親を書き下した。

```
yamaContext_height_orig   c < n−1 なら height c = height base c
yamaContext_height_seam   0 < i なら height (y + L*i) = height base y
yamaContext_height_other  y < j < n−1 なら height (j + L*i) = height base j
yamaContext_parent_orig       c < n−1 なら元の親そのもの
yamaContext_parent_seam_low   置き換えの継ぎ目・r < level: 元の列 x、桁上げ i−1
yamaContext_parent_seam_high  置き換えの継ぎ目・level ≤ r: 元の列 y、桁上げ無し
yamaContext_parent_other      それ以外: 元の列 j、桁上げ i
```

高さはどの列 `j + L*i` についても「元の列 `j` の高さ」になり、JS の
`kmax(i,j) = height base j + 1`（`kmaxAt_expRes_eq`）と一致する。

**そして親が一致することを証明した。**

```
fujiCellAt_parCol_yama:
  JS が段 k に積むセル（列 j + L*i）の par が添字 p を指すとき、
    (yamaContext …).parent k (j + L*i) = some（添字 p のセルの列）
```

3 分岐がそのまま対応する。`j = y`（置き換えの継ぎ目）で `k < level` なら元の列は
最後の列 `x` で桁上げ `i−1`、`level ≤ k` なら元の列は根 `y`。後者で JS は桁上げ
`i−1` を掛けるが、根 `y` の親は `y` より左なので `parentCopy` は恒等になる
（`parentCopy_of_parent_y`）。`j ≠ y` なら元の列は `j` で桁上げ `i`。

### 残っているところ

`ShapeRep` の条件のうち `parNone`（JS が親を見つけないなら原文も親なし）は、
対偶「原文に親があれば JS も見つける」を示すのが本筋である。そこで要るのが

- 親の列 `pc` が、積む時点の段 `k` に**既に載っている**こと

である。積む列は `(i, j)` の辞書式順で真に増えるので、`pc < j + L*i` なら
`pc` はより早い `(i', j')` で積まれているか、元からある列である。そのための
道具は揃えた。

```
hasCol_cutChild  子を切ったあとも、列 n−1 より左の生きた列は残る
col_decomp       x ≤ c < x + L*n なら c = j + L*i（0 < i ≤ n、y ≤ j < x）
col_lt_lex       j1 + L*i1 < j2 + L*i2 なら (i1,j1) は辞書式で小さい
hasCol_fujiSeams / hasCol_fujiIters  途中の状態での被覆
rowExt_fujiSeams / rowExt_fujiIters  段は後ろに伸びるだけ
```

値の側は `fujiCell` の定義から直ちに出る（`fujiCellAt_val_of_par_none` /
`fujiCellAt_val_of_par_some`）。親を持たないセルの値は `topVal = nd（その列）`、
親を持つセルの値は 0 である。

### 積む時点での被覆（済）

```
hasCol_state:
  (i'+1, y+t) を処理する直前の段 k には、
    pc < (y+t) + L*(i'+1) かつ k ≤ height_G pc
  を満たす列 pc がすべて載っている。
```

場合分けは 3 つ。`pc < n−1` なら元からある列で `hasCol_cutChild`、
`pc = j2 + L*i2` で `i2 ≤ i'` なら前の繰り返しで `hasCol_fujiIters`、
`i2 = i'+1` かつ `j2 < y+t` なら同じ繰り返しの前の継ぎ目で `hasCol_fujiSeams`。
積む列が `(i, j)` の辞書式順で真に増えること（`col_lt_lex`）が効いている。

親が負の位置にならないことも出た。どの `RowMountain` でも `height c ≤ c` である
（`rowMountain_height_le`。親は真に左へ動き、親は自分の段まで生きているから）。
原文の `parent_endpoint`（`r ≤ height p`）と合わせると、親の新しい列は段より右に
あるので、JS の `parentPos` は負にならない。

### 「原文に親があれば JS も見つける」の鎖（部品が揃った）

```
parRep_some_of_forest  密表現の親が some なら疎配列のセルも親を持つ
rowMountain_height_le  どの山でも height c ≤ c
  ＋ 原文の parent_endpoint（r ≤ height p）
    ⇒ 親の新しい列は段より右
parentPos_some         したがって parentPos = some（新しい列 − k）で、負にならない
hasCol_state           その列は積む時点の段 k に載っている
hasCol_pos             そこから添字と位置を取り出す
fujiCell_par_isSome    lookupPos がその添字を見つけるので par は some
```

### `ShapeRep` の組み立て（進行中）

```
parLt_yama / rowsMono_yama  parLt と mono（切り・積み足し・空段落としを通す）
tall_yama                   高さ height_G c の段は空でないので残る
rows_diff                   元の山の差分の関係
yamaRaw / yamaRs            埋めの前・埋めに渡す疎な山に名前を付けた
cutChild_cell_val           残るセルの値は元の山の値で、正
colVal_orig_yama            元からある列の値は元の山の値のまま
step_orig_yama              **step の「元からある列」側**
cell_fujiSeams' / cell_fujiIters'
                            積んだセルの正体（fujiCellAt そのもの）と
                            積んだ時点の状態を返す強い版
```

`step` の「元からある列」側は、3 つの列の値がいずれも元の山の値のままなので
元の山の差分の関係に帰着する。「コピーで作った列」側は積んだセルの値が 0 なので
値の埋めから出る。後者には積んだセルの正体が要るので `cell_fujiIters'` を作った。
返る状態はちょうど `hasCol_state` が被覆を主張している状態である。

`valTop_yama` は `yamaRs` の形で証明済み（`nd` が「`c < n−1` では
`topValue base c`」を満たすという仮定つき）。

途中で仮定を 1 つ落とした。`sourceIdx_yama_col` が要求していた
「最後の列が段 `k` で生きている」は、「行の最後から取る」枝でしか使わない。
その枝では `k < badRootHeight` なので、`badRootHeight ≤ height (n−1)` さえ
あれば導ける。積んだセルについては `k ≤ height（元の列）` しか分からないので、
この弱化が要る。

セルの正体を `yamaRs` の言葉に持ち上げる道具も揃えた。

```
rowExt_fujiSeams_mono / rowExt_fujiIters_mono  ループの回数について単調
rowExt_state_to_final / rowExt_state_to_yamaRs 積んだ時点の状態から最終形へ
yamaRs_cell            埋めに渡す疎な山のセルは 元からあるセルか 積んだセル
fujiCellAt_col_yama    kmax の範囲から積むセルの列が定まる
valTop_push_yama       積んだセルが親を持たないなら val = nd（その列）
```

### **`ShapeRep` が構成できた（山崎噴火の枝）**

```
shapeRep_yama:
  nd が「c < n−1 では topValue base c」かつ正であれば
    ShapeRep (yamaRs M mfuel nd nrep)
             ((yamaContext S y …).toRowMountain) nd ((n−1) + len*nrep)
```

10 条件の埋め方は次のとおり。

```
mono     rowsMono_yama       parLt   parLt_yama
cellCol  cellCol_yama        cover   cover_yama
parCol   parCol_yama         parNone parNone_yama
step     step_orig_yama（c < n−1）/ step_push_yama（c ≥ n−1）
valTop   valTop_yama         topPos  仮定      tall  tall_yama'
```

`shapeRep_value` と合わせると出力が出る。

```
expandJS_out_yama:
  expandOut (expandJS nrep mfuel (efuel+1) M)
    = (List.range ((n−1) + len*nrep)).map
        (Reconstruction.value ((yamaContext S y …).toRowMountain)
          (expNd nrep mfuel efuel M) 0)
```

原文は

```
reconstructedValues (G :: rest) W = (List.range W).map (assemble (G :: rest) (fun _ => 1))
assemble (G :: rest) top c = Reconstruction.value G (assemble rest top) 0 c
```

なので**同じ式**である。

さらに、こちらで組んだ `TerminalCopy.Context` が原文の `badAtTerminalContext`
そのものであることも示した。

```
iterSet_n       列の上限は抽出で変わらない
yamaContext_eq  BadAt (rootedSequence s hs) K d x y と s.length−1 = x のもとで
                  yamaContext (iterSet (linearSetting s hs.1) K) y … 
                    = badAtTerminalContext … hbad
```

3 つのデータ欄が一致する。`mountain` は `iterSet_base`（`k` 回抽出した設定の底は
`layers` の `k` 段目）、`coordinates` は `iterSet_n` と `s.length−1 = x`、
`level` は `badAt_height_and_top`（`height x = d+1`）から。証明欄は Prop なので
証明無関係で一致する。

頂の値も原文と一致した。

```
size_rowAt_expDg / valAtIdx_expDg  対角の行 0 は抽出段そのもので、
                                   添字 s の値は topValue base s
expNd_topValue     expNd c = topValue base (source0 c)
layers_succ_value  layers a (k+1) の値は layers a k の topValue
assemble_above_eq  K+1 段目以上を畳むと topValue (layers a K).row (source0 c)
expNd_eq_assemble  したがって expNd = assemble（K+1 段目以上）(fun _ => 1)
```

**これで山崎噴火の枝（原文の層 `k = K`）は、山の同定と頂の値の両方が片付いた。**

### `k < K` の枝（`badAtLowerContext`）の読み

原文の `badAtLowerContext a hbad hk = activeLowerContext a hbad.1 hk` は
`LowerCopy.Context` で、

```
mountain    = mountain (layers a k).row
coordinates = ⟨y, x, y < x⟩
last_root   : mountain.rootAt (height y) x = y
last_higher : height y < height x
floor := height y
rise  := height x − floor
InCone c := floor ≤ height c ∧ rootAt floor c = y
```

JS 側と読み合わせると **`bh = floor`、`d = rise`** である。JS の
`badRootHeight` は「列 `seam` を含む最上段」＝ `height y` であり、
`cutHeight = height x` だからである。

高さは

```
height c = if c ≤ x then M.height c
           else if InCone (source c) then M.height (source c) + block c * rise
                else M.height (source c)
```

で、JS の `kmax = if isAsc then seamH + d*i else seamH` に対応する。
`isAscending` が `InCone` にあたる（「段 `floor` での鎖が継ぎ目 `y` に届く」）。
`j = y` の列については `source = x`、`block = i−1` で、`InCone x` は `last_root`
そのものだから `height = height x + (i−1)*rise = floor + i*rise` となり、
JS の `floor + 1 + d*i`（= 高さ + 1）と合う。

親は

```
parent r c = if c ≤ x then (M.row r).parent c
             else if InCone s ∧ floor ≤ r then
               if r < floor + b*rise then ((M.row floor).parent s).map (· + b*length)
               else ((M.row (r − b*rise)).parent s).map (· + b*length)
             else ((M.row r).parent s).map (parentCopy b)
```

で、真ん中の 2 つが JS の「Br replace」「Br extend」にあたる。山崎噴火の枝で
`rise = 0` だったため潰れていた分岐がここで効いてくる。

形式化はここまで進んだ。

```
fujiSrcRow / fujiSource_notyama  この枝では「行の最後から取るか」はつねに isRep
ancestor_conv        ZeroY 側の Ancestor（TransGen）と OneY 側（帰納型）の言い換え
root_eq_iff          r が根なら root c = r ↔ (r は c の祖先 か r = c)
parent_none_at_top   頂には親が無い
isAscending_iff_root isAscending M bh seam j fuel = true
                       ↔ bh ≤ height j ∧ (rows base bh).forest.root j = seam
```

最後のものが原文の `InCone`（`floor ≤ height c ∧ rootAt floor c = y`）と
同じ条件である。継ぎ目 `y` は段 `floor = height y` で頂なので親を持たず、
「祖先に届く」と「根が一致する」が同値になる。

そこでコピー先の山を組み立てた（`Lower.lean`）。

```
lowerContext S y x …        こちらの Setting から LowerCopy.Context を作る
lowerContext_floor / _rise  floor = height y、rise = height x − height y
lowerContext_inCone         InCone c ↔ (height y ≤ height c ∧ 段 height y の根が y)
isAscending_iff_inCone      **JS の isAscending は InCone そのもの**
inCone_seam                 継ぎ目自身は InCone（その段で頂だから根）
lowerContext_height_orig    c ≤ x では高さは元の山のまま
lowerContext_height_seam    height (y + (x−y)*i) = height y + i*rise
lowerContext_height_other   y < j ≤ x なら
                              height (j + (x−y)*i)
                                = if InCone j then height j + i*rise else height j
kmaxAt_eq_height_lower      **JS の kmax = 原文の高さ + 1**
```

`kmaxAt_eq_height_lower` で、この枝についても山の形（高さ）が一致した。
残るのは親の対応で、原文の

```
parent r c = … else if InCone s ∧ floor ≤ r then
               if r < floor + b*rise then ((M.row floor).parent s).map (· + b*length)
               else ((M.row (r − b*rise)).parent s).map (· + b*length)
             else ((M.row r).parent s).map (parentCopy b)
```

の真ん中の 2 つが JS の Br replace / Br extend にあたる。

枝ごとに読み合わせると次のように対応する（`b` は `block c`、`r` は段）。

| 列 | 段 | 原文 | JS（`fujiSrcRow`） |
|---|---|---|---|
| `y + L*i`（`source = x`, `b = i−1`） | `r < floor` | `((M.row r).parent x).map (parentCopy b)` | `sy = k`、元の列は行の最後（= `x`） |
| 同上 | `floor ≤ r ≤ floor + b*rise` | `((M.row floor).parent x).map (·+b*L)` | `sy = bh` |
| 同上 | `floor + b*rise < r` | `((M.row (r−b*rise)).parent x).map (·+b*L)` | `sy = k − d*(i−1)` |
| `j + L*i`（`y < j < x`, `InCone j`, `b = i`） | `r < floor` | `((M.row r).parent j).map (parentCopy b)` | `sy = k` |
| 同上 | `floor ≤ r ≤ floor + b*rise` | `((M.row floor).parent j).map (·+b*L)` | `sy = bh` |
| `j + L*i`（`¬InCone j`） | 全段 | `((M.row r).parent j).map (parentCopy b)` | `sy = k`（Bb 枝のみ） |

原文が真ん中の枝で `parentCopy` ではなく無条件の `(·+b*L)` を使うのは、
そこでの親が `y` 以上だから（鎖が `y` に届く＝ `InCone`）で、
`parentCopy` は `y` 以上では無条件の加算に一致する。境目（`r = floor + b*rise`）は
原文の第 3 枝に落ちるが `r − b*rise = floor` なので第 2 枝と同じ式になり、
JS の `≤` と原文の `<` の食い違いは消える。

`¬InCone s` の枝は、原文が段 `r` そのものを使う（`((M.row r).parent s).map
(parentCopy b)`）のに対し、`script.js` も `isAscending` が偽のときは Bb 枝
（`sy = k`）しか使わないので、そのまま対応する。親のセルが積まれていることは

```
parent_endpoint        r ≤ M.height p
height_parentCopy_ge   M.height p ≤ height (parentCopy b p)
```

から出る。したがってこの枝に幾何的な追加の義務は無い。

原文の 3 つの枝は 1 つにまとめられる。上りの列では `r < floor + b*rise` なら
`floor`、そうでなければ `r − b*rise` を使うが、これは `floor` で下から押さえた

```
max floor (r − b*rise)
```

に等しい（`clamp_srcRow`）。JS の `fujiSrcRow` も、段が `floor + rise*i` 以下で
あればこれに一致する。継ぎ目の列では `b = i−1`、そうでない列では `b = i` で、
どちらも 4 番目の枝（`k − d*i`）には落ちない。

```
fujiSrcRowAt            上りかどうかまで込めた元の段（上りでなければ k）
fujiSrcRowAt_eq         **JS の元の段 = if 上り ∧ floor ≤ k then max floor (k − b*rise) else k**
lowerContext_parent_new c = s + b*L（0 < b）での原文の親を開く
lowerContext_parent_other  y < j < x の列
lowerContext_parent_seam   継ぎ目の列（元の列は x、block は i−1）
lowerContext_parent_src **原文の親 → 元の段・元の列・その親**
sourceIdx_lower_col     JS の元のセルの列（継ぎ目なら n−1、そうでなければ j）
```

`lowerContext_parent_src` が山崎噴火の枝の `yamaContext_parent_src` にあたる。

JS 側のセルとの突き合わせも済んだ。

```
fujiCellAt_par_lower              JS のセルの親は元の段の元の列の親の写し
fujiCellAt_par_some_of_parent_lower  原文に親があれば JS も見つける
fujiCellAt_parCol_lower           JS の親のセルの列は原文の親
fujiCellAt_parNone_lower          JS が親を見つけなければ原文でも根
```

**落差は幅を超えない。** 段 `r ∈ [floor, height x]` について `rootAt r x` は
真に増え、`rootAt floor x = y`、`rootAt (height x) x = x` なので

```
rise = height x − floor ≤ x − y = len      rise_le_length
```

である。これで `kmaxAt` の一様な上界が取れ、三重ループの不変量が使える。

これらから **`k < K` の枝でも `ShapeRep` が構成できた**。

```
rowsMono_lower / cover_lower / cellCol_lower / tall_lower
parNone_lower / parCol_lower / valTop（valTop_exp）
step_orig_lower / step_push_lower
shapeRep_lower       **ShapeRep（k < K の枝）**
expandOut_lower      JS の出力 = 原文の復元値
expandJS_out_lower   JS の expand の枝そのもので書いた形
```

### 元からあるセルについての条件（済）

コピーで積んだセルとは別に、`cutChild` から残った列 `c < n−1` のセルについても
条件が要る。こちらは元の山の `ParRep` と `yamaContext_parent_orig`
（列 `c < x` では原文の親は元の山の親そのもの）から出る。

```
cell_orig_of_col_lt  列が n−1 より小さいセルは元からあるセルに限る
parNone_orig_yama    親を持たないなら原文の山でも根
parCol_orig_yama     親を持つならその添字が指すセルの列が原文の親
valTop_orig_yama     親を持たないセルの値は topValue base（その列）
```

`valTop_orig_yama` は「親を持たない ⇒ m = height（その列）」を経由する
（`m < height` なら `parent_exists_iff_lt_height` で親が存在してしまう）。
山崎噴火の枝の新しい対角は `expNd c = topValue base (source0 c)` で、
`c < n−1` では `source0 c = c` なのでこの値と一致する。

### `cover` と `cellCol`（済）

```
cover_yama         c < (n−1) + len*nrep で m ≤ height_G c なら段 m に列 c が載る
cutChild_cell_live 子を切ったあとに残るセルは元の山で生きていて列は n−1 未満
cellCol_yama       段 m にあるセルの列 c は m ≤ height_G c を満たす
```

`cell_fujiIters` で「元からあるセル」と「積んだセル」に分け、前者は
`cutChild_cell_live`、後者は `kmaxAt_expRes_eq`（`kmax = height j + 1`）で片付く。

この鎖を実際に繋いだ。

```
srcColY / srcColYama_eq  元の列を Setting と継ぎ目 y だけで書いた形
parentCopy_eq            parentCopy b p = p + (if y ≤ p then b*L else 0)
yamaContext_parent_src   原文の親 pc から 元の列とその親 q を取り出し
                           pc = q + (if y ≤ q then shifts*L else 0)
fujiCellAt_par_some_of_parent  原文に親があれば JS も親を持つ
fujiCellAt_parNone_yama  その対偶（= ShapeRep の parNone）
```

`yamaContext_parent_src` で 3 分岐が 1 つの式にまとまる。`level` 以上の枝で
桁上げが消えるのは、親 `q` が根 `y` より左で `if` の条件が偽になるからである。
その形は `parentPos_some` がそのまま要求する形になっている。

空段落としを通す運搬補題も揃えた。

```
take_len_cons / dropEmptyTop_length_le / rowAt_dropEmptyTop
lt_dropEmptyTop_length   空でない段は残る（ShapeRep の tall に要る）
getElem?_dropEmptyTop / hasCol_dropEmptyTop
rowsMono_dropEmptyTop / parLt_dropEmptyTop
```

### 値の埋め

`fillRow` は「直前までに積んだ結果を見ながら 1 つずつ積む折り畳み」である。この形を
`pushFold` として取り出し、次を示した（`Fill.lean`）。

```
pushFold_size    大きさは積んだ個数だけ増える
pushFold_prefix  既に積んだ要素は後から変わらない
pushFold_get     i 番目は「i 個目までを積んだ時点の配列」から決まる
```

これで `fillRow` の値の決まり方が書ける。親の添字はつねに自分より前なので、右辺の
「親の値」は途中の配列でも最終形でも同じである。

```
val(i) = if 元の値 ≠ 0 then 元の値
         else val(親) + （1 つ上の段の 列 pos−1 の値）
```

`fillValues` は上から下へこれを繰り返すので、最上段より下の段について同じ形になる
（`fillValues_val`）。`Recon.lean` の `value_of_diff` が

```
V r c = V r (行 r での c の親) + V (r+1) c ，V (height c) c = top c ，山の外は 0
```

を満たす `V` は `Reconstruction.value` に一致すると言うので、値の側はこれで閉じる。
残るのは、コピーで作った森が Phyrion の `expandedMountain` と同じ形であることと、
最上段の値が合っていることである。

### bad root が無いときの一致（証明済み）

`findBadRoot s hs (s.length−1) = none` のとき、両者は一致する（`expand_eq_no_bad`）。

```
expandOut (expandJS nrep mfuel (efuel+1) (calcMountain s (mf+1))) = expandValues s hs N
```

どちらも `s.take (s.length−1)` になる。JS 側は「行 0 の最後のセルを削る → 末尾の空段を
落とす → 値を埋める」だが、行 0 にはもう値が入っているので埋めは行 0 を変えない。
そのために次を示した。

```
pos_eq_index      行 0 の疎配列は密（位置 = 添字）
readPar_row0      行 0 では列で引いた親 = 疎配列の親
fillRow_id        値が入っている行は埋めで変わらない
dropEmptyTop_row0 末尾の空段を落としても行 0 は変わらない
row0Vals          行 0 の値の列は s そのもの
```

## 積み上げ

```
山の段      済（密表現・疎配列とも）
抽出段      済（密表現・疎配列とも）
bad root    済（getBadRoot = findBadRoot）
値の埋め    済（差分の関係 → Reconstruction.value）
分岐 none   済（expand_eq_no_bad）
三重ループ  済（構造・座標・出力の幅）
値の層      済（ShapeRep → expandOut_eq_value）
森のコピー  済
            k = K（山崎噴火）: shapeRep_yama / yamaContext_eq / expNd_eq_assemble
            k < K（badAtLowerContext）: shapeRep_lower / lowerContext_eq
層の再帰    済（expandOut_step_lower / expandOut_base_yama / expandOut_layers）
全体        済（expand_eq）
```

層の再帰は、bad root の層 `K` を底にして下向きに 1 段ずつ降りる。層 `k < K` では
JS の新しい対角が「`k+1` 段目以上の畳み込み」に一致し（`expandOut_step_lower`）、
層 `K` では山崎噴火の枝がその底になる（`expandOut_base_yama`）。

### 書き起こしの忠実さについて

`script.js` は Lean の対象ではないので、`Equiv/Yukito.lean` が原本の忠実な写しで
あることは証明の対象にできない。代わりに、原本を実行した出力と突き合わせて
`#guard` に固定してある（`Equiv/YukitoCheck.lean`）。`calcMountain` /
`calcDiagonal` / `getBadRoot` / `expand` の各段階と、分岐を一通り通す例を含む。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
