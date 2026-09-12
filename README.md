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
これにあたる。残るのは `root + 1 < e` の場合である。

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

山の段が済んでも、抽出・bad root・コピー層が残る。コピー層が全体の大半である。

## ビルド

Lean 4.33.1 が要る。依存として Phyrion 版の形式化を兄弟ディレクトリに置く。

```sh
git clone https://github.com/Phyrion1343/1Y-Well-Ordering-Lean
git clone git@github.com:koteitan/1y-expand-equiv
cd 1y-expand-equiv
lake --keep-toolchain --no-cache build Equiv
```

`lakefile.toml` は依存を `../1Y-Well-Ordering-Lean/formalization` として参照する。
