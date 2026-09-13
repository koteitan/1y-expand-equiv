import Equiv.RootGen

/-!
# 「最初に生きている列」から出ること

一般化した主張はことごとく偽だった（`Sibling.lean` を参照）。真なのは
`j` が「`root` より右で最初に生きている列」であるという条件を保った形だけである。
本ファイルはその条件を直接使って何が出るかを示す。

記号は `RootGen.lean` と同じ。`F` が frame、`U` がその上の値、
`Φ = restrictedParent F U` がその行の森である。「`q` が生きている」は
`Φ.parent q ≠ none` を指す。値との対応 `0 < U q ↔ F.parent q ≠ none` は
仮定として渡す（山では前の行の差分がこれを与える）。

## 中心になる型

`root` より右で `j` より左の列はすべて死んでいる。そのような列 `w` が
`j` の `F` 祖先でもあると仮定すると、次の 2 つが同時に成り立つ。

* `w` は死んでいるので、その `F` 祖先である `root` について `U w ≤ U root`
* `w` は `root` より右の `F` 祖先なので、最大性から `U j ≤ U w`

ところが `Φ.parent j = root` は `U root < U j` を要求するので

```
U root < U j ≤ U w ≤ U root
```

となって矛盾する。この型が以下すべてに効く。
-/

namespace Yukito

open OneY OneY.Numeric

variable {F : ParentForest} {U : Nat → Nat}

/-! ## 残る 1 本と、その再帰構造

`fparent_eq_root` により `j` の `F` 親は `root` である。`e` を `root` の `F` 子で
`p` の鎖にあるものとすると、`j` と `e` は `F` 兄弟になる。`U e ≥ U p` は最大性から
出るので、残るのは

```
F 兄弟 q1 < q2 で q1 が生きているなら U q1 ≥ U q2
```

だけである。左の兄弟が生きているという条件は外せない（外した形は偽。
列 `(1,2,4,8,11,8)` の行 2 が反例）。

これは層を降りる再帰で片付く見込みである。各層で次の 3 つのいずれかになる。

1. `q1` が `q2` の祖先 → その層の最大性で `U q1 ≥ U q2`。完了
2. `q1` と `q2` が兄弟 → 下の `sibling_descent` で一段下の同じ問題に移る
3. どちらでもない → 合流点 `m` を取る。`m` の直上の両側の要素 `u`, `z` のうち
   `u = q1` となり、`q2` を `z` に置き換えて続ける

値 12 までの探索では 69,364 件すべてがこの再帰で尽き、未処理は 0 件だった。
降りる段数は 1 段が 68,560 件、2 段が 804 件。3 の合流点は 5 件で、
いずれも `u = q1` である。以前つまずいた `u < q1` は 1 度も起きなかった。

基底は行 0 で、frame が線形なので `q1 < q2` なら必ず 1 の場合になる。 -/

/-- 降下段。兄弟なら、差分の大小は元の値の大小と一致する。 -/
theorem sibling_descent (a : Row) {t q1 q2 : Nat}
    (h1 : a.forest.parent q1 = some t) (h2 : a.forest.parent q2 = some t) :
    a.difference q2 ≤ a.difference q1 ↔ a.value q2 ≤ a.value q1 := by
  have hv1 := a.parent_values h1
  have hv2 := a.parent_values h2
  simp only [Row.difference, h1, h2]
  omega

/-! ## `j` は `root` の右隣である

実測で次が分かった。**`root` が `Φ` の子を持つなら `root + 1` は生きている。**
値 10 まで全数 111,110 列、215,290 件で反例なし。

子を持つという条件は外せない。列 `(1,1,1,1,1,2)` の行 0 では `root = 0` が
`Φ` 根で右に生きた列があるが `root + 1 = 1` は死んでいる。ただしこの `0` は
どの列の鎖の根にもならない。実際の根は `4` で、そこでは `4 + 1 = 5` が生きている。

実際の配置では `root` は必ず `Φ` の子 `p` を持つ。したがって `j`、すなわち
`root` より右で最初に生きている列は、`root + 1` そのものになる。

これは大きな簡約である。`root` と `j` の間に列が無いので、これまで使ってきた
「間の列はすべて死んでいる」という仮定が自明になる。 -/

/-- `root` が `Φ` の子を持つなら、その右隣は生きている。 -/
def RootChildAdjacent (F : ParentForest) (U : Nat → Nat) : Prop :=
  ∀ root p, restrictedParent F U p = some root →
    restrictedParent F U (root + 1) ≠ none

/-! ## 層をまたぐ連鎖

`fparent_succ` は仮定 `restrictedParent F U (root+1) = some root` から
結論 `F.parent (root+1) = some root` を出す。山では

```
restrictedParent (rows base k).forest (rows base (k+1)).value
  = (rows base (k+1)).forest.parent
```

なので、結論がそのまま一段下の仮定になる。したがって連鎖する。
`Compat` は `rows_parent_iff_next_live` がそのまま与えるので仮定も要らない。 -/

/-! ## `RootChildAdjacent` のうち片付く場合

`e` を `root` の `F` 子で `p` の鎖にあるものとすると `root + 1 ≤ e` である。
`root + 1 = e` のときは最大性で閉じる。`e` は `p` の `F` 祖先（または `p` 自身）
なので `U p ≤ U e`、`root = Φ.parent p` から `U root < U p`、あわせて
`U root < U (root + 1)` となり、`root` が `root + 1` の親候補になる。 -/

/-! ## 非祖先の場合の組み上げ

`fparent_eq_root` により `F.parent j = root`、`e` の定義から `F.parent e = root`
なので、`j` と `e` は `F` 兄弟である。`e` は `p` の `F` 祖先（または `p` 自身）
なので最大性から `U p ≤ U e`。したがって残る義務は `U e ≤ U j` の 1 本だけになる。 -/

/-- 非祖先の場合の (1)。`Compat` を使わず `0 < U e` を直接受け取る形。
層 0 では `Compat` が成り立たない（`U 0 > 0` だが線形森で `0` は親を持たない）ので、
こちらを基本形にする。 -/
theorem one_of_nonancestor' {root p j e : Nat}
    (hp : restrictedParent F U p = some root)
    (he : F.parent e = some root)
    (hanc : ZeroY.Forest.Ancestor F.parent p e ∨ e = p)
    (hpos : 0 < U e)
    (hsib : U e ≤ U j) : U p ≤ U j := by
  have hre : root < e := F.parent_left he
  have h1 : U p ≤ U e := by
    rcases hanc with ha | heq
    · exact one_of_ancestor root p e hp ha hre hpos
    · subst heq; exact Nat.le_refl _
  omega

end Yukito
