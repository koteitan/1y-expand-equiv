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

/-- `F` 祖先を持つ列は `F` 親を持つ。 -/
theorem ancestor_parent_exists {a c : Nat}
    (h : ZeroY.Forest.Ancestor F.parent c a) : ∃ z, F.parent c = some z := by
  induction h with
  | single hp => exact ⟨_, hp⟩
  | tail _ _ ih => exact ih

/-- `F` 親は最も右の `F` 祖先。 -/
theorem ancestor_le_parent {j w a : Nat}
    (hp : F.parent j = some w) (ha : ZeroY.Forest.Ancestor F.parent j a) : a ≤ w := by
  induction ha with
  | single h =>
      have : some w = some _ := hp.symm.trans h
      exact Nat.le_of_eq (Option.some.inj this).symm
  | @tail b a _ h2 ih =>
      have hab : a < b := F.parent_left h2
      omega

/-- 値と frame の対応。山では「行 `r` の値が正」と「行 `r-1` で親を持つ」が同値。 -/
def Compat (F : ParentForest) (U : Nat → Nat) : Prop :=
  ∀ q, 0 < U q ↔ ∃ z, F.parent q = some z

/-- 中心の矛盾。`root` より右で `j` より左にある死んだ列は、`j` の `F` 祖先に
なれない。 -/
theorem no_dead_ancestor (hc : Compat F U) {root j w : Nat}
    (hj : restrictedParent F U j = some root)
    (hw : ZeroY.Forest.Ancestor F.parent j w)
    (hlt : root < w)
    (hdead : restrictedParent F U w = none) : False := by
  obtain ⟨hanc, hUroot, hUj, hmax⟩ := (restrictedParent_some_iff F U j root).mp hj
  -- root は w の F 祖先
  have hrw : ZeroY.Forest.Ancestor F.parent w root :=
    anc_of_common j root w hanc hw hlt
  -- w は F 親を持つので U w > 0
  have hUw : 0 < U w := (hc w).mpr (ancestor_parent_exists hrw)
  -- w が死んでいるので U w ≤ U root
  have h1 : U w ≤ U root :=
    (restrictedParent_none_iff F U w).mp hdead root
      (ParentForest.ancestor_of_zeroY hrw) hUroot
  -- 最大性から U j ≤ U w
  have h2 : U j ≤ U w := by
    rcases Nat.lt_or_ge (U w) (U j) with hlt' | hge
    · have := hmax w hw hUw hlt'
      omega
    · exact hge
  omega

/-- `root` と `j` の間がすべて死んでいるなら、`j` の `F` 親は `root` である。 -/
theorem fparent_eq_root (hc : Compat F U) {root j : Nat}
    (hj : restrictedParent F U j = some root)
    (hdead : ∀ q, root < q → q < j → restrictedParent F U q = none) :
    F.parent j = some root := by
  obtain ⟨hanc, _, _, _⟩ := (restrictedParent_some_iff F U j root).mp hj
  -- j は F 親を持つ（root が F 祖先だから）
  obtain ⟨w, hp⟩ := ancestor_parent_exists hanc
  rw [hp]
  congr 1
  ·
      -- root ≤ w。root は j の F 鎖の上にあり、w はその先頭だから。
    have hwj : w < j := F.parent_left hp
    have hwanc : ZeroY.Forest.Ancestor F.parent j w := Relation.TransGen.single hp
    have hle : root ≤ w := ancestor_le_parent hp hanc
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · exact heq.symm
    · exact absurd (no_dead_ancestor hc hj hwanc hlt (hdead w hlt hwj)) (fun h => h)

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

/-- 行 `r` に当てはめた形。 -/
theorem succ_sibling_descent (base : Row) (r : Nat) {t q1 q2 : Nat}
    (h1 : (rows base r).forest.parent q1 = some t)
    (h2 : (rows base r).forest.parent q2 = some t) :
    (rows base (r+1)).value q2 ≤ (rows base (r+1)).value q1 ↔
      (rows base r).value q2 ≤ (rows base r).value q1 :=
  sibling_descent (rows base r) h1 h2

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

/-- 上が成り立てば、`root` より右で最初に生きている列は `root + 1` である。 -/
theorem firstLive_eq_succ (hadj : RootChildAdjacent F U) {root p j : Nat}
    (hp : restrictedParent F U p = some root)
    (_hjlive : restrictedParent F U j ≠ none)
    (hjr : root < j)
    (hfirst : ∀ q, root < q → q < j → restrictedParent F U q = none) :
    j = root + 1 := by
  rcases Nat.eq_or_lt_of_le hjr with heq | hlt
  · omega
  · exact absurd (hfirst (root + 1) (by omega) (by omega)) (hadj root p hp)

/-- `j = root + 1` のときは「間の列が死んでいる」という仮定が自明に満たされる。
したがって `F` 親が `root` であることが仮定なしで出る。 -/
theorem fparent_succ (hc : Compat F U) {root : Nat}
    (hj : restrictedParent F U (root + 1) = some root) :
    F.parent (root + 1) = some root :=
  fparent_eq_root hc hj (fun _ h1 h2 => absurd h2 (by omega))

/-- `e` を `root` の `F` 子とすると、`root + 1 ≤ e` である。 -/
theorem succ_le_child {root e : Nat} (he : F.parent e = some root) : root + 1 ≤ e := by
  have := F.parent_left he
  omega

/-- 非祖先の場合、すなわち `j = root + 1` が `e` と異なるときは `j < e` である。 -/
theorem succ_lt_child {root e : Nat} (he : F.parent e = some root)
    (hne : root + 1 ≠ e) : root + 1 < e := by
  have := succ_le_child he
  omega

/-- 場合 1 の形。`j = root + 1` が `e` の `F'` 祖先なら、一段下の最大性で
`U e ≤ U j` が出る。ここで `F'` は `F` の frame、`U'` はその上の値である。 -/
theorem one_of_lower_ancestor {F' : ParentForest} {U' : Nat → Nat} {root e : Nat}
    (hF : F.parent = restrictedParent F' U')
    (he : F.parent e = some root)
    (hanc : ZeroY.Forest.Ancestor F'.parent e (root + 1))
    (hpos : 0 < U' (root + 1)) : U' e ≤ U' (root + 1) := by
  have he' : restrictedParent F' U' e = some root := by rw [← hF]; exact he
  exact one_of_ancestor root e (root + 1) he' hanc (by omega) hpos

/-! ## 層をまたぐ連鎖

`fparent_succ` は仮定 `restrictedParent F U (root+1) = some root` から
結論 `F.parent (root+1) = some root` を出す。山では

```
restrictedParent (rows base k).forest (rows base (k+1)).value
  = (rows base (k+1)).forest.parent
```

なので、結論がそのまま一段下の仮定になる。したがって連鎖する。
`Compat` は `rows_parent_iff_next_live` がそのまま与えるので仮定も要らない。 -/

/-- 山では値と frame の対応が成り立つ。 -/
theorem compat_rows (base : Row) (k : Nat) :
    Compat (rows base k).forest (rows base (k+1)).value := by
  intro q
  exact (rows_parent_iff_next_live base k q).symm

/-- 1 段の連鎖。 -/
theorem fparent_succ_step (base : Row) (k root : Nat)
    (h : (rows base (k+1)).forest.parent (root + 1) = some root) :
    (rows base k).forest.parent (root + 1) = some root :=
  fparent_succ (compat_rows base k) h

/-- 連鎖を下まで回した形。行 `k + m` で成り立てば行 `k` でも成り立つ。 -/
theorem fparent_succ_down (base : Row) (root : Nat) :
    ∀ m k, (rows base (k + m)).forest.parent (root + 1) = some root →
      (rows base k).forest.parent (root + 1) = some root
  | 0, _, h => h
  | m+1, k, h => by
      have h' : (rows base ((k+1) + m)).forest.parent (root + 1) = some root := by
        have : (k+1) + m = k + (m+1) := by omega
        rw [this]; exact h
      exact fparent_succ_step base k root (fparent_succ_down base root m (k+1) h')

/-- `F` 親が `root` なら、その層で `U root < U (root+1)` が成り立つ。
`Row.parent_values` がそのまま与える。 -/
theorem value_lt_of_fparent (base : Row) (k root : Nat)
    (hp : (rows base k).forest.parent (root + 1) = some root) :
    0 < (rows base k).value root ∧
      (rows base k).value root < (rows base k).value (root + 1) :=
  (rows base k).parent_values hp

/-- 連鎖と合わせた形。行 `k+m` で `j = root+1` の親が `root` なら、
行 `k` でも値の大小が成り立つ。 -/
theorem value_lt_down (base : Row) (root : Nat) (m k : Nat)
    (h : (rows base (k + m)).forest.parent (root + 1) = some root) :
    (rows base k).value root < (rows base k).value (root + 1) :=
  (value_lt_of_fparent base k root (fparent_succ_down base root m k h)).2

/-- `root` が下の層で生きていることも同時に出る。 -/
theorem root_pos_down (base : Row) (root : Nat) (m k : Nat)
    (h : (rows base (k + m)).forest.parent (root + 1) = some root) :
    0 < (rows base k).value root :=
  (value_lt_of_fparent base k root (fparent_succ_down base root m k h)).1

/-! ## `RootChildAdjacent` のうち片付く場合

`e` を `root` の `F` 子で `p` の鎖にあるものとすると `root + 1 ≤ e` である。
`root + 1 = e` のときは最大性で閉じる。`e` は `p` の `F` 祖先（または `p` 自身）
なので `U p ≤ U e`、`root = Φ.parent p` から `U root < U p`、あわせて
`U root < U (root + 1)` となり、`root` が `root + 1` の親候補になる。 -/

/-- `root + 1` が `p` の `F` 祖先（または `p` 自身）で、その `F` 親が `root` なら、
`root + 1` は生きている。 -/
theorem rootChildAdjacent_of_ancestor (hc : Compat F U) {root p : Nat}
    (hp : restrictedParent F U p = some root)
    (hf : F.parent (root + 1) = some root)
    (hep : ZeroY.Forest.Ancestor F.parent p (root + 1) ∨ root + 1 = p) :
    restrictedParent F U (root + 1) ≠ none := by
  have hpos : 0 < U (root + 1) := (hc (root + 1)).mpr ⟨root, hf⟩
  obtain ⟨_, hUroot, hUp, _⟩ := (restrictedParent_some_iff F U p root).mp hp
  -- U p ≤ U (root+1)
  have hle : U p ≤ U (root + 1) := by
    rcases hep with hanc | heq
    · exact one_of_ancestor root p (root + 1) hp hanc (by omega) hpos
    · subst heq; exact Nat.le_refl _
  intro hnone
  have := (restrictedParent_none_iff F U (root + 1)).mp hnone root
    (ParentForest.ancestor_of_zeroY (Relation.TransGen.single hf)) hUroot
  omega

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

/-- 非祖先の場合の (1)。兄弟の単調性を仮定として受け取り、`U p ≤ U j` を出す。 -/
theorem one_of_nonancestor (hc : Compat F U) {root p j e : Nat}
    (hp : restrictedParent F U p = some root)
    (he : F.parent e = some root)
    (hanc : ZeroY.Forest.Ancestor F.parent p e ∨ e = p)
    (hsib : U e ≤ U j) : U p ≤ U j :=
  one_of_nonancestor' hp he hanc ((hc e).mpr ⟨root, he⟩) hsib

/-- `j` と `e` が `F` 兄弟であること。`j` 側は `fparent_eq_root` から出る。 -/
theorem j_e_siblings (hc : Compat F U) {root j e : Nat}
    (hj : restrictedParent F U j = some root)
    (hdead : ∀ q, root < q → q < j → restrictedParent F U q = none)
    (he : F.parent e = some root) :
    F.parent j = some root ∧ F.parent e = some root :=
  ⟨fparent_eq_root hc hj hdead, he⟩

end Yukito
