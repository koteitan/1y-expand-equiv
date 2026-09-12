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

end Yukito
