import Equiv.Row0Spec
import Equiv.RootCase

/-!
# `FirstLiveNotSmaller` の行 0 の場合

記号を固定する。`V` を行 0 の値、`F` を行 0 の森（左で最も近い小さい列）、
`w q` を行 1 の値、すなわち `w q = V q - V (F.parent q)`（親が無ければ 0）とする。

`root` を `c` の鎖の根、`j` を `root` より右で最初に「行 1 で生きている」列とする。
`p` を鎖で `root` の 1 つ手前の要素（`F.parent p = root`）とする。

証明の筋は次のとおり。

1. `F.parent p = root` から `V root < V p`
2. `root` は根なので、`root` より左の列 `t` は `V root ≤ V t`
3. `(root, j)` の列はすべて根なので、`V q ≤ V root`
4. `F.parent p = root` の最大性から、`root < t < p` なら `V p ≤ V t`。とくに `V p ≤ V j`
5. 1 と 4 から `V root < V j`。よって `F.parent j` は `root` 以上の位置にある
6. 5 と 3 から `V (F.parent j) ≤ V root`
7. `w j = V j - V (F.parent j) ≥ V j - V root ≥ V p - V root = w p`
-/

namespace Yukito

open OneY OneY.Numeric

variable {V : Nat → Nat}

/-- 行 1 の値。親が無ければ 0。 -/
def w (V : Nat → Nat) (q : Nat) : Nat :=
  match restrictedParent linearForest V q with
  | none => 0
  | some t => V q - V t

theorem w_pos_iff (hv : ∀ p, 0 < V p) (q : Nat) :
    0 < w V q ↔ ∃ t, restrictedParent linearForest V q = some t := by
  unfold w
  cases ht : restrictedParent linearForest V q with
  | none => simp
  | some t =>
      obtain ⟨_, hlt, _⟩ := (parent0_some_iff hv q t).mp ht
      dsimp only
      constructor
      · intro _; exact ⟨t, rfl⟩
      · intro _; omega

/-- 手順 4。`F.parent p = root` の最大性から、間の列の値は `V p` 以上。 -/
theorem between_ge (hv : ∀ p, 0 < V p) {p root t : Nat}
    (hp : restrictedParent linearForest V p = some root)
    (h1 : root < t) (h2 : t < p) : V p ≤ V t := by
  obtain ⟨_, _, hmax⟩ := (parent0_some_iff hv p root).mp hp
  rcases Nat.lt_or_ge (V t) (V p) with hlt | hge
  · have hle := hmax t h2 hlt
    omega
  · exact hge

/-- 手順 3。`(root, j)` の列が根なら、その値は `V root` 以下。 -/
theorem dead_le_root (hv : ∀ p, 0 < V p) {root q : Nat}
    (hq : restrictedParent linearForest V q = none) (hlt : root < q) :
    V q ≤ V root := root0_le hv hq hlt

/-- 手順 6。`V root < V j` なら `j` の親の値は `V root` 以下。
`root` 自身が候補になるので親は `root` 以上の位置にあり、
`(root, j)` の列は根なので値が `V root` 以下だからである。 -/
theorem parent_val_le_root (hv : ∀ p, 0 < V p) {root j t : Nat}
    (_hroot : restrictedParent linearForest V root = none)
    (hlt : root < j) (hV : V root < V j)
    (hdead : ∀ q, root < q → q < j → restrictedParent linearForest V q = none)
    (ht : restrictedParent linearForest V j = some t) : V t ≤ V root := by
  have hs := (parent0_some_iff hv j t).mp ht
  -- root は候補なので t は root 以上
  have hge : root ≤ t := hs.2.2 root (by omega) hV
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · subst heq
    exact Nat.le_refl _
  · -- root < t < j なら t は死んでいるので V t ≤ V root
    exact dead_le_root hv (hdead t hgt hs.1) hgt

/-- 行 0 の `FirstLiveNotSmaller`。

`p` は鎖で `root` の 1 つ手前（`F.parent p = root`）、`j` は `root` より右で
最初に行 1 で生きている列。仮定 `hreach` は「歩行が根に到達した」ことを表し、
とくに `w p` について `w c ≤ w p` を与える。 -/
theorem firstLive_not_smaller_zero (hv : ∀ q, 0 < V q)
    {c p root j : Nat}
    (hp : restrictedParent linearForest V p = some root)
    (hpc : w V c ≤ w V p)
    (hroot : restrictedParent linearForest V root = none)
    (hpj : j ≤ p)
    (hrj : root < j)
    (hdead : ∀ q, root < q → q < j → restrictedParent linearForest V q = none)
    (hjlive : 0 < w V j) :
    w V c ≤ w V j := by
  -- 手順 1
  obtain ⟨_, hVroot, _⟩ := (parent0_some_iff hv p root).mp hp
  -- 手順 4: V p ≤ V j
  have hVpj : V p ≤ V j := by
    rcases Nat.eq_or_lt_of_le hpj with heq | hlt
    · subst heq; exact Nat.le_refl _
    · exact between_ge hv hp hrj hlt
  -- 手順 5
  have hVrj : V root < V j := by omega
  -- j の親を取り出す
  obtain ⟨t, ht⟩ := (w_pos_iff hv j).mp hjlive
  -- 手順 6
  have hVt : V t ≤ V root := parent_val_le_root hv hroot hrj hVrj hdead ht
  -- 手順 7
  have hwj : w V j = V j - V t := by unfold w; rw [ht]
  have hwp : w V p = V p - V root := by unfold w; rw [hp]
  omega

end Yukito
