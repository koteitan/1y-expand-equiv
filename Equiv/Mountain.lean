import Equiv.SibSucc
import Equiv.RootCase
import OneY.NumericGeometry

/-!
# 山の段の組み上げ

`RootCase.lean` で立てた残る義務 `FirstLiveNotSmaller` を、揃った部品から
組み立てる。標準形の Y 数列（要素がすべて正の列）について成り立つ。

記号は次のとおり。行 `r` について

```
G = (rows base r).forest = frameAt s (r+1)   その行の森
F = frameAt s r                              frame（1 つ下の行の森、行 0 では線形森）
U = towerVal s r = (rows base r).value       frame の上の値
v = towerVal s (r+1) = (rows base (r+1)).value  次の行の値（= U の差分）
```

## 手順

```
1  root の G 子 p で c に至る道の上にあるものを取る（child_toward）
2  hreach から v c ≤ v p
3  root は G 子 p を持つので root+1 は生きている（rootChildAdjacent_tower）
4  したがって firstLiveAfter が返す j は root+1（firstLiveAfter_eq_succ）
5  root の F 子 e で p に至る道の上にあるものを取る
6  (1)  U p ≤ U (root+1)                     one_of_nonancestor_tower
7  (a)  root は root+1 の F 祖先              leftmost_child_all
8  v p ≤ v (root+1)                          diff_le_of_a_and_one
9  1 と 8 を繋いで v c ≤ v j
```

`hroot`（`root` がその行の森の根であること）は使わない。必要なのは `root` が
`G` 子を持つことだけである。
-/

namespace Yukito

open OneY OneY.Numeric

/-- Phyrion 版の山。 -/
def mountainOf (s : List Nat) (hs : ∀ x ∈ s, 0 < x) : RootGeometry.RowMountain :=
  mountain (ofSequence s) (ofSequence_positive s hs)

theorem mountainOf_height_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (c : Nat) :
    (mountainOf s hs).height c = height (ofSequence s) c := rfl

theorem mountainOf_rootAt_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (r c : Nat) :
    (mountainOf s hs).rootAt r c = (rows (ofSequence s) r).forest.root c := rfl

/-- 山の頂の高さは列番号以下。生きた列は 1 行ごとに右へずれるからである。 -/
theorem height_le_self' (base : Row) (hpos : ∀ c, 0 < base.value c) (c : Nat) :
    height base c ≤ c := by
  rcases Nat.lt_or_ge c (height base c) with h | h
  · have hl := height_live base (hpos c)
    rw [rows_value_zero_of_lt base _ c h] at hl
    omega
  · exact h

theorem height_le_self (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (c : Nat) :
    height (ofSequence s) c ≤ c :=
  height_le_self' (ofSequence s) (ofSequence_positive s hs) c

/-- `select (frameAt s r) (towerVal s r)` の差分は次の層の値そのもの。 -/
theorem difference_eq_towerVal (T : Tower) (r : Nat) :
    (select (frameAt T r) (towerVal T r)).difference = towerVal T (r + 1) := by
  funext c
  cases r with
  | zero =>
      show (match restrictedParent T.frame0 T.base.value c with
            | none => 0
            | some p => T.base.value c - T.base.value p) = _
      rw [← T.hbase c]
      rfl
  | succ k => rfl

/-- JS の `firstLiveAfter` は、`root + 1` が生きていればそこで止まる。 -/
theorem firstLiveAfter_eq_succ (base : Row) (r root fuel j : Nat)
    (hlive : 0 < (rows base (r + 1)).value (root + 1))
    (h : firstLiveAfter base r root fuel = some j) : j = root + 1 := by
  cases fuel with
  | zero => cases h
  | succ n =>
      rw [firstLiveAfter, if_pos hlive] at h
      exact (Option.some.inj h).symm

/-- **鎖の根での段。** 歩行が根に到達したなら、`root + 1` は生きていて、その値は
`c` の値以上である。JS が根の所で `firstAtLeast` に指される列がこれである。 -/
theorem root_step_le (T : Tower) (r c root : Nat)
    (hanc : ZeroY.Forest.Ancestor (rows T.base r).forest.parent c root)
    (hreach : ∀ q, ZeroY.Forest.Ancestor (rows T.base r).forest.parent c q →
      (∃ t, (rows T.base r).forest.parent q = some t) →
      (rows T.base (r + 1)).value c ≤ (rows T.base (r + 1)).value q) :
    0 < (rows T.base (r + 1)).value (root + 1) ∧
      (rows T.base (r + 1)).value c ≤
        (rows T.base (r + 1)).value (root + 1) := by
  -- 手順 1
  obtain ⟨p, hGp, hpc⟩ := child_toward (ParentForest.ancestor_of_zeroY hanc)
  have hGp' : restrictedParent (frameAt T r) (towerVal T r) p = some root := by
    rw [← frameAt_step]; exact hGp
  -- 手順 2
  have h2 : (rows T.base (r + 1)).value c ≤
      (rows T.base (r + 1)).value p := by
    rcases hpc with ha | heq
    · exact hreach p (ParentForest.ancestor_to_zeroY ha) ⟨root, hGp⟩
    · rw [heq]
      exact Nat.le_refl _
  -- 手順 3
  obtain ⟨z, hz⟩ : ∃ z, (frameAt T (r + 1)).parent (root + 1) = some z := by
    rcases hq : (frameAt T (r + 1)).parent (root + 1) with _ | z
    · exact absurd (by rw [frameAt_step] at hq; exact hq)
        (rootChildAdjacent_tower T r root p hGp')
    · exact ⟨z, rfl⟩
  have hlive : 0 < (rows T.base (r + 1)).value (root + 1) :=
    (rows_parent_iff_next_live T.base r (root + 1)).mp ⟨z, hz⟩
  -- 手順 5
  obtain ⟨hancF, hposR, _, _⟩ :=
    (restrictedParent_some_iff (frameAt T r) (towerVal T r) p root).mp hGp'
  obtain ⟨e, hFe, hep⟩ := child_toward (ParentForest.ancestor_of_zeroY hancF)
  -- 手順 6
  have hone : towerVal T r p ≤ towerVal T r (root + 1) :=
    one_of_nonancestor_tower T r hGp hFe
      (by rcases hep with h | h
          · exact Or.inl (ParentForest.ancestor_to_zeroY h)
          · exact Or.inr h)
  -- 手順 7
  have hA : ZeroY.Forest.Ancestor (frameAt T r).parent (root + 1) root :=
    Relation.TransGen.single (leftmost_child_all T r root e hFe)
  -- 手順 8
  have h8 := diff_le_of_a_and_one (F := frameAt T r) (U := towerVal T r)
    root p (root + 1) hGp' hA hposR
    (fun _ h1 h2 => absurd h2 (by omega))
    ⟨z, by rw [← frameAt_step]; exact hz⟩ hone
  rw [difference_eq_towerVal] at h8
  have h8' : (rows T.base (r + 1)).value p ≤
      (rows T.base (r + 1)).value (root + 1) := h8
  exact ⟨hlive, by omega⟩

/-- **山の段の残る義務。** 要素がすべて正の列について `FirstLiveNotSmaller` が
成り立つ。すなわち JS の親探索が鎖の根に到達したとき、そこで `firstAtLeast` が
指す列は Lean 側で親に採られる列より値が小さくならない。 -/
theorem firstLiveNotSmaller_tower (T : Tower) : FirstLiveNotSmaller T.base := by
  intro r c root j fuel hanc _hroot hreach hj
  obtain ⟨hlive, hle⟩ := root_step_le T r c root hanc hreach
  have hjeq : j = root + 1 := firstLiveAfter_eq_succ T.base r root fuel j hlive hj
  subst hjeq
  exact hle

/-- 入力列から作る塔での特殊化。 -/
theorem root_step_le_seq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (r c root : Nat)
    (hanc : ZeroY.Forest.Ancestor (rows (ofSequence s) r).forest.parent c root)
    (hreach : ∀ q, ZeroY.Forest.Ancestor (rows (ofSequence s) r).forest.parent c q →
      (∃ t, (rows (ofSequence s) r).forest.parent q = some t) →
      (rows (ofSequence s) (r + 1)).value c ≤ (rows (ofSequence s) (r + 1)).value q) :
    0 < (rows (ofSequence s) (r + 1)).value (root + 1) ∧
      (rows (ofSequence s) (r + 1)).value c ≤
        (rows (ofSequence s) (r + 1)).value (root + 1) :=
  root_step_le (linearTower s hs) r c root hanc hreach

theorem firstLiveNotSmaller_ofSequence (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    FirstLiveNotSmaller (ofSequence s) :=
  firstLiveNotSmaller_tower (linearTower s hs)

end Yukito
