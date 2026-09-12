import Equiv.SibSucc
import Equiv.RootCase

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

/-- `select (frameAt s r) (towerVal s r)` の差分は次の層の値そのもの。 -/
theorem difference_eq_towerVal (s : List Nat) (r : Nat) :
    (select (frameAt s r) (towerVal s r)).difference = towerVal s (r + 1) := by
  cases r <;> rfl

/-- JS の `firstLiveAfter` は、`root + 1` が生きていればそこで止まる。 -/
theorem firstLiveAfter_eq_succ (base : Row) (r root fuel j : Nat)
    (hlive : 0 < (rows base (r + 1)).value (root + 1))
    (h : firstLiveAfter base r root fuel = some j) : j = root + 1 := by
  cases fuel with
  | zero => cases h
  | succ n =>
      rw [firstLiveAfter, if_pos hlive] at h
      exact (Option.some.inj h).symm

/-- **山の段の残る義務。** 要素がすべて正の列について `FirstLiveNotSmaller` が
成り立つ。すなわち JS の親探索が鎖の根に到達したとき、そこで `firstAtLeast` が
指す列は Lean 側で親に採られる列より値が小さくならない。 -/
theorem firstLiveNotSmaller_ofSequence (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    FirstLiveNotSmaller (ofSequence s) := by
  intro r c root j fuel hanc _hroot hreach hj
  -- 手順 1
  obtain ⟨p, hGp, hpc⟩ := child_toward (ParentForest.ancestor_of_zeroY hanc)
  have hGp' : restrictedParent (frameAt s r) (towerVal s r) p = some root := by
    rw [← frameAt_step]; exact hGp
  -- 手順 2
  have h2 : (rows (ofSequence s) (r + 1)).value c ≤
      (rows (ofSequence s) (r + 1)).value p := by
    rcases hpc with ha | heq
    · exact hreach p (ParentForest.ancestor_to_zeroY ha) ⟨root, hGp⟩
    · rw [heq]
      exact Nat.le_refl _
  -- 手順 3
  obtain ⟨z, hz⟩ : ∃ z, (frameAt s (r + 1)).parent (root + 1) = some z := by
    rcases hq : (frameAt s (r + 1)).parent (root + 1) with _ | z
    · exact absurd (by rw [frameAt_step] at hq; exact hq)
        (rootChildAdjacent_tower s hs r root p hGp')
    · exact ⟨z, rfl⟩
  have hlive : 0 < (rows (ofSequence s) (r + 1)).value (root + 1) :=
    (rows_parent_iff_next_live (ofSequence s) r (root + 1)).mp ⟨z, hz⟩
  -- 手順 4
  have hjeq : j = root + 1 := firstLiveAfter_eq_succ (ofSequence s) r root fuel j hlive hj
  subst hjeq
  -- 手順 5
  obtain ⟨hancF, hposR, _, _⟩ :=
    (restrictedParent_some_iff (frameAt s r) (towerVal s r) p root).mp hGp'
  obtain ⟨e, hFe, hep⟩ := child_toward (ParentForest.ancestor_of_zeroY hancF)
  -- 手順 6
  have hone : towerVal s r p ≤ towerVal s r (root + 1) :=
    one_of_nonancestor_tower s hs r hGp hFe
      (by rcases hep with h | h
          · exact Or.inl (ParentForest.ancestor_to_zeroY h)
          · exact Or.inr h)
  -- 手順 7
  have hA : ZeroY.Forest.Ancestor (frameAt s r).parent (root + 1) root :=
    Relation.TransGen.single (leftmost_child_all s hs r root e hFe)
  -- 手順 8
  have h8 := diff_le_of_a_and_one (F := frameAt s r) (U := towerVal s r)
    root p (root + 1) hGp' hA hposR
    (fun _ h1 h2 => absurd h2 (by omega))
    ⟨z, by rw [← frameAt_step]; exact hz⟩ hone
  rw [difference_eq_towerVal] at h8
  have h8' : (rows (ofSequence s) (r + 1)).value p ≤
      (rows (ofSequence s) (r + 1)).value (root + 1) := h8
  omega

end Yukito
