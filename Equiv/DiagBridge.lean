import Equiv.Lift
import Equiv.Extract

/-!
# 抽出段の疎配列との橋渡し

`calcDiagonal` の書き起こし（`Yukito.lean`）が、密表現側の `rawExtract` に一致する
ことを示す。山の段で作った `Rep` / `ParRep` / `firstAtLeast` をそのまま使う。

まず頂の探索から。JS は段を上から下へ走らせて、列 `i` を含む最上段を探す。密表現側
でそれにあたるのが Phyrion の `height` である。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 山の各行が対応していること。`calcMountain_rep` がこれを与える。 -/
def MountainRep (M : List Rowj) (s : List Nat) : Prop :=
  ∀ r, ∀ hr : r < M.length,
    Rep (M[r]'hr) r s.length (rows (ofSequence s) r).value ∧
      ParRep (M[r]'hr) r (rows (ofSequence s) r).forest

theorem mountainRep_calcMountain (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat) :
    MountainRep (calcMountain s (fuel + 1)) s :=
  fun r hr => calcMountain_rep s hs fuel r hr

/-- 列 `i` が行 `r` にあることと、`r ≤ height i` は同値。 -/
theorem col_live_iff (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (i : Nat) (hi : i < s.length)
    (r : Nat) : 0 < (rows (ofSequence s) r).value i ↔ r ≤ height (ofSequence s) i :=
  live_iff_le_height (ofSequence s) (ofSequence_positive s hs i) r

/-- 範囲内なら `rowAt` はその行。 -/
theorem rowAt_eq (M : List Rowj) (j : Nat) (hj : j < M.length) : rowAt M j = M[j]'hj :=
  (List.getElem_eq_getD #[]).symm

/-- 範囲外なら `rowAt` は空行。 -/
theorem rowAt_of_ge (M : List Rowj) (j : Nat) (hj : M.length ≤ j) : rowAt M j = #[] := by
  simp [rowAt, List.getD, List.getElem?_eq_none hj]

/-- **頂の探索。** 段が足りていれば、`topAt` は `height i` の段とその添字を返す。 -/
theorem topAt_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (M : List Rowj)
    (hM : MountainRep M s) (i : Nat) (hi : i < s.length) :
    ∀ L, L ≤ M.length → height (ofSequence s) i < L →
      ∃ k, ∃ hk : k < (rowAt M (height (ofSequence s) i)).size,
        ((rowAt M (height (ofSequence s) i))[k]'hk).pos + height (ofSequence s) i = i ∧
          topAt M i L = some (height (ofSequence s) i, k) := by
  intro L
  induction L with
  | zero => intro _ h; omega
  | succ j ih =>
    intro hjM hij
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with heq | hlt
    · rw [heq]
      have hj : j < M.length := by omega
      have hrowj : rowAt M j = M[j]'hj := rowAt_eq M j hj
      obtain ⟨hrep, _⟩ := hM j hj
      have hlive : 0 < (rows (ofSequence s) j).value i :=
        (col_live_iff s hs i hi j).mpr (by omega)
      have hji : j ≤ i := by
        rcases Nat.lt_or_ge i j with h | h
        · rw [rows_value_zero_of_lt (ofSequence s) j i h] at hlive; omega
        · exact h
      rw [hrowj]
      obtain ⟨k, hk, hck, hfa⟩ :=
        rep_lookup (M[j]'hj) j s.length _ hrep i hji hi hlive
      refine ⟨k, hk, hck, ?_⟩
      rw [topAt, hrowj]
      simp only [hfa, dif_pos hk, if_pos hck]
    · have hstep : topAt M i (j + 1) = topAt M i j := by
        rw [topAt]
        rcases Nat.lt_or_ge j M.length with hjlen | hjlen
        · have hrowj : rowAt M j = M[j]'hjlen := rowAt_eq M j hjlen
          obtain ⟨hrep, _⟩ := hM j hjlen
          have hdead : (rows (ofSequence s) j).value i = 0 := by
            rcases Nat.eq_zero_or_pos ((rows (ofSequence s) j).value i) with h | h
            · exact h
            · exact absurd ((col_live_iff s hs i hi j).mp h) (by omega)
          rw [hrowj]
          split
          · rename_i hk
            have hne :
                ((M[j]'hjlen)[firstAtLeast (M[j]'hjlen) (i - j)]'hk).pos + j ≠ i := by
              intro he
              have h1 := hrep.val _ (mem_of_getElem _ _ hk)
              have h2 := hrep.live _ (mem_of_getElem _ _ hk)
              rw [he, hdead] at h1
              omega
            rw [if_neg hne]
          · rfl
        · rw [rowAt_of_ge M j hjlen]
          simp
      rw [hstep]
      exact ih (by omega) hlt

/-- 頂の段の `Rep`。 -/
theorem rep_top (s : List Nat) (M : List Rowj) (hM : MountainRep M s)
    (H : Nat) (hH : H < M.length) :
    Rep (rowAt M H) H s.length (rows (ofSequence s) H).value := by
  rw [rowAt_eq M H hH]
  exact (hM H hH).1

/-- **対角の値は頂の値。** JS が `diagonal` に積む値は Phyrion の `topValue` である。 -/
theorem diagEntry_value (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (M : List Rowj)
    (hM : MountainRep M s) (i : Nat) (hi : i < s.length)
    (hlen : height (ofSequence s) i < M.length) :
    ∃ p, diagEntry M i = some (topValue (ofSequence s) i, p) := by
  obtain ⟨k, hk, hck, htop⟩ := topAt_eq s hs M hM i hi M.length (Nat.le_refl _) hlen
  have hrep := rep_top s M hM (height (ofSequence s) i) hlen
  have hval : ((rowAt M (height (ofSequence s) i))[k]'hk).val
      = topValue (ofSequence s) i := by
    have h := hrep.val _ (mem_of_getElem _ k hk)
    rw [hck] at h
    exact h
  refine ⟨legWalkJS M (i + 1) (height (ofSequence s) i) k, ?_⟩
  rw [diagEntry, htop]
  simp only [dif_pos hk, hval]

end Yukito
