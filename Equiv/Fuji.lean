import Equiv.Recon

/-!
# Mt.Fuji シェルの補助スキャン

`expand` の本体で使う 3 つの走査（`hasCol` / `seamHeightOf` / `isAscending`）を
密表現の言葉に翻訳する。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **列がその段にあることの判定。** -/
theorem hasCol_iff (S : Setting) (M : List Rowj) (hM : MtRep S M) (r j : Nat)
    (hr : r < M.length) (hj : j < S.n) :
    hasCol M r j = true ↔ 0 < (rows S.tower.base r).value j := by
  have hrep := rep_top S M hM r hr
  constructor
  · intro h
    rw [hasCol] at h
    cases hlk : lookupPos (rowAt M r) (j - r) with
    | none => rw [hlk] at h; cases h
    | some m =>
        rw [hlk] at h
        dsimp only at h
        by_cases hm : m < (rowAt M r).size
        · rw [dif_pos hm] at h
          have he : ((rowAt M r)[m]'hm).pos + r = j := by simpa using h
          have h1 := hrep.val _ (mem_of_getElem _ m hm)
          have h2 := hrep.live _ (mem_of_getElem _ m hm)
          rw [he] at h1
          omega
        · rw [dif_neg hm] at h; cases h
  · intro hlive
    have hrj : r ≤ j := by
      rcases Nat.lt_or_ge j r with hx | hx
      · rw [rows_value_zero_of_lt S.tower.base r j hx] at hlive; omega
      · exact hx
    obtain ⟨m, hm, hlk, hcm⟩ := lookupPos_some (rowAt M r) r S.n _ hrep j hrj hj hlive
    rw [hasCol, hlk]
    dsimp only
    rw [dif_pos hm]
    simp [hcm]

/-- **`seamHeight` は「列 `j` を含む最上段の 1 つ上」。** 上限が足りていれば
`height j + 1` である。 -/
theorem seamHeightOf_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (j : Nat)
    (hj : j < S.n) :
    ∀ hi, hi ≤ M.length → height S.tower.base j < hi →
      seamHeightOf M j hi = height S.tower.base j + 1 := by
  intro hi
  induction hi with
  | zero => intro _ h; omega
  | succ h ih =>
    intro hhM hjh
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hjh) with heq | hlt
    · rw [seamHeightOf, if_pos ((hasCol_iff S M hM h j (by omega) hj).mpr
        ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mpr (by omega))), heq]
    · have hdead : ¬ (0 < (rows S.tower.base h).value j) := by
        intro hcon
        exact absurd ((live_iff_le_height S.tower.base (S.tower.hpos j) h).mp hcon)
          (by omega)
      rw [seamHeightOf, if_neg (fun hcon =>
        hdead ((hasCol_iff S M hM h j (by omega) hj).mp hcon))]
      exact ih (by omega) hlt

end Yukito
