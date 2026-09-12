import Equiv.Search
import Equiv.Row0

/-!
# 山全体への持ち上げ

1 行ぶんの対応（`rep_row0` / `rep_assignParents` / `rep_nextRow` /
`parRep_assignParents`）を `calcMountain` の全行に回す。

行 0 だけは JS が `searchBase`（左へ走る）を使う。これは `Row0.lean` の `scanLeft`
そのもので、`restrictedParent_linear` により線形森の `restrictedParent` に一致する。
-/

namespace Yukito

open OneY OneY.Numeric

/-! ## 行 0 -/

/-- JS の左スキャン `searchBase` は `scanLeft` そのもの。 -/
theorem searchBase_eq_scanLeft (s : List Nat) (i : Nat) (hi : i < (row0 s).size) :
    ∀ j, j ≤ i → searchBase (row0 s) i j
      = scanLeft (ofSequence s).value ((ofSequence s).value i) j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hji
      have hj : j < (row0 s).size := by omega
      rw [searchBase, dif_pos hj, dif_pos hi, scanLeft, row0_val s j hj, row0_val s i hi]
      by_cases hc : (ofSequence s).value j < (ofSequence s).value i
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        exact ih (by omega)

/-- 行 0 の親も `restrictedParent` に一致する。 -/
theorem parRep_row0 (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    ParRep (assignParents none (row0 s)) 0 (rows (ofSequence s) 0).forest := by
  intro y hy
  obtain ⟨i, hi, hiy⟩ := getElem_of_mem _ hy
  have hsz : (assignParents none (row0 s)).size = (row0 s).size :=
    assignParents_size none (row0 s)
  have hi' : i < (row0 s).size := by omega
  have hpos : ((assignParents none (row0 s))[i]'hi).pos = i := by
    rw [assignParents_pos none (row0 s) i hi hi', row0_pos s i hi']
  have hp : ((assignParents none (row0 s))[i]'hi).par
      = restrictedParent linearForest (ofSequence s).value i := by
    rw [assignParents_none_par (row0 s) i hi hi' (noForced_row0 s _ (mem_of_getElem _ i hi')),
      row0_pos s i hi',
      searchBase_eq_scanLeft s i hi' i (Nat.le_refl _),
      restrictedParent_linear (ofSequence s).value (ofSequence_positive s hs) i]
  rw [← hiy, hp, hpos]
  cases hrp : restrictedParent linearForest (ofSequence s).value i with
  | none =>
      show (rows (ofSequence s) 0).forest.parent (i + 0) = none
      rw [Nat.add_zero]
      exact hrp
  | some p =>
      have hpi : p < i := restrictedParent_left _ _ hrp
      refine ⟨by omega, ?_⟩
      show (rows (ofSequence s) 0).forest.parent (i + 0)
        = some (((assignParents none (row0 s))[p]'(by omega)).pos + 0)
      rw [Nat.add_zero, Nat.add_zero,
        assignParents_pos none (row0 s) p (by omega) (by omega),
        row0_pos s p (by omega)]
      exact hrp

/-! ## 全行 -/

/-- 反復部の全行が対応していること。 -/
theorem mountainGo_rep (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    ∀ f cur k, Rep cur k s.length (rows (ofSequence s) k).value →
      ParRep cur k (rows (ofSequence s) k).forest →
      ∀ r, ∀ hr : r < (mountainGo cur f).length,
        Rep ((mountainGo cur f)[r]'hr) (k + r) s.length
            (rows (ofSequence s) (k + r)).value ∧
          ParRep ((mountainGo cur f)[r]'hr) (k + r)
            (rows (ofSequence s) (k + r)).forest := by
  intro f
  induction f with
  | zero =>
      intro cur k hrep hpar r hr
      simp only [mountainGo] at hr ⊢
      have hr0 : r = 0 := by simp at hr; omega
      subst hr0
      exact ⟨hrep, hpar⟩
  | succ f ih =>
      intro cur k hrep hpar r hr
      by_cases hall : cur.all (fun c => c.par.isNone) = true
      · simp only [mountainGo, if_pos hall] at hr ⊢
        have hr0 : r = 0 := by simp at hr; omega
        subst hr0
        exact ⟨hrep, hpar⟩
      · simp only [mountainGo, if_neg hall] at hr ⊢
        cases r with
        | zero => exact ⟨hrep, hpar⟩
        | succ r =>
            have hnr : Rep (nextRow cur) (k + 1) s.length
                (rows (ofSequence s) (k + 1)).value :=
              rep_nextRow cur k s.length (rows (ofSequence s) k) hrep hpar
            have hnrep : Rep (assignParents (some cur) (nextRow cur)) (k + 1) s.length
                (rows (ofSequence s) (k + 1)).value :=
              rep_assignParents (some cur) (nextRow cur) (k + 1) s.length _ hnr
            have hnpar := parRep_assignParents s hs k cur (nextRow cur) hrep hpar hnr
              (noForced_nextRow cur)
            have hr' : r < (mountainGo (assignParents (some cur) (nextRow cur)) f).length := by
              simp at hr; omega
            have h := ih (assignParents (some cur) (nextRow cur)) (k + 1) hnrep hnpar r hr'
            rw [show k + (r + 1) = (k + 1) + r from by omega]
            exact h

/-- **山の全行が対応している。** -/
theorem calcMountain_rep (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel r : Nat)
    (hr : r < (calcMountain s (fuel + 1)).length) :
    Rep ((calcMountain s (fuel + 1))[r]'hr) r s.length (rows (ofSequence s) r).value ∧
      ParRep ((calcMountain s (fuel + 1))[r]'hr) r (rows (ofSequence s) r).forest := by
  have h := mountainGo_rep s hs fuel (assignParents none (row0 s)) 0
    (rep_assignParents none (row0 s) 0 s.length _ (rep_row0 s hs))
    (parRep_row0 s hs) r hr
  rw [Nat.zero_add] at h
  exact h

/-- **山の値が一致する。** JS の行 `r` を列番号 `c` で引いた値は、
Phyrion 版の行 `r` の列 `c` の値である。 -/
theorem calcMountain_value (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel r c : Nat)
    (hr : r < (calcMountain s (fuel + 1)).length) (hc : c < s.length) :
    readVal ((calcMountain s (fuel + 1))[r]'hr) r c = (rows (ofSequence s) r).value c :=
  rep_read _ r s.length _ (calcMountain_rep s hs fuel r hr).1
    (fun q hq => rows_value_zero_of_lt (ofSequence s) r q hq) c hc

/-- **山の親が一致する。** JS の行 `r` の列 `c` の親は、Phyrion 版の行 `r` の
森での親である。 -/
theorem calcMountain_parent (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel r c : Nat)
    (hr : r < (calcMountain s (fuel + 1)).length) (hc : c < s.length) :
    readPar ((calcMountain s (fuel + 1))[r]'hr) r c
      = (rows (ofSequence s) r).forest.parent c :=
  rep_read_par _ r s.length (rows (ofSequence s) r)
    (calcMountain_rep s hs fuel r hr).1 (calcMountain_rep s hs fuel r hr).2
    (fun q hq => rows_value_zero_of_lt (ofSequence s) r q hq) c hc

end Yukito
