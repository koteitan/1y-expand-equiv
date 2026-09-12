import Equiv.Lookup
import Equiv.Diagonal
import Equiv.Mountain

/-!
# 親探索が `restrictedParent` に一致すること

JS の `searchUpper` は、1 つ下の行の親チェーンを辿り、各要素の列を今の行で引いて
値を比べ、最初に小さいものを親にする。Lean 側の `chainFind`（`Diagonal.lean`）は
同じ形をしており、`chainFind_eq_restrictedParent'` で `restrictedParent` に一致する。

食い違いうるのは 2 か所だけで、どちらも押さえてある。

```
firstAtLeast のずれ  鎖の要素が今の行で死んでいるときだけ起きる（= 鎖の根）
                     そこで指す列の値は c の値以上（root_step_le）
隙間 break           鎖の要素の右隣は生きているので鎖の上では発動しない
                     （chain_succ_live と not_breakHere）
```

したがって歩行は 1 歩ずつ重なる。根に降りたときは JS も Lean も親を返さない。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 探索の結果（`row` の添字）を列番号に読み替える。 -/
def readIdx (row : Rowj) (r : Nat) : Option Nat → Option Nat
  | none => none
  | some j => if h : j < row.size then some ((row[j]'h).pos + r) else none

/-- 位置の大小から添字の大小が出る。 -/
theorem index_lt_of_pos_lt (row : Rowj) (h : PosMono row) (i j : Nat)
    (hi : i < row.size) (hj : j < row.size)
    (hlt : (row[i]'hi).pos < (row[j]'hj).pos) : i < j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact h1
  · subst h1; omega
  · have := h j i hj hi h1; omega

/-- 鎖の線形性。`x` の親 `q` より右にある `c` の祖先は、`x` 以上である。 -/
theorem anc_ge_of_gt_parent {F : ParentForest} {c x q y : Nat}
    (hxc : ZeroY.Forest.Ancestor F.parent c x ∨ x = c)
    (hq : F.parent x = some q)
    (hy : ZeroY.Forest.Ancestor F.parent c y) (hqy : q < y) : x ≤ y := by
  rcases Nat.lt_or_ge y x with hlt | hge
  · exfalso
    have hyx : ZeroY.Forest.Ancestor F.parent x y := by
      rcases hxc with hxa | hxe
      · exact anc_of_common c y x hy hxa hlt
      · rw [hxe]; exact hy
    have := ancestor_le_of_parent hq (ParentForest.ancestor_of_zeroY hyx)
    omega
  · exact hge

/-- 探索が見る述語。「その列が生きていて、値が `c` の値より小さい」。 -/
def searchPred (U : Nat → Nat) (c : Nat) : Nat → Bool :=
  fun q => decide (0 < U q) && decide (U q < U c)

/-- **親探索は `chainFind` に 1 歩ずつ重なる。**

`x` は今いる鎖の位置、`p` はその `prev` での添字。`hacc` は「`x` 以上の生きた祖先は
すべて値が `c` の値以上」で、これまでの比較が失敗してきたことを表す。 -/
theorem searchUpper_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (k : Nat)
    (prev row : Rowj) (i c : Nat)
    (hprev : Rep prev k s.length (rows (ofSequence s) k).value)
    (hpar : ParRep prev k (rows (ofSequence s) k).forest)
    (hrow : Rep row (k + 1) s.length (rows (ofSequence s) (k + 1)).value)
    (hi : i < row.size) (hci : (row[i]'hi).pos + (k + 1) = c) :
    ∀ fuel x p, ∀ hp : p < prev.size, (prev[p]'hp).pos + k = x →
      (ZeroY.Forest.Ancestor (rows (ofSequence s) k).forest.parent c x ∨ x = c) →
      (∀ y, ZeroY.Forest.Ancestor (rows (ofSequence s) k).forest.parent c y → x ≤ y →
        0 < (rows (ofSequence s) (k + 1)).value y →
        (rows (ofSequence s) (k + 1)).value c ≤ (rows (ofSequence s) (k + 1)).value y) →
      p < fuel →
      readIdx row (k + 1) (searchUpper prev row i fuel (some p))
        = chainFind (rows (ofSequence s) k).forest
            (searchPred (rows (ofSequence s) (k + 1)).value c) fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x p hp _ _ _ hf; omega
  | succ fuel ih =>
    intro x p hp hpx hxc hacc hf
    rw [searchUpper, dif_pos hp]
    have hP := hpar _ (mem_of_getElem prev p hp)
    cases hpp : (prev[p]'hp).par with
    | none =>
        rw [hpp] at hP
        rw [hpx] at hP
        simp only [readIdx]
        rw [chainFind, hP]
    | some p' =>
        rw [hpp] at hP
        obtain ⟨hp', hFx⟩ := hP
        rw [hpx] at hFx
        dsimp only
        rw [dif_pos hp']
        -- q は鎖の次の要素
        obtain ⟨q, hq⟩ : ∃ q, (prev[p']'hp').pos + k = q := ⟨_, rfl⟩
        rw [hq] at hFx
        -- q は行 k で生きているので k ≤ q
        have hqV : 0 < (rows (ofSequence s) k).value q :=
          ((rows (ofSequence s) k).parent_values hFx).1
        have hqk : k ≤ q := by
          rcases Nat.lt_or_ge q k with hlt | hge
          · rw [rows_value_zero_of_lt (ofSequence s) k q hlt] at hqV; omega
          · exact hge
        have htarget : (prev[p']'hp').pos - 1 = q - (k + 1) := by omega
        -- q は c の祖先
        have hqc : ZeroY.Forest.Ancestor (rows (ofSequence s) k).forest.parent c q := by
          rcases hxc with ha | he
          · exact Relation.TransGen.tail ha hFx
          · rw [← he]; exact Relation.TransGen.single hFx
        -- 添字は減る
        have hidx : p' < p :=
          index_lt_of_pos_lt prev hprev.posMono p' p hp' hp
            (by have := (rows (ofSequence s) k).forest.parent_left hFx; omega)
        rw [chainFind, hFx]
        dsimp only
        rcases Nat.eq_zero_or_pos ((rows (ofSequence s) (k + 1)).value q) with hdead | hlive
        · -- 鎖の根に降りた場合。どちらも親を返さない。
          have hnp : (rows (ofSequence s) k).forest.parent q = none := by
            rcases hqp : (rows (ofSequence s) k).forest.parent q with _ | t
            · rfl
            · exact absurd ((rows_parent_iff_next_live (ofSequence s) k q).mp ⟨t, hqp⟩)
                (by omega)
          have hpred : searchPred (rows (ofSequence s) (k + 1)).value c q = false := by
            simp only [searchPred, Bool.and_eq_false_iff, decide_eq_false_iff_not]
            exact Or.inl (by omega)
          have hfalse : ¬ (searchPred (rows (ofSequence s) (k + 1)).value c q = true) := by
            rw [hpred]
            exact fun hcon => Bool.noConfusion hcon
          rw [if_neg hfalse, chainFind_none_of_no_parent hnp fuel]
          -- JS 側
          have hsucc : 0 < (rows (ofSequence s) (k + 1)).value (q + 1) :=
            chain_succ_live s hs k q x hFx
          have hsn : q + 1 < s.length := by
            rcases Nat.lt_or_ge (q + 1) s.length with h | h
            · exact h
            · rw [rows_value_zero_of_ge s (k + 1) (q + 1) (by omega) h] at hsucc; omega
          obtain ⟨j, hj, hcj, hfa⟩ := rep_lookup_dead row (k + 1) s.length
            (rows (ofSequence s) (k + 1)).value hrow q (by omega) hsn (by omega) hsucc
          rw [htarget, hfa]
          by_cases hb : breakHere row j = true
          · rw [if_pos hb]; rfl
          · rw [if_neg hb, dif_pos hj, dif_pos hi]
            have hreach : ∀ y,
                ZeroY.Forest.Ancestor (rows (ofSequence s) k).forest.parent c y →
                (∃ t, (rows (ofSequence s) k).forest.parent y = some t) →
                (rows (ofSequence s) (k + 1)).value c ≤
                  (rows (ofSequence s) (k + 1)).value y := by
              intro y hy hyt
              have hlive' := (rows_parent_iff_next_live (ofSequence s) k y).mp hyt
              refine hacc y hy (anc_ge_of_gt_parent hxc hFx hy ?_) hlive'
              rcases Nat.lt_or_ge q y with h | h
              · exact h
              · exfalso
                rcases Nat.eq_or_lt_of_le h with he | he
                · rw [he] at hlive'; omega
                · obtain ⟨t, ht⟩ := ancestor_parent_exists'
                    (ParentForest.ancestor_of_zeroY (anc_of_common c y q hy hqc he))
                  rw [hnp] at ht
                  cases ht
            have hle := (root_step_le s hs k c q hqc hreach).2
            have hvj : (row[j]'hj).val = (rows (ofSequence s) (k + 1)).value (q + 1) := by
              rw [hrow.val _ (mem_of_getElem row j hj), hcj]
            have hvi : (row[i]'hi).val = (rows (ofSequence s) (k + 1)).value c := by
              rw [hrow.val _ (mem_of_getElem row i hi), hci]
            rw [if_neg (by omega)]
            cases fuel with
            | zero => omega
            | succ f =>
                rw [searchUpper, dif_pos hp']
                have hP' := hpar _ (mem_of_getElem prev p' hp')
                rw [hq] at hP'
                cases hpp' : (prev[p']'hp').par with
                | none => simp only [hpp', readIdx]
                | some t =>
                    exfalso
                    rw [hpp'] at hP'
                    obtain ⟨ht, hFq⟩ := hP'
                    rw [hnp] at hFq
                    cases hFq
        · -- 鎖の要素が生きている場合。ちょうど引けて隙間 break も出ない。
          have hqn : q < s.length := by
            rcases Nat.lt_or_ge q s.length with h | h
            · exact h
            · rw [rows_value_zero_of_ge s (k + 1) q (by omega) h] at hlive; omega
          have hqk1 : k + 1 ≤ q := by
            rcases Nat.lt_or_ge q (k + 1) with h | h
            · rw [rows_value_zero_of_lt (ofSequence s) (k + 1) q h] at hlive; omega
            · exact h
          obtain ⟨j, hj, hcj, hfa⟩ := rep_lookup row (k + 1) s.length
            (rows (ofSequence s) (k + 1)).value hrow q (by omega) hqn hlive
          have hsucc : 0 < (rows (ofSequence s) (k + 1)).value (q + 1) :=
            chain_succ_live s hs k q x hFx
          have hsn : q + 1 < s.length := by
            rcases Nat.lt_or_ge (q + 1) s.length with h | h
            · exact h
            · rw [rows_value_zero_of_ge s (k + 1) (q + 1) (by omega) h] at hsucc; omega
          have hnb := not_breakHere row (k + 1) s.length
            (rows (ofSequence s) (k + 1)).value hrow q j hj hcj (by omega) hsn hsucc
          rw [htarget, hfa, if_neg (by rw [hnb]; simp), dif_pos hj, dif_pos hi]
          have hvj : (row[j]'hj).val = (rows (ofSequence s) (k + 1)).value q := by
            rw [hrow.val _ (mem_of_getElem row j hj), hcj]
          have hvi : (row[i]'hi).val = (rows (ofSequence s) (k + 1)).value c := by
            rw [hrow.val _ (mem_of_getElem row i hi), hci]
          have hpred : searchPred (rows (ofSequence s) (k + 1)).value c q
              = decide ((rows (ofSequence s) (k + 1)).value q <
                        (rows (ofSequence s) (k + 1)).value c) := by
            simp only [searchPred, decide_eq_true hlive, Bool.true_and]
          rw [hpred]
          by_cases hcmp : (rows (ofSequence s) (k + 1)).value q <
              (rows (ofSequence s) (k + 1)).value c
          · rw [if_pos (by omega), if_pos (decide_eq_true hcmp)]
            simp only [readIdx, dif_pos hj, hcj]
          · rw [if_neg (by omega), if_neg (by simp [hcmp])]
            refine ih q p' hp' hq (Or.inl hqc) ?_ (by omega)
            intro y hy hqy hly
            rcases Nat.eq_or_lt_of_le hqy with he | hgt
            · rw [← he]; omega
            · exact hacc y hy (anc_ge_of_gt_parent hxc hFx hy hgt) hly

end Yukito
