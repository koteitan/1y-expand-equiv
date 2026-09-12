import Equiv.NoBad

/-!
# コピーの座標

JS の Mt.Fuji シェルは、継ぎ目の列 `j` を `j + len * i` へ写す。Phyrion 側の
`CopyCoordinates` は同じ写像を `encode` / `parentCopy` と呼ぶ。ここでは両者の
算術が一致することを示す。

- 値の周期的なコピー（JS の `yamaVal`）は `OrdinaryCopy` の `source0` である。
- 親の桁上げ（JS の `shift`）は `parentCopy` である。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **周期的なコピーは `source0` の形をしている。** -/
theorem yamaVal_eq (base : Rowj) (y x c : Nat) (hyx : y < x) :
    yamaVal base y x c = valAtIdx base (if c < y then c else y + (c - y) % (x - y)) := by
  unfold yamaVal
  rcases Nat.lt_or_ge c x with hcx | hcx
  · rw [if_pos hcx]
    rcases Nat.lt_or_ge c y with hcy | hcy
    · rw [if_pos hcy]
    · rw [if_neg (Nat.not_lt.mpr hcy)]
      have h1 : (c - y) % (x - y) = c - y := Nat.mod_eq_of_lt (by omega)
      have h2 : y + (c - y) = c := by omega
      rw [h1, h2]
  · rw [if_neg (Nat.not_lt.mpr hcx), if_neg (by omega)]
    have hmod : (c - x) % (x - y) = (c - y) % (x - y) := by
      have he : c - y = (c - x) + (x - y) := by omega
      rw [he, Nat.add_mod_right]
    rw [hmod]

/-- **`yamaVal` は `OrdinaryCopy` の値のコピーである。** -/
theorem yamaVal_eq_source0 (base : Rowj) (C : OrdinaryCopy.Context) (c : Nat) :
    yamaVal base C.coordinates.y C.coordinates.x c = valAtIdx base (C.source0 c) := by
  rw [yamaVal_eq base _ _ c C.coordinates.root_lt_last]
  unfold OrdinaryCopy.Context.source0 CopyCoordinates.Context.length
  rfl

/-- **JS の桁上げは `parentCopy` である。** -/
theorem js_shift_eq_parentCopy (C : CopyCoordinates.Context) (b col : Nat) :
    col + (if C.y ≤ col then b * C.length else 0) = C.parentCopy b col := by
  unfold CopyCoordinates.Context.parentCopy
  rcases Nat.lt_or_ge col C.y with h | h
  · rw [if_neg (Nat.not_le.mpr h), if_pos h, Nat.add_zero]
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h)]

/-! ## 段への積み足し

`pushAt res k c` は段 `k` の末尾にセルを積む。段が無ければ作る。ループでは `k` は
0 から順に増えるので、つねに `k ≤ res.length` である。 -/

theorem rowAt_getElem? (L : List Rowj) (r : Nat) : rowAt L r = (L[r]?).getD #[] := rfl

theorem rowAt_set_self (L : List Rowj) (y : Rowj) (k : Nat) (h : k < L.length) :
    rowAt (L.set k y) k = y := by
  rw [rowAt_getElem?, List.getElem?_set_self h]
  rfl

theorem rowAt_set_of_ne (L : List Rowj) (y : Rowj) (k m : Nat) (h : m ≠ k) :
    rowAt (L.set k y) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_set_ne (Ne.symm h)]

theorem rowAt_append_lt (L : List Rowj) (x : Rowj) (m : Nat) (h : m < L.length) :
    rowAt (L ++ [x]) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_append_left h]

theorem rowAt_append_self (L : List Rowj) (x : Rowj) : rowAt (L ++ [x]) L.length = x := by
  rw [rowAt_getElem?, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem rowAt_append_gt (L : List Rowj) (x : Rowj) (m : Nat) (h : L.length < m) :
    rowAt (L ++ [x]) m = #[] := by
  rw [rowAt_of_ge]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- 積み足したあとの段の数。 -/
theorem pushAt_length (res : List Rowj) (k : Nat) (c : Cell) (hk : k ≤ res.length) :
    (pushAt res k c).length = max res.length (k + 1) := by
  unfold pushAt
  rcases Nat.lt_or_ge k res.length with h | h
  · rw [if_pos h, List.length_set]
    omega
  · have he : k = res.length := by omega
    subst he
    rw [if_neg (Nat.lt_irrefl _)]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- **積み足したあとの各段。** 段 `k` には末尾にセルが増え、他の段は変わらない。 -/
theorem rowAt_pushAt (res : List Rowj) (k m : Nat) (c : Cell) (hk : k ≤ res.length) :
    rowAt (pushAt res k c) m = if m = k then (rowAt res k).push c else rowAt res m := by
  unfold pushAt
  rcases Nat.lt_or_ge k res.length with h | h
  · rw [if_pos h]
    rcases Decidable.em (m = k) with hm | hm
    · subst hm
      rw [if_pos rfl, rowAt_set_self _ _ _ h]
      rfl
    · rw [if_neg hm, rowAt_set_of_ne _ _ _ _ hm]
  · have he : k = res.length := by omega
    subst he
    rw [if_neg (Nat.lt_irrefl _)]
    rcases Decidable.em (m = res.length) with hm | hm
    · subst hm
      rw [if_pos rfl, rowAt_append_self, rowAt_of_ge res _ (Nat.le_refl _)]
      rfl
    · rw [if_neg hm]
      rcases Nat.lt_or_ge m res.length with h2 | h2
      · exact rowAt_append_lt _ _ _ h2
      · rw [rowAt_append_gt _ _ _ (by omega), rowAt_of_ge _ _ (by omega)]

end Yukito
