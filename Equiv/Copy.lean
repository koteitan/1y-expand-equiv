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

/-! ## 段のループ

`fujiRows` は段 `k = 0 … kmax−1` に 1 個ずつセルを積む。段 `k` に積むとき、
それより上の段はまだ触られていないので、`fujiCell` に渡る「今の段」は
ループに入る前の段 `k` そのものである。 -/

/-- `fujiRows` が段 `k` に積むセル。 -/
def fujiCellAt (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat) (isRep : Bool)
    (res : List Rowj) (k : Nat) : Cell :=
  let sysx := fujiSource P i k isRep
  let sx := sourceIdx M sysx.1 j sysx.2
  let ir := if isRep then 1 else 0
  fujiCell M P (rowAt res k) sysx.1 sx k i j (i - ir) (nd (j + P.len * i))

theorem fujiRows_length (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep : Bool) : ∀ (kmax : Nat) (res : List Rowj),
      (fujiRows M P nd i j isRep kmax res).length = max res.length kmax := by
  intro kmax
  induction kmax with
  | zero => intro res; simp only [fujiRows, Nat.max_def]; split <;> omega
  | succ kmax ih =>
      intro res
      have hlen := ih res
      have hk : kmax ≤ (fujiRows M P nd i j isRep kmax res).length := by
        rw [hlen]
        simp only [Nat.max_def]
        split <;> omega
      show (pushAt (fujiRows M P nd i j isRep kmax res) kmax _).length = _
      rw [pushAt_length _ _ _ hk, hlen]
      simp only [Nat.max_def]
      split <;> split <;> (first | omega | (split <;> omega))

/-- **段のループの結果。** 段 `m < kmax` にはセルが 1 個増え、他は変わらない。 -/
theorem rowAt_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep : Bool) : ∀ (kmax : Nat) (res : List Rowj) (m : Nat),
      rowAt (fujiRows M P nd i j isRep kmax res) m
        = if m < kmax then (rowAt res m).push (fujiCellAt M P nd i j isRep res m)
          else rowAt res m := by
  intro kmax
  induction kmax with
  | zero => intro res m; rw [if_neg (by omega)]; rfl
  | succ kmax ih =>
      intro res m
      have hlen := fujiRows_length M P nd i j isRep kmax res
      have hk : kmax ≤ (fujiRows M P nd i j isRep kmax res).length := by
        rw [hlen]
        simp only [Nat.max_def]
        split <;> omega
      have hcur : rowAt (fujiRows M P nd i j isRep kmax res) kmax = rowAt res kmax := by
        rw [ih res kmax, if_neg (by omega)]
      show rowAt (pushAt (fujiRows M P nd i j isRep kmax res) kmax
        (fujiCell M P (rowAt (fujiRows M P nd i j isRep kmax res) kmax)
          (fujiSource P i kmax isRep).1
          (sourceIdx M (fujiSource P i kmax isRep).1 j (fujiSource P i kmax isRep).2)
          kmax i j (i - (if isRep then 1 else 0)) (nd (j + P.len * i)))) m = _
      rw [rowAt_pushAt _ _ _ _ hk]
      rcases Decidable.em (m = kmax) with hm | hm
      · rw [if_pos hm, hcur, if_pos (show m < kmax + 1 by omega), hm]
        rfl
      · rw [if_neg hm, ih res m]
        rcases Nat.lt_or_ge m kmax with h | h
        · rw [if_pos h, if_pos (show m < kmax + 1 by omega)]
        · rw [if_neg (show ¬ m < kmax by omega), if_neg (show ¬ m < kmax + 1 by omega)]

/-! ## 継ぎ目と繰り返しのループ -/

/-- 継ぎ目の列 `j` が「置き換え」の列か。 -/
def isRepAt (P : FujiParams) (j : Nat) : Bool := decide (j = P.badRootSeam)

/-- 継ぎ目の列 `j` で積む段の数。 -/
def kmaxAt (M : List Rowj) (P : FujiParams) (i j afterCutHeight ascFuel : Nat) : Nat :=
  let isAsc := isAscending M P.badRootHeight P.badRootSeam j ascFuel
  let seamH := seamHeightOf M j afterCutHeight
  let d := P.cutHeight - P.badRootHeight
  if isAsc then seamH + d * i else seamH

theorem fujiSeams_zero (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i ach af : Nat) (res : List Rowj) : fujiSeams M P nd i ach af 0 res = res := rfl

theorem fujiSeams_succ (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (i ach af t : Nat) (res : List Rowj) :
    fujiSeams M P nd i ach af (t + 1) res
      = fujiRows M P nd i (P.badRootSeam + t) (isRepAt P (P.badRootSeam + t))
          (kmaxAt M P i (P.badRootSeam + t) ach af) (fujiSeams M P nd i ach af t res) := rfl

theorem fujiIters_zero (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (ach af : Nat) (res : List Rowj) : fujiIters M P nd ach af 0 res = res := rfl

theorem fujiIters_succ (M : List Rowj) (P : FujiParams) (nd : Nat → Nat)
    (ach af i : Nat) (res : List Rowj) :
    fujiIters M P nd ach af (i + 1) res
      = fujiSeams M P nd (i + 1) ach af P.len (fujiIters M P nd ach af i res) := rfl

/-! ## 段は後ろに伸びるだけ

`pushAt` は末尾に積むので、既にある添字のセルは変わらない。したがって
`fujiCell` が見る「今の段」は、最終形と既存の添字の上で一致する。 -/

/-- `b` は `a` の後ろにセルを足したもの。 -/
def RowExt (a b : Rowj) : Prop := a.size ≤ b.size ∧ ∀ i, i < a.size → b[i]? = a[i]?

theorem RowExt.rfl' (a : Rowj) : RowExt a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RowExt.trans {a b c : Rowj} (h1 : RowExt a b) (h2 : RowExt b c) : RowExt a c := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun i hi => ?_⟩
  exact (h2.2 i (Nat.lt_of_lt_of_le hi h1.1)).trans (h1.2 i hi)

theorem RowExt.push (a : Rowj) (c : Cell) : RowExt a (a.push c) :=
  ⟨by rw [Array.size_push]; omega,
   fun i hi => by rw [Array.getElem?_push, if_neg (by omega)]⟩

theorem rowExt_fujiRows (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep : Bool) (kmax : Nat) (res : List Rowj) (m : Nat) :
    RowExt (rowAt res m) (rowAt (fujiRows M P nd i j isRep kmax res) m) := by
  rw [rowAt_fujiRows]
  split
  · exact RowExt.push _ _
  · exact RowExt.rfl' _

theorem rowExt_fujiSeams (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat) :
    ∀ (t : Nat) (res : List Rowj) (m : Nat),
      RowExt (rowAt res m) (rowAt (fujiSeams M P nd i ach af t res) m) := by
  intro t
  induction t with
  | zero => intro res m; exact RowExt.rfl' _
  | succ t ih =>
      intro res m
      rw [fujiSeams_succ]
      exact RowExt.trans (ih res m) (rowExt_fujiRows _ _ _ _ _ _ _ _ _)

theorem rowExt_fujiIters (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat) :
    ∀ (n : Nat) (res : List Rowj) (m : Nat),
      RowExt (rowAt res m) (rowAt (fujiIters M P nd ach af n res) m) := by
  intro n
  induction n with
  | zero => intro res m; exact RowExt.rfl' _
  | succ n ih =>
      intro res m
      rw [fujiIters_succ]
      exact RowExt.trans (ih res m) (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)

/-! ## 積むセルの列と親の列 -/

/-- **積むセルの列は `j + len * i`。** どの段でも同じ列に積む。 -/
theorem fujiCell_col (M : List Rowj) (P : FujiParams) (cur : Rowj) (sy sx k i j shifts : Nat)
    (topVal : Nat) (h : k ≤ j + P.len * i) :
    (fujiCell M P cur sy sx k i j shifts topVal).pos + k = j + P.len * i := by
  show (j + P.len * i - k) + k = j + P.len * i
  omega

/-- **親の列は「元の親の列 + 桁上げ」。** `parentPos` はそれを段 `k` の position に
直したものである。 -/
theorem parentPos_eq (M : List Rowj) (P : FujiParams) (sy sx k shifts q : Nat)
    (hsy : sy ≤ k) (hq : parentPos M P sy sx k shifts = some q) :
    ∃ hx : sx < (rowAt M sy).size, ∃ sp, ((rowAt M sy)[sx]'hx).par = some sp ∧
      ∃ hp : sp < (rowAt M sy).size,
        q + k = ((rowAt M sy)[sp]'hp).pos + sy
          + (if P.badRootSeam ≤ ((rowAt M sy)[sp]'hp).pos + sy then shifts * P.len else 0) := by
  unfold parentPos at hq
  dsimp only at hq
  split at hq
  · next hx =>
      cases hpar : ((rowAt M sy)[sx]'hx).par with
      | none => rw [hpar] at hq; exact absurd hq (by simp)
      | some sp =>
          rw [hpar] at hq
          dsimp only at hq
          split at hq
          · next hp =>
              split at hq
              · next hs =>
                  split at hq
                  · next hcond =>
                      refine ⟨hx, sp, hpar, hp, ?_⟩
                      rw [if_pos hs]
                      have he := Option.some.inj hq
                      omega
                  · exact absurd hq (by simp)
              · next hs =>
                  split at hq
                  · next hcond =>
                      refine ⟨hx, sp, hpar, hp, ?_⟩
                      rw [if_neg hs]
                      have he := Option.some.inj hq
                      omega
                  · exact absurd hq (by simp)
          · exact absurd hq (by simp)
  · exact absurd hq (by simp)

/-! ## 子を切る

`cutChild res cutH` は段 `0 … cutH` の最後のセルを落とし、最上段が空なら段ごと落とす。 -/

/-- 段 `i` の最後のセルを落とす 1 歩。 -/
def popStep (r : List Rowj) (i : Nat) : List Rowj :=
  if i < r.length then r.set i ((r.getD i #[]).pop) else r

theorem rowAt_take_lt (L : List Rowj) (k m : Nat) (h : m < k) :
    rowAt (L.take k) m = rowAt L m := by
  rw [rowAt_getElem?, rowAt_getElem?, List.getElem?_take_of_lt h]

theorem popFold_length : ∀ (n : Nat) (res : List Rowj),
    ((List.range n).foldl popStep res).length = res.length := by
  intro n
  induction n with
  | zero => intro res; rfl
  | succ n ih =>
      intro res
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, popStep]
      split
      · rw [List.length_set, ih]
      · exact ih res

/-- **段 `m ≤ cutH` は最後のセルが 1 つ減る。** -/
theorem rowAt_popFold : ∀ (n : Nat) (res : List Rowj) (m : Nat),
    rowAt ((List.range n).foldl popStep res) m
      = if m < n then (rowAt res m).pop else rowAt res m := by
  intro n
  induction n with
  | zero => intro res m; rw [if_neg (show ¬ m < 0 by omega)]; rfl
  | succ n ih =>
      intro res m
      have hlen := popFold_length n res
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, popStep]
      split
      · next hn =>
          rcases Decidable.em (m = n) with hm | hm
          · have hA : ((List.range n).foldl popStep res).getD n #[] = rowAt res n := by
              rw [show ((List.range n).foldl popStep res).getD n #[]
                    = rowAt ((List.range n).foldl popStep res) n from rfl,
                ih res n, if_neg (show ¬ n < n by omega)]
            rw [hm, rowAt_set_self _ _ _ hn, if_pos (show n < n + 1 by omega), hA]
          · rw [rowAt_set_of_ne _ _ _ _ hm, ih res m]
            rcases Nat.lt_or_ge m n with h | h
            · rw [if_pos h, if_pos (show m < n + 1 by omega)]
            · rw [if_neg (show ¬ m < n by omega), if_neg (show ¬ m < n + 1 by omega)]
      · next hn =>
          rw [ih res m]
          rcases Nat.lt_or_ge m n with h | h
          · rw [if_pos h, if_pos (show m < n + 1 by omega)]
          · rcases Decidable.em (m = n) with hm | hm
            · have hres : rowAt res m = #[] := rowAt_of_ge res m (by omega)
              rw [if_neg (show ¬ m < n by omega), if_pos (show m < n + 1 by omega), hres]
              rfl
            · rw [if_neg (show ¬ m < n by omega), if_neg (show ¬ m < n + 1 by omega)]

theorem cutChild_eq (res : List Rowj) (cutH : Nat) :
    cutChild res cutH
      = (if 0 < ((List.range (cutH + 1)).foldl popStep res).length ∧
            (rowAt ((List.range (cutH + 1)).foldl popStep res)
              (((List.range (cutH + 1)).foldl popStep res).length - 1)).size = 0
          then ((List.range (cutH + 1)).foldl popStep res).take
            (((List.range (cutH + 1)).foldl popStep res).length - 1)
          else (List.range (cutH + 1)).foldl popStep res) := rfl

theorem cutChild_length_le (res : List Rowj) (cutH : Nat) :
    (cutChild res cutH).length ≤ res.length := by
  have hlen := popFold_length (cutH + 1) res
  rw [cutChild_eq]
  split
  · rw [List.length_take]
    simp only [Nat.min_def]
    split <;> omega
  · omega

/-- **子を切ったあとの段。** 残っている段については、`cutH` 以下なら最後のセルが
1 つ減り、それより上は変わらない。 -/
theorem rowAt_cutChild (res : List Rowj) (cutH m : Nat) (h : m < (cutChild res cutH).length) :
    rowAt (cutChild res cutH) m
      = if m < cutH + 1 then (rowAt res m).pop else rowAt res m := by
  rw [cutChild_eq] at h
  rw [← rowAt_popFold (cutH + 1) res m, cutChild_eq]
  rcases Decidable.em (0 < ((List.range (cutH + 1)).foldl popStep res).length ∧
      (rowAt ((List.range (cutH + 1)).foldl popStep res)
        (((List.range (cutH + 1)).foldl popStep res).length - 1)).size = 0) with hc | hc
  · rw [if_pos hc] at h ⊢
    rw [List.length_take] at h
    refine rowAt_take_lt _ _ _ ?_
    simp only [Nat.min_def] at h
    split at h <;> omega
  · rw [if_neg hc]

/-! ## 伸びても引ける

`fujiCell` は `lookupPos` で親の添字を引く。段は後ろに伸びるだけなので、その添字は
最終形でも同じ添字である。 -/

theorem RowExt.getElem {a b : Rowj} (h : RowExt a b) (i : Nat) (hi : i < a.size) :
    ∃ hb : i < b.size, (b[i]'hb) = (a[i]'hi) := by
  have hb : i < b.size := Nat.lt_of_lt_of_le hi h.1
  refine ⟨hb, ?_⟩
  have h2 := h.2 i hi
  rw [Array.getElem?_eq_getElem hb, Array.getElem?_eq_getElem hi] at h2
  exact Option.some.inj h2

theorem lookupPos_some_iff (row : Rowj) (q i : Nat) (hl : lookupPos row q = some i) :
    ∃ hi : i < row.size, (row[i]'hi).pos = q := by
  unfold lookupPos at hl
  dsimp only at hl
  split at hl
  · next hm =>
      split at hl
      · next hpos =>
          have heq : firstAtLeast row q = i := Option.some.inj hl
          subst heq
          exact ⟨hm, hpos⟩
      · exact absurd hl (by simp)
  · exact absurd hl (by simp)

theorem lookupPos_of_pos (row : Rowj) (hmono : PosMono row) (q i : Nat) (hi : i < row.size)
    (hpos : (row[i]'hi).pos = q) : lookupPos row q = some i := by
  have hfa : firstAtLeast row q = i := firstAtLeast_eq_of_mem row hmono q i hi hpos
  simp only [lookupPos, hfa, dif_pos hi, if_pos hpos]

/-- **伸びた段でも同じ添字が引ける。** -/
theorem lookupPos_of_rowExt {a b : Rowj} (h : RowExt a b) (hmono : PosMono b) (q i : Nat)
    (hl : lookupPos a q = some i) : lookupPos b q = some i := by
  obtain ⟨hi, hpos⟩ := lookupPos_some_iff a q i hl
  obtain ⟨hb, heq⟩ := h.getElem i hi
  exact lookupPos_of_pos b hmono q i hb (by rw [heq]; exact hpos)

/-! ## 位置の単調性と列の上限

積むセルの列は `(i, j)` の辞書式順で真に増える。段への積み足しは末尾なので、
各段の位置はつねに真に増加のままである。 -/

/-- どの段も位置が真に増加している。 -/
def RowsMono (res : List Rowj) : Prop := ∀ m, PosMono (rowAt res m)

/-- どのセルの列も `b` より小さい。 -/
def ColLt (res : List Rowj) (b : Nat) : Prop :=
  ∀ (m t : Nat) (c : Cell), (rowAt res m)[t]? = some c → c.pos + m < b

theorem ColLt.mono {res : List Rowj} {b b' : Nat} (h : ColLt res b) (hb : b ≤ b') :
    ColLt res b' := fun m t c hc => Nat.lt_of_lt_of_le (h m t c hc) hb

theorem posMono_push (row : Rowj) (hmono : PosMono row) (c : Cell)
    (h : ∀ (t : Nat) (d : Cell), row[t]? = some d → d.pos < c.pos) : PosMono (row.push c) := by
  intro p q hp hq hpq
  rw [Array.size_push] at hp hq
  rcases Nat.lt_or_ge q row.size with hqs | hqs
  · have hps : p < row.size := by omega
    rw [Array.getElem_push_lt hps, Array.getElem_push_lt hqs]
    exact hmono p q hps hqs hpq
  · have hqe : q = row.size := by omega
    have hps : p < row.size := by omega
    subst hqe
    rw [Array.getElem_push_lt hps, Array.getElem_push_eq]
    exact h p (row[p]'hps) (Array.getElem?_eq_getElem hps)

theorem fujiCellAt_col (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep : Bool) (res : List Rowj) (k : Nat) (h : k ≤ j + P.len * i) :
    (fujiCellAt M P nd i j isRep res k).pos + k = j + P.len * i := by
  show (j + P.len * i - k) + k = j + P.len * i
  omega

theorem fujiRows_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i j : Nat)
    (isRep : Bool) (kmax : Nat) (res : List Rowj) (b : Nat)
    (hk : kmax ≤ j + P.len * i + 1) (hb : ColLt res b) (hbc : b ≤ j + P.len * i)
    (hmono : RowsMono res) :
    RowsMono (fujiRows M P nd i j isRep kmax res) ∧
      ColLt (fujiRows M P nd i j isRep kmax res) (j + P.len * i + 1) := by
  constructor
  · intro m
    rw [rowAt_fujiRows]
    split
    · next hm =>
        refine posMono_push _ (hmono m) _ ?_
        intro t d hd
        have h1 := hb m t d hd
        have h2 := fujiCellAt_col M P nd i j isRep res m (by omega)
        omega
    · exact hmono m
  · intro m t c hc
    rw [rowAt_fujiRows] at hc
    split at hc
    · next hm =>
        rw [Array.getElem?_push] at hc
        split at hc
        · have he := Option.some.inj hc
          have h2 := fujiCellAt_col M P nd i j isRep res m (by omega)
          rw [he] at h2
          omega
        · have := hb m t c hc
          omega
    · have := hb m t c hc
      omega

theorem fujiSeams_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (i ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (t : Nat) (res : List Rowj) (b : Nat),
      ColLt res b → b ≤ P.badRootSeam + P.len * i → RowsMono res →
      RowsMono (fujiSeams M P nd i ach af t res) ∧
        ColLt (fujiSeams M P nd i ach af t res) (P.badRootSeam + t + P.len * i) := by
  intro t
  induction t with
  | zero =>
      intro res b hb hbc hmono
      exact ⟨hmono, hb.mono (by omega)⟩
  | succ t ih =>
      intro res b hb hbc hmono
      obtain ⟨hm1, hb1⟩ := ih res b hb hbc hmono
      rw [fujiSeams_succ]
      have h := fujiRows_invariant M P nd i (P.badRootSeam + t)
        (isRepAt P (P.badRootSeam + t)) (kmaxAt M P i (P.badRootSeam + t) ach af)
        (fujiSeams M P nd i ach af t res) (P.badRootSeam + t + P.len * i)
        (hkm i (P.badRootSeam + t)) hb1 (by omega) hm1
      exact ⟨h.1, h.2.mono (by omega)⟩

theorem fujiIters_invariant (M : List Rowj) (P : FujiParams) (nd : Nat → Nat) (ach af : Nat)
    (hkm : ∀ i' j', kmaxAt M P i' j' ach af ≤ j' + P.len * i' + 1) :
    ∀ (n : Nat) (res : List Rowj) (b : Nat),
      ColLt res b → b ≤ P.badRootSeam + P.len → RowsMono res →
      RowsMono (fujiIters M P nd ach af n res) ∧
        ColLt (fujiIters M P nd ach af n res) (P.badRootSeam + P.len + P.len * n) := by
  intro n
  induction n with
  | zero =>
      intro res b hb hbc hmono
      exact ⟨hmono, hb.mono (by omega)⟩
  | succ n ih =>
      intro res b hb hbc hmono
      obtain ⟨hm1, hb1⟩ := ih res b hb hbc hmono
      rw [fujiIters_succ]
      have hle : P.badRootSeam + P.len + P.len * n ≤ P.badRootSeam + P.len * (n + 1) := by
        rw [Nat.mul_succ]
        omega
      have h := fujiSeams_invariant M P nd (n + 1) ach af hkm P.len
        (fujiIters M P nd ach af n res) (P.badRootSeam + P.len + P.len * n) hb1 hle hm1
      refine ⟨h.1, h.2.mono ?_⟩
      rw [Nat.mul_succ]
      omega

end Yukito
