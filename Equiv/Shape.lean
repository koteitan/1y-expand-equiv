import Equiv.Copy

/-!
# 疎な山が密な山を表していること

コピーで作った疎な山（値はまだ 0 の印が入っている）が、Phyrion の `RowMountain` の
形と頂の値を表していることを `ShapeRep` として書く。`ShapeRep` があれば、値の埋め
`fillValues` のあとの値は `Reconstruction.value` に一致する。

森の具体形（`fujiSource` の枝）に踏み込まずに、値の層をここで閉じてしまう。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- 疎な山 `Rs` が、密な山 `G`・頂の値 `top`・列の上限 `W` を表している。 -/
structure ShapeRep (Rs : List Rowj) (G : RowMountain) (top : Nat → Nat) (W : Nat) : Prop where
  /-- 各段の位置は真に増加。 -/
  mono : ∀ r, PosMono (rowAt Rs r)
  /-- 親の添字は自分より前。 -/
  parLt : ∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
    ((rowAt Rs r)[i]'h).par = some p → p < i
  /-- 段 `r` にあるセルの列は高さ `r` 以上。 -/
  cellCol : ∀ (r i : Nat) (h : i < (rowAt Rs r).size),
    r ≤ G.height (((rowAt Rs r)[i]'h).pos + r)
  /-- 高さ `r` 以上の列は段 `r` にある。 -/
  cover : ∀ r c, c < W → r ≤ G.height c → ∃ (i : Nat) (h : i < (rowAt Rs r).size),
    ((rowAt Rs r)[i]'h).pos + r = c
  /-- 親を持つセルの親の列。 -/
  parCol : ∀ (r i : Nat) (h : i < (rowAt Rs r).size) (p : Nat),
    ((rowAt Rs r)[i]'h).par = some p → ∃ hp : p < (rowAt Rs r).size,
      (G.row r).parent (((rowAt Rs r)[i]'h).pos + r) = some (((rowAt Rs r)[p]'hp).pos + r)
  /-- 親を持たないセルは密な山でも根。 -/
  parNone : ∀ (r i : Nat) (h : i < (rowAt Rs r).size),
    ((rowAt Rs r)[i]'h).par = none → (G.row r).parent (((rowAt Rs r)[i]'h).pos + r) = none
  /-- 親を持つセルの値は未確定（0）。 -/
  valZero : ∀ (r i : Nat) (h : i < (rowAt Rs r).size),
    ((rowAt Rs r)[i]'h).par ≠ none → ((rowAt Rs r)[i]'h).val = 0
  /-- 親を持たないセルの値は頂の値。 -/
  valTop : ∀ (r i : Nat) (h : i < (rowAt Rs r).size),
    ((rowAt Rs r)[i]'h).par = none → ((rowAt Rs r)[i]'h).val = top (((rowAt Rs r)[i]'h).pos + r)
  /-- 頂の値は正。 -/
  topPos : ∀ c, 0 < top c
  /-- 段が足りている。 -/
  tall : ∀ c, c < W → G.height c + 1 < Rs.length

variable {Rs : List Rowj} {G : RowMountain} {top : Nat → Nat} {W : Nat}

/-- 段 `r` の列 `c` に読める値。 -/
def colVal (Rs : List Rowj) (r c : Nat) : Nat := readVal (rowAt (fillValues Rs) r) r c

theorem ShapeRep.hzero (h : ShapeRep Rs G top W) (r c : Nat) (hc : c < W)
    (hgt : G.height c < r) : colVal Rs r c = 0 := by
  refine readVal_of_no_col _ r c ?_
  intro t d hd hcol
  have hts : t < (rowAt (fillValues Rs) r).size := lt_size_of_getElem? hd
  have hdt : (rowAt (fillValues Rs) r)[t]'hts = d := by
    rw [Array.getElem?_eq_getElem hts] at hd
    exact Option.some.inj hd
  have hsz := fillValues_size Rs r
  have hts' : t < (rowAt Rs r).size := by omega
  have hpos : ((rowAt Rs r)[t]'hts').pos + r = c := by
    rw [← fillValues_pos_get Rs r t hts hts', hdt]
    exact hcol
  have := h.cellCol r t hts'
  rw [hpos] at this
  omega

theorem ShapeRep.htop (h : ShapeRep Rs G top W) (c : Nat) (hc : c < W) :
    colVal Rs (G.height c) c = top c := by
  obtain ⟨i, hi, hpos⟩ := h.cover (G.height c) c hc (Nat.le_refl _)
  have hnone : ((rowAt Rs (G.height c))[i]'hi).par = none := by
    cases hp : ((rowAt Rs (G.height c))[i]'hi).par with
    | none => rfl
    | some p =>
        exfalso
        obtain ⟨hp', hG⟩ := h.parCol (G.height c) i hi p hp
        rw [hpos] at hG
        have := G.parent_source hG
        omega
  have hval := h.valTop (G.height c) i hi hnone
  rw [hpos] at hval
  have hne : ((rowAt Rs (G.height c))[i]'hi).val ≠ 0 := by
    rw [hval]
    have := h.topPos c
    omega
  have htall := h.tall c hc
  rw [colVal, colVal_top Rs h.parLt (G.height c) htall i hi (h.mono _) c hpos hne, hval]

theorem ShapeRep.hstep (h : ShapeRep Rs G top W) (r c p : Nat) (hc : c < W)
    (hp : (G.row r).parent c = some p) :
    colVal Rs r c = colVal Rs r p + colVal Rs (r + 1) c := by
  have hlt : r < G.height c := G.parent_source hp
  obtain ⟨i, hi, hpos⟩ := h.cover r c hc (by omega)
  cases hq : ((rowAt Rs r)[i]'hi).par with
  | none =>
      exfalso
      have := h.parNone r i hi hq
      rw [hpos, hp] at this
      exact absurd this (by simp)
  | some q =>
      obtain ⟨hq', hG⟩ := h.parCol r i hi q hq
      rw [hpos, hp] at hG
      have hpe : ((rowAt Rs r)[q]'hq').pos + r = p := (Option.some.inj hG).symm
      have hql : q < i := h.parLt r i hi q hq
      have hposq : ((rowAt Rs r)[q]'hq').pos < ((rowAt Rs r)[i]'hi).pos :=
        h.mono r q i hq' hi hql
      have hrc : r + 1 ≤ c := by omega
      have hval : ((rowAt Rs r)[i]'hi).val = 0 := h.valZero r i hi (by rw [hq]; simp)
      have htall : r + 1 < Rs.length := by
        have := h.tall c hc
        omega
      exact colVal_step_col Rs h.parLt r htall i hi (h.mono r) c hpos hrc hval q hq hq' p hpe

/-- **`ShapeRep` があれば、埋めたあとの値は `Reconstruction.value` に一致する。** -/
theorem shapeRep_value (h : ShapeRep Rs G top W) (c : Nat) (hc : c < W) (r : Nat) :
    colVal Rs r c = Reconstruction.value G top r c := by
  refine value_of_diff_prefix G top (colVal Rs) W ?_ ?_ ?_ c hc r
  · intro r' c' p hc' hp
    exact h.hstep r' c' p hc' hp
  · intro c' hc'
    exact h.htop c' hc'
  · intro r' c' hc' hgt
    exact h.hzero r' c' hc' hgt

theorem valAtIdx_eq_colVal (Rs : List Rowj) (c : Nat)
    (hmono : PosMono (rowAt (fillValues Rs) 0))
    (hpos : ∀ (t : Nat) (ht : t < (rowAt (fillValues Rs) 0).size),
      ((rowAt (fillValues Rs) 0)[t]'ht).pos = t)
    (hc : c < (rowAt (fillValues Rs) 0).size) :
    valAtIdx (rowAt (fillValues Rs) 0) c = colVal Rs 0 c := by
  rw [colVal, readVal_of_index _ hmono 0 c c hc (by rw [hpos c hc]; omega)]

/-- **値の層の結論。** 疎な山が `G` と `top` を表していて、行 0 が幅 `W` で密なら、
JS の出力は Phyrion の復元値そのものである。 -/
theorem expandOut_eq_value (Rs : List Rowj) (G : RowMountain) (top : Nat → Nat) (W : Nat)
    (h : ShapeRep Rs G top W)
    (hsize : (rowAt (fillValues Rs) 0).size = W)
    (hpos : ∀ (t : Nat) (ht : t < (rowAt (fillValues Rs) 0).size),
      ((rowAt (fillValues Rs) 0)[t]'ht).pos = t) :
    expandOut (fillValues Rs) = (List.range W).map (Reconstruction.value G top 0) := by
  rw [expandOut_eq_range _ W hsize]
  refine List.map_congr_left ?_
  intro c hcm
  have hc : c < W := List.mem_range.mp hcm
  rw [valAtIdx_eq_colVal Rs c (posMono_fillValues Rs 0 (h.mono 0)) hpos (by omega),
    shapeRep_value h c hc 0]

end Yukito
