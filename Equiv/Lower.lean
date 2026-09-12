import Equiv.Yama

/-!
# `k < K` の枝のコピー先の山

原文の `badAtLowerContext`（= `activeLowerContext`）は `LowerCopy.Context` である。
こちらの `Setting` から同じものを組み立てる。

JS 側との対応は
```
badRootHeight = floor = height y
cutHeight     = height x
d             = rise = height x − height y
isAscending   = InCone
```
である。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-! ## この枝の `FujiParams`

`expYama` が偽のとき、JS のパラメータは次のようになる。

```
badRootSeam   = expSeam M mfuel     （= y）
badRootHeight = height y            （列 y を含む最上段）
cutHeight     = height (n−1)        （= expCutH M）
yamakazi      = false
```
-/

theorem expP_yamakazi_lower (M : List Rowj) (mfuel : Nat) (h : ¬ expYama M mfuel) :
    (expP M mfuel).yamakazi = false := by
  show decide (expYama M mfuel) = false
  exact decide_eq_false h

theorem expP_badRootSeam (M : List Rowj) (mfuel : Nat) :
    (expP M mfuel).badRootSeam = expSeam M mfuel := rfl

theorem expP_cutHeight_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (mfuel : Nat) (h : ¬ expYama M mfuel) :
    (expP M mfuel).cutHeight = height S.tower.base (S.n - 1) := by
  show (if expYama M mfuel then expCutH M - 1 else expCutH M) = _
  rw [if_neg h]
  exact expCutH_eq S M hM hn

theorem expP_badRootHeight_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (mfuel : Nat) (h : ¬ expYama M mfuel) (hseam : expSeam M mfuel < S.n) :
    (expP M mfuel).badRootHeight = height S.tower.base (expSeam M mfuel) := by
  show (if expYama M mfuel then expCutH M - 1
        else (topRowWithCol M (expSeam M mfuel) M.length).getD 0) = _
  rw [if_neg h, topRowWithCol_eq S M hM _ hseam M.length (Nat.le_refl _)
    (hM.tall _ hseam)]
  rfl

/-- `k < K` の枝で使う `LowerCopy.Context`。 -/
def lowerContext (S : Setting) (y x : Nat) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x) : LowerCopy.Context where
  mountain := mountainOf' S
  coordinates := ⟨y, x, hyx⟩
  last_root := hroot
  last_higher := hhigher

variable {S : Setting} {y x : Nat}

theorem lowerContext_y (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.y = y := rfl

theorem lowerContext_x (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.x = x := rfl

theorem lowerContext_length (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.length = x - y := rfl

theorem lowerContext_floor (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl

theorem lowerContext_rise (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl

/-- **`InCone` は「段 `height y` で生きていて、その段の根が `y`」。** -/
theorem lowerContext_inCone (hyx : y < x) (hroot) (hhigher) (c : Nat) :
    (lowerContext S y x hyx hroot hhigher).InCone c
      ↔ (height S.tower.base y ≤ height S.tower.base c ∧
          (rows S.tower.base (height S.tower.base y)).forest.root c = y) := Iff.rfl

/-- **JS の `isAscending` は `InCone`。** -/
theorem isAscending_iff_inCone (M : List Rowj) (hM : MtRep S M) (hyx : y < x)
    (hroot) (hhigher) (j fuel : Nat)
    (hbh : height S.tower.base y < M.length) (hj : j < S.n)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ fuel) :
    isAscending M (height S.tower.base y) y j fuel = true
      ↔ (lowerContext S y x hyx hroot hhigher).InCone j := by
  rw [isAscending_iff_root S M hM (height S.tower.base y) y j fuel hbh hj hfuel
    (parent_none_at_top S.tower.base S.tower.hpos y)]
  exact (lowerContext_inCone hyx hroot hhigher j).symm

theorem lowerContext_height_orig (hyx : y < x) (hroot) (hhigher) (c : Nat) (hc : c ≤ x) :
    (lowerContext S y x hyx hroot hhigher).height c = height S.tower.base c :=
  (lowerContext S y x hyx hroot hhigher).height_original hc

/-- **継ぎ目の列（`j = y`）の高さ。** -/
theorem lowerContext_height_seam (hyx : y < x) (hroot) (hhigher) (i : Nat) :
    (lowerContext S y x hyx hroot hhigher).height (y + (x - y) * i)
      = height S.tower.base y
        + i * (height S.tower.base x - height S.tower.base y) := by
  have hc : y + (x - y) * i = (lowerContext S y x hyx hroot hhigher).coordinates.y
      + i * (lowerContext S y x hyx hroot hhigher).coordinates.length := by
    show y + (x - y) * i = y + i * (x - y)
    rw [Nat.mul_comm]
  rw [hc]
  exact (lowerContext S y x hyx hroot hhigher).height_root_copy i

/-- **それ以外の継ぎ目の列の高さ。** `InCone` なら `rise * i` だけ持ち上がる。 -/
theorem lowerContext_height_other (hyx : y < x) (hroot) (hhigher) (j i : Nat)
    (hj1 : y < j) (hj2 : j ≤ x) :
    (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)
      = if (lowerContext S y x hyx hroot hhigher).InCone j then
          height S.tower.base j + i * (height S.tower.base x - height S.tower.base y)
        else height S.tower.base j := by
  have hc : j + (x - y) * i
      = (lowerContext S y x hyx hroot hhigher).coordinates.encode j i := by
    show j + (x - y) * i = j + i * (x - y)
    rw [Nat.mul_comm]
  rw [hc]
  exact (lowerContext S y x hyx hroot hhigher).height_encode hj1 hj2 i

/-- 継ぎ目自身は `InCone`。 -/
theorem inCone_seam (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).InCone y := by
  refine ⟨Nat.le_refl _, ?_⟩
  exact ParentForest.root_of_parent_none _
    (parent_none_at_top S.tower.base S.tower.hpos y)

/-- **JS の `kmax` は原文の高さ + 1。** -/
theorem kmaxAt_eq_height_lower (M : List Rowj) (hM : MtRep S M) (P : FujiParams)
    (hyx : y < x) (hroot) (hhigher)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hsm : P.badRootSeam = y) (hcut : P.cutHeight = height S.tower.base x)
    (ach af i j : Nat) (hj1 : y ≤ j) (hj2 : j < x) (hjn : j < S.n)
    (hsh : seamHeightOf M j ach = height S.tower.base j + 1)
    (hbhlen : height S.tower.base y < M.length)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ af) :
    kmaxAt M P i j ach af
      = (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i) + 1 := by
  have hasc := isAscending_iff_inCone M hM hyx hroot hhigher j af hbhlen hjn hfuel
  unfold kmaxAt isAscAt
  dsimp only
  rw [hbh, hsm, hcut, hsh]
  rcases Decidable.em (j = y) with hje | hjne
  · subst hje
    rw [lowerContext_height_seam hyx hroot hhigher i,
      if_pos (hasc.mpr (inCone_seam hyx hroot hhigher))]
    rw [Nat.mul_comm]
    omega
  · rw [lowerContext_height_other hyx hroot hhigher j i (by omega) (by omega)]
    rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j) with hc | hc
    · rw [if_pos (hasc.mpr hc), if_pos hc, Nat.mul_comm]
      omega
    · rw [if_neg (fun h => hc (hasc.mp h)), if_neg hc]

/-! ## 上りでない列

`isAscending` が偽の列では、`script.js` は Bb 枝しか使わない（`sy = k`）。原文の
`¬InCone s` の枝も `((M.row r).parent s).map (parentCopy b)` で段は `r` そのもの
なので、そのまま対応する。親のセルが積んであることは原文側の
`height_parentCopy_ge`（`M.height p ≤ height (parentCopy b p)`）と
`parent_endpoint`（`r ≤ M.height p`）から出る。 -/

/-! ## 原文の親をコピーの座標で開く

`c = s + b*L`（`y < s ≤ x`、`0 < b`）は `x` より右なので、原文の `parent` は
新しい列の枝に入る。 -/

theorem lowerContext_row (hyx : y < x) (hroot) (hhigher) (r : Nat) :
    (lowerContext S y x hyx hroot hhigher).mountain.row r
      = (rows S.tower.base r).forest := rfl

theorem lowerContext_parent_new (hyx : y < x) (hroot) (hhigher) (r s b : Nat)
    (hs1 : y < s) (hs2 : s ≤ x) (hb : 0 < b) :
    (lowerContext S y x hyx hroot hhigher).parent r (s + b * (x - y))
      = if (lowerContext S y x hyx hroot hhigher).InCone s
            ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ r then
          (if r < (lowerContext S y x hyx hroot hhigher).floor
                + b * (lowerContext S y x hyx hroot hhigher).rise then
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (lowerContext S y x hyx hroot hhigher).floor).parent s
           else
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (r - b * (lowerContext S y x hyx hroot hhigher).rise)).parent s).map
            (fun p => p + b * (lowerContext S y x hyx hroot hhigher).coordinates.length)
        else (((lowerContext S y x hyx hroot hhigher).mountain.row r).parent s).map
          ((lowerContext S y x hyx hroot hhigher).coordinates.parentCopy b) := by
  have henc : s + b * (x - y)
      = (lowerContext S y x hyx hroot hhigher).coordinates.encode s b := rfl
  have hgt : (lowerContext S y x hyx hroot hhigher).coordinates.x
      < (lowerContext S y x hyx hroot hhigher).coordinates.encode s b := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact (lowerContext S y x hyx hroot hhigher).encode_succ_gt_last hs1 b'
  have hsrc : (lowerContext S y x hyx hroot hhigher).coordinates.source
      ((lowerContext S y x hyx hroot hhigher).coordinates.encode s b) = s :=
    (lowerContext S y x hyx hroot hhigher).coordinates.source_encode hs1 hs2 b
  have hblk : (lowerContext S y x hyx hroot hhigher).coordinates.block
      ((lowerContext S y x hyx hroot hhigher).coordinates.encode s b) = b :=
    (lowerContext S y x hyx hroot hhigher).coordinates.block_encode hs1 hs2 b
  rw [henc]
  show (if (lowerContext S y x hyx hroot hhigher).coordinates.encode s b
      ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x then _ else _) = _
  rw [if_neg (Nat.not_le_of_gt hgt)]
  dsimp only
  rw [hsrc, hblk]
  split
  · split <;> rfl
  · rfl

/-! ## 元の段の一致

原文は上りの列について `r < floor + b*rise` なら段 `floor`、そうでなければ
`r − b*rise` を使う。これは `floor` で下から押さえた `max floor (r − b*rise)` に
等しい。JS の `fujiSrcRow` も、段が `floor + rise*i` 以下であればこれに一致する。 -/

theorem clamp_srcRow (f b R r : Nat) :
    (if r < f + b * R then f else r - b * R) = max f (r - b * R) := by
  simp only [Nat.max_def]
  split <;> split <;> omega

theorem fujiSrcRow_notrep (P : FujiParams) (i k : Nat) :
    fujiSrcRow P i k false
      = if k < P.badRootHeight then k
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * i then P.badRootHeight
        else k - (P.cutHeight - P.badRootHeight) * i := by
  simp [fujiSrcRow]

theorem fujiSrcRow_rep (P : FujiParams) (i k : Nat) :
    fujiSrcRow P i k true
      = if k < P.badRootHeight then k
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * (i - 1) then
          P.badRootHeight
        else if k ≤ P.badRootHeight + (P.cutHeight - P.badRootHeight) * i then
          k - (P.cutHeight - P.badRootHeight) * (i - 1)
        else k - (P.cutHeight - P.badRootHeight) * i := by
  simp [fujiSrcRow]

/-- **JS の元の段は原文の元の段に一致する。** 段が `floor + rise*i` 以下であれば、
上りの列では `max floor (k − b*rise)`、そうでなければ `k` そのものである。 -/
theorem fujiSrcRowAt_eq (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (i k : Nat) (isRep isAsc : Bool)
    (hk : k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    fujiSrcRowAt P i k isRep isAsc
      = if isAsc = true ∧ height S.tower.base y ≤ k then
          max (height S.tower.base y)
            (k - (i - (if isRep then 1 else 0))
              * (height S.tower.base x - height S.tower.base y))
        else k := by
  unfold fujiSrcRowAt
  have hc1 : (height S.tower.base x - height S.tower.base y) * i
      = i * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  have hc2 : (height S.tower.base x - height S.tower.base y) * (i - 1)
      = (i - 1) * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  cases isAsc with
  | false => simp
  | true =>
      cases isRep with
      | false =>
          rw [if_pos rfl, fujiSrcRow_notrep, hbh, hcut]
          simp only [Bool.false_eq_true, if_false, Nat.sub_zero, and_true, true_and,
            Nat.max_def]
          repeat' split
          all_goals omega
      | true =>
          rw [if_pos rfl, fujiSrcRow_rep, hbh, hcut]
          simp only [if_true, true_and, Nat.max_def]
          repeat' split
          all_goals omega

/-! ## 原文の親から元の段・元の列・その親を取り出す -/

theorem lowerContext_y_eq (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.y = y := rfl

theorem lowerContext_length_eq (hyx : y < x) (hroot) (hhigher) :
    (lowerContext S y x hyx hroot hhigher).coordinates.length = x - y := rfl

/-- 継ぎ目でない列（`y < j < x`）。 -/
theorem lowerContext_parent_other (hyx : y < x) (hroot) (hhigher) (k i j pc : Nat)
    (hi : 0 < i) (hjy : y < j) (hjx : j < x)
    (hpc : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = some pc) :
    ∃ q, (rows S.tower.base
        (if (lowerContext S y x hyx hroot hhigher).InCone j ∧ height S.tower.base y ≤ k then
          max (height S.tower.base y)
            (k - i * (height S.tower.base x - height S.tower.base y))
         else k)).forest.parent j = some q ∧
      pc = q + (if y ≤ q then i * (x - y) else 0) := by
  have hcol : j + (x - y) * i = j + i * (x - y) := by rw [Nat.mul_comm]
  rw [hcol, lowerContext_parent_new hyx hroot hhigher k j i hjy (by omega) hi] at hpc
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j
      ∧ height S.tower.base y ≤ k) with hcase | hcase
  · rw [if_pos hcase]
    rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone j
      ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcase.1, hcase.2⟩)] at hpc
    rw [hfl, hri] at hpc
    have hif : (if k < height S.tower.base y
              + i * (height S.tower.base x - height S.tower.base y) then
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (height S.tower.base y)).parent j
          else
            ((lowerContext S y x hyx hroot hhigher).mountain.row
              (k - i * (height S.tower.base x - height S.tower.base y))).parent j)
        = ((lowerContext S y x hyx hroot hhigher).mountain.row
            (max (height S.tower.base y)
              (k - i * (height S.tower.base x - height S.tower.base y)))).parent j := by
      rw [← clamp_srcRow (height S.tower.base y) i
        (height S.tower.base x - height S.tower.base y) k]
      split <;> rfl
    rw [hif] at hpc
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
    refine ⟨q, hq, ?_⟩
    have hcone : (lowerContext S y x hyx hroot hhigher).InCone q :=
      (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcase.1
        (show (lowerContext S y x hyx hroot hhigher).floor
          ≤ max (height S.tower.base y)
              (k - i * (height S.tower.base x - height S.tower.base y)) by
          rw [hfl]; exact Nat.le_max_left _ _) hq
    have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hcone
    rw [← hqe, if_pos hyq]
    rfl
  · rw [if_neg hcase]
    rw [if_neg (fun h => hcase ⟨h.1, h.2⟩)] at hpc
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
    refine ⟨q, hq, ?_⟩
    rw [← hqe, parentCopy_eq, lowerContext_y_eq, lowerContext_length_eq]

/-- 継ぎ目の列（`j = y`）。この列の元の列は `x` で、繰り返し `i` のコピーは
`x` の block `i−1` にあたる。 -/
theorem lowerContext_parent_seam (hyx : y < x) (hroot) (hhigher) (k i pc : Nat)
    (hi : 0 < i)
    (hpc : (lowerContext S y x hyx hroot hhigher).parent k (y + (x - y) * i) = some pc) :
    ∃ q, (rows S.tower.base
        (if height S.tower.base y ≤ k then
          max (height S.tower.base y)
            (k - (i - 1) * (height S.tower.base x - height S.tower.base y))
         else k)).forest.parent x = some q ∧
      pc = q + (if y ≤ q then (i - 1) * (x - y) else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hcol : y + (x - y) * (m + 1) = x + m * (x - y) := by
    have h1 : (x - y) * (m + 1) = (x - y) * m + (x - y) := Nat.mul_succ _ _
    have h2 : (x - y) * m = m * (x - y) := Nat.mul_comm _ _
    omega
  have hm1 : m + 1 - 1 = m := by omega
  rw [hcol] at hpc
  rw [hm1]
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  have hcone : (lowerContext S y x hyx hroot hhigher).InCone x :=
    (lowerContext S y x hyx hroot hhigher).last_inCone
  cases m with
  | zero =>
      have hx0 : x + 0 * (x - y) = x := by omega
      rw [hx0, (lowerContext S y x hyx hroot hhigher).parent_original
        (show x ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x from Nat.le_refl _)] at hpc
      refine ⟨pc, ?_, by simp⟩
      rcases Nat.lt_or_ge k (height S.tower.base y) with hk | hk
      · rw [if_neg (by omega)]
        exact hpc
      · rw [if_pos hk]
        have hmx : max (height S.tower.base y)
            (k - 0 * (height S.tower.base x - height S.tower.base y)) = k := by
          simp only [Nat.max_def]
          split <;> omega
        rw [hmx]
        exact hpc
  | succ m' =>
      rw [lowerContext_parent_new hyx hroot hhigher k x (m' + 1) hyx (Nat.le_refl _)
        (by omega)] at hpc
      rcases Nat.lt_or_ge k (height S.tower.base y) with hk | hk
      · rw [if_neg (by omega)]
        rw [if_neg (fun h => absurd h.2 (by rw [hfl]; omega))] at hpc
        obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
        refine ⟨q, hq, ?_⟩
        rw [← hqe, parentCopy_eq, lowerContext_y_eq, lowerContext_length_eq]
      · rw [if_pos hk]
        rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone x
          ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcone, by rw [hfl]; exact hk⟩),
          hfl, hri] at hpc
        have hif : (if k < height S.tower.base y
                  + (m' + 1) * (height S.tower.base x - height S.tower.base y) then
                ((lowerContext S y x hyx hroot hhigher).mountain.row
                  (height S.tower.base y)).parent x
              else
                ((lowerContext S y x hyx hroot hhigher).mountain.row
                  (k - (m' + 1)
                    * (height S.tower.base x - height S.tower.base y))).parent x)
            = ((lowerContext S y x hyx hroot hhigher).mountain.row
                (max (height S.tower.base y)
                  (k - (m' + 1)
                    * (height S.tower.base x - height S.tower.base y)))).parent x := by
          rw [← clamp_srcRow (height S.tower.base y) (m' + 1)
            (height S.tower.base x - height S.tower.base y) k]
          split <;> rfl
        rw [hif] at hpc
        obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
        refine ⟨q, hq, ?_⟩
        have hconeq : (lowerContext S y x hyx hroot hhigher).InCone q :=
          (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcone
            (show (lowerContext S y x hyx hroot hhigher).floor
              ≤ max (height S.tower.base y)
                  (k - (m' + 1)
                    * (height S.tower.base x - height S.tower.base y)) by
              rw [hfl]; exact Nat.le_max_left _ _) hq
        have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hconeq
        rw [← hqe, if_pos hyq]
        rfl

/-- **原文の親から、JS が使う元の段・元の列とその親を取り出す。** -/
theorem lowerContext_parent_src (hyx : y < x) (hroot) (hhigher) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y)
    (k i j pc : Nat) (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hk : k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hpc : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = some pc) :
    ∃ q, (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
          (if j = y then x else j) = some q ∧
      pc = q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (x - y) else 0) := by
  rw [fujiSrcRowAt_eq P hbh hcut i k (isRepAt P j) isAsc hk]
  rcases Decidable.em (j = y) with hje | hjne
  · subst hje
    have hrep : isRepAt P j = true := by
      show decide (j = P.badRootSeam) = true
      rw [hsm]
      simp
    have hasct : isAsc = true := hasc.mpr (inCone_seam hyx hroot hhigher)
    rw [hrep, hasct, if_pos rfl, if_pos rfl]
    simp only [true_and]
    exact lowerContext_parent_seam hyx hroot hhigher k i pc hi hpc
  · have hrep : isRepAt P j = false := by
      show decide (j = P.badRootSeam) = false
      rw [hsm]
      simp [hjne]
    rw [hrep]
    simp only [if_neg hjne, Bool.false_eq_true, if_false, Nat.sub_zero]
    have h := lowerContext_parent_other hyx hroot hhigher k i j pc hi (by omega) hjx hpc
    rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j
        ∧ height S.tower.base y ≤ k) with hc | hc
    · rw [if_pos (show isAsc = true ∧ height S.tower.base y ≤ k from ⟨hasc.mpr hc.1, hc.2⟩)]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg (fun hcon => hc ⟨hasc.mp hcon.1, hcon.2⟩)]
      rw [if_neg hc] at h
      exact h

/-- **JS の元のセルの列。** 置き換えの継ぎ目では行の最後（= `n−1`）、
そうでなければ列 `j` そのもの。 -/
theorem sourceIdx_lower_col (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (sy j : Nat) (hsy : sy < M.length) (hn : 1 < S.n)
    (hsyj : sy ≤ j) (hj : j < S.n)
    (hlive : 0 < (rows S.tower.base sy).value j)
    (hlast : 0 < (rows S.tower.base sy).value (S.n - 1)) :
    ∃ h : sourceIdx M sy j (isRepAt P j) < (rowAt M sy).size,
      ((rowAt M sy)[sourceIdx M sy j (isRepAt P j)]'h).pos + sy
        = if j = P.badRootSeam then S.n - 1 else j := by
  cases hb : isRepAt P j with
  | true =>
      rw [if_pos (of_decide_eq_true hb)]
      exact sourceIdx_last_col S M hM sy j hsy hn hlast
  | false =>
      rw [if_neg (of_decide_eq_false hb)]
      exact sourceIdx_col S M hM sy j hsy hsyj hj hlive

end Yukito
