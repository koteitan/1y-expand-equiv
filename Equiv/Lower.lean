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
    (hk : isRep = true → k ≤ height S.tower.base y
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
          have hk' := hk rfl
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
theorem lowerContext_parent_other (hyx : y < x) (hroot) (hhigher) (k i j : Nat)
    (hi : 0 < i) (hjy : y < j) (hjx : j < x) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
      = ((rows S.tower.base
          (if (lowerContext S y x hyx hroot hhigher).InCone j ∧ height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - i * (height S.tower.base x - height S.tower.base y))
           else k)).forest.parent j).map
          (fun q => q + (if y ≤ q then i * (x - y) else 0)) := by
  have hcol : j + (x - y) * i = j + i * (x - y) := by rw [Nat.mul_comm]
  rw [hcol, lowerContext_parent_new hyx hroot hhigher k j i hjy (by omega) hi]
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j
      ∧ height S.tower.base y ≤ k) with hcase | hcase
  · rw [if_pos hcase]
    rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone j
      ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcase.1, hcase.2⟩)]
    rw [hfl, hri]
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
    rw [hif, lowerContext_row]
    cases hq : (rows S.tower.base (max (height S.tower.base y)
        (k - i * (height S.tower.base x - height S.tower.base y)))).forest.parent j with
    | none => rfl
    | some q =>
        have hcone : (lowerContext S y x hyx hroot hhigher).InCone q :=
          (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcase.1
            (show (lowerContext S y x hyx hroot hhigher).floor
              ≤ max (height S.tower.base y)
                  (k - i * (height S.tower.base x - height S.tower.base y)) by
              rw [hfl]; exact Nat.le_max_left _ _) hq
        have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hcone
        show Option.map _ (some q) = Option.map _ (some q)
        rw [Option.map_some, Option.map_some, if_pos hyq]
        rfl
  · rw [if_neg hcase]
    rw [if_neg (fun h => hcase ⟨h.1, h.2⟩), lowerContext_row]
    cases hq : (rows S.tower.base k).forest.parent j with
    | none => rfl
    | some q =>
        show Option.map _ (some q) = Option.map _ (some q)
        rw [Option.map_some, Option.map_some, parentCopy_eq,
          lowerContext_y_eq, lowerContext_length_eq]

/-- 継ぎ目の列（`j = y`）。この列の元の列は `x` で、繰り返し `i` のコピーは
`x` の block `i−1` にあたる。 -/
theorem lowerContext_parent_seam (hyx : y < x) (hroot) (hhigher) (k i : Nat)
    (hi : 0 < i) :
    (lowerContext S y x hyx hroot hhigher).parent k (y + (x - y) * i)
      = ((rows S.tower.base
          (if height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - (i - 1) * (height S.tower.base x - height S.tower.base y))
           else k)).forest.parent x).map
          (fun q => q + (if y ≤ q then (i - 1) * (x - y) else 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hcol : y + (x - y) * (m + 1) = x + m * (x - y) := by
    have h1 : (x - y) * (m + 1) = (x - y) * m + (x - y) := Nat.mul_succ _ _
    have h2 : (x - y) * m = m * (x - y) := Nat.mul_comm _ _
    omega
  have hm1 : m + 1 - 1 = m := by omega
  rw [hcol, hm1]
  have hfl : (lowerContext S y x hyx hroot hhigher).floor = height S.tower.base y := rfl
  have hri : (lowerContext S y x hyx hroot hhigher).rise
      = height S.tower.base x - height S.tower.base y := rfl
  have hcone : (lowerContext S y x hyx hroot hhigher).InCone x :=
    (lowerContext S y x hyx hroot hhigher).last_inCone
  cases m with
  | zero =>
      have hx0 : x + 0 * (x - y) = x := by omega
      rw [hx0, (lowerContext S y x hyx hroot hhigher).parent_original
        (show x ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x from Nat.le_refl _)]
      have hrowk : (if height S.tower.base y ≤ k then
            max (height S.tower.base y)
              (k - 0 * (height S.tower.base x - height S.tower.base y))
           else k) = k := by
        split
        · simp only [Nat.max_def]
          split <;> omega
        · rfl
      rw [hrowk, lowerContext_row]
      cases hq : (rows S.tower.base k).forest.parent x with
      | none => rfl
      | some q => simp
  | succ m' =>
      rw [lowerContext_parent_new hyx hroot hhigher k x (m' + 1) hyx (Nat.le_refl _)
        (by omega)]
      rcases Nat.lt_or_ge k (height S.tower.base y) with hk | hk
      · rw [if_neg (show ¬ (height S.tower.base y ≤ k) by omega)]
        rw [if_neg (show ¬ ((lowerContext S y x hyx hroot hhigher).InCone x
          ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k) by
          rintro ⟨-, h2⟩; rw [hfl] at h2; omega), lowerContext_row]
        cases hq : (rows S.tower.base k).forest.parent x with
        | none => rfl
        | some q =>
            show Option.map _ (some q) = Option.map _ (some q)
            rw [Option.map_some, Option.map_some, parentCopy_eq,
              lowerContext_y_eq, lowerContext_length_eq]
      · rw [if_pos hk]
        rw [if_pos (show (lowerContext S y x hyx hroot hhigher).InCone x
          ∧ (lowerContext S y x hyx hroot hhigher).floor ≤ k from ⟨hcone, by rw [hfl]; exact hk⟩),
          hfl, hri]
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
        rw [hif, lowerContext_row]
        cases hq : (rows S.tower.base (max (height S.tower.base y)
            (k - (m' + 1) * (height S.tower.base x - height S.tower.base y)))).forest.parent x with
        | none => rfl
        | some q =>
            have hconeq : (lowerContext S y x hyx hroot hhigher).InCone q :=
              (lowerContext S y x hyx hroot hhigher).high_parent_inCone hcone
                (show (lowerContext S y x hyx hroot hhigher).floor
                  ≤ max (height S.tower.base y)
                      (k - (m' + 1)
                        * (height S.tower.base x - height S.tower.base y)) by
                  rw [hfl]; exact Nat.le_max_left _ _) hq
            have hyq : y ≤ q := (lowerContext S y x hyx hroot hhigher).root_le_of_inCone hconeq
            show Option.map _ (some q) = Option.map _ (some q)
            rw [Option.map_some, Option.map_some, if_pos hyq]
            rfl

/-- **原文の親は、JS が使う元の段・元の列の親の写しである。** -/
theorem lowerContext_parent_src (hyx : y < x) (hroot) (hhigher) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y)
    (k i j : Nat) (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
      = ((rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
          (if j = y then x else j)).map
          (fun q => q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (x - y) else 0)) := by
  rw [fujiSrcRowAt_eq P hbh hcut i k (isRepAt P j) isAsc
    (fun hr => hk (by rw [← hsm]; exact of_decide_eq_true hr))]
  rcases Decidable.em (j = y) with hje | hjne
  · subst hje
    have hrep : isRepAt P j = true := by
      show decide (j = P.badRootSeam) = true
      rw [hsm]
      simp
    have hasct : isAsc = true := hasc.mpr (inCone_seam hyx hroot hhigher)
    rw [hrep, hasct, if_pos rfl, if_pos rfl]
    simp only [true_and]
    exact lowerContext_parent_seam hyx hroot hhigher k i hi
  · have hrep : isRepAt P j = false := by
      show decide (j = P.badRootSeam) = false
      rw [hsm]
      simp [hjne]
    rw [hrep]
    simp only [if_neg hjne, Bool.false_eq_true, if_false, Nat.sub_zero]
    have h := lowerContext_parent_other hyx hroot hhigher k i j hi (by omega) hjx
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
    (P : FujiParams) (sy j : Nat) (hsy : sy < M.length) (hn : 1 < S.n) (hj : j < S.n)
    (hlive : isRepAt P j = false → 0 < (rows S.tower.base sy).value j)
    (hlast : isRepAt P j = true → 0 < (rows S.tower.base sy).value (S.n - 1)) :
    ∃ h : sourceIdx M sy j (isRepAt P j) < (rowAt M sy).size,
      ((rowAt M sy)[sourceIdx M sy j (isRepAt P j)]'h).pos + sy
        = if j = P.badRootSeam then S.n - 1 else j := by
  cases hb : isRepAt P j with
  | true =>
      rw [if_pos (of_decide_eq_true hb)]
      exact sourceIdx_last_col S M hM sy j hsy hn (hlast hb)
  | false =>
      rw [if_neg (of_decide_eq_false hb)]
      have hlv := hlive hb
      have hsyj : sy ≤ j := by
        rcases Nat.lt_or_ge j sy with hxx | hxx
        · rw [rows_value_zero_of_lt S.tower.base sy j hxx] at hlv
          omega
        · exact hxx
      exact sourceIdx_col S M hM sy j hsy hsyj hj hlv

/-- **JS が積むセルの親。** 元の段の元の列の親を、`parentCopy` で写した列にある。 -/
theorem fujiCellAt_par_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false) (nd : Nat → Nat)
    (i j : Nat) (isAsc : Bool) (res : List Rowj) (k : Nat)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n) (hjn : j < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (C : CopyCoordinates.Context) (hy : C.y = P.badRootSeam) (hL : C.length = P.len)
    (p : Nat) (hp : (fujiCellAt M P nd i j (isRepAt P j) isAsc res k).par = some p) :
    ∃ hp' : p < (rowAt res k).size, ∃ q,
      (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
        (if j = P.badRootSeam then S.n - 1 else j) = some q ∧
      ((rowAt res k)[p]'hp').pos + k
        = C.parentCopy (i - (if isRepAt P j then 1 else 0)) q := by
  have hsy : fujiSrcRowAt P i k (isRepAt P j) isAsc ≤ k :=
    fujiSrcRowAt_le P i k (isRepAt P j) isAsc
  have hp' : (fujiCell M P (rowAt res k) (fujiSrcRowAt P i k (isRepAt P j) isAsc)
      (sourceIdx M (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)) k i j
      (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i))).par = some p := by
    have hun : fujiCellAt M P nd i j (isRepAt P j) isAsc res k
        = fujiCell M P (rowAt res k) (fujiSourceAt P i k (isRepAt P j) isAsc).1
          (sourceIdx M (fujiSourceAt P i k (isRepAt P j) isAsc).1 j
            (fujiSourceAt P i k (isRepAt P j) isAsc).2) k i j
          (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i)) := rfl
    rw [hun, fujiSourceAt_notyama P hyk] at hp
    exact hp
  obtain ⟨hpp, hsx, q, hq, hcol⟩ :=
    fujiCell_par_parentCopy S M hM P (rowAt res k) (fujiSrcRowAt P i k (isRepAt P j) isAsc)
      (sourceIdx M (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)) k i j
      (i - (if isRepAt P j then 1 else 0)) (nd (j + P.len * i)) hsy hry C hy hL p hp'
  obtain ⟨hsx', hcolsrc⟩ :=
    sourceIdx_lower_col S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) j hry hn
      hjn hlive hlast
  refine ⟨hpp, q, ?_, hcol⟩
  rw [← hcolsrc]
  exact hq

/-- `isRepAt` と `j = y` は同じ判定。 -/
theorem isRepAt_eq_lower (P : FujiParams) (hsm : P.badRootSeam = y) (j : Nat) :
    (if isRepAt P j then 1 else 0) = (if j = y then 1 else 0) := by
  show (if (decide (j = P.badRootSeam)) = true then 1 else 0) = _
  rw [hsm]
  simp

/-- **原文に親があれば JS も親を見つける。** -/
theorem fujiCellAt_par_some_of_parent_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (st : List Rowj) (i j k pc : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hmono : PosMono (rowAt st k)) (hcov : HasCol st k pc)
    (hpc : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = some pc) :
    ∃ u, (fujiCellAt M P nd i j (isRepAt P j) isAsc st k).par = some u := by
  have hpcM : ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent
      (j + (x - y) * i) = some pc := hpc
  have hkpc : k ≤ pc := by
    have h1 : k ≤ ((lowerContext S y x hyx hroot hhigher).toRowMountain).height pc :=
      ((lowerContext S y x hyx hroot hhigher).toRowMountain).parent_endpoint hpcM
    have h2 := rowMountain_height_le ((lowerContext S y x hyx hroot hhigher).toRowMountain) pc
    omega
  rw [lowerContext_parent_src hyx hroot hhigher P hbh hcut hsm k i j hi hjy hjx isAsc hasc hk]
    at hpc
  obtain ⟨q, hq, hpceq0⟩ := Option.map_eq_some_iff.mp hpc
  have hpceq : q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (x - y) else 0) = pc :=
    hpceq0
  obtain ⟨hsx, hcolsrc⟩ :=
    sourceIdx_lower_col S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) j hry hn
      (by omega) hlive hlast
  have hsrceq : (if j = P.badRootSeam then S.n - 1 else j) = (if j = y then x else j) := by
    rw [hsm, hx]
  have hF : (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).forest.parent
      (((rowAt M (fujiSrcRowAt P i k (isRepAt P j) isAsc))[sourceIdx M
        (fujiSrcRowAt P i k (isRepAt P j) isAsc) j (isRepAt P j)]'hsx).pos
        + fujiSrcRowAt P i k (isRepAt P j) isAsc) = some q := by
    rw [hcolsrc, hsrceq]
    exact hq
  have hir := isRepAt_eq_lower P hsm j
  have hge : k ≤ q + (if P.badRootSeam ≤ q then
      (i - (if isRepAt P j then 1 else 0)) * P.len else 0) := by
    rw [hsm, hir, hlen]
    omega
  have hpp := parentPos_some S M hM P (fujiSrcRowAt P i k (isRepAt P j) isAsc) _ k
    (i - (if isRepAt P j then 1 else 0)) q hry hsx
    (fujiSrcRowAt_le P i k (isRepAt P j) isAsc) hF hge
  rw [← hir] at hpceq
  rw [hsm, hlen, hpceq] at hpp
  obtain ⟨u, hu, hupos⟩ := hasCol_pos st k pc hcov
  refine ⟨u, ?_⟩
  refine fujiCellAt_par_isSome M P nd i j (isRepAt P j) isAsc st k (pc - k) hmono ?_ u hu
    (by omega)
  rw [fujiSourceAt_notyama P hyk i k (isRepAt P j) isAsc]
  exact hpp

/-- **JS の親のセルの列は原文の親である。** -/
theorem fujiCellAt_parCol_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (res : List Rowj) (i j k p : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hp : (fujiCellAt M P nd i j (isRepAt P j) isAsc res k).par = some p) :
    ∃ hp' : p < (rowAt res k).size,
      (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i)
        = some (((rowAt res k)[p]'hp').pos + k) := by
  obtain ⟨hpp, q, hq, hcol⟩ :=
    fujiCellAt_par_lower S M hM P hyk nd i j isAsc res k hry hn (by omega) hlive hlast
      (lowerContext S y x hyx hroot hhigher).coordinates (by rw [hsm]; rfl)
      (by rw [hlen]; rfl) p hp
  refine ⟨hpp, ?_⟩
  rw [lowerContext_parent_src hyx hroot hhigher P hbh hcut hsm k i j hi hjy hjx isAsc hasc hk]
  have hsrceq : (if j = P.badRootSeam then S.n - 1 else j) = (if j = y then x else j) := by
    rw [hsm, hx]
  rw [hsrceq] at hq
  rw [hq, hcol, parentCopy_eq, lowerContext_y_eq, lowerContext_length_eq,
    isRepAt_eq_lower P hsm j]
  rfl

/-- **JS が親を見つけなければ原文でも根。** -/
theorem fujiCellAt_parNone_lower (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (P : FujiParams) (hyk : P.yamakazi = false)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hsm : P.badRootSeam = y) (hlen : P.len = x - y) (hx : x = S.n - 1)
    (hyx : y < x) (hroot) (hhigher)
    (nd : Nat → Nat) (st : List Rowj) (i j k : Nat) (isAsc : Bool)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < x)
    (hk : j = y → k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i)
    (hry : fujiSrcRowAt P i k (isRepAt P j) isAsc < M.length)
    (hn : 1 < S.n)
    (hlive : isRepAt P j = false →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value j)
    (hlast : isRepAt P j = true →
      0 < (rows S.tower.base (fujiSrcRowAt P i k (isRepAt P j) isAsc)).value (S.n - 1))
    (hmono : PosMono (rowAt st k))
    (hcov : ∀ pc, pc < j + (x - y) * i →
      k ≤ (lowerContext S y x hyx hroot hhigher).height pc → HasCol st k pc)
    (hnone : (fujiCellAt M P nd i j (isRepAt P j) isAsc st k).par = none) :
    (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) = none := by
  cases hp : (lowerContext S y x hyx hroot hhigher).parent k (j + (x - y) * i) with
  | none => rfl
  | some pc =>
      exfalso
      have hpcM : ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent
          (j + (x - y) * i) = some pc := hp
      have hlt : pc < j + (x - y) * i :=
        ((lowerContext S y x hyx hroot hhigher).toRowMountain.row k).parent_left hpcM
      have hge : k ≤ (lowerContext S y x hyx hroot hhigher).height pc :=
        ((lowerContext S y x hyx hroot hhigher).toRowMountain).parent_endpoint hpcM
      obtain ⟨u, hu⟩ :=
        fujiCellAt_par_some_of_parent_lower S M hM P hyk hbh hcut hsm hlen hx hyx hroot hhigher
          nd st i j k pc isAsc hasc hi hjy hjx hk hry hn hlive hlast hmono
          (hcov pc hlt hge) hp
      rw [hu] at hnone
      exact absurd hnone (by simp)

/-! ## 積む段の数

この枝では `kmax` は原文の高さ + 1 である（`kmaxAt_eq_height_lower`）。
`expRes` を使う形にしておく。 -/

/-- **`kmax` は原文の高さ + 1（`expRes` の形）。** -/
theorem kmaxAt_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hsm : P.badRootSeam = y) (hcut : P.cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x) (hroot) (hhigher)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (i j : Nat) (hj1 : y ≤ j) (hj2 : j < x) :
    kmaxAt M P i j (expRes M).length mfuel
      = (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i) + 1 := by
  have hjn : j < S.n := by omega
  have hbhlen : height S.tower.base y < M.length := hM.tall y (by omega)
  exact kmaxAt_eq_height_lower M hM P hyx hroot hhigher hbh hsm hcut
    (expRes M).length mfuel i j hj1 hj2 hjn
    (seamHeightOf_expRes S M hM hn hM2 j (by omega)) hbhlen hfuel

/-- **積む段の数は列より小さい。** 山の高さが列以下であることから出る。 -/
theorem kmaxAt_le_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (P : FujiParams)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hsm : P.badRootSeam = y) (hcut : P.cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (i j : Nat) (hj1 : y ≤ j) (hj2 : j < x) :
    kmaxAt M P i j (expRes M).length mfuel ≤ j + (x - y) * i + 1 := by
  rw [kmaxAt_lower S M hM mfuel hn hM2 P hbh hsm hcut hx hyx hroot hhigher hfuel i j hj1 hj2]
  have hle : (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)
      ≤ j + (x - y) * i :=
    rowMountain_height_le ((lowerContext S y x hyx hroot hhigher).toRowMountain)
      (j + (x - y) * i)
  omega

/-! ## 落差は幅を超えない

段 `r ∈ [floor, height x]` について `rootAt r x` は真に増える。`rootAt floor x = y`
で `rootAt (height x) x = x` なので、段の数だけ列が進む。 -/

theorem rootAt_ge_of_gap (S : Setting) (x : Nat) (y : Nat)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y) :
    ∀ d, height S.tower.base y + d ≤ height S.tower.base x →
      y + d ≤ (mountainOf' S).rootAt (height S.tower.base y + d) x := by
  intro d
  induction d with
  | zero =>
      intro _
      have h0 : height S.tower.base y + 0 = height S.tower.base y := by omega
      rw [h0, hroot]
      omega
  | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 : (mountainOf' S).rootAt (height S.tower.base y + d) x
          < (mountainOf' S).rootAt (height S.tower.base y + (d + 1)) x :=
        (mountainOf' S).rootAt_strict_mono (by omega) (show height S.tower.base y + (d + 1)
          ≤ (mountainOf' S).height x from hd)
      omega

/-- **落差は幅を超えない。** -/
theorem rise_le_length (S : Setting) (y x : Nat)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x) :
    height S.tower.base x - height S.tower.base y ≤ x - y := by
  have hd : height S.tower.base y + (height S.tower.base x - height S.tower.base y)
      = height S.tower.base x := by omega
  have h := rootAt_ge_of_gap S x y hroot
    (height S.tower.base x - height S.tower.base y) (by omega)
  rw [hd] at h
  have htop : (mountainOf' S).rootAt (height S.tower.base x) x = x :=
    (mountainOf' S).top_root x
  rw [htop] at h
  omega

/-- **積む段の数の一様な上界。** -/
theorem kmaxAt_le_lower' (S : Setting) (M : List Rowj) (P : FujiParams)
    (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x) (hlen : P.len = x - y)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i j ach af : Nat) :
    kmaxAt M P i j ach af ≤ j + P.len * i + 1 := by
  refine kmaxAt_le' M P i j ach af ?_
  rw [hbh, hcut, hlen]
  exact rise_le_length S y x hroot hhigher

/-! ## この枝で作る疎な山の形 -/

/-- コピー 1 つぶんの長さ。 -/
theorem expP_len_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (h0 : 0 < (expRes M).length) (y x : Nat)
    (hsm : (expP M mfuel).badRootSeam = y) (hx : x = S.n - 1) :
    (expP M mfuel).len = x - y := by
  show (expP M mfuel).afterCutLength - (expP M mfuel).badRootSeam = x - y
  rw [expP_afterCutLength S M hM mfuel h0, hsm, hx]

theorem rowsMono_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (nd : Nat → Nat) (nrep : Nat) :
    RowsMono (fujiRs M mfuel nd nrep) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcuth : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hsum : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by rw [hsm, hacl]; omega)
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq hcuth.symm)
  exact rowsMono_dropEmptyTop _
    (fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel
      (fun i2 j2 => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut hlen hroot hhigher
        i2 j2 _ _)
      nrep (expRes M) (expP M mfuel).afterCutLength hcolLt (by omega)
      (rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM))).1

/-- **コピーで作った列は原文の高さまで届く。** -/
theorem hasCol_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (nd : Nat → Nat) (nrep m i j : Nat) (hi : 0 < i) (hin : i ≤ nrep)
    (hjy : y ≤ j) (hjx : j < x)
    (hm : m ≤ (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)) :
    HasCol (fujiRaw M mfuel nd nrep) m (j + (expP M mfuel).len * i) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  refine hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel
    (fun i' j' => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut hlen hroot hhigher
      i' j' _ _)
    nrep (expRes M) m i j hi hin (by omega) (by omega) ?_
  rw [kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot hhigher
    hfuel i j hjy hjx]
  omega

/-! ## `ShapeRep` の `cover` -/

/-- **原文の高さ `m` 以下の列は段 `m` に載る。** -/
theorem cover_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (nd : Nat → Nat) (nrep m c : Nat)
    (hc : c < x + (expP M mfuel).len * nrep)
    (hm : m ≤ (lowerContext S y x hyx hroot hhigher).height c) :
    HasCol (fujiRaw M mfuel nd nrep) m c := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hcuth : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  rcases Nat.lt_or_ge c x with hcx | hcx
  · rw [lowerContext_height_orig hyx hroot hhigher c (by omega)] at hm
    have hml : m < (expRes M).length := by
      have := height_lt_expRes_length S M hM hn hM2 c (by omega)
      omega
    exact hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m c
      (hasCol_cutChild S M hM hn (expCutH M) hcuth m c (by omega) hm hml)
  · obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hceq⟩ :=
      col_decomp y x (expP M mfuel).len nrep c hlen (by omega) hyx hcx hc
    have hc' : c = j2 + (x - y) * i2 := by rw [hceq, hlen]
    rw [hceq]
    refine hasCol_lower S M hM mfuel hn hM2 y x hbh hsm hcut hx hyx hroot hhigher hfuel
      nd nrep m i2 j2 hi2 hi2n hj2y hj2x ?_
    rw [← hc']
    exact hm

/-! ## `ShapeRep` の `cellCol` -/

/-- **段 `m` にあるセルの列は原文の高さ `m` 以上。** -/
theorem cellCol_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (nd : Nat → Nat) (nrep m t : Nat) (d : Cell)
    (hd : (rowAt (fujiRaw M mfuel nd nrep) m)[t]? = some d) :
    m ≤ (lowerContext S y x hyx hroot hhigher).height (d.pos + m) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hcuth : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  rcases cell_fujiIters M (expP M mfuel) nd (expRes M).length mfuel
      (fun i2 j2 => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut hlen hroot hhigher
        i2 j2 _ _)
      nrep (expRes M) m t d hd
    with hold | ⟨i2, j2, hi2, _, hj2y, hj2x, hkmax, hceq⟩
  · obtain ⟨hlive, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcuth m t d hold
    rw [lowerContext_height_orig hyx hroot hhigher (d.pos + m) (by omega)]
    exact hlive
  · have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
    have hsum : (expP M mfuel).badRootSeam + (expP M mfuel).len
        = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by rw [hsm, hacl]; omega)
    have hj2x' : j2 < x := by omega
    have hj2y' : y ≤ j2 := by omega
    have hc' : d.pos + m = j2 + (x - y) * i2 := by rw [hceq, hlen]
    rw [hc']
    have hkm := kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot
      hhigher hfuel i2 j2 hj2y' hj2x'
    omega

/-! ## 元からあるセルについての条件

`cutChild` から残った列 `c < n−1` のセルは、原文でも元の山の親をそのまま持つ。 -/

theorem parNone_orig_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (y x : Nat) (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d) (hp : d.par = none) :
    (lowerContext S y x hyx hroot hhigher).parent m (d.pos + m) = none := by
  obtain ⟨_, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcut m t d hd
  have hts : t < (rowAt (expRes M) m).size := lt_size_of_getElem? hd
  have hm : m < (expRes M).length := by
    rcases Nat.lt_or_ge m (expRes M).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  have hdM : (rowAt M m)[t]? = some d := by
    rw [← rowAt_cutChild_getElem? M (expCutH M) m t hm hts]
    exact hd
  have htM : t < (rowAt M m).size := lt_size_of_getElem? hdM
  have hdt : (rowAt M m)[t]'htM = d := by
    rw [Array.getElem?_eq_getElem htM] at hdM
    exact Option.some.inj hdM
  have hmM : m < M.length := by
    have h2 : (expRes M).length ≤ M.length := cutChild_length_le M (expCutH M)
    omega
  have hF := parRep_none S M hM m hmM t htM (by rw [hdt]; exact hp)
  rw [hdt] at hF
  rw [(lowerContext S y x hyx hroot hhigher).parent_original
    (show d.pos + m ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x by
      show d.pos + m ≤ x; omega)]
  exact hF

theorem parCol_orig_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (y x : Nat) (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (st : List Rowj) (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d)
    (hext : RowExt (rowAt (expRes M) m) (rowAt st m))
    (p : Nat) (hp : d.par = some p) :
    ∃ hp' : p < (rowAt st m).size,
      (lowerContext S y x hyx hroot hhigher).parent m (d.pos + m)
        = some (((rowAt st m)[p]'hp').pos + m) := by
  obtain ⟨_, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcut m t d hd
  have hts : t < (rowAt (expRes M) m).size := lt_size_of_getElem? hd
  have hm : m < (expRes M).length := by
    rcases Nat.lt_or_ge m (expRes M).length with h1 | h1
    · exact h1
    · exfalso
      rw [rowAt_of_ge _ m h1] at hts
      simp at hts
  have hdM : (rowAt M m)[t]? = some d := by
    rw [← rowAt_cutChild_getElem? M (expCutH M) m t hm hts]
    exact hd
  have htM : t < (rowAt M m).size := lt_size_of_getElem? hdM
  have hdt : (rowAt M m)[t]'htM = d := by
    rw [Array.getElem?_eq_getElem htM] at hdM
    exact Option.some.inj hdM
  have hmM : m < M.length := by
    have h2 : (expRes M).length ≤ M.length := cutChild_length_le M (expCutH M)
    omega
  obtain ⟨hpM, hF⟩ := parRep_some S M hM m hmM t htM p (by rw [hdt]; exact hp)
  rw [hdt] at hF
  have hpt : p < t := (par_index_lt S M hM m hmM t p htM (by rw [hdt]; exact hp)).2
  have hpc : p < (rowAt (expRes M) m).size := by omega
  have hpe : (rowAt (expRes M) m)[p]? = (rowAt M m)[p]? :=
    rowAt_cutChild_getElem? M (expCutH M) m p hm hpc
  obtain ⟨hp', hpeq⟩ := hext.getElem p hpc
  refine ⟨hp', ?_⟩
  rw [(lowerContext S y x hyx hroot hhigher).parent_original
    (show d.pos + m ≤ (lowerContext S y x hyx hroot hhigher).coordinates.x by
      show d.pos + m ≤ x; omega), lowerContext_row, hF]
  have hcell : (rowAt st m)[p]'hp' = (rowAt M m)[p]'hpM := by
    rw [hpeq]
    rw [Array.getElem?_eq_getElem hpc, Array.getElem?_eq_getElem hpM] at hpe
    exact Option.some.inj hpe
  rw [hcell]

/-! ## 上りの判定と元の段の上界 -/

/-- **JS の上り判定は原文の `InCone`。** -/
theorem hasc_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y) (hsm : P.badRootSeam = y)
    (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (hyn : y < S.n) (j : Nat) (hjn : j < S.n) :
    isAscAt M P j mfuel = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j := by
  have hbhlen : height S.tower.base y < M.length := hM.tall y hyn
  show isAscending M P.badRootHeight P.badRootSeam j mfuel = true ↔ _
  rw [hbh, hsm]
  exact isAscending_iff_inCone M hM hyx hroot hhigher j mfuel hbhlen hjn hfuel

/-- **継ぎ目でない列では、元の段はその列の高さ以下。** -/
theorem srcRow_le_other (S : Setting) (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i k j : Nat) (hi : 0 < i) (hjy : y < j) (hjx : j ≤ x) (isRep isAsc : Bool)
    (hrep : isRep = false)
    (hasc : isAsc = true ↔ (lowerContext S y x hyx hroot hhigher).InCone j)
    (hk : k ≤ (lowerContext S y x hyx hroot hhigher).height (j + (x - y) * i)) :
    fujiSrcRowAt P i k isRep isAsc ≤ height S.tower.base j := by
  rw [lowerContext_height_other hyx hroot hhigher j i hjy hjx] at hk
  rw [fujiSrcRowAt_eq P hbh hcut i k isRep isAsc (by rw [hrep]; intro hc; cases hc)]
  rcases Decidable.em ((lowerContext S y x hyx hroot hhigher).InCone j) with hc | hc
  · rw [if_pos hc] at hk
    have hfl : height S.tower.base y ≤ height S.tower.base j := hc.1
    rcases Decidable.em (isAsc = true ∧ height S.tower.base y ≤ k) with hcc | hcc
    · rw [if_pos hcc, hrep]
      simp only [Bool.false_eq_true, if_false, Nat.sub_zero, Nat.max_def]
      split <;> omega
    · rw [if_neg hcc]
      rcases Decidable.em (height S.tower.base y ≤ k) with h1 | h1
      · exact absurd ⟨hasc.mpr hc, h1⟩ hcc
      · omega
  · rw [if_neg hc] at hk
    have hnot : isAsc = false := by
      cases hA : isAsc with
      | true => exact absurd (hasc.mp hA) hc
      | false => rfl
    rw [if_neg (by rw [hnot]; rintro ⟨h1, -⟩; cases h1)]
    exact hk

/-- **継ぎ目の列では、元の段は `x` の高さ以下。** -/
theorem srcRow_le_seam (S : Setting) (P : FujiParams) (y x : Nat)
    (hbh : P.badRootHeight = height S.tower.base y)
    (hcut : P.cutHeight = height S.tower.base x)
    (hyx : y < x)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (i k : Nat) (hi : 0 < i) (isRep isAsc : Bool) (hasct : isAsc = true)
    (hk : k ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * i) :
    fujiSrcRowAt P i k isRep isAsc ≤ height S.tower.base x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hsucc : (m + 1) * (height S.tower.base x - height S.tower.base y)
      = m * (height S.tower.base x - height S.tower.base y)
        + (height S.tower.base x - height S.tower.base y) := Nat.succ_mul _ _
  have hm1 : (m + 1) - 1 = m := by omega
  have hcomm : (height S.tower.base x - height S.tower.base y) * (m + 1)
      = (m + 1) * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  have hcomm2 : (height S.tower.base x - height S.tower.base y) * m
      = m * (height S.tower.base x - height S.tower.base y) := Nat.mul_comm _ _
  rw [fujiSrcRowAt_eq P hbh hcut (m + 1) k isRep isAsc (fun _ => hk)]
  rcases Decidable.em (isAsc = true ∧ height S.tower.base y ≤ k) with hc | hc
  · rw [if_pos hc]
    cases isRep with
    | false =>
        simp only [Bool.false_eq_true, if_false, Nat.sub_zero, Nat.max_def]
        split <;> omega
    | true =>
        simp only [if_true, hm1, Nat.max_def]
        split <;> omega
  · rw [if_neg hc]
    have hlt : k < height S.tower.base y := by
      rcases Nat.lt_or_ge k (height S.tower.base y) with h1 | h1
      · exact h1
      · exact absurd ⟨hasct, h1⟩ hc
    omega

/-! ## 積んだセルの補助条件

`m < kmaxAt` から、段と列についての条件がまとめて出る。 -/

theorem push_side_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (i' t' m : Nat) (ht' : t' < (expP M mfuel).len)
    (hk' : m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel) :
    y + t' < x ∧
      m ≤ (lowerContext S y x hyx hroot hhigher).height ((y + t') + (x - y) * (i' + 1)) ∧
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel) < M.length ∧
      (isRepAt (expP M mfuel) (y + t') = false →
        0 < (rows S.tower.base (fujiSrcRowAt (expP M mfuel) (i' + 1) m
          (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel))).value (y + t')) ∧
      (isRepAt (expP M mfuel) (y + t') = true →
        0 < (rows S.tower.base (fujiSrcRowAt (expP M mfuel) (i' + 1) m
          (isRepAt (expP M mfuel) (y + t'))
          (isAscAt M (expP M mfuel) (y + t') mfuel))).value (S.n - 1)) ∧
      ((y + t') = y → m ≤ height S.tower.base y
        + (height S.tower.base x - height S.tower.base y) * (i' + 1)) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hjx : y + t' < x := by omega
  have hjn : y + t' < S.n := by omega
  have hasc := hasc_lower S M hM mfuel (expP M mfuel) y x hbh hsm hyx hroot hhigher hfuel
    (by omega) (y + t') hjn
  have hm : m ≤ (lowerContext S y x hyx hroot hhigher).height ((y + t') + (x - y) * (i' + 1)) := by
    have := kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot hhigher
      hfuel (i' + 1) (y + t') (by omega) hjx
    omega
  -- 継ぎ目の列のときの段の上界
  have hseamk : (y + t') = y → m ≤ height S.tower.base y
      + (height S.tower.base x - height S.tower.base y) * (i' + 1) := by
    intro he
    have hcomm : (i' + 1) * (height S.tower.base x - height S.tower.base y)
        = (height S.tower.base x - height S.tower.base y) * (i' + 1) := Nat.mul_comm _ _
    rw [he, lowerContext_height_seam hyx hroot hhigher (i' + 1)] at hm
    omega
  -- 元の段の上界
  have hsyj : isRepAt (expP M mfuel) (y + t') = false →
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
        (isAscAt M (expP M mfuel) (y + t') mfuel) ≤ height S.tower.base (y + t') := by
    intro hrep
    have hne : y + t' ≠ y := by
      intro he
      have : isRepAt (expP M mfuel) (y + t') = true := by
        show decide (y + t' = (expP M mfuel).badRootSeam) = true
        rw [hsm, he]
        simp
      rw [this] at hrep
      cases hrep
    exact srcRow_le_other S (expP M mfuel) y x hbh hcut hyx hroot hhigher (i' + 1) m (y + t')
      (by omega) (by omega) (by omega) _ _ hrep hasc hm
  have hsyx : isRepAt (expP M mfuel) (y + t') = true →
      fujiSrcRowAt (expP M mfuel) (i' + 1) m (isRepAt (expP M mfuel) (y + t'))
        (isAscAt M (expP M mfuel) (y + t') mfuel) ≤ height S.tower.base x := by
    intro hrep
    have he : y + t' = y := by
      have := of_decide_eq_true hrep
      omega
    have hasct : isAscAt M (expP M mfuel) (y + t') mfuel = true := by
      rw [he] at hasc ⊢
      exact hasc.mpr (inCone_seam hyx hroot hhigher)
    exact srcRow_le_seam S (expP M mfuel) y x hbh hcut hyx hhigher (i' + 1) m (by omega) _ _
      hasct (hseamk he)
  have htallj : height S.tower.base (y + t') < M.length := hM.tall (y + t') hjn
  have htallx : height S.tower.base x < M.length := hM.tall x (by omega)
  refine ⟨hjx, hm, ?_, ?_, ?_, hseamk⟩
  · rcases Decidable.em (isRepAt (expP M mfuel) (y + t') = true) with hrep | hrep
    · have := hsyx hrep
      omega
    · have hf : isRepAt (expP M mfuel) (y + t') = false := by
        cases h : isRepAt (expP M mfuel) (y + t') with
        | true => exact absurd h hrep
        | false => rfl
      have := hsyj hf
      omega
  · intro hrep
    exact (live_iff_le_height S.tower.base (S.tower.hpos (y + t')) _).mpr (hsyj hrep)
  · intro hrep
    have hxn : x = S.n - 1 := hx
    rw [← hxn]
    exact (live_iff_le_height S.tower.base (S.tower.hpos x) _).mpr (hsyx hrep)

/-! ## 積む時点での被覆と単調性 -/

theorem rowsMono_state_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (nd : Nat → Nat) (i' t' : Nat) :
    RowsMono (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcuth : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hsum : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by rw [hsm, hacl]; omega)
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut hlen hroot hhigher i2 j2 _ _
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq hcuth.symm)
  obtain ⟨hm1, hb1⟩ := fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel hkm i'
    (expRes M) (expP M mfuel).afterCutLength hcolLt (by omega)
    (rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM))
  have hmul : (expP M mfuel).len * (i' + 1)
      = (expP M mfuel).len * i' + (expP M mfuel).len := Nat.mul_succ _ _
  exact (fujiSeams_invariant M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel hkm t'
    (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))
    ((expP M mfuel).badRootSeam + (expP M mfuel).len + (expP M mfuel).len * i')
    hb1 (by omega) hm1).1

theorem hasCol_state_lower (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (y x : Nat)
    (hbh : (expP M mfuel).badRootHeight = height S.tower.base y)
    (hsm : (expP M mfuel).badRootSeam = y)
    (hcut : (expP M mfuel).cutHeight = height S.tower.base x)
    (hx : x = S.n - 1) (hyx : y < x)
    (hroot : (mountainOf' S).rootAt (height S.tower.base y) x = y)
    (hhigher : height S.tower.base y < height S.tower.base x)
    (hfuel : (rowAt M (height S.tower.base y)).size ≤ mfuel)
    (nd : Nat → Nat) (i' t k pc : Nat) (ht : t < (expP M mfuel).len)
    (hlt : pc < (y + t) + (expP M mfuel).len * (i' + 1))
    (hk : k ≤ (lowerContext S y x hyx hroot hhigher).height pc) :
    HasCol (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) k pc := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hlen : (expP M mfuel).len = x - y := expP_len_lower S M hM mfuel h0 y x hsm hx
  have hcuth : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_lower' S M (expP M mfuel) y x hbh hcut hlen hroot hhigher i2 j2 _ _
  rcases Nat.lt_or_ge pc x with hpc | hpc
  · have hkh : k ≤ height S.tower.base pc := by
      rwa [lowerContext_height_orig hyx hroot hhigher pc (by omega)] at hk
    have hkl : k < (expRes M).length := by
      have := height_lt_expRes_length S M hM hn hM2 pc (by omega)
      omega
    have hres : HasCol (expRes M) k pc :=
      hasCol_cutChild S M hM hn (expCutH M) hcuth k pc (by omega) hkh hkl
    exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
      (hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M) k pc hres)
  · obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hpceq⟩ :=
      col_decomp y x (expP M mfuel).len (i' + 1) pc hlen (by omega) hyx hpc (by omega)
    have hpc' : pc = j2 + (x - y) * i2 := by rw [hpceq, hlen]
    have hkmax : k < kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel := by
      rw [kmaxAt_lower S M hM mfuel hn hM2 (expP M mfuel) hbh hsm hcut hx hyx hroot hhigher
        hfuel i2 j2 hj2y hj2x, ← hpc']
      omega
    rcases col_lt_lex y x (expP M mfuel).len hlen (by omega) j2 i2 (y + t) (i' + 1)
      hj2y hj2x (by omega) (by omega) (by omega) with hlex | ⟨hie, hje⟩
    · rw [hpceq]
      exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
        (hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel hkm i' (expRes M) k i2 j2
          hi2 (by omega) (by omega) (by omega) hkmax)
    · rw [hpceq, hie]
      exact hasCol_fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel hkm t
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M)) k j2
        (by omega) (by omega) (by rw [← hie]; exact hkmax)

end Yukito
