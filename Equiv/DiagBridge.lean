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

/-! ## 脚 1 歩の対応

`Extract.lean` の `legStep` は密表現での脚 1 歩である。JS の `legStepJS` と
1 対 1 に対応する。状態の読み替えは「（段, 添字）→（段, 列）」である。 -/

/-- 山の頂の高さは列番号以下。生きた列は 1 行ごとに右へずれるからである。 -/
theorem height_le_self (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (c : Nat) :
    height (ofSequence s) c ≤ c := by
  rcases Nat.lt_or_ge c (height (ofSequence s) c) with h | h
  · have hl := height_live (ofSequence s) (ofSequence_positive s hs c)
    rw [rows_value_zero_of_lt (ofSequence s) _ c h] at hl
    omega
  · exact h

/-- Phyrion 版の山。 -/
def mountainOf (s : List Nat) (hs : ∀ x ∈ s, 0 < x) : RootGeometry.RowMountain :=
  mountain (ofSequence s) (ofSequence_positive s hs)

/-- 疎配列の状態（段, 添字）を列座標に読み替える。 -/
def readState (M : List Rowj) (st : Nat × Nat) : Option (Nat × Nat) :=
  if hi : st.2 < (rowAt M st.1).size then
    some (st.1, ((rowAt M st.1)[st.2]'hi).pos + st.1)
  else none

/-- 状態の読み替えを `Option` へ持ち上げたもの。 -/
def readOpt (M : List Rowj) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => none
  | some st => readState M st

/-- **脚 1 歩が一致する。** -/
theorem legStepJS_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (M : List Rowj)
    (hM : MountainRep M s) (h idx : Nat) (hh : h < M.length)
    (hidx : idx < (rowAt M h).size) (hn : ((rowAt M h)[idx]'hidx).pos + h < s.length) :
    readOpt M (legStepJS M h idx)
      = legStep (mountainOf s hs) h (((rowAt M h)[idx]'hidx).pos + h) := by
  have hrep := rep_top s M hM h hh
  have hpar : ParRep (rowAt M h) h (rows (ofSequence s) h).forest := by
    rw [rowAt_eq M h hh]; exact (hM h hh).2
  have hP := hpar _ (mem_of_getElem _ idx hidx)
  cases h with
  | zero =>
    show (readOpt M (if hi : idx < (rowAt M 0).size then
            match ((rowAt M 0)[idx]'hi).par with
            | none => none
            | some p => some ((0 : Nat), p)
          else none)) = _
    rw [dif_pos hidx]
    cases hpp : ((rowAt M 0)[idx]'hidx).par with
    | none =>
        rw [hpp] at hP
        show (none : Option (Nat × Nat)) = _
        show _ = (match (rows (ofSequence s) 0).forest.parent
          (((rowAt M 0)[idx]'hidx).pos + 0) with
          | none => none
          | some q => if 0 ≤ (mountainOf s hs).height q then some (0, q)
                      else some (0 - 1, q))
        rw [hP]
    | some p =>
        rw [hpp] at hP
        obtain ⟨hp, hFc⟩ := hP
        show (readOpt M (some ((0 : Nat), p))) = _
        show (readState M (0, p)) = _
        show (if hi : p < (rowAt M 0).size then
                some ((0 : Nat), ((rowAt M 0)[p]'hi).pos + 0) else none) = _
        rw [dif_pos hp]
        show _ = (match (rows (ofSequence s) 0).forest.parent
          (((rowAt M 0)[idx]'hidx).pos + 0) with
          | none => none
          | some q => if 0 ≤ (mountainOf s hs).height q then some (0, q)
                      else some (0 - 1, q))
        rw [hFc]
        simp
  | succ h' =>
    have hh' : h' < M.length := by omega
    have hrep' := rep_top s M hM h' hh'
    have hpar' : ParRep (rowAt M h') h' (rows (ofSequence s) h').forest := by
      rw [rowAt_eq M h' hh']; exact (hM h' hh').2
    have hlive : 0 < (rows (ofSequence s) (h' + 1)).value
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) := by
      have h1 := hrep.val _ (mem_of_getElem _ idx hidx)
      have h2 := hrep.live _ (mem_of_getElem _ idx hidx)
      omega
    have hlive' : 0 < (rows (ofSequence s) h').value
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) := by
      have := rows_value_le (ofSequence s) h'
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1))
      omega
    obtain ⟨l0, hl0, hlk0, hcl0⟩ :=
      lookupPos_some (rowAt M h') h' s.length _ hrep'
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) (by omega) hn hlive'
    have htarget : ((rowAt M (h' + 1))[idx]'hidx).pos + 1
        = (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) - h' := by omega
    show (readOpt M (legStepJS M (h' + 1) idx)) = _
    rw [legStepJS]
    simp only [dif_pos hidx, htarget, hlk0]
    have hP' := hpar' _ (mem_of_getElem _ l0 hl0)
    rw [hcl0] at hP'
    show _ = (match (rows (ofSequence s) h').forest.parent
        (((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1)) with
      | none => none
      | some q => if h' + 1 ≤ (mountainOf s hs).height q then some (h' + 1, q)
                  else some (h' + 1 - 1, q))
    rw [dif_pos hl0]
    cases hpp : ((rowAt M h')[l0]'hl0).par with
    | none =>
        rw [hpp] at hP'
        rw [hP']
        rfl
    | some l =>
        rw [hpp] at hP'
        obtain ⟨hl, hFc⟩ := hP'
        dsimp only
        rw [hFc, dif_pos hl]
        dsimp only
        have hqlt : ((rowAt M h')[l]'hl).pos + h'
            < ((rowAt M (h' + 1))[idx]'hidx).pos + (h' + 1) :=
          (rows (ofSequence s) h').forest.parent_left hFc
        have hqlive' : 0 < (rows (ofSequence s) h').value
            (((rowAt M h')[l]'hl).pos + h') := by
          have h1 := hrep'.val _ (mem_of_getElem _ l hl)
          have h2 := hrep'.live _ (mem_of_getElem _ l hl)
          omega
        have hqn : ((rowAt M h')[l]'hl).pos + h' < s.length := by omega
        by_cases hz : ((rowAt M h')[l]'hl).pos = 0
        · rw [if_pos hz]
          have hhq : height (ofSequence s) (((rowAt M h')[l]'hl).pos + h') ≤ h' := by
            have := height_le_self s hs (((rowAt M h')[l]'hl).pos + h')
            omega
          rw [if_neg (show ¬ (h' + 1 ≤ (mountainOf s hs).height
            (((rowAt M h')[l]'hl).pos + h')) by
              show ¬ (h' + 1 ≤ height (ofSequence s) _); omega)]
          show readState M (h', l) = _
          simp only [readState, dif_pos hl, Nat.add_sub_cancel]
        · rw [if_neg hz]
          have hteq : ((rowAt M h')[l]'hl).pos - 1
              = (((rowAt M h')[l]'hl).pos + h') - (h' + 1) := by omega
          rw [hteq]
          by_cases hql : 0 < (rows (ofSequence s) (h' + 1)).value
              (((rowAt M h')[l]'hl).pos + h')
          · obtain ⟨m, hm, hlkm, hcm⟩ :=
              lookupPos_some (rowAt M (h' + 1)) (h' + 1) s.length _ hrep
                (((rowAt M h')[l]'hl).pos + h') (by omega) hqn hql
            rw [hlkm]
            rw [if_pos (show h' + 1 ≤ (mountainOf s hs).height
              (((rowAt M h')[l]'hl).pos + h') from
                (live_iff_le_height (ofSequence s)
                  (ofSequence_positive s hs _) (h' + 1)).mp hql)]
            show readState M (h' + 1, m) = _
            simp only [readState, dif_pos hm, hcm]
          · rw [lookupPos_none (rowAt M (h' + 1)) (h' + 1) s.length _ hrep
              (((rowAt M h')[l]'hl).pos + h') (by omega) (by omega)]
            rw [if_neg (show ¬ (h' + 1 ≤ (mountainOf s hs).height
              (((rowAt M h')[l]'hl).pos + h')) from fun hcon =>
                hql ((live_iff_le_height (ofSequence s)
                  (ofSequence_positive s hs _) (h' + 1)).mpr hcon))]
            show readState M (h', l) = _
            simp only [readState, dif_pos hl, Nat.add_sub_cancel]

/-! ## 脚歩行の対応 -/

/-- **脚歩行が一致する。** 1 歩の対応を歩行全体に回したもの。 -/
theorem legWalkJS_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (M : List Rowj)
    (hM : MountainRep M s) :
    ∀ fuel h idx, ∀ hh : h < M.length, ∀ hidx : idx < (rowAt M h).size,
      ((rowAt M h)[idx]'hidx).pos + h < s.length →
      legWalkJS M fuel h idx
        = jsWalk (mountainOf s hs) fuel h (((rowAt M h)[idx]'hidx).pos + h) := by
  intro fuel
  induction fuel with
  | zero => intro h idx _ _ _; rfl
  | succ fuel ih =>
    intro h idx hh hidx hn
    have hstep := legStepJS_eq s hs M hM h idx hh hidx hn
    rw [legWalkJS, jsWalk]
    cases hst : legStepJS M h idx with
    | none =>
        rw [hst, readOpt] at hstep
        rw [← hstep]
    | some st =>
        obtain ⟨h', idx'⟩ := st
        rw [hst, readOpt] at hstep
        dsimp only
        by_cases hi : idx' < (rowAt M h').size
        · rw [readState] at hstep
          dsimp only at hstep
          rw [dif_pos hi] at hstep
          have hh'h : h' ≤ h := legStep_row_le _ hstep.symm
          have hh' : h' < M.length := by omega
          have hlt := legStep_col_lt _ hstep.symm
          have hpar' : ParRep (rowAt M h') h' (rows (ofSequence s) h').forest := by
            rw [rowAt_eq M h' hh']; exact (hM h' hh').2
          have hP := hpar' _ (mem_of_getElem _ idx' hi)
          rw [← hstep]
          dsimp only
          rw [dif_pos hi]
          cases hpp : ((rowAt M h')[idx']'hi).par with
          | none =>
              rw [hpp] at hP
              have hPn : ((mountainOf s hs).row h').parent
                  (((rowAt M h')[idx']'hi).pos + h') = none := hP
              rw [if_pos hPn]
          | some p =>
              rw [hpp] at hP
              obtain ⟨hp, hFc⟩ := hP
              rw [if_neg (show ¬ (((mountainOf s hs).row h').parent
                  (((rowAt M h')[idx']'hi).pos + h') = none) from by
                    show ¬ ((rows (ofSequence s) h').forest.parent
                      (((rowAt M h')[idx']'hi).pos + h') = none)
                    rw [hFc]
                    intro hcon
                    cases hcon)]
              exact ih h' idx' hh' hi (by omega)
        · rw [readState, dif_neg hi] at hstep
          rw [← hstep]
          dsimp only
          rw [dif_neg hi]

/-- **対角の 1 要素が一致する。** JS が積む値は `topValue`、歩行の結果は
Phyrion の `Pseudo.parent` である。 -/
theorem diagEntry_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (M : List Rowj)
    (hM : MountainRep M s) (i : Nat) (hi : i < s.length)
    (hlen : height (ofSequence s) i < M.length) :
    diagEntry M i
      = some (topValue (ofSequence s) i, Pseudo.parent (mountainOf s hs) i) := by
  obtain ⟨k, hk, hck, htop⟩ := topAt_eq s hs M hM i hi M.length (Nat.le_refl _) hlen
  have hrep := rep_top s M hM (height (ofSequence s) i) hlen
  have hval : ((rowAt M (height (ofSequence s) i))[k]'hk).val
      = topValue (ofSequence s) i := by
    have h := hrep.val _ (mem_of_getElem _ k hk)
    rw [hck] at h
    exact h
  have hwalk : legWalkJS M (i + 1) (height (ofSequence s) i) k
      = jsWalk (mountainOf s hs) (i + 1) (height (ofSequence s) i) i := by
    have h := legWalkJS_eq s hs M hM (i + 1) (height (ofSequence s) i) k hlen hk
      (by rw [hck]; exact hi)
    rw [hck] at h
    exact h
  have hps : jsWalk (mountainOf s hs) (i + 1) (height (ofSequence s) i) i
      = Pseudo.parent (mountainOf s hs) i :=
    jsWalk_eq_pseudo (mountainOf s hs) i (i + 1) (by omega)
  rw [diagEntry, htop]
  simp only [dif_pos hk, hval, hwalk, hps]

/-! ## 対角のリスト -/

theorem filterMap_range_eq_map {α : Type} (n : Nat) (f : Nat → Option α) (g : Nat → α)
    (h : ∀ i, i < n → f i = some (g i)) :
    (List.range n).filterMap f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.filterMap_append, List.map_append,
        ih (fun i hi => h i (by omega))]
      simp [h n (by omega)]

/-- **対角のリストが一致する。** JS の `diagonal` と `diagonalTree` は、
Phyrion の `topValue` と `Pseudo.parent` の並びである。 -/
theorem diagList_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) :
    diagList (calcMountain s (fuel + 1))
      = (List.range s.length).map
          (fun i => (topValue (ofSequence s) i, Pseudo.parent (mountainOf s hs) i)) := by
  rw [diagList, size_rowAt_calcMountain_zero]
  exact filterMap_range_eq_map _ _ _ (fun i hi =>
    diagEntry_eq s hs _ (mountainRep_calcMountain s hs fuel) i hi
      (height_lt_length s hs fuel hf i hi))

/-! ## 2 つの探索

`treeScan` は `diagonalTree`（擬親森）を辿る探索で、`Diagonal.lean` の `chainFind`
と同じ形をしている。`pwScan` は線形森を辿る探索で、`Row0.lean` の `scanLeft` と
同じ形である。 -/

theorem getD_map_range {α : Type} (n i : Nat) (g : Nat → α) (dflt : α) (hi : i < n) :
    ((List.range n).map g).getD i dflt = g i := by
  simp only [List.getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

theorem getD_map_range_ge {α : Type} (n i : Nat) (g : Nat → α) (dflt : α) (hi : n ≤ i) :
    ((List.range n).map g).getD i dflt = dflt := by
  have h : (List.range n)[i]? = none :=
    List.getElem?_eq_none (by simp only [List.length_range]; omega)
  simp only [List.getD, List.getElem?_map, h, Option.map_none, Option.getD_none]

/-- 対角の値の並び。 -/
theorem diagVals (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) :
    (diagList (calcMountain s (fuel + 1))).map Prod.fst
      = (List.range s.length).map (topValue (ofSequence s)) := by
  rw [diagList_eq s hs fuel hf, List.map_map]
  rfl

/-- 対角の歩行結果の並び。 -/
theorem diagTree (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) :
    (diagList (calcMountain s (fuel + 1))).map Prod.snd
      = (List.range s.length).map (Pseudo.parent (mountainOf s hs)) := by
  rw [diagList_eq s hs fuel hf, List.map_map]
  rfl

/-- 入力列の外の列は頂が段 0 なので擬親を持たない。 -/
theorem pseudo_parent_of_ge (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (p : Nat)
    (hp : s.length ≤ p) : Pseudo.parent (mountainOf s hs) p = none := by
  refine (Pseudo.parent_none_iff (mountainOf s hs) p).mpr ?_
  show height (ofSequence s) p = 0
  rcases Nat.eq_zero_or_pos (height (ofSequence s) p) with h | h
  · exact h
  · exfalso
    have hlive := height_live (ofSequence s) (ofSequence_positive s hs p)
    rw [rows_value_zero_of_ge s (height (ofSequence s) p) p h hp] at hlive
    omega

/-- **`treeScan` は `chainFind` である。** -/
theorem treeScan_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (target : Nat) :
    ∀ fuel p,
      treeScan ((List.range s.length).map (topValue (ofSequence s)))
        ((List.range s.length).map (Pseudo.parent (mountainOf s hs))) target fuel p
        = chainFind (Pseudo.forest (mountainOf s hs))
            (fun q => decide (topValue (ofSequence s) q < target)) fuel p := by
  intro fuel
  induction fuel with
  | zero => intro p; rfl
  | succ fuel ih =>
    intro p
    rw [treeScan, chainFind]
    have hkey : ((List.range s.length).map (Pseudo.parent (mountainOf s hs))).getD p none
        = (Pseudo.forest (mountainOf s hs)).parent p := by
      rcases Nat.lt_or_ge p s.length with h | h
      · rw [getD_map_range s.length p _ none h]
        rfl
      · rw [getD_map_range_ge s.length p _ none h]
        exact (pseudo_parent_of_ge s hs p h).symm
    rw [hkey]
    cases hq : (Pseudo.forest (mountainOf s hs)).parent p with
    | none => rfl
    | some q =>
        dsimp only
        have hqp : q < p := (Pseudo.forest (mountainOf s hs)).parent_left hq
        have hpn : p < s.length := by
          rcases Nat.lt_or_ge p s.length with h | h
          · exact h
          · exfalso
            have h2 : Pseudo.parent (mountainOf s hs) p = some q := hq
            rw [pseudo_parent_of_ge s hs p h] at h2
            cases h2
        rw [getD_map_range s.length q _ 0 (by omega)]
        by_cases hc : topValue (ofSequence s) q < target
        · rw [if_pos hc, if_pos (decide_eq_true hc)]
        · rw [if_neg hc, if_neg (by simp [hc])]
          exact ih q

/-- **`pwScan` は `scanLeft` である。** -/
theorem pwScan_eq (s : List Nat) (target : Nat) :
    ∀ j, j ≤ s.length →
      pwScan ((List.range s.length).map (topValue (ofSequence s))) target j
        = scanLeft (topValue (ofSequence s)) target j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [pwScan, scanLeft, getD_map_range s.length j _ 0 (by omega)]
      by_cases hc : topValue (ofSequence s) j < target
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        exact ih (by omega)

/-! ## `calcDiagonal` 全体 -/

/-- **`calcDiagonal` の出力が一致する。** 各要素の値は `topValue`、明示する親は
擬親森の `restrictedParent`（= `rawExtract` の親）で、線形森の `restrictedParent`
（= 読み直しの既定の親）と食い違うときだけ `"v"` が付く。 -/
theorem calcDiagonal_eq (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) :
    calcDiagonal (calcMountain s (fuel + 1))
      = (List.range s.length).map (fun i =>
          if restrictedParent (Pseudo.forest (mountainOf s hs))
                (topValue (ofSequence s)) i
              = restrictedParent linearForest (topValue (ofSequence s)) i then
            { val := topValue (ofSequence s) i, forced := false, par := none }
          else
            { val := topValue (ofSequence s) i, forced := true,
              par := restrictedParent (Pseudo.forest (mountainOf s hs))
                (topValue (ofSequence s)) i }) := by
  have hpos : ∀ p, 0 < topValue (ofSequence s) p :=
    fun p => topValue_pos (ofSequence s) (ofSequence_positive s hs p)
  have hd := diagVals s hs fuel hf
  have ht := diagTree s hs fuel hf
  show (List.range ((diagList (calcMountain s (fuel + 1))).map Prod.fst).length).map _ = _
  rw [hd]
  simp only [List.length_map, List.length_range]
  refine List.map_congr_left ?_
  intro i hi
  have hin : i < s.length := List.mem_range.mp hi
  have htarget : ((List.range s.length).map (topValue (ofSequence s))).getD i 0
      = topValue (ofSequence s) i := getD_map_range s.length i _ 0 hin
  simp only [hd, ht, htarget]
  rw [treeScan_eq s hs (topValue (ofSequence s) i) (i + 1) i,
    chainFind_eq_restrictedParent (Pseudo.forest (mountainOf s hs))
      (topValue (ofSequence s)) hpos (i + 1) i (by omega),
    pwScan_eq s (topValue (ofSequence s) i) i (by omega),
    restrictedParent_linear (topValue (ofSequence s)) hpos i]

end Yukito
