import Equiv.Shape

/-!
# 山崎噴火の枝の組み立て

`expandJS` の `some` の枝のうち、`yama`（対角の最後の値が 1）の場合について、
`Copy.lean` で作った部品を繋ぐ。この枝は原文の層 `k = K`
（`badAtTerminalMountain`）にあたる。

まず出力の幅が仮定なしで定まることを示す。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- 山崎噴火の枝では切る段と bad root の段が一致する。 -/
theorem expP_yama_cut (M : List Rowj) (mfuel : Nat) (h : expYama M mfuel) :
    (expP M mfuel).cutHeight = (expP M mfuel).badRootHeight := by
  show (if expYama M mfuel then expCutH M - 1 else expCutH M)
      = (if expYama M mfuel then expCutH M - 1
         else (topRowWithCol M (expSeam M mfuel) M.length).getD 0)
  rw [if_pos h, if_pos h]

/-- **切る段は列 `n−1` の高さ。** -/
theorem expCutH_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n) :
    expCutH M = height S.tower.base (S.n - 1) := by
  unfold expCutH
  rw [hM.size0, topRowOfLast_eq S M hM hn M.length (Nat.le_refl _) (hM.tall _ (by omega))]
  rfl

/-- 切ったあとの列数は `n−1`。 -/
theorem expP_afterCutLength (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (h0 : 0 < (expRes M).length) : (expP M mfuel).afterCutLength = S.n - 1 :=
  size_rowAt_cutChild_zero S M hM (expCutH M) h0

theorem expRes_length_pos (M : List Rowj) (hM2 : 2 ≤ M.length) : 0 < (expRes M).length := by
  have := cutChild_length_ge M (expCutH M)
  show 0 < (cutChild M (expCutH M)).length
  omega

/-- **山崎噴火の枝での出力の形。** 幅は `(n−1) + len * nrep` で、仮定は
「列が 2 つ以上」「継ぎ目が `n−1` より左」「行 0 の最後のセルが親を持つ」だけ。 -/
theorem expandOut_some_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (nrep mfuel efuel : Nat) (hn : 1 < S.n) (hM2 : 2 ≤ M.length)
    (hyama : expYama M mfuel)
    (hsm : (expP M mfuel).badRootSeam < S.n - 1)
    (hhas : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true) :
    expandOut (expandJS nrep mfuel (efuel + 1) M)
      = (List.range ((S.n - 1) + (expP M mfuel).len * nrep)).map
          (fun c => valAtIdx (rowAt (expandJS nrep mfuel (efuel + 1) M) 0) c) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcut : (expP M mfuel).cutHeight = (expP M mfuel).badRootHeight :=
    expP_yama_cut M mfuel hyama
  have hlenpos : 0 < (expP M mfuel).len := by
    show 0 < (expP M mfuel).afterCutLength - (expP M mfuel).badRootSeam
    omega
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  have hkm : ∀ i' j', kmaxAt M (expP M mfuel) i' j' (expRes M).length mfuel
      ≤ j' + (expP M mfuel).len * i' + 1 :=
    fun i' j' => kmaxAt_le_yama' M (expP M mfuel) i' j' _ _ hcut
  have hkpos : ∀ i r, r < (expP M mfuel).len →
      0 < kmaxAt M (expP M mfuel) i ((expP M mfuel).badRootSeam + r)
        (expRes M).length mfuel := by
    intro i r hr
    exact kmaxAt_pos' S M hM (by omega) (expP M mfuel) i _ _ _ (by omega) h0
  have hmono : RowsMono (expRes M) :=
    rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM)
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq (expCutH_eq S M hM hn).symm)
  have hd0 : ∀ c, c < (expP M mfuel).afterCutLength → HasCol (expRes M) 0 c := by
    intro c hc
    rw [hacl] at hc
    exact hasCol_cutChild_zero S M hM (expCutH M) h0 (by omega) c hc
  have h := expandOut_some nrep mfuel efuel M hhas hkm hkpos hlenpos (by omega) hmono hcolLt hd0
  rw [hacl] at h
  exact h

/-! ## 切ったあとも段は足りている

切ると最上段が空になって段が 1 つ減ることがあるが、そのとき最上段には
列 `n−1` しか無かったのだから、それより左の列の高さは減った段数より小さい。 -/

/-- 生きている列が 2 つあれば、その段のセルは 2 つ以上。 -/
theorem two_cells (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat) (hr : r < M.length)
    (c1 c2 : Nat) (h1 : c1 < S.n) (h2 : c2 < S.n) (hne : c1 ≠ c2)
    (hl1 : 0 < (rows S.tower.base r).value c1) (hl2 : 0 < (rows S.tower.base r).value c2) :
    2 ≤ (rowAt M r).size := by
  have hrep := rep_top S M hM r hr
  have hr1 : r ≤ c1 := by
    rcases Nat.lt_or_ge c1 r with hx | hx
    · rw [rows_value_zero_of_lt S.tower.base r c1 hx] at hl1; omega
    · exact hx
  have hr2 : r ≤ c2 := by
    rcases Nat.lt_or_ge c2 r with hx | hx
    · rw [rows_value_zero_of_lt S.tower.base r c2 hx] at hl2; omega
    · exact hx
  obtain ⟨x1, hx1, hc1⟩ := hrep.cover c1 hr1 h1 hl1
  obtain ⟨x2, hx2, hc2⟩ := hrep.cover c2 hr2 h2 hl2
  obtain ⟨t1, ht1, he1⟩ := getElem_of_mem _ hx1
  obtain ⟨t2, ht2, he2⟩ := getElem_of_mem _ hx2
  have htne : t1 ≠ t2 := by
    intro h
    subst h
    have hxx : x1 = x2 := by rw [← he1, ← he2]
    rw [hxx] at hc1
    omega
  omega

/-- 生きている列があれば、その段のセルは 1 つ以上。 -/
theorem one_cell (S : Setting) (M : List Rowj) (hM : MtRep S M) (r : Nat) (hr : r < M.length)
    (c : Nat) (h : c < S.n) (hl : 0 < (rows S.tower.base r).value c) :
    1 ≤ (rowAt M r).size := by
  have hrep := rep_top S M hM r hr
  have hrc : r ≤ c := by
    rcases Nat.lt_or_ge c r with hx | hx
    · rw [rows_value_zero_of_lt S.tower.base r c hx] at hl; omega
    · exact hx
  obtain ⟨x1, hx1, _⟩ := hrep.cover c hrc h hl
  obtain ⟨t1, ht1, _⟩ := getElem_of_mem _ hx1
  omega

/-- **切ったあとも、列 `n−1` より左の列の高さは段の数より小さい。** -/
theorem height_lt_expRes_length (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (j : Nat) (hj : j < S.n - 1) :
    height S.tower.base j < (expRes M).length := by
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have htall := hM.tall j (by omega)
  have hge := cutChild_length_ge M (expCutH M)
  have hpf := popFold_length (expCutH M + 1) M
  show height S.tower.base j < (cutChild M (expCutH M)).length
  rcases Nat.lt_or_ge (height S.tower.base j) (M.length - 1) with h | h
  · omega
  · have heq : height S.tower.base j = M.length - 1 := by omega
    have hlive : 0 < (rows S.tower.base (M.length - 1)).value j := by
      refine (live_iff_le_height S.tower.base (S.tower.hpos j) (M.length - 1)).mpr ?_
      omega
    have hlen : (cutChild M (expCutH M)).length = M.length := by
      rw [cutChild_eq, if_neg ?_]
      · exact hpf
      · intro hc
        obtain ⟨_, hempty⟩ := hc
        rw [hpf, rowAt_popFold (expCutH M + 1) M (M.length - 1)] at hempty
        rcases Nat.lt_or_ge (M.length - 1) (expCutH M + 1) with hlt | hgeq
        · rw [if_pos hlt, Array.size_pop] at hempty
          have hlast : 0 < (rows S.tower.base (M.length - 1)).value (S.n - 1) := by
            refine (live_iff_le_height S.tower.base
              (S.tower.hpos (S.n - 1)) (M.length - 1)).mpr ?_
            omega
          have := two_cells S M hM (M.length - 1) (by omega) j (S.n - 1)
            (by omega) (by omega) (by omega) hlive hlast
          omega
        · rw [if_neg (by omega)] at hempty
          have := one_cell S M hM (M.length - 1) (by omega) j (by omega) hlive
          omega
    omega

/-! ## 積む段の数は「継ぎ目の列の高さ + 1」 -/

/-- **山崎噴火の枝では、継ぎ目の列 `j` について `kmax = height j + 1`。** -/
theorem kmaxAt_expRes_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel) (i j : Nat)
    (hj : j < S.n - 1) :
    kmaxAt M (expP M mfuel) i j (expRes M).length mfuel = height S.tower.base j + 1 := by
  rw [kmaxAt_yama M (expP M mfuel) i j _ _ (expP_yama_cut M mfuel hyama)]
  exact seamHeightOf_eq S M hM j (by omega) (expRes M).length
    (cutChild_length_le M (expCutH M)) (height_lt_expRes_length S M hM hn hM2 j hj)

/-- **コピーで作った列は「元の列の高さ」まで届く。** -/
theorem hasCol_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (nrep mfuel efuel : Nat) (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (m i j : Nat) (hi : 0 < i) (hin : i ≤ nrep)
    (hjy : (expP M mfuel).badRootSeam ≤ j) (hjx : j < S.n - 1)
    (hm : m ≤ height S.tower.base j)
    (h0 : 0 < (expRes M).length) :
    HasCol (fujiIters M (expP M mfuel) (expNd nrep mfuel efuel M) (expRes M).length mfuel nrep
      (expRes M)) m (j + (expP M mfuel).len * i) := by
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  refine hasCol_fujiIters M (expP M mfuel) (expNd nrep mfuel efuel M) (expRes M).length mfuel
    (fun i' j' => kmaxAt_le_yama' M (expP M mfuel) i' j' _ _ (expP_yama_cut M mfuel hyama))
    nrep (expRes M) m i j hi hin hjy (by omega) ?_
  rw [kmaxAt_expRes_eq S M hM mfuel hn hM2 hyama i j hjx]
  omega

/-! ## 山崎噴火の枝の判定は「頂の値が 1」

JS は対角の最後の値で分岐する。対角の値は `topValue` なので、これは
原文の「bad root がこの層で見つかる」と同じ条件である。 -/

/-- 行の最後の値は、最後の列の値。 -/
theorem lastVal_of_rep (row : Rowj) (n : Nat) (V : Nat → Nat) (h : Rep row 0 n V)
    (hn : 1 < n) (hlive : 0 < V (n - 1)) : lastVal row = V (n - 1) := by
  obtain ⟨x, hx, hcx⟩ := h.cover (n - 1) (Nat.zero_le _) (by omega) hlive
  obtain ⟨t, ht, het⟩ := getElem_of_mem _ hx
  have hne : 0 < row.size := by omega
  have hlt : row.size - 1 < row.size := by omega
  have hmax := lastCol_max row 0 h.posMono hne t ht
  simp only [lastCol, dif_pos hne] at hmax
  rw [het] at hmax
  have hb := h.bound _ (mem_of_getElem row (row.size - 1) hlt)
  have hpe : (row[row.size - 1]'hlt).pos = n - 1 := by omega
  simp only [lastVal, dif_pos hne]
  rw [h.val _ (mem_of_getElem row (row.size - 1) hlt), hpe]
  rfl

/-- **対角の最後の値は最後の列の `topValue`。** -/
theorem lastVal_expDg (S : Setting) (M : List Rowj) (hM : MtRep S M) (f : Nat) (hn : 1 < S.n) :
    lastVal (rowAt (expDg M (f + 1)) 0) = topValue S.tower.base (S.n - 1) := by
  show lastVal (rowAt (calcMountainFrom (parseDiag (calcDiagonal M)) (f + 1)) 0) = _
  rw [rowAt_calcMountainFrom_zero]
  exact lastVal_of_rep _ S.n _ (rep_extract S M hM) hn
    (topValue_pos S.tower.base (S.tower.hpos (S.n - 1)))

/-- **JS の分岐条件は「頂の値が 1」。** 原文の `badRootOf` が
その層で止まる条件と同じである。 -/
theorem expYama_iff (S : Setting) (M : List Rowj) (hM : MtRep S M) (f : Nat) (hn : 1 < S.n) :
    expYama M (f + 1) ↔ topValue S.tower.base (S.n - 1) = 1 := by
  show lastVal (rowAt (expDg M (f + 1)) 0) = 1 ↔ _
  rw [lastVal_expDg S M hM f hn]

/-! ## 山崎噴火の枝の bad root

この枝では bad root はその層で見つかる。すなわち「頂の 1 つ下の段での、
最後の列の親」である。 -/

theorem getBadRoot_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (m : Nat)
    (hbnd : S.bnd ≤ m) (hn : 1 < S.n) (hgt : 1 < S.tower.base.value (S.n - 1))
    (hyama : topValue S.tower.base (S.n - 1) = 1) :
    getBadRoot M (m + 1) (m + 1)
      = (rows S.tower.base (height S.tower.base (S.n - 1) - 1)).forest.parent (S.n - 1) := by
  rw [getBadRoot_eq m (m + 1) S M hM hbnd hn hgt]
  show (if topValue S.tower.base (S.n - 1) = 1 then _ else _) = _
  rw [if_pos hyama]

/-- **山崎噴火の枝の継ぎ目は、山の最後の列の親である。** -/
theorem expSeam_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (m : Nat)
    (hbnd : S.bnd ≤ m) (hn : 1 < S.n) (hgt : 1 < S.tower.base.value (S.n - 1))
    (hyama : topValue S.tower.base (S.n - 1) = 1) (y : Nat)
    (hy : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1)
      = some y) :
    expSeam M (m + 1) = y := by
  show (getBadRoot M (m + 1) (m + 1)).getD 0 = y
  rw [getBadRoot_yama S M hM m hbnd hn hgt hyama]
  have hy' : (rows S.tower.base (height S.tower.base (S.n - 1) - 1)).forest.parent (S.n - 1)
      = some y := hy
  rw [hy']
  rfl

/-- 山の高さと段。`TerminalCopy.Context` の `last_height` にあたる。 -/
theorem mountainOf'_height (S : Setting) (c : Nat) :
    (mountainOf' S).height c = height S.tower.base c := rfl

theorem mountainOf'_row (S : Setting) (r : Nat) :
    (mountainOf' S).row r = (rows S.tower.base r).forest := rfl

/-! ## 山崎噴火の枝のコピー先の山

原文の `TerminalCopy.Context` を、こちらの `Setting` から組み立てる。
これが `badAtTerminalMountain` にあたる山である。 -/

/-- 山崎噴火の枝で使う `TerminalCopy.Context`。 -/
def yamaContext (S : Setting) (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1)) : TerminalCopy.Context where
  mountain := mountainOf' S
  coordinates := ⟨y, S.n - 1, hy⟩
  level := height S.tower.base (S.n - 1) - 1
  last_parent := hpar
  last_height := by
    show height S.tower.base (S.n - 1) = height S.tower.base (S.n - 1) - 1 + 1
    omega

theorem yamaContext_height (S : Setting) (y : Nat) (hy hpar hh) (c : Nat) :
    ((yamaContext S y hy hpar hh).toRowMountain).height c
      = (yamaContext S y hy hpar hh).height c := rfl

theorem yamaContext_row (S : Setting) (y : Nat) (hy hpar hh) (r c : Nat) :
    (((yamaContext S y hy hpar hh).toRowMountain).row r).parent c
      = (yamaContext S y hy hpar hh).parent r c := rfl

theorem yamaContext_y (S : Setting) (y : Nat) (hy hpar hh) :
    (yamaContext S y hy hpar hh).coordinates.y = y := rfl

theorem yamaContext_x (S : Setting) (y : Nat) (hy hpar hh) :
    (yamaContext S y hy hpar hh).coordinates.x = S.n - 1 := rfl

theorem yamaContext_level (S : Setting) (y : Nat) (hy hpar hh) :
    (yamaContext S y hy hpar hh).level = height S.tower.base (S.n - 1) - 1 := rfl

theorem yamaContext_length (S : Setting) (y : Nat) (hy hpar hh) :
    (yamaContext S y hy hpar hh).coordinates.length = S.n - 1 - y := rfl

/-! ## コピー先の山の高さ

原文の `TerminalCopy.height` は 3 つに分かれるが、コピーで作る列
`j + L*i`（`y ≤ j < x`）についてはどれも「元の列 `j` の高さ」になる。 -/

theorem yamaContext_height_orig (S : Setting) (y : Nat) (hy hpar hh) (c : Nat)
    (hc : c < S.n - 1) :
    (yamaContext S y hy hpar hh).height c = height S.tower.base c :=
  (yamaContext S y hy hpar hh).height_original hc

theorem yamaContext_height_seam (S : Setting) (y : Nat) (hy hpar hh) (i : Nat) (hi : 0 < i) :
    (yamaContext S y hy hpar hh).height
        ((yamaContext S y hy hpar hh).coordinates.y
          + (yamaContext S y hy hpar hh).coordinates.length * i)
      = height S.tower.base y := by
  obtain ⟨hsrc, _⟩ := coord_source_block_seam (yamaContext S y hy hpar hh).coordinates i hi
  have hL := (yamaContext S y hy hpar hh).coordinates.root_add_length
  have hmul : (yamaContext S y hy hpar hh).coordinates.length * 1
      ≤ (yamaContext S y hy hpar hh).coordinates.length * i := Nat.mul_le_mul_left _ hi
  have hone : (yamaContext S y hy hpar hh).coordinates.length * 1
      = (yamaContext S y hy hpar hh).coordinates.length := Nat.mul_one _
  unfold TerminalCopy.Context.height
  rw [if_neg (by omega), if_pos hsrc]
  rfl

theorem yamaContext_height_other (S : Setting) (y : Nat) (hy hpar hh) (j i : Nat)
    (hj1 : y < j) (hj2 : j < S.n - 1) :
    (yamaContext S y hy hpar hh).height
        (j + (yamaContext S y hy hpar hh).coordinates.length * i)
      = height S.tower.base j := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.mul_zero, Nat.add_zero]
    exact yamaContext_height_orig S y hy hpar hh j hj2
  · obtain ⟨hsrc, _⟩ := coord_source_block (yamaContext S y hy hpar hh).coordinates j i
      hj1 hj2
    have hL := (yamaContext S y hy hpar hh).coordinates.root_add_length
    have hmul : (yamaContext S y hy hpar hh).coordinates.length * 1
        ≤ (yamaContext S y hy hpar hh).coordinates.length * i := Nat.mul_le_mul_left _ hi
    have hone : (yamaContext S y hy hpar hh).coordinates.length * 1
        = (yamaContext S y hy hpar hh).coordinates.length := Nat.mul_one _
    have hyy : (yamaContext S y hy hpar hh).coordinates.y = y := rfl
    have hxx : (yamaContext S y hy hpar hh).coordinates.x = S.n - 1 := rfl
    unfold TerminalCopy.Context.height
    rw [if_neg (by omega), if_neg (by rw [hsrc]; omega), hsrc]
    rfl

/-! ## コピー先の山の親

原文の `TerminalCopy.parent` の 3 分岐が、JS の枝と 1 対 1 に対応する。 -/

theorem yamaContext_parent_orig (S : Setting) (y : Nat) (hy hpar hh) (r c : Nat)
    (hc : c < S.n - 1) :
    (yamaContext S y hy hpar hh).parent r c = (rows S.tower.base r).forest.parent c :=
  (yamaContext S y hy hpar hh).parent_original hc r

/-- 置き換えの継ぎ目、`level` より下の段。元の列は最後の列 `x`、桁上げは `i−1`。 -/
theorem yamaContext_parent_seam_low (S : Setting) (y : Nat) (hy hpar hh) (r i : Nat)
    (hi : 0 < i) (hr : r < height S.tower.base (S.n - 1) - 1) :
    (yamaContext S y hy hpar hh).parent r
        ((yamaContext S y hy hpar hh).coordinates.y
          + (yamaContext S y hy hpar hh).coordinates.length * i)
      = ((rows S.tower.base r).forest.parent (S.n - 1)).map
          ((yamaContext S y hy hpar hh).coordinates.parentCopy (i - 1)) := by
  obtain ⟨hsrc, hblk⟩ := coord_source_block_seam (yamaContext S y hy hpar hh).coordinates i hi
  have hL := (yamaContext S y hy hpar hh).coordinates.root_add_length
  have hmul : (yamaContext S y hy hpar hh).coordinates.length * 1
      ≤ (yamaContext S y hy hpar hh).coordinates.length * i := Nat.mul_le_mul_left _ hi
  have hone : (yamaContext S y hy hpar hh).coordinates.length * 1
      = (yamaContext S y hy hpar hh).coordinates.length := Nat.mul_one _
  have hlv : (yamaContext S y hy hpar hh).level = height S.tower.base (S.n - 1) - 1 := rfl
  unfold TerminalCopy.Context.parent
  rw [if_neg (by omega), if_neg (by rintro ⟨_, h2⟩; rw [hlv] at h2; omega), hsrc, hblk]
  rfl

/-- 置き換えの継ぎ目、`level` 以上の段。元の列は根 `y`、桁上げは無し。 -/
theorem yamaContext_parent_seam_high (S : Setting) (y : Nat) (hy hpar hh) (r i : Nat)
    (hi : 0 < i) (hr : height S.tower.base (S.n - 1) - 1 ≤ r) :
    (yamaContext S y hy hpar hh).parent r
        ((yamaContext S y hy hpar hh).coordinates.y
          + (yamaContext S y hy hpar hh).coordinates.length * i)
      = (rows S.tower.base r).forest.parent y := by
  obtain ⟨hsrc, _⟩ := coord_source_block_seam (yamaContext S y hy hpar hh).coordinates i hi
  have hL := (yamaContext S y hy hpar hh).coordinates.root_add_length
  have hmul : (yamaContext S y hy hpar hh).coordinates.length * 1
      ≤ (yamaContext S y hy hpar hh).coordinates.length * i := Nat.mul_le_mul_left _ hi
  have hone : (yamaContext S y hy hpar hh).coordinates.length * 1
      = (yamaContext S y hy hpar hh).coordinates.length := Nat.mul_one _
  have hlv : (yamaContext S y hy hpar hh).level = height S.tower.base (S.n - 1) - 1 := rfl
  unfold TerminalCopy.Context.parent
  rw [if_neg (by omega), if_pos ⟨hsrc, by rw [hlv]; omega⟩]
  rfl

/-- 置き換えでない継ぎ目。元の列は `j`、桁上げは `i`。 -/
theorem yamaContext_parent_other (S : Setting) (y : Nat) (hy hpar hh) (r j i : Nat)
    (hj1 : y < j) (hj2 : j < S.n - 1) :
    (yamaContext S y hy hpar hh).parent r
        (j + (yamaContext S y hy hpar hh).coordinates.length * i)
      = ((rows S.tower.base r).forest.parent j).map
          ((yamaContext S y hy hpar hh).coordinates.parentCopy i) := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.mul_zero, Nat.add_zero, yamaContext_parent_orig S y hy hpar hh r j hj2]
    cases (rows S.tower.base r).forest.parent j with
    | none => rfl
    | some p =>
        simp only [Option.map_some]
        rw [(yamaContext S y hy hpar hh).coordinates.parentCopy_zero]
  · obtain ⟨hsrc, hblk⟩ := coord_source_block (yamaContext S y hy hpar hh).coordinates j i
      hj1 hj2
    have hL := (yamaContext S y hy hpar hh).coordinates.root_add_length
    have hmul : (yamaContext S y hy hpar hh).coordinates.length * 1
        ≤ (yamaContext S y hy hpar hh).coordinates.length * i := Nat.mul_le_mul_left _ hi
    have hone : (yamaContext S y hy hpar hh).coordinates.length * 1
        = (yamaContext S y hy hpar hh).coordinates.length := Nat.mul_one _
    have hyy : (yamaContext S y hy hpar hh).coordinates.y = y := rfl
    have hxx : (yamaContext S y hy hpar hh).coordinates.x = S.n - 1 := rfl
    unfold TerminalCopy.Context.parent
    rw [if_neg (by omega), if_neg (by rintro ⟨h1, _⟩; rw [hsrc] at h1; omega), hsrc, hblk]
    rfl

end Yukito
