import Equiv.Shape
import OneY.TowerCopyAssembly

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

/-- **切ったあとの山でも `seamHeight` は「列の高さ + 1」。** 枝によらない。 -/
theorem seamHeightOf_expRes (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (j : Nat) (hj : j < S.n - 1) :
    seamHeightOf M j (expRes M).length = height S.tower.base j + 1 :=
  seamHeightOf_eq S M hM j (by omega) (expRes M).length
    (cutChild_length_le M (expCutH M)) (height_lt_expRes_length S M hM hn hM2 j hj)

/-- **山崎噴火の枝では、継ぎ目の列 `j` について `kmax = height j + 1`。** -/
theorem kmaxAt_expRes_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel) (i j : Nat)
    (hj : j < S.n - 1) :
    kmaxAt M (expP M mfuel) i j (expRes M).length mfuel = height S.tower.base j + 1 := by
  rw [kmaxAt_yama M (expP M mfuel) i j _ _ (expP_yama_cut M mfuel hyama)]
  exact seamHeightOf_expRes S M hM hn hM2 j hj

/-- **コピーで作った列は「元の列の高さ」まで届く。** -/
theorem hasCol_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (nrep mfuel : Nat) (nd : Nat → Nat) (hn : 1 < S.n) (hM2 : 2 ≤ M.length)
    (hyama : expYama M mfuel)
    (m i j : Nat) (hi : 0 < i) (hin : i ≤ nrep)
    (hjy : (expP M mfuel).badRootSeam ≤ j) (hjx : j < S.n - 1)
    (hm : m ≤ height S.tower.base j)
    (h0 : 0 < (expRes M).length) :
    HasCol (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep
      (expRes M)) m (j + (expP M mfuel).len * i) := by
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  refine hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel
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

/-! ## `expP` の各成分（山崎噴火の枝） -/

theorem expP_badRootHeight_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (mfuel : Nat) (hyama : expYama M mfuel) :
    (expP M mfuel).badRootHeight = height S.tower.base (S.n - 1) - 1 := by
  show (if expYama M mfuel then expCutH M - 1
        else (topRowWithCol M (expSeam M mfuel) M.length).getD 0) = _
  rw [if_pos hyama, expCutH_eq S M hM hn]

theorem expP_yamakazi (M : List Rowj) (mfuel : Nat) (hyama : expYama M mfuel) :
    (expP M mfuel).yamakazi = true := decide_eq_true hyama

theorem expP_len_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (h0 : 0 < (expRes M).length) (y : Nat) (hseam : (expP M mfuel).badRootSeam = y) :
    (expP M mfuel).len = S.n - 1 - y := by
  show (expP M mfuel).afterCutLength - (expP M mfuel).badRootSeam = S.n - 1 - y
  rw [expP_afterCutLength S M hM mfuel h0, hseam]

/-! ## 素の形での言い換え -/

theorem yamaContext_height_seam' (S : Setting) (y : Nat) (hy hpar hh) (i : Nat) (hi : 0 < i) :
    (yamaContext S y hy hpar hh).height (y + (S.n - 1 - y) * i) = height S.tower.base y :=
  yamaContext_height_seam S y hy hpar hh i hi

theorem yamaContext_height_other' (S : Setting) (y : Nat) (hy hpar hh) (j i : Nat)
    (hj1 : y < j) (hj2 : j < S.n - 1) :
    (yamaContext S y hy hpar hh).height (j + (S.n - 1 - y) * i) = height S.tower.base j :=
  yamaContext_height_other S y hy hpar hh j i hj1 hj2

theorem yamaContext_parent_seam_low' (S : Setting) (y : Nat) (hy hpar hh) (r i : Nat)
    (hi : 0 < i) (hr : r < height S.tower.base (S.n - 1) - 1) :
    (yamaContext S y hy hpar hh).parent r (y + (S.n - 1 - y) * i)
      = ((rows S.tower.base r).forest.parent (S.n - 1)).map
          ((yamaContext S y hy hpar hh).coordinates.parentCopy (i - 1)) :=
  yamaContext_parent_seam_low S y hy hpar hh r i hi hr

theorem yamaContext_parent_seam_high' (S : Setting) (y : Nat) (hy hpar hh) (r i : Nat)
    (hi : 0 < i) (hr : height S.tower.base (S.n - 1) - 1 ≤ r) :
    (yamaContext S y hy hpar hh).parent r (y + (S.n - 1 - y) * i)
      = (rows S.tower.base r).forest.parent y :=
  yamaContext_parent_seam_high S y hy hpar hh r i hi hr

theorem yamaContext_parent_other' (S : Setting) (y : Nat) (hy hpar hh) (r j i : Nat)
    (hj1 : y < j) (hj2 : j < S.n - 1) :
    (yamaContext S y hy hpar hh).parent r (j + (S.n - 1 - y) * i)
      = ((rows S.tower.base r).forest.parent j).map
          ((yamaContext S y hy hpar hh).coordinates.parentCopy i) :=
  yamaContext_parent_other S y hy hpar hh r j i hj1 hj2

/-! ## **JS の親と原文の親が一致する（山崎噴火の枝）** -/

theorem fujiCellAt_parCol_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (mfuel : Nat) (hn : 1 < S.n) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (h0 : 0 < (expRes M).length)
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (res : List Rowj) (i j k : Nat)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < S.n - 1)
    (hk : k < M.length) (hkj : k ≤ j)
    (hlive : 0 < (rows S.tower.base k).value j)
    (p : Nat)
    (isAsc : Bool) (hra : isRepAt (expP M mfuel) j = true → isAsc = true)
    (hp : (fujiCellAt M (expP M mfuel) nd i j (isRepAt (expP M mfuel) j) isAsc res k).par
      = some p) :
    ∃ hp' : p < (rowAt res k).size,
      (yamaContext S y hy hpar hh).parent k (j + (S.n - 1 - y) * i)
        = some (((rowAt res k)[p]'hp').pos + k) := by
  have hbh : (expP M mfuel).badRootHeight = height S.tower.base (S.n - 1) - 1 :=
    expP_badRootHeight_yama S M hM hn mfuel hyama
  have hcy : (yamaContext S y hy hpar hh).coordinates.y = (expP M mfuel).badRootSeam := by
    rw [hseam]
    rfl
  have hcL : (yamaContext S y hy hpar hh).coordinates.length = (expP M mfuel).len := by
    rw [expP_len_yama S M hM mfuel h0 y hseam]
    rfl
  obtain ⟨hp', q, hq, hcol⟩ :=
    fujiCellAt_par_yama S M hM (expP M mfuel) nd i j (isRepAt (expP M mfuel) j) isAsc res k
      (expP_yamakazi M mfuel hyama) (expP_yama_cut M mfuel hyama) hk hn hkj (by omega)
      hlive (by rw [hbh]; omega) hra (yamaContext S y hy hpar hh).coordinates hcy hcL p hp
  refine ⟨hp', ?_⟩
  rcases Decidable.em (j = y) with hjeq | hjne
  · have hrep : isRepAt (expP M mfuel) j = true := by
      show decide (j = (expP M mfuel).badRootSeam) = true
      rw [hseam, hjeq]
      simp
    rw [hrep] at hcol hq
    have hir : i - (if (true : Bool) then 1 else 0) = i - 1 := by simp
    rw [hir] at hcol
    rcases Nat.lt_or_ge k (expP M mfuel).badRootHeight with hkb | hkb
    · have hsrc : srcColYama S (expP M mfuel) j k true = S.n - 1 := by
        show (if (true && decide (k < (expP M mfuel).badRootHeight)) = true
              then S.n - 1 else j) = _
        rw [if_pos (by simp [hkb])]
      rw [hsrc] at hq
      rw [hjeq, yamaContext_parent_seam_low' S y hy hpar hh k i hi (by omega), hq, hcol]
      rfl
    · have hsrc : srcColYama S (expP M mfuel) j k true = j := by
        show (if (true && decide (k < (expP M mfuel).badRootHeight)) = true
              then S.n - 1 else j) = _
        rw [if_neg (by simp [Nat.not_lt.mpr hkb])]
      rw [hsrc, hjeq] at hq
      have hqy : (rows S.tower.base k).forest.parent
          (yamaContext S y hy hpar hh).coordinates.y = some q := hq
      rw [hjeq, yamaContext_parent_seam_high' S y hy hpar hh k i hi (by omega), hq, hcol,
        parentCopy_of_parent_y _ _ q hqy]
  · have hrep : isRepAt (expP M mfuel) j = false := by
      show decide (j = (expP M mfuel).badRootSeam) = false
      rw [hseam]
      simp [hjne]
    rw [hrep] at hcol hq
    have hir : i - (if (false : Bool) then 1 else 0) = i := by simp
    rw [hir] at hcol
    have hsrc : srcColYama S (expP M mfuel) j k false = j := by
      show (if (false && decide (k < (expP M mfuel).badRootHeight)) = true
            then S.n - 1 else j) = _
      rw [if_neg (by simp)]
    rw [hsrc] at hq
    rw [yamaContext_parent_other' S y hy hpar hh k j i (by omega) hjx, hq, hcol]
    rfl

/-! ## 積む時点での被覆

`(i'+1, y+t)` を処理する直前の段 `k` には、`pc < (y+t) + L*(i'+1)` かつ
`k ≤ height_G pc` を満たす列 `pc` がすべて載っている。積む列が `(i, j)` の
辞書式順で真に増えるからである。 -/

theorem hasCol_state (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (i' t k pc : Nat) (ht : t < (expP M mfuel).len)
    (hlt : pc < (y + t) + (expP M mfuel).len * (i' + 1))
    (hk : k ≤ (yamaContext S y hy hpar hh).height pc) :
    HasCol (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) k pc := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama)
  rcases Nat.lt_or_ge pc (S.n - 1) with hpc | hpc
  · -- 元からある列
    have hkh : k ≤ height S.tower.base pc := by
      rwa [yamaContext_height_orig S y hy hpar hh pc hpc] at hk
    have hkl : k < (expRes M).length := by
      have := height_lt_expRes_length S M hM hn hM2 pc hpc
      omega
    have hres : HasCol (expRes M) k pc :=
      hasCol_cutChild S M hM hn (expCutH M) hcut k pc hpc hkh hkl
    exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
      (hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M) k pc hres)
  · -- コピーで作った列
    obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hpceq⟩ :=
      col_decomp y (S.n - 1) (expP M mfuel).len (i' + 1) pc hLp (by omega) (by omega) hpc
        (by omega)
    have hkh : k ≤ height S.tower.base j2 := by
      have hpc' : pc = j2 + (S.n - 1 - y) * i2 := by rw [hpceq, hLp]
      rcases Decidable.em (j2 = y) with hje | hjne
      · rw [hpc', hje] at hk
        rw [yamaContext_height_seam' S y hy hpar hh i2 hi2] at hk
        rw [hje]
        exact hk
      · rw [hpc'] at hk
        rwa [yamaContext_height_other' S y hy hpar hh j2 i2 (by omega) hj2x] at hk
    have hkmax : k < kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel := by
      rw [kmaxAt_expRes_eq S M hM mfuel hn hM2 hyama i2 j2 hj2x]
      omega
    rcases col_lt_lex y (S.n - 1) (expP M mfuel).len hLp (by omega) j2 i2 (y + t) (i' + 1)
      hj2y hj2x (by omega) (by omega) (by omega) with hlex | ⟨hie, hje⟩
    · rw [hpceq]
      exact HasCol.ext (rowExt_fujiSeams _ _ _ _ _ _ _ _ _)
        (hasCol_fujiIters M (expP M mfuel) nd (expRes M).length mfuel hkm i' (expRes M) k i2 j2
          hi2 (by omega) (by omega) (by omega) hkmax)
    · rw [hpceq, hie]
      exact hasCol_fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel hkm t
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M)) k j2
        (by omega) (by omega) (by rw [← hie]; exact hkmax)

/-! ## 元の列を密表現の言葉で

JS の `srcColYama` を、`Setting` と継ぎ目 `y` だけで書いた形。 -/

/-- 元の列。置き換えの継ぎ目で `level` より下なら最後の列、そうでなければ `j`。 -/
def srcColY (S : Setting) (y j k : Nat) : Nat :=
  if j = y ∧ k < height S.tower.base (S.n - 1) - 1 then S.n - 1 else j

theorem srcColYama_eq (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (mfuel : Nat) (hyama : expYama M mfuel) (y : Nat)
    (hseam : (expP M mfuel).badRootSeam = y) (j k : Nat) :
    srcColYama S (expP M mfuel) j k (isRepAt (expP M mfuel) j) = srcColY S y j k := by
  have hbh := expP_badRootHeight_yama S M hM hn mfuel hyama
  show (if (isRepAt (expP M mfuel) j && decide (k < (expP M mfuel).badRootHeight)) = true
        then S.n - 1 else j) = _
  unfold srcColY
  rcases Decidable.em (j = y) with hje | hjne
  · have hrep : isRepAt (expP M mfuel) j = true := by
      show decide (j = (expP M mfuel).badRootSeam) = true
      rw [hseam, hje]
      simp
    rw [hrep, hbh]
    rcases Nat.lt_or_ge k (height S.tower.base (S.n - 1) - 1) with hk | hk
    · rw [if_pos (by simp [hk]), if_pos ⟨hje, hk⟩]
    · rw [if_neg (by simp [Nat.not_lt.mpr hk]), if_neg (by rintro ⟨_, h2⟩; omega)]
  · have hrep : isRepAt (expP M mfuel) j = false := by
      show decide (j = (expP M mfuel).badRootSeam) = false
      rw [hseam]
      simp [hjne]
    rw [hrep, if_neg (by simp), if_neg (by rintro ⟨h1, _⟩; exact hjne h1)]

theorem parentCopy_eq (C : CopyCoordinates.Context) (b p : Nat) :
    C.parentCopy b p = p + (if C.y ≤ p then b * C.length else 0) :=
  (js_shift_eq_parentCopy C b p).symm

/-- **原文の親から、元の列とその親を取り出す。** -/
theorem yamaContext_parent_src (S : Setting) (y : Nat) (hy hpar hh) (k i j pc : Nat)
    (hi : 0 < i) (hjy : y ≤ j) (hjx : j < S.n - 1)
    (hpc : (yamaContext S y hy hpar hh).parent k (j + (S.n - 1 - y) * i) = some pc) :
    ∃ q, (rows S.tower.base k).forest.parent (srcColY S y j k) = some q ∧
      pc = q + (if y ≤ q then (i - (if j = y then 1 else 0)) * (S.n - 1 - y) else 0) := by
  have hcy : (yamaContext S y hy hpar hh).coordinates.y = y := rfl
  have hcl : (yamaContext S y hy hpar hh).coordinates.length = S.n - 1 - y := rfl
  unfold srcColY
  rcases Decidable.em (j = y) with hje | hjne
  · rcases Nat.lt_or_ge k (height S.tower.base (S.n - 1) - 1) with hk | hk
    · rw [if_pos ⟨hje, hk⟩, if_pos hje]
      rw [hje, yamaContext_parent_seam_low' S y hy hpar hh k i hi hk] at hpc
      obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
      refine ⟨q, hq, ?_⟩
      rw [← hqe, parentCopy_eq, hcy, hcl]
    · rw [hje, if_neg (by rintro ⟨_, h2⟩; omega), if_pos rfl]
      rw [hje, yamaContext_parent_seam_high' S y hy hpar hh k i hi hk] at hpc
      refine ⟨pc, hpc, ?_⟩
      have hlt := (rows S.tower.base k).forest.parent_left hpc
      rw [if_neg (by omega)]
      omega
  · rw [if_neg (by rintro ⟨h1, _⟩; exact hjne h1), if_neg hjne]
    rw [yamaContext_parent_other' S y hy hpar hh k j i (by omega) hjx] at hpc
    obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hpc
    refine ⟨q, hq, ?_⟩
    rw [← hqe, parentCopy_eq, hcy, hcl, Nat.sub_zero]

/-! ## **原文に親があれば JS も親を持つ** -/

theorem fujiCellAt_par_some_of_parent (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (mfuel : Nat) (hn : 1 < S.n) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (h0 : 0 < (expRes M).length)
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (st : List Rowj) (i t k pc : Nat) (isAsc : Bool)
    (hra : isRepAt (expP M mfuel) (y + t) = true → isAsc = true)
    (hi : 0 < i) (ht : t < (expP M mfuel).len)
    (hk : k < M.length) (hkj : k ≤ y + t)
    (hlivej : 0 < (rows S.tower.base k).value (y + t))
    (hmono : PosMono (rowAt st k))
    (hpc : (yamaContext S y hy hpar hh).parent k ((y + t) + (expP M mfuel).len * i) = some pc)
    (hcov : HasCol st k pc) :
    ∃ u, (fujiCellAt M (expP M mfuel) nd i (y + t) (isRepAt (expP M mfuel) (y + t))
      isAsc st k).par = some u := by
  have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
  have hpc' : (yamaContext S y hy hpar hh).parent k ((y + t) + (S.n - 1 - y) * i) = some pc := by
    rwa [hLp] at hpc
  obtain ⟨q, hq, hpceq⟩ :=
    yamaContext_parent_src S y hy hpar hh k i (y + t) pc hi (by omega) (by omega) hpc'
  -- 親の新しい列は段より右
  have hpcge : k ≤ pc := by
    have h1 : k ≤ ((yamaContext S y hy hpar hh).toRowMountain).height pc :=
      ((yamaContext S y hy hpar hh).toRowMountain).parent_endpoint hpc'
    have h2 := rowMountain_height_le ((yamaContext S y hy hpar hh).toRowMountain) pc
    omega
  -- 元のセルの列
  have hbh : (expP M mfuel).badRootHeight = height S.tower.base (S.n - 1) - 1 :=
    expP_badRootHeight_yama S M hM hn mfuel hyama
  obtain ⟨hsx, hcolsrc⟩ :=
    sourceIdx_yama_col S M hM (expP M mfuel) (y + t) k (isRepAt (expP M mfuel) (y + t))
      hk hn hkj (by omega) hlivej (by rw [hbh]; omega)
  rw [srcColYama_eq S M hM hn mfuel hyama y hseam (y + t) k] at hcolsrc
  have hF : (rows S.tower.base k).forest.parent
      (((rowAt M k)[sourceIdx M k (y + t)
        (isRepAt (expP M mfuel) (y + t) && decide (k < (expP M mfuel).badRootHeight))]'hsx).pos
        + k) = some q := by
    rw [hcolsrc]
    exact hq
  -- 桁上げの形を揃える
  have hir : (i - (if isRepAt (expP M mfuel) (y + t) then 1 else 0))
      = (i - (if (y + t) = y then 1 else 0)) := by
    show (i - (if (decide ((y + t) = (expP M mfuel).badRootSeam)) = true then 1 else 0)) = _
    rw [hseam]
    simp
  have hge : k ≤ q + (if (expP M mfuel).badRootSeam ≤ q then
      (i - (if isRepAt (expP M mfuel) (y + t) then 1 else 0)) * (expP M mfuel).len else 0) := by
    rw [hseam, hir, hLp]
    omega
  have hpp := parentPos_some S M hM (expP M mfuel) k _ k
    (i - (if isRepAt (expP M mfuel) (y + t) then 1 else 0)) q hk hsx (Nat.le_refl _) hF hge
  rw [← hir] at hpceq
  rw [hseam, hLp, ← hpceq] at hpp
  -- 親の列は今の段にある
  obtain ⟨u, hu, hupos⟩ := hasCol_pos st k pc hcov
  refine ⟨u, ?_⟩
  refine fujiCellAt_par_isSome M (expP M mfuel) nd i (y + t)
    (isRepAt (expP M mfuel) (y + t)) isAsc st k (pc - k) hmono ?_ u hu (by omega)
  rw [fujiSourceAt_yama (expP M mfuel) (expP_yamakazi M mfuel hyama)
    (expP_yama_cut M mfuel hyama) i k (isRepAt (expP M mfuel) (y + t)) isAsc hra]
  exact hpp

/-- **`ShapeRep` の `parNone`（対偶を取った形）。** -/
theorem fujiCellAt_parNone_yama (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (mfuel : Nat) (hn : 1 < S.n) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (h0 : 0 < (expRes M).length)
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (st : List Rowj) (i t k : Nat) (isAsc : Bool)
    (hra : isRepAt (expP M mfuel) (y + t) = true → isAsc = true)
    (hi : 0 < i) (ht : t < (expP M mfuel).len)
    (hk : k < M.length) (hkj : k ≤ y + t)
    (hlivej : 0 < (rows S.tower.base k).value (y + t))
    (hmono : PosMono (rowAt st k))
    (hcov : ∀ pc, pc < (y + t) + (expP M mfuel).len * i →
      k ≤ (yamaContext S y hy hpar hh).height pc → HasCol st k pc)
    (hnone : (fujiCellAt M (expP M mfuel) nd i (y + t) (isRepAt (expP M mfuel) (y + t))
      isAsc st k).par = none) :
    (yamaContext S y hy hpar hh).parent k ((y + t) + (expP M mfuel).len * i) = none := by
  cases hp : (yamaContext S y hy hpar hh).parent k ((y + t) + (expP M mfuel).len * i) with
  | none => rfl
  | some pc =>
      exfalso
      have hlt : pc < (y + t) + (expP M mfuel).len * i :=
        (((yamaContext S y hy hpar hh).toRowMountain).row k).parent_left hp
      have hge : k ≤ (yamaContext S y hy hpar hh).height pc :=
        ((yamaContext S y hy hpar hh).toRowMountain).parent_endpoint hp
      obtain ⟨u, hu⟩ := fujiCellAt_par_some_of_parent S M hM mfuel hn hyama y hy hpar hh h0
        hseam nd st i t k pc isAsc hra hi ht hk hkj hlivej hmono hp (hcov pc hlt hge)
      rw [hu] at hnone
      exact absurd hnone (by simp)

/-! ## `ShapeRep` の `cover` -/

/-- **高さ `m` 以上の列は段 `m` に載る。** -/
theorem cover_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep m c : Nat)
    (hc : c < (S.n - 1) + (expP M mfuel).len * nrep)
    (hm : m ≤ (yamaContext S y hy hpar hh).height c) :
    HasCol (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)) m c := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  rcases Nat.lt_or_ge c (S.n - 1) with hcx | hcx
  · have hkh : m ≤ height S.tower.base c := by
      rwa [yamaContext_height_orig S y hy hpar hh c hcx] at hm
    have hml : m < (expRes M).length := by
      have := height_lt_expRes_length S M hM hn hM2 c hcx
      omega
    exact hasCol_fujiIters_old M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m c
      (hasCol_cutChild S M hM hn (expCutH M) hcut m c hcx hkh hml)
  · obtain ⟨i2, j2, hi2, hi2n, hj2y, hj2x, hceq⟩ :=
      col_decomp y (S.n - 1) (expP M mfuel).len nrep c hLp (by omega) (by omega) hcx (by omega)
    have hkh : m ≤ height S.tower.base j2 := by
      have hc' : c = j2 + (S.n - 1 - y) * i2 := by rw [hceq, hLp]
      rcases Decidable.em (j2 = y) with hje | hjne
      · rw [hc', hje] at hm
        rw [yamaContext_height_seam' S y hy hpar hh i2 hi2] at hm
        rw [hje]
        exact hm
      · rw [hc'] at hm
        rwa [yamaContext_height_other' S y hy hpar hh j2 i2 (by omega) hj2x] at hm
    rw [hceq]
    exact hasCol_yama S M hM nrep mfuel nd hn hM2 hyama m i2 j2 hi2 hi2n (by omega) hj2x hkh h0

/-! ## `ShapeRep` の `cellCol` -/

/-- **段 `m` にあるセルの列は高さ `m` 以上。** -/
theorem cellCol_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep m t : Nat) (d : Cell)
    (hd : (rowAt (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)) m)[t]?
      = some d) :
    m ≤ (yamaContext S y hy hpar hh).height (d.pos + m) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama)
  rcases cell_fujiIters M (expP M mfuel) nd (expRes M).length mfuel hkm nrep (expRes M) m t d hd
    with hold | ⟨i2, j2, hi2, _, hj2y, hj2x, hkmax, hceq⟩
  · obtain ⟨hlive, hbound⟩ :=
      cutChild_cell_live S M hM hn (expCutH M) hcut m t d hold
    rw [yamaContext_height_orig S y hy hpar hh (d.pos + m) hbound]
    exact hlive
  · have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
    have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
        = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
    have hj2x' : j2 < S.n - 1 := by omega
    have hkh : m ≤ height S.tower.base j2 := by
      have := kmaxAt_expRes_eq S M hM mfuel hn hM2 hyama i2 j2 hj2x'
      omega
    have hc' : d.pos + m = j2 + (S.n - 1 - y) * i2 := by rw [hceq, hLp]
    rcases Decidable.em (j2 = y) with hje | hjne
    · rw [hc', hje, yamaContext_height_seam' S y hy hpar hh i2 hi2]
      rw [hje] at hkh
      exact hkh
    · rw [hc', yamaContext_height_other' S y hy hpar hh j2 i2 (by omega) hj2x']
      exact hkh

/-! ## 元からあるセルについての条件

コピーで積んだセルとは別に、`cutChild` から残った列 `c < n−1` のセルについても
`parCol` / `parNone` / `valTop` を示す必要がある。こちらは元の山の `ParRep` と
`yamaContext_parent_orig` から出る。 -/

theorem parNone_orig_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d) (hp : d.par = none) :
    (yamaContext S y hy hpar hh).parent m (d.pos + m) = none := by
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
  rw [yamaContext_parent_orig S y hy hpar hh m (d.pos + m) hbound]
  exact hF

theorem parCol_orig_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (st : List Rowj) (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d)
    (hext : RowExt (rowAt (expRes M) m) (rowAt st m))
    (p : Nat) (hp : d.par = some p) :
    ∃ hp' : p < (rowAt st m).size,
      (yamaContext S y hy hpar hh).parent m (d.pos + m)
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
  -- 親の添字は自分より前なので、切ったあとの段にも残っている
  have hpt : p < t := (par_index_lt S M hM m hmM t p htM (by rw [hdt]; exact hp)).2
  have hpc : p < (rowAt (expRes M) m).size := by omega
  have hpe : (rowAt (expRes M) m)[p]? = (rowAt M m)[p]? :=
    rowAt_cutChild_getElem? M (expCutH M) m p hm hpc
  obtain ⟨hp', hpeq⟩ := hext.getElem p hpc
  refine ⟨hp', ?_⟩
  rw [yamaContext_parent_orig S y hy hpar hh m (d.pos + m) hbound, hF]
  have hcell : (rowAt st m)[p]'hp' = (rowAt M m)[p]'hpM := by
    rw [hpeq]
    rw [Array.getElem?_eq_getElem hpc, Array.getElem?_eq_getElem hpM] at hpe
    exact Option.some.inj hpe
  rw [hcell]

/-- **元からあるセルが親を持たないなら、その値は頂の値。** -/
theorem valTop_orig_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (hn : 1 < S.n)
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (m t : Nat) (d : Cell) (hd : (rowAt (expRes M) m)[t]? = some d) (hp : d.par = none) :
    d.val = topValue S.tower.base (d.pos + m) := by
  obtain ⟨hlive, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcut m t d hd
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
  have hme : m = height S.tower.base (d.pos + m) := by
    rcases Nat.eq_or_lt_of_le hlive with he | hlt
    · exact he
    · exfalso
      obtain ⟨q, hq⟩ :=
        (parent_exists_iff_lt_height S.tower.base (S.tower.hpos (d.pos + m)) m).mpr hlt
      rw [hF] at hq
      exact absurd hq (by simp)
  have hrep := rep_top S M hM m hmM
  have hval := hrep.val d (by rw [← hdt]; exact mem_of_getElem _ t htM)
  show d.val = (rows S.tower.base (height S.tower.base (d.pos + m))).value (d.pos + m)
  rw [← hme]
  simpa using hval

/-- **列が `n−1` より小さいセルは元からあるセルである。** 積んだセルの列は
`y + L*i ≥ y + L = n−1` だからである。 -/
theorem cell_orig_of_col_lt (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1) (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep m t : Nat) (d : Cell)
    (hd : (rowAt (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)) m)[t]?
      = some d)
    (hlt : d.pos + m < S.n - 1) :
    (rowAt (expRes M) m)[t]? = some d := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama)
  rcases cell_fujiIters M (expP M mfuel) nd (expRes M).length mfuel hkm nrep (expRes M) m t d hd
    with hold | ⟨i2, j2, hi2, _, hj2y, _, _, hceq⟩
  · exact hold
  · exfalso
    have hmul : (expP M mfuel).len * 1 ≤ (expP M mfuel).len * i2 :=
      Nat.mul_le_mul_left _ hi2
    have hone : (expP M mfuel).len * 1 = (expP M mfuel).len := Nat.mul_one _
    omega

/-! ## 元の山の差分の関係

`ShapeRep` の `step` のうち、値が入っているセル（元からある列）はこれで片付く。 -/

theorem rows_diff (base : Row) (r c p : Nat)
    (hp : (rows base r).forest.parent c = some p) :
    (rows base r).value c = (rows base r).value p + (rows base (r + 1)).value c := by
  have hv := (rows base r).parent_values hp
  have hnext : (rows base (r + 1)).value c = (rows base r).difference c :=
    Row.next_value (rows base r) c
  rw [hnext]
  unfold Row.difference
  rw [hp]
  dsimp only
  omega

/-! ## `ShapeRep` の `tall` -/

/-- **高さ `height_G c` の段は空段落としのあとにも残る。** -/
theorem tall_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep c : Nat)
    (hc : c < (S.n - 1) + (expP M mfuel).len * nrep) :
    (yamaContext S y hy hpar hh).height c
      < (dropEmptyTop
          (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M))).length := by
  obtain ⟨t, d, hd, _⟩ := cover_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep
    ((yamaContext S y hy hpar hh).height c) c hc (Nat.le_refl _)
  have hts : t < (rowAt (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M))
      ((yamaContext S y hy hpar hh).height c)).size := lt_size_of_getElem? hd
  have hlen : (yamaContext S y hy hpar hh).height c
      < (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)).length := by
    rcases Nat.lt_or_ge ((yamaContext S y hy hpar hh).height c)
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)).length with h | h
    · exact h
    · exfalso
      rw [rowAt_of_ge _ _ h] at hts
      simp at hts
  exact lt_dropEmptyTop_length
    (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)).length
    (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M))
    ((yamaContext S y hy hpar hh).height c) (Nat.le_refl _) hlen (by omega)

/-! ## `ShapeRep` の `mono` と `parLt` -/

theorem parLt_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (nd : Nat → Nat) (nrep : Nat) :
    ParLt (dropEmptyTop
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M))) :=
  parLt_dropEmptyTop _
    (parLt_fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M)
      (parLt_cutChild M (expCutH M) (parLt_of_mtRep S M hM)))

theorem rowsMono_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1) (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep : Nat) :
    RowsMono (dropEmptyTop
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M))) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama)
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq hcut.symm)
  exact rowsMono_dropEmptyTop _
    (fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel hkm nrep (expRes M)
      (expP M mfuel).afterCutLength hcolLt (by omega)
      (rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM))).1

/-! ## 山崎噴火の枝で作る疎な山 -/

/-- `tall_yama` を `fujiRs` の形で。 -/
theorem tall_yama' (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep c : Nat)
    (hc : c < (S.n - 1) + (expP M mfuel).len * nrep) :
    (yamaContext S y hy hpar hh).height c < (fujiRs M mfuel nd nrep).length :=
  tall_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep c hc

/-- **元からある列の値は元の山の値のまま。** JS の `fillRow` は値が 0 でない
セルを触らないからである。 -/
theorem colVal_orig_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep r c : Nat) (hc : c < S.n - 1)
    (hlive : r ≤ height S.tower.base c) :
    colVal (fujiRs M mfuel nd nrep) r c = (rows S.tower.base r).value c := by
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hG : (yamaContext S y hy hpar hh).height c = height S.tower.base c :=
    yamaContext_height_orig S y hy hpar hh c hc
  have hcovL : HasCol (fujiRaw M mfuel nd nrep) r c :=
    cover_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r c (by omega) (by omega)
  have hcov : HasCol (fujiRs M mfuel nd nrep) r c := hasCol_dropEmptyTop _ r c hcovL
  obtain ⟨t, ht, hpos⟩ := hasCol_pos _ r c hcov
  have hdRs : (rowAt (fujiRs M mfuel nd nrep) r)[t]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) := Array.getElem?_eq_getElem ht
  have hrow : rowAt (fujiRs M mfuel nd nrep) r = rowAt (fujiRaw M mfuel nd nrep) r :=
    rowAt_dropEmptyTop_of_cell _ r t _ hdRs
  have hdRaw : (rowAt (fujiRaw M mfuel nd nrep) r)[t]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) := by
    rw [← hrow]
    exact hdRs
  have hdOrig : (rowAt (expRes M) r)[t]? = some ((rowAt (fujiRs M mfuel nd nrep) r)[t]'ht) :=
    cell_orig_of_col_lt S M hM mfuel hn hM2 hyama y hy hseam nd nrep r t _ hdRaw (by omega)
  obtain ⟨hval, hvpos⟩ := cutChild_cell_val S M hM (expCutH M) r t _ hdOrig
  -- 段が足りているか
  have htall : (yamaContext S y hy hpar hh).height c < (fujiRs M mfuel nd nrep).length :=
    tall_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep c (by omega)
  have hrlen : r < (fujiRs M mfuel nd nrep).length := by omega
  rw [hpos] at hval
  rcases Nat.lt_or_ge (r + 1) (fujiRs M mfuel nd nrep).length with hlt | hge
  · rw [colVal, colVal_top (fujiRs M mfuel nd nrep)
      (parLt_yama S M hM mfuel nd nrep).dep r hlt t ht
      (rowsMono_yama S M hM mfuel hn hM2 hyama y hy hseam nd nrep r) c hpos (by omega), hval]
  · rw [colVal, colVal_top_last (fujiRs M mfuel nd nrep) r (by omega) t ht
      (rowsMono_yama S M hM mfuel hn hM2 hyama y hy hseam nd nrep r) c hpos, hval]

/-- **`ShapeRep` の `step`（元からある列）。** -/
theorem step_orig_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep r c p : Nat) (hc : c < S.n - 1)
    (hp : (yamaContext S y hy hpar hh).parent r c = some p) :
    colVal (fujiRs M mfuel nd nrep) r c
      = colVal (fujiRs M mfuel nd nrep) r p
        + colVal (fujiRs M mfuel nd nrep) (r + 1) c := by
  rw [yamaContext_parent_orig S y hy hpar hh r c hc] at hp
  have hpc : p < c := (rows S.tower.base r).forest.parent_left hp
  have hfp : ((mountainOf' S).row r).parent c = some p := hp
  have hrc : r < height S.tower.base c := (mountainOf' S).parent_source hfp
  have hrp : r ≤ height S.tower.base p := (mountainOf' S).parent_endpoint hfp
  rw [colVal_orig_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r c hc (by omega),
    colVal_orig_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r p (by omega) hrp,
    colVal_orig_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep (r + 1) c hc
      (by omega)]
  exact rows_diff S.tower.base r c p hp

/-! ## `fujiRs` のセルの正体 -/

theorem fujiRs_cell (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (y : Nat) (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) :
    (rowAt (expRes M) m)[u]? = some d ∨
      ∃ i' t', i' < nrep ∧ t' < (expP M mfuel).len ∧
        m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel ∧
        d = fujiCellAt M (expP M mfuel) nd (i' + 1) (y + t')
              (isRepAt (expP M mfuel) (y + t'))
              (isAscAt M (expP M mfuel) (y + t') mfuel)
              (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
                (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) m := by
  have hdRaw : (rowAt (fujiRaw M mfuel nd nrep) m)[u]? = some d :=
    getElem?_dropEmptyTop (fujiRaw M mfuel nd nrep) m u d hd
  rcases cell_fujiIters' M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m u d hdRaw
    with h1 | ⟨i', t', hi', ht', hk', hde⟩
  · exact Or.inl h1
  · refine Or.inr ⟨i', t', hi', ht', ?_, ?_⟩
    · rwa [hseam] at hk'
    · rwa [hseam] at hde

/-- 積んだセルの位置から最終形へ伸びていること。 -/
theorem rowExt_state_to_fujiRs (M : List Rowj) (mfuel : Nat) (nd : Nat → Nat)
    (nrep m i' t' : Nat) (hi : i' < nrep) (ht : t' ≤ (expP M mfuel).len)
    (hne : 0 < (rowAt (fujiRs M mfuel nd nrep) m).size) :
    RowExt (rowAt (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
        (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) m)
      (rowAt (fujiRs M mfuel nd nrep) m) := by
  have hm : m < (dropEmptyTop (fujiRaw M mfuel nd nrep)).length := by
    rcases Nat.lt_or_ge m (dropEmptyTop (fujiRaw M mfuel nd nrep)).length with h1 | h1
    · exact h1
    · exfalso
      have : rowAt (fujiRs M mfuel nd nrep) m = #[] := rowAt_of_ge _ m h1
      rw [this] at hne
      simp at hne
  have hrow : rowAt (fujiRs M mfuel nd nrep) m = rowAt (fujiRaw M mfuel nd nrep) m :=
    rowAt_dropEmptyTop (fujiRaw M mfuel nd nrep).length (fujiRaw M mfuel nd nrep) m
      (Nat.le_refl _) hm
  rw [hrow]
  exact rowExt_state_to_final M (expP M mfuel) nd (expRes M).length mfuel (expRes M) m i' t' nrep
    hi ht

/-- 積むセルの列（山崎噴火の枝、`kmax` の範囲から）。 -/
theorem fujiCellAt_col_exp (M : List Rowj) (mfuel : Nat) (nd : Nat → Nat) (i j m : Nat)
    (isRep isAsc : Bool) (st : List Rowj)
    (hk : kmaxAt M (expP M mfuel) i j (expRes M).length mfuel
      ≤ j + (expP M mfuel).len * i + 1)
    (hm : m < kmaxAt M (expP M mfuel) i j (expRes M).length mfuel) :
    (fujiCellAt M (expP M mfuel) nd i j isRep isAsc st m).pos + m
      = j + (expP M mfuel).len * i :=
  fujiCellAt_col M (expP M mfuel) nd i j isRep isAsc st m (by omega)

/-- **積んだセルが親を持たないなら、その値は新しい対角のその列の値。** -/
theorem valTop_push_exp (M : List Rowj) (mfuel : Nat) (nd : Nat → Nat) (i j m : Nat)
    (isRep isAsc : Bool) (st : List Rowj)
    (hk : kmaxAt M (expP M mfuel) i j (expRes M).length mfuel
      ≤ j + (expP M mfuel).len * i + 1)
    (hm : m < kmaxAt M (expP M mfuel) i j (expRes M).length mfuel)
    (hp : (fujiCellAt M (expP M mfuel) nd i j isRep isAsc st m).par = none) :
    (fujiCellAt M (expP M mfuel) nd i j isRep isAsc st m).val
      = nd ((fujiCellAt M (expP M mfuel) nd i j isRep isAsc st m).pos + m) := by
  rw [fujiCellAt_col_exp M mfuel nd i j m isRep isAsc st hk hm]
  exact fujiCellAt_val_of_par_none M (expP M mfuel) nd i j isRep isAsc st m hp

/-! ## `ShapeRep` の `valTop`（`fujiRs` の形） -/

theorem valTop_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hyama : expYama M mfuel)
    (y : Nat) (hseam : (expP M mfuel).badRootSeam = y)
    (hcut : expCutH M = height S.tower.base (S.n - 1))
    (nd : Nat → Nat) (hnd : ∀ c, c < S.n - 1 → nd c = topValue S.tower.base c)
    (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) (hp : d.par = none) :
    d.val = nd (d.pos + m) := by
  rcases fujiRs_cell S M hM mfuel y hseam nd nrep m u d hd with hold | ⟨i', t', _, _, hk', hde⟩
  · obtain ⟨_, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcut m u d hold
    rw [hnd (d.pos + m) hbound]
    exact valTop_orig_yama S M hM hn hcut m u d hold hp
  · rw [hde]
    refine valTop_push_exp M mfuel nd (i' + 1) (y + t') m
      (isRepAt (expP M mfuel) (y + t')) _ _
      (kmaxAt_le_yama' M (expP M mfuel) _ _ _ _ (expP_yama_cut M mfuel hyama)) hk' ?_
    rw [← hde]
    exact hp

/-! ## 積んだセルの補助条件

`m < kmaxAt` から、段と列についての条件がまとめて出る。 -/

theorem push_side (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1) (hseam : (expP M mfuel).badRootSeam = y)
    (i' t' m : Nat) (ht' : t' < (expP M mfuel).len)
    (hk' : m < kmaxAt M (expP M mfuel) (i' + 1) (y + t') (expRes M).length mfuel) :
    y + t' < S.n - 1 ∧ m ≤ height S.tower.base (y + t') ∧ m < M.length ∧ m ≤ y + t' ∧
      0 < (rows S.tower.base m).value (y + t') := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  have hjx : y + t' < S.n - 1 := by omega
  have hkm := kmaxAt_expRes_eq S M hM mfuel hn hM2 hyama (i' + 1) (y + t') hjx
  have hhs := height_le_self' S.tower.base S.tower.hpos (y + t')
  have htall := hM.tall (y + t') (by omega)
  refine ⟨hjx, by omega, by omega, by omega, ?_⟩
  exact (live_iff_le_height S.tower.base (S.tower.hpos (y + t')) m).mpr (by omega)

/-- 積んだ時点の状態でも位置は真に増加している。 -/
theorem rowsMono_state (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1) (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (i' t' : Nat) :
    RowsMono (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
      (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  have hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1 :=
    fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama)
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq hcut.symm)
  obtain ⟨hm1, hb1⟩ := fujiIters_invariant M (expP M mfuel) nd (expRes M).length mfuel hkm i'
    (expRes M) (expP M mfuel).afterCutLength hcolLt (by omega)
    (rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM))
  have hmul : (expP M mfuel).len * (i' + 1)
      = (expP M mfuel).len * i' + (expP M mfuel).len := Nat.mul_succ _ _
  exact (fujiSeams_invariant M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel hkm t'
    (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))
    ((expP M mfuel).badRootSeam + (expP M mfuel).len + (expP M mfuel).len * i')
    hb1 (by omega) hm1).1

/-! ## `ShapeRep` の `parNone`（`fujiRs` の形） -/

theorem parNone_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true)
    (nd : Nat → Nat) (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) (hp : d.par = none) :
    (yamaContext S y hy hpar hh).parent m (d.pos + m) = none := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  rcases fujiRs_cell S M hM mfuel y hseam nd nrep m u d hd
    with hold | ⟨i', t', hi', ht', hk', hde⟩
  · exact parNone_orig_yama S M hM hn y hy hpar hh hcut m u d hold hp
  · obtain ⟨hjx, hmh, hmM, hmj, hlivej⟩ :=
      push_side S M hM mfuel hn hM2 hyama y hy hseam i' t' m ht' hk'
    have hcol : d.pos + m = (y + t') + (expP M mfuel).len * (i' + 1) := by
      rw [hde]
      exact fujiCellAt_col_exp M mfuel nd (i' + 1) (y + t') m _ _ _
        (kmaxAt_le_yama' M (expP M mfuel) _ _ _ _ (expP_yama_cut M mfuel hyama)) hk'
    rw [hcol]
    refine fujiCellAt_parNone_yama S M hM mfuel hn hyama y hy hpar hh h0 hseam nd _
      (i' + 1) t' m _ (hra_of_seamAsc M (expP M mfuel) mfuel (y + t') hasc) (by omega) ht' hmM hmj hlivej
      (rowsMono_state S M hM mfuel hn hM2 hyama y hy hseam nd i' t' m) ?_ ?_
    · intro pc hlt hge
      exact hasCol_state S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd i' t' m pc ht' hlt hge
    · rw [← hde]
      exact hp

/-! ## `ShapeRep` の `parCol`（`fujiRs` の形） -/

theorem parCol_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true)
    (nd : Nat → Nat) (nrep m u : Nat) (d : Cell)
    (hd : (rowAt (fujiRs M mfuel nd nrep) m)[u]? = some d) (p : Nat) (hp : d.par = some p) :
    ∃ hp' : p < (rowAt (fujiRs M mfuel nd nrep) m).size,
      (yamaContext S y hy hpar hh).parent m (d.pos + m)
        = some (((rowAt (fujiRs M mfuel nd nrep) m)[p]'hp').pos + m) := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hne : 0 < (rowAt (fujiRs M mfuel nd nrep) m).size := by
    have := lt_size_of_getElem? hd
    omega
  have hrow : rowAt (fujiRs M mfuel nd nrep) m = rowAt (fujiRaw M mfuel nd nrep) m := by
    have hm : m < (dropEmptyTop (fujiRaw M mfuel nd nrep)).length := by
      rcases Nat.lt_or_ge m (dropEmptyTop (fujiRaw M mfuel nd nrep)).length with h1 | h1
      · exact h1
      · exfalso
        have hz : rowAt (fujiRs M mfuel nd nrep) m = #[] := rowAt_of_ge _ m h1
        rw [hz] at hne
        simp at hne
    exact rowAt_dropEmptyTop (fujiRaw M mfuel nd nrep).length (fujiRaw M mfuel nd nrep) m
      (Nat.le_refl _) hm
  rcases fujiRs_cell S M hM mfuel y hseam nd nrep m u d hd
    with hold | ⟨i', t', hi', ht', hk', hde⟩
  · have hext : RowExt (rowAt (expRes M) m) (rowAt (fujiRs M mfuel nd nrep) m) := by
      rw [hrow]
      exact rowExt_fujiIters M (expP M mfuel) nd (expRes M).length mfuel nrep (expRes M) m
    exact parCol_orig_yama S M hM hn y hy hpar hh hcut (fujiRs M mfuel nd nrep) m u d hold
      hext p hp
  · obtain ⟨hjx, hmh, hmM, hmj, hlivej⟩ :=
      push_side S M hM mfuel hn hM2 hyama y hy hseam i' t' m ht' hk'
    have hLp : (expP M mfuel).len = S.n - 1 - y := expP_len_yama S M hM mfuel h0 y hseam
    have hcol : d.pos + m = (y + t') + (expP M mfuel).len * (i' + 1) := by
      rw [hde]
      exact fujiCellAt_col_exp M mfuel nd (i' + 1) (y + t') m _ _ _
        (kmaxAt_le_yama' M (expP M mfuel) _ _ _ _ (expP_yama_cut M mfuel hyama)) hk'
    have hpst : (fujiCellAt M (expP M mfuel) nd (i' + 1) (y + t')
        (isRepAt (expP M mfuel) (y + t')) (isAscAt M (expP M mfuel) (y + t') mfuel)
        (fujiSeams M (expP M mfuel) nd (i' + 1) (expRes M).length mfuel t'
          (fujiIters M (expP M mfuel) nd (expRes M).length mfuel i' (expRes M))) m).par
        = some p := by
      rw [← hde]
      exact hp
    obtain ⟨hp'', hcolp⟩ := fujiCellAt_parCol_yama S M hM mfuel hn hyama y hy hpar hh h0 hseam
      nd _ (i' + 1) (y + t') m (by omega) (by omega) hjx hmM hmj hlivej p _
      (hra_of_seamAsc M (expP M mfuel) mfuel (y + t') hasc) hpst
    obtain ⟨hp', hpeq⟩ :=
      (rowExt_state_to_fujiRs M mfuel nd nrep m i' t' hi' (by omega) hne).getElem p hp''
    refine ⟨hp', ?_⟩
    rw [hcol, hLp, hcolp, hpeq]

/-! ## `ShapeRep` の `step`（コピーで作った列） -/

theorem step_push_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true)
    (nd : Nat → Nat) (nrep r c p : Nat)
    (hc : c < (S.n - 1) + (expP M mfuel).len * nrep) (hcx : S.n - 1 ≤ c)
    (hp : (yamaContext S y hy hpar hh).parent r c = some p) :
    colVal (fujiRs M mfuel nd nrep) r c
      = colVal (fujiRs M mfuel nd nrep) r p
        + colVal (fujiRs M mfuel nd nrep) (r + 1) c := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hrh : r < (yamaContext S y hy hpar hh).height c :=
    ((yamaContext S y hy hpar hh).toRowMountain).parent_source hp
  have hhc : (yamaContext S y hy hpar hh).height c ≤ c :=
    rowMountain_height_le ((yamaContext S y hy hpar hh).toRowMountain) c
  have htall := tall_yama' S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep c hc
  have hcov : HasCol (fujiRs M mfuel nd nrep) r c :=
    hasCol_dropEmptyTop _ r c
      (cover_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r c hc (by omega))
  obtain ⟨i, hi, hposi⟩ := hasCol_pos _ r c hcov
  have hd : (rowAt (fujiRs M mfuel nd nrep) r)[i]?
      = some ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi) := Array.getElem?_eq_getElem hi
  -- 親を持つ
  have hpn : ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi).par ≠ none := by
    intro hnone
    have := parNone_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd nrep r i _ hd hnone
    rw [hposi, hp] at this
    exact absurd this (by simp)
  cases hq : ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi).par with
  | none => exact absurd hq hpn
  | some q =>
      obtain ⟨hq', hcolq⟩ := parCol_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd nrep
        r i _ hd q hq
      rw [hposi, hp] at hcolq
      have hpq : ((rowAt (fujiRs M mfuel nd nrep) r)[q]'hq').pos + r = p :=
        (Option.some.inj hcolq).symm
      -- 値は 0
      have hval : ((rowAt (fujiRs M mfuel nd nrep) r)[i]'hi).val = 0 := by
        rcases fujiRs_cell S M hM mfuel y hseam nd nrep r i _ hd
          with hold | ⟨i', t', _, _, _, hde⟩
        · exfalso
          obtain ⟨_, hbound⟩ := cutChild_cell_live S M hM hn (expCutH M) hcut r i _ hold
          omega
        · rw [hde]
          exact fujiCellAt_val_of_par_some M (expP M mfuel) nd (i' + 1) (y + t')
            (isRepAt (expP M mfuel) (y + t')) _ _ r q (by rw [← hde]; exact hq)
      exact colVal_step_col (fujiRs M mfuel nd nrep)
        (parLt_yama S M hM mfuel nd nrep).dep r (by omega) i hi
        (rowsMono_yama S M hM mfuel hn hM2 hyama y hy hseam nd nrep r) c hposi (by omega) hval
        q hq hq' p hpq

/-! ## **`ShapeRep` の構成（山崎噴火の枝）** -/

theorem shapeRep_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true)
    (nd : Nat → Nat) (hnd : ∀ c, c < S.n - 1 → nd c = topValue S.tower.base c)
    (hndpos : ∀ c, 0 < nd c) (nrep : Nat) :
    ShapeRep (fujiRs M mfuel nd nrep) ((yamaContext S y hy hpar hh).toRowMountain) nd
      ((S.n - 1) + (expP M mfuel).len * nrep) where
  mono := rowsMono_yama S M hM mfuel hn hM2 hyama y hy hseam nd nrep
  parLt := (parLt_yama S M hM mfuel nd nrep).dep
  cellCol := fun r i h =>
    cellCol_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r i _
      (getElem?_dropEmptyTop (fujiRaw M mfuel nd nrep) r i _ (Array.getElem?_eq_getElem h))
  cover := fun r c hc hr => by
    obtain ⟨i, hi, hpos⟩ := hasCol_pos _ r c (hasCol_dropEmptyTop _ r c
      (cover_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r c hc hr))
    exact ⟨i, hi, hpos⟩
  parCol := fun r i h p hp =>
    parCol_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd nrep r i _
      (Array.getElem?_eq_getElem h) p hp
  parNone := fun r i h hp =>
    parNone_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd nrep r i _
      (Array.getElem?_eq_getElem h) hp
  step := fun r c p hc hp => by
    rcases Nat.lt_or_ge c (S.n - 1) with h | h
    · exact step_orig_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep r c p h hp
    · exact step_push_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd nrep r c p hc h hp
  valTop := fun r i h hp =>
    valTop_yama S M hM mfuel hn hyama y hseam (expCutH_eq S M hM hn) nd hnd nrep r i _
      (Array.getElem?_eq_getElem h) hp
  topPos := hndpos
  tall := fun c hc =>
    tall_yama' S M hM mfuel hn hM2 hyama y hy hpar hh hseam nd nrep c hc

/-! ## 行 0 は密（`fujiRs` の形） -/

theorem row0_fujiRs (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length)
    (hkm : ∀ i2 j2, kmaxAt M (expP M mfuel) i2 j2 (expRes M).length mfuel
      ≤ j2 + (expP M mfuel).len * i2 + 1)
    (y : Nat) (hy : y < S.n - 1) (hseam : (expP M mfuel).badRootSeam = y)
    (nd : Nat → Nat) (nrep : Nat) :
    (rowAt (fillValues (fujiRs M mfuel nd nrep)) 0).size
        = (S.n - 1) + (expP M mfuel).len * nrep ∧
      ∀ (t : Nat) (ht : t < (rowAt (fillValues (fujiRs M mfuel nd nrep)) 0).size),
        ((rowAt (fillValues (fujiRs M mfuel nd nrep)) 0)[t]'ht).pos = t := by
  have h0 : 0 < (expRes M).length := expRes_length_pos M hM2
  have hacl : (expP M mfuel).afterCutLength = S.n - 1 := expP_afterCutLength S M hM mfuel h0
  have hcut : expCutH M = height S.tower.base (S.n - 1) := expCutH_eq S M hM hn
  have hlenpos : 0 < (expP M mfuel).len := by
    show 0 < (expP M mfuel).afterCutLength - (expP M mfuel).badRootSeam
    omega
  have hlen : (expP M mfuel).badRootSeam + (expP M mfuel).len
      = (expP M mfuel).afterCutLength := badRootSeam_add_len _ (by omega)
  have hkpos : ∀ i r, r < (expP M mfuel).len →
      0 < kmaxAt M (expP M mfuel) i ((expP M mfuel).badRootSeam + r)
        (expRes M).length mfuel := by
    intro i r hr
    exact kmaxAt_pos' S M hM (by omega) (expP M mfuel) i _ _ _ (by omega) h0
  have hcolLt : ColLt (expRes M) (expP M mfuel).afterCutLength := by
    rw [hacl]
    exact colLt_cutChild S M hM (expCutH M) hn (Nat.le_of_eq hcut.symm)
  have hd0 : ∀ c, c < (expP M mfuel).afterCutLength → HasCol (expRes M) 0 c := by
    intro c hc
    rw [hacl] at hc
    exact hasCol_cutChild_zero S M hM (expCutH M) h0 (by omega) c hc
  obtain ⟨hsz, hposd⟩ := row0_dense_fujiIters M (expP M mfuel) nd (expRes M).length mfuel hkm
    hkpos hlenpos hlen nrep (expRes M)
    (rowsMono_cutChild M (expCutH M) (rowsMono_of_mtRep S M hM)) hcolLt hd0
  have hrow0 : rowAt (fujiRs M mfuel nd nrep) 0 = rowAt (fujiRaw M mfuel nd nrep) 0 :=
    dropEmptyTop_row0 (fujiRaw M mfuel nd nrep).length (fujiRaw M mfuel nd nrep) (Nat.le_refl _)
  have hsz' : (rowAt (fujiRaw M mfuel nd nrep) 0).size
      = (expP M mfuel).afterCutLength + (expP M mfuel).len * nrep := hsz
  have hszRs : (rowAt (fillValues (fujiRs M mfuel nd nrep)) 0).size
      = (S.n - 1) + (expP M mfuel).len * nrep := by
    rw [fillValues_size, hrow0, hsz', hacl]
  refine ⟨hszRs, fun t ht => ?_⟩
  have ht' : t < (rowAt (fujiRs M mfuel nd nrep) 0).size := by
    rw [fillValues_size] at ht
    exact ht
  rw [fillValues_pos_get (fujiRs M mfuel nd nrep) 0 t ht ht']
  have ht'' : t < (rowAt (fujiRaw M mfuel nd nrep) 0).size := by rwa [hrow0] at ht'
  rw [getElem_congr_arr _ _ hrow0 t ht' ht'']
  exact hposd t ht''

/-! ## **山崎噴火の枝の出力** -/

/-- **JS の出力は原文の復元値そのもの（山崎噴火の枝）。** -/
theorem expandOut_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hasc : isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true)
    (nd : Nat → Nat) (hnd : ∀ c, c < S.n - 1 → nd c = topValue S.tower.base c)
    (hndpos : ∀ c, 0 < nd c) (nrep : Nat) :
    expandOut (fillValues (fujiRs M mfuel nd nrep))
      = (List.range ((S.n - 1) + (expP M mfuel).len * nrep)).map
          (Reconstruction.value ((yamaContext S y hy hpar hh).toRowMountain) nd 0) := by
  obtain ⟨hsz, hpos⟩ := row0_fujiRs S M hM mfuel hn hM2
    (fun i2 j2 => kmaxAt_le_yama' M (expP M mfuel) i2 j2 _ _ (expP_yama_cut M mfuel hyama))
    y hy hseam nd nrep
  exact expandOut_eq_value (fujiRs M mfuel nd nrep)
    ((yamaContext S y hy hpar hh).toRowMountain) nd _
    (shapeRep_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam hasc nd hnd hndpos nrep) hsz hpos

/-- **置き換えの継ぎ目は上りである。** 継ぎ目 `y` は段 `badRootHeight` で生きていて、
その段の親鎖はそこから始まるので、`isAscending` は自明に真になる。 -/
theorem isAscAt_seam_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hyama : expYama M mfuel) (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hseam : (expP M mfuel).badRootSeam = y)
    (hfuel : (rowAt M (height S.tower.base (S.n - 1) - 1)).size ≤ mfuel) :
    isAscAt M (expP M mfuel) (expP M mfuel).badRootSeam mfuel = true := by
  have hbh : (expP M mfuel).badRootHeight = height S.tower.base (S.n - 1) - 1 :=
    expP_badRootHeight_yama S M hM hn mfuel hyama
  have htall : height S.tower.base (S.n - 1) < M.length := hM.tall (S.n - 1) (by omega)
  have hle : height S.tower.base (S.n - 1) - 1 ≤ height S.tower.base y :=
    (mountainOf' S).parent_endpoint hpar
  have hlive : 0 < (rows S.tower.base (height S.tower.base (S.n - 1) - 1)).value y :=
    (live_iff_le_height S.tower.base (S.tower.hpos y) _).mpr hle
  show isAscending M (expP M mfuel).badRootHeight (expP M mfuel).badRootSeam
    (expP M mfuel).badRootSeam mfuel = true
  rw [hbh, hseam]
  exact (isAscending_iff S M hM (height S.tower.base (S.n - 1) - 1) y y mfuel
    (by omega) (by omega) hfuel).mpr ⟨hlive, Or.inl rfl⟩

/-- JS の `expand` の枝そのもので書いた形。 -/
theorem expandJS_out_yama (S : Setting) (M : List Rowj) (hM : MtRep S M) (mfuel : Nat)
    (hn : 1 < S.n) (hM2 : 2 ≤ M.length) (hyama : expYama M mfuel)
    (y : Nat) (hy : y < S.n - 1)
    (hpar : ((mountainOf' S).row (height S.tower.base (S.n - 1) - 1)).parent (S.n - 1) = some y)
    (hh : 0 < height S.tower.base (S.n - 1))
    (hseam : (expP M mfuel).badRootSeam = y)
    (hfuel : (rowAt M (height S.tower.base (S.n - 1) - 1)).size ≤ mfuel)
    (nrep efuel : Nat)
    (hnd : ∀ c, c < S.n - 1 → expNd nrep mfuel efuel M c = topValue S.tower.base c)
    (hndpos : ∀ c, 0 < expNd nrep mfuel efuel M c)
    (hhas : (if hlt : (rowAt M 0).size - 1 < (rowAt M 0).size
          then (((rowAt M 0)[(rowAt M 0).size - 1]'hlt).par).isSome else false) = true) :
    expandOut (expandJS nrep mfuel (efuel + 1) M)
      = (List.range ((S.n - 1) + (expP M mfuel).len * nrep)).map
          (Reconstruction.value ((yamaContext S y hy hpar hh).toRowMountain)
            (expNd nrep mfuel efuel M) 0) := by
  rw [expandJS_some nrep mfuel efuel M hhas]
  exact expandOut_yama S M hM mfuel hn hM2 hyama y hy hpar hh hseam
    (isAscAt_seam_yama S M hM mfuel hn hyama y hy hpar hseam hfuel)
    (expNd nrep mfuel efuel M) hnd hndpos nrep

/-! ## 原文の `badAtTerminalContext` との同定 -/

theorem iterSet_n (s : List Nat) (hs : ∀ v ∈ s, 0 < v) (k : Nat) :
    (iterSet (linearSetting s hs) k).n = s.length := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- **こちらで組んだ `TerminalCopy.Context` は原文の `badAtTerminalContext`。** -/
theorem yamaContext_eq (s : List Nat) (hs : ZeroY.Legal s) (K d x y : Nat)
    (hbad : BadAt (rootedSequence s hs) K d x y)
    (hx : s.length - 1 = x)
    (hy : y < (iterSet (linearSetting s hs.1) K).n - 1)
    (hpar : ((mountainOf' (iterSet (linearSetting s hs.1) K)).row
        (height (iterSet (linearSetting s hs.1) K).tower.base
          ((iterSet (linearSetting s hs.1) K).n - 1) - 1)).parent
        ((iterSet (linearSetting s hs.1) K).n - 1) = some y)
    (hh : 0 < height (iterSet (linearSetting s hs.1) K).tower.base
      ((iterSet (linearSetting s hs.1) K).n - 1)) :
    yamaContext (iterSet (linearSetting s hs.1) K) y hy hpar hh
      = badAtTerminalContext (rootedSequence s hs) hbad := by
  have hb : (iterSet (linearSetting s hs.1) K).tower.base
      = (layers (rootedSequence s hs) K).row := iterSet_base s hs K
  have hn : (iterSet (linearSetting s hs.1) K).n = s.length := iterSet_n s hs.1 K
  obtain ⟨hh1, _⟩ := badAt_height_and_top hbad
  have hlev : height (iterSet (linearSetting s hs.1) K).tower.base
      ((iterSet (linearSetting s hs.1) K).n - 1) - 1 = d := by
    rw [hb, hn, hx, hh1]
    omega
  unfold yamaContext badAtTerminalContext
  congr 1
  · unfold mountainOf'
    congr 1
  all_goals first
    | omega
    | (congr 1 <;> omega)

/-! ## 新しい対角の値は上の層の値

JS の対角の行 0 は抽出段そのものなので、その添字 `s` の値は `topValue base s` である。 -/

theorem size_rowAt_expDg (S : Setting) (M : List Rowj) (hM : MtRep S M) (f : Nat) :
    (rowAt (expDg M (f + 1)) 0).size = S.n := by
  show (rowAt (calcMountainFrom (parseDiag (calcDiagonal M)) (f + 1)) 0).size = S.n
  rw [rowAt_calcMountainFrom_zero, assignParents_size, parseDiag_size,
    calcDiagonal_eq' S M hM]
  simp

theorem valAtIdx_expDg (S : Setting) (M : List Rowj) (hM : MtRep S M) (f s : Nat)
    (hs : s < S.n) : valAtIdx (rowAt (expDg M (f + 1)) 0) s = topValue S.tower.base s := by
  have hsize := size_rowAt_expDg S M hM f
  have hrow : rowAt (expDg M (f + 1)) 0 = assignParents none (parseDiag (calcDiagonal M)) :=
    rowAt_calcMountainFrom_zero _ f
  have hss : s < (rowAt (expDg M (f + 1)) 0).size := by omega
  have hrep : Rep (rowAt (expDg M (f + 1)) 0) 0 S.n (extractOf S).value := by
    rw [hrow]
    exact rep_extract S M hM
  have hpos := pos_eq_index (rowAt (expDg M (f + 1)) 0) S.n _ hrep hsize s hss
  have hval := hrep.val _ (mem_of_getElem _ s hss)
  rw [hpos] at hval
  show (if h : s < (rowAt (expDg M (f + 1)) 0).size then
      ((rowAt (expDg M (f + 1)) 0)[s]'h).val else 0) = _
  rw [dif_pos hss, hval]
  rfl

/-- **山崎噴火の枝の新しい対角は、上の層の値を `source0` で読んだもの。** -/
theorem expNd_topValue (S : Setting) (M : List Rowj) (hM : MtRep S M) (f : Nat)
    (hn : 1 < S.n) (hyama : expYama M (f + 1))
    (C : OrdinaryCopy.Context) (hcy : C.coordinates.y = expSeam M (f + 1))
    (hcx : C.coordinates.x = (rowAt M 0).size - 1)
    (nrep efuel c : Nat) :
    expNd nrep (f + 1) efuel M c = topValue S.tower.base (C.source0 c) := by
  have hsizeM : (rowAt M 0).size = S.n := hM.size0
  have hx : C.coordinates.x = S.n - 1 := by rw [hcx, hsizeM]
  have hsrc : C.source0 c < C.coordinates.x := by
    have := source0_lt C.coordinates.y C.coordinates.x c C.coordinates.root_lt_last
    unfold OrdinaryCopy.Context.source0 CopyCoordinates.Context.length
    exact this
  rw [expNd_yama_source0 nrep (f + 1) efuel M hyama C hcy hcx
    (by rw [hsizeM, size_rowAt_expDg S M hM f]; omega)]
  exact valAtIdx_expDg S M hM f (C.source0 c) (by omega)

/-! ## 原文の `assemble` との一致 -/

theorem layers_succ_value (a : RootedRow) (k c : Nat) :
    (layers a (k + 1)).row.value c = topValue (layers a k).row c := rfl

/-- **`K+1` 段目以上を畳んだ値は、`layers a K` の頂の値を `source0` で読んだもの。** -/
theorem assemble_above_eq (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hK : K < sequenceBound s) (c : Nat) :
    TowerReconstruction.assemble
        ((List.range' (K + 1) (sequenceBound s - (K + 1))).map
          (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c
      = topValue (layers (rootedSequence s hs) K).row
          ((badAtTerminalContext (rootedSequence s hs) hbad).ordinaryContext.source0 c) := by
  have h := assemble_expanded_above (rootedSequence s hs) hbad (K + 1)
    (sequenceBound s - (K + 1)) (Nat.lt_succ_self K)
  have hend : (K + 1) + (sequenceBound s - (K + 1)) = sequenceBound s := by omega
  rw [hend] at h
  have hone : (badAtTerminalContext (rootedSequence s hs) hbad).ordinaryContext.copyValue
      (layers (rootedSequence s hs) (sequenceBound s)).row.value = (fun _ => 1) := by
    funext c'
    exact sequence_layers_all_one s hs (by omega) _
  rw [hone] at h
  rw [h]
  rfl

/-- **JS の新しい対角は原文の `assemble`（`K+1` 段目以上）である。** -/
theorem expNd_eq_assemble (s : List Nat) (hs : ZeroY.Legal s) {K d x y : Nat}
    (hbad : BadAt (rootedSequence s hs) K d x y) (hK : K < sequenceBound s)
    (M : List Rowj) (hM : MtRep (iterSet (linearSetting s hs.1) K) M) (f : Nat)
    (hn : 1 < (iterSet (linearSetting s hs.1) K).n)
    (hyama : expYama M (f + 1)) (hseam : expSeam M (f + 1) = y) (hx : s.length - 1 = x)
    (nrep efuel c : Nat) :
    expNd nrep (f + 1) efuel M c
      = TowerReconstruction.assemble
          ((List.range' (K + 1) (sequenceBound s - (K + 1))).map
            (expandedMountain (rootedSequence s hs) hbad)) (fun _ => 1) c := by
  have hb : (iterSet (linearSetting s hs.1) K).tower.base
      = (layers (rootedSequence s hs) K).row := iterSet_base s hs K
  have hnn : (iterSet (linearSetting s hs.1) K).n = s.length := iterSet_n s hs.1 K
  rw [assemble_above_eq s hs hbad hK c, ← hb]
  refine expNd_topValue (iterSet (linearSetting s hs.1) K) M hM f hn hyama
    ((badAtTerminalContext (rootedSequence s hs) hbad).ordinaryContext) ?_ ?_ nrep efuel c
  · show y = expSeam M (f + 1)
    rw [hseam]
  · show x = (rowAt M 0).size - 1
    rw [hM.size0, hnn, hx]

/-! ## `isAscending` は `InCone`

原文の `LowerCopy.Context.InCone c` は「段 `floor` で列 `c` が生きていて、
その段での根が継ぎ目 `y` である」。JS の `isAscending` は「段 `bh` で親鎖を辿って
継ぎ目に届く」なので、`y` が段 `floor` で根であれば同じことになる。 -/

/-- 2 つの `Ancestor` の言い換え。`ZeroY` 側は `TransGen`、`OneY` 側は帰納型。 -/
theorem ancestor_conv (F : ParentForest) (a c : Nat) :
    ZeroY.Forest.Ancestor F.parent c a ↔ F.Ancestor a c := by
  constructor
  · intro h
    induction h with
    | single hp => exact ParentForest.Ancestor.direct hp
    | tail _ hp ih => exact ParentForest.Ancestor.trans (ParentForest.Ancestor.direct hp) ih
  · intro h
    induction h with
    | direct hp => exact Relation.TransGen.single hp
    | step _ hp ih => exact Relation.TransGen.trans (Relation.TransGen.single hp) ih

/-- 根であることと、根が一致することの言い換え。 -/
theorem root_eq_iff (F : ParentForest) (r c : Nat) (hr : F.parent r = none) :
    F.root c = r ↔ (F.Ancestor r c ∨ r = c) := by
  constructor
  · intro h
    rcases ParentForest.root_ancestor_or_eq F c with h1 | h1
    · rw [h] at h1
      exact Or.inl h1
    · rw [h] at h1
      exact Or.inr h1
  · intro h
    refine ParentForest.root_unique F hr ?_
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **`isAscending` は「段 `bh` での根が継ぎ目」と同値。** -/
theorem isAscending_iff_root (S : Setting) (M : List Rowj) (hM : MtRep S M)
    (bh seam j fuel : Nat) (hbh : bh < M.length) (hj : j < S.n)
    (hfuel : (rowAt M bh).size ≤ fuel)
    (hroot : (rows S.tower.base bh).forest.parent seam = none) :
    isAscending M bh seam j fuel = true ↔
      (bh ≤ height S.tower.base j ∧ (rows S.tower.base bh).forest.root j = seam) := by
  rw [isAscending_iff S M hM bh seam j fuel hbh hj hfuel]
  constructor
  · rintro ⟨hlive, hpath⟩
    refine ⟨(live_iff_le_height S.tower.base (S.tower.hpos j) bh).mp hlive, ?_⟩
    refine (root_eq_iff _ seam j hroot).mpr ?_
    rcases hpath with h | h
    · exact Or.inr h.symm
    · exact Or.inl ((ancestor_conv (rows S.tower.base bh).forest seam j).mp h)
  · rintro ⟨hle, hr⟩
    refine ⟨(live_iff_le_height S.tower.base (S.tower.hpos j) bh).mpr hle, ?_⟩
    rcases (root_eq_iff _ seam j hroot).mp hr with h | h
    · exact Or.inr ((ancestor_conv (rows S.tower.base bh).forest seam j).mpr h)
    · exact Or.inl h.symm

/-- 列 `y` はその高さの段では根（頂には親が無い）。 -/
theorem parent_none_at_top (base : Row) (hpos : ∀ c, 0 < base.value c) (y : Nat) :
    (rows base (height base y)).forest.parent y = none := by
  cases hp : (rows base (height base y)).forest.parent y with
  | none => rfl
  | some p =>
      exfalso
      have := (parent_exists_iff_lt_height base (hpos y) (height base y)).mp ⟨p, hp⟩
      omega

end Yukito
