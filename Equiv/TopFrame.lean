import Equiv.Mountain

/-!
# 抽出後の行の下にある frame

抽出を繰り返すには、橋渡しを「一般の行から作る山」へ広げる必要がある。そのとき
塔の底に来るのは、`ofSequence` のときの線形森ではなく、抽出後の行の下にある frame
である。

Phyrion は `rawExtract` の親が `topForest` 上の `restrictedParent` に一致することを
示している（`rawExtract_parent_eq_topForest`）。`topForest` は

```
topForest.parent c = if height c = 0 then none else some (rootAt (height c − 1) c)
```

で、「頂の 1 つ下の段での成分の根」である。擬親森より構造がはっきりしていて、
山の段で証明した道具がそのまま効く。

本ファイルは底の義務の 1 本目、**最左の子は右隣**を `topForest` について示す。
-/

namespace Yukito

open OneY OneY.Numeric OneY.RootGeometry

/-- 頂の 1 つ上の段では、頂の根はもう親を持たない。 -/
theorem height_succ_of_leftmost (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (root : Nat)
    (hn : (rows (ofSequence s) (height (ofSequence s) root)).forest.parent root = none)
    (hf : (rows (ofSequence s) (height (ofSequence s) root)).forest.parent (root + 1)
      = some root) :
    height (ofSequence s) (root + 1) = height (ofSequence s) root + 1 := by
  have hlive : 0 < (rows (ofSequence s)
      (height (ofSequence s) root + 1)).value (root + 1) :=
    (rows_parent_iff_next_live (ofSequence s) _ (root + 1)).mp ⟨root, hf⟩
  have hge : height (ofSequence s) root + 1 ≤ height (ofSequence s) (root + 1) :=
    (live_iff_le_height (ofSequence s) (ofSequence_positive s hs (root + 1)) _).mp hlive
  have hle : height (ofSequence s) (root + 1) ≤ height (ofSequence s) root + 1 := by
    rcases Nat.lt_or_ge (height (ofSequence s) root + 1)
      (height (ofSequence s) (root + 1)) with hlt | hle
    · exfalso
      -- 行 `H root + 1` で `root+1` が親を持つことになるが、その親は
      -- 行 `H root` での祖先、すなわち `root` しかなく、`root` はそこで死んでいる
      obtain ⟨q, hq⟩ := (parent_exists_iff_lt_height (ofSequence s)
        (ofSequence_positive s hs (root + 1)) (height (ofSequence s) root + 1)).mpr hlt
      have hq' : restrictedParent (rows (ofSequence s) (height (ofSequence s) root)).forest
          (rows (ofSequence s) (height (ofSequence s) root + 1)).value (root + 1)
          = some q := hq
      obtain ⟨hanc, hpos, _, _⟩ :=
        (restrictedParent_some_iff _ _ (root + 1) q).mp hq'
      -- `q` は行 `H root` で `root+1` の祖先。祖先は `root` のみ
      have hqr : q = root := by
        rcases ancestor_cases hf (ParentForest.ancestor_of_zeroY hanc) with he | ha
        · exact he
        · exact absurd (ancestor_parent_exists' ha) (by rw [hn]; rintro ⟨t, ht⟩; cases ht)
      rw [hqr] at hpos
      have hdead : (rows (ofSequence s) (height (ofSequence s) root + 1)).value root = 0 := by
        rcases Nat.eq_zero_or_pos
          ((rows (ofSequence s) (height (ofSequence s) root + 1)).value root) with h | h
        · exact h
        · exact absurd ((live_iff_le_height (ofSequence s)
            (ofSequence_positive s hs root) _).mp h) (by omega)
      omega
    · exact hle
  omega

/-- **底の義務 1。** `topForest` でも最左の子は右隣である。 -/
theorem topForest_leftmost_child (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (root e : Nat)
    (h : (mountainOf s hs).topForest.parent e = some root) :
    (mountainOf s hs).topForest.parent (root + 1) = some root := by
  obtain ⟨hHe, hroot⟩ :=
    (RowMountain.topForest_parent_some_iff (mountainOf s hs) e root).mp h
  rw [mountainOf_height_eq] at hHe
  rw [mountainOf_height_eq, mountainOf_rootAt_eq] at hroot
  -- `H root = H e − 1`
  have hHr : height (ofSequence s) root = height (ofSequence s) e - 1 := by
    have hrh := (mountainOf s hs).root_height
      (show height (ofSequence s) e - 1 ≤ (mountainOf s hs).height e by
        rw [mountainOf_height_eq]; omega) (c := e)
    rw [mountainOf_height_eq, mountainOf_rootAt_eq, hroot] at hrh
    exact hrh
  have hlt : root < e := by
    have hrl := (mountainOf s hs).rootAt_lt
      (show height (ofSequence s) e - 1 < (mountainOf s hs).height e by
        rw [mountainOf_height_eq]; omega) (c := e)
    rw [mountainOf_rootAt_eq, hroot] at hrl
    exact hrl
  -- `root` は行 `H root` で `e` の祖先
  have hanc : (rows (ofSequence s) (height (ofSequence s) root)).forest.Ancestor root e := by
    have hpath := ((mountainOf s hs).rootAt_eq_iff_path
      (r := height (ofSequence s) e - 1) (q := root) (c := e)
      (by rw [mountainOf_height_eq]; omega)).mp
      (by rw [mountainOf_rootAt_eq]; exact hroot)
    rcases hpath with ha | he
    · rw [hHr]
      exact ha
    · omega
  obtain ⟨a, hFa, _⟩ := child_toward hanc
  have hf := leftmost_child_seq s hs (height (ofSequence s) root) root a hFa
  have hn : (rows (ofSequence s) (height (ofSequence s) root)).forest.parent root = none := by
    cases hp : (rows (ofSequence s) (height (ofSequence s) root)).forest.parent root with
    | none => rfl
    | some q =>
        exfalso
        have := (parent_exists_iff_lt_height (ofSequence s)
          (ofSequence_positive s hs root) (height (ofSequence s) root)).mp ⟨q, hp⟩
        omega
  have hH1 := height_succ_of_leftmost s hs root hn hf
  refine (RowMountain.topForest_parent_some_iff (mountainOf s hs) (root + 1) root).mpr
    ⟨by rw [mountainOf_height_eq]; omega, ?_⟩
  rw [mountainOf_height_eq, mountainOf_rootAt_eq, hH1,
    show height (ofSequence s) root + 1 - 1 = height (ofSequence s) root from by omega,
    (rows (ofSequence s) (height (ofSequence s) root)).forest.root_of_parent_some hf]
  exact (rows (ofSequence s) (height (ofSequence s) root)).forest.root_of_parent_none hn

/-- `topForest` の親から、段の関係を読む。 -/
theorem topForest_heights (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (root e : Nat)
    (h : (mountainOf s hs).topForest.parent e = some root) :
    height (ofSequence s) e = height (ofSequence s) root + 1 ∧
      root < e ∧
      (rows (ofSequence s) (height (ofSequence s) root)).forest.Ancestor root e := by
  obtain ⟨hHe, hroot⟩ :=
    (RowMountain.topForest_parent_some_iff (mountainOf s hs) e root).mp h
  rw [mountainOf_height_eq] at hHe
  rw [mountainOf_height_eq, mountainOf_rootAt_eq] at hroot
  have hHr : height (ofSequence s) root = height (ofSequence s) e - 1 := by
    have hrh := (mountainOf s hs).root_height
      (show height (ofSequence s) e - 1 ≤ (mountainOf s hs).height e by
        rw [mountainOf_height_eq]; omega) (c := e)
    rw [mountainOf_height_eq, mountainOf_rootAt_eq, hroot] at hrh
    exact hrh
  have hlt : root < e := by
    have hrl := (mountainOf s hs).rootAt_lt
      (show height (ofSequence s) e - 1 < (mountainOf s hs).height e by
        rw [mountainOf_height_eq]; omega) (c := e)
    rw [mountainOf_rootAt_eq, hroot] at hrl
    exact hrl
  refine ⟨by omega, hlt, ?_⟩
  have hpath := ((mountainOf s hs).rootAt_eq_iff_path
    (r := height (ofSequence s) e - 1) (q := root) (c := e)
    (by rw [mountainOf_height_eq]; omega)).mp
    (by rw [mountainOf_rootAt_eq]; exact hroot)
  rcases hpath with ha | he
  · rw [hHr]
    exact ha
  · omega

/-- **底の義務 2。** `topForest` の子 `root+1` と `e`（`root+1 < e`）について
`topValue e ≤ topValue (root+1)`。

`topForest` の親が `root` なら段はちょうど `H root + 1` なので、両方の `topValue` は
その段の値である。`e` はその段が頂なので次の段では親を持たず、`restrictedParent` の
最大性から `root` の子 `a`（`e` へ至る道の上）について `V e ≤ V a`。あとは
`sibSucc_rows` で `V a ≤ V (root+1)` を繋ぐ。 -/
theorem topForest_sibSucc (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (root e : Nat)
    (hj : (mountainOf s hs).topForest.parent (root + 1) = some root)
    (he : (mountainOf s hs).topForest.parent e = some root)
    (hlt : root + 1 < e) :
    topValue (ofSequence s) e ≤ topValue (ofSequence s) (root + 1) := by
  obtain ⟨hHe, _, hanc⟩ := topForest_heights s hs root e he
  obtain ⟨hHj, _, _⟩ := topForest_heights s hs root (root + 1) hj
  -- 両方の頂は段 `H root + 1`
  have hve : topValue (ofSequence s) e
      = (rows (ofSequence s) (height (ofSequence s) root + 1)).value e := by
    show (rows (ofSequence s) (height (ofSequence s) e)).value e = _
    rw [hHe]
  have hvj : topValue (ofSequence s) (root + 1)
      = (rows (ofSequence s) (height (ofSequence s) root + 1)).value (root + 1) := by
    show (rows (ofSequence s) (height (ofSequence s) (root + 1))).value (root + 1) = _
    rw [hHj]
  rw [hve, hvj]
  -- `root` の子 `a` で `e` に至る道の上にあるもの
  obtain ⟨a, hFa, hae⟩ := child_toward hanc
  have hja := leftmost_child_seq s hs (height (ofSequence s) root) root a hFa
  have hapos : 0 < (rows (ofSequence s) (height (ofSequence s) root + 1)).value a :=
    (rows_parent_iff_next_live (ofSequence s) _ a).mp ⟨root, hFa⟩
  -- `e` はこの段が頂なので次の段で親を持たない
  have hnone : (rows (ofSequence s) (height (ofSequence s) root + 1)).forest.parent e
      = none := by
    cases hp : (rows (ofSequence s) (height (ofSequence s) root + 1)).forest.parent e with
    | none => rfl
    | some q =>
        exfalso
        have := (parent_exists_iff_lt_height (ofSequence s)
          (ofSequence_positive s hs e) (height (ofSequence s) root + 1)).mp ⟨q, hp⟩
        omega
  have hea : (rows (ofSequence s) (height (ofSequence s) root + 1)).value e
      ≤ (rows (ofSequence s) (height (ofSequence s) root + 1)).value a := by
    rcases hae with ha' | heq
    · exact (restrictedParent_none_iff (rows (ofSequence s) (height (ofSequence s) root)).forest
        (rows (ofSequence s) (height (ofSequence s) root + 1)).value e).mp hnone a ha' hapos
    · rw [heq]
      exact Nat.le_refl _
  have haj : (rows (ofSequence s) (height (ofSequence s) root + 1)).value a
      ≤ (rows (ofSequence s) (height (ofSequence s) root + 1)).value (root + 1) := by
    rcases Nat.lt_or_ge (root + 1) a with hx | hx
    · exact sibSucc_seq s hs (height (ofSequence s) root) root a hja hFa hx
    · have hra := (rows (ofSequence s) (height (ofSequence s) root)).forest.parent_left hFa
      have heqa : a = root + 1 := by omega
      rw [heqa]
      exact Nat.le_refl _
  omega

end Yukito
