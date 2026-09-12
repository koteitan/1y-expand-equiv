import Equiv.Yama
import Equiv.NoCross

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
  unfold kmaxAt
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

/-! ## 根の区間性（残る幾何的義務）

`k < K` の枝で JS と原文の親が一致するには、次が要る。段 `r` で列 `x` の根が `y`
なら、`y` と `x` の間にあって段 `r` で生きている列 `j` の根も `y` である。
森の非交差性から従うはずの主張で、この枝に残る唯一の幾何的義務である。

これが無いと、`¬InCone j` かつ `height y ≤ height j` の場合に JS の
`sy = badRootHeight` と原文の `sy = r` が食い違う。 -/

/-- 段 `r` での根の区間性。 -/
def RootInterval (S : Setting) : Prop :=
  ∀ (r y j x : Nat), (mountainOf' S).rootAt r x = y → y < j → j < x →
    r ≤ height S.tower.base j → (mountainOf' S).rootAt r j = y

/-- **根の単調性。** 段 `r` で生きている 2 つの列について、根は列の順を保つ。
これが森の非交差性の言い換えで、区間性はここから出る。 -/
def RootMono (S : Setting) : Prop :=
  ∀ (r c1 c2 : Nat), c1 ≤ c2 → r ≤ height S.tower.base c1 → r ≤ height S.tower.base c2 →
    (mountainOf' S).rootAt r c1 ≤ (mountainOf' S).rootAt r c2

/-- **辺の内側に根は無い。** 段 `r` で `c` の親が `p` なら、`p` と `c` の間の
生きた列は根でない。森の非交差性の核心である。 -/
def NoRootInside (S : Setting) : Prop :=
  ∀ (r c p w : Nat), ((mountainOf' S).row r).parent c = some p → p < w → w < c →
    r ≤ height S.tower.base w → ((mountainOf' S).row r).parent w ≠ none

/-! ## 鎖は辺を跨げない

森が非交差で、辺の内側に根が無ければ、辺の内側から始まる鎖は辺の下端に到達する。 -/

/-- 辺 `(b, a)` の内側 `w` から始まる `F` 鎖は `b` に到達する。 -/
theorem chain_hits (F : ParentForest) (hnc : NoCross F)
    (hnri : ∀ u u' v, F.parent u = some u' → u' < v → v < u → F.parent v ≠ none)
    (b a : Nat) (hba : F.parent a = some b) :
    ∀ w, b < w → w < a → ZeroY.Forest.Ancestor F.parent w b := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hbw hwa
    cases hv : F.parent w with
    | none => exact absurd hv (hnri a b w hba hbw hwa)
    | some v =>
        have hvw : v < w := F.parent_left hv
        rcases Nat.lt_or_ge v b with hvb | hbv
        · exact absurd (hnc v w b a hv hba hvb hbw hwa) (by simp)
        · rcases Nat.eq_or_lt_of_le hbv with hve | hvb'
          · rw [hve]
            exact Relation.TransGen.single hv
          · exact Relation.TransGen.trans (Relation.TransGen.single hv)
              (ih v hvw hvb' (by omega))

/-- 親が無ければ祖先も無い。 -/
theorem not_ancestor_of_parent_none (F : ParentForest) (c p : Nat) (hq : F.parent c = none)
    (h : ZeroY.Forest.Ancestor F.parent c p) : False := by
  induction h with
  | single h1 => rw [hq] at h1; exact absurd h1 (by simp)
  | tail _ _ ih => exact ih

/-- 鎖の最初の一歩。 -/
theorem ancestor_first_step (F : ParentForest) (c q p : Nat) (hq : F.parent c = some q)
    (h : ZeroY.Forest.Ancestor F.parent c p) :
    p = q ∨ ZeroY.Forest.Ancestor F.parent q p := by
  induction h with
  | single h1 =>
      rw [hq] at h1
      exact Or.inl (Option.some.inj h1).symm
  | tail h1 h2 ih =>
      rcases ih with he | ha
      · rw [he] at h2
        exact Or.inr (Relation.TransGen.single h2)
      · exact Or.inr (Relation.TransGen.tail ha h2)

/-- **間にある列は祖先の祖先。** `p` が `c` の `F` 祖先で `p < w < c` なら、
`p` は `w` の `F` 祖先でもある。 -/
theorem frame_ancestor_of_between (F : ParentForest) (hnc : NoCross F)
    (hnri : ∀ u u' v, F.parent u = some u' → u' < v → v < u → F.parent v ≠ none) :
    ∀ c p w, ZeroY.Forest.Ancestor F.parent c p → p < w → w < c →
      ZeroY.Forest.Ancestor F.parent w p := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro p w hpc hpw hwc
    cases hq : F.parent c with
    | none => exact (not_ancestor_of_parent_none F c p hq hpc).elim
    | some q =>
        have hqc : q < c := F.parent_left hq
        have hpq : p = q ∨ ZeroY.Forest.Ancestor F.parent q p :=
          ancestor_first_step F c q p hq hpc
        have hpqle : p ≤ q := by
          rcases hpq with h | h
          · omega
          · have := ZeroY.Forest.ancestor_lt F.parent_left h
            omega
        rcases Nat.lt_or_ge q w with hqw | hwq
        · -- q < w < c、辺 (q, c) の内側
          have hwq' : ZeroY.Forest.Ancestor F.parent w q := chain_hits F hnc hnri q c hq w hqw hwc
          rcases hpq with h | h
          · rw [h]; exact hwq'
          · exact Relation.TransGen.trans hwq' h
        · rcases Nat.eq_or_lt_of_le hwq with hwe | hwq'
          · -- w = q
            rcases hpq with h | h
            · omega
            · rw [hwe]; exact h
          · -- w < q、q を新しい c として帰納
            rcases hpq with h | h
            · omega
            · exact ih q hqc p w h hpw hwq'

/-- **`NoRootInside` の第 1 の場合。** `w` が `c` の frame 祖先なら証明できる。
`p` が最大の候補なので `U c ≤ U w`、そして `p` は `w` の frame 祖先で
`0 < U p < U c ≤ U w` だから `w` は親を持つ。 -/
theorem noRootInside_ancestor {F : ParentForest} {U : Nat → Nat} {c p w : Nat}
    (hp : restrictedParent F U c = some p) (hpw : p < w)
    (hanc : ZeroY.Forest.Ancestor F.parent c w) (hlive : 0 < U w) :
    restrictedParent F U w ≠ none := by
  obtain ⟨hpa, hppos, hplt, hmax⟩ := (restrictedParent_some_iff F U c p).mp hp
  have hge : U c ≤ U w := by
    rcases Nat.lt_or_ge (U w) (U c) with hlt | hge
    · have := hmax w hanc hlive hlt
      omega
    · exact hge
  have hpw0 : ZeroY.Forest.Ancestor F.parent w p :=
    ZeroY.Forest.ancestor_of_common_target F.parent_left hpa hanc hpw
  have hpw1 : F.Ancestor p w := (ancestor_conv F p w).mp hpw0
  intro hnone
  have h2 := (restrictedParent_none_iff F U w).mp hnone p hpw1 hppos
  omega

/-- **「辺の内側に根は無い」から根の単調性が出る。** -/
theorem rootMono_of_noRootInside (S : Setting) (h : NoRootInside S) : RootMono S := by
  intro r
  have key : ∀ c2 c1, c1 ≤ c2 → r ≤ height S.tower.base c1 → r ≤ height S.tower.base c2 →
      (mountainOf' S).rootAt r c1 ≤ (mountainOf' S).rootAt r c2 := by
    intro c2
    induction c2 using Nat.strongRecOn with
    | ind c2 ih2 =>
      intro c1
      induction c1 using Nat.strongRecOn with
      | ind c1 ih1 =>
        intro hle hl1 hl2
        cases hp : ((mountainOf' S).row r).parent c2 with
        | none =>
            have hr2 : (mountainOf' S).rootAt r c2 = c2 :=
              ParentForest.root_of_parent_none _ hp
            have hr1 : (mountainOf' S).rootAt r c1 ≤ c1 := (mountainOf' S).rootAt_le r c1
            omega
        | some p =>
            have hpc : p < c2 := ((mountainOf' S).row r).parent_left hp
            have hrp : (mountainOf' S).rootAt r c2 = (mountainOf' S).rootAt r p :=
              (mountainOf' S).rootAt_of_parent hp
            have hlp : r ≤ height S.tower.base p := (mountainOf' S).parent_endpoint hp
            rcases Nat.lt_or_ge p c1 with hpc1 | hc1p
            · rcases Nat.eq_or_lt_of_le hle with heq | hlt
              · subst heq
                omega
              · cases hq : ((mountainOf' S).row r).parent c1 with
                | none => exact absurd hq (h r c2 p c1 hp hpc1 hlt hl1)
                | some q =>
                    have hqc : q < c1 := ((mountainOf' S).row r).parent_left hq
                    have hlq : r ≤ height S.tower.base q := (mountainOf' S).parent_endpoint hq
                    have hrq : (mountainOf' S).rootAt r c1 = (mountainOf' S).rootAt r q :=
                      (mountainOf' S).rootAt_of_parent hq
                    rcases Nat.lt_or_ge p q with hpq | hqp
                    · have h1 := ih1 q hqc (by omega) hlq hl2
                      omega
                    · have h1 := ih2 p hpc q hqp hlq hlp
                      omega
            · have h1 := ih2 p hpc c1 hc1p hl1 hlp
              omega
  intro c1 c2 hle hl1 hl2
  exact key c2 c1 hle hl1 hl2

/-- **単調性から区間性が出る。** `rootAt r y = y ≤ rootAt r j ≤ rootAt r x = y`。 -/
theorem rootInterval_of_rootMono (S : Setting) (h : RootMono S) : RootInterval S := by
  intro r y j x hx hyj hjx hj
  have hxlive : r ≤ height S.tower.base x := by
    rcases Nat.lt_or_ge (height S.tower.base x) r with hlt | hge
    · exfalso
      have hself : (mountainOf' S).rootAt r x = x :=
        ParentForest.root_of_parent_none _
          (((mountainOf' S).parent_none_iff r x).mpr (Nat.le_of_lt hlt))
      omega
    · exact hge
  have hh : (mountainOf' S).height y = r := by
    rw [← hx]
    exact (mountainOf' S).root_height hxlive
  have hylive : r ≤ height S.tower.base y := by
    show r ≤ (mountainOf' S).height y
    omega
  have hry : (mountainOf' S).rootAt r y = y := by
    rw [← hh]
    exact (mountainOf' S).top_root y
  have h1 := h r y j (by omega) hylive hj
  have h2 := h r j x (by omega) hj hxlive
  omega

/-- 区間性があれば、`y` と `x` の間の生きた列は `InCone`。 -/
theorem inCone_of_between (hri : RootInterval S) (hyx : y < x) (hroot) (hhigher) (j : Nat)
    (hj1 : y < j) (hj2 : j < x)
    (hlive : height S.tower.base y ≤ height S.tower.base j) :
    (lowerContext S y x hyx hroot hhigher).InCone j :=
  ⟨hlive, hri (height S.tower.base y) y j x hroot hj1 hj2 hlive⟩

/-- したがって `InCone` でない列は段 `floor` より下で死んでいる。 -/
theorem height_lt_floor_of_not_inCone (hri : RootInterval S) (hyx : y < x) (hroot) (hhigher)
    (j : Nat) (hj1 : y < j) (hj2 : j < x)
    (h : ¬ (lowerContext S y x hyx hroot hhigher).InCone j) :
    height S.tower.base j < height S.tower.base y := by
  rcases Nat.lt_or_ge (height S.tower.base j) (height S.tower.base y) with h1 | h1
  · exact h1
  · exact absurd (inCone_of_between hri hyx hroot hhigher j hj1 hj2 h1) h

end Yukito
