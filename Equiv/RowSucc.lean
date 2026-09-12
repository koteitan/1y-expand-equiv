import Equiv.Row0
import OneY.NumericGeometry

/-!
# 行 `r+1` の親：正値条件は「鎖の根を除く」ことと同じ

Lean 側の行 `r+1` の親は

```
(rows base (r+1)).forest.parent c
  = restrictedParent (rows base r).forest (rows base r).difference c
  = greatestBelow? c (fun p => p が行 r の森で c の祖先
                             ∧ 0 < 差分 p ∧ 差分 p < 差分 c)
```

である。JS 側は行 `r` の親チェーンを辿って最初に値の小さいものを取るだけで、
正値条件に当たるものを持たない。両者が食い違わない理由は次の一点にある。

> 行 `r` で親を持つ列は、行 `r+1` で必ず値が正になる。

したがって祖先鎖 `c > p₁ > p₂ > … > p_last` のうち、行 `r+1` で死んでいるのは
鎖の根 `p_last` だけであり、正値条件はちょうどその根だけを落とす。
本ファイルはこれを示す。
-/

namespace Yukito

open OneY.Numeric

/-- 行 `r+1` の値は行 `r` の差分そのもの。 -/
theorem succ_value (base : Row) (r c : Nat) :
    (rows base (r+1)).value c = (rows base r).difference c := rfl

/-- 正値条件は「行 `r` で親を持つ」ことと同値である。 -/
theorem pos_iff_has_parent (base : Row) (r p : Nat) :
    0 < (rows base (r+1)).value p ↔ ∃ q, (rows base r).forest.parent p = some q :=
  (rows_parent_iff_next_live base r p).symm

/-- 行 `r+1` の親の特徴づけ。正値条件を「鎖の根でない」に読み替えたもの。 -/
theorem succ_parent_iff (base : Row) (r c p : Nat) :
    (rows base (r+1)).forest.parent c = some p ↔
      ZeroY.Forest.Ancestor (rows base r).forest.parent c p ∧
      (∃ q, (rows base r).forest.parent p = some q) ∧
      (rows base (r+1)).value p < (rows base (r+1)).value c ∧
      ∀ q, ZeroY.Forest.Ancestor (rows base r).forest.parent c q →
        (∃ t, (rows base r).forest.parent q = some t) →
        (rows base (r+1)).value q < (rows base (r+1)).value c → q ≤ p := by
  have h := restrictedParent_some_iff (rows base r).forest (rows base r).difference c p
  simp only [← succ_value] at h
  rw [show (rows base (r+1)).forest.parent c
        = restrictedParent (rows base r).forest (rows base r).difference c from rfl, h]
  constructor
  · rintro ⟨ha, hpos, hlt, hmax⟩
    exact ⟨ha, (pos_iff_has_parent base r p).mp hpos, hlt,
      fun q hq hqp hlt' => hmax q hq ((pos_iff_has_parent base r q).mpr hqp) hlt'⟩
  · rintro ⟨ha, hpar, hlt, hmax⟩
    exact ⟨ha, (pos_iff_has_parent base r p).mpr hpar, hlt,
      fun q hq hqpos hlt' => hmax q hq ((pos_iff_has_parent base r q).mp hqpos) hlt'⟩

/-- 鎖の根だけが行 `r+1` で死んでいる。すなわち、行 `r` の森で `c` の祖先 `p` が
自分も親を持つなら、`p` は行 `r+1` で生きている。 -/
theorem chain_live_of_nonroot (base : Row) (r c p q : Nat)
    (_hanc : ZeroY.Forest.Ancestor (rows base r).forest.parent c p)
    (hq : (rows base r).forest.parent p = some q) :
    0 < (rows base (r+1)).value p :=
  (pos_iff_has_parent base r p).mpr ⟨q, hq⟩

/-- 逆向き。行 `r+1` で死んでいる列は行 `r` の森で根である。 -/
theorem root_of_dead (base : Row) (r p : Nat)
    (hdead : (rows base (r+1)).value p = 0) :
    (rows base r).forest.parent p = none := by
  cases hp : (rows base r).forest.parent p with
  | none => rfl
  | some q =>
      have h := (pos_iff_has_parent base r p).mpr ⟨q, hp⟩
      omega

/-- 行 0 の証明の最終段は `r` に依らない。親の値についての 2 つの不等式から、
差分についての不等式が出る。

`v p = U p - U root`、`v j = U j - U t` であり、`U t ≤ U root` と `U p ≤ U j`
から `v p ≤ v j` が従う。 -/
theorem difference_le_of_value_le (a : Row) {p root j t : Nat}
    (hp : a.forest.parent p = some root)
    (ht : a.forest.parent j = some t)
    (hUt : a.value t ≤ a.value root)
    (hUpj : a.value p ≤ a.value j) :
    a.difference p ≤ a.difference j := by
  have h1 : a.difference p = a.value p - a.value root := by
    simp only [Row.difference, hp]
  have h2 : a.difference j = a.value j - a.value t := by
    simp only [Row.difference, ht]
  omega

/-- 上を行 `r` に当てはめた形。 -/
theorem succ_value_le (base : Row) (r : Nat) {p root j t : Nat}
    (hp : (rows base r).forest.parent p = some root)
    (ht : (rows base r).forest.parent j = some t)
    (hUt : (rows base r).value t ≤ (rows base r).value root)
    (hUpj : (rows base r).value p ≤ (rows base r).value j) :
    (rows base (r+1)).value p ≤ (rows base (r+1)).value j :=
  difference_le_of_value_le (rows base r) hp ht hUt hUpj

/-! ## 密表現側：行 `r` では列 `r` 未満は死んでいる -/

/-- 行 `r` では列 `r` 未満の値は 0。列 `c` が行 `r+1` で生きるにはその親が行 `r` で
生きていなければならず、親は左にあるから、生きた列は 1 行ごとに右へ 1 つ以上ずれる。 -/
theorem rows_value_zero_of_lt (base : Row) :
    ∀ r c, c < r → (rows base r).value c = 0 := by
  intro r
  induction r with
  | zero => intro c h; exact absurd h (Nat.not_lt_zero c)
  | succ r ih =>
      intro c hc
      show (rows base r).difference c = 0
      cases hp : (rows base r).forest.parent c with
      | none => simp only [Row.difference, hp]
      | some p =>
          exfalso
          have hpv := ((rows base r).parent_values hp).1
          have hlt := (rows base r).forest.parent_left hp
          rw [ih p (by omega)] at hpv
          omega

/-- 入力列の外の列は値 1 である。`ofSequence` がそう定めている。 -/
theorem ofSequence_value_ge (s : List Nat) (c : Nat) (h : s.length ≤ c) :
    (ofSequence s).value c = 1 := by
  show s[c]?.getD 1 = 1
  rw [List.getElem?_eq_none h]
  rfl

/-- 入力列の外の列は行 1 以降では死んでいる。値 1 の列は親を持てないからである。 -/
theorem rows_value_zero_of_ge (s : List Nat) (r c : Nat) (hr : 0 < r)
    (h : s.length ≤ c) : (rows (ofSequence s) r).value c = 0 := by
  have h1 : (rows (ofSequence s) 1).value c = 0 := by
    show (ofSequence s).difference c = 0
    have hn := Row.parent_none_of_one (ofSequence s) (ofSequence_value_ge s c h)
    simp only [Row.difference, hn]
  have h2 : (rows (ofSequence s) r).value c ≤ (rows (ofSequence s) 1).value c :=
    rows_value_antitone (ofSequence s) hr c
  omega


end Yukito
