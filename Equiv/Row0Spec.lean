import Equiv.Row0

/-!
# 行 0 の親の初等的な特徴づけ

行 0 の frame は線形森なので、祖先条件は `p < c` と同じである。したがって
行 0 の親は「左にある最も近い、値の小さい列」そのものになる。
`FirstLiveNotSmaller` の行 0 の場合を扱うための道具をここに揃える。

`restrictedParent_some_iff` は ZeroY 形式の祖先 `ZeroY.Forest.Ancestor F.parent c p`、
`restrictedParent_none_iff` は OneY 形式 `F.Ancestor p c` を使うので、両方の
言い換えを用意する。
-/

namespace Yukito

open OneY OneY.Numeric

variable {v : Nat → Nat}

/-- 線形森での祖先（ZeroY 形式）は `p < c` と同値。 -/
theorem linear_anc_zeroY (c p : Nat) :
    ZeroY.Forest.Ancestor (linearForest : ParentForest).parent c p ↔ p < c := by
  constructor
  · intro h; exact ZeroY.Forest.ancestor_lt ZeroY.linearParent_leftward h
  · intro h; exact ZeroY.linearParent_ancestor_of_lt h

/-- 線形森での祖先（OneY 形式）は `p < c` と同値。 -/
theorem linear_anc_oneY (c p : Nat) :
    (linearForest : ParentForest).Ancestor p c ↔ p < c := by
  rw [ParentForest.ancestor_iff_zeroY]
  exact linear_anc_zeroY c p

/-- 行 0 の親：左で最も近い、値の小さい列。 -/
theorem parent0_some_iff (hv : ∀ p, 0 < v p) (c p : Nat) :
    restrictedParent linearForest v c = some p ↔
      p < c ∧ v p < v c ∧ ∀ t, t < c → v t < v c → t ≤ p := by
  rw [restrictedParent_some_iff]
  constructor
  · rintro ⟨ha, _, hlt, hmax⟩
    exact ⟨(linear_anc_zeroY c p).mp ha, hlt,
      fun t ht hvt => hmax t ((linear_anc_zeroY c t).mpr ht) (hv t) hvt⟩
  · rintro ⟨hp, hlt, hmax⟩
    exact ⟨(linear_anc_zeroY c p).mpr hp, hv p, hlt,
      fun t ha _ hvt => hmax t ((linear_anc_zeroY c t).mp ha) hvt⟩

/-- 行 0 で親を持たない列は、左のどの列よりも値が大きくない。 -/
theorem parent0_none_iff (hv : ∀ p, 0 < v p) (c : Nat) :
    restrictedParent linearForest v c = none ↔ ∀ t, t < c → v c ≤ v t := by
  rw [restrictedParent_none_iff]
  constructor
  · intro h t ht
    exact h t ((linear_anc_oneY c t).mpr ht) (hv t)
  · intro h p ha _
    exact h p ((linear_anc_oneY c p).mp ha)

/-- 行 0 の根は、それより左のすべての列以下の値を持つ。 -/
theorem root0_le (hv : ∀ p, 0 < v p) {r : Nat}
    (hroot : restrictedParent linearForest v r = none) {t : Nat} (ht : t < r) :
    v r ≤ v t := (parent0_none_iff hv r).mp hroot t ht

end Yukito
