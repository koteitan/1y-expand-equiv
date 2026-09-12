import Equiv.RowSucc

/-!
# 残る義務：鎖の根を評価しても親にならないこと

`RowSucc.lean` で、行 `r` の祖先鎖のうち行 `r+1` で死んでいるのは鎖の根だけである
ことを示した（`root_of_dead`）。したがって JS の親探索は、根でない鎖要素の上では
Lean の `restrictedParent` とそのまま一致する。目標列が生きているので
`firstAtLeast` はその列を指し、値比較も同じになる。

食い違う余地は鎖の根を評価する 1 回だけである。そこでは目標列が死んでいるため
JS の `firstAtLeast` は右隣の生きた列 `j` を指してしまう。必要なのは、その `j` が
親に採用されないことである。

探索の結果、必要十分に近い形は次であった（`j = c` の場合は等号で含まれ、
JS の隙間 `break` は使わなくてよい）。

> 歩行が根に到達したなら、根より右で最初に生きている列 `j` は `v c ≤ v j` を満たす。

「歩行が根に到達した」は「根でない祖先はどれも `v c ≤ v q`」と言い換えられる。
すなわち下の `FirstLiveNotSmaller` である。
-/

namespace Yukito

open OneY.Numeric

/-- 列 `q` が行 `r` で生きている。 -/
def Live (base : Row) (r q : Nat) : Prop := 0 < (rows base r).value q

/-- `root` より真に右にある、行 `r+1` で最初に生きている列。
JS の `firstAtLeast` が指す列に対応する。 -/
def firstLiveAfter (base : Row) (r root : Nat) : Nat → Option Nat
  | 0 => none
  | fuel+1 =>
    let q := root + 1
    if 0 < (rows base (r+1)).value q then some q
    else firstLiveAfter base r q fuel

/-- 残る義務。JS の歩行が鎖の根に到達したとき、そこで指す列は親にならない。

前件の 3 つ目が「歩行が根に到達した」の言い換えである。根でない祖先 `q` は
すべて行 `r` で親を持つので行 `r+1` で生きており（`chain_live_of_nonroot`）、
JS はその列をそのまま見て比較する。どれも `v c` 未満でなかった、というのが
根に到達した条件である。 -/
def FirstLiveNotSmaller (base : Row) : Prop :=
  ∀ r c root j fuel,
    ZeroY.Forest.Ancestor (rows base r).forest.parent c root →
    (rows base r).forest.parent root = none →
    (∀ q, ZeroY.Forest.Ancestor (rows base r).forest.parent c q →
          (∃ t, (rows base r).forest.parent q = some t) →
          (rows base (r+1)).value c ≤ (rows base (r+1)).value q) →
    firstLiveAfter base r root fuel = some j →
    (rows base (r+1)).value c ≤ (rows base (r+1)).value j

/-- Lean 側は鎖の根を親に選ばない。正値条件がそれを排除する。 -/
theorem root_not_parent (base : Row) (r c root : Nat)
    (_hanc : ZeroY.Forest.Ancestor (rows base r).forest.parent c root)
    (hroot : (rows base r).forest.parent root = none) :
    (rows base (r+1)).forest.parent c ≠ some root := by
  intro h
  have hspec := (succ_parent_iff base r c root).mp h
  obtain ⟨_, ⟨q, hq⟩, _, _⟩ := hspec
  rw [hroot] at hq
  cases hq

/-- 根に到達したとき、JS が指す列 `j` は親にならない。
`FirstLiveNotSmaller` から直ちに従う。 -/
theorem js_root_step_no_parent (base : Row) (h : FirstLiveNotSmaller base)
    (r c root j fuel : Nat)
    (hanc : ZeroY.Forest.Ancestor (rows base r).forest.parent c root)
    (hroot : (rows base r).forest.parent root = none)
    (hreach : ∀ q, ZeroY.Forest.Ancestor (rows base r).forest.parent c q →
      (∃ t, (rows base r).forest.parent q = some t) →
      (rows base (r+1)).value c ≤ (rows base (r+1)).value q)
    (hj : firstLiveAfter base r root fuel = some j) :
    ¬ ((rows base (r+1)).value j < (rows base (r+1)).value c) := by
  have hle := h r c root j fuel hanc hroot hreach hj
  omega

end Yukito
