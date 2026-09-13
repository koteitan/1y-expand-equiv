import Equiv.Yukito
import ZeroY.Forest.MatrixParents
import ZeroY.Forest.Comparison

/-!
# 行 0 の親探索の一致

JS `calcMountain` の行 0 は

```js
p = position+1;
while (true){ p--; j = p-1; if (j<0) break;
              if (lastLayer[j].value < lastLayer[i].value){ parentIndex = j; break; } }
```

で `j = c-1, c-2, …, 0` と左へ走り、最初に値が小さいものを親にする。
Lean 側は `restrictedParent linearForest v c`、すなわち
`greatestBelow? c (fun p => p が c の祖先 ∧ 0 < v p ∧ v p < v c)` である。

行 0 の frame は `linearForest`（親は `c-1`）なので祖先条件は `p < c` と同値であり、
両者は同じ関数になる。本ファイルはそれを示す。
-/

namespace Yukito

open OneY.Numeric YesMetaZFC.BMS

/-- JS の左スキャンを値関数の形で書いたもの。`j` から下へ走る。 -/
def scanLeft (v : Nat → Nat) (target : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if v j < target then some j else scanLeft v target j

/-- 左スキャンは `greatestBelow?` そのものである。定義が同じ形なので帰納法で済む。 -/
theorem scanLeft_eq_greatestBelow (v : Nat → Nat) (target : Nat) :
    ∀ j, scanLeft v target j = greatestBelow? j (fun k => decide (v k < target))
  | 0 => rfl
  | j+1 => by
      simp only [scanLeft, greatestBelow?]
      by_cases h : v j < target
      · simp [h]
      · simp [h, scanLeft_eq_greatestBelow v target j]

/-- 行 0 の frame は線形森なので、祖先条件は `p < c` と同値である。 -/
theorem linear_ancestorChain_contains (c p : Nat) (hp : p < c) :
    (ancestorChain ZeroY.linearParent c c).contains p = true :=
  (ZeroY.Forest.ancestorChain_contains_iff ZeroY.linearParent_leftward).mpr
    (ZeroY.linearParent_ancestor_of_lt hp)

/-- 値がすべて正なら、行 0 の `restrictedParent` は左スキャンに一致する。
祖先条件は `greatestBelow?` の探索範囲 `p < c` に含まれ、正値条件は仮定から常に真。 -/
theorem restrictedParent_linear (v : Nat → Nat) (hv : ∀ p, 0 < v p) (c : Nat) :
    restrictedParent linearForest v c = scanLeft v (v c) c := by
  rw [scanLeft_eq_greatestBelow]
  unfold restrictedParent
  apply ZeroY.Forest.greatestBelow?_congr
  intro p hp
  simp only [linearForest, linear_ancestorChain_contains c p hp, Bool.true_and]
  simp [hv p]

end Yukito
