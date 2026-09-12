import Equiv.FirstLive
import Equiv.Row0Spec

/-!
# 生きた左の兄弟についての単調性

残る 1 本は次である。

```
(rows base (k-1)).forest 兄弟 q1 < q2 で q1 が生きているなら
  (rows base k).value q2 ≤ (rows base k).value q1
```

「生きている」は `(rows base (k+1)).value q1 > 0` を指す。この条件は外せない。
外した形は偽で、列 `(1,2,4,8,11,8)` の行 2 が反例である（`Sibling.lean`）。

## 帰納法が一様になること

層 `k` で兄弟なら `sibling_descent` により、目標は一段下の

```
(rows base (k-1)).value q2 ≤ (rows base (k-1)).value q1
```

に移る。このとき liveness の仮定は `(rows base k).value q1 > 0` へ弱まるが、
それは層 `k-1` の主張がちょうど要求するものである。したがって帰納法の仮定は
層をまたいで同じ形になる。弱まる向きは `rows_value_antitone` が保証する。

## 各層での場合分け

1. `q1` が `q2` の祖先 → `one_of_ancestor` で完了
2. `q1` と `q2` が兄弟 → `sibling_descent` で一段下へ
3. どちらでもない → 合流点 `m` を取り、`q2` を `m` の直上の要素 `z` に置き換える。
   `z < q2` なので `(層, q2)` の辞書式順序で減る

基底は行 0 である。frame が線形なので `q1 < q2` は常に 1 の場合になる。
-/

namespace Yukito

open OneY OneY.Numeric

/-- liveness は下の層へ伝播する。行が上がるほど値は増えないため。 -/
theorem live_descends (base : Row) (k q : Nat)
    (h : 0 < (rows base (k+1)).value q) : 0 < (rows base k).value q := by
  have := rows_value_le base k q
  omega

/-- 基底。行 0 の frame は線形なので `q1 < q2` なら `q1` は `q2` の祖先であり、
最大性がそのまま効く。 -/
theorem sibling_mono_zero {U : Nat → Nat} (hv : ∀ p, 0 < U p) {t q1 q2 : Nat}
    (h2 : restrictedParent linearForest U q2 = some t)
    (ht : t < q1) (hlt : q1 < q2) : U q2 ≤ U q1 :=
  one_of_ancestor t q2 q1 h2 ((linear_anc_zeroY q2 q1).mpr hlt) ht (hv q1)

/-- 場合 1。`q1` が frame で `q2` の祖先なら、`q2` の親の最大性で完了する。 -/
theorem sibling_case_ancestor {F : ParentForest} {U : Nat → Nat} {t q1 q2 : Nat}
    (h2 : restrictedParent F U q2 = some t)
    (hanc : ZeroY.Forest.Ancestor F.parent q2 q1)
    (ht : t < q1) (hpos : 0 < U q1) : U q2 ≤ U q1 :=
  one_of_ancestor t q2 q1 h2 hanc ht hpos

/-- 場合 2。兄弟なら目標が一段下に移る。 -/
theorem sibling_case_descent (base : Row) (k : Nat) {t q1 q2 : Nat}
    (h1 : (rows base k).forest.parent q1 = some t)
    (h2 : (rows base k).forest.parent q2 = some t)
    (hgoal : (rows base k).value q2 ≤ (rows base k).value q1) :
    (rows base (k+1)).value q2 ≤ (rows base (k+1)).value q1 :=
  (succ_sibling_descent base k h1 h2).mpr hgoal

end Yukito
