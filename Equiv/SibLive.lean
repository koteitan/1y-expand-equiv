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

/-- 場合 3 の結合部。合流点の直上にある `z` について、`q2` 側は最大性で、
`q1` 側は再帰で押さえ、連鎖する。 -/
theorem sibling_case_meet {F : ParentForest} {U : Nat → Nat} {t z q1 q2 : Nat}
    (h2 : restrictedParent F U q2 = some t)
    (hz : ZeroY.Forest.Ancestor F.parent q2 z)
    (htz : t < z) (hzpos : 0 < U z)
    (hrec : U z ≤ U q1) : U q2 ≤ U q1 := by
  have := one_of_ancestor t q2 z h2 hz htz hzpos
  omega

/-! ## 残っているもの

場合 3 では、合流点 `m` の直上にある `q1` 側の要素 `u` が `q1` 自身であることが
要る。そうであれば `q1` と `z` が兄弟になり、`sibling_case_meet` で閉じる。

`u < q1` になると閉じない。実際、liveness を外した反例
（列 `(1,2,4,8,11,8)` の行 2）を降ろすと、層 1 で合流点 `2` に対し
`u = 3 < q1 = 4` となる。つまり **`u = q1` を保証しているのが liveness である**。

したがって残るのは次の 2 つ。

* liveness から `u = q1` を出すこと
* 3 択を `(層, q2)` の辞書式順序で回す整礎帰納の組み立て

値 12 までの探索では、実際の配置で `u < q1` は 1 度も起きなかった（合流点の
使用 5 件はすべて `u = q1`）。

## 追記：この 3 択は使わなかった

`SibSucc.lean` で別の道から閉じた。`q2` を一段下がる**前に** 共通の親の子まで
引き上げると、合流点の場合が現れない。本ファイルの `sibling_mono_zero` は
そちらの基底として使う。 -/

end Yukito
