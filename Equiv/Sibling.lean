import Equiv.RootGen
import Equiv.Row0Spec

/-!
# 兄弟の単調性

`Φ = restrictedParent F U` において、同じ親を持つ 2 列 `q1 < q2` は

```
U q1 ≥ U q2
```

を満たす。これを **兄弟の単調性** と呼ぶ。

## なぜ要るか

残る義務 (1)「`U p ≤ U j`」は、`j` が `p` の `F` 祖先でない場合が未解決だった。
その場合 `j` と `p` は `Φ` 兄弟（共通の親が `root`）になるので、
兄弟の単調性から `U j ≥ U p` が直ちに出る。

## 層をまたぐ関係

行 `r` の森における兄弟の単調性は、値 `U` が行 `r-1` の差分であることから、
一段下の同じ主張に帰着する。`F.parent q1 = F.parent q2 = t` なら

```
U q1 = U' q1 - U' t,   U q2 = U' q2 - U' t
```

なので `U q1 ≥ U q2` と `U' q1 ≥ U' q2` は同値である。

### 潰した筋

一般の行で (ii) を (i) から出そうとして、次の 2 つを試したがどちらも破れた。

* **合流点を使う筋**。`q1` と `q2` の `F` 鎖の合流点 `m` を取り、`m` の直上の
  両側の要素 `u'`, `z'` が `F` 兄弟になることを使う。`U u' ≥ U z' ≥ U q2` は
  出るが、最大性が与えるのは `U u' ≥ U q1` で向きが逆であり、`q1` と `q2` を
  比べられない。`u' = q1` なら閉じるが、そうならない例がある。
  列 `(1,1,1,2,4,6,4)` の行 1 で `q1 = 5` の親は `4`、`q2 = 6` の鎖は `3, 2` で
  `4` を含まない。
* **甥の筋**。`w < z` が `F` 兄弟で `q1` が `w` の部分木にあれば `U q1 ≥ U z`、
  という形。列 `(1,1,1,1,2,4,5,4)` の行 1 が反例で、`U 6 = 1 < U 7 = 2` となる。

後者の反例では `6` は `Φ` 根であって `7` の兄弟ではない。ここに機構がある。
**値が小さい列は `Φ` 親を失って根になり、兄弟の関係から外れる。** したがって
(ii) の証明には、森の形だけでなく値の算術が要る。

基底は行 0 である。行 0 の frame は線形なので、`root` と `q2` の間の列はすべて
祖先であり、最大性がそのまま「間の列の値は `U q2` 以上」を与える。
一般の行ではこの強い形は成り立たない（列 `(1,1,1,1,2,4,5,4)` が反例）が、
兄弟に限れば成り立つ。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 兄弟の単調性。 -/
def SiblingMono (F : ParentForest) (U : Nat → Nat) : Prop :=
  ∀ t q1 q2, restrictedParent F U q1 = some t → restrictedParent F U q2 = some t →
    q1 < q2 → U q2 ≤ U q1

/-- 行 0 では、`root` と `q2` の間の列はすべて値が `U q2` 以上である。
frame が線形なので、間の列は自動的に祖先になり、最大性が効く。 -/
theorem between_ge_zero {U : Nat → Nat} (hv : ∀ p, 0 < U p) {root q2 t : Nat}
    (hq2 : restrictedParent linearForest U q2 = some root)
    (h1 : root < t) (h2 : t < q2) : U q2 ≤ U t := by
  obtain ⟨_, _, hmax⟩ := (parent0_some_iff hv q2 root).mp hq2
  rcases Nat.lt_or_ge (U t) (U q2) with hlt | hge
  · have := hmax t h2 hlt
    omega
  · exact hge

/-- 行 0 の兄弟の単調性。上の間の性質から直ちに従う。 -/
theorem siblingMono_zero {U : Nat → Nat} (hv : ∀ p, 0 < U p) :
    SiblingMono linearForest U := by
  intro t q1 q2 h1 h2 hlt
  have hlt1 : t < q1 := ((parent0_some_iff hv q1 t).mp h1).1
  exact between_ge_zero hv h2 hlt1 hlt

/-- 兄弟の単調性があれば、`j` が `p` の `F` 祖先でない場合の (1) が出る。
その場合 `j` と `p` は共通の親 `root` を持つ。 -/
theorem one_of_sibling {F : ParentForest} {U : Nat → Nat}
    (hsib : SiblingMono F U) {root p j : Nat}
    (hp : restrictedParent F U p = some root)
    (hj : restrictedParent F U j = some root)
    (hjp : j < p) : U p ≤ U j :=
  hsib root j p hj hp hjp

end Yukito
