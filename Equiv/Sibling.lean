import Equiv.RootGen
import Equiv.Row0Spec

/-!
# 兄弟の単調性

`Φ = restrictedParent F U` において、同じ親を持つ 2 列 `q1 < q2` は

```
U q1 ≥ U q2
```

を満たす。これを **兄弟の単調性** と呼ぶ。

## 一般の行では偽である

**一般の行で兄弟の単調性は成り立たない。** 反例は列 `(1,1,2,5,7,5)` の行 1 で、

```
Fp = [-1,-1, 1, 2, 3, 2]        U = [0, 0, 1, 3, 2, 3]
Φ  = [-1,-1,-1, 2, 2, 2]
```

`q1 = 4` と `q2 = 5` はどちらも親が `2` の兄弟だが `U 4 = 2 < U 5 = 3` である。

したがって下の `SiblingMono` を一般の行について仮定してはならない。
行 0 については真であり、`siblingMono_zero` で証明してある。

## なぜ要るか

残る義務 (1)「`U p ≤ U j`」で `j` が `p` の `F` 祖先でない場合、`j` と `p` は
`Φ` 兄弟になる。しかし上のとおり兄弟であるだけでは足りない。実際の配置では
`j` は **`root` より右で最初に生きている列** であり、この条件が効いている。
上の反例でも `root = 2` の次に生きている列は `3` であって `4` ではないので、
実際の配置には現れない。

`one_of_sibling` は `SiblingMono` を仮定した条件付きの定理である。一般の行では
その仮定が成り立たないので、そのままでは使えない。

### 一段下の形も偽である

`F` 兄弟についての同じ主張（`F.parent q1 = F.parent q2` なら `U q1 ≥ U q2`）も
偽である。反例は列 `(1,2,4,8,11,8)` の行 2 で、親 `2` を共有する列 `4` と `5` が
`U 4 = 1 < U 5 = 2` となる。下の帰着が正しいので、これは上と同じ事実の別の層である。

## 層をまたぐ関係

行 `r` の森における兄弟の単調性は、値 `U` が行 `r-1` の差分であることから、
一段下の同じ主張に帰着する。`F.parent q1 = F.parent q2 = t` なら

```
U q1 = U' q1 - U' t,   U q2 = U' q2 - U' t
```

なので `U q1 ≥ U q2` と `U' q1 ≥ U' q2` は同値である。

### 潰した筋

まず、一般の行の兄弟の単調性そのものが偽である（上記）。
偽と分かる前に (ii) を (i) から出そうとして次の 2 つを試したが、どちらも破れた。

* **合流点を使う筋**。`q1` と `q2` の `F` 鎖の合流点 `m` を取り、`m` の直上の
  両側の要素 `u'`, `z'` が `F` 兄弟になることを使う。`U u' ≥ U z' ≥ U q2` は
  出るが、最大性が与えるのは `U u' ≥ U q1` で向きが逆であり、`q1` と `q2` を
  比べられない。`u' = q1` なら閉じるが、そうならない例がある。
  列 `(1,1,1,2,4,6,4)` の行 1 で `q1 = 5` の親は `4`、`q2 = 6` の鎖は `3, 2` で
  `4` を含まない。
* **甥の筋**。`w < z` が `F` 兄弟で `q1` が `w` の部分木にあれば `U q1 ≥ U z`、
  という形。列 `(1,1,1,1,2,4,5,4)` の行 1 が反例で、`U 6 = 1 < U 7 = 2` となる。

後者の反例では `6` は `Φ` 根であって `7` の兄弟ではない。

さらに、次の「台地」の形も偽である。`Φ.parent q = root` のとき
`root < u < q` なる `q` の `F` 祖先 `u` はすべて `U u = U q` を満たす、という形で、
列 `(1,1,1,2,5,7)` の行 1 が反例（`U 4 = 3`、`U 5 = 2`）。

これらの反例はいずれも値を 7 以上にしないと現れない。値 6 までの探索では
見つからなかった。予想を確かめるときは値の範囲を十分に取ること。

### 「兄弟」を「間にある」に緩めても偽

`q1` が `q2` の親 `t` と `q2` の間にあるだけでは足りない。兄弟であることが要る。
反例は列 `(1,1,2,5,7,5)` で、frame を `rows 0` の森、値を `rows 1` の値とすると

```
F = [-1,-1, 1, 2, 3, 2]      U = [0, 0, 1, 3, 2, 3]
```

`t = F 5 = 2`、`q1 = 4`、`q2 = 5` で `t < q1 < q2` かつ `q1` は生きているが
`U 4 = 2 < U 5 = 3` となる。`F 4 = 3 ≠ 2 = F 5` なので兄弟ではない。

層の対応を取り違えると別の反例が出るので注意する。正しい対応は
「frame が `rows k` の森、値が `rows (k+1)` の値、liveness が `rows (k+1)` の森」
である。

### 一貫している機構

一般化した主張を破る列は、調べたかぎり例外なく **次の行で死んでいるか、
`root` より右で最初に生きている列ではない**。たとえば `(1,2,4,8,11,8)` の行 2 で
`(i)` を破る列 `4` は `Φ.parent 4 = none` で行 3 では死んでおり、実際の `j` は
`3` である。したがって証明は「`j` が最初の生きている列である」ことを本質的に
使う必要がある。この条件を落とした一般化はすべて偽になる。

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
