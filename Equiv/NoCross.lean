import Equiv.RootGen

/-!
# 辺の非交差性

森 `F` の辺が **真に交差しない** とは、

```
F.parent b = some a,  F.parent y = some x,  a < x < b < y
```

となる 4 点が無いことをいう。入れ子（`a < x < y < b`）は許す。

## 祖先版は偽である

「`a` が `b` の祖先、`x` が `y` の祖先で `a < x < b < y` は無い」という強い形は
成り立たない。反例は列 `(1,1,1,1,2,3,3)` の行 0 で、親写像は

```
親: [-,-,-,-,3,4,4]
```

`3` は `5` の祖先、`4` は `6` の祖先、`3 < 4 < 5 < 6` で交差する。
辺は `(3,4), (4,5), (4,6)` の 3 本だけで、こちらは交差しない。

したがって `ParentForest.Refines` を経由した継承（祖先の包含）では非交差性を
引き継げない。辺版を直接扱う必要がある。

## 帰納法の仮定は森の形だけでは足りない

`NoCross F` と「`U q = 0` ⟺ `q` は `F` 根」だけを仮定しても、
`NoCross (restrictedParent F U)` は出ない。反例:

```
F = [-1, 0, 1, 2, 2, 2, 2]
U = [ 0, 1, 4, 7, 3, 7, 7]
G = [-1,-1, 1, 2, 1, 2, 2]   →  a=1 < x=2 < b=4 < y=5 で交差する
```

この `U` は差分として実現できない。差分だとすると
`U' = [t, t+1, t+5, t+12, t+8, t+12, t+12]` となるが、
このとき列 5 の最近接小さい値は列 2 ではなく列 4 になり、`F` と食い違う。

したがって帰納法の仮定には、`U` が前の行の差分であるという関係を含める必要がある。
森の形だけを引き継ぐ形の帰納法は成立しない。

## 何に使うか

辺版があれば、残る義務 (a)「鎖の根 `root` は `j` の `F` 祖先である」が出る。
`j` の `F` 鎖が `root` を跨ぐとすると、跨ぐ辺 `(f', f)`（`f' < root < f`）と、
`p` の鎖にある辺 `(root, b')`（`root < b' ≤ p`）が現れる。`f < b'` なら
`f' < root < f < b'` で真の交差、`f = b'` なら `f' = root` で矛盾となる。
-/

namespace Yukito

open OneY OneY.Numeric

/-- 辺が真に交差しない。 -/
def NoCross (F : ParentForest) : Prop :=
  ∀ a b x y, F.parent b = some a → F.parent y = some x →
    a < x → x < b → b < y → False

/-- 線形森は非交差。辺は `(c-1, c)` の形しかないので、
`a < x < b < y` は `b - 1 < y - 1 < b` を要求して成り立たない。 -/
theorem noCross_linear : NoCross (linearForest : ParentForest) := by
  intro a b x y hb hy hax hxb hby
  -- linearForest の親は 1 つ前
  have hb' : b = a + 1 := by
    cases b with
    | zero => cases hb
    | succ n =>
        have : (some n : Option Nat) = some a := hb
        have hna : n = a := Option.some.inj this
        omega
  have hy' : y = x + 1 := by
    cases y with
    | zero => cases hy
    | succ n =>
        have : (some n : Option Nat) = some x := hy
        have hnx : n = x := Option.some.inj this
        omega
  omega

/-- 帰納段の第 1 の場合。`b` が `y` の `F` 祖先なら交差は起きない。

`x` と `b` は共に `y` の `F` 祖先で `x < b` なので、`x` は `b` の `F` 祖先である。
すると `a = G b` の最大性から `U b ≤ U x`、`x = G y` の最大性から `U y ≤ U b`、
あわせて `U y ≤ U x`。しかし `x = G y` は `U x < U y` を要求する。 -/
theorem noCross_of_ancestor {F : ParentForest} {U : Nat → Nat} {a b x y : Nat}
    (hb : restrictedParent F U b = some a)
    (hy : restrictedParent F U y = some x)
    (hax : a < x) (hxb : x < b)
    (hanc : ZeroY.Forest.Ancestor F.parent y b) : False := by
  obtain ⟨_, _, hUab, hmaxb⟩ := (restrictedParent_some_iff F U b a).mp hb
  obtain ⟨hxy, hUx, hUxy, hmaxy⟩ := (restrictedParent_some_iff F U y x).mp hy
  have hxb' : ZeroY.Forest.Ancestor F.parent b x :=
    ZeroY.Forest.ancestor_of_common_target F.parent_left hxy hanc hxb
  have h1 : ¬ (U x < U b) := by
    intro hlt
    have := hmaxb x hxb' hUx hlt
    omega
  have h2 : ¬ (U b < U y) := by
    intro hlt
    have := hmaxy b hanc (by omega) hlt
    omega
  omega

end Yukito
