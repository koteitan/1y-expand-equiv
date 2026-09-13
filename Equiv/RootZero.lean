import Equiv.Row0
import Equiv.RowSucc

/-!
# `FirstLiveNotSmaller` の行 0 の場合

記号を固定する。`V` を行 0 の値、`F` を行 0 の森（左で最も近い小さい列）、
`w q` を行 1 の値、すなわち `w q = V q - V (F.parent q)`（親が無ければ 0）とする。

`root` を `c` の鎖の根、`j` を `root` より右で最初に「行 1 で生きている」列とする。
`p` を鎖で `root` の 1 つ手前の要素（`F.parent p = root`）とする。

証明の筋は次のとおり。

1. `F.parent p = root` から `V root < V p`
2. `root` は根なので、`root` より左の列 `t` は `V root ≤ V t`
3. `(root, j)` の列はすべて根なので、`V q ≤ V root`
4. `F.parent p = root` の最大性から、`root < t < p` なら `V p ≤ V t`。とくに `V p ≤ V j`
5. 1 と 4 から `V root < V j`。よって `F.parent j` は `root` 以上の位置にある
6. 5 と 3 から `V (F.parent j) ≤ V root`
7. `w j = V j - V (F.parent j) ≥ V j - V root ≥ V p - V root = w p`
-/

namespace Yukito

open OneY OneY.Numeric

variable {V : Nat → Nat}

/-- 行 1 の値。親が無ければ 0。 -/
def w (V : Nat → Nat) (q : Nat) : Nat :=
  match restrictedParent linearForest V q with
  | none => 0
  | some t => V q - V t

end Yukito
