import Equiv.DiagBridge
import OneY.Expansion

/-!
# bad root と `expand` の分岐

Phyrion の `expandValues` は最後の列の bad root で分岐する。

```
match findBadRoot s hs (s.length − 1) with
| none   => s.take (s.length − 1)
| some z => reconstructedValues … (x + N*(x − z.column))
```

JS の `expand` は「行 0 の最後のセルが親を持たない」で分岐し、持たなければ最後の列を
落とす。この 2 つの分岐条件が同じであることを示す。
-/

namespace Yukito

open OneY OneY.Numeric

/-- **`expand` の分岐条件が一致する。** JS の「行 0 の最後のセルに親が無い」と、
Phyrion の「`findBadRoot` が `none`」は同値である。 -/
theorem last_parent_none_iff (s : List Nat) (hs : ZeroY.Legal s) (fuel : Nat)
    (hf : sequenceBound s ≤ fuel) (hn : 0 < s.length) :
    readPar (rowAt (calcMountain s (fuel + 1)) 0) 0 (s.length - 1) = none
      ↔ findBadRoot s hs (s.length - 1) = none := by
  have h0 : (0 : Nat) < (calcMountain s (fuel + 1)).length :=
    calcMountainFrom_length_pos _ fuel
  rw [findBadRoot_none_iff, rowAt_eq _ 0 h0,
    calcMountain_parent s hs.1 fuel 0 (s.length - 1) h0 (by omega)]
  exact Iff.rfl

end Yukito
