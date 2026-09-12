import Equiv.Tower
import OneY.Pseudo

/-!
# 抽出段の対応

JS の `calcDiagonal` は、列 `c` の頂から出発して脚をたどり、
**その行で親を持たない節点**に着いたら止まる。

```js
if (!mountain[height][lastIndex] || mountain[height][lastIndex].parentIndex == -1) {
  diagonal.push(...); break;
}
```

Lean の `Pseudo.parent` は代わりに高さの条件を課す。

```
eligible M c p = p は行 (H c − 1) で c の祖先 ∧ (H p = H c ∨ H p + 1 = H c)
Pseudo.parent M c = greatestBelow? c (eligible M c)
```

見た目は違うが同じことを言っている。JS が訪れる節点 `(h, p)` は必ず行 `h` で
生きている、すなわち `h ≤ H p` を満たす。その状況で

```
その行で親を持たない  ⟺  H p ≤ h  ⟺  H p = h
```

となる。`≤` は `RowMountain.parent_none_iff` が与える。

歩行は高さ `H c` から始まり、脚を 1 つ進むごとに高さが変わらないか 1 下がる。
したがって止まった時点の高さは `H c` か `H c − 1` であり、そこで
`H p = h ∈ {H c − 1, H c}` が成り立つ。これが Lean の条件である。
-/

namespace Yukito

open OneY OneY.RootGeometry

/-- 行 `h` で生きている列について、「その行で親を持たない」ことと
「高さがちょうど `h`」は同値である。JS の停止条件はこれである。 -/
theorem top_iff_height_eq (M : RowMountain) {h p : Nat} (hlive : h ≤ M.height p) :
    (M.row h).parent p = none ↔ M.height p = h := by
  rw [M.parent_none_iff]
  omega

/-- 高さ `H c` で止まった場合。`H p = H c` となる。 -/
theorem stop_at_top (M : RowMountain) {c p : Nat}
    (hlive : M.height c ≤ M.height p)
    (hstop : (M.row (M.height c)).parent p = none) : M.height p = M.height c :=
  (top_iff_height_eq M hlive).mp hstop

/-- 高さ `H c − 1` に降りて止まった場合。`H p + 1 = H c` となる。 -/
theorem stop_after_drop (M : RowMountain) {c p : Nat} (hc : 0 < M.height c)
    (hlive : M.height c - 1 ≤ M.height p)
    (hnotlive : ¬ (M.height c ≤ M.height p))
    (hstop : (M.row (M.height c - 1)).parent p = none) : M.height p + 1 = M.height c := by
  have := (top_iff_height_eq M hlive).mp hstop
  omega

end Yukito
