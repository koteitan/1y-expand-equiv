import Equiv.Yukito

/-!
# 書き起こしの忠実性チェック

`Yukito.lean` は `script.js` の `calcMountain` を写したものである。写し間違いや
以後の書き換えで壊れていないことを、実際の JS の出力と突き合わせて確かめる。

下の期待値は `script.js` の `calcMountain` をそのまま実行して得たものである
（`parseSequenceElement` と `calcMountain` だけを取り出して評価した）。
セルは `{position, value, parentIndex}` の順に並べ、`parentIndex = -1` を
`none` に読み替えてある。

これは予想の検証ではなく、**書き起こしが原本と一致していること**の確認である。
-/

namespace Yukito

#guard calcMountain [1, 3, 3] 8 =
  [#[{ pos := 0, val := 1, par := none }, { pos := 1, val := 3, par := some 0 },
     { pos := 2, val := 3, par := some 0 }],
   #[{ pos := 0, val := 2, par := none }, { pos := 1, val := 2, par := none }]]

#guard calcMountain [1, 2, 4, 8] 8 =
  [#[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 },
     { pos := 2, val := 4, par := some 1 }, { pos := 3, val := 8, par := some 2 }],
   #[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 },
     { pos := 2, val := 4, par := some 1 }],
   #[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 }],
   #[{ pos := 0, val := 1, par := none }]]

#guard calcMountain [1, 3, 2, 5] 8 =
  [#[{ pos := 0, val := 1, par := none }, { pos := 1, val := 3, par := some 0 },
     { pos := 2, val := 2, par := some 0 }, { pos := 3, val := 5, par := some 2 }],
   #[{ pos := 0, val := 2, par := none }, { pos := 1, val := 1, par := none },
     { pos := 2, val := 3, par := some 1 }],
   #[{ pos := 1, val := 2, par := none }]]

#guard calcMountain [1, 1, 2, 3, 3] 8 =
  [#[{ pos := 0, val := 1, par := none }, { pos := 1, val := 1, par := none },
     { pos := 2, val := 2, par := some 1 }, { pos := 3, val := 3, par := some 2 },
     { pos := 4, val := 3, par := some 2 }],
   #[{ pos := 1, val := 1, par := none }, { pos := 2, val := 1, par := none },
     { pos := 3, val := 1, par := none }]]

#guard calcMountain [1, 2, 4, 8, 11, 8] 8 =
  [#[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 },
     { pos := 2, val := 4, par := some 1 }, { pos := 3, val := 8, par := some 2 },
     { pos := 4, val := 11, par := some 3 }, { pos := 5, val := 8, par := some 2 }],
   #[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 },
     { pos := 2, val := 4, par := some 1 }, { pos := 3, val := 3, par := some 1 },
     { pos := 4, val := 4, par := some 1 }],
   #[{ pos := 0, val := 1, par := none }, { pos := 1, val := 2, par := some 0 },
     { pos := 2, val := 1, par := none }, { pos := 3, val := 2, par := some 0 }],
   #[{ pos := 0, val := 1, par := none }, { pos := 2, val := 1, par := none }]]

/-! ## `calcDiagonal`

期待値は `script.js` の `calcDiagonal` の出力文字列を、`"値"` → `forced := false`、
`"値v親"` → `forced := true`（`-1` は `none`）に読み替えたものである。 -/

#guard calcDiagonal (calcMountain [1, 3, 3] 8) =
  [{ val := 1, forced := false, par := none },
   { val := 2, forced := false, par := none },
   { val := 2, forced := false, par := none }]

#guard calcDiagonal (calcMountain [1, 3, 2, 5] 8) =
  [{ val := 1, forced := false, par := none },
   { val := 2, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 2, forced := false, par := none }]

#guard calcDiagonal (calcMountain [1, 2, 4, 8, 11, 8] 8) =
  [{ val := 1, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 1, forced := false, par := none }]

-- `"v"` が出る例
#guard calcDiagonal (calcMountain [1, 3, 4, 3] 8) =
  [{ val := 1, forced := false, par := none },
   { val := 2, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 2, forced := true, par := some 0 }]

#guard calcDiagonal (calcMountain [1, 4, 5, 3] 8) =
  [{ val := 1, forced := false, par := none },
   { val := 3, forced := false, par := none },
   { val := 1, forced := false, par := none },
   { val := 2, forced := true, par := some 0 }]

/-! ## `getBadRoot`

期待値は `script.js` の `getBadRoot` を実行して得たもの。 -/

#guard getBadRoot (calcMountain [1, 3, 3] 8) 8 8 = some 0
#guard getBadRoot (calcMountain [1, 2, 4, 8] 8) 8 8 = some 2
#guard getBadRoot (calcMountain [1, 3, 2, 5] 8) 8 8 = some 2
#guard getBadRoot (calcMountain [1, 1, 2, 3, 3] 8) 8 8 = some 2
#guard getBadRoot (calcMountain [1, 2, 4, 8, 11, 8] 12) 12 12 = some 2
#guard getBadRoot (calcMountain [1, 3, 4, 3] 8) 8 8 = some 0
#guard getBadRoot (calcMountain [1, 4, 5, 3] 8) 8 8 = some 0

end Yukito
