[← 戻る](README.md)

# `script.js` と `Equiv/Yukito.lean` の行対応

`Equiv/Yukito.lean` は [Naruyoko/YNySequence](https://github.com/Naruyoko/YNySequence) の
`script.js` を Lean に写したものである。この表はどの行がどの定義になったかを示す。

行番号は次のスナップショットのものである。

```
Naruyoko/YNySequence  コミット 2de1397  script.js  477 行
```

## 全体の対応

| `script.js` | 役割 | `Equiv/Yukito.lean` |
|---|---|---|
| 15–31 | `parseSequenceElement` | 111 `row0` / 261 `parseDiag` / 254 `clampPar` |
| 32–86 | `calcMountain` | 129 `calcMountain` / 124 `calcMountainFrom` |
| 87–145 | `calcDiagonal` | 242 `calcDiagonal` |
| 146–161 | `cloneMountain` | 写していない（不変な値なので複製が要らない） |
| 162–174 | `getBadRoot` | 285 `getBadRoot` |
| 175–403 | `expand` | 578 `expandJS` / 574 `expandOut` |

## セルと行

| `script.js` | Lean |
|---|---|
| `{value, position, parentIndex, forcedParent}` | 25–30 `structure Cell`（`pos` / `val` / `par` / `forced`） |
| `parentIndex = -1` | `par = none` |
| `lastLayer`（`position` 昇順の疎配列） | 33 `abbrev Rowj := Array Cell` |
| `while (row[j].position < t) j++` | 38 `scanFrom` / 46 `firstAtLeast` |
| `mountain[h]` | 143 `rowAt`（範囲外は空行） |

## `parseSequenceElement`（15–31）

| `script.js` | Lean |
|---|---|
| 16–22 素の数の枝 | 111 `row0`（`forced := false`） |
| 23–30 `"値v親"` の枝 | 261 `parseDiag`（`forced := true`） |
| 27 `Math.max(Math.min(i-1,p),-1)` | 254 `clampPar` |

入力の文字列を解析する部分は写していない。Lean 側は `calcDiagonal` の出力を
文字列にせず `List DiagItem` のまま `parseDiag` に渡す。

## `calcMountain`（32–86）

| `script.js` | Lean |
|---|---|
| 34–38 文字列か配列かの分岐 | 129 `calcMountain` / 124 `calcMountainFrom` |
| 39 `calculatedMountain=[lastLayer]` | 124–126 `calcMountainFrom` |
| 40 `while (true)` | 116–120 `mountainGo`（`fuel` で止める） |
| 41–74 親の割り当て | 101 `assignParents` |
| 44–47 `forcedParent` なら `continue` | 103 `if c.forced then c` |
| 49–50 `calculatedMountain.length==1` | 106 `match prev with \| none` |
| 52–53 `p` の初期化 | 107–108 `firstAtLeast pv (c.pos + 1)` |
| 55–73 探索ループ（行 0） | 80–86 `searchBase` |
| 55–73 探索ループ（行 1 以上） | 58–77 `searchUpper` |
| 56 `if (p<0) break` | 64 `match prev[p].par with \| none => none` |
| 58–60 `p--; j=p-1;` | 83–85 `searchBase` の再帰 |
| 62 `p=…[p].parentIndex` | 63–65 `prev[p].par` |
| 65 `while (lastLayer[j].position < …) j++` | 68 `firstAtLeast row target` |
| 67 `break` の条件 | 51 `breakHere` |
| 68–71 `lastLayer[j].value < lastLayer[i].value` | 71–73 `row[j].val < row[i].val` |
| 75 `if (!hasNextLayer) break` | 119 `if cur.all (fun c => c.par.isNone)` |
| 76–83 次の階差行 | 90 `nextRow` |
| 85 `return calculatedMountain` | 116–120 `mountainGo` の返り値 |

`hasNextLayer` は JS では親の割り当てと同時に立てるフラグだが、Lean では
割り当て後の行を見て「どのセルも親を持たない」で判定する。同じ条件である。

## `calcDiagonal`（87–145）

| `script.js` | Lean |
|---|---|
| 90 列 `i` のループ | 217 `diagList` |
| 91–94 列 `i` を含む最上段を探す | 146 `topAt` |
| 93 `while (mountain[j][k] && …) k++` | 157 `lookupPos` |
| 95–96 `height` / `lastIndex` | 193 `legWalkJS` の状態 `(h, idx)` |
| 97–118 脚の歩行 | 162 `legStepJS` / 193 `legWalkJS` |
| 98–99 `height==0` の枝 | 166–169 `legStepJS` |
| 101–103 右下へ行って親を取る | 171–178 `legStepJS` |
| 104–107 その左上（＝左）を探す | 183–186 `legStepJS` |
| 108–111 左が無ければ 1 段下がる | 187 `legStepJS` |
| 113–117 停止条件と `push` | 200–203 `legWalkJS` / 207 `diagEntry` |
| 122–132 `pw` | 221 `pwScan` |
| 133–142 `diagonalTree` を辿る | 226 `treeScan` / 248 |
| 140–141 `"v"` を付けるか | 234 `DiagItem` / 250–251 |
| 144 `r.join(",")` | 写していない（文字列にしない） |

## `getBadRoot`（162–174）

| `script.js` | Lean |
|---|---|
| 163–165 文字列か配列か | 引数がすでに山 |
| 166 対角の山を作る | 288 `calcMountainFrom (parseDiag (calcDiagonal M)) mfuel` |
| 167 `diagonal[0][…].value!=1` | 289 `lastVal (rowAt d 0) = 1` / 276 `lastVal` |
| 168 再帰 | 300 `getBadRoot d mfuel fuel` |
| 170 最上段を探す | 280 `topRowOfLast` / 290 |
| 171 その 1 つ下の段で最後のセルの親を返す | 293–298 |

## `expand`（175–403）

### 入口と分岐（175–224）

| `script.js` | Lean |
|---|---|
| 176–179 引数の正規化と複製 | 578–580（引数がすでに山） |
| 180–181 最後のセルに親が無い枝 | 583–585 `hasPar` / `fillValues (dropEmptyTop (M.set 0 row0.pop))` |
| 184–185 `cutHeight` | 587 `topRowOfLast M n M.length` |
| 187 `badRootSeam` | 588 `getBadRoot M mfuel mfuel` |
| 189 `diagonal` | 589 `calcMountainFrom (parseDiag (calcDiagonal M)) mfuel` |
| 191 `yamakazi` | 590 `lastVal (rowAt dg 0) = 1` |
| 192–199 山崎噴火の `newDiagonal` | 569 `yamaVal` / 592 |
| 200–201 `cutHeight--` と `badRootHeight` | 594–595 |
| 203 `expand(diagonal,n,false)` | 593（`efuel` で止まる再帰） |
| 204–210 `badRootHeight` の走査 | 563 `topRowWithCol` / 595 |
| 212–213 子を切る | 517 `cutChild` / 596 |
| 214 `afterCutHeight` | 599 `res.length` |
| 216 `afterCutLength` | 597 `acl` |
| 217–224 `badRootSeamHeight` | 写していない（この後どこでも使われない） |
| 215 `afterCutMountain` | 写していない（同上） |

`FujiParams`（377）が `badRootSeam` / `badRootHeight` / `cutHeight` /
`afterCutLength` / `yamakazi` の 5 つをまとめたものである（598 で組み立てる）。

### Mt.Fuji シェル（225–376）

| `script.js` | Lean |
|---|---|
| 226 `for (var i=1;i<=n;i++)` | 493 `fujiIters` |
| 227 `for (var j=badRootSeam;j<afterCutLength;j++)` | 479 `fujiSeams` |
| 228–245 `isAscending` | 348 `isAscending` / 333 `ascendTo` / 486 |
| 246–253 `seamHeight` | 328 `seamHeightOf` / 321 `hasCol` / 487 |
| 254 `isReplacingCut` | 485 `isRep := decide (j = P.badRootSeam)` |
| 256 `if (isAscending)` | 463 `fujiSourceAt` / 489 `kmax` |
| 257 `for (var k=0;k<seamHeight+(cutHeight−badRootHeight)*i;k++)` | 466 `fujiRows` / 489 |
| 259–279 Bb（`k<badRootHeight`） | 453 `fujiSource` 第 1 枝 |
| 280–300 Br replace | 454–455 第 2 枝 |
| 301–321 Br extend | 456–457 第 3 枝 |
| 322–344 Be | 458 第 4 枝 |
| 348 `for (var k=0;k<seamHeight;k++)`（上りでない側） | 489 `else seamH` |
| 351–373 Bb だけ | 463 `else (k, isRep)` |

4 つの枝は `sy`（元の段）と `sx`（元のセルを行の最後から取るか）の選び方だけが
違うので、`fujiSource`（450）にまとめてある。積むセルの中身は共通で、次のとおり。

| `script.js`（各枝の中） | Lean |
|---|---|
| `sx=mountain[sy].length-1` / `while (…) sx++` | 393 `sourceIdx` |
| `var sourceParentIndex=mountain[sy][sx].parentIndex` | 397 `parentPos` |
| `var parentPosition=…` | 397 `parentPos` |
| `while (result[k][parentIndex]…) parentIndex++` | 157 `lookupPos` |
| `result[k].push({…})` | 413 `fujiCell` / 445 `pushAt` |
| `if (!result[k]) result.push([])` | 445 `pushAt`（段が無ければ作る） |

### 値の埋めと出力（378–402）

| `script.js` | Lean |
|---|---|
| 379 上から下へ | 534 `fillValues` |
| 380–383 空段を落とす | 542 `dropEmptyTop` |
| 384–390 `NaN` を埋める | 526 `fillRow` |
| 385 `if (!isNaN(…)) continue` | 526 `fillRow`（値 0 を「未確定」の印にする） |
| 389 `親の値 + 1 つ上の段の同じ列の値` | 526 `fillRow` |
| 393–398 `stringify` | 574 `expandOut` |

## 意図的に違えたところ

**燃料。** JS の `while (true)` は Lean では停止しないので、`calcMountain` /
`getBadRoot` / `expand` の再帰に燃料を付けた。主定理はどの燃料も十分大きければ
よい、という形になっている。

```
mfuel  山を作る／bad root を探すループの上限
efuel  newDiagonal = expand(diagonal, n, false) の再帰の上限
ascFuel  isAscending の親鎖を辿るループの上限
```

**`-1` と `undefined`。** JS の `parentIndex = -1` は `Option Nat` の `none`、
配列外の `mountain[h][k]` は空行（`rowAt`）または `none`（`lookupPos`）にした。
`parentPosition` が負になる場合は `parentPos` が `none` を返す。

**自然数の切り捨て引き算。** JS が `position - 1` を目標にする所（105、387）で
`position = 0` だと目標は `-1` になり、どのセルにも一致しない。Lean の `Nat` では
`0 - 1 = 0` になってしまうので、`legStepJS` の 183 行で `pos = 0` を場合分けして
「一致しない」側に倒してある。

**文字列。** `calcDiagonal` の `join(",")` と `parseSequenceElement` の解析は
往復して元に戻るだけなので、`List DiagItem` を直接渡す形にした。

**複製。** `cloneMountain` は JS が破壊的に書き換えるためのもので、Lean では要らない。

**使われない変数。** `badRootSeamHeight`（217–224）と `afterCutMountain`（215）は
JS で計算されるがその後どこでも読まれないので写していない。

**`newDiagonal` の重複 `position`。** JS は 197 で同じセルの参照を積むため
`position` が重複するが、値しか読まれない。Lean では値の関数 `Nat → Nat` として持つ。

## 忠実さの検査

この対応表は読み合わせであって、証明ではない。`script.js` は Lean の対象ではないので、
写しが原本と同じ関数であること自体は証明できない。代わりに原本を実行した出力と
突き合わせて `#guard` に固定してある（`Equiv/YukitoCheck.lean`）。`calcMountain` /
`calcDiagonal` / `getBadRoot` / `expand` の各段階と、`expand` の分岐を一通り通す例、
および上りでない列が `badRootHeight` より高くなる例を含む。
