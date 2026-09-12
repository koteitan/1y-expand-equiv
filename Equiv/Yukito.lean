import OneY.Extraction

/-!
# Yukito の 1-Y 展開規則（Naruyoko 実装 `script.js`）の Lean への書き起こし

`YNySequence/script.js` の `calcMountain` を、疎配列表現・添字演算・
`break` の位置まで含めてそのまま写す。値の意味づけや簡約は行わない。

JS 側の 1 セルは `{value, position, parentIndex}` である。行 `r` の
`position` は「もとの列番号 − r」であり、本ファイルでは

```
列番号 c = position + r
```

を `Cell.col` として持たせる。`parentIndex` は同じ行の配列添字であって
列番号ではないので、`Option Nat` の添字として保持する。
-/

namespace Yukito

/-- JS の 1 セル。`par` は同じ行の配列添字（JS の `parentIndex`、`-1` は `none`）。
`forced` は JS の `forcedParent` で、入力が `"値v親"` の形だったときに立ち、
親探索を飛ばす。素の数から作った行では常に `false` である。 -/
structure Cell where
  pos : Nat
  val : Nat
  par : Option Nat
  forced : Bool := false
  deriving Repr, DecidableEq

/-- 行は JS の `lastLayer`（`position` 昇順の疎配列）。 -/
abbrev Rowj := Array Cell

/-- JS: `while (lastLayer[j].position < target) j++` で得る最初の添字。
配列を走り切ったら `row.size` を返す（JS では `lastLayer[j]` が
`undefined` になる位置）。 -/
def scanFrom (row : Rowj) (target : Nat) (j : Nat) : Nat :=
  if h : j < row.size then
    if row[j].pos < target then scanFrom row target (j+1) else j
  else j
termination_by row.size - j
decreasing_by simp_wf; omega

/-- `j = 0` から始めた形。JS の `var j=0; while (…) j++` にあたる。 -/
def firstAtLeast (row : Rowj) (target : Nat) : Nat := scanFrom row target 0

/-- JS の
`if (j<0 || j<lastLayer.length-1 && lastLayer[j].position+1!=lastLayer[j+1].position) break;`
の条件部。`j` は自然数なので `j<0` は「走り切った」に読み替える。 -/
def breakHere (row : Rowj) (j : Nat) : Bool :=
  if h : j < row.size then
    if h2 : j + 1 < row.size then row[j].pos + 1 ≠ row[j+1].pos else false
  else true

/-- JS の親探索ループ本体（行 `r ≥ 1`）。`prev` は 1 つ下の行。
`p` は `prev` の添字を辿る。`fuel` は `prev.size` で足りる。 -/
def searchUpper (prev row : Rowj) (i : Nat) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _+1, none => none
  | fuel+1, some p =>
    if hp : p < prev.size then
      match prev[p].par with
      | none => none                            -- JS: `if (p<0) break;`
      | some p' =>
        if hp' : p' < prev.size then
          let target := prev[p'].pos - 1
          let j := firstAtLeast row target
          if breakHere row j then none
          else if hj : j < row.size then
            if hi : i < row.size then
              if row[j].val < row[i].val then some j
              else searchUpper prev row i fuel (some p')
            else none
          else none
        else none
    else none

/-- JS の行 0 の親探索。`p--; j=p-1;` で `j = c-1, c-2, …` と左へ走る。 -/
def searchBase (row : Rowj) (i : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if hj : j < row.size then
             if hi : i < row.size then
               if row[j].val < row[i].val then some j else searchBase row i j
             else none
           else none

/-- 1 行から次の階差行を作る（JS の `currentLayer` 構成）。
親のあるセルだけが次の行に現れ、`position` は 1 減る。 -/
def nextRow (row : Rowj) : Rowj :=
  row.foldl (init := #[]) fun acc c =>
    match c.par with
    | none => acc
    | some p =>
      if hp : p < row.size then
        acc.push { pos := c.pos - 1, val := c.val - row[p].val, par := none }
      else acc

/-- 行に親を割り当てる。`prev = none` が JS の `calculatedMountain.length == 1`。
`forced` が立ったセルは JS が `continue` で飛ばすので、そのまま返す。 -/
def assignParents (prev : Option Rowj) (row : Rowj) : Rowj :=
  row.mapIdx fun i c =>
    if c.forced then c
    else
      match prev with
      | none     => { c with par := searchBase row i c.pos }
      | some pv  => { c with par := searchUpper pv row i (pv.size + 1)
                               (some (firstAtLeast pv (c.pos + 1))) }

/-- 入力列から行 0 を作る。 -/
def row0 (s : List Nat) : Rowj :=
  (s.toArray.mapIdx fun i v => { pos := i, val := v, par := none })

/-- JS の `calcMountain` の反復部。`fuel` は層数の上限
（JS は `hasNextLayer` で止まる）。 -/
def mountainGo (cur : Rowj) : Nat → List Rowj
  | 0 => [cur]
  | f+1 =>
    if cur.all (fun c => c.par.isNone) then [cur]
    else cur :: mountainGo (assignParents (some cur) (nextRow cur)) f

/-- JS の `calcMountain` 本体。 -/
def calcMountain (s : List Nat) : Nat → List Rowj
  | 0 => []
  | fuel+1 => mountainGo (assignParents none (row0 s)) fuel

/-! ## `calcDiagonal`

JS の後半。列ごとに頂から脚をたどり、着いた列を `diagonalTree` に記録する。

`while (mountain[height-1][l].position != … + 1) l++` のような完全一致の走査は、
`firstAtLeast` で書く。探している列は必ず在る（同じ列の 1 段下は生きている）ので
挙動は同じである。在らなければ JS は配列の外を触って落ちるが、そこは
`none` を返す形にしてある。
-/

/-- 列 `i` を含む最上段とその添字。JS は `j` を上から下へ走らせる。 -/
def topAt (M : List Rowj) (i : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | j+1 =>
    match M[j]? with
    | none => topAt M i j
    | some row =>
      let k := firstAtLeast row (i - j)
      if hk : k < row.size then
        if (row[k]'hk).pos + j = i then some (j, k) else topAt M i j
      else topAt M i j

/-- JS の脚 1 歩（疎配列版）。状態は `(段, その段での添字)`。 -/
def legStepJS (M : List Rowj) (h idx : Nat) : Option (Nat × Nat) :=
  match M[h]? with
  | none => none
  | some row =>
    if hi : idx < row.size then
      match h with
      | 0 =>
        match (row[idx]'hi).par with
        | none => none
        | some p => some (0, p)
      | h'+1 =>
        match M[h']? with
        | none => none
        | some below =>
          let l0 := firstAtLeast below ((row[idx]'hi).pos + 1)
          if hl0 : l0 < below.size then
            match (below[l0]'hl0).par with
            | none => none
            | some l =>
              if hl : l < below.size then
                -- JS の目標は `position - 1`。`position = 0` なら `-1` になり、
                -- どのセルにも一致しないので必ず段を下げる。自然数の切り捨て
                -- 引き算では `0` になってしまうので、ここだけ場合分けする。
                if (below[l]'hl).pos = 0 then some (h', l)
                else
                  let t := (below[l]'hl).pos - 1
                  let m := firstAtLeast row t
                  if hm : m < row.size then
                    if (row[m]'hm).pos = t then some (h'+1, m) else some (h', l)
                  else some (h', l)
              else none
          else none
    else none

/-- JS の脚歩行（疎配列版）。着いた列を返す。`none` は JS の `-1`。 -/
def legWalkJS (M : List Rowj) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, h, idx =>
    match legStepJS M h idx with
    | none => none
    | some (h', idx') =>
      match M[h']? with
      | none => none
      | some row =>
        if hi : idx' < row.size then
          match (row[idx']'hi).par with
          | none => some ((row[idx']'hi).pos + h')
          | some _ => legWalkJS M fuel h' idx'
        else none

/-- 列 `i` についての対角の 1 要素。値と歩行結果。 -/
def diagEntry (M : List Rowj) (i : Nat) : Option (Nat × Option Nat) :=
  match topAt M i M.length with
  | none => none
  | some (j, k) =>
    match M[j]? with
    | none => none
    | some row =>
      if hk : k < row.size then
        some ((row[k]'hk).val, legWalkJS M (i + 1) j k)
      else none

/-- 対角の値と歩行結果の並び。JS の `diagonal` と `diagonalTree`。 -/
def diagList (M : List Rowj) : List (Nat × Option Nat) :=
  (List.range (M.headD #[]).size).filterMap (diagEntry M)

/-- JS の `pw`：左へ走って最初に値が小さい添字。 -/
def pwScan (d : List Nat) (target : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if d.getD j 0 < target then some j else pwScan d target j

/-- JS の後半のループ：`diagonalTree` を辿って最初に値が小さい所で止まる。 -/
def treeScan (d : List Nat) (tree : List (Option Nat)) (target : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, p =>
    match tree.getD p none with
    | none => none
    | some q => if d.getD q 0 < target then some q else treeScan d tree target fuel q

/-- 出力の 1 要素。`forced` が JS の `"v"` 付きにあたる。 -/
structure DiagItem where
  val : Nat
  forced : Bool
  par : Option Nat
  deriving Repr, DecidableEq

/-- JS の `calcDiagonal` の出力（文字列にする前）。 -/
def calcDiagonal (M : List Rowj) : List DiagItem :=
  let e := diagList M
  let d := e.map Prod.fst
  let tree := e.map Prod.snd
  (List.range d.length).map fun i =>
    let target := d.getD i 0
    let p := treeScan d tree target (i + 1) i
    let w := pwScan d target i
    if p = w then { val := target, forced := false, par := none }
    else { val := target, forced := true, par := p }

/-- JS の `Math.max(Math.min(i-1,p),-1)`。`p` は `i` の祖先なので実際には効かない。 -/
def clampPar (i : Nat) (p : Option Nat) : Option Nat :=
  match i, p with
  | 0, _ => none
  | _+1, none => none
  | i'+1, some q => some (min i' q)

/-- JS の `parseSequenceElement` 相当。`"v"` 付きは `forced` を立てて親を固定する。 -/
def parseDiag (l : List DiagItem) : Rowj :=
  l.toArray.mapIdx fun i x =>
    { pos := i, val := x.val,
      par := if x.forced then clampPar i x.par else none, forced := x.forced }

end Yukito
