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

/-- JS の 1 セル。`par` は同じ行の配列添字（JS の `parentIndex`、`-1` は `none`）。 -/
structure Cell where
  pos : Nat
  val : Nat
  par : Option Nat
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

/-- 行に親を割り当てる。`isBase` は JS の `calculatedMountain.length == 1`。 -/
def assignParents (prev : Option Rowj) (row : Rowj) : Rowj :=
  row.mapIdx fun i c =>
    match prev with
    | none     => { c with par := searchBase row i c.pos }
    | some pv  => { c with par := searchUpper pv row i (pv.size + 1)
                             (some (firstAtLeast pv (c.pos + 1))) }

/-- 入力列から行 0 を作る。 -/
def row0 (s : List Nat) : Rowj :=
  (s.toArray.mapIdx fun i v => { pos := i, val := v, par := none })

/-- JS の `calcMountain`。`fuel` は層数の上限（JS は `hasNextLayer` で止まる）。 -/
def calcMountain (s : List Nat) : Nat → List Rowj
  | 0 => []
  | fuel+1 =>
    let base := assignParents none (row0 s)
    let rec go (cur : Rowj) : Nat → List Rowj
      | 0 => [cur]
      | f+1 =>
        if cur.all (fun c => c.par.isNone) then [cur]
        else
          let nxt := assignParents (some cur) (nextRow cur)
          cur :: go nxt f
    go base fuel

end Yukito
